import os
import re
import subprocess
from azure.identity import ClientSecretCredential
import openai

# ------------------ Configuration ------------------
TENANT_ID = "dummy"
CLIENT_ID = "dummy"
CLIENT_SECRET = "dummy"
RESOURCE_NAME = "dummy"
DEPLOYMENT_NAME = "gpt-35-turbo-blue"
API_VERSION = "2024-02-15-preview"
API_BASE = f"https://{RESOURCE_NAME}.openai.azure.com/"
FILENAME = "statediagram"
BASEPATH = os.path.dirname(os.path.dirname(os.path.realpath(__file__))) + "/resources/examples/"
TLA_TOOL_JAR = "../lib/tla2tools.jar"

def authenticate():
    credential = ClientSecretCredential(
        tenant_id=TENANT_ID,
        client_id=CLIENT_ID,
        client_secret=CLIENT_SECRET
    )

    client = openai.AzureOpenAI(
        api_version=API_VERSION,
        azure_endpoint=API_BASE,
        azure_ad_token_provider=lambda: credential.get_token("https://cognitiveservices.azure.com/.default").token
    )
    return client

def read_xml_file(filepath):
    with open(filepath, "r", encoding="utf-8") as f:
        return f.read()

def build_prompt_for_tla_no_cfg(xml_content: str):
    return [
        {
            "role": "user",
            "content": f"""Convert the following Draw.io XML diagram into a valid and meaningful TLA+ specification. Name the module `{FILENAME}`.

Your TLA+ specification should:
- Represent each component (e.g., lifeline, state, block) as a meaningful variable or process.
- Translate any communication or transitions into TLA+ actions using state updates with primed variables.
- Include a clear `Init` predicate that defines the initial system state.
- Define a `Next` predicate that includes all valid transitions between states.
- Use a `Spec` definition like `Init /\\ [][Next]_vars` to define system behavior.
- Assume that the vertical position (`y` values) in the XML reflects the temporal order of events in a sequence diagram — higher elements occur earlier in time.
- If the diagram implies logical errors (e.g., message misordering), model them explicitly as logical errors or highlight the inconsistency.
- Do not simply translate labels, but model the actual behavior implied by the diagram.

Here is the XML input:
{xml_content}
"""
        }
    ]

def extract_code_block(response_text):
    """Extract the TLA+ code block from the response."""
    code_blocks = re.findall(r"```(?:tla)?\n(.*?)```", response_text, re.DOTALL)
    return code_blocks[0].strip() if code_blocks else response_text.strip()

def clean_tla_spec(tla_text: str) -> str:
    # Remove broken or placeholder lines like ' = ""'
    tla_text = re.sub(r"^\s*=\s*\"\"$", "", tla_text, flags=re.MULTILINE)

    # Ensure variables are correctly declared
    if "VARIABLES =" in tla_text:
        tla_text = re.sub(r"VARIABLES = \"VARIABLES\"", "VARIABLES clientState, serviceState", tla_text)

    # Ensure Init and Next actions aren't just TRUE placeholders
    if "Init == \n    /\ TRUE" in tla_text:
        tla_text = tla_text.replace("Init == \n    /\ TRUE", "Init == \n    /\ clientState = \"idle\"\n    /\ serviceState = \"idle\"")

    if "Next == \n    /\ TRUE" in tla_text:
        tla_text = tla_text.replace("Next == \n    /\ TRUE", "Next == \n    /\ clientState' = \"sending\"\n    /\ serviceState' = \"processing\"")

    # Check for placeholders like 'StateInvariant == \n    /\ TRUE'
    if "StateInvariant == \n    /\ TRUE" in tla_text:
        tla_text = tla_text.replace("StateInvariant == \n    /\ TRUE", "StateInvariant == \n    /\ clientState \in {\"idle\", \"sending\"}\n    /\ serviceState \in {\"idle\", \"processing\"}")

    return tla_text

def clean_constants_block(tla_text: str) -> str:
    """Clean up the CONSTANTS block in the TLA+ code."""
    pattern = r'CONSTANTS\s+((?:.|\n)*?)\n\n'
    match = re.search(pattern, tla_text)
    if not match:
        return tla_text

    block = match.group(1)
    constants = re.findall(r'([A-Za-z_][A-Za-z0-9_]*)', block)

    # Ensure constants are in correct TLA+ format
    cleaned_block = 'CONSTANTS\n' + '\n'.join(f"{constant} = \"{constant}\"" for constant in constants) + '\n\n'
    return tla_text.replace(match.group(0), cleaned_block)

def ensure_footer(tla_text: str) -> str:
    """Ensure the TLA+ text ends with the footer."""
    if not tla_text.strip().endswith("============================================================================="):
        tla_text += "\n\n============================================================================="
    return tla_text

def fix_constants(tla_code: str) -> str:
    """Fix constants to match TLA+ syntax."""
    return re.sub(
        r"(?<=CONSTANTS\n)((?:\s*\w+\n)+)",
        lambda m: "".join(f"{line.strip()} = \"{line.strip()}\"\n" for line in m.group(1).strip().splitlines()),
        tla_code,
        flags=re.MULTILINE
    )

def write_tla_file(content: str, path: str):
    with open(path, "w") as f:
        f.write(clean_tla_spec(content) + "\n")

def run_tlc(filepath: str):
    try:
        command = ["java", "-cp", "tla2tools.jar",  "tlc2.TLC", "-generateSpecTE", filepath]
        # Run TLC as a separate process
        print(f"Executing: {' '.join(command)}")

        process = subprocess.run(
            command,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True  # Capture output as text (Python 3.7+)
        )

        # Check if there were any errors in stderr
        if process.returncode != 0:
            print(f"Error executing TLC: {process.returncode}")
            return

        # Print the TLC output
        print("----- TLC OUTPUT -----")
        print(process.stdout)

    except Exception as e:
        print(f"An error occurred: {e}")


# ------------------ Main Pipeline ------------------

def main():
    try:
        client = authenticate()
        xmlfile_name = FILENAME + ".xml"
        tlafile_name = FILENAME + ".tla"
        xml_content = read_xml_file(BASEPATH + xmlfile_name)
        # Step 1: XML ➜ TLA+
        tla_prompt = build_prompt_for_tla_no_cfg(xml_content)
        print(">>> Generating TLA+ from XML...")
        response = client.chat.completions.create(
            model=DEPLOYMENT_NAME,
            messages=tla_prompt,
            temperature=0.3
        )
        tla_raw = response.choices[0].message.content
        print("TLA+ content:", tla_raw)
        tla_code = extract_code_block(tla_raw)
        tla_code = clean_constants_block(tla_code)
        tla_code = ensure_footer(tla_code)

        write_tla_file(tla_code, BASEPATH + tlafile_name)
        print(f"✅ TLA+ content written to {tlafile_name}")

        # run_tlc(os.path.join(os.getcwd(), "SequenceDiagram.tla"))

    except Exception as e:
        print(">>> ERROR during execution:")
        print(e)

if __name__ == "__main__":
    main()