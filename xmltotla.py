import xml.etree.ElementTree as ET
import subprocess
import os

def parse_xml(xml_file):
    tree = ET.parse(xml_file)
    root = tree.getroot()
    return root


def extract_participants_and_messages(root):
    participants = set()
    messages = []

    for cell in root.findall(".//mxCell"):
        style = cell.attrib.get("style", "")
        value = cell.attrib.get("value", "").strip()
        cell_id = cell.attrib.get("id", "")

        # Lifelines
        if "umlLifeline" in style and cell.attrib.get("vertex") == "1":
            participants.add(value or cell_id)

        # Messages
        if cell.attrib.get("edge") == "1":
            source = cell.attrib.get("source")
            target = cell.attrib.get("target")
            message_value = value or cell.attrib.get("id", "")
            if source and target:
                messages.append((source, target, message_value))

    return participants, messages


def generate_generic_tla_code(filename, init_state, messages_info):
    lines = []
    # Add module header with constant declaration.
    lines.append("---- MODULE generated_workflow ----\n")
    lines.append("EXTENDS Sequences, Integers, TLC\n\n")
    lines.append("CONSTANT MAX_LEN\n\n")
    lines.append("VARIABLES state, messages\n\n")

    # Init: set the starting state using the first participant from init_state.
    lines.append("Init ==\n")
    if init_state:
        lines.append(f"  /\\ state = \"{list(init_state)[0]}\"\n")
    else:
        lines.append("  /\\ state = \"Unknown\"\n")
    lines.append("  /\\ messages = << >>\n\n")

    # Actions: For each message (edge), add a guard that messages haven't exceeded MAX_LEN.
    lines.append("(* Actions with bounded messages *)\n")
    for i, (src, dst, label) in enumerate(messages_info):
        lines.append(f"Action_{i} ==\n")
        lines.append(f"  /\\ state = \"{src}\"\n")
        # Add the bound guard:
        lines.append("  /\\ Len(messages) < MAX_LEN\n")
        lines.append(f"  /\\ state' = \"{dst}\"\n")
        lines.append(f"  /\\ messages' = Append(messages, \"{label}\")\n\n")

    # Next: combine actions in a nondeterministic choice.
    actions = " \\/ ".join([f"Action_{i}" for i in range(len(messages_info))])
    lines.append(f"Next == {actions}\n\n")

    # Helper: SelectIndex (must be defined before used in the invariant)
    lines.append("SelectIndex(seq, msg) ==\n")
    lines.append("  IF \\E i \\in 1..Len(seq): seq[i] = msg\n")
    lines.append("  THEN CHOOSE i \\in 1..Len(seq): seq[i] = msg\n")
    lines.append("  ELSE -1\n\n")

    # Invariant: Require that a Request appears before a Response.
    lines.append("(* Invariant: Request must appear before Response *)\n")
    lines.append("Invariant ==\n")
    lines.append("  LET r1 == SelectIndex(messages, \"Response\") IN\n")
    lines.append("  LET r0 == SelectIndex(messages, \"Request\") IN\n")
    lines.append("    r1 = -1 \\/ (r0 # -1 /\\ r0 < r1)\n\n")

    # Specification
    lines.append("Spec == Init /\\ [][Next]_<<state, messages>> /\\ Invariant\n\n")
    lines.append("====\n")

    # Write to file
    with open(filename, "w") as f:
        f.writelines(lines)

    return "".join(lines)

def generate_generic_cfg_file(tla_filename, participants, messages):
    module_name = os.path.splitext(os.path.basename(tla_filename))[0]
    cfg_filename = f"{module_name}.cfg"
    cfg_content = f"""INIT Init
NEXT Next
INVARIANT Invariant
CONSTANTS
  MAX_LEN = 3
"""
    with open(cfg_filename, 'w') as f:
        f.write(cfg_content)
    print(f"✅ TLC config file '{cfg_filename}' generated.")

def run_tla_model_checker(tla_file_path):
    if not os.path.exists(tla_file_path):
        print(f"Error: File '{tla_file_path}' not found.")
        return

    print(f"Running TLC on '{tla_file_path}'...")
    try:
        result = subprocess.run(
            ["java", "-cp", "./tla2tools.jar", "tlc2.TLC", tla_file_path],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            universal_newlines=True
        )

        print("TLC Output:")
        print(result.stdout)
        if result.stderr:
            print("TLC Errors:")
            print(result.stderr)
    except FileNotFoundError:
        print("Error: Java not found or TLC not configured correctly.")
    except Exception as e:
        print(f"Unexpected error: {e}")

def main():
    xml_file = "bugfix.xml"  # Replace with your XML file path
    tla_file = "generated_workflow.tla"

    root = parse_xml(xml_file)
    participants, messages = extract_participants_and_messages(root)

    tla_code = generate_generic_tla_code(tla_file, participants, messages)
    print("\nGenerated TLA+ Specification:\n")
    print(tla_code)

    generate_generic_cfg_file(tla_file, participants, messages)
    run_tla_model_checker(tla_file)

if __name__ == "__main__":
    main()
