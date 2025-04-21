import xml.etree.ElementTree as ET
import subprocess
import os

BASEPATH = os.path.dirname(os.path.dirname(os.path.realpath(__file__))) + "/resources/examples/"

def parse_xml(xml_file):
    tree = ET.parse(BASEPATH + xml_file)
    root = tree.getroot()
    return root


def extract_participants_and_messages(root):
    participants = set()
    messages = []

    # Traverse each cell in the Draw.io diagram XML
    for cell in root.findall(".//mxCell"):
        style = cell.attrib.get("style", "")
        value = cell.attrib.get("value", "").strip()
        cell_id = cell.attrib.get("id", "")

        # Extract participants (lifelines)
        if "umlLifeline" in style and cell.attrib.get("vertex") == "1":
            participants.add(value or cell_id)

        # Extract messages (edges)
        if cell.attrib.get("edge") == "1":
            source = cell.attrib.get("source")
            target = cell.attrib.get("target")
            message_value = value or cell.attrib.get("id", "")

            if source and target:
                messages.append((source, target, message_value))

    # Sort messages based on source and target to follow the Y-axis flow of the sequence diagram
    messages_sorted = sorted(messages, key=lambda x: (x[0], x[1]))  # Sort by source and target

    # Print the sorted messages
    print("Extracted Messages:")
    for message in messages_sorted:
        print(f"Source: {message[0]}, Target: {message[1]}, Message: {message[2]}")

    return participants, messages_sorted


def generate_generic_tla_code(filename, init_state, messages_info, moduleName):
    lines = []
    # Add module header with constant declaration.
    lines.append("---- MODULE " + moduleName + "  ----\n")
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

    # No sorting: process messages in the order they appear
    for i, (src, dst, label) in enumerate(messages_info):
        lines.append(f"Action_{i} ==\n")
        lines.append(f"  /\\ state = \"{src}\"\n")
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

    try:
        result = subprocess.run(
            [
                "java", "-cp", "../lib/tla2tools.jar", "tlc2.TLC",
                "-deadlock", tla_file_path
            ],
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

def parse_trace_file(filepath):
    transitions = []
    with open(filepath, 'r') as f:
        lines = f.readlines()

    states = []
    for line in lines:
        if line.startswith("State"):
            states.append({})
        elif '=' in line:
            var, val = line.strip().split(" = ")
            states[-1][var] = val.strip('"')

    for i in range(len(states) - 1):
        from_state = states[i].get("state", f"Unknown_{i}")
        to_state = states[i + 1].get("state", f"Unknown_{i+1}")
        label = ""
        if states[i].get("decision") != states[i + 1].get("decision"):
            label = f'decision={states[i + 1]["decision"]}'
        transitions.append((from_state, to_state, label))

    return transitions


from graphviz import Digraph

def create_state_diagram(transitions, filename="tla_flow"):
    dot = Digraph(format='png')
    for from_state, to_state, label in transitions:
        dot.edge(from_state, to_state, label)
    output_path = dot.render(filename, cleanup=True)
    print(f"Diagram saved to: {output_path}")


def main():
    fileName = "oor"  # Your filename without extensions
    xml_file = fileName + ".xml"  # Replace with your XML file path
    tla_file = fileName + ".tla"

    # Step 1: Parse the XML and extract participants and messages
    root = parse_xml(xml_file)
    participants, messages = extract_participants_and_messages(root)

    # Step 2: Generate TLA+ code from extracted information
    tla_code = generate_generic_tla_code(tla_file, participants, messages, fileName)
    print("\nGenerated TLA+ Specification:\n")
    print(tla_code)

    # Step 3: Generate TLC config file
    generate_generic_cfg_file(tla_file, participants, messages)

    # Step 4: Run TLC model checker and generate trace
    trace_file = run_tla_model_checker(tla_file)
    if trace_file:
        # Step 5: Parse the trace file to get transitions
        transitions = parse_trace_file(trace_file)
        # Step 6: Create a state diagram based on the transitions
        create_state_diagram(transitions, filename=fileName + "_state_diagram")
    else:
        print("Error: Trace file not generated.")

if __name__ == "__main__":
    main()
