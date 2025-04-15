from PIL import Image
import pytesseract
import re
pytesseract.pytesseract.tesseract_cmd = "/opt/homebrew/bin/tesseract"
def extract_messages_from_image(image_path):
    # Run OCR on image
    image = Image.open(image_path)
    text = pytesseract.image_to_string(image)

    # Extract lines like: Object1 -> Object2 : message
    lines = text.split('\n')
    messages = []
    participants = set()

    for line in lines:
        line = line.strip()
        # Heuristic: find lines with arrows
        match = re.match(r"(\w+)\s*->\s*(\w+)\s*:\s*(.+)", line)
        if match:
            src, dst, msg = match.groups()
            participants.update([src, dst])
            messages.append((src, dst, msg))

        # Fallback: lines with only words that could be messages
        elif "<<" in line and ">>" in line:
            msg = line.replace("<<", "").replace(">>", "").strip()
            messages.append(("UNKNOWN", "UNKNOWN", msg))

    return list(participants), messages

def generate_tla(participants, messages):
    tla_lines = [
        "---- MODULE GeneratedSpec ----",
        "EXTENDS Naturals, Sequences",
        "",
        "VARIABLES state",
        "",
        'Init == state = "Start"',
        "",
        "Next ==\n  \/ " + "\n  \/ ".join([
            f'state = "{messages[i-1][2] if i > 0 else "Start"}" /\\ state\' = "{msg}"'
            for i, (_, _, msg) in enumerate(messages)
        ]) if messages else "Next == UNCHANGED state",
        "",
        "Spec == Init /\\ [][Next]_state",
        "===="
    ]

    return "\n".join(tla_lines)

def image_to_tla(image_path):
    participants, messages = extract_messages_from_image(image_path)
    return generate_tla(participants, messages)


# Example usage
if __name__ == "__main__":
    image_path = "img2.png"  # Replace with your image path
    tla_spec = image_to_tla(image_path)
    with open("GeneratedSpec.tla", "w") as f:
        f.write(tla_spec)
    print(tla_spec)
