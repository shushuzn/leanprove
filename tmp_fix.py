import re

with open(r"D:\OpenClaw\leanprove\Leanprove\WienerProof.lean", "r", encoding="utf-8") as f:
    lines = f.readlines()

# Find the sorry at line 421 and remove everything after it until the next lemma/theorem/def
output = []
i = 0
while i < len(lines):
    line = lines[i]
    stripped = line.strip()
    
    # If we find "sorry" on line 421 area, skip until next lemma/theorem/def
    if stripped == "sorry" and i >= 420 and i <= 425:
        output.append(line)
        i += 1
        # Skip lines until next lemma/theorem/def or non-empty line
        while i < len(lines):
            next_line = lines[i]
            next_stripped = next_line.strip()
            if next_stripped.startswith("theorem ") or next_stripped.startswith("lemma ") or next_stripped.startswith("def ") or next_stripped.startswith("/-!"):
                break
            i += 1
    else:
        output.append(line)
        i += 1

with open(r"D:\OpenClaw\leanprove\Leanprove\WienerProof.lean", "w", encoding="utf-8") as f:
    f.writelines(output)

print("Done!")
