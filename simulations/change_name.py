import os
import re

# Input/output folders
original_folder = "simulations/Testcases/test10/original"
renamed_folder = "simulations/Testcases/test10"
os.makedirs(renamed_folder, exist_ok=True)

# Extract number after dash (e.g., from I_SI_01-277.bmp)
def extract_frame_number(filename):
    match = re.search(r'-(\d+)', filename)
    return int(match.group(1)) if match else None

# Get all .bmp files
bmp_files = [f for f in os.listdir(original_folder) if f.endswith(".bmp")]

for file_name in bmp_files:
    number = extract_frame_number(file_name)
    if number is not None:
        new_number = number - 1  # ✅ Shift down by 1
        if new_number < 0:
            print(f"⚠️ Skipping {file_name}, new number would be negative.")
            continue
        new_name = f"frame_{new_number:03}.bmp"
        src = os.path.join(original_folder, file_name)
        dst = os.path.join(renamed_folder, new_name)

        if os.path.exists(dst):
            print(f"⚠️ Skipping {file_name}, destination {new_name} already exists.")
        else:
            print(f"✅ Renaming {file_name} → {new_name}")
            os.rename(src, dst)
    else:
        print(f"❌ Skipping {file_name}, no number found.")
