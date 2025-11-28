import os
import re

original_folder = "simulations/Testcases/test10/original_mask"
renamed_folder = "simulations/Testcases/test10/ground_truth"
os.makedirs(renamed_folder, exist_ok=True)

def extract_frame_number(filename):
    match = re.search(r'GT_(\d+)', filename)  # 🔧 look after 'GT_'
    return int(match.group(1)) if match else None

bmp_files = [f for f in os.listdir(original_folder) if f.endswith(".png")]

for file_name in bmp_files:
    number = extract_frame_number(file_name)
    if number is not None:
        new_number = number - 1  # ✅ Shift down by 1
        if new_number < 0:
            print(f"⚠️ Skipping {file_name}, new number would be negative.")
            continue
        new_name = f"mask_{new_number:03}.png"
        src = os.path.join(original_folder, file_name)
        dst = os.path.join(renamed_folder, new_name)

        if os.path.exists(dst):
            print(f"⚠️ Skipping {file_name}, destination {new_name} already exists.")
        else:
            print(f"✅ Renaming {file_name} → {new_name}")
            os.rename(src, dst)
    else:
        print(f"❌ Skipping {file_name}, no number found.")
