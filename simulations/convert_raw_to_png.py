import os
import glob
from PIL import Image
import numpy as np
import re

# Set resolution
width, height = 352, 288
base_folder = os.path.abspath("simulations/results")

def extract_number(path):
    """Extracts numeric part like result123.raw → 123"""
    filename = os.path.basename(path)
    match = re.search(r'result(\d+)\.raw', filename)
    return int(match.group(1)) if match else -1

def raw_to_png(raw_path, png_path):
    with open(raw_path, "rb") as f:
        raw_bytes = f.read()

    if len(raw_bytes) != width * height * 4:
        print(f"❌ Skipping {raw_path}: Unexpected size {len(raw_bytes)} bytes")
        return

    rgb_data = [
        (raw_bytes[i], raw_bytes[i + 1], raw_bytes[i + 2])
        for i in range(0, len(raw_bytes), 4)
    ]

    rgb_array = np.array(rgb_data, dtype=np.uint8).reshape((height, width, 3))
    img = Image.fromarray(rgb_array, mode='RGB')
    img.save(png_path)
    print(f"✅ Saved {png_path}")

# Get all raw files and sort numerically by index
raw_files = glob.glob(os.path.join(base_folder, "result*.raw"))
raw_files.sort(key=extract_number)

# Convert to PNG
for raw_path in raw_files:
    base_name = os.path.splitext(os.path.basename(raw_path))[0]
    png_path = os.path.join(base_folder, f"{base_name}.png")
    raw_to_png(raw_path, png_path)
