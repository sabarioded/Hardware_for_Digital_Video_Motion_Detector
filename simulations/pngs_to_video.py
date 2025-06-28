import cv2
import glob
import os
import re

def extract_number(filename):
    """Extract numeric part from filename like 'result42.png'"""
    match = re.search(r'result(\d+)\.png', os.path.basename(filename))
    return int(match.group(1)) if match else float('inf')  # fallback for non-matching

def pngs_to_video(png_folder, output_path, fps=30):
    # Get and sort PNG files by extracted number
    png_files = glob.glob(os.path.join(png_folder, "result*.png"))
    png_files.sort(key=extract_number)

    if not png_files:
        print("❌ No PNG files found in:", png_folder)
        return

    # Read first frame to get dimensions
    first = cv2.imread(png_files[0])
    height, width, _ = first.shape

    # Initialize video writer
    fourcc = cv2.VideoWriter_fourcc(*'mp4v')
    video_writer = cv2.VideoWriter(output_path, fourcc, fps, (width, height))

    # Write all frames
    for file in png_files:
        frame = cv2.imread(file)
        video_writer.write(frame)

    video_writer.release()
    print(f"🎞️ Video saved to: {output_path}")

# Example usage
pngs_to_video("simulations/results", "simulations/results/output_video.mp4", fps=30)
