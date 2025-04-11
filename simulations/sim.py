from PIL import Image
import subprocess
import time
import os
import glob
import numpy as np
import cv2
import os

def extract_frames(video_path, output_folder, prefix="frame"):
    os.makedirs(output_folder, exist_ok=True)

    cap = cv2.VideoCapture(video_path)
    frame_idx = 0

    if not cap.isOpened():
        print("❌ Error: Cannot open video.")
        return

    while True:
        ret, frame = cap.read()
        if not ret:
            break

        filename = f"{prefix}_{frame_idx:03}.png"
        path = os.path.join(output_folder, filename)
        cv2.imwrite(path, frame)
        # print(f"✅ Saved: {path}")
        frame_idx += 1

    cap.release()
    # print(f"\n🎉 Done! Extracted {frame_idx} frames to {output_folder}")

def png_to_video(frames_folder, output_path, fps=30):
    # Get all PNG frames
    frame_files = sorted(glob.glob(os.path.join(frames_folder, '*.png')))

    if not frame_files:
        print("❌ No PNG files found.")
        return

    # Get frame size from the first image
    first_frame = cv2.imread(frame_files[0])
    height, width, _ = first_frame.shape

    # Define video writer (codec, filename, FPS, resolution)
    fourcc = cv2.VideoWriter_fourcc(*'mp4v')  # or 'XVID' for .avi
    out = cv2.VideoWriter(output_path, fourcc, fps, (width, height))

    for frame_file in frame_files:
        frame = cv2.imread(frame_file)
        out.write(frame)

    out.release()
    print(f"🎥 Video saved to: {output_path}")

############################# PREPROCESS #############################
def convert_png_to_raw(frames_folder):
    output_folder = os.path.join(frames_folder, 'raw_rbg32')
    os.makedirs(output_folder, exist_ok=True)

    frame_paths = sorted(glob.glob(os.path.join(frames_folder, '*.png')))

    for path in frame_paths:
        img = Image.open(path).convert('RGB')
        width, height = img.size
        pixels = img.load()

        raw_bytes = bytearray()
        for y in range(height):
            for x in range(width):
                r, g, b = pixels[x, y]
                raw_bytes.extend([r, b, g, 0x00])  # R, B, G, 0

        filename = os.path.splitext(os.path.basename(path))[0]
        output_path = os.path.join(output_folder, f'{filename}.raw')
        with open(output_path, 'wb') as f:
            f.write(raw_bytes)

        # print(f"✅ Saved: {output_path}")

    # print("🎉 All frames converted to 32-bit RBG raw format.")


############################# POSTPROCESS #############################
def convert_all_raw_to_png(raw_folder, width, height):
    raw_files = sorted(glob.glob(os.path.join(raw_folder, '*.raw')))

    for raw_path in raw_files:
        with open(raw_path, 'rb') as f:
            raw_bytes = f.read()

        rgb_data = bytearray()
        for i in range(0, len(raw_bytes), 4):
            r = raw_bytes[i]
            b = raw_bytes[i+1]
            g = raw_bytes[i+2]
            rgb_data.extend([r, g, b])

        img = Image.frombytes('RGB', (width, height), bytes(rgb_data))

        # Save as PNG with matching name
        output_png = raw_path.replace('.raw', '_reconstructed.png')
        img.save(output_png)
        # print(f"✅ Reconstructed: {output_png}")

def save_rgb_frame_as_raw(output_frame, width, height, output_folder, base_filename, frame_idx):
    output_bytes = bytearray()
    for y in range(height):
        for x in range(width):
            r, b, g = output_frame[y, x]
            output_bytes.extend([r, b, g, 0x00])  # R, B, G, 0x00

    output_name = f"{base_filename}_{frame_idx:03}.raw"
    output_path = os.path.join(output_folder, output_name)

    with open(output_path, 'wb') as f:
        f.write(output_bytes)

    # print(f"✅ Saved frame: {output_path}")

def simulate_motion_3frames(raw_folder, width, height, threshold=30, highlight_color=(255, 0, 0)):
    raw_files = sorted(glob.glob(os.path.join(raw_folder, '*.raw')))
    if len(raw_files) < 3:
        print("❌ Not enough frames for 3-frame differencing.")
        return

    output_folder = os.path.join(raw_folder, '3frames_diff')
    os.makedirs(output_folder, exist_ok=True)

    frame_buffer = []

    for frame_idx, raw_path in enumerate(raw_files):
        with open(raw_path, 'rb') as f:
            raw_bytes = f.read()

        frame = np.zeros((height, width, 3), dtype=np.uint8)
        byte_idx = 0
        for y in range(height):
            for x in range(width):
                r = raw_bytes[byte_idx]
                b = raw_bytes[byte_idx + 1]
                g = raw_bytes[byte_idx + 2]
                frame[y, x] = [r, b, g]
                byte_idx += 4

        frame_buffer.append(frame)

        if len(frame_buffer) < 3:
            continue  # wait until we have 3 frames

        F_t2 = frame_buffer[0]  # t-2
        F_t1 = frame_buffer[1]  # t-1
        F_t  = frame_buffer[2]  # t

        # Compute differences
        D1 = np.where(F_t > F_t1, F_t - F_t1, F_t1 - F_t)
        D2 = np.where(F_t1 > F_t2, F_t1 - F_t2, F_t2 - F_t1)

        # Reduce to max difference per pixel (across R, B, G)
        D1_max = np.max(D1, axis=2)
        D2_max = np.max(D2, axis=2)

        # Motion is only valid if both diffs are above threshold
        motion_mask = (D1_max > threshold) & (D2_max > threshold)

        # Optional: apply a "motion energy" threshold
        motion_energy = D1_max + D2_max
        strong_motion = motion_energy > (threshold * 2)

        # Final motion map
        motion_map = motion_mask & strong_motion

        # Overlay motion on current frame
        output_frame = frame_buffer[1].copy()  # F_t-2
        output_frame[motion_map] = highlight_color

        # Write to raw format
        output_bytes = bytearray()
        for y in range(height):
            for x in range(width):
                r, b, g = output_frame[y, x]
                output_bytes.extend([r, b, g, 0x00])

        output_name = f"frame3_{frame_idx-1:03}.raw"
        output_path = os.path.join(output_folder, output_name)
        with open(output_path, 'wb') as f:
            f.write(output_bytes)

        print(f"✅ Saved overlay frame: {output_path}")

        # Slide window to keep 2 previous frames
        frame_buffer.pop(0)

    print("✅ Three-frame motion overlay complete.")

def simulate_motion_2frames(raw_folder, width, height, threshold=30, highlight_color=(255, 0, 0)):
    raw_files = sorted(glob.glob(os.path.join(raw_folder, '*.raw')))
    if len(raw_files) < 2:
        print("❌ Not enough frames for 2-frame differencing.")
        return

    output_folder = os.path.join(raw_folder, '2frames_diff')
    os.makedirs(output_folder, exist_ok=True)

    frame_buffer = []

    for frame_idx, raw_path in enumerate(raw_files):
        with open(raw_path, 'rb') as f:
            raw_bytes = f.read()

        frame = np.zeros((height, width, 3), dtype=np.uint8)
        byte_idx = 0
        for y in range(height):
            for x in range(width):
                r = raw_bytes[byte_idx]
                b = raw_bytes[byte_idx + 1]
                g = raw_bytes[byte_idx + 2]
                frame[y, x] = [r, b, g]
                byte_idx += 4

        frame_buffer.append(frame)

        if len(frame_buffer) < 2:
            continue  # wait until we have 2 frames

        F_t1 = frame_buffer[0]  # t-1
        F_t  = frame_buffer[1]  # t

        # Compute differences
        D = np.where(F_t > F_t1, F_t - F_t1, F_t1 - F_t)

        # Reduce to max difference per pixel (across R, B, G)
        D_max = np.max(D, axis=2)

        brightness_t = np.sum(F_t, axis=2) # R + G + B
        brightness_t1 =  np.sum(F_t1, axis=2) 
        brightness = np.where(brightness_t > brightness_t1, brightness_t - brightness_t1, brightness_t1 - brightness_t)
        brightness_threshold = 60

        # Motion is only valid if both diffs are above threshold
        motion_map = (D_max > threshold) & (brightness > brightness_threshold)

        if not np.any(motion_map):
            output_frame = frame_buffer[0].copy()
        else:
            output_frame = frame_buffer[0].copy()
            output_frame[motion_map] = highlight_color

        # Write to raw format
        output_bytes = bytearray()
        for y in range(height):
            for x in range(width):
                r, b, g = output_frame[y, x]
                output_bytes.extend([r, b, g, 0x00])

        output_name = f"frame2_{frame_idx-1:03}.raw"
        output_path = os.path.join(output_folder, output_name)
        with open(output_path, 'wb') as f:
            f.write(output_bytes)

        print(f"✅ Saved overlay frame: {output_path}")

        # Slide window to keep 2 previous frames
        frame_buffer.pop(0)

    print("✅ Two motion overlay complete.")

    
def background_subtraction_hw(raw_folder, width, height, alpha=0.1, threshold=30, highlight_color=(255, 0, 0)):
    import numpy as np
    raw_files = sorted(glob.glob(os.path.join(raw_folder, '*.raw')))
    if not raw_files:
        print("❌ No raw files found.")
        return

    output_folder = os.path.join(raw_folder, 'motion_bg_subtract')
    os.makedirs(output_folder, exist_ok=True)

    background = None

    for frame_idx, raw_path in enumerate(raw_files):
        with open(raw_path, 'rb') as f:
            raw_bytes = f.read()

        # Parse raw R,B,G,0x00 into frame
        frame = np.zeros((height, width, 3), dtype=np.float32)
        byte_idx = 0
        for y in range(height):
            for x in range(width):
                r = raw_bytes[byte_idx]
                b = raw_bytes[byte_idx + 1]
                g = raw_bytes[byte_idx + 2]
                frame[y, x] = [r, b, g]
                byte_idx += 4

        if background is None:
            background = frame.copy()  # Init on first frame
            continue

        # Update background
        background = alpha * frame + (1 - alpha) * background

        # Compute difference and motion map
        diff = np.abs(frame - background)
        diff_max = np.max(diff, axis=2)
        motion_map = (diff_max > threshold)

        # Overlay motion on original frame
        output_frame = frame.astype(np.uint8).copy()
        output_frame[motion_map] = highlight_color

        # Save as raw: R, B, G, 0x00
        output_bytes = bytearray()
        for y in range(height):
            for x in range(width):
                r, b, g = output_frame[y, x]
                output_bytes.extend([int(r), int(b), int(g), 0x00])

        output_path = os.path.join(output_folder, f'motion_bg_{frame_idx:03}.raw')
        with open(output_path, 'wb') as f:
            f.write(output_bytes)

        print(f"✅ Background-subtracted frame saved: {output_path}")

    print("✅ Running average background subtraction completed.")

def background_and_2frames(raw_folder, width, height, alpha=0.1, threshold=30, highlight_color=(255, 0, 0)):
    raw_files = sorted(glob.glob(os.path.join(raw_folder, '*.raw')))
    if len(raw_files) < 2:
        print("❌ Not enough frames for 2-frame differencing.")
        return

    output_folder = os.path.join(raw_folder, 'background_and_2frames')
    os.makedirs(output_folder, exist_ok=True)

    frame_buffer = []
    background = None

    for frame_idx, raw_path in enumerate(raw_files):
        with open(raw_path, 'rb') as f:
            raw_bytes = f.read()

        frame = np.zeros((height, width, 3), dtype=np.uint8)
        byte_idx = 0
        for y in range(height):
            for x in range(width):
                r = raw_bytes[byte_idx]
                b = raw_bytes[byte_idx + 1]
                g = raw_bytes[byte_idx + 2]
                frame[y, x] = [r, b, g]
                byte_idx += 4
        
        frame_buffer.append(frame)

        if background is None:
            background = frame.copy()  # Init on first frame
            save_rgb_frame_as_raw(
            output_frame=frame_buffer[0].copy(),
            width=width,
            height=height,
            output_folder=output_folder,
            base_filename="subt_2frame",
            frame_idx=frame_idx
            )
            continue

        if len(frame_buffer) < 2:
            continue  # wait until we have 2 frames

        # Compute difference and motion map BEFORE updating background
        diff = np.where(frame > background, frame - background, background - frame)
        diff_max = np.max(diff, axis=2)

        F_t1 = frame_buffer[0]  # t-1
        F_t  = frame_buffer[1]  # t

        # Compute differences
        D = np.where(F_t > F_t1, F_t - F_t1, F_t1 - F_t)
        D_max = np.max(D, axis=2)

        # Motion is only valid if both diffs are above threshold
        motion_map = (D_max > threshold) & (diff_max > threshold)

        # Overlay
        output_frame = F_t.copy()
        if np.any(motion_map):
            output_frame[motion_map] = highlight_color

        save_rgb_frame_as_raw(
            output_frame=output_frame,
            width=width,
            height=height,
            output_folder=output_folder,
            base_filename="subt_2frame",
            frame_idx=frame_idx
        )

        background = alpha * frame + (1 - alpha) * background

        # Slide window to keep previous frames
        frame_buffer.pop(0)

def background_and_3frames(raw_folder, width, height, shift=4, threshold=30, highlight_color=(255, 0, 0)):
    raw_files = sorted(glob.glob(os.path.join(raw_folder, '*.raw')))
    if len(raw_files) < 3:
        print("❌ Not enough frames for 2-frame differencing.")
        return

    output_folder = os.path.join(raw_folder, 'background_and_3frames')
    os.makedirs(output_folder, exist_ok=True)

    frame_buffer = []
    background = None

    for frame_idx, raw_path in enumerate(raw_files):
        with open(raw_path, 'rb') as f:
            raw_bytes = f.read()

        frame = np.zeros((height, width, 3), dtype=np.uint8)
        byte_idx = 0
        for y in range(height):
            for x in range(width):
                r = raw_bytes[byte_idx]
                b = raw_bytes[byte_idx + 1]
                g = raw_bytes[byte_idx + 2]
                frame[y, x] = [r, b, g]
                byte_idx += 4
        
        frame_buffer.append(frame)

        if background is None:
            background = frame.copy()  # Init on first frame
            continue

        if len(frame_buffer) < 3:
            continue  # wait until we have 3 frames

        bg_diff = np.where(frame > background, frame - background, background - frame)
        bg_diff_max = np.max(bg_diff, axis=2)

        F_t2 = frame_buffer[0]  # t-2
        F_t1 = frame_buffer[1]  # t-1
        F_t  = frame_buffer[2]  # t

        # Compute differences
        D1 = np.where(F_t > F_t1, F_t - F_t1, F_t1 - F_t)
        D2 = np.where(F_t1 > F_t2, F_t1 - F_t2, F_t2 - F_t1)
        D1_max = np.max(D1, axis=2)
        D2_max = np.max(D1, axis=2)

        # Motion is only valid if both diffs are above threshold
        motion_map = (D1_max > threshold) & (D2_max > threshold) & (bg_diff_max > threshold)

        # Overlay
        output_frame = F_t.copy()
        if np.any(motion_map):
            output_frame[motion_map] = highlight_color

        save_rgb_frame_as_raw(
            output_frame=output_frame,
            width=width,
            height=height,
            output_folder=output_folder,
            base_filename="subt_3frame",
            frame_idx=frame_idx
        )

        #background = alpha * frame + (1 - alpha) * background
        background = np.clip(background.astype(np.int32) - (background >> shift) + (frame.astype(np.int32) >> shift), 0, 255).astype(np.uint8)


        # Slide window to keep previous frames
        frame_buffer.pop(0)

def background_and_3frames_grayscale(raw_folder, width, height, shift=4, threshold=15, highlight_color=(255, 0, 0)):
    raw_files = sorted(glob.glob(os.path.join(raw_folder, '*.raw')))
    if len(raw_files) < 3:
        print("❌ Not enough frames for 2-frame differencing.")
        return

    output_folder = os.path.join(raw_folder, 'background_and_3frames')
    os.makedirs(output_folder, exist_ok=True)

    frame_buffer = []
    gray_buffer = []
    background = None

    for frame_idx, raw_path in enumerate(raw_files):
        with open(raw_path, 'rb') as f:
            raw_bytes = f.read()

        frame = np.zeros((height, width, 3), dtype=np.uint8)
        byte_idx = 0
        for y in range(height):
            for x in range(width):
                r = raw_bytes[byte_idx]
                b = raw_bytes[byte_idx + 1]
                g = raw_bytes[byte_idx + 2]
                frame[y, x] = [r, b, g]
                byte_idx += 4

        # # Convert to grayscale: simple average
        # gray_frame = np.mean(frame, axis=2).astype(np.uint8)
        # Convert to grayscale: luminosity method
        r = frame[:, :, 0].astype(np.uint16)
        g = frame[:, :, 1].astype(np.uint16)
        b = frame[:, :, 2].astype(np.uint16)
        gray_frame = ((77 * r + 150 * g + 29 * b) >> 8).astype(np.uint8) #(77, 150, 29) is the luminosity method weights divided by 256

        frame_buffer.append(frame)
        gray_buffer.append(gray_frame)

        if background is None:
            background = gray_frame.copy()
            continue

        if len(frame_buffer) < 3:
            continue  # Wait for 3 frames

        # Background difference (grayscale)
        bg_diff = np.where(gray_frame > background, gray_frame - background, background - gray_frame)

        F_t2 = gray_buffer[0]  # t-2
        F_t1 = gray_buffer[1]  # t-1
        F_t  = gray_buffer[2]  # t

        # Motion differences
        D1 = np.where(F_t > F_t1, F_t - F_t1, F_t1 - F_t)
        D2 = np.where(F_t1 > F_t2, F_t1 - F_t2, F_t2 - F_t1)

        # adaptive threshold
        num_pixels = width * height
        adaptive_shift = int(np.log2(3 * num_pixels))
        sum_diffs = np.sum(D1.astype(np.uint32) + D2.astype(np.uint32) + bg_diff.astype(np.uint32))
        adaptive_threshold = (int(sum_diffs) >> adaptive_shift) + 5

        # Motion detection map
        motion_map = (D1 > adaptive_threshold) & (D2 > adaptive_threshold) & (bg_diff > adaptive_threshold)

        # Overlay on original RGB frame
        output_frame = frame_buffer[1].copy()
        if np.any(motion_map):
            output_frame[motion_map] = highlight_color

        save_rgb_frame_as_raw(
            output_frame=output_frame,
            width=width,
            height=height,
            output_folder=output_folder,
            base_filename="subt_3frame",
            frame_idx=frame_idx
        )

        # Background update
        background = np.clip(
            background.astype(np.int32) - (background >> shift) + (gray_frame.astype(np.int32) >> shift),
            0, 255
        ).astype(np.uint8)

        # Keep sliding window of last 3 frames
        frame_buffer.pop(0)
        gray_buffer.pop(0)

def main():

    ####### TEST1 #########
    frames_folder_t1 = 'simulations/Testcases/test1'
    convert_png_to_raw(frames_folder_t1)
    # Detect width and height from an original image
    example_png_t1 = os.path.join(frames_folder_t1, 'frame_00.png')
    img_t1 = Image.open(example_png_t1)
    width_t1, height_t1 = img_t1.size

    # Define raw folder before using it
    raw_folder = os.path.join(frames_folder_t1, 'raw_rbg32')
    # raw_folder_2frame = os.path.join(raw_folder, '2frames_diff') # 2 frames
    # raw_folder_motion = os.path.join(raw_folder, '3frames_diff') # 3 frames
    # raw_folder_subtract = os.path.join(raw_folder, 'motion_bg_subtract') # subt
    # raw_folder_subtract_2frame = os.path.join(raw_folder, 'background_and_2frames') # subt
    raw_folder_subtract_3frame = os.path.join(raw_folder, 'background_and_3frames') # subt

    # Run motion simulation
    # simulate_motion_overlay_hw(raw_folder, width, height, threshold=30)
    # simulate_motion_2frames(raw_folder, width, height, threshold=30)
    # simulate_motion_3frames(raw_folder, width, height, threshold=30)
    # background_subtraction_hw(raw_folder, width, height, alpha=0.2, threshold=30)
    # background_and_2frames(raw_folder, width, height, alpha=0.05, threshold=30)
    # background_and_3frames(raw_folder, width_t1, height_t1, shift=4, threshold=30)
    background_and_3frames_grayscale(raw_folder, width_t1, height_t1, shift=4, threshold=5)

    # Reconstruct all raw frames
    # convert_all_raw_to_png(raw_folder, width_t1, height_t1)
    # convert_all_raw_to_png(raw_folder_2frame, width, height)
    # convert_all_raw_to_png(raw_folder_motion, width, height)
    # convert_all_raw_to_png(raw_folder_subtract, width, height)
    # convert_all_raw_to_png(raw_folder_subtract_2frame, width, height)
    convert_all_raw_to_png(raw_folder_subtract_3frame, width_t1, height_t1)

    ###### TEST2 #######
    frames_folder_t2 = 'simulations/Testcases/test2'
    video_test2_path = 'simulations/Testcases/test2/Ball Bouncing Across the Screen.mp4'
    extract_frames(video_test2_path, frames_folder_t2)
    convert_png_to_raw(frames_folder_t2)

    # Detect width and height from an original image
    example_png_t2 = os.path.join(frames_folder_t2, 'frame_000.png')
    img_t2 = Image.open(example_png_t2)
    width_t2, height_t2 = img_t2.size

    # Define raw folder before using it
    raw_folder = os.path.join(frames_folder_t2, 'raw_rbg32')
    raw_folder_subtract_3frame = os.path.join(raw_folder, 'background_and_3frames') # subt
    print("Define raw folder before using it - done")

    # Run motion simulation
    # background_and_3frames(raw_folder, width_t2, height_t2, shift=4, threshold=30)
    background_and_3frames_grayscale(raw_folder, width_t2, height_t2, shift=4, threshold=15)
    print("Run motion simulation - done")

    # Reconstruct all raw frames
    convert_all_raw_to_png(raw_folder_subtract_3frame, width_t2, height_t2)
    print("Reconstruct all raw frames - done")

    # convert back the frames to video
    png_to_video(raw_folder_subtract_3frame, "test2_output.mp4", fps=30)
    print("convert back the frames to video - done")

    ###### TEST3 #######
    frames_folder_t3 = 'simulations/Testcases/test3'
    video_test3_path = 'simulations/Testcases/test3/Different Ball Bounce Animation in Maya.mp4'
    extract_frames(video_test3_path, frames_folder_t3)
    convert_png_to_raw(frames_folder_t3)

    # Detect width and height from an original image
    example_png_t3 = os.path.join(frames_folder_t3, 'frame_000.png')
    img_t3 = Image.open(example_png_t3)
    width_t3, height_t3 = img_t3.size

    # Define raw folder before using it
    raw_folder = os.path.join(frames_folder_t3, 'raw_rbg32')
    raw_folder_subtract_3frame = os.path.join(raw_folder, 'background_and_3frames') # subt
    print("Define raw folder before using it - done")

    # Run motion simulation
    # background_and_3frames(raw_folder, width_t3, height_t3, shift=4, threshold=30)
    background_and_3frames_grayscale(raw_folder, width_t3, height_t3, shift=4, threshold=15)
    print("Run motion simulation - done")

    # Reconstruct all raw frames
    convert_all_raw_to_png(raw_folder_subtract_3frame, width_t3, height_t3)
    print("Reconstruct all raw frames - done")

    # convert back the frames to video
    png_to_video(raw_folder_subtract_3frame, "test3_output.mp4", fps=30)
    print("convert back the frames to video - done")

    ###### TEST4 #######
    frames_folder_t4 = 'simulations/Testcases/test4'
    video_test4_path = 'simulations/Testcases/test4/videoplayback.mp4'
    extract_frames(video_test4_path, frames_folder_t4)
    convert_png_to_raw(frames_folder_t4)

    # Detect width and height from an original image
    example_png_t4 = os.path.join(frames_folder_t4, 'frame_000.png')
    img_t4 = Image.open(example_png_t4)
    width_t4, height_t4 = img_t4.size

    # Define raw folder before using it
    raw_folder = os.path.join(frames_folder_t4, 'raw_rbg32')
    raw_folder_subtract_3frame = os.path.join(raw_folder, 'background_and_3frames') # subt
    print("Define raw folder before using it - done")

    # Run motion simulation
    # background_and_3frames(raw_folder, width_t4, height_t4, shift=4, threshold=50)
    background_and_3frames_grayscale(raw_folder, width_t4, height_t4, shift=4, threshold=15)
    print("Run motion simulation - done")

    # Reconstruct all raw frames
    convert_all_raw_to_png(raw_folder_subtract_3frame, width_t4, height_t4)
    print("Reconstruct all raw frames - done")

    # convert back the frames to video
    png_to_video(raw_folder_subtract_3frame, "test4_output.mp4", fps=30)
    print("convert back the frames to video - done")


if __name__ == '__main__':
    main()
