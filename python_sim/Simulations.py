from PIL import Image
import subprocess
import time
import os
import glob
import numpy as np
import cv2
import os
from sklearn.metrics import precision_score, recall_score, f1_score

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

def save_rgb_frame_as_raw(output_frame, width, height, output_folder, base_filename, frame_idx):
    output_path = os.path.join(output_folder, f"{base_filename}_{frame_idx:04d}.raw")
    with open(output_path, 'wb') as f:
        for y in range(height):
            for x in range(width):
                r, b, g = output_frame[y, x]
                f.write(bytes([r, b, g, 0]))

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

def filter_motion_box_manual(motion_map, min_neighbors=5):
    height, width = motion_map.shape
    filtered = np.zeros_like(motion_map, dtype=bool)
    for y in range(1, height - 1):
        for x in range(1, width - 1):
            neighborhood = motion_map[y - 1:y + 2, x - 1:x + 2]
            if np.sum(neighborhood) >= min_neighbors:
                filtered[y, x] = True
    return filtered

def sigma_delta_motion_detection(raw_folder, width, height, highlight_color=(255, 0, 0)):

    raw_files = sorted(glob.glob(os.path.join(raw_folder, '*.raw')))
    if len(raw_files) < 2:
        print("❌ Not enough frames.")
        return

    output_folder = os.path.join(raw_folder, 'sigma_delta')
    os.makedirs(output_folder, exist_ok=True)

    background = None  # M(t)
    variation = None   # V(t)
    gray_prev = None   # for 2-frame differencing

    diff2_threshold = 8 # Tune as needed

    for frame_idx, raw_path in enumerate(raw_files):
        with open(raw_path, 'rb') as f:
            raw_bytes = f.read()

        # Parse RGB
        frame = np.zeros((height, width, 3), dtype=np.uint8)
        byte_idx = 0
        for y in range(height):
            for x in range(width):
                r = raw_bytes[byte_idx]
                b = raw_bytes[byte_idx + 1]
                g = raw_bytes[byte_idx + 2]
                frame[y, x] = [r, b, g]
                byte_idx += 4

        # Convert to grayscale (luminosity)
        r = frame[:, :, 0].astype(np.uint16)
        g = frame[:, :, 1].astype(np.uint16)
        b = frame[:, :, 2].astype(np.uint16)
        gray = ((77 * r + 150 * g + 29 * b) >> 8).astype(np.uint8)
        
        # gray = filter_motion_median_manual(gray)


        if background is None:
            background = gray.copy()
            variation = np.full_like(gray, 2, dtype=np.uint8)
            gray_prev = gray.copy()
            continue

        # Step 1: Update background M(t)
        background[gray > background] += 1
        background[gray < background] -= 1

        # Step 2: Compute |I - M| and variation
        diff = np.abs(gray.astype(np.int16) - background.astype(np.int16)).astype(np.uint8)

        variation[diff > variation] += 2
        variation[diff < variation] -= 2
        variation = np.clip(variation, 2, 255)

        motion_sigma = diff >= variation

        # Step 3: 2-frame difference
        diff2 = np.abs(gray.astype(np.int16) - gray_prev.astype(np.int16)).astype(np.uint8)
        motion_diff2 = diff2 > diff2_threshold

        # Step 4: Combine both detections
        motion_map = motion_sigma & motion_diff2

        # Optional: box filter
        motion_map = filter_motion_box_manual(motion_map, min_neighbors=4)
        # motion_map = hardware_friendly_closing(motion_map)
        # motion_map = filter_motion_median_manual(motion_map)


        # # Step 5: Overlay motion on frame
        output_frame = frame.copy()
        # output_frame[motion_map] = highlight_color
        
        # # Find bounding box of motion
        # ys, xs = np.where(motion_map)
        # if len(xs) > 0 and len(ys) > 0:
        #     x_min, x_max = np.min(xs), np.max(xs)
        #     y_min, y_max = np.min(ys), np.max(ys)

        #     # Draw bounding box (top, bottom, left, right)
        #     output_frame[y_min:y_max+1, x_min] = highlight_color         # Left edge
        #     output_frame[y_min:y_max+1, x_max] = highlight_color         # Right edge
        #     output_frame[y_min, x_min:x_max+1] = highlight_color         # Top edge
        #     output_frame[y_max, x_min:x_max+1] = highlight_color         # Bottom edge
        
        boxes = find_bounding_boxes_hw_friendly_with_merge_and_eviction(motion_map, min_pixels=50, max_boxes=20)
        for (x_min, y_min, x_max, y_max) in boxes:
            # if (x_max - x_min) * (y_max - y_min) > 50:  # optional area filter
                output_frame[y_min:y_max+1, x_min] = highlight_color
                output_frame[y_min:y_max+1, x_max] = highlight_color
                output_frame[y_min, x_min:x_max+1] = highlight_color
                output_frame[y_max, x_min:x_max+1] = highlight_color




        # Save result
        save_rgb_frame_as_raw(
            output_frame=output_frame,
            width=width,
            height=height,
            output_folder=output_folder,
            base_filename="sigma_delta",
            frame_idx=frame_idx
        )
        
        np.save(os.path.join(output_folder, f"motion_map_{frame_idx:03}.npy"), motion_map.astype(np.uint8))


        gray_prev = gray.copy()

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
        # adaptive_threshold = 8

        # Motion detection map
        motion_map = (D1 > adaptive_threshold) & (D2 > adaptive_threshold) & (bg_diff > adaptive_threshold)

        # Apply 3x3 box filtering
        motion_map = filter_motion_box_manual(motion_map, min_neighbors=5)
        
        # Overlay on original RGB frame
        output_frame = frame_buffer[1].copy()
        output_frame[motion_map] = highlight_color

        save_rgb_frame_as_raw(
            output_frame=output_frame,
            width=width,
            height=height,
            output_folder=output_folder,
            base_filename="subt_3frame",
            frame_idx=frame_idx-1
        )
        
        np.save(os.path.join(output_folder, f"motion_map_{frame_idx-1:03}.npy"), motion_map.astype(np.uint8))


        # Background update
        background = np.clip(
            background.astype(np.int32) - (background >> shift) + (gray_frame.astype(np.int32) >> shift),
            0, 255
        ).astype(np.uint8)
        
        # Keep sliding window of last 3 frames
        frame_buffer.pop(0)
        gray_buffer.pop(0) 
 
def evaluate_motion_map(motion_map, expected_mask_path):
    expected_mask = np.array(Image.open(expected_mask_path).convert('L'))
    expected_binary = (expected_mask > 127).astype(np.uint8).flatten()
    predicted_binary = (motion_map > 0).astype(np.uint8).flatten()

    # print(f"[DEBUG] Frame sums — Expected: {expected_binary.sum()}, Predicted: {predicted_binary.sum()}")

    if expected_binary.sum() == 0 and predicted_binary.sum() <= 5:
        return 1.0, 1.0, 1.0

    precision = precision_score(expected_binary, predicted_binary, zero_division=0)
    recall = recall_score(expected_binary, predicted_binary, zero_division=0)
    f1 = f1_score(expected_binary, predicted_binary, zero_division=0)

    return precision, recall, f1

def evaluate_all_motion_maps(motion_map_folder, ground_truth_folder, num_frames):
    precisions, recalls, f1s = [], [], []

    for i in range(num_frames):
        motion_map_path = os.path.join(motion_map_folder, f"motion_map_{i:03}.npy")
        ground_truth_path = os.path.join(ground_truth_folder, f"mask_{i:03}.png")

        if not os.path.exists(motion_map_path) or not os.path.exists(ground_truth_path):
            print(f"Skipping frame {i} (missing mask or map)")
            continue

        motion_map = np.load(motion_map_path)
        precision, recall, f1 = evaluate_motion_map(motion_map, ground_truth_path)

        precisions.append(precision)
        recalls.append(recall)
        f1s.append(f1)

        # print(f"Frame {i:03} — Precision: {precision:.2f}, Recall: {recall:.2f}, F1: {f1:.2f}")

    print(f"\n🎯 AVERAGE over {len(precisions)} frames:")
    print(f"Precision: {np.mean(precisions):.2f}")
    print(f"Recall:    {np.mean(recalls):.2f}")
    print(f"F1 Score:  {np.mean(f1s):.2f}")

def convert_bmp_to_raw(frames_folder):
    output_folder = os.path.join(frames_folder, 'raw_rbg32')
    os.makedirs(output_folder, exist_ok=True)

    frame_paths = sorted(glob.glob(os.path.join(frames_folder, '*.bmp')))

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

def convert_jpg_to_raw(frames_folder):
    output_folder = os.path.join(frames_folder, 'raw_rbg32')
    os.makedirs(output_folder, exist_ok=True)

    frame_paths = sorted([f for f in os.listdir(frames_folder) if f.lower().endswith(".jpg")])

    for filename in frame_paths:
        path = os.path.join(frames_folder, filename)
        img = Image.open(path).convert('RGB')
        width, height = img.size
        pixels = img.load()

        raw_bytes = bytearray()
        for y in range(height):
            for x in range(width):
                r, g, b = pixels[x, y]
                raw_bytes.extend([r, b, g, 0x00])  # R, B, G, 0 format

        frame_index = int(''.join(filter(str.isdigit, filename)))  # extract number from filename
        output_path = os.path.join(output_folder, f"frame_{frame_index:03}.raw")

        with open(output_path, 'wb') as f:
            f.write(raw_bytes)
    
def sigma_delta_motion_detection_3frames(raw_folder, width, height, highlight_color=(255, 0, 0)):

    raw_files = sorted(glob.glob(os.path.join(raw_folder, '*.raw')))
    if len(raw_files) < 3:
        print("❌ Not enough frames for 3-frame differencing.")
        return

    output_folder = os.path.join(raw_folder, 'sigma_delta_3frames')
    os.makedirs(output_folder, exist_ok=True)

    background = None  # M(t)
    variation = None   # V(t)
    gray_prev1 = None  # G(t-1)
    gray_prev2 = None  # G(t-2)

    diff3_threshold = 8  # Tune as needed

    for frame_idx, raw_path in enumerate(raw_files):
        with open(raw_path, 'rb') as f:
            raw_bytes = f.read()

        # Parse RGB
        frame = np.zeros((height, width, 3), dtype=np.uint8)
        byte_idx = 0
        for y in range(height):
            for x in range(width):
                r = raw_bytes[byte_idx]
                b = raw_bytes[byte_idx + 1]
                g = raw_bytes[byte_idx + 2]
                frame[y, x] = [r, b, g]
                byte_idx += 4

        # Convert to grayscale (luminosity)
        r = frame[:, :, 0].astype(np.uint16)
        g = frame[:, :, 1].astype(np.uint16)
        b = frame[:, :, 2].astype(np.uint16)
        gray = ((77 * r + 150 * g + 29 * b) >> 8).astype(np.uint8)

        if background is None:
            background = gray.copy()
            variation = np.full_like(gray, 2, dtype=np.uint8)
            gray_prev1 = gray.copy()
            gray_prev2 = gray.copy()
            continue

        # Step 1: Update background M(t)
        background[gray > background] += 1
        background[gray < background] -= 1

        # Step 2: Compute |I - M| and variation
        diff = np.abs(gray.astype(np.int16) - background.astype(np.int16)).astype(np.uint8)

        variation[diff > variation] += 2
        variation[diff < variation] -= 2
        variation = np.clip(variation, 2, 255)

        motion_sigma = diff >= variation

        # Step 3: 3-frame difference (second derivative)
        diff3 = np.abs((gray.astype(np.int16) - 2 * gray_prev1.astype(np.int16) + gray_prev2.astype(np.int16)))
        motion_diff3 = diff3 > diff3_threshold

        # Step 4: Combine both detections
        motion_map = motion_sigma & motion_diff3

        # Optional: box filter
        motion_map = filter_motion_box_manual(motion_map, min_neighbors=5)

        # Step 5: Overlay motion on frame
        output_frame = frame.copy()
        output_frame[motion_map] = highlight_color

        # Save result
        save_rgb_frame_as_raw(
            output_frame=output_frame,
            width=width,
            height=height,
            output_folder=output_folder,
            base_filename="sigma_delta",
            frame_idx=frame_idx
        )
        
        np.save(os.path.join(output_folder, f"motion_map_{frame_idx:03}.npy"), motion_map.astype(np.uint8))

        # Update history
        gray_prev2 = gray_prev1.copy()
        gray_prev1 = gray.copy()
    
def compute_gradients(img1, img2):
    sobel_x = np.array([[-1, 0, 1],
                        [-2, 0, 2],
                        [-1, 0, 1]], dtype=np.int16)
    sobel_y = np.array([[-1, -2, -1],
                        [ 0,  0,  0],
                        [ 1,  2,  1]], dtype=np.int16)

    I_x = cv2.filter2D(img1, cv2.CV_16S, sobel_x)
    I_y = cv2.filter2D(img1, cv2.CV_16S, sobel_y)
    I_t = (img2.astype(np.int16) - img1.astype(np.int16))

    return I_x, I_y, I_t

def lucas_kanade_flow(prev_gray, gray, motion_magnitude_threshold):
    I_x, I_y, I_t = compute_gradients(prev_gray, gray)

    h, w = gray.shape
    motion_map = np.zeros((h, w), dtype=np.uint8)

    for y in range(1, h-1):
        for x in range(1, w-1):
            Ix_patch = I_x[y-1:y+2, x-1:x+2].flatten()
            Iy_patch = I_y[y-1:y+2, x-1:x+2].flatten()
            It_patch = I_t[y-1:y+2, x-1:x+2].flatten()

            A = np.vstack((Ix_patch, Iy_patch)).T  # (9,2)
            b = -It_patch.reshape(-1, 1)            # (9,1)

            ATA = A.T @ A
            ATb = A.T @ b

            # Determinant check to avoid singularity
            if np.linalg.det(ATA) >= 1e-4:
                v = np.linalg.inv(ATA) @ ATb
                vx, vy = v[0,0], v[1,0]
                magnitude = np.sqrt(vx**2 + vy**2)
                if magnitude > motion_magnitude_threshold:
                    motion_map[y, x] = 1

    return motion_map

def optical_flow_motion_detection(raw_folder, width, height, highlight_color=(255, 0, 0)):

    raw_files = sorted(glob.glob(os.path.join(raw_folder, '*.raw')))
    if len(raw_files) < 2:
        print("❌ Not enough frames for Optical Flow.")
        return

    output_folder = os.path.join(raw_folder, 'optical_flow')
    os.makedirs(output_folder, exist_ok=True)

    prev_gray = None
    motion_magnitude_threshold = 2.0  # Flow vector magnitude threshold

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
                frame[y, x] = [r, g, b]  # Correct RGB order
                byte_idx += 4

        gray = cv2.cvtColor(frame, cv2.COLOR_RGB2GRAY)

        if prev_gray is None:
            prev_gray = gray.copy()
            continue

        # Use Lucas-Kanade optical flow
        motion_map = lucas_kanade_flow(prev_gray, gray, motion_magnitude_threshold)

        # Optional: median filter motion map to remove noise
        # motion_map = apply_median_filter(motion_map)

        # Highlight detected motion
        output_frame = frame.copy()
        output_frame[motion_map == 1] = highlight_color

        # Save output
        save_rgb_frame_as_raw(
            output_frame=output_frame,
            width=width,
            height=height,
            output_folder=output_folder,
            base_filename="optical_flow",
            frame_idx=frame_idx
        )

        np.save(os.path.join(output_folder, f"motion_map_{frame_idx:03}.npy"), motion_map)

        # Update previous frame
        prev_gray = gray.copy()

def filter_motion_median_manual(motion_map):
    """
    Apply an optimized 3x3 median filter on a binary motion_map (0/1 or False/True).
    """
    height, width = motion_map.shape
    filtered = np.copy(motion_map)

    for y in range(1, height-1):
        for x in range(1, width-1):
            window = [
                motion_map[y-1, x-1], motion_map[y-1, x], motion_map[y-1, x+1],
                motion_map[y  , x-1], motion_map[y  , x], motion_map[y  , x+1],
                motion_map[y+1, x-1], motion_map[y+1, x], motion_map[y+1, x+1],
            ]
            window = [int(v) for v in window]  # Ensure 0/1 values
            filtered[y,x] = median_filter_3x3_window(window)

    return filtered

def hardware_friendly_closing(motion_map):
    """
    Simulate hardware-friendly 3x3 closing: dilation then erosion.
    Input: motion_map (2D np.array, dtype=bool or uint8)
    Output: closed_map (same shape)
    """

    # Ensure input is binary (0 or 1)
    motion_map = (motion_map > 0).astype(np.uint8)

    # Define 3x3 kernel
    kernel = np.ones((3, 3), np.uint8)

    # Step 1: Dilation (expand motion regions)
    dilated = cv2.dilate(motion_map, kernel, iterations=1)

    # Step 2: Erosion (shrink back to solidify shapes)
    closed = cv2.erode(dilated, kernel, iterations=1)

    # Return as boolean map
    return closed > 0

def median_filter_3x3_window(pixels):
    a = list(pixels)

    def swap(i, j):
        if a[i] > a[j]:
            a[i], a[j] = a[j], a[i]

    swap(0,1); swap(3,4); swap(6,7)
    swap(1,2); swap(4,5); swap(7,8)
    swap(0,1); swap(3,4); swap(6,7)
    swap(0,3); swap(1,4); swap(2,5)
    swap(3,6); swap(4,7); swap(5,8)
    swap(1,3); swap(2,4); swap(5,7)
    swap(2,3); swap(5,6)

    return a[4]

def sigma_delta_motion_detection_improved(raw_folder, width, height, highlight_color=(255, 0, 0)):
    raw_files = sorted(glob.glob(os.path.join(raw_folder, '*.raw')))
    if len(raw_files) < 2:
        print("❌ Not enough frames.")
        return

    output_folder = os.path.join(raw_folder, 'sigma_delta_improved')
    os.makedirs(output_folder, exist_ok=True)

    background = None
    variation = None
    gray_prev = None

    for frame_idx, raw_path in enumerate(raw_files):
        with open(raw_path, 'rb') as f:
            raw_bytes = f.read()

        # Parse RGB
        frame = np.zeros((height, width, 3), dtype=np.uint8)
        byte_idx = 0
        for y in range(height):
            for x in range(width):
                r = raw_bytes[byte_idx]
                b = raw_bytes[byte_idx + 1]
                g = raw_bytes[byte_idx + 2]
                frame[y, x] = [r, b, g]
                byte_idx += 4

        # Convert to grayscale
        r = frame[:, :, 0].astype(np.uint16)
        g = frame[:, :, 1].astype(np.uint16)
        b = frame[:, :, 2].astype(np.uint16)
        gray = ((77 * r + 150 * g + 29 * b) >> 8).astype(np.uint8)

        if background is None:
            background = gray.copy()
            variation = np.full_like(gray, 2, dtype=np.uint8)
            gray_prev = gray.copy()
            continue

        #### Step 1: Dynamic Background Update
        diff = np.abs(gray.astype(np.int16) - background.astype(np.int16)).astype(np.uint8)

        # Dynamic learning rate
        small_diff_mask = diff < 10
        large_diff_mask = diff > 30

        update_amount = (small_diff_mask * 1 + large_diff_mask * 2).astype(np.uint8)
        background[gray > background] = np.clip(background[gray > background] + update_amount[gray > background], 0, 255)
        background[gray < background] = np.clip(background[gray < background] - update_amount[gray < background], 0, 255)

        #### Step 2: Smarter Sigma-Delta Variation Update
        # Smarter Sigma-Delta Variation Update
        variation = variation.astype(np.int16)
        variation += ((diff > variation) * 4 - (diff < variation) * 1)
        variation = np.clip(variation, 2, 255).astype(np.uint8)


        #### Step 3: 2-Frame Differencing with Adaptive Threshold
        diff2 = np.abs(gray.astype(np.int16) - gray_prev.astype(np.int16)).astype(np.uint8)
        adaptive_diff2_threshold = np.clip((background // 16) + 4, 4, 20)
        motion_diff2 = diff2 > adaptive_diff2_threshold

        #### Step 4: Combine Sigma-Delta and 2-Frame Differencing
        motion_sigma = diff >= variation
        motion_map = motion_sigma & motion_diff2

        #### Step 5: Morphological Cleaning
        motion_map = hardware_friendly_closing(motion_map)
        # motion_map = filter_motion_box_manual(motion_map, min_neighbors=3)
        

        #### Step 6: Overlay Motion
        output_frame = frame.copy()
        output_frame[motion_map] = highlight_color

        #### Step 7: Save Outputs
        output_raw_path = os.path.join(output_folder, f"sigma_delta_{frame_idx:04}.raw")
        with open(output_raw_path, 'wb') as f_out:
            for y in range(height):
                for x in range(width):
                    r, b, g = output_frame[y, x]
                    f_out.write(bytes([r, b, g, 0]))

        # Save binary motion map for evaluation
        np.save(os.path.join(output_folder, f"motion_map_{frame_idx:03}.npy"), motion_map.astype(np.uint8))

        #### Step 8: Update Previous Frame
        gray_prev = gray.copy()

def test(current_test,frames_folder,ground_truth_folder,num_frames):
    convert_bmp_to_raw(frames_folder)

    # Detect width and height
    example_png = os.path.join(frames_folder, 'frame_000.bmp')
    img = Image.open(example_png)
    width, height = img.size

    # Prepare paths
    raw_folder = os.path.join(frames_folder, 'raw_rbg32')
    output_folder = os.path.join(raw_folder, current_test)
    os.makedirs(output_folder, exist_ok=True)

    # Run motion simulation
    if(current_test == 'sigma_delta'):
        sigma_delta_motion_detection(
            raw_folder=raw_folder,
            width=width,
            height=height,
            highlight_color=(255, 0, 0)
        )
    elif(current_test == 'background_and_3frames'):
        background_and_3frames_grayscale(raw_folder, width, height, shift=4, threshold=15)
    elif(current_test == 'sigma_delta_3frames'):
        sigma_delta_motion_detection_3frames(
            raw_folder=raw_folder,
            width=width,
            height=height,
            highlight_color=(255, 0, 0)
        )
    elif(current_test == 'optical_flow'):
        optical_flow_motion_detection(
            raw_folder=raw_folder,
            width=width,
            height=height,
            highlight_color=(255, 0, 0)
        )
    elif(current_test == 'sigma_delta_improved'):
        sigma_delta_motion_detection_improved(
            raw_folder=raw_folder,
            width=width,
            height=height,
            highlight_color=(255, 0, 0)
        )


    # Convert output to PNG
    convert_all_raw_to_png(output_folder, width, height)
    
    # convert back the frames to video
    video_folder = os.path.join(frames_folder, 'test_output.mp4')
    png_to_video(output_folder, video_folder, fps=30)
    
    evaluate_all_motion_maps(
    motion_map_folder=os.path.join(raw_folder, current_test),
    ground_truth_folder=ground_truth_folder,
    num_frames=num_frames
    )
 
 

def find_bounding_boxes_hw_friendly_with_merge_and_eviction(motion_map, min_pixels=20, max_boxes=8):
    height, width = motion_map.shape
    boxes = np.zeros((max_boxes, 4), dtype=np.int16)  # [x_min, y_min, x_max, y_max]
    box_valid = np.zeros(max_boxes, dtype=bool)

    for y in range(height):
        x = 0
        while x < width:
            if motion_map[y, x]:
                x_start = x
                while x < width and motion_map[y, x]:
                    x += 1
                x_end = x - 1

                merged = False
                for i in range(max_boxes):
                    if not box_valid[i]:
                        continue
                    bx_min, by_min, bx_max, by_max = boxes[i]
                    if x_start <= bx_max and x_end >= bx_min and y <= by_max + 1:
                        boxes[i, 0] = min(bx_min, x_start)
                        boxes[i, 1] = min(by_min, y)
                        boxes[i, 2] = max(bx_max, x_end)
                        boxes[i, 3] = max(by_max, y)
                        merged = True
                        break

                if not merged:
                    inserted = False
                    for i in range(max_boxes):
                        if not box_valid[i]:
                            boxes[i] = [x_start, y, x_end, y]
                            box_valid[i] = True
                            inserted = True
                            break
                    if not inserted:
                        # All boxes full — evict smallest if new box is larger
                        new_area = (x_end - x_start + 1)
                        min_area = float('inf')
                        min_idx = -1
                        for i in range(max_boxes):
                            if box_valid[i]:
                                bx_min, by_min, bx_max, by_max = boxes[i]
                                area = (bx_max - bx_min + 1) * (by_max - by_min + 1)
                                if area < min_area:
                                    min_area = area
                                    min_idx = i
                        if new_area > min_area and min_idx >= 0:
                            boxes[min_idx] = [x_start, y, x_end, y]

            else:
                x += 1

    final_boxes = []
    for i in range(max_boxes):
        if box_valid[i]:
            x_min, y_min, x_max, y_max = boxes[i]
            area = (x_max - x_min + 1) * (y_max - y_min + 1)
            if area >= min_pixels:
                final_boxes.append((x_min, y_min, x_max, y_max))

    return final_boxes




 
def main():
    selected_algorithm = 'sigma_delta'  # Change here if you want to run another algorithm

    test_cases = [
        ('test1',  300),
        ('test2',  272),
        ('test3',  525),
        ('test4',  300),
        ('test5',  225),
        ('test6',  250),
        ('test7',  250),
        ('test8',  300),
        ('test9',  275),
        ('test10', 400)
    ]

    for test_name, num_frames in test_cases:
        print(f"\n🔍 Running {test_name.upper()} with {selected_algorithm}")
        test(
            current_test=selected_algorithm,
            frames_folder=f'simulations/Testcases/{test_name}',
            ground_truth_folder=f'simulations/Testcases/{test_name}/ground_truth',
            num_frames=num_frames
        )
    
    
if __name__ == '__main__':
    main()
