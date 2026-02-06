from PIL import Image
import os
import glob
import re
import numpy as np
import cv2
from sklearn.metrics import precision_score, recall_score, f1_score

RAW_ORDER = "RGB0"

def ensure_dir(path):
    """Create a directory if it does not already exist."""
    os.makedirs(path, exist_ok=True)


def extract_number(filename, regex, default=-1):
    """Extract the first numeric group using a regex; return default if missing."""
    match = re.search(regex, os.path.basename(filename))
    return int(match.group(1)) if match else default


def sorted_files(pattern, number_regex=None, default=-1):
    """Return a sorted list of files, optionally using a numeric sort key."""
    files = glob.glob(pattern)
    if number_regex:
        files.sort(key=lambda p: extract_number(p, number_regex, default))
    else:
        files.sort()
    return files


def _order_to_indices(order):
    """Map channel letters (R, G, B) to indices in a 4-byte pixel order."""
    if len(order) != 4:
        raise ValueError("order must be 4 chars like 'RGB0' or 'RBG0'")
    idx = {}
    for ch in "RGB":
        if ch not in order:
            raise ValueError("order must include R, G, B")
        idx[ch] = order.index(ch)
    return idx


def raw_bytes_to_rgb(raw_bytes, width, height, order="RGB0"):
    """Convert raw bytes (4 bytes per pixel) into packed RGB bytes."""
    expected = width * height * 4
    if len(raw_bytes) != expected:
        raise ValueError(f"Unexpected raw size: {len(raw_bytes)} bytes, expected {expected}")

    idx = _order_to_indices(order)
    rgb_data = bytearray()
    for i in range(0, len(raw_bytes), 4):
        base = i
        rgb_data.extend([
            raw_bytes[base + idx["R"]],
            raw_bytes[base + idx["G"]],
            raw_bytes[base + idx["B"]],
        ])
    return bytes(rgb_data)


def raw_bytes_to_frame(raw_bytes, width, height, order=RAW_ORDER):
    """Convert raw bytes (4 bytes per pixel) into an HxWx3 RGB frame."""
    expected = width * height * 4
    if len(raw_bytes) != expected:
        raise ValueError(f"Unexpected raw size: {len(raw_bytes)} bytes, expected {expected}")

    idx = _order_to_indices(order)
    data = np.frombuffer(raw_bytes, dtype=np.uint8).reshape((height * width, 4))
    rgb = data[:, [idx["R"], idx["G"], idx["B"]]]
    return rgb.reshape((height, width, 3))


def raw_to_png(raw_path, png_path, width, height, order="RGB0"):
    """Convert a raw frame file into a PNG image."""
    with open(raw_path, "rb") as f:
        raw_bytes = f.read()
    rgb_bytes = raw_bytes_to_rgb(raw_bytes, width, height, order=order)
    img = Image.frombytes("RGB", (width, height), rgb_bytes)
    img.save(png_path)


def convert_all_raw_to_png(raw_folder, width, height, order="RGB0", suffix="_reconstructed.png"):
    """Convert all raw files in a folder to PNG images."""
    raw_files = sorted_files(os.path.join(raw_folder, "*.raw"))
    for raw_path in raw_files:
        output_png = raw_path.replace(".raw", suffix)
        try:
            raw_to_png(raw_path, output_png, width, height, order=order)
        except ValueError as exc:
            print(f"Skipping {raw_path}: {exc}")


def save_rgb_frame_as_raw(output_frame, width, height, output_folder, base_filename, frame_idx,
                          order="RGB0", index_width=3):
    """Save an RGB frame to a raw file with a configurable byte order."""
    ensure_dir(output_folder)
    raw_path = os.path.join(output_folder, f"{base_filename}_{frame_idx:0{index_width}d}.raw")

    with open(raw_path, "wb") as f:
        for y in range(height):
            for x in range(width):
                r, g, b = output_frame[y, x]
                pixels = {"R": r, "G": g, "B": b, "0": 0}
                f.write(bytes([
                    pixels[order[0]],
                    pixels[order[1]],
                    pixels[order[2]],
                    pixels[order[3]],
                ]))


def convert_images_to_raw(frames_folder, ext, order="RGB0", output_folder=None):
    """Convert all images with extension ext in a folder into raw frames."""
    if output_folder is None:
        output_folder = os.path.join(frames_folder, "raw_rbg32")
    ensure_dir(output_folder)

    frame_paths = sorted_files(os.path.join(frames_folder, f"*.{ext}"))
    for path in frame_paths:
        img = Image.open(path).convert("RGB")
        width, height = img.size
        pixels = img.load()

        raw_bytes = bytearray()
        for y in range(height):
            for x in range(width):
                r, g, b = pixels[x, y]
                pmap = {"R": r, "G": g, "B": b, "0": 0}
                raw_bytes.extend([
                    pmap[order[0]],
                    pmap[order[1]],
                    pmap[order[2]],
                    pmap[order[3]],
                ])

        filename = os.path.splitext(os.path.basename(path))[0]
        output_path = os.path.join(output_folder, f"{filename}.raw")
        with open(output_path, "wb") as f:
            f.write(raw_bytes)


def pngs_to_video(frames_folder, output_path, fps=30, pattern="*.png", number_regex=None):
    """Create a video from PNG frames in a folder."""
    frame_files = sorted_files(os.path.join(frames_folder, pattern), number_regex=number_regex, default=float("inf"))
    if not frame_files:
        print("No PNG files found.")
        return

    first = cv2.imread(frame_files[0])
    h, w, _ = first.shape
    fourcc = cv2.VideoWriter_fourcc(*"mp4v")
    out = cv2.VideoWriter(output_path, fourcc, fps, (w, h))

    for fn in frame_files:
        frame = cv2.imread(fn)
        out.write(frame)
    out.release()
    print(f"Video saved to: {output_path}")


def hardware_friendly_closing(motion_map):
    """Apply a 3x3 morphological closing on a binary motion map."""
    kernel = np.ones((3, 3), np.uint8)
    mm8 = (motion_map.astype(np.uint8) * 255)
    closed = cv2.morphologyEx(mm8, cv2.MORPH_CLOSE, kernel)
    return (closed > 0)

def extract_frames(video_path, output_folder, prefix="frame"):
    """Extract video frames into PNG files."""
    os.makedirs(output_folder, exist_ok=True)

    cap = cv2.VideoCapture(video_path)
    frame_idx = 0

    if not cap.isOpened():
        print("Error: Cannot open video.")
        return

    while True:
        ret, frame = cap.read()
        if not ret:
            break

        filename = f"{prefix}_{frame_idx:03}.png"
        path = os.path.join(output_folder, filename)
        cv2.imwrite(path, frame)
        # print(f" Saved: {path}")
        frame_idx += 1

    cap.release()
    # print(f\"Done. Extracted {frame_idx} frames to {output_folder}\")

def png_to_video(frames_folder, output_path, fps=30):
    pngs_to_video(frames_folder, output_path, fps=fps, pattern="*.png")

def convert_png_to_raw(frames_folder):
    """Convert PNG frames to raw files using RGB0 byte order."""
    output_folder = os.path.join(frames_folder, 'raw_rbg32')
    convert_images_to_raw(frames_folder, ext="png", order=RAW_ORDER, output_folder=output_folder)

def filter_motion_box_manual(motion_map, min_neighbors=5):
    """Apply a 3x3 neighbor count filter to suppress isolated motion pixels."""
    height, width = motion_map.shape
    filtered = np.zeros_like(motion_map, dtype=bool)
    for y in range(1, height - 1):
        for x in range(1, width - 1):
            neighborhood = motion_map[y - 1:y + 2, x - 1:x + 2]
            if np.sum(neighborhood) >= min_neighbors:
                filtered[y, x] = True
    return filtered

def sigma_delta_motion_detection(raw_folder, width, height, highlight_color=(255, 0, 0), progress_every=25):
    """Sigma-delta motion detection with frame differencing and box filtering."""

    raw_files = sorted(glob.glob(os.path.join(raw_folder, '*.raw')))
    if len(raw_files) < 2:
        print("Not enough frames.")
        return
    total_frames = len(raw_files)
    if progress_every and progress_every > 0:
        print(f"[sigma_delta] Processing {total_frames} frames from {raw_folder}")

    output_folder = os.path.join(raw_folder, 'sigma_delta')
    os.makedirs(output_folder, exist_ok=True)

    background = None  # M(t)
    variation = None   # V(t)
    gray_prev = None   # for 2-frame differencing

    diff2_threshold = 8 # Tune as needed

    for frame_idx, raw_path in enumerate(raw_files):
        with open(raw_path, 'rb') as f:
            raw_bytes = f.read()

        # Parse RGB (matches hardware input: {R,G,B,0})
        frame = raw_bytes_to_frame(raw_bytes, width, height, order=RAW_ORDER)

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
            if progress_every and (frame_idx % progress_every == 0 or frame_idx == total_frames - 1):
                print(f"[sigma_delta] {frame_idx + 1}/{total_frames} frames processed", flush=True)
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

        if progress_every and (frame_idx % progress_every == 0 or frame_idx == total_frames - 1):
            print(f"[sigma_delta] {frame_idx + 1}/{total_frames} frames processed", flush=True)

def background_and_3frames_grayscale(raw_folder, width, height, shift=4, threshold=15, highlight_color=(255, 0, 0)):
    """Background update with 3-frame differencing in grayscale."""
    raw_files = sorted(glob.glob(os.path.join(raw_folder, '*.raw')))
    if len(raw_files) < 3:
        print("Not enough frames for 2-frame differencing.")
        return

    output_folder = os.path.join(raw_folder, 'background_and_3frames')
    os.makedirs(output_folder, exist_ok=True)

    frame_buffer = []
    gray_buffer = []
    background = None

    for frame_idx, raw_path in enumerate(raw_files):
        with open(raw_path, 'rb') as f:
            raw_bytes = f.read()

        frame = raw_bytes_to_frame(raw_bytes, width, height, order=RAW_ORDER)

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
    """Return precision/recall/F1 for a single motion map against a mask image."""
    expected_mask = np.array(Image.open(expected_mask_path).convert('L'))
    expected_binary = (expected_mask > 127).astype(np.uint8).flatten()
    predicted_binary = (motion_map > 0).astype(np.uint8).flatten()

    # print(f"[DEBUG] Frame sums - Expected: {expected_binary.sum()}, Predicted: {predicted_binary.sum()}")

    if expected_binary.sum() == 0 and predicted_binary.sum() <= 5:
        return 1.0, 1.0, 1.0

    precision = precision_score(expected_binary, predicted_binary, zero_division=0)
    recall = recall_score(expected_binary, predicted_binary, zero_division=0)
    f1 = f1_score(expected_binary, predicted_binary, zero_division=0)

    return precision, recall, f1

def evaluate_all_motion_maps(motion_map_folder, ground_truth_folder, num_frames):
    """Evaluate a sequence of motion maps against ground truth masks."""
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

        # print(f"Frame {i:03} - Precision: {precision:.2f}, Recall: {recall:.2f}, F1: {f1:.2f}")

    print(f"\n AVERAGE over {len(precisions)} frames:")
    print(f"Precision: {np.mean(precisions):.2f}")
    print(f"Recall:    {np.mean(recalls):.2f}")
    print(f"F1 Score:  {np.mean(f1s):.2f}")

def convert_bmp_to_raw(frames_folder):
    """Convert BMP frames into raw RGB0 files."""
    convert_images_to_raw(frames_folder, ext="bmp", order=RAW_ORDER)

def convert_jpg_to_raw(frames_folder):
    """Convert JPG frames into raw RGB0 files."""
    convert_images_to_raw(frames_folder, ext="jpg", order=RAW_ORDER)

def sigma_delta_motion_detection_3frames(raw_folder, width, height, highlight_color=(255, 0, 0)):
    """Sigma-delta motion detection using 3-frame differencing."""

    raw_files = sorted(glob.glob(os.path.join(raw_folder, '*.raw')))
    if len(raw_files) < 3:
        print("Not enough frames for 3-frame differencing.")
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

        # Parse RGB (matches hardware input: {R,G,B,0})
        frame = raw_bytes_to_frame(raw_bytes, width, height, order=RAW_ORDER)

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
    """Compute spatial (x, y) and temporal gradients between frames."""
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
    """Estimate optical flow using a 3x3 Lucas-Kanade window."""
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
    """Detect motion using optical flow and a magnitude threshold."""

    raw_files = sorted(glob.glob(os.path.join(raw_folder, '*.raw')))
    if len(raw_files) < 2:
        print("Not enough frames for optical flow.")
        return

    output_folder = os.path.join(raw_folder, 'optical_flow')
    os.makedirs(output_folder, exist_ok=True)

    prev_gray = None
    motion_magnitude_threshold = 2.0  # Flow vector magnitude threshold

    for frame_idx, raw_path in enumerate(raw_files):
        with open(raw_path, 'rb') as f:
            raw_bytes = f.read()

        frame = raw_bytes_to_frame(raw_bytes, width, height, order=RAW_ORDER)

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

def median_filter_3x3_window(pixels):
    """Return the median of a 3x3 window represented as a flat list of 9 values."""
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
    """Sigma-delta motion detection with additional filtering and cleanup steps."""
    raw_files = sorted(glob.glob(os.path.join(raw_folder, '*.raw')))
    if len(raw_files) < 2:
        print("Not enough frames.")
        return

    output_folder = os.path.join(raw_folder, 'sigma_delta_improved')
    os.makedirs(output_folder, exist_ok=True)

    background = None
    variation = None
    gray_prev = None

    for frame_idx, raw_path in enumerate(raw_files):
        with open(raw_path, 'rb') as f:
            raw_bytes = f.read()

        # Parse RGB (matches hardware input: {R,G,B,0})
        frame = raw_bytes_to_frame(raw_bytes, width, height, order=RAW_ORDER)

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
        save_rgb_frame_as_raw(
            output_frame=output_frame,
            width=width,
            height=height,
            output_folder=output_folder,
            base_filename="sigma_delta",
            frame_idx=frame_idx,
            order=RAW_ORDER
        )

        # Save binary motion map for evaluation
        np.save(os.path.join(output_folder, f"motion_map_{frame_idx:03}.npy"), motion_map.astype(np.uint8))

        #### Step 8: Update Previous Frame
        gray_prev = gray.copy()

def test(current_test, frames_folder, ground_truth_folder, num_frames, progress_every=25):
    """Run a single test case for the selected algorithm and evaluate results."""
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
            highlight_color=(255, 0, 0),
            progress_every=progress_every
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
    elif(current_test == 'sigma_delta_labeler'):
        sigma_delta_motion_detection_labeler(
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
    """Scanline-based bounding box merge with limited box capacity."""
    height, width = motion_map.shape
    boxes = np.zeros((max_boxes, 4), dtype=np.int32)  # [x_min, y_min, x_max, y_max]
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
                        # All boxes full - evict smallest if new box is larger
                        new_area = int(x_end - x_start + 1)
                        min_area = float('inf')
                        min_idx = -1
                        for i in range(max_boxes):
                            if box_valid[i]:
                                bx_min, by_min, bx_max, by_max = boxes[i]
                                area = int((bx_max - bx_min + 1) * (by_max - by_min + 1))
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
            area = int((x_max - x_min + 1) * (y_max - y_min + 1))
            if area >= min_pixels:
                final_boxes.append((x_min, y_min, x_max, y_max))

    return final_boxes




 
def label_components(motion_map, max_labels=255):
    """
    Two-pass CC labeler with at most `max_labels` (255) distinct labels.
    Any component after 255 is dropped (stays label 0).
    Returns:
      labels: uint8 array of shape motion_map.shape
      parent: dict for union-find equivalences
    """
    h, w = motion_map.shape
    labels = np.zeros((h, w), dtype=np.uint8)
    parent = {}
    next_label = 1

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[rb] = ra

    # First pass: assign provisional labels (uint8, cap at max_labels)
    for y in range(h):
        for x in range(w):
            if not motion_map[y, x]:
                continue

            # check west & north
            nbrs = []
            if x>0  and labels[y, x-1]>0: nbrs.append(labels[y, x-1])
            if y>0  and labels[y-1, x]>0: nbrs.append(labels[y-1, x])

            if not nbrs:
                if next_label <= max_labels:
                    lbl = next_label
                    parent[lbl] = lbl
                    next_label += 1
                else:
                    # overflow -> treat as background
                    lbl = 0
            else:
                lbl = min(nbrs)
                for n in nbrs:
                    if n!=lbl:
                        union(lbl, n)

            labels[y, x] = lbl

    # Flatten the UF tree
    for lbl in list(parent):
        parent[lbl] = find(lbl)

    return labels, parent

def extract_bboxes_from_labels(labels, parent, min_pixels=0, max_boxes=255):
    """Compute bounding boxes for connected components given label equivalences."""
    h, w = labels.shape
    bboxes = {}
    counts = {}

    for y in range(h):
        for x in range(w):
            lbl = labels[y, x]
            if lbl == 0:
                continue
            root = parent.get(lbl, lbl)
            if root not in bboxes:
                bboxes[root] = [x, y, x, y]
                counts[root] = 1
            else:
                xmin, ymin, xmax, ymax = bboxes[root]
                bboxes[root] = [
                    min(xmin, x),
                    min(ymin, y),
                    max(xmax, x),
                    max(ymax, y),
                ]
                counts[root] += 1

    boxes = [
        (xmin, ymin, xmax, ymax)
        for root, (xmin, ymin, xmax, ymax) in bboxes.items()
        if counts[root] >= min_pixels
    ]
    boxes.sort(key=lambda b: (b[2] - b[0]) * (b[3] - b[1]), reverse=True)
    return boxes[:max_boxes]

def merge_overlapping_boxes(boxes):
    """
    Merge any boxes that overlap into a single enclosing box.
    """
    merged = []
    while boxes:
        x0, y0, x1, y1 = boxes.pop(0)
        i = 0
        while i < len(boxes):
            bx0, by0, bx1, by1 = boxes[i]
            # if they overlap (or touch)
            if not (bx1 < x0 or bx0 > x1 or by1 < y0 or by0 > y1):
                # merge into the current box
                x0 = min(x0, bx0)
                y0 = min(y0, by0)
                x1 = max(x1, bx1)
                y1 = max(y1, by1)
                boxes.pop(i)
                # restart checking against the newly expanded box
                i = 0
            else:
                i += 1
        merged.append((x0, y0, x1, y1))
    return merged

def sigma_delta_motion_detection_labeler(raw_folder, width, height,
                                         highlight_color=(255, 0, 0),
                                         min_pixels=0,
                                         max_boxes=255,
                                         diff2_threshold=8):
    """
    Sigma-delta motion detection with labeler-based bounding boxes.
    """
    raw_files = sorted(glob.glob(os.path.join(raw_folder, '*.raw')))
    if len(raw_files) < 2:
        print("Not enough frames.")
        return

    output_folder = os.path.join(raw_folder, 'sigma_delta_labeler')
    os.makedirs(output_folder, exist_ok=True)

    background = None
    variation = None
    gray_prev = None

    for frame_idx, raw_path in enumerate(raw_files):
        with open(raw_path, 'rb') as f:
            raw_bytes = f.read()

        frame = raw_bytes_to_frame(raw_bytes, width, height, order=RAW_ORDER)

        r16 = frame[:, :, 0].astype(np.uint16)
        g16 = frame[:, :, 1].astype(np.uint16)
        b16 = frame[:, :, 2].astype(np.uint16)
        gray = ((77 * r16 + 150 * g16 + 29 * b16) >> 8).astype(np.uint8)

        if background is None:
            background = gray.copy()
            variation = np.full_like(gray, 2, dtype=np.uint8)
            gray_prev = gray.copy()
            continue

        inc = gray > background
        dec = gray < background
        background[inc] += 1
        background[dec] -= 1

        diff = np.abs(gray.astype(np.int16) - background.astype(np.int16)).astype(np.uint8)
        variation[diff > variation] += 2
        variation[diff < variation] -= 2
        variation = np.clip(variation, 2, 255)

        diff2 = np.abs(gray.astype(np.int16) - gray_prev.astype(np.int16)).astype(np.uint8)
        motion_map = (diff >= variation) & (diff2 > diff2_threshold)

        labels, parent = label_components(motion_map, max_labels=255)
        boxes = extract_bboxes_from_labels(labels, parent,
                                           min_pixels=min_pixels,
                                           max_boxes=max_boxes)
        boxes = merge_overlapping_boxes(boxes)

        output = frame.copy()
        for x0, y0, x1, y1 in boxes:
            output[y0:y1+1, x0] = highlight_color
            output[y0:y1+1, x1] = highlight_color
            output[y0, x0:x1+1] = highlight_color
            output[y1, x0:x1+1] = highlight_color

        save_rgb_frame_as_raw(output, width, height,
                              output_folder, "sigma_delta", frame_idx)
        np.save(os.path.join(output_folder, f"motion_map_{frame_idx:03}.npy"),
                motion_map.astype(np.uint8))

        gray_prev = gray.copy()

def main():
    """Run all test cases using the selected algorithm."""
    import argparse
    import os
    import re
    
    # Command: run (SIMULATION)
    script_dir = os.path.dirname(os.path.abspath(__file__))
    default_testcases_root = os.path.join(script_dir, "Testcases")

    run_parent = argparse.ArgumentParser(add_help=False)
    run_parent.add_argument("--algorithm", default="sigma_delta", help="Algorithm to use (sigma_delta, etc.)")
    run_parent.add_argument("--testcases-root", default=default_testcases_root,
                            help="Path to the Testcases folder")
    run_parent.add_argument("--progress-every", type=int, default=25,
                            help="Print progress every N frames (0 to disable)")
    run_parent.add_argument("--tests", default="",
                            help="Comma-separated list of tests to run (e.g. test1,test3). Empty runs all.")

    parser = argparse.ArgumentParser(description="Motion Detection Simulation CLI", parents=[run_parent])
    subparsers = parser.add_subparsers(dest="command", help="Command to run")

    parser_run = subparsers.add_parser("run", help="Run motion detection simulation", parents=[run_parent])
    
    # Command: rename (from rename_utils.py)
    parser_rename = subparsers.add_parser("rename", help="Rename files using regex")
    parser_rename.add_argument("src", help="Source folder")
    parser_rename.add_argument("dst", help="Destination folder")
    parser_rename.add_argument("regex", help="Regex to capture number (e.g. '-(\\d+)')")
    parser_rename.add_argument("format", help="New name format (e.g. 'frame_{number:03}.bmp')")
    parser_rename.add_argument("--offset", type=int, default=-1, help="Number offset")
    parser_rename.add_argument("--ext", help="Extension filter")

    # Command: convert (raw to png)
    parser_convert = subparsers.add_parser("convert", help="Convert RAW to PNG")
    parser_convert.add_argument("folder", help="Folder containing RAW files")
    parser_convert.add_argument("--width", type=int, required=True, help="Image width")
    parser_convert.add_argument("--height", type=int, required=True, help="Image height")
    parser_convert.add_argument("--order", default="RGB0", help="Byte order")

    # Command: video (png to video)
    parser_video = subparsers.add_parser("video", help="Create video from PNGs")
    parser_video.add_argument("folder", help="Folder containing PNGs")
    parser_video.add_argument("output", help="Output video path")
    parser_video.add_argument("--fps", type=int, default=30, help="Frames per second")
    parser_video.add_argument("--pattern", default="*.png", help="File pattern")
    
    args = parser.parse_args()
    
    if args.command == "run" or args.command is None:
        # Default behavior: Run simulation
        selected_algorithm = args.algorithm if args.command == "run" else "sigma_delta"
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

        testcases_root = default_testcases_root
        if args.command == "run":
            testcases_root = args.testcases_root

        if not os.path.isdir(testcases_root):
            raise SystemExit(f"Testcases folder not found: {testcases_root}")

        selected_tests = None
        if args.command == "run" and args.tests:
            selected_tests = {t.strip() for t in args.tests.split(",") if t.strip()}
            valid_tests = {name for name, _ in test_cases}
            invalid = sorted(selected_tests - valid_tests)
            if invalid:
                raise SystemExit(f"Unknown tests: {', '.join(invalid)}")

        for test_name, num_frames in test_cases:
            if selected_tests and test_name not in selected_tests:
                continue
            print(f"\nRunning {test_name.upper()} with {selected_algorithm}")
            test(
                current_test=selected_algorithm,
                frames_folder=os.path.join(testcases_root, test_name),
                ground_truth_folder=os.path.join(testcases_root, test_name, "ground_truth"),
                num_frames=num_frames,
                progress_every=args.progress_every
            )
            
    elif args.command == "rename":
        # Inline implementation of rename_by_regex
        os.makedirs(args.dst, exist_ok=True)
        files = os.listdir(args.src)
        for file_name in files:
            if args.ext and not file_name.endswith(args.ext):
                continue
            match = re.search(args.regex, file_name)
            if not match:
                print(f"Skipping {file_name}, no number found.")
                continue
            number = int(match.group(1)) + args.offset
            if number < 0:
                print(f"Skipping {file_name}, new number would be negative.")
                continue
            new_name = args.format.format(number=number)
            src_path = os.path.join(args.src, file_name)
            dst_path = os.path.join(args.dst, new_name)
            if os.path.exists(dst_path):
                print(f"Skipping {file_name}, destination {new_name} already exists.")
            else:
                print(f"Renaming {file_name} -> {new_name}")
                os.rename(src_path, dst_path)
                
    elif args.command == "convert":
        convert_all_raw_to_png(args.folder, args.width, args.height, order=args.order)
        
    elif args.command == "video":
        pngs_to_video(args.folder, args.output, fps=args.fps, pattern=args.pattern)

if __name__ == '__main__':
    main()
