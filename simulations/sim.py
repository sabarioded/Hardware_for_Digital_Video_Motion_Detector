from PIL import Image
import subprocess
import time
import os
import glob
import numpy as np
import cv2
from sklearn.metrics import precision_score, recall_score, f1_score

def save_rgb_frame_as_raw(output_frame, width, height, output_folder, base_filename, frame_idx):
    """
    Save an RGB frame as a raw file with R, G, B, 0x00 ordering per pixel.
    """
    raw_path = os.path.join(output_folder, f"{base_filename}_{frame_idx:03}.raw")
    with open(raw_path, 'wb') as f:
        for y in range(height):
            for x in range(width):
                r, g, b = output_frame[y, x]
                # WRITE R, G, B, 0x00
                f.write(bytes([r, g, b, 0x00]))

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
                    # overflow → treat as background
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

def extract_bboxes_from_labels(labels, parent,
                               min_pixels=0,   # no size filter
                               max_boxes=255): # allow up to 255 boxes
    """
    Second pass: build one bbox per root label.
    Returns list of (x_min, y_min, x_max, y_max).
    """
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

    # collect & sort (no size filtering)
    boxes = [
        (xmin, ymin, xmax, ymax)
        for root, (xmin, ymin, xmax, ymax) in bboxes.items()
        if counts[root] >= min_pixels
    ]
    # sort by area descending
    boxes.sort(key=lambda b: (b[2]-b[0])*(b[3]-b[1]), reverse=True)

    return boxes[:max_boxes]

def sigma_delta_motion_detection(raw_folder, width, height,
                                 highlight_color=(255, 0, 0),
                                 min_pixels=0,
                                 max_boxes=255,
                                 diff2_threshold=8):
    """
    Runs sigma-delta motion detection on raw RGB frames, applying
    the labeler-based bounding-box algorithm exactly as your SV.
    """
    raw_files = sorted(glob.glob(os.path.join(raw_folder, '*.raw')))
    if len(raw_files) < 2:
        print("❌ Not enough frames.")
        return

    output_folder = os.path.join(raw_folder, 'sigma_delta')
    os.makedirs(output_folder, exist_ok=True)

    background = None
    variation = None
    gray_prev = None

    for frame_idx, raw_path in enumerate(raw_files):
        # Read raw bytes
        with open(raw_path, 'rb') as f:
            raw_bytes = f.read()

        # Parse RGB frame (R, G, B, 0x00)
        frame = np.zeros((height, width, 3), dtype=np.uint8)
        idx = 0
        for y in range(height):
            for x in range(width):
                r = raw_bytes[idx]
                g = raw_bytes[idx+1]
                b = raw_bytes[idx+2]
                frame[y, x] = [r, g, b]
                idx += 4

        # Convert to grayscale (luminosity)
        r16 = frame[:, :, 0].astype(np.uint16)
        g16 = frame[:, :, 1].astype(np.uint16)
        b16 = frame[:, :, 2].astype(np.uint16)
        gray = ((77*r16 + 150*g16 + 29*b16) >> 8).astype(np.uint8)

        if background is None:
            background = gray.copy()
            variation  = np.full_like(gray, 2, dtype=np.uint8)
            gray_prev  = gray.copy()
            continue

        # Sigma-delta update
        inc = gray > background
        dec = gray < background
        background[inc] += 1
        background[dec] -= 1

        diff = np.abs(gray.astype(np.int16) - background.astype(np.int16)).astype(np.uint8)
        variation[diff > variation] += 2
        variation[diff < variation] -= 2
        variation = np.clip(variation, 2, 255)

        # Motion map
        diff2 = np.abs(gray.astype(np.int16) - gray_prev.astype(np.int16)).astype(np.uint8)
        motion_map = (diff >= variation) & (diff2 > diff2_threshold)
        
        # motion_map = hardware_friendly_closing(motion_map)

        # Labeler-based bounding boxes
        labels, parent = label_components(motion_map, max_labels=255)
        boxes = extract_bboxes_from_labels(labels, parent,
                                           min_pixels=0,
                                           max_boxes=255)

        boxes = merge_overlapping_boxes(boxes)
        
        # Overlay bounding boxes on the frame
        output = frame.copy()
        for x0, y0, x1, y1 in boxes:
            output[y0:y1+1, x0] = highlight_color
            output[y0:y1+1, x1] = highlight_color
            output[y0, x0:x1+1] = highlight_color
            output[y1, x0:x1+1] = highlight_color

        # Save raw and motion_map
        save_rgb_frame_as_raw(output, width, height,
                              output_folder, "sigma_delta", frame_idx)
        np.save(os.path.join(output_folder, f"motion_map_{frame_idx:03}.npy"),
                motion_map.astype(np.uint8))

        gray_prev = gray.copy()

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
                # WRITE R, G, B, 0x00
                raw_bytes.extend([r, g, b, 0x00])

        filename = os.path.splitext(os.path.basename(path))[0]
        output_path = os.path.join(output_folder, f'{filename}.raw')
        with open(output_path, 'wb') as f:
            f.write(raw_bytes)

def convert_all_raw_to_png(raw_folder, width, height):
    raw_files = sorted(glob.glob(os.path.join(raw_folder, '*.raw')))
    for raw_path in raw_files:
        with open(raw_path, 'rb') as f:
            raw_bytes = f.read()

        rgb_data = bytearray()
        # READ as R, G, B, 0x00
        for i in range(0, len(raw_bytes), 4):
            r = raw_bytes[i]
            g = raw_bytes[i+1]
            b = raw_bytes[i+2]
            rgb_data.extend([r, g, b])

        img = Image.frombytes('RGB', (width, height), bytes(rgb_data))
        output_png = raw_path.replace('.raw', '_reconstructed.png')
        img.save(output_png)

def png_to_video(frames_folder, output_path, fps=30):
    frame_files = sorted(glob.glob(os.path.join(frames_folder, '*.png')))
    if not frame_files:
        print("❌ No PNG files found.")
        return

    first = cv2.imread(frame_files[0])
    h, w, _ = first.shape
    fourcc = cv2.VideoWriter_fourcc(*'mp4v')
    out = cv2.VideoWriter(output_path, fourcc, fps, (w, h))

    for fn in frame_files:
        frame = cv2.imread(fn)
        out.write(frame)
    out.release()
    print(f"🎥 Video saved to: {output_path}")

def hardware_friendly_closing(motion_map):
    """
    Emulates your SV closing stage: a 3×3 dilation followed by erosion
    to fill small holes.
    """
    kernel = np.ones((3, 3), np.uint8)
    # motion_map is bool; convert to 0/255 uint8
    mm8 = (motion_map.astype(np.uint8) * 255)
    closed = cv2.morphologyEx(mm8, cv2.MORPH_CLOSE, kernel)
    return (closed > 0)

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


def test(current_test, frames_folder, ground_truth_folder, num_frames):
    convert_bmp_to_raw(frames_folder)
    example_bmp = os.path.join(frames_folder, 'frame_000.bmp')
    width, height = Image.open(example_bmp).size

    raw_folder = os.path.join(frames_folder, 'raw_rbg32')
    output_folder = os.path.join(raw_folder, current_test)
    os.makedirs(output_folder, exist_ok=True)

    if current_test == 'sigma_delta':
        sigma_delta_motion_detection(raw_folder, width, height)

    # Evaluation (precision/recall/F1)…
    pred_folder = os.path.join(raw_folder, current_test)
    pred_paths = sorted(glob.glob(os.path.join(pred_folder, 'motion_map_*.npy')))
    gt_paths = sorted(glob.glob(os.path.join(ground_truth_folder, '*.png'))) + \
               sorted(glob.glob(os.path.join(ground_truth_folder, '*.bmp')))

    if not pred_paths or not gt_paths:
        print("⚠️ No predictions or ground truth files found.")
    else:
        n = min(len(pred_paths), len(gt_paths))
        metrics = []
        for p, g in zip(pred_paths[:n], gt_paths[:n]):
            pred = np.load(p).flatten()
            gt_img = cv2.imread(g, cv2.IMREAD_GRAYSCALE)
            gt = (gt_img > 0).astype(np.uint8).flatten()
            metrics.append((
                precision_score(gt, pred, zero_division=0),
                recall_score   (gt, pred, zero_division=0),
                f1_score       (gt, pred, zero_division=0),
            ))
        avg_p, avg_r, avg_f1 = np.mean(metrics, axis=0)
        print(f"→ Precision: {avg_p:.3f}, Recall: {avg_r:.3f}, F1-score: {avg_f1:.3f}")

    # Reconstruct PNGs & make video
    convert_all_raw_to_png(output_folder, width, height)
    png_to_video(output_folder, os.path.join(frames_folder, 'test_output.mp4'))

def main():
    selected_algorithm = 'sigma_delta'
    test_cases = [
        ('test1',  300), ('test2', 272), ('test3', 525), ('test4', 300),
        ('test5', 225), ('test6', 250), ('test7', 250), ('test8', 300),
        ('test9', 275), ('test10', 400)
    ]
    for test_name, num_frames in test_cases:
        print(f"\n🔍 Running {test_name} [{selected_algorithm}]")
        test(
            current_test=selected_algorithm,
            frames_folder=f'simulations/Testcases/{test_name}',
            ground_truth_folder=f'simulations/Testcases/{test_name}/ground_truth',
            num_frames=num_frames
        )

if __name__ == '__main__':
    main()
