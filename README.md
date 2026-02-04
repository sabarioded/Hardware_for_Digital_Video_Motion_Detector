# Hardware for Digital Video Motion Detector

![Platform](https://img.shields.io/badge/platform-ASIC%20%2F%20FPGA-green.svg)
![Language](https://img.shields.io/badge/language-SystemVerilog%20%7C%20Python-blue.svg)
![Verification](https://img.shields.io/badge/verification-UVM-orange.svg)
![License](https://img.shields.io/badge/license-Educational-lightgrey.svg)

## Table of Contents

- [Overview](#overview)
- [Key Features](#key-features)
- [Architecture](#architecture)
- [Algorithm](#algorithm)
- [Project Structure](#project-structure)
- [Getting Started](#getting-started)
  - [Simulation & Verification](#simulation--verification)
  - [Python Reference Model](#python-reference-model)
- [Results](#results)
- [License](#license)

---

## Overview

This project implements a **hardware-oriented Digital Video Motion Detector**. It was designed to bridge the gap between algorithmic motion detection and realistic RTL implementation.

Motion detection is a core building block in surveillance systems, smart traffic monitoring, and embedded vision pipelines. This design focuses on a lightweight, efficient pipeline validated using **industry-standard UVM methodology**.

![Project Context](docs/image.png)

---

## Key Features

### Hardware Design
*   **Efficient Pipeline:** Frame-based processing tailored for real-time video flow.
*   **Modular RTL:** Clear separation between datapath and control using SystemVerilog.
*   **Parameterized:** Configurable resolution and thresholding.

### Algorithmic Core
*   **Sigma-Delta Detection:** Integer-only algorithm suitable for hardware synthesis.
*   **Background Modeling:** Dynamic background update mechanism.
*   **Bounding Box Extraction:** Hardware-friendly logic to merge motion pixels into spatial regions.

### Verification & Modeling
*   **UVM Environment:** Comprehensive testbench with drivers, monitors, and scoreboards.
*   **Python Reference:** Bit-accurate software model for algorithm exploration and verification.

---

## Architecture

The system processes video frames to produce a **binary motion map** and high-level **bounding boxes**.

![Pipeline Architecture](docs/image-1.png)

**Pipeline Stages:**
1.  **Frame Acquisition:** Ingests video stream.
2.  **Background Modeling:** Maintains a running estimate of the static background.
3.  **Motion Detection:** Compares current frame to background (Sigma-Delta).
4.  **Motion Map:** Generates a binary mask of moving pixels.
5.  **Bounding Boxes:** Aggregates motion pixels into rectangular coordinates.

---

## Algorithm

### Sigma-Delta Background Subtraction

The core engine uses a modified **Sigma-Delta** algorithm with a dual-condition check for robust detection. It maintains both a **Background** model and a **Variance (Sigma)** estimate.

**Motion Logic:**
A pixel is marked as motion only if **both** conditions are met:
1.  **Temporal Difference:** `|current - previous| > threshold` (Filters out slow changes)
2.  **Background Deviation:** `|current - background| >= variance` (Filters out noise)

**Update Logic:**
*   **Background:** Incremented/Decremented by 1 towards current pixel.
*   **Variance:** Incremented/Decremented by 2 towards the current deviation.

![Sigma Delta Algorithm](docs/image-2.png)

### Bounding Box Extraction

The bounding box block converts unstructured motion pixels into spatial regions using a hardware-optimized **Connected Component Labeling (CCL)** approach.

**Key Hardware Features:**
*   **Single-Pass Labeling:** Assigns labels on-the-fly using a line buffer (checks Left/Top neighbors).
*   **Ping-Pong Banking:** Uses 4 memory banks to pipeline the stages:
    1.  **Accumulate:** Update min/max coordinates for each label.
    2.  **Filter/Merge:** Merge overlapping bounding boxes.
    3.  **Output:** Highlight pixel edges based on active boxes.
    4.  **Clear:** Reset bank for reuse.

![Bounding Box](docs/image-3.png)

---

## Project Structure

The repository is organized to separate Synthesizable RTL, Verification methods, and Documentation.

```text
.
├── rtl/                                     # Synthesizable Design
│   ├── Digital_Motion_Detector.sv           # Top Level
│   ├── addr_manager.sv
│   └── motion_pipeline/                     # Pipeline Stages
│       ├── motion_map_generator/
│       └── bounding_boxes/
├── dv/                                      # Verification
│   ├── uvm/                                 # UVM Testbenches
│   │   ├── dmd/                             # Top-Level TB
│   │   └── motion_pipeline/                 # Unit TBs
│   └── python/                              # Reference Model
│       ├── sim.py                           # Main simulation CLI
│       └── Testcases/
└── docs/                                    # Images & Documentation
```

---

## Getting Started

### Simulation & Verification

To run the full UVM regression on the top-level design:

```bash
cd dv/uvm/dmd
make x
```

This will compile the RTL and Testbench using VCS and run the default test case.

### Python Reference Model

The Python model serves as the "Golden Reference". You can run it via the unified CLI:

```bash
# General help
python3 dv/python/sim.py --help

# Run Sigma-Delta algorithm on all testcases
python3 dv/python/sim.py run --algorithm sigma_delta

# Create a video from output frames
python3 dv/python/sim.py video output_folder/ result.mp4
```

---

## Results

Evaluation demonstrates that the hardware implementation successfully detects motion with reasonable accuracy (F1 Score, Precision, Recall) compared to software baselines, while fitting within hardware constraints.

---

## License

This project was developed for academic purposes at the Technion – Israel Institute of Technology. Provided for educational and demonstration purposes.
