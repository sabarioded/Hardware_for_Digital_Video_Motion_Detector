# Path to UVM library
UVM_HOME = /eda/synopsys/2020-21/RHELx86/VCS_2020.12/vcs/R-2020.12/etc/uvm-1.2

# UVM verbosity level (options: UVM_NONE, UVM_LOW, UVM_MEDIUM, UVM_HIGH, UVM_FULL)
UVM_VERBOSITY = UVM_MEDIUM

# Compiler flags to enable 64-bit compilation
CFLAGS = full64

# VCS compile command
VCS = vcs -sverilog -full64 -timescale=1ns/1ns \
      -kdb +warn=noOBSV2G \
      -debug_access+r+w+nomemcbk -debug_region+cell \
      +define+UVM_OBJECT_MUST_HAVE_CONSTRUCTOR \
      +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm.sv \
      -cm_cond allops+anywidth+event -cm_noconst \
      -cm line+cond+fsm+branch+tgl -cm_dir ./coverage.vdb \
      $(UVM_HOME)/src/dpi/uvm_dpi.cc -CFLAGS -DVCS \
      -debug_acc+all -debug_region+cell+encrypt +define+nobanner

# Simulation execution command (with VCD dump & GUI launch)
SIMV = ./simv \
       +UVM_VERBOSITY=$(UVM_VERBOSITY) \
       +UVM_TR_RECORD +UVM_LOG_RECORD +UVM_LOG_FILE=uvm_output.log \
       +vcd=wave.vcd \
       -cm line+cond+fsm \
       +ntb_random_seed=244 \
       -l vcs.log \
       -R

# Default target: compile & run
all: comp run

# Compile all DUT & testbench files
comp:
	$(VCS) +define+ENABLE_MMG_ASSERTIONS \
	  +incdir+. \
	  motion_map_generator.sv \
	  frame_manager.sv \
	  sigma_delta.sv \
	  motion_detector.sv \
	  mmg_if.sv \
	  mmg_trans.sv \
	  mmg_sequence.sv \
	  mmg_sequencer.sv \
	  mmg_driver.sv \
	  mmg_monitor.sv \
	  mmg_scoreboard.sv \
	  mmg_agent.sv \
	  mmg_env.sv \
	  mmg_test.sv \
	  mmg_tb.sv \
	  -l compile.log

# Run the simulation (will dump wave.vcd and open DVE)
run:
	$(SIMV)

# Remove generated files
clean:
	rm -rf coverage.vdb csrc DVEfiles inter.vpd simv simv.daidir ucli.key \
	       vc_hdrs.h vcs.log wave.vcd compile.log
