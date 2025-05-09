# Path to UVM library
UVM_HOME = /eda/synopsys/2020-21/RHELx86/VCS_2020.12/vcs/R-2020.12/etc/uvm-1.2

# UVM verbosity level
UVM_VERBOSITY = UVM_MEDIUM

# Compiler flags
CFLAGS = full64

# VCS compile command
VCS = vcs -sverilog -kdb +warn=noOBSV2G -full64 -timescale=1ns/1ns \
	-debug_access+r+w+nomemcbk -debug_region+cell +vpi \
	+define+UVM_OBJECT_MUST_HAVE_CONSTRUCTOR \
	+incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm.sv \
	-cm_cond allops+anywidth+event -cm_noconst \
	-cm line+cond+fsm+branch+tgl -cm_dir ./coverage.vdb \
	$(UVM_HOME)/src/dpi/uvm_dpi.cc -CFLAGS -DVCS -debug_acc+all -debug_region+cell+encrypt +define+nobanner

# Simulation command
SIMV = ./simv +UVM_VERBOSITY=$(UVM_VERBOSITY) \
	+UVM_TR_RECORD +UVM_LOG_RECORD +UVM_LOG_FILE=uvm_output.log \
	-cm line+cond+fsm \
	+verbose=1 +ntb_random_seed=244 -l vcs.log

# Default target
x: comp run

# Compilation target for motion detector project
comp:
	$(VCS) +incdir+. \
		box_filter.sv \
		box_filter_assertions.sv \
		box_filter_if.sv \
		box_filter_transaction.sv \
		box_filter_sequence.sv \
		box_filter_sequencer.sv \
		box_filter_driver.sv \
		box_filter_monitor.sv \
		box_filter_scoreboard.sv \
		box_filter_agent.sv \
		box_filter_env.sv \
		box_filter_test.sv \
		box_filter_tb.sv

# Run simulation
run:
	$(SIMV)

# Clean generated files
clean:
	rm -rf coverage.vdb csrc DVEfiles inter.vpd simv simv.daidir ucli.key vc_hdrs.h vcs.log .inter.vpd.uvm uvm_output.log
