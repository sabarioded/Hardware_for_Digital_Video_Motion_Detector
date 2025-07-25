UVM_HOME = /eda/synopsys/2020-21/RHELx86/VCS_2020.12/vcs/R-2020.12/etc/uvm-1.2
UVM_VERBOSITY = UVM_MEDIUM
CFLAGS = full64
	
VCS = vcs -sverilog -kdb +warn=noOBSV2G -full64 -timescale=1ns/1ns \
		-debug_access+r+w+nomemcbk -debug_region+cell +vpi -debug_access+nomemcbk+dmptf -debug_region+cell \
	+define+UVM_OBJECT_MUST_HAVE_CONSTRUCTOR \
	+incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm.sv \
	-cm_cond allops+anywidth+event -cm_noconst \
	-cm line+cond+fsm+branch+tgl -cm_dir ./coverage.vdb\
	$(UVM_HOME)/src/dpi/uvm_dpi.cc -CFLAGS -DVCS -debug_acc+all -debug_region+cell+encrypt +define+nobanner
		
SIMV = ./simv +UVM_VERBOSITY=$(UVM_VERBOSITY) \
	+UVM_TR_RECORD +UVM_LOG_RECORD \
	-cm line+cond+fsm \
	+verbose=1 +ntb_random_seed=244 -l vcs.log
	
x: comp run
	
comp:
	$(VCS) +define+ENABLE_mp_ASSERTIONS \
	  +incdir+. \
	  motion_pipeline/bounding_boxes/labeler/labler.sv \
	  motion_pipeline/bounding_boxes/label_merger/label_merger.sv \
	  motion_pipeline/bounding_boxes/bbox_top.sv \
	  motion_pipeline/motion_map_generator/motion_map_generator.sv \
	  motion_pipeline/motion_map_generator/frame_manager/frame_manager.sv \
	  motion_pipeline/motion_map_generator/frame_manager/sigma_delta/sigma_delta.sv \
	  motion_pipeline/motion_map_generator/motion_detector/motion_detector.sv \
	  motion_pipeline/motion_pipeline.sv \
	  addr_manager/addr_manager.sv \
	  Digital_Motion_Detector.sv \
	  dmd_if.sv \
	  dmd_trans.sv \
	  dmd_sequencer.sv \
	  dmd_sequence.sv \
	  dmd_driver.sv \
	  dmd_monitor.sv \
	  dmd_scoreboard.sv \
	  dmd_agent.sv \
	  dmd_env.sv \
	  dmd_test.sv \
	  dmd_tb.sv \
	  -l compile.log
	  
run:
	$(SIMV)
	
clean:
	rm -rf coverage.vdb csrc DVEfiles inter.vpd simv simv.daidir ucli.key vc_hdrs.h vcs.log .inter.vpd.uvm
