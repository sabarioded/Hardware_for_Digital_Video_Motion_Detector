/*------------------------------------------------------------------------------
 * File          : motion_detector_sequencer.sv
 * Project       : RTL
 * Author        : eposmk
 * Creation date : May 9, 2025
 * Description   :
 *------------------------------------------------------------------------------*/

class motion_detector_sequencer extends uvm_sequencer#(motion_detector_transaction);
	`uvm_component_utils(motion_detector_sequencer)

	function new(string name = "motion_detector_sequencer", uvm_component parent = null);
	  super.new(name, parent);
	endfunction

  endclass