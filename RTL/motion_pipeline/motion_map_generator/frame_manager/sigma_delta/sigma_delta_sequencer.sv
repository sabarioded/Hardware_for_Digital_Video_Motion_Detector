/*------------------------------------------------------------------------------
 * File          : sigma_delta_sequencer.sv
 * Project       : RTL
 * Description   : Sequencer for sigma_delta_update UVM environment
 *------------------------------------------------------------------------------*/

class sigma_delta_sequencer extends uvm_sequencer#(sigma_delta_transaction);
  `uvm_component_utils(sigma_delta_sequencer)

  function new(string name = "sigma_delta_sequencer", uvm_component parent = null);
	super.new(name, parent);
  endfunction

endclass
