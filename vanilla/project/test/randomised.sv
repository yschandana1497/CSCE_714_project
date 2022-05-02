//=====================================================================
// Project: 4 core MESI cache design
// File Name: randomised.sv
// Description: Test for read-miss to I-cache
// Designers: group 8
//=====================================================================

class randomised extends base_test;

//component macro
`uvm_component_utils(randomised)

//Constructor
function new(string name, uvm_component parent);
    super.new(name, parent);
endfunction : new

//UVM build phase
function void build_phase(uvm_phase phase);
    uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", randomised_sequence::type_id::get());
    super.build_phase(phase);
endfunction : build_phase

//UVM run phase()
task run_phase(uvm_phase phase);
    `uvm_info(get_type_name(), "Executing randomised test" , UVM_LOW)
endtask: run_phase

endclass : randomised






class constrained_trans extends cpu_transaction_c;
`uvm_object_utils(constrained_trans)

function new (string name="constrained Transaction packet");
    super.new(name);
endfunction:new

constraint req_type_set {
    request_type dist { 0 := 5 , 1 := 3 };
}
endclass: constrained_trans



// Sequence for a read-miss on I-cache
class randomised_sequence extends base_vseq;
//object macro
`uvm_object_utils(randomised_sequence)


//constructor
function new (string name="randomised_sequence");
    super.new(name);
endfunction : new


constrained_trans trans = constrained_trans::type_id::create("t");
virtual task body();
bit [3:0] randVar;
repeat(10)
begin
    randVar = $urandom_range(0,3);
    `uvm_do_on(trans, p_sequencer.cpu_seqr[randVar])
end
    
endtask

endclass : randomised_sequence
