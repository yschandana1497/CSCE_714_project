//=====================================================================
// Project: 4 core MESI cache design
// File Name: cache_data_hit_read.sv
// Description: Test for read-miss to I-cache
// Designers: group 8
//=====================================================================

class cache_data_hit_read extends base_test;

//component macro
`uvm_component_utils(cache_data_hit_read)

//Constructor
function new(string name, uvm_component parent);
    super.new(name, parent);
endfunction : new

//UVM build phase
function void build_phase(uvm_phase phase);
    uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", ran_seq_read_hit_d::type_id::get());
    super.build_phase(phase);
endfunction : build_phase

//UVM run phase()
task run_phase(uvm_phase phase);
    `uvm_info(get_type_name(), "Executing randomised test" , UVM_LOW)
endtask: run_phase

endclass : cache_data_hit_read





//constraints for cache_data_hit_read
class constrained_trans_1 extends cpu_transaction_c;
`uvm_object_utils(constrained_trans_1)

function new (string name="constrained Transaction packet");
    super.new(name);
endfunction:new

//request type -- Read or --Write READ==0, Write ==1
constraint req_type_set {
    request_type == 0;
}

//constraint for address
constraint address_set {
    address > 32'h4000_0000;
    unique {address} ;
}


//constraint for data



//constraint for wait cycels   //Number of cycles to wait before driving the transactio

endclass: constrained_trans_1



//test for cache_data_hit_read
class ran_seq_read_hit_d extends base_vseq;
//object macro
`uvm_object_utils(ran_seq_read_hit_d)


//constructor
function new (string name="ran_seq_read_hit_d");
    super.new(name);
endfunction : new


constrained_trans_1 trans = constrained_trans_1::type_id::create("t");
virtual task body();

bit [31:0] addrRand;
repeat(10)
begin
    
    for(int i=0; i<4; i++)
    begin
        addrRand = $urandom_range(32'h4000_0000,32'hffff_ffff);
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i],{address== addrRand ;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i],{address== addrRand ;})
    end

end
    
    
endtask

endclass : ran_seq_read_hit_d
