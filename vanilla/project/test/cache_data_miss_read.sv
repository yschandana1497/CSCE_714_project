//=====================================================================
// Project: 4 core MESI cache design
// File Name: Cache_data_miss_read.sv
// Description: Test for read-miss to I-cache
// Designers: group 8
//=====================================================================

class cache_data_miss_read extends base_test;

//component macro
`uvm_component_utils(cache_data_miss_read)

//Constructor
function new(string name, uvm_component parent);
    super.new(name, parent);
endfunction : new

//UVM build phase
function void build_phase(uvm_phase phase);
    uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", ran_seq_read_miss_lru_replacement_d::type_id::get());
    super.build_phase(phase);
endfunction : build_phase

//UVM run phase()
task run_phase(uvm_phase phase);
    `uvm_info(get_type_name(), "Executing randomised test" , UVM_LOW)
endtask: run_phase

endclass : cache_data_miss_read





//constraints for Cache_data_miss_read
class constrained_trans extends cpu_transaction_c;
`uvm_object_utils(constrained_trans)

function new (string name="constrained Transaction packet");
    super.new(name);
endfunction:new

//request type -- Read or --Write READ==0, Write ==1
constraint req_type_set {
   soft request_type == 0;
}

//constraint for address
constraint address_set {
    address > 32'h4000_0000;
	address[15:2] == 14'b11111111111111;
    unique {address} ;
}


//constraint for data

//accesss cache type   icache =0; dcache 1
constraint cache_type_set {
  soft  access_cache_type ==  1 ;
}


//constraint for wait cycels   //Number of cycles to wait before driving the transactio

endclass: constrained_trans





//test for Cache_data_miss_read
class ran_seq_read_miss_lru_replacement_d extends base_vseq;
//object macro
`uvm_object_utils(ran_seq_read_miss_lru_replacement_d)


//constructor
function new (string name="ran_seq_read_miss_lru_replacement_d");
    super.new(name);
endfunction : new


constrained_trans trans = constrained_trans::type_id::create("t");
virtual task body();
bit [1:0] randVar;
bit [1:0] randVar2;
bit[31:0] addrRand;
repeat(10)
begin
    randVar = $urandom_range(0,3);
	addrRand = $urandom_range(32'h4000_0000,32'hffff_ffff);
	`uvm_do_on_with(trans, p_sequencer.cpu_seqr[randVar],{request_type==WRITE_REQ; address==addrRand;})
	randVar2 = (randVar+1)%4;
    `uvm_do_on(trans, p_sequencer.cpu_seqr[randVar2])
	`uvm_do_on(trans, p_sequencer.cpu_seqr[randVar])
	`uvm_do_on(trans, p_sequencer.cpu_seqr[randVar])
	`uvm_do_on(trans, p_sequencer.cpu_seqr[randVar])
	`uvm_do_on(trans, p_sequencer.cpu_seqr[randVar])
end
    
endtask

endclass : ran_seq_read_miss_lru_replacement_d