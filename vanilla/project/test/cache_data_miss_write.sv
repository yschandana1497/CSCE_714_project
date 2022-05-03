//=====================================================================
// Project: 4 core MESI cache design
// File Name: cache_data_miss_write.sv
// Description: Test for write-miss to d-cache
// Designers: group 8
//=====================================================================

class cache_data_miss_write extends base_test;

//component macro
`uvm_component_utils(cache_data_miss_write)

//Constructor
function new(string name, uvm_component parent);
    super.new(name, parent);
endfunction : new

//UVM build phase
function void build_phase(uvm_phase phase);
    uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", ran_seq_write_miss_lru_replacement_d::type_id::get());
    super.build_phase(phase);
endfunction : build_phase

//UVM run phase()
task run_phase(uvm_phase phase);
    `uvm_info(get_type_name(), "Executing randomised test" , UVM_LOW)
endtask: run_phase

endclass : cache_data_miss_write





//constraints for cache_data_miss_write
class constrained_trans_2 extends cpu_transaction_c;
`uvm_object_utils(constrained_trans_2)

function new (string name="constrained Transaction packet");
    super.new(name);
endfunction:new

//request type -- Read or --Write READ==0, Write ==1
constraint req_type_set {
  soft  request_type == 1;
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
   soft access_cache_type ==  1 ;
}


//constraint for wait cycels   //Number of cycles to wait before driving the transactio

endclass: constrained_trans_2

//test for cache_data_miss_write_lru_replacement
class ran_seq_write_miss_lru_replacement_d extends base_vseq;
//object macro
`uvm_object_utils(ran_seq_write_miss_lru_replacement_d)


//constructor
function new (string name="ran_seq_write_miss_lru_replacement_d");
    super.new(name);
endfunction : new


constrained_trans_2 trans = constrained_trans_2::type_id::create("t");
virtual task body();

 for(int i=0; i<4; i++)
begin
	for(int j=0; j<5; j++)
		begin
        `uvm_do_on(trans, p_sequencer.cpu_seqr[i])
    end
end

endtask

endclass : ran_seq_write_miss_lru_replacement_d
