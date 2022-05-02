//=====================================================================
// Project: 4 core MESI cache design
// File Name: cache_inst_hit_read.sv
// Description: Test for read-miss to I-cache
// Designers: group 8
//=====================================================================

class cache_inst_hit_read extends base_test;

//component macro
`uvm_component_utils(cache_inst_hit_read)

//Constructor
function new(string name, uvm_component parent);
    super.new(name, parent);
endfunction : new

//UVM build phase
function void build_phase(uvm_phase phase);
    uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", ran_seq_read_hit_i::type_id::get());
    //uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", ran_seq_read_hit_i_lrutest::type_id::get());
    super.build_phase(phase);
endfunction : build_phase

//UVM run phase()
task run_phase(uvm_phase phase);
    `uvm_info(get_type_name(), "Executing randomised test" , UVM_LOW)
endtask: run_phase

endclass : cache_inst_hit_read





//constraints for cache_inst_hit_read
class constrained_trans_4 extends cpu_transaction_c;
`uvm_object_utils(constrained_trans_4)

function new (string name="constrained Transaction packet");
    super.new(name);
endfunction:new

//request type -- Read or --Write READ==0, Write ==1
constraint req_type_set {
    request_type == 0;
}

//constraint for address
constraint address_set {
    address < 32'h4000_0000;
}


//constraint for data
constraint data_rand_set {
    unique {data} ;
}

//accesss cache type   icache =0; dcache 1
constraint cache_type_set {
    access_cache_type ==  0 ;
}


//constraint for wait cycels   //Number of cycles to wait before driving the transactio

endclass: constrained_trans_4



//test for cache_inst_hit_read
class ran_seq_read_hit_i extends base_vseq;
//object macro
`uvm_object_utils(ran_seq_read_hit_i)


//constructor
function new (string name="ran_seq_read_hit_i");
    super.new(name);
endfunction : new


constrained_trans_4 trans = constrained_trans_4::type_id::create("t");
virtual task body();
bit [31:0] addrarray[7] = {32'h3ff0_fff0, 32'h3ff1_fff0,32'h3ff2_fff0,32'h3ff3_fff0,32'h3ff4_fff0,32'h3ff5_fff0,32'h3ff2_fff0};

repeat(2)
begin
    for(int i=0; i<4; i++)
    begin 
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i],{address== addrarray[0] ;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i],{address== addrarray[1] ;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i],{address== addrarray[2] ;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i],{address== addrarray[3] ;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i],{address== addrarray[4] ;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i],{address== addrarray[6] ;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i],{address== addrarray[7] ;})
    end
end
    
    
endtask

endclass : ran_seq_read_hit_i