//=====================================================================
// Project: 4 core MESI cache design
// File Name: write_miss_dcache.sv
// Description: Test for various write_miss_dcache transitions
// Designers: group8
//=====================================================================

class write_miss_dcache extends base_test;

    //component macro
    `uvm_component_utils(write_miss_dcache)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", write_miss_seq::type_id::get());

        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing write_miss_dcache test" , UVM_LOW)
    endtask: run_phase

endclass : write_miss_dcache


// Sequence for a Modified to Shared transition
class write_miss_seq extends base_vseq;
    //object macro
    `uvm_object_utils(write_miss_seq)

    cpu_transaction_c trans;
    logic [`ADDR_WID_LV1 - 1 : 0] trans_addr;
    //constructor
    function new (string name="write_miss_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; })
        trans_addr = trans.address;

        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == trans_addr; data == 32'h0101_0101;})

        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == trans_addr;})

         `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC;})
        trans_addr = trans.address;
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == trans_addr; data == 32'hF001_F101;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == trans_addr;})

        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC;})
        trans_addr = trans.address;
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == trans_addr; data == 32'hF341_F011;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == trans_addr;})
        
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC;})
        trans_addr = trans.address;
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == trans_addr; data == 32'hF021_F031;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == trans_addr;})

        
    endtask

endclass : write_miss_seq