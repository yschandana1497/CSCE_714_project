//=====================================================================
// Project: 4 core MESI cache design
// File Name: write_hit_dcache.sv
// Description: Test for write hit D-cache
// Designers: group8
//=====================================================================

class write_hit_dcache extends base_test;

    //component macro
    `uvm_component_utils(write_hit_dcache)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", write_hit_dcache_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing write_hit_dcache test" , UVM_LOW)
    endtask: run_phase

endclass : write_hit_dcache


// Sequence for a write hit on D-cache
class write_hit_dcache_seq extends base_vseq;
    //object macro
    `uvm_object_utils(write_hit_dcache_seq)

    cpu_transaction_c trans;
    logic [`ADDR_WID_LV1 - 1 : 0] trans_addr;

    //constructor
    function new (string name="write_hit_dcache_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        /*BUG-5*/
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hFFFF_FFFF; })
        trans_addr = trans.address;
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == trans_addr; data == 32'hF0F0_F0F0;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == trans_addr;})
        

        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'h4444_4444;})
        trans_addr = trans.address;
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == trans_addr;data==32'h3333_3333})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == trans_addr;})


        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'h5555_5555})
        trans_addr = trans.address;
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == trans_addr; data == 32'h6666_6666})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == trans_addr;})


        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'h6666_6666})
        trans_addr = trans.address;
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == trans_addr; data == 32'h7777_7777})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == trans_addr;})

    endtask

endclass : write_hit_dcache_seq
