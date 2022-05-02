//=====================================================================
// Project: 4 core MESI cache design
// File Name: read_miss_icache.sv
// Description: Test for read-miss to I-cache
// Designers: Venky & Suru
//=====================================================================

class read_miss_icache extends base_test;

    //component macro
    `uvm_component_utils(read_miss_icache)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", read_miss_icache_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing read_miss_icache test" , UVM_LOW)
    endtask: run_phase

endclass : read_miss_icache


// Sequence for a read-miss on I-cache
class read_miss_icache_seq extends base_vseq;
    //object macro
    `uvm_object_utils(read_miss_icache_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="read_miss_icache_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[mp], {request_type == READ_REQ; access_cache_type == ICACHE_ACC;})

// Read miss free block not available

         `uvm_do_on_with(trans, p_sequencer.cpu_seqr[mp], {request_type == READ_REQ; access_cache_type == ICACHE_ACC; address == 32'h3000_0000;})
         `uvm_do_on_with(trans, p_sequencer.cpu_seqr[mp], {request_type == READ_REQ; access_cache_type == ICACHE_ACC; address == 32'h3001_0000;})
         `uvm_do_on_with(trans, p_sequencer.cpu_seqr[mp], {request_type == READ_REQ; access_cache_type == ICACHE_ACC; address == 32'h3002_0000;})
         `uvm_do_on_with(trans, p_sequencer.cpu_seqr[mp], {request_type == READ_REQ; access_cache_type == ICACHE_ACC; address == 32'h3003_0000;})
         `uvm_do_on_with(trans, p_sequencer.cpu_seqr[mp], {request_type == READ_REQ; access_cache_type == ICACHE_ACC; address == 32'h3004_0000;})
         `uvm_do_on_with(trans, p_sequencer.cpu_seqr[mp], {request_type == READ_REQ; access_cache_type == ICACHE_ACC; address == 32'h3005_0000;})
         `uvm_do_on_with(trans, p_sequencer.cpu_seqr[mp], {request_type == READ_REQ; access_cache_type == ICACHE_ACC; address == 32'h3002_0000;})
     
    endtask


endclass : read_miss_icache_seq
