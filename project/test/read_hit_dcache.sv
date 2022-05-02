//=====================================================================
// Project: 4 core MESI cache design
// File Name: read_hit_dcache.sv
// Description: Test for read-miss to I-cache
// Designers: Venky & Suru
//=====================================================================

class read_hit_dcache extends base_test;

    //component macro
    `uvm_component_utils(read_hit_dcache)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", read_hit_dcache_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing read_hit_dcache test" , UVM_LOW)
    endtask: run_phase

endclass : read_hit_dcache


// Sequence for a read-miss on D-cache
class read_hit_dcache_seq extends base_vseq;
    //object macro
    `uvm_object_utils(read_hit_dcache_seq)

    cpu_transaction_c trans;
    int i,j;
    bit [`ADDR_WID_LV1 - 1 : 0] trans_addr;

    random_dcache_address random_address_handle = new(); // Vaibhavi:  class in cpu_transaction_c.sv file

    //constructor
    function new (string name="read_hit_dcache_seq");
        super.new(name);
    endfunction : new

    virtual task body();
    assert( random_address_handle.randomize());
    random_address_handle.randomize_address();

    /***********************************************************************************************************************************************/
    // Read hit to all cpu dcache
    
    for(int i =0; i<4; i++) begin
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address inside {random_address_handle.random_addr};})
         trans_addr = trans.address;
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == trans_addr;})  
    end
    
    /***********************************************************************************************************************************************/
    // Read hit on complete set  4 writes 4 reads
    
    for ( j =0; j<4; j++)begin
    for( i =0; i<4; i++)begin
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[j], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == random_address_handle.random_addr[i]; data == i;}) //random data
    end
    for( i =0; i<4; i++)begin
      `uvm_do_on_with(trans, p_sequencer.cpu_seqr[j], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == random_address_handle.random_addr[i];})
    end
    end
    
    endtask

endclass : read_hit_dcache_seq