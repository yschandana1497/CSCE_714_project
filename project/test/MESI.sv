//=====================================================================
// Project: 4 core MESI cache design
// File Name: MESItest.sv
// Description: Test for various MESI transitions
// Designers: Bhavesh
//=====================================================================

class MESItest extends base_test;

    //component macro
    `uvm_component_utils(MESItest)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        //uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", MS_seq::type_id::get());
        //uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", MI_seq::type_id::get());
        //uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", IS_seq::type_id::get());
        //uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", IM_seq::type_id::get());
        //uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", EI_seq::type_id::get());
        //uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", ES_seq::type_id::get());
        //uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", SS_seq::type_id::get());
	  uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", MSI_Seq::type_id::get());

        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Testing MESI test" , UVM_LOW)
    endtask: run_phase

endclass : MESItest

//// Modified to Shared Sequence////

class MS_seq extends base_vseq;
    //object macro
    `uvm_object_utils(MS_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="MS_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'hFEDC_CDEF; data == 32'hABCD_EF01;})//write miss, data brought in, in M state
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hFEDC_CDEF;})//data read by proc1, state transitions from M to S
        `uvm_info(get_type_name(), "Testing MS sequence" , UVM_LOW)
    endtask

endclass : MS_seq

//// Modified to Invalid Sequence////

class MI_seq extends base_vseq;
    //object macro
    `uvm_object_utils(MI_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="MI_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'hFEDC_CDEF; data == 32'hEF01_ABCD;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'hFEDC_CDEF; data == 32'hABCD_EF01;})
        `uvm_info(get_type_name(), "Testing MI sequence" , UVM_LOW)
    endtask

endclass : MI_seq

//// Invalid to Shared Sequence////

class IS_seq extends base_vseq;
    //object macro
    `uvm_object_utils(IS_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="IS_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hFEDC_CDEF;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'hFEDC_CDEF; data == 32'hABCD_EF01;}) //0 is Invalid
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hFEDC_CDEF;}) // 0 is in Shared again
        `uvm_info(get_type_name(), "Testing IS sequence" , UVM_LOW)
    endtask

endclass : IS_seq

//// Invalid to Modified Sequence////

class IM_seq extends base_vseq;
    //object macro
    `uvm_object_utils(IM_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="IM_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hFEDC_CDEF;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'hFEDC_CDEF; data == 32'hEF01_ABCD;}) 
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'hFEDC_CDEF; data == 32'hABCD_EF01;})  
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hFEDC_CDEF;})
        `uvm_info(get_type_name(), "Executing I_to_M sequence" , UVM_LOW)
    endtask

endclass : IM_seq

//// Exclusive to Invalid Sequence////

class EI_seq extends base_vseq;
    //object macro
    `uvm_object_utils(EI_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="EI_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hFEDC_CDEF;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'hFEDC_CDEF; data == 32'hABCD_EF01;})
        `uvm_info(get_type_name(), "Testing EI sequence" , UVM_LOW)
    endtask

endclass : EI_seq

//// Exclusive to Shared Sequence////

class ES_seq extends base_vseq;
    //object macro
    `uvm_object_utils(ES_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="ES_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hFEDC_CDEF;})//read miss, data brought in, in E state
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hFEDC_CDEF;})//data read by proc1, state transitions from M to S
        `uvm_info(get_type_name(), "Testing ES sequence" , UVM_LOW)
    endtask

endclass : ES_seq

//// Shared to Shared Sequence////

class SS_seq extends base_vseq;
    //object macro
    `uvm_object_utils(SS_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="SS_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'hFEDC_CDEF; data == 32'hABCD_EF01;})//write miss, data brought in, in M state
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hFEDC_CDEF;})//data read by proc1, state transitions from M to S
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hFEDC_CDEF;})//data read by proc2, state transitions from S to S
        `uvm_info(get_type_name(), "Testing SS sequence" , UVM_LOW)
    endtask

endclass : SS_seq


//// Modified to Shared to Invalid Sequence////

class MSI_Seq extends base_vseq;
    //object macro
    `uvm_object_utils(MSI_Seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="MSI_Seq");
        super.new(name);
    endfunction : new

    virtual task body();
	`uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'hFEDC_CDEF; data == 32'hABCD_EF01;})
      `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hFEDC_CDEF;})
      `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'hFEDC_CDEF; data == 32'hEF01_ABCD;})
      `uvm_info(get_type_name(), "Testing MSI sequence" , UVM_LOW)
    endtask

endclass : MSI_Seq