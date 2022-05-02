//=====================================================================
// Project: 4 core MESI cache design
// File Name: MESI.sv
// Description: Test for various MESI transitions
// Designers: group8
//=====================================================================

class MESI extends base_test;

    //component macro
    `uvm_component_utils(MESI)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        //uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", M_to_S_seq::type_id::get());
        //uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", E_to_S_seq::type_id::get());
        //uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", S_to_S_seq::type_id::get());
        //uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", I_to_S_seq::type_id::get());
        //uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", M_to_I_seq::type_id::get());
        //uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", E_to_I_seq::type_id::get());
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", M_S_I_S_Seq::type_id::get());

        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing MESI test" , UVM_LOW)
    endtask: run_phase

endclass : MESI


// Sequence for a Modified to Shared transition
class M_to_S_seq extends base_vseq;
    //object macro
    `uvm_object_utils(M_to_S_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="M_to_S_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[mp], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'hF111_F111; data == 32'hF000_000F;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[sp1], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hF111_F111;})
        `uvm_info(get_type_name(), "Executing M_to_S sequence" , UVM_LOW)
    endtask

endclass : M_to_S_seq

class E_to_S_seq extends base_vseq;
    //object macro
    `uvm_object_utils(E_to_S_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="E_to_S_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[mp], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hF111_F111;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[sp1], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hF111_F111;})
        `uvm_info(get_type_name(), "Executing E_to_S sequence" , UVM_LOW)
    endtask

endclass : E_to_S_seq

class S_to_S_seq extends base_vseq;
    //object macro
    `uvm_object_utils(S_to_S_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="S_to_S_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[mp], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'hF111_F111; data == 32'hF000_000F;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[sp1], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hF111_F111;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[sp2], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hF111_F111;})
        `uvm_info(get_type_name(), "Executing S_to_S sequence" , UVM_LOW)
    endtask

endclass : S_to_S_seq

class E_to_I_seq extends base_vseq;
    //object macro
    `uvm_object_utils(E_to_I_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="E_to_I_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[mp], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hF111_F111;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[sp1], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'hF111_F111; data == 32'h1234_5678;})
        `uvm_info(get_type_name(), "Executing E_to_I sequence" , UVM_LOW)
    endtask

endclass : E_to_I_seq

class I_to_S_seq extends base_vseq;
    //object macro
    `uvm_object_utils(I_to_S_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="I_to_S_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[mp], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hF111_F111;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[sp1], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'hF111_F111; data == 32'h1234_5678;}) //mp is Invalid
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[mp], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hF111_F111;}) // mp is in Shared again
        `uvm_info(get_type_name(), "Executing I_to_S sequence" , UVM_LOW)
    endtask

endclass : I_to_S_seq

class M_to_I_seq extends base_vseq;
    //object macro
    `uvm_object_utils(M_to_I_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="M_to_I_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[mp], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'hF111_F111; data == 32'h0000_0000;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[sp1], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'hF111_F111; data == 32'h1234_5678;})
        `uvm_info(get_type_name(), "Executing M_to_I sequence" , UVM_LOW)
    endtask

endclass : M_to_I_seq

class M_S_I_S_Seq extends base_vseq;
    //object macro
    `uvm_object_utils(M_S_I_S_Seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="M_S_I_S_Seq");
        super.new(name);
    endfunction : new

    virtual task body();
	`uvm_do_on_with(trans, p_sequencer.cpu_seqr[mp], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'hF111_F111; data == 32'hF011_000F;})

        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[sp1], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hF111_F111;})

        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[sp1], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'hF111_F111; data == 32'h1234_1234;})

	    `uvm_do_on_with(trans, p_sequencer.cpu_seqr[sp1], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hF111_F111;})

        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[mp], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'hF111_F111;})

        `uvm_info(get_type_name(), "Executing S_to_I sequence" , UVM_LOW)
    endtask

endclass : M_S_I_S_Seq
