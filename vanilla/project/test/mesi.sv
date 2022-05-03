//=====================================================================
// Project: 4 core MESI cache design
// File Name: mesi.sv
// Description: Test for read-miss to I-cache
// Designers: group 8
//=====================================================================

class mesi extends base_test;

//component macro
`uvm_component_utils(mesi)

//Constructor
function new(string name, uvm_component parent);
    super.new(name, parent);
endfunction : new

//UVM build phase
function void build_phase(uvm_phase phase);
    //uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", MS_seq::type_id::get());
    //uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", MI_seq::type_id::get());
    //uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", ES_seq::type_id::get());
    //uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", EI_seq::type_id::get());
    //uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", SS_seq::type_id::get());
    //uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", IS_seq::type_id::get());
    //uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", IM_seq::type_id::get());
    uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", MSI_seq::type_id::get());
    super.build_phase(phase);
endfunction : build_phase

//UVM run phase()
task run_phase(uvm_phase phase);
    `uvm_info(get_type_name(), "Executing randomised test" , UVM_LOW)
endtask: run_phase

endclass : mesi


//constraints for mesi
class constrained_trans_5 extends cpu_transaction_c;
`uvm_object_utils(constrained_trans_5)

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
    unique {address} ;
}


//constraint for data
constraint data_rand_set {
    unique {data} ;
}

//accesss cache type   icache =0; dcache 1
constraint cache_type_set {
    access_cache_type ==  1;
}


//constraint for wait cycels   //Number of cycles to wait before driving the transactio

endclass: constrained_trans_5



//test for mesi
class MS_seq extends base_vseq;
//object macro
`uvm_object_utils(MS_seq)


//constructor
function new (string name="MS_seq");
    super.new(name);
endfunction : new


constrained_trans_5 trans = constrained_trans_5::type_id::create("t");
virtual task body();

bit [31:0] addrRand;
repeat(2)
begin
    
    for(int i=0; i<4; i++)
    begin
        for(int j=0; j<4; j++)
        begin
        addrRand = $urandom_range(32'h4000_0000,32'hffff_ffff);
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i], {request_type == 1; address == addrRand;})//write miss, data brought in, in M state
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[j], {address == addrRand;})//data read by different processor, state transitions from M to S
        `uvm_info(get_type_name(), "Testing MS sequence" , UVM_LOW)

        end
    end

end
    
    
endtask

endclass : MS_seq

class MI_seq extends base_vseq;
//object macro
`uvm_object_utils(MI_seq)


//constructor
function new (string name="MI_seq");
    super.new(name);
endfunction : new


constrained_trans_5 trans = constrained_trans_5::type_id::create("t");
virtual task body();

bit [31:0] addrRand;
repeat(2)
begin
    
    for(int i=0; i<4; i++)
    begin
        for(int j=0; j<4; j++)
        begin
        addrRand = $urandom_range(32'h4000_0000,32'hffff_ffff);
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i], {request_type == 1; address == addrRand;})//write miss, data brought in, in M state
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[j], {request_type == 1; address == addrRand;})//data write by different processor, state transitions from M to I
        `uvm_info(get_type_name(), "Testing MI sequence" , UVM_LOW)

        end
    end

end
    
    
endtask

endclass : MI_seq

class ES_seq extends base_vseq;
//object macro
`uvm_object_utils(ES_seq)


//constructor
function new (string name="ES_seq");
    super.new(name);
endfunction : new


constrained_trans_5 trans = constrained_trans_5::type_id::create("t");
virtual task body();

bit [31:0] addrRand;
repeat(2)
begin
    
    for(int i=0; i<4; i++)
    begin
        for(int j=0; j<4; j++)
        begin
        addrRand = $urandom_range(32'h4000_0000,32'hffff_ffff);
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i], {address == addrRand;})//read miss, data brought in, in E state
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[j], {address == addrRand;})//data read by different processor, state transitions from E to S
        `uvm_info(get_type_name(), "Testing ES sequence" , UVM_LOW)

        end
    end

end
    
    
endtask

endclass : ES_seq

class EI_seq extends base_vseq;
//object macro
`uvm_object_utils(EI_seq)


//constructor
function new (string name="EI_seq");
    super.new(name);
endfunction : new


constrained_trans_5 trans = constrained_trans_5::type_id::create("t");
virtual task body();

bit [31:0] addrRand;
repeat(2)
begin
    
    for(int i=0; i<4; i++)
    begin
        for(int j=0; j<4; j++)
        begin
        addrRand = $urandom_range(32'h4000_0000,32'hffff_ffff);
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i], {address == addrRand;})//read miss, data brought in, in E state
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[j], {request_type == 1; address == addrRand;})//data read by different processor, state transitions from E to S
        `uvm_info(get_type_name(), "Testing EI sequence" , UVM_LOW)

        end
    end

end
    
    
endtask

endclass : EI_seq

class SS_seq extends base_vseq;
//object macro
`uvm_object_utils(SS_seq)


//constructor
function new (string name="SS_seq");
    super.new(name);
endfunction : new


constrained_trans_5 trans = constrained_trans_5::type_id::create("t");
virtual task body();

bit [31:0] addrRand;
repeat(2)
begin
    
    for(int i=0; i<4; i++)
    begin
        for(int j=0; j<4; j++)
        begin
            for(int k=0; k<4; j++)
            begin
            addrRand = $urandom_range(32'h4000_0000,32'hffff_ffff);
                `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i], {request_type == 1; address == addrRand;})//write miss, data brought in, in M state
                `uvm_do_on_with(trans, p_sequencer.cpu_seqr[j], {address == addrRand;})//data read by different processor, state transitions from M to S
                `uvm_do_on_with(trans, p_sequencer.cpu_seqr[k], {address == addrRand;})//data read by different processor, state transitions from S to S
            end

        end
    end

end
    
    
endtask

endclass : SS_seq

class IS_seq extends base_vseq;
//object macro
`uvm_object_utils(IS_seq)


//constructor
function new (string name="IS_seq");
    super.new(name);
endfunction : new


constrained_trans_5 trans = constrained_trans_5::type_id::create("t");
virtual task body();

bit [31:0] addrRand;
repeat(2)
begin
    
    for(int i=0; i<4; i++)
    begin
        for(int j=0; j<4; j++)
        begin
        addrRand = $urandom_range(32'h4000_0000,32'hffff_ffff);
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i], {address == addrRand;})//read miss, data brought in, in E state
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[j], {request_type == 1; address == addrRand;})//data read by different processor, state transitions from E to I
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i], {address == addrRand;})//read miss, data brought in, in S state
        `uvm_info(get_type_name(), "Testing IS sequence" , UVM_LOW)

        end
    end

end
    
    
endtask

endclass : IS_seq

class IM_seq extends base_vseq;
//object macro
`uvm_object_utils(IM_seq)


//constructor
function new (string name="IM_seq");
    super.new(name);
endfunction : new


constrained_trans_5 trans = constrained_trans_5::type_id::create("t");
virtual task body();

bit [31:0] addrRand;
repeat(2)
begin
    
    for(int i=0; i<4; i++)
    begin
        for(int j=0; j<4; j++)
        begin
        addrRand = $urandom_range(32'h4000_0000,32'hffff_ffff);
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i], {address == addrRand;})//read miss, data brought in, in E state
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[j], {request_type == 1; address == addrRand;})//data read by different processor, state transitions from E to I
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i], {request_type == 1; address == addrRand;})//write miss, data brought in, in M state
        `uvm_info(get_type_name(), "Testing IM sequence" , UVM_LOW)

        end
    end

end
    
    
endtask

endclass : IM_seq

class MSI_seq extends base_vseq;
//object macro
`uvm_object_utils(MSI_seq)


//constructor
function new (string name="MSI_seq");
    super.new(name);
endfunction : new


constrained_trans_5 trans = constrained_trans_5::type_id::create("t");
virtual task body();

bit [31:0] addrRand;
repeat(2)
begin
    
    for(int i=0; i<4; i++)
    begin
        for(int j=0; j<4; j++)
        begin
        addrRand = $urandom_range(32'h4000_0000,32'hffff_ffff);
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i], {request_type == 1; address == addrRand;})//write miss, data brought in, in M state
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[j], {address == addrRand;})//data read by different processor, state transitions from M to S
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[j], {request_type == 1; address == addrRand;})//write miss, data brought in, from S to I state
        `uvm_info(get_type_name(), "Testing MSI sequence" , UVM_LOW)

        end
    end

end
    
    
endtask

endclass : MSI_seq