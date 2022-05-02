//=====================================================================
// Project: 4 core MESI cache design
// File Name: cpu_lv1_interface.sv
// Description: Basic CPU-LV1 interface with assertions
// Designers: Venky & Suru
//=====================================================================


interface cpu_lv1_interface(input clk);

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    parameter DATA_WID_LV1           = `DATA_WID_LV1       ;
    parameter ADDR_WID_LV1           = `ADDR_WID_LV1       ;

    reg   [DATA_WID_LV1 - 1   : 0] data_bus_cpu_lv1_reg    ;

    wire  [DATA_WID_LV1 - 1   : 0] data_bus_cpu_lv1        ;
    logic [ADDR_WID_LV1 - 1   : 0] addr_bus_cpu_lv1        ;
    logic                          cpu_rd                  ;
    logic                          cpu_wr                  ;
    logic                          cpu_wr_done             ;
    logic                          data_in_bus_cpu_lv1     ;

    assign data_bus_cpu_lv1 = data_bus_cpu_lv1_reg ;

//Assertions
//ASSERTION1: cpu_wr and cpu_rd should not be asserted at the same clock cycle
    property prop_simult_cpu_wr_rd;
        @(posedge clk)
          not(cpu_rd && cpu_wr);
    endproperty

    assert_simult_cpu_wr_rd: assert property (prop_simult_cpu_wr_rd)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion assert_simult_cpu_wr_rd Failed: cpu_wr and cpu_rd asserted simultaneously"))




//TODO: Add assertions at this interface



//Assertion 2: DEASSERT THE CPU WRITE IN NEXT CYCLE WHEN CPU WRITE DONE 
   property prop_write_done;
        @(posedge clk)
          cpu_wr_done |=> (!cpu_wr);
    endproperty
    assert_cpu_write_done: assert property (prop_write_done)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion2 assert_cpu_write_done Failed: DEASSERT THE CPU WRITE IN NEXT CYCLE WHEN CPU WRITE DONE"))




//ASSERTION3: CPU_RD AND CPU_WR_DONE SHOULD NOT BE ASSERTED AT SAME CLOCK CYCLE 
    property prop_simult_cpu_wr_done_cpu_rd;
        @(posedge clk)
          not(cpu_rd && cpu_wr_done);
    endproperty

    assert_simult_cpu_wr_done_cpu_rd: assert property (prop_simult_cpu_wr_done_cpu_rd)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion3 assert_simult_cpu_wr_done_cpu_rd Failed: CPU_RD AND CPU_WR_DONE SHOULD NOT BE ASSERTED AT SAME CLOCK CYCLE"))



//AASSERTION 4: DATA IN BUS data_in_bus_cpu_lv1 THEN IN NEXT CYCLE cpu_rd DEASSERTED
    property prop_cpu_rd_done;
        @(posedge clk)
            data_in_bus_cpu_lv1 |=> (!cpu_rd);
    endproperty

    assert_cpu_rd_done: assert property (prop_cpu_rd_done)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion4 assert_cpu_rd_done Failed: DATA IN BUS data_in_bus_cpu_lv1 THEN IN NEXT CYCLE cpu_rd DEASSERTED"))



// ASSERTION 5: IF data_in_bus_cpu_lv1 IS ASSERTED, cpu_rd OR cpu_wr SHOULD BE HIGH
 property valid_data_in_bus_rd;
        @(posedge clk)
        $rose(data_in_bus_cpu_lv1) |-> (cpu_rd | cpu_wr);
    endproperty

    assert_valid_data_in_bus_rd: assert property (valid_data_in_bus_rd)
    else
        `uvm_error("cpu_lv1_interface", "Assertion-5 valid_data_in_bus_rd failed: data_in_bus_cpu_lv1 IS ASSERTED, cpu_rd OR cpu_wr SHOULD BE HIGH")




// ASSERTION 6: cpu_rd SHOULD BE FOLLOWED BY data_in_bus_cpu_lv1 AND BOTH SHOULD BE DEASSERTED 

property valid_rd_txn;
        @(posedge clk)
        cpu_rd |=> ##[0:$] data_in_bus_cpu_lv1 ##1 !cpu_rd ##1 !data_in_bus_cpu_lv1;
    endproperty

    assert_valid_rd_txn: assert property (valid_rd_txn)
    else
        `uvm_error("cpu_lv1_interface", "Assertion-6 valid_rd_txn failed: cpu_rd=>data_in_bus_cpu_lv1=>!cpu_rd=>!data_in_bus_cpu_lv1 sequence is not followed")



// ASSERTION7: DURING CPU REQUESTS ADDRESS HAS TO BE VALID

    property proc_valid_address_in_cpu_req;
    @(posedge clk)
        (cpu_rd || cpu_wr) |-> (addr_bus_cpu_lv1[31:0] !== 32'bx);
    endproperty

    assert_valid_addr_cpu_req: assert property (proc_valid_address_in_cpu_req)
    else
       `uvm_error("cpu_lv1_interface",$sformatf("Assertion7 assert_valid_addr_cpu_req Failed: During cpu requests address has to be valid")) 




//ASSERTION8: During CPU_RD, IF DATA IS PRESENT IN THE BUS THEN DATA_IN_BUS IS ASSERTED 
    property prop_data_in_bus;
        @(posedge clk)
          (data_bus_cpu_lv1_reg && cpu_rd) |-> data_in_bus_cpu_lv1 ; 
    endproperty

    assert_data_in_bus: assert property (prop_data_in_bus)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion-8 assert_data_actually_in_bus Failed: data_in_bus asserted incorrectly"))


endinterface
