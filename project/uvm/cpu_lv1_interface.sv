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

//ASSERTION2: cpu_rd and cpu_wr_done  should not be asserted at the same clock cycle
    property prop_simult_cpu_wr_done_cpu_rd;
        @(posedge clk)
          not(cpu_rd && cpu_wr_done);
    endproperty

    assert_simult_cpu_wr_done_cpu_rd: assert property (prop_simult_cpu_wr_done_cpu_rd)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion2 assert_simult_cpu_wr_done_cpu_rd Failed: cpu_wr_done and cpu_rd asserted simultaneously"))

//ASSERTION3: Deassert the cpu write in next cycle  when cpu write done 
    property prop_write_done;
        @(posedge clk)
          cpu_wr_done |=> (!cpu_wr);
    endproperty
    assert_cpu_write_done: assert property (prop_write_done)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion3 assert_cpu_write_done Failed: Deassert the cpu write in next cycle  when cpu write done"))


//ASSERTION4: 4: During CPU_RD, if data is present in the bus then Data_in_bus is asserted 
    property prop_data_in_bus;
        @(posedge clk)
          (data_bus_cpu_lv1_reg && cpu_rd) |-> data_in_bus_cpu_lv1 ; 
    endproperty

    assert_data_in_bus: assert property (prop_data_in_bus)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion-4 assert_data_actually_in_bus Failed: data_in_bus asserted incorrectly"))


// ASSERTION5: During cpu requests address has to be valid

    property proc_valid_address_in_cpu_req;
    @(posedge clk)
        (cpu_rd || cpu_wr) |-> (addr_bus_cpu_lv1[31:0] !== 32'bx);
    endproperty

    assert_valid_addr_cpu_req: assert property (proc_valid_address_in_cpu_req)
    else
       `uvm_error("cpu_lv1_interface",$sformatf("Assertion5 assert_valid_addr_cpu_req Failed: Cpu request address not valid")) 


//Assertion6: data in bus cpulvl1 next clock cycle cpu rd deasserted
    property prop_cpu_rd_done;
        @(posedge clk)
            data_in_bus_cpu_lv1 |=> (!cpu_rd);
    endproperty

    assert_cpu_rd_done: assert property (prop_cpu_rd_done)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion6 assert_cpu_rd_done Failed: Data copied into bus the cpu_rd is deasserted"))


endinterface
