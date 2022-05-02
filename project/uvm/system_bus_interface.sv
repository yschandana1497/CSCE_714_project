//=====================================================================
// Project: 4 core MESI cache design
// File Name: system_bus_interface.sv
// Description: Basic system bus interface including arbiter
// Designers: Venky & Suru
//=====================================================================

interface system_bus_interface(input clk);

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    parameter DATA_WID_LV1        = `DATA_WID_LV1       ;
    parameter ADDR_WID_LV1        = `ADDR_WID_LV1       ;
    parameter NO_OF_CORE            = 4;

    wire [DATA_WID_LV1 - 1 : 0] data_bus_lv1_lv2     ;
    wire [ADDR_WID_LV1 - 1 : 0] addr_bus_lv1_lv2     ;
    wire                        bus_rd               ;
    wire                        bus_rdx              ;
    wire                        lv2_rd               ;
    wire                        lv2_wr               ;
    wire                        lv2_wr_done          ;
    wire                        cp_in_cache          ;
    wire                        data_in_bus_lv1_lv2  ;

    wire                        shared               ;
    wire                        all_invalidation_done;
    wire                        invalidate           ;

    logic [NO_OF_CORE - 1  : 0]   bus_lv1_lv2_gnt_proc ;
    logic [NO_OF_CORE - 1  : 0]   bus_lv1_lv2_req_proc ;
    logic [NO_OF_CORE - 1  : 0]   bus_lv1_lv2_gnt_snoop;
    logic [NO_OF_CORE - 1  : 0]   bus_lv1_lv2_req_snoop;
    logic                       bus_lv1_lv2_gnt_lv2  ;
    logic                       bus_lv1_lv2_req_lv2  ;
    
    `define TIME_OUT_VAL 110 

//Assertions
//property that checks that signal_1 is asserted in the previous cycle of signal_2 assertion
    property prop_sig1_before_sig2(signal_1,signal_2);
    @(posedge clk)
        signal_2 |-> $past(signal_1);
    endproperty

//ASSERTION1: lv2_wr_done should not be asserted without lv2_wr being asserted in previous cycle
    assert_lv2_wr_done: assert property (prop_sig1_before_sig2(lv2_wr,lv2_wr_done))
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion assert_lv2_wr_done Failed: lv2_wr not asserted before lv2_wr_done goes high"))

//ASSERTION2: data_in_bus_lv1_lv2 and cp_in_cache should not be asserted without lv2_rd being asserted in previous cycle
 assert_signals_after_rd: assert property (prop_sig1_before_sig2(lv2_rd, data_in_bus_lv1_lv2 && cp_in_cache))
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion 2 assert_signals_after_rd Failed: lv2_rd not asserted before data_in_bus_lv1_lv2 and cp_in_cache go high"))


//TODO: Add assertions at this interface
//There are atleast 20 such assertions. Add as many as you can!!




// ASSERTION-3: all_invalidation_done should not be high without invalidate being high in previous cycle
    assert_invalidation_done_after_invalidate: assert property (prop_sig1_before_sig2(invalidate,all_invalidation_done))
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion 3 assert_invalidation_done_after_invalidate Failed: invalidate not asserted before all_invalidation_done goes high"))
    
// ASSERTION-4: bus_lv1_lv2_gnt_proc is mutually exclusive
    assert_mutually_exclusive_proc_gnt: assert property (prop_mutually_exclusive(bus_lv1_lv2_gnt_proc))
    else `uvm_error("system_bus_interface",$sformatf("Assertion 4 assert_mutually_exclusive_proc_gnt Failed: Grants to multiple processors at one time"))

// ASSERTION-5: bus_lv1_lv2_gnt_snoop is mutually exclusive
    assert_mutually_exclusive_snoop_gnt: assert property (prop_mutually_exclusive(bus_lv1_lv2_gnt_snoop))
    else `uvm_error("system_bus_interface",$sformatf("Assertion 5 assert_mutually_exclusive_gnt_snoop Failed: Grants to multiple snoop at one time"))  
	
// ASSERTION-6: If lv2_wr is deasserted, lv2_wr_done is deasserted
  assert_lv2_wr_deasserted: assert property (prop_deasserted_signals(lv2_wr,lv2_wr_done))
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion 6 assert_lv2_wr_deasserted: lv2_wr_done not deasserted "))
	
// ASSERTION-7: If data_in_bus_lv1_lv2 is raised without cp_in_cache, bus_lv1_lv2_gnt_lv2 should be asserted in previous cycle and same cycle
    assert_data_in_bus: assert property (prop_sig1_before_and_during_sig2(bus_lv1_lv2_gnt_lv2, data_in_bus_lv1_lv2 && !cp_in_cache))
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion 7 assert_data_in_bus Failed: data_in_bus_lv1_lv2 asserted without bus_lv1_lv2_gnt_lv2 or cp_in_cache high"))
	
// ASSERTION-8: If lv2_rd is asserted bus_rd or bus_rdx must be asserted
    assert_bus_rd: assert property (@(posedge clk) ((lv2_rd) && (addr_bus_lv1_lv2[31:30] != 2'b0))|-> (bus_rd || bus_rdx))
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion 8 assert_bus_rd Failed: bus_rd not asserted when lv2_rd goes high"))
	

// ASSERTION-9:  If bus_lv1_lv2_gnt_lv2 is raised, bus_lv1_lv2_req_lv2 should be asserted in previous and same cycle
    assert_req_before_gnt_bus: assert property (prop_sig1_before_and_during_sig2(bus_lv1_lv2_req_lv2, bus_lv1_lv2_gnt_lv2))
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion 9 assert_req_before_gnt_bus Failed: bus_lv1_lv2_gnt_lv2 asserted without bus_lv1_lv2_req_lv2 high"))

//ASSERTION-10: If cp_in_cache is asserted, bus_lv1_lv2_req_lv2 will be dropped
    assert_drop_req: assert property (@(posedge clk) cp_in_cache |=> (!bus_lv1_lv2_req_lv2))
    else
    `uvm_error("system_bus_interface", $sformatf("Assertion 10 assert_drop_req failed: bus_lv1_lv2_req_lv2  not dropped when cp_in_cache is asserted"))

//ASSERTION-11: If shared is asserted, bus_rd or bus_rdx or invalidate must be asserted in previous cycle
    assert_shared_after_bus_rd: assert property (prop_sig1_before_sig2((bus_rd | bus_rdx | invalidate), shared))
    else
    `uvm_error("system_bus_interface", $sformatf("Assertion 11 assert_shared_after_bus_rd failed: bus_rd(x) or invalidate is not asserted before shared is asserted"))

//ASSERTION-12: If shared is asserted, data_in_bus must be asserted or all_invalidation done must be high
    assert_shared_and_data_in_bus: assert property (@(posedge clk) shared |-> data_in_bus_lv1_lv2 | all_invalidation_done)
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion 12 assert_shared_and_data_in_bus Failed: Shared asserted without data_in_bus or without invalidation"))

//ASSERTION-13: bus_rd and bus_rdx are mutually exclusive
    assert_bus_rd_and_rdx_exclusive: assert property (@(posedge clk) not(bus_rd && bus_rdx))
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion 13 assert_bus_rd_and_rdx_exclusive Failed: bus_rd and bus_rdx asserted together"))

//ASSERTION-14: If invalidate asserted, bus_lv1_lv2_gnt_proc must be asserted in previous cycle and same cycle
    assert_gnt_before_invalidate: assert property (prop_sig1_before_and_during_sig2(bus_lv1_lv2_gnt_proc, invalidate))
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion 14 assert_gnt_before_invalidate Failed: invalidate asserted without bus_lv1_lv2_gnt_proc high"))


//ASSERTION-15: When cp_in_cache is asserted, bus_lv1_lv2_gnt_lv2 must be deasserted 
    assert_cp_in_cache_no_gnt: assert property (@(posedge clk) cp_in_cache |-> !bus_lv1_lv2_gnt_lv2)
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion 15 assert_cp_in_cache_no_gnt Failed: bus_lv1_lv2_gnt_lv2 is high when cp_in_cache asserted"))

//ASSERTION-16: data_in_bus_lv1_lv2 is deasserted after lv2_rd drops 
    assert_data_deasserted_after_rd: assert property (@(posedge clk) $fell(data_in_bus_lv1_lv2) -> (!lv2_rd))
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion 16 assert_data_deasserted_after_rd Failed: data_in_bus is de-asserted before lv2_rd"))

//ASSERTION-17: If bus_lv1_lv2_req_lv2  asserted then lv2_rd or lv2_wr asserted in previous cycle
    assert_req_after_bus_rd_wr: assert property (prop_sig1_before_sig2((lv2_rd || lv2_wr), bus_lv1_lv2_req_lv2))
    else
    `uvm_error("system_bus_interface", $sformatf("Assertion 17 assert_req_after_bus_rd_wr failed: lv1_rd or lv2_wr is not asserted before bus_lv1_lv2_req_lv2 is asserted"))
//ASSERTION-18: No grant without request for proc - 0, 1, 2, 3
    assert_req_before_gnt_proc: assert property (@(posedge clk) (bus_lv1_lv2_gnt_proc & $past(bus_lv1_lv2_req_proc)) == bus_lv1_lv2_gnt_proc )
    else
    `uvm_error("system_bus_interface", $sformatf("Assertion 18 assert_req_before_gnt_proc failed: proc_req is not asserted before proc_gnt is asserted"))

//ASSERTION-19: 
    assert_req_before_gnt_snoop: assert property (@(posedge clk) (bus_lv1_lv2_gnt_snoop & $past(bus_lv1_lv2_req_snoop)) == bus_lv1_lv2_gnt_snoop )
    else
    `uvm_error("system_bus_interface", $sformatf("Assertion 19 assert_req_before_gnt_proc failed: snoop_req is not asserted before snoop_gnt is asserted"))

//ASSERTION-20: Address is present in address bus during lv2_rd and lv2_wr
    assert_address_rd_wr: assert property (@(posedge clk) (lv2_rd || lv2_wr) |-> ((addr_bus_lv1_lv2[31:0] !== 32'hx) || (addr_bus_lv1_lv2[31:0] !== 32'hz)) )
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion 20 assert_address_rd_wr Failed: lv2 rd or wr asserted without address bus"))



// Assertion 21: Bus request eventually granted
property liveness_l1_l2;
        @(posedge clk)
        ($rose(bus_lv1_lv2_request_proc)) |=> ##[0:`TIME_OUT_VAL] ($rose(bus_lv1_lv2_grant_proc));
    endproperty


    assert_liveness_l1_l2: assert property (liveness_l1_l2)
    else
    `uvm_error("system_bus_interface", "Assertion-21 liveness_l1_l2 failed")

// Assertion 22: Snoop request eventually granted
property liveness_l1_l2_snoop;
        @(posedge clk)
       ($rose(bus_lv1_lv2_request_snoop)) |=> ##[0:`TIME_OUT_VAL] ($rose(bus_lv1_lv2_grant_snoop));
    endproperty


    assert_liveness_l1_l2_snoop: assert property (liveness_l1_l2_snoop)
    else
    `uvm_error("system_bus_interface", "Assertion-22 liveness_l1_l2_snoop failed")

// Assertion 23: Level-2 request eventually granted
property liveness_l1_l2_lv2;
        @(posedge clk)
        ($rose(bus_lv1_lv2_req_lv2_bit)) |=> ##[0:`TIME_OUT_VAL] ($rose(bus_lv1_lv2_gnt_lv2_bit || cp_in_cache));
    endproperty


    assert_liveness_l1_l2_lv2: assert property (liveness_l1_l2_lv2)
    else
    `uvm_error("system_bus_interface", "Assertion-23 liveness_l1_l2_lv2 failed")


//Assertion 24: Bus request asserted within TIME_OUT_VAL clock cycles of Bus RD or Bus RDX

    assert_req_after_rd: assert property (@(posedge clk)((bus_rd_bit)) |=> ##[0:`TIME_OUT_VAL] ((bus_lv1_lv2_request_proc)))
    else
    `uvm_error("system_bus_interface", "Assertion-24 failed: Bus access not requested after bus_rd(x)")


//Assertion 25: Lv2 Write Done asserted within TIME_OUT_VAL clock cycles of Lv2 Write

    assert_wr_done_after_wr: assert property (@(posedge clk)(lv2_wr) |=> ##[0:`TIME_OUT_VAL] lv2_wr_done)
    else
    `uvm_error("system_bus_interface", "Assertion-25 ")


endinterface
