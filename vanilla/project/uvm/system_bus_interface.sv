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

bit bus_lv1_lv2_req_lv2_bit;
bit bus_lv1_lv2_gnt_lv2_bit;
bit bus_lv1_lv2_request_snoop;
bit bus_lv1_lv2_grant_snoop;
bit bus_lv1_lv2_request_proc;
bit bus_lv1_lv2_grant_proc;
bit bus_rd_bit;
bit bus_rdx_bit;

assign bus_lv1_lv2_request_proc = bus_lv1_lv2_req_proc[0] | bus_lv1_lv2_req_proc[1] | bus_lv1_lv2_req_proc[2] | bus_lv1_lv2_req_proc[3];
assign bus_lv1_lv2_grant_proc = bus_lv1_lv2_gnt_proc[0] | bus_lv1_lv2_gnt_proc[1] | bus_lv1_lv2_gnt_proc[2]| bus_lv1_lv2_gnt_proc[3];
assign bus_lv1_lv2_request_snoop = bus_lv1_lv2_req_snoop[0] | bus_lv1_lv2_req_snoop[1] | bus_lv1_lv2_req_snoop[2] | bus_lv1_lv2_req_snoop[3];
assign bus_lv1_lv2_grant_snoop = bus_lv1_lv2_gnt_snoop[0] | bus_lv1_lv2_gnt_snoop[1] | bus_lv1_lv2_gnt_snoop[2] | bus_lv1_lv2_gnt_snoop[3];
assign bus_rd_bit  = bus_rd;
assign bus_rdx_bit = bus_rdx;

//Assertions
//property that checks that signal_1 is asserted in the previous cycle of signal_2 assertion
    property prop_sig1_before_sig2(signal_1,signal_2);
    @(posedge clk)
        signal_2 |-> $past(signal_1);
    endproperty
    property prop_deasserted_signals(signal_1,signal_2);
    @(posedge clk)
       $fell(signal_2) |-> (!signal_1); // When signal-2 falls, signal-1 should be 0
    endproperty	
    property prop_sig1_before_and_during_sig2(signal_1,signal_2);
     @(posedge clk)
            signal_2 |-> ($past(signal_1) && signal_1); // When signal-2 asserted, signal-1 asserted in previous cycle as well as current cycle
    endproperty
    property prop_mutually_exclusive(signal);
    @(posedge clk)
        $onehot0(signal); // All bits of signal mutually exclusive
    endproperty



//ASSERTION1: lv2_wr_done should not be asserted without lv2_wr being asserted in previous cycle
    assert_lv2_wr_done: assert property (prop_sig1_before_sig2(lv2_wr,lv2_wr_done))
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion assert_lv2_wr_done Failed: lv2_wr not asserted before lv2_wr_done goes high"))

//ASSERTION2: data_in_bus_lv1_lv2 and cp_in_cache should not be asserted without lv2_rd being asserted in previous cycle
        assert_data_in_bus_lv1_lv2_and_cp_in_cache: assert property (prop_sig1_before_sig2(lv2_rd, data_in_bus_lv1_lv2 && cp_in_cache))
        else
        `uvm_error("system_bus_interface",$sformatf("Assertion 2 assert_data_in_bus_lv1_lv2_and_cp_in_cache Failed: lv2_rd not asserted before data_in_bus_lv1_lv2 and cp_in_cache goes high"))

//TODO: Add assertions at this interface
//There are atleast 20 such assertions. Add as many as you can!!
//Assertion 3:lv2_wr is made LOW only after lv2_wr_done is HIGH

        assert_lv2_wr_low_after_lv2_wr_done_high: assert property (@(posedge clk)($rose(lv2_wr_done) |-> lv2_wr))
        else
        `uvm_error("system_bus_interface", "Assertion 3 assert_lv2_wr_low_after_lv2_wr_done_high Failed: Before lv2_wr_done is asserted lv2_wr is becoming low")
//Assertion 4: 
 //ASSERTION 4: After lv2_rd goes low, data_in_bus_lv1_lv2 should be deasserted 
        assert_data_in_deasserted_after_lv2_rd_low: assert property (@(posedge clk) $fell(data_in_bus_lv1_lv2) -> (!lv2_rd))
        else
        `uvm_error("system_bus_interface",$sformatf("Assertion 4 assert_data_in_deasserted_after_lv2_rd_low Failed: data_in_bus is de-asserted before lv2_rd"))

//ASSERTION-5: After lv2_wr or lv2_rd is asserted then address should be present address bus 
        assert_lv2_rd_or_lv2_wr_address_bus: assert property (@(posedge clk) (lv2_rd || lv2_wr) |-> ((addr_bus_lv1_lv2[31:0] !== 32'hx) || (addr_bus_lv1_lv2[31:0] !== 32'hz)) )
        else
        `uvm_error("system_bus_interface",$sformatf("Assertion 5 assert_lv2_rd_or_lv2_wr_address_bus Failed:  Address not present in address bus after lv2 rd or lv2 wr is asserted "))
//ASSERTION-6: bus_rd and bus_rdx are not asserted together.
        assert_bus_rd_and_bus_rdx_not_together: assert property (@(posedge clk) not(bus_rd && bus_rdx))
        else
        `uvm_error("system_bus_interface",$sformatf("Assertion 6 assert_bus_rd_and_rdx_not_together Failed: bus_rd and bus_rdx asserted together"))


    // ASSERTION-7: bus_rd or bus_rdx must be asserted if lv2_rd is asserted
        assert_bus_rd_or_bus_rdx_after_lv2_rd: assert property (@(posedge clk) ((lv2_rd) && (addr_bus_lv1_lv2[31:30] != 2'b0))|-> (bus_rd || bus_rdx))
        else
        `uvm_error("system_bus_interface",$sformatf("Assertion 7 assert_bus_rd_or_bus_rdx_after_lv2_rd Failed: bus_rd or bus_rdx not asserted when lv2_rd goes high"))
//ASSERTION-8: when lv2_rd or lv2_wr gets asserted in previous cycle then bus_lv1_lv2_req_lv2 should be asserted in current cycle
        assert_bus_lv1_lv2_req_after_lv2_rd_or_lv2_wr_pc: assert property (prop_sig1_before_sig2((lv2_rd || lv2_wr), bus_lv1_lv2_req_lv2))
        else
        `uvm_error("system_bus_interface", $sformatf("Assertion 8 assert_bus_lv1_lv2_req_after_lv2_rd_or_lv2_wr_pc Failed: lv2_rd or lv2_wr is not asserted before bus_lv1_lv2_req_lv2 is asserted"))
//ASSERTION-9: bus_lv1_lv2_gnt_lv2 is  deasserted when cp_in_cache asserted 
        assert_bus_lv1_lv2_gnt_lv2_low_when_cp_in_cache_high: assert property (@(posedge clk) cp_in_cache |-> !bus_lv1_lv2_gnt_lv2)
        else
        `uvm_error("system_bus_interface",$sformatf("Assertion 9 assert_bus_lv1_lv2_gnt_lv2_low_when_cp_in_cache_high: Failed: when cp_in_cache asserted bus_lv1_lv2_gnt_lv2 is also high"))
 //ASSERTION-10: If cp_in_cache is HIGH, bus_lv1_lv2_req_lv2 will be LOW
        assert_cp_in_cache_high_bus_lv1_lv2_req_lv2_drop: assert property (@(posedge clk) cp_in_cache |=> (!bus_lv1_lv2_req_lv2))
        else
        `uvm_error("system_bus_interface", $sformatf("Assertion 10 assert_cp_in_cache_high_bus_lv1_lv2_req_lv2_drop Failed: bus_lv1_lv2_req_lv2  not low when cp_in_cache is high"))
 // ASSERTION-11: : if data_in_bus_lv1_lv2 is asserted with cp_in_cache not being asserted, bus_lv1_lv2_gnt_lv2 should be asserted in previous cycle
        assert_data_in_bus_high_before_cp_in_cache_low_and_bus_lv1_lv2_gnt_lv2: assert property (prop_sig1_before_and_during_sig2(bus_lv1_lv2_gnt_lv2, data_in_bus_lv1_lv2 && !cp_in_cache))
        else
        `uvm_error("system_bus_interface",$sformatf("Assertion 11 assert_data_in_bus_high_before_cp_in_cache_low_and_bus_lv1_lv2_gnt_lv2 Failed: data_in_bus_lv1_lv2 asserted without bus_lv1_lv2_gnt_lv2 or cp_in_cache high"))
// ASSERTION 12: : invalidate goes high, then all_invalidation done goes high in next cycle
        assert_all_invalidation_done_after_invalidate_goes_high: assert property (prop_sig1_before_sig2(invalidate,all_invalidation_done))
        else
        `uvm_error("system_bus_interface",$sformatf("Assertion 12 assert_all_invalidation_done_after_invalidate_goes_high Failed: all_invalidation_done goes high before invalidate is not asserted"))
 //ASSERTION-13: invalidate asserted only when bus_lv1_lv2_gnt_proc must be asserted in previous cycle and same cycle
        assert_bus_lv1_lv2_gnt_proc_before_invalidate: assert property (prop_sig1_before_and_during_sig2(bus_lv1_lv2_gnt_proc, invalidate))
        else
        `uvm_error("system_bus_interface",$sformatf("Assertion 13 assert_bus_lv1_lv2_gnt_proc_before_invalidate Failed: invalidate asserted without bus_lv1_lv2_gnt_proc is high "))     
 //ASSERTION-14: shared is asserted only when all_invalidation_done or data_in_bus must be asserted must be HIGH
        assert_shared_when_all_invalidation_done_or_data_in_bus_high: assert property (@(posedge clk) shared |-> data_in_bus_lv1_lv2 | all_invalidation_done)
        else
        `uvm_error("system_bus_interface",$sformatf("Assertion 14 assert_shared_when_all_invalidation_done_or_data_in_bus_high Failed: Shared is asserted without data_in_bus_lv1_lv2 or all_invalidation_done being asserted"))
 
 //ASSERTION-15:If shared is asserted, then bus_rd/bus_rdx/invalidate should be be asserted in the previous cycle
        assert_shared_after_bus_rd_bus_rdx_invalidate: assert property (prop_sig1_before_sig2((bus_rd | bus_rdx | invalidate), shared))
        else
        `uvm_error("system_bus_interface", $sformatf("Assertion 15 assert_shared_after_bus_rd_bus_rdx_invalidate Failed: bus_rd or bus_rdx or invalidate is not asserted before shared is asserted"))
//ASSERTION-16: No request from any processor so there is no grant
        assert_no_req_before_so_no_gnt_for_proc: assert property (@(posedge clk) (bus_lv1_lv2_gnt_proc & $past(bus_lv1_lv2_req_proc)) == bus_lv1_lv2_gnt_proc )
        else
        `uvm_error("system_bus_interface", $sformatf("Assertion 16 assert_no_req_before_so_no_gnt_for_proc failed: proc_req is not asserted before proc_gnt is asserted"))
//ASSERTION-17: 
        assert_no_req_before_so_no_gnt_for_snoop: assert property (@(posedge clk) (bus_lv1_lv2_gnt_snoop & $past(bus_lv1_lv2_req_snoop)) == bus_lv1_lv2_gnt_snoop )
        else
        `uvm_error("system_bus_interface", $sformatf("Assertion 17 assert_no_req_before_so_no_gnt_for_proc failed: snoop_req is not asserted before snoop_gnt is asserted"))
//Assertion 18: When bus_rd or bus_rdx is high then bus_lv1_lv2_request_proc should be high within a definite number of cycles
        assert_req_after_bus_rd_or_bus_rdx: assert property (@(posedge clk)((bus_rd_bit)) |=> ##[0:`TIME_OUT_VAL] ((bus_lv1_lv2_request_proc)))
        else
        `uvm_error("system_bus_interface", "Assertion-18 failed: bus request is not asserted after bus_rd or bus_rdx")


//Assertion 19: lv2_wr_done should be asserted within TIME_OUT_VAL clock cycles of lv2_write
        assert_lv2_wr_done_after_lv2_wr: assert property (@(posedge clk)(lv2_wr) |=> ##[0:`TIME_OUT_VAL] lv2_wr_done)
        else
        `uvm_error("system_bus_interface", "Assertion-19 Failed: lv2_wr_done is not getting asserted after lv2_wr ")

endinterface
