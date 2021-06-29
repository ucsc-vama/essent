circuit Testrsvd :
  module Break :
    input clk : Clock
    input case : UInt<1>
    input in_b : UInt<1>
    output out_c : UInt<1>
    output out_d : UInt<1>
    output out_e : UInt<1>


    reg my_reg : UInt<1>, clk with :
      reset => (UInt<1>("h0"), my_reg)
    node first = and(and(case, in_b), case)
    my_reg <= first
    out_c <= or(first, my_reg)
    out_e <= not(case)
    node abc = mux(first,my_reg,case)
    out_d <= abc

  module Testrsvd :
    input clk : Clock
    input in_0 : UInt<1>
    input in_1 : UInt<1>
    output out_2 : UInt<1>
    output out_3 : UInt<1>
    output out_4 : UInt<1>
    output out_5 : UInt<1>
    output out_6 : UInt<1>

    inst sub_inst1 of Break
    sub_inst1.clk <= clk
    sub_inst1.case <= in_0
    sub_inst1.in_b <= in_1
    out_2 <= sub_inst1.out_c
    out_3 <= sub_inst1.out_d
    out_6 <= sub_inst1.out_e
    inst sub_inst2 of Break
    sub_inst2.clk <= clk
    sub_inst2.case <= out_2
    sub_inst2.in_b <= sub_inst1.out_d
    out_4 <= sub_inst2.out_c
    out_5 <= sub_inst2.out_d

