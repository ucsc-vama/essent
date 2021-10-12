circuit Testrsvd :
  module Break :
    input clk : Clock
    input case$ : UInt<1>
    input in_b : UInt<1>
    output out_c : UInt<1>
    output out_d : UInt<1>
    output out_e : UInt<1>

    reg my_reg : UInt<1>, clk with :
      reset => (UInt<1>("h0"), my_reg)
    node _GEN_0 = and(case$, in_b)
    node first = and(_GEN_0, case$)
    out_c <= or(first, my_reg)
    out_d <= mux(first, my_reg, case$)
    out_e <= not(case$)
    my_reg <= and(_GEN_0, case$)

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
    inst sub_inst2 of Break
    out_2 <= sub_inst1.out_c
    out_3 <= sub_inst1.out_d
    out_4 <= sub_inst2.out_c
    out_5 <= sub_inst2.out_d
    out_6 <= sub_inst1.out_e
    sub_inst1.clk <= clk
    sub_inst1.case$ <= in_0
    sub_inst1.in_b <= in_1
    sub_inst2.clk <= clk
    sub_inst2.case$ <= out_2
    sub_inst2.in_b <= sub_inst1.out_d

