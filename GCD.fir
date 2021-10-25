 circuit GCD :
  module GCD : 
    input clk : Clock
    input reset : UInt<1>
    output io : {flip a : UInt<16>, flip b : UInt<16>, flip e : UInt<1>, z : UInt<16>, v : UInt<1>}
    
    io is invalid
    reg x : UInt, clk
    reg y : UInt, clk
    node T_7 = gt(x, y)
    when T_7 :
      node T_8 = sub(x, y)
      node T_9 = tail(T_8, 1)
      x <= T_9
      skip
    node T_10 = gt(x, y)
    node T_12 = eq(T_10, UInt<1>("h00"))
    when T_12 :
      node T_13 = sub(y, x)
      node T_14 = tail(T_13, 1)
      y <= T_14
      skip
    when io.e :
      x <= io.a
      y <= io.b
      skip
    io.z <= x
    node T_16 = eq(y, UInt<1>("h00"))
    io.v <= T_16