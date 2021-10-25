#ifndef GCD_H_
#define GCD_H_

#include <array>
#include <cstdint>
#include <cstdlib>
#include <uint.h>
#include <sint.h>
#define UNLIKELY(condition) __builtin_expect(static_cast<bool>(condition), 0)

typedef struct GCD {
  UInt<16> x;
  UInt<16> y;
  UInt<1> clk;
  UInt<1> reset;
  UInt<16> io_a;
  UInt<16> io_b;
  UInt<1> io_e;
  UInt<16> io_z;
  UInt<1> io_v;

  GCD() {
    x.rand_init();
    y.rand_init();
    reset.rand_init();
    io_a.rand_init();
    io_b.rand_init();
    io_e.rand_init();
    io_z.rand_init();
    io_v.rand_init();
  }

  void eval(bool update_registers, bool verbose, bool done_reset) {
    UInt<1> T_7 = x > y;
    UInt<17> T_8 = x - y;
    UInt<16> T_9 = T_8.tail<1>();
    UInt<16> _GEN_0 = T_7 ? T_9 : x;
    UInt<1> T_12 = ~T_7;
    UInt<17> T_13 = y - x;
    UInt<16> T_14 = T_13.tail<1>();
    UInt<16> _GEN_1 = T_12 ? T_14 : y;
    io_z = x;
    io_v = y == UInt<16>(0x0);
    UInt<16> x$next = io_e ? io_a : _GEN_0;
    UInt<16> y$next = io_e ? io_b : _GEN_1;
    if (update_registers) x = x$next;
    if (update_registers) y = y$next;
  }
} GCD;

#endif  // GCD_H_
