class GCD {
    public int x = 0;
    public int y = 0;
    public int clk = 0;
    public boolean reset = false;
    public int io_a = 0;
    public int io_b = 0;
    public boolean io_e = false;
    public int io_z = 0;
    public boolean io_v = false;
    public void eval(boolean update_registers) {
        boolean T_7 = x > y;
        int T_8 = x - y;
        int T_9 = T_8 & 0xffff;
        int _GEN_0 = T_7 ? T_9 : x;
        boolean T_12 = !T_7;
        int T_13 = y - x;
        int T_14 = T_13 & 0xffff;
        int _GEN_1 = T_12 ? T_14 : y;
        io_z = x;
        io_v = y == 0;
        int x$next = io_e ? io_a : _GEN_0;
        int y$next = io_e ? io_b : _GEN_1;
        if (update_registers) x = x$next;
        if (update_registers) y = y$next;
    }
}