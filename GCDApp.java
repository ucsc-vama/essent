class GCDApp {
    public static void main(String[] args) {
        System.out.println("Hello");
        GCD gcd = new GCD();
        gcd.io_a = 6;
        gcd.io_b = 3;
        gcd.io_e = true;
        gcd.eval(true);
        gcd.io_e = false;
        for (int i = 0; i < 5; i++) {
            System.out.println("i is " + i);
            System.out.println("x is " + gcd.x + " y is " + gcd.y);
            System.out.println("io_v is " + gcd.io_v);
            gcd.eval(true);
        }
    }
}