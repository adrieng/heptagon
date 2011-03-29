package Rapide_lent;

public class Main_sim {
    public static final int default_step_nb = 30000;
    
    
    public static void main (String[] args) {
        int step = 0;
        Main main = new Main();
        if ((args.length > 1)) {
            step = Integer.parseInt(args[1]);
        } else {
            step = default_step_nb;
        }
        for (int i = 0; i<step; i++) { int r = main.step(); }
    }
}
