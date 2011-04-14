package Reset_6_a_bis;
import java.util.concurrent.Future;
import java.util.concurrent.ExecutionException;

public class Main_sim {
    public static final int default_step_nb = 100;
    
    
    public static void main (String[] args) throws InterruptedException, ExecutionException {
        int step = 0;
        Main main = new Main();
        if ((args.length > 1)) {
            step = Integer.parseInt(args[1]);
        } else {
            step = default_step_nb;
        }
        long t = java.lang.System.currentTimeMillis();
        for (int i = 0; i<step; i++) { java.lang.System.out.printf("%d => %s\n", i, main.step().toString()); }
        java.lang.System.out.printf("time : %d\n", (java.lang.System.currentTimeMillis() - t));
    }
}
