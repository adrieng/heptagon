package Kill_fun;
import java.util.concurrent.Future;
import java.util.concurrent.ExecutionException;

public class Main_sim {
    public static final int default_step_nb = 15;
    
    
    public static void main (String[] args) throws InterruptedException, ExecutionException {
        int step = 0;
        Main main = new Main();
        if ((args.length > 1)) {
            step = Integer.parseInt(args[1]);
        } else {
            step = default_step_nb;
        }
        for (int i = 0; i<step; i++) { main.step(); java.lang.System.out.printf("%d => _\n", i); }
    }
}
