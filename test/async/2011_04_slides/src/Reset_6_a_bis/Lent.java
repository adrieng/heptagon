package Reset_6_a_bis;
import java.util.concurrent.Future;
import java.util.concurrent.ExecutionException;

public class Lent {
    protected int v_2;
    
    public Lent () {
        {
            this.v_2 = 1;
        }
    }
    public int step () throws InterruptedException, ExecutionException {
        int r = 0;
        int v = 0;
        r = this.v_2;
        v = ((jeptagon.Pervasives.do_stuff(10) + r) + 1);
        this.v_2 = v;
        return r;
    }
    public void reset () {
        this.v_2 = 1;
    }
}
