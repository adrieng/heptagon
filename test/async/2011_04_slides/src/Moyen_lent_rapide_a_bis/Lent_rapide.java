package Moyen_lent_rapide_a_bis;
import java.util.concurrent.Future;
import java.util.concurrent.ExecutionException;

public class Lent_rapide {
    protected int v_2;
    protected final int N;
    
    public Lent_rapide (int N) {
        this.N = N;
        {
            this.v_2 = 1;
        }
    }
    public int step (boolean lent) throws InterruptedException, ExecutionException {
        int r = 0;
        int v = 0;
        r = this.v_2;
        if (lent) {
            v = ((jeptagon.Pervasives.do_stuff((N * 9)) + r) + 1);
        } else {
            v = ((jeptagon.Pervasives.do_stuff(1) + r) + 1);
        }
        this.v_2 = v;
        return r;
    }
    public void reset () {
        this.v_2 = 1;
    }
}
