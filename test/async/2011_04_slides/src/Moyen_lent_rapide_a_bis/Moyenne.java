package Moyen_lent_rapide_a_bis;
import java.util.concurrent.Future;
import java.util.concurrent.ExecutionException;

public class Moyenne {
    protected Async_factory_lent_rapide lent_rapide_inst;
    protected Future<Integer> v_4;
    protected Future<Integer> v_5;
    protected Future<Integer> v_6;
    protected int v_8;
    protected boolean v_11;
    protected final int N;
    
    public Moyenne (int N) {
        this.N = N;
        this.lent_rapide_inst = new Async_factory_lent_rapide(N);
        {
            this.v_6 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_5 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_4 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_11 = true;
            this.v_8 = N;
        }
    }
    public jeptagon.Pervasives.Tuple2 step () throws InterruptedException, ExecutionException {
        int r = 0;
        boolean big_step = true;
        boolean v_10 = true;
        int v_9 = 0;
        int v_7 = 0;
        Future<Integer> v_3 = null;
        int cpt = 0;
        boolean r_2 = true;
        big_step = this.v_11;
        v_7 = this.v_6.get();
        v_3 = lent_rapide_inst.step(big_step);
        r = (v_7 + jeptagon.Pervasives.do_stuff(10));
        r_2 = big_step;
        this.v_6 = this.v_5;
        if (r_2) {
            v_9 = N;
        } else {
            v_9 = this.v_8;
        }
        cpt = (v_9 - 1);
        this.v_5 = this.v_4;
        v_10 = (cpt == 0);
        this.v_4 = v_3;
        this.v_11 = v_10;
        this.v_8 = cpt;
        return new jeptagon.Pervasives.Tuple2(r, big_step);
    }
    public void reset () {
        lent_rapide_inst.reset();
        this.v_6 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_5 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_4 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_11 = true;
        this.v_8 = N;
    }
}
