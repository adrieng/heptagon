package Reset_a_bis;
import java.util.concurrent.Future;
import java.util.concurrent.ExecutionException;

public class Main {
    protected Async_factory_lent lent_inst;
    protected Future<Integer> v_3;
    protected Future<Integer> v_4;
    protected Future<Integer> v_5;
    protected Future<Integer> v_6;
    protected boolean v_8;
    
    public Main () {
        this.lent_inst = new Async_factory_lent();
        {
            this.v_6 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_8 = true;
            this.v_5 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_4 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_3 = new jeptagon.Pervasives.StaticFuture(0);
        }
    }
    public jeptagon.Pervasives.Tuple2 step () throws InterruptedException, ExecutionException {
        int r = 0;
        boolean half = true;
        boolean v_7 = true;
        Future<Integer> c = null;
        boolean r_2 = true;
        r = this.v_6.get();
        half = this.v_8;
        this.v_6 = this.v_5;
        v_7 = !half;
        r_2 = half;
        this.v_8 = v_7;
        this.v_5 = this.v_4;
        if (r_2) {
            lent_inst.reset(); }
        c = lent_inst.step();
        this.v_4 = this.v_3;
        this.v_3 = c;
        return new jeptagon.Pervasives.Tuple2(r, half);
    }
    public void reset () {
        this.v_6 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_8 = true;
        this.v_5 = new jeptagon.Pervasives.StaticFuture(0);
        lent_inst.reset();
        this.v_4 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_3 = new jeptagon.Pervasives.StaticFuture(0);
    }
}
