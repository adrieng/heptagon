package Reset_6_a_bis;
import java.util.concurrent.Future;
import java.util.concurrent.ExecutionException;

public class Main {
    protected Async_factory_lent lent_inst;
    protected Future<Integer> v_3;
    protected Future<Integer> v_4;
    protected Future<Integer> v_5;
    protected Future<Integer> v_6;
    protected Future<Integer> v_7;
    protected Future<Integer> v_8;
    protected Future<Integer> v_9;
    protected Future<Integer> v_10;
    protected Future<Integer> v_11;
    protected Future<Integer> v_12;
    protected Future<Integer> v_13;
    protected Future<Integer> v_14;
    protected Future<Integer> v_15;
    protected Future<Integer> v_16;
    protected Future<Integer> v_17;
    protected Future<Integer> v_18;
    protected Future<Integer> v_19;
    protected Future<Integer> v_20;
    protected Future<Integer> v_21;
    protected Future<Integer> v_22;
    protected boolean v_24;
    
    public Main () {
        this.lent_inst = new Async_factory_lent();
        {
            this.v_22 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_24 = true;
            this.v_21 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_20 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_19 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_18 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_17 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_16 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_15 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_14 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_13 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_12 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_11 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_10 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_9 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_8 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_7 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_6 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_5 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_4 = new jeptagon.Pervasives.StaticFuture(0);
            this.v_3 = new jeptagon.Pervasives.StaticFuture(0);
        }
    }
    public jeptagon.Pervasives.Tuple2 step () throws InterruptedException, ExecutionException {
        int r = 0;
        boolean half = true;
        boolean v_23 = true;
        Future<Integer> c = null;
        boolean r_2 = true;
        r = this.v_22.get();
        half = this.v_24;
        this.v_22 = this.v_21;
        v_23 = !half;
        r_2 = half;
        this.v_24 = v_23;
        this.v_21 = this.v_20;
        if (r_2) {
            lent_inst.reset(); }
        c = lent_inst.step();
        this.v_20 = this.v_19;
        this.v_19 = this.v_18;
        this.v_18 = this.v_17;
        this.v_17 = this.v_16;
        this.v_16 = this.v_15;
        this.v_15 = this.v_14;
        this.v_14 = this.v_13;
        this.v_13 = this.v_12;
        this.v_12 = this.v_11;
        this.v_11 = this.v_10;
        this.v_10 = this.v_9;
        this.v_9 = this.v_8;
        this.v_8 = this.v_7;
        this.v_7 = this.v_6;
        this.v_6 = this.v_5;
        this.v_5 = this.v_4;
        this.v_4 = this.v_3;
        this.v_3 = c;
        return new jeptagon.Pervasives.Tuple2(r, half);
    }
    public void reset () {
        this.v_22 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_24 = true;
        this.v_21 = new jeptagon.Pervasives.StaticFuture(0);
        lent_inst.reset();
        this.v_20 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_19 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_18 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_17 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_16 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_15 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_14 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_13 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_12 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_11 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_10 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_9 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_8 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_7 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_6 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_5 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_4 = new jeptagon.Pervasives.StaticFuture(0);
        this.v_3 = new jeptagon.Pervasives.StaticFuture(0);
    }
}
