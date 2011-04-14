package Kill_fun;
import java.util.concurrent.Future;
import java.util.concurrent.ExecutionException;

public class Async_factory_lent {
    protected Lent lent_inst;
    protected Future<Integer> result;
    protected final int N;
    
    protected static class Async_lent implements java.util.concurrent.Callable{
        protected Lent lent_inst;
        
        public Async_lent (Lent lent_inst) {
            this.lent_inst = lent_inst;
        }
        public Integer call () throws InterruptedException, ExecutionException {
            return this.lent_inst.step();
        }
    }
    
    public Async_factory_lent (int N) {
        this.result = null;
        this.lent_inst = new Lent(N);
        this.N = N;
    }
    
    public Future<Integer> step () throws InterruptedException, ExecutionException {
        this.result = jeptagon.Pervasives.executor_cached.submit(new Async_factory_lent.Async_lent(lent_inst));
        return result;
    }
    
    public void reset () {
        this.result = null;
        this.lent_inst = new Lent(N);
    }
}
