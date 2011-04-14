package Reset_a_bis;
import java.util.concurrent.Future;
import java.util.concurrent.ExecutionException;

public class Async_factory_lent {
    protected Lent lent_inst;
    protected Future<Integer> result;
    
    protected static class Async_lent implements java.util.concurrent.Callable{
        protected Lent lent_inst;
        protected Future<Integer> result;
        
        public Async_lent (Lent lent_inst, Future<Integer> result) {
            this.lent_inst = lent_inst;
            this.result = result;
        }
        public Integer call () throws InterruptedException, ExecutionException {
            if ((null != result)) {
                result.get(); }
            return this.lent_inst.step();
        }
    }
    public Async_factory_lent () {
        this.result = null;
        this.lent_inst = new Lent();
    }
    public Future<Integer> step () throws InterruptedException, ExecutionException {
        this.result = jeptagon.Pervasives.executor_cached.submit(new Async_factory_lent.Async_lent(lent_inst,result));
        return result;
    }
    public void reset () {
        this.result = null;
        this.lent_inst = new Lent();
    }
}
