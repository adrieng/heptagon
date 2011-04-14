package Kill_node;
import java.util.concurrent.Future;
import java.util.concurrent.Callable;
import jeptagon.AsyncNode;

public class Async_factory_lent {
    protected Lent lent_inst;
    protected AsyncNode<Integer> executor;
    protected final int N;
    
    protected static class Async_lent implements Callable<Integer>{
        protected Lent lent_inst;
        
        public Async_lent (Lent lent_inst) {
            this.lent_inst = lent_inst;
        }
        public Integer call () {
            return this.lent_inst.step();
        }
    }
    public Async_factory_lent (int N) {
    	this.executor = new AsyncNode<Integer>();
        this.lent_inst = new Lent(N);
        this.N = N;
    }
    public Future<Integer> step () {
        return executor.submit(new Async_factory_lent.Async_lent(lent_inst));
    }
    public void reset () {
    	executor.shutdown();
        this.executor = new AsyncNode<Integer>();
        this.lent_inst = new Lent(N);
    }
}

