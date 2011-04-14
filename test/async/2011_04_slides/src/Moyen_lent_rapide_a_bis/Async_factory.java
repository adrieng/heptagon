package Moyen_lent_rapide_a_bis;
import java.util.concurrent.Future;
import java.util.concurrent.ExecutionException;

public class Async_factory<T> {
	protected int nb_instances = 0;
    protected T lent_rapide_inst;
    protected Future<Integer> result;
    protected final int N;
    
    protected static class Async_lent_rapide implements java.util.concurrent.Callable{
        protected Lent_rapide lent_rapide_inst;
        public boolean lent;
        protected Future<Integer> result;
        
        public Async_lent_rapide (Lent_rapide lent_rapide_inst, boolean lent, Future<Integer> result) {
            this.lent_rapide_inst = lent_rapide_inst;
            this.lent = lent;
            this.result = result;
        }
        public Integer call () throws InterruptedException, ExecutionException {
            if ((null != result)) {
                result.get(); }
            return this.lent_rapide_inst.step(lent);
        }
    }
    public Async_factory_lent_rapide (int N) {
        this.result = null;
        this.lent_rapide_inst = new Lent_rapide(N);
        this.N = N;
    }
    public Future<Integer> step (boolean lent) throws InterruptedException, ExecutionException {
        this.result =
            jeptagon.Pervasives.executor_cached.submit(new Async_factory_lent_rapide.Async_lent_rapide
                                                      (lent_rapide_inst, lent,result));
        return result;
    }
    public void reset () {
        this.result = null;
        this.lent_rapide_inst = new Lent_rapide(N);
    }
}
