package Kill_node_bis;
import java.util.concurrent.Future;
import java.util.concurrent.ExecutionException;

public class Main {
    protected Async_factory_lent lent_inst;
    
    public Main () {
        this.lent_inst = new Async_factory_lent(5);
        
    }
    public void step () throws InterruptedException, ExecutionException {
        Future<Integer> y = null;
        y = lent_inst.step();
        return ;
    }
    public void reset () {
        lent_inst.reset();
    }
}
