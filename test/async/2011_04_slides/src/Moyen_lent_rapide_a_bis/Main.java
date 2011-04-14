package Moyen_lent_rapide_a_bis;
import java.util.concurrent.Future;
import java.util.concurrent.ExecutionException;

public class Main {
    protected Moyenne moyenne_inst;
    
    public Main () {
        this.moyenne_inst = new Moyenne(3);
        
    }
    public jeptagon.Pervasives.Tuple2 step () throws InterruptedException, ExecutionException {
        int r = 0;
        boolean big_step = true;
        jeptagon.Pervasives.Tuple2 out = moyenne_inst.step();
        r = (int)((Integer)(out.c0));
        big_step = (boolean)((Boolean)(out.c1));
        return new jeptagon.Pervasives.Tuple2(r, big_step);
    }
    public void reset () {
        moyenne_inst.reset();
    }
}
