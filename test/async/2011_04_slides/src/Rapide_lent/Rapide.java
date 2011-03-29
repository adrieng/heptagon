package Rapide_lent;
import jeptagon.Pervasives;

public class Rapide {
    protected int N;
    protected Lent lent_inst;
    protected int cpt;
    protected int y;
    protected boolean big_step;
    
    public Rapide (int N) {
        this.N = N;
        this.lent_inst = new Lent(N);
        {
            this.cpt = N;
            this.y = 0;
            this.big_step = false;
        }
    }
    public int step () {
        int z, v_1, v_2;
        if (this.big_step) {
            v_1 = lent_inst.step();
            v_2 = N;
        } else {
            v_1 = this.y;
            v_2 = this.cpt;
        }
        z = Pervasives.do_stuff(1) - this.y;
        this.y = v_1;
        this.cpt = (v_2 - 1);
        this.big_step = this.cpt == 0;
        return z;
    }
    public void reset () {
        this.cpt = N;
        this.y = 0;
        this.big_step = false;
    }
}
