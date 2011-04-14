
package Rapide_lent;

public class Rapide {
    protected Lent lent_inst;
    protected boolean big_step;
    protected int cpt;
    protected int v;
    protected final int N;
    
    public Rapide (int N) {
        this.N = N;
        this.lent_inst = new Lent(N);
        {
            this.cpt = N;
            this.v = 0;
            this.big_step = true;
        }
    }
    public int step () {
        int z, v_1, v_2;
        if (this.big_step) {
            v_1 = lent_inst.step();
            v_2 = N;
           
        } else {
            v_2 = this.cpt;
            v_1 = jeptagon.Pervasives.do_stuff(1);
        }
        this.cpt = (v_2 - 1);
        z = this.v;
        this.v = v_1;
        this.big_step = this.cpt == 0;
        return z;
    }
    public void reset () {
        lent_inst.reset();
        this.cpt = N;
        this.v = 0;
        this.big_step = true;
    }
}
