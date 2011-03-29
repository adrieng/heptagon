package Rapide_lent;

public class Main {
    protected Rapide rapide_inst;
    
    public Main () {
        this.rapide_inst = new Rapide(100);
        
    }
    public int step () {
        int r = 0;
        r = rapide_inst.step();
        return r;
    }
    public void reset () {
        rapide_inst.reset();
    }
}
