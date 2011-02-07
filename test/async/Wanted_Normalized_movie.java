package pipline_b;

import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Future;

public class Wanted_Normalized_movie {
    protected final int N;;
    protected Async_mean_factory mean_factory;;
    protected Substr[] substr_inst;;
    protected Future<Integer> v;;
    protected boolean v_2;;
    protected int[] v_4;;
    protected boolean v_5;;
    
    
    
    public Wanted_Normalized_movie (int N) {
        this.mean_factory = new Async_mean_factory(N);
        this.substr_inst = new Substr[N];
        for (int i_3 = 0; i_3<N; i_3++) { this.substr_inst[i_3] = new Substr(); };
        this.N = N;
    }
    public int[] step (int[] i) throws InterruptedException, ExecutionException {
        int[] im = new int[N];
        int[] v_6 = new int[N];
        int v_3 = 0;
        int trash = 0;
        Future<Integer> m = null;
        if (this.v_2) { v_3 = 0; }
        else { v_3 = this.v.get(); };
        if (this.v_5) { v_6 = i; }
        else { v_6 = this.v_4; };
        this.v_5 = false;
        trash = v_3;
        for (int i_2 = 0; i_2<N; i_2++) {
          jeptagon.Pervasives.Tuple2<Integer, Integer> out = substr_inst[i_2].step(v_6[i_2], trash);
          im[i_2] = out.c0;
          trash = out.c1;
          };
        this.v_2 = false;
        m = mean_factory.step(i);
        this.v_4 = i;
        this.v = m;
        return im;
    }
    
    
    //params, class, step_result_type, step_args
    public class Async_mean_factory {
    	Mean mean_inst;
    	int N;
        Future<Integer> result;
    	
    	public Async_mean_factory(int N) {
    		this.N = N;
    		this.mean_inst = new Mean(N);
    	}
    	
    	public void reset () {
    		this.mean_inst = new Mean(N);
    		this.result = null;
    	}
    	
    	public Future<Integer> step(int[] i) {
    		if (null != result) // Wait for the last result to be completed, null if nothing to wait for.
				try {
					result.get();
				} catch (InterruptedException e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				} catch (ExecutionException e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				}
    		result = jeptagon.Pervasives.executor_cached.submit(new Async_mean_step(mean_inst, i));
    		return result;
    	}
    	
        class Async_mean_step implements Callable<Integer>{
        	int[] i;
        	Mean mean_inst;
        	public Async_mean_step(Mean mean_inst, int[] i) {
        		this.i = i;
        		this.mean_inst = mean_inst;
        	}
        	public Integer call () {
        		return mean_inst.step(i);
        	}
        }
        
        
    	
    }
    

    
    public static void main() {
    	
    }
    
    public void reset () {
        this.v_5 = true;
        this.v_2 = true;
    }
}