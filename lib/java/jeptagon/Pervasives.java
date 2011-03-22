package jeptagon;

import java.util.concurrent.Executors;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

public class Pervasives {

	public static int between(int i, int m) {
		if (i<0) return 0;
		else if (i>=m) return m-1;
		else return i;
	}

    public static final ExecutorService executor_cached = Executors.newCachedThreadPool();

    public static class StaticFuture<V> implements Future<V> {
    	V v;
    	
    	public StaticFuture(V v) { this.v = v;	}
    	
    	public boolean cancel(boolean mayInterruptIfRunning) { return false; }
    	
    	public boolean isCancelled() { return false; }
    	
    	public boolean isDone() { return true; }
    	
    	public V get() { return v; }
    	
    	public V get(long timeout, TimeUnit unit) { return v; }	
    }
	
    public static class Tuple1 {
    	public final Object c0;
    	public Tuple1(Object v) {
    		c0 = v;
    	}
    }
    
    public static class Tuple2 {
    	public final Object c0;
    	public final Object c1;
    	public Tuple2(Object v0, Object v1) {
    		c0 = v0;
    		c1 = v1;
    	}
    }
    
    public static class Tuple3 {
    	public final Object c0;
    	public final Object c1;
    	public final Object c2;
    	public Tuple3(Object v0, Object v1, Object v2) {
    		c0 = v0;
    		c1 = v1;
    		c2 = v2;
        }
    }
    
    public static class Tuple4 {
    	public final Object c0;
    	public final Object c1;
    	public final Object c2;
    	public final Object c3;
    	public Tuple4(Object v0, Object v1, Object v2, Object v3) {
    		c0 = v0;
    		c1 = v1;
    		c2 = v2;
    		c3 = v3;
    	}
    }
    
    public static class Tuple5 {
    	public final Object c0;
    	public final Object c1;
    	public final Object c2;
    	public final Object c3;
    	public final Object c4;
    	public Tuple5(Object v0, Object v1, Object v2, Object v3, Object v4) {
    		c0 = v0;
    		c1 = v1;
    		c2 = v2;
    		c3 = v3;
    		c4 = v4;
    	}
    }
    
    public static class Tuple6 {
    	public final Object c0;
    	public final Object c1;
    	public final Object c2;
    	public final Object c3;
    	public final Object c4;
    	public final Object c5;
    	public Tuple6(Object v0, Object v1, Object v2, Object v3, Object v4, Object v5) {
    		c0 = v0;
    		c1 = v1;
    		c2 = v2;
    		c3 = v3;
    		c4 = v4;
    		c5 = v5;
    	}
    }
    
    public static class Tuple7 {
    	public final Object c0;
    	public final Object c1;
    	public final Object c2;
    	public final Object c3;
    	public final Object c4;
    	public final Object c5;
    	public final Object c6;
    	public Tuple7(Object v0, Object v1, Object v2, Object v3, Object v4, Object v5, Object v6) {
    		c0 = v0;
    		c1 = v1;
    		c2 = v2;
    		c3 = v3;
    		c4 = v4;
    		c5 = v5;
    		c6 = v6;
    	}
    }

    public static int do_stuff(int coeff) {
        int x = 13;
        for (int i = 0; i < coeff; i++) {
            for (int j = 0; j < 1000000; j++) {
                x = (x + j) % (x + j/x) + 13;
            }
        }
        return x;
    }


}
