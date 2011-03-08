package jeptagon;

import java.util.concurrent.Executors;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

public class Pervasives {

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
	
    public static class Tuple1<T> {
    	public final T c0;
    	public Tuple1(T v) {
    		c0 = v;
    	}
    }
    
    public static class Tuple22 {
    	public final Object c0;
    	public final Object c1;
    	public Tuple22(Object v0, Object v1) {
    		c0 = v0;
    		c1 = v1;
    	}
    }
    
    public static class Tuple2 <T0,T1> {
    	public final T0 c0;
    	public final T1 c1;
    	public Tuple2(T0 v0, T1 v1) {
    		c0 = v0;
    		c1 = v1;
    	}
    }
    
    public static class Tuple3 <T0,T1,T2> {
    	public final T0 c0;
    	public final T1 c1;
    	public final T2 c2;
    	public Tuple3(T0 v0, T1 v1, T2 v2) {
    		c0 = v0;
    		c1 = v1;
    		c2 = v2;
        }
    }
    
    public static class Tuple4 <T0,T1,T2,T3> {
    	public final T0 c0;
    	public final T1 c1;
    	public final T2 c2;
    	public final T3 c3;
    	public Tuple4(T0 v0, T1 v1, T2 v2, T3 v3) {
    		c0 = v0;
    		c1 = v1;
    		c2 = v2;
    		c3 = v3;
    	}
    }
    
    public static class Tuple5 <T0,T1,T2,T3,T4> {
    	public final T0 c0;
    	public final T1 c1;
    	public final T2 c2;
    	public final T3 c3;
    	public final T4 c4;
    	public Tuple5(T0 v0, T1 v1, T2 v2, T3 v3, T4 v4) {
    		c0 = v0;
    		c1 = v1;
    		c2 = v2;
    		c3 = v3;
    		c4 = v4;
    	}
    }
    
    public static class Tuple6 <T0,T1,T2,T3,T4,T5> {
    	public final T0 c0;
    	public final T1 c1;
    	public final T2 c2;
    	public final T3 c3;
    	public final T4 c4;
    	public final T5 c5;
    	public Tuple6(T0 v0, T1 v1, T2 v2, T3 v3, T4 v4, T5 v5) {
    		c0 = v0;
    		c1 = v1;
    		c2 = v2;
    		c3 = v3;
    		c4 = v4;
    		c5 = v5;
    	}
    }
    
    public static class Tuple7 <T0,T1,T2,T3,T4,T5,T6> {
    	public final T0 c0;
    	public final T1 c1;
    	public final T2 c2;
    	public final T3 c3;
    	public final T4 c4;
    	public final T5 c5;
    	public final T6 c6;
    	public Tuple7(T0 v0, T1 v1, T2 v2, T3 v3, T4 v4, T5 v5, T6 v6) {
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
