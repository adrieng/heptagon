package jeptagon;

import java.util.concurrent.Future;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.Callable;
import java.util.concurrent.FutureTask;

public class AsyncNode<T> implements Runnable {
	
	protected final ArrayBlockingQueue<FutureTask<T>>[] queue;
	protected int currentQueue;
	protected final int queueNb;
	
	@SuppressWarnings("unchecked")
	public AsyncNode(int queueNb, int queueSize) {
		this.queue = new ArrayBlockingQueue[queueNb];
		if (queueNb<1) { java.lang.System.err.println("asyncnode given with 0 thread to execute"); }
		for (int i = 0; i<queueNb; i++) {
			this.queue[i] = new ArrayBlockingQueue<FutureTask<T>>(queueSize,false);
		}
		this.currentQueue = 0;
		this.queueNb = queueNb;
		for (int i = 0; i<queueNb; i++) {
			
		}
		(new Thread(this)).start();
	}
	
	public void run() {
		try {
			while (true) queue[currentQueue].take().run();
		}
		catch (InterruptedException e) {
			return;
		}		
	}
	
	public Future<T> submit(Callable<T> c) {
		FutureTask<T> t = new FutureTask<T>(c);
		try { queue[currentQueue].put(t); } catch (InterruptedException e) { e.printStackTrace(); }
		return (Future<T>) t;
	}
	
	public void reset() {
		currentQueue = (currentQueue + 1) % queueNb;
	}
	
	
	protected static class ShutdownTask<T> implements Callable<T> {
		public T call() throws InterruptedException {
			throw new InterruptedException();
		}
	}
			
	public void shutdown() {
		submit(new ShutdownTask<T>());
		return;
	}
	
	protected void finalize() throws Throwable {
		 try { shutdown(); }
		 finally { super.finalize(); }
	}
}