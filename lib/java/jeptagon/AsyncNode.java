package jeptagon;

import java.util.concurrent.Future;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.Callable;
import java.util.concurrent.FutureTask;

public class AsyncNode<T> implements Runnable {
	
	private final ArrayBlockingQueue<FutureTask<T>> queue;
	
	public AsyncNode(int queueSize){
		queue = new ArrayBlockingQueue<FutureTask<T>>(queueSize,false);
		(new Thread(this)).start();
	}
	
	public void run() {
		try {
			while (true) queue.take().run();
		}
		catch (InterruptedException e) {
			return;
		}		
	}
	
	public Future<T> submit(Callable<T> c) {
		FutureTask<T> t = new FutureTask<T>(c);
		try { queue.put(t); } catch (InterruptedException e) { e.printStackTrace(); }
		return (Future<T>) t;
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