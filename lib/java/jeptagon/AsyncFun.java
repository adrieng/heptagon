package jeptagon;

import java.util.concurrent.Future;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.Callable;
import java.util.concurrent.FutureTask;

public class AsyncFun<T> {

  protected final ArrayBlockingQueue<FutureTask<T>>[] queue;
  protected int currentQueue;
  protected final int queueNb;
  protected final Thread[] t;

  protected class AsyncFunThread extends Thread {
    protected final int queueId;
    public AsyncFunThread(int queueId) {
      this.queueId = queueId;
    }
    public void run() {
      try {
        while (true) queue[queueId].take().run();
      }
      catch (InterruptedException e) {
        return;
      }
    }
  }

  @SuppressWarnings("unchecked")
  public AsyncFun(int queueNb, int queueSize, int priority) {
    if (queueNb<1) { java.lang.System.err.println("asyncnode given with 0 thread to execute"); }
    this.queue = new ArrayBlockingQueue[queueNb];
    this.t = new Thread[queueNb];
    this.currentQueue = 0;
    this.queueNb = queueNb;
    for (int i = 0; i<queueNb; i++) {
      this.queue[i] = new ArrayBlockingQueue<FutureTask<T>>(queueSize,false);
      t[i] = new AsyncFunThread(i);
      t[i].setPriority(priority);
      java.lang.System.out.printf("Priority asked %d, set to %d\n",priority,t[i].getPriority());
      t[i].start();
    }
  }
  public AsyncFun(int queueNb, int queueSize) {
    this(queueNb, queueSize, Thread.NORM_PRIORITY);
  }

  public AsyncFun() {
    this(1,1);
  }


  public Future<T> submit(Callable<T> c) {
    FutureTask<T> t = new FutureTask<T>(c);
    try {
      queue[currentQueue].put(t);
    }
    catch (InterruptedException e) { e.printStackTrace(); }
    // There is no dependency between calls,
    // the heuristic is to use the available threads in a round-robin manner.
    currentQueue = (currentQueue + 1) % queueNb;
    return (Future<T>) t;
  }


  public void reset() {
  }


  public void shutdown() {
    for (int i = 0; i<queueNb; i++) {
      t[i].interrupt();
    }
    return;
  }

  protected void finalize() throws Throwable {
    try { shutdown(); }
    finally { super.finalize(); }
  }
}
