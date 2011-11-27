package Time;


public class Sleep_until {
	
	public synchronized boolean step(long d) {
		long sommeil = d - java.lang.System.currentTimeMillis();
		try {
			if (sommeil<=0) return false;
			this.wait(sommeil);
		} catch (InterruptedException ie) { return false; }
		return true;
	}
}