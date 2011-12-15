package Time;

public class FUNS {
	public static long add_time(long t, int i) {
		return t+i;
	}
	public static long get_time() {
		return java.lang.System.currentTimeMillis();
	}
	public static boolean sleep_until(Long d) {
		synchronized (d) {
			long sommeil = d - java.lang.System.currentTimeMillis();
			try {
				if (sommeil<=0) return false;
				d.wait(sommeil);
			} catch (InterruptedException ie) { return false; }
			return true;
		}
	}
}
