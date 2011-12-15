package Time;

public class Start_time {
	static Long start_time;
	public Start_time() {
		if (start_time == null) {
			start_time = java.lang.System.currentTimeMillis();
		}
	}
	public long step() {
		return (long) start_time;
	}
}
