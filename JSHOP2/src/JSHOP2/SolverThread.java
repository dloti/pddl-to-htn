package JSHOP2;

import java.util.GregorianCalendar;
import java.util.Iterator;
import java.util.LinkedList;

/** The thread that invokes JSHOP2 to solve a planning problem. The only reason
 *  to have another thread to solve problems rather than using the main thread
 *  to do so is that, in some platforms, the command line parameters that are
 *  supposed to change the stack size work only for the threads other than the
 *  main thread.
 *
 *  @author Okhtay Ilghami
 *  @author <a href="http://www.cs.umd.edu/~okhtay">http://www.cs.umd.edu/~okhtay</a>
 *  @version 1.0.3
*/
public class SolverThread extends Thread
{
  /** The maximum number of plans allowed. */
  private int planNo;

  /** The task list to be achieved.
  */
  private TaskList tl;

  /** To initialize this thread.
   *
   *  @param tlIn
   *          the task list to be achieved by this thread.
   *  @param planNoIn
   *          the maximum number of plans allowed.
  */
  public SolverThread(TaskList tlIn, int planNoIn)
  {
    tl = tlIn;
    planNo = planNoIn;
  }

  /** The function that is called when this thread is invoked.
  */
  public void run()
  {
    //-- Get the current time.
    long t1 = new GregorianCalendar().getTimeInMillis();

    //-- Solve the planning problem.
    LinkedList p = JSHOP2.findPlans(tl, planNo);

    //-- Get the current time again, to calculate the time used.
    long t2 = new GregorianCalendar().getTimeInMillis();

    System.out.println();
    System.out.println(p.size() + " plan(s) were found:");
    System.out.println();

    //-- Print the plans found.
    Iterator e = p.iterator();
    int i = 0;
    while (e.hasNext())
    {
      System.out.println("Plan #" + ++i + ":");
      System.out.println((Plan)e.next());
    }

    System.out.println("Time Used = " + (t2 - t1) / 1000.0);
    System.out.println();
  }
}

