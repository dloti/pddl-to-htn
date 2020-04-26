package JSHOP2;

import java.util.Comparator;

/** This class handles <code>:sort-by</code> logical preconditions that use
 *  numerical <b>less than</b> as the sorting function.
 *
 *  @author Okhtay Ilghami
 *  @author <a href="http://www.cs.umd.edu/~okhtay">http://www.cs.umd.edu/~okhtay</a>
 *  @version 1.0.3
*/
public class CompLess implements Comparator
{
  /** The index of the variable according to the value of which the satisfiers
   *  should be sorted.
  */
  private int varIdx;

  /** To initialize this object.
   *
   *  @param varIdxIn
   *          The index of the variable according to the value of which the
   *          satisfiers should be sorted.
  */
  public CompLess(int varIdxIn)
  {
    varIdx = varIdxIn;
  }

  /** The function that implements the actual comparison.
   *
   *  @param o1
   *          the first binding.
   *  @param o2
   *          the second binding.
   *  @return
   *          -1 if the first binding should come first, 1 if the second
   *          binding should come first, 0 if the variable according to value
   *          of which the satisfiers are being sorted has the same value in
   *          these two bindings.
  */
  public int compare(Object o1, Object o2)
  {
    Term[] t1 = (Term[])o1;
    Term[] t2 = (Term[])o2;

    //-- Get the numerical values of the two terms.
    double n1 = ((TermNumber)t1[varIdx]).getNumber();
    double n2 = ((TermNumber)t2[varIdx]).getNumber();

    //-- Compare them and return the result.

    if (n1 < n2)
      return -1;

    if (n1 > n2)
      return 1;

    return 0;
  }
}
