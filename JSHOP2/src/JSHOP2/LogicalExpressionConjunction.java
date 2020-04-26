package JSHOP2;

import java.util.Vector;

/** Each conjunction at compile time is represented as an instance of this
 *  class.
 *
 *  @author Okhtay Ilghami
 *  @author <a href="http://www.cs.umd.edu/~okhtay">http://www.cs.umd.edu/~okhtay</a>
 *  @version 1.0.3
*/
public class LogicalExpressionConjunction extends LogicalExpression
{
  /** The number of objects instantiated from this class before this object was
   *  instantiated. Used to make the name of the precondition class that
   *  implements this conjunction unique.
  */
  private int cnt;

  /** An array of logical expressions the conjunction of which is represented
   *  by this object.
  */
  private LogicalExpression[] le;

  /** To initialize this conjunction.
   *
   *  @param leIn
   *          a <code>Vector</code> of logical expressions the conjunction of
   *          which is represented by this object. Note that we use a
   *          <code>Vector</code> rather than an array since at compile time
   *          we do not know how many conjuncts there are in this particular
   *          conjunction.
  */
  public LogicalExpressionConjunction(Vector leIn)
  {
    le = new LogicalExpression[leIn.size()];

    for (int i = 0; i < leIn.size(); i++)
      le[i] = (LogicalExpression)leIn.get(i);

    cnt = getClassCnt();
  }

  /** This function produces Java code that implements the classes any object
   *  of which can be used at run time to represent the conjuncts of this
   *  conjunction, and the conjunction itself.
  */
  public String getInitCode()
  {
    String s = "";

    //-- First produce any code needed by the conjuncts.
    for (int i = 0; i < le.length; i++)
      s += le[i].getInitCode();

    //-- The header of the class for this conjunction at run time. Note the use
    //-- of 'cnt' to make the name of this class unique.
    s += "class Precondition" + cnt + " extends Precondition" + endl;

    //-- Defining two arrays for storing the iterators and bindings for each
    //-- conjunct.
    s += "{" + endl + "\tPrecondition[] p;" + endl + "\tTerm[][] b;" + endl;

    //-- The constructor of the class.
    s += endl+ "\tpublic Precondition" + cnt + "(Term[] unifier)" + endl;

    //-- Allocate the array of iterators.
    s += "\t{" + endl + "\t\tp = new Precondition[" + le.length + "];" + endl;

    //-- For each conjunct,
    for (int i = 0; i < le.length; i++)
      //-- Set the corresponding element in the array to the code that produces
      //-- that conjunct.
      s += "\t\tp[" + i + "] = " + le[i].toCode() + ";" + endl;

    //-- Allocate the array of bindings.
    s += "\t\tb = new Term[" + le.length + "][];" + endl + endl;

    //-- A conjucntion can be potentially satisfied more than once, so the
    //-- default for the 'isFirstCall' flag is false.
    s += "\t\tsetFirst(false);" + endl + "\t}" + endl + endl;

    //-- Define the 'bind' function.
    s += "\tpublic void bind(Term[] binding)" + endl + "\t{" + endl;

    //-- Implement the 'bind' function by:
    for (int i = 0; i < le.length; i++)
      //-- Binding each conjunct in this conjunction.
      s += "\t\tp[" + i + "].bind(binding);" + endl;

    //-- Define the 'nextBindingHelper' function.
    s += "\t}" + endl + endl + "\tprotected Term[] nextBindingHelper()" + endl;
    s += "\t{" + endl;

    //-- Implement the 'nextBindingHelper' function.
    s += getInitCodeNext();

    //-- Define the 'resetHelper' function.
    s += "\t}" + endl + endl + "\tprotected void resetHelper()" + endl + "\t{";
    s += endl;

    //-- Implement the 'resetHelper' function.
    s += getInitCodeReset();

    //-- Close the function definition and the class definition and return the
    //-- resulting string.
    return s + "\t}" + endl + "}" + endl + endl;
  }

  /** This function produces Java code that implements the
   *  <code>nextBindingHelper</code> function for the precondtion object that
   *  represents this conjunction at run time.
   *
   *  @return
   *          the produced code as a <code>String</code>.
  */
  private String getInitCodeNext()
  {
    String s;
    int i;

    //-- To be used to add appropriate number of tabs to each line of code.
    String tabs;

    //-- First, if there is no more binding for the innermost conjunct, return
    //-- null.
    s = "\t\tif (b[0] == null)" + endl + "\t\t\treturn null;" + endl + endl;

    //-- Start with the outermost conjunct, and try to find a binding for that
    //-- conjunct. If there is no more binding for that conjunct, try to find
    //-- the next binding for the next outermost conjunct.
    for (i = le.length - 1, tabs = "\t\t"; i > 0; i--, tabs += "\t")
    {
      s += tabs + "b[" + i + "] = p[" + i + "].nextBinding();" + endl;
      s += tabs + "while (b[" + i + "] == null)" + endl + tabs + "{" + endl;
    }

    //-- Try the outer most conjunct.
    s += tabs + "b[0] = p[0].nextBinding();" + endl;

    //-- If there is no more binding for the outermost conjunct, return null.
    s += tabs + "if (b[0] == null)" + endl + tabs + "\treturn null;" + endl;

    //-- Try the second outer most conjunct.
    s += tabs + "p[1].reset();" + endl + tabs + "p[1].bind(b[0]);" + endl;
    s += tabs + "b[1] = p[1].nextBinding();" + endl;

    //-- Going from third outermost conjunct inward, try to apply newly-found
    //-- bindings for outermost conjuncts to each inner conjunct after reseting
    //-- it, and try to find bindings for inner conjuncts.
    tabs = tabs.substring(0, tabs.length() - 1);
    for (i = 2; i < le.length; i++, tabs = tabs.substring(0, tabs.length() - 1))
    {
      s += tabs + "}" + endl + tabs + "p[" + i + "].reset();" + endl;
      s += tabs + "p[" + i + "].bind(Term.merge(b, " + i + "));" + endl;
      s += tabs + "b[" + i + "] = p[" + i + "].nextBinding();" + endl;
    }

    //-- Return the result of the merging of the bindings found for each
    //-- conjunct.
    return s + "\t\t}" + endl + endl + "\t\treturn Term.merge(b, " + le.length
             + ");" + endl;
  }

  /** This function produces Java code that implements the
   *  <code>resetHelper</code> function for the precondtion object that
   *  represents this conjunction at run time.
   *
   *  @return
   *          the produced code as a <code>String</code>.
  */
  private String getInitCodeReset()
  {
    String s = "";
    int i, j;

    //-- First, reset all the conjuncts.
    for (i = 0; i < le.length; i++)
      s += "\t\tp[" + i + "].reset();" + endl;

    //-- Try to find a binding for the outermost conjunct.
    s += endl + "\t\tb[0] = p[0].nextBinding();" + endl;

    //-- If there are no more such bindings, return.
    s += "\t\tif (b[0] == null)" + endl + "\t\t\treturn;" + endl + endl;

    //-- Bind the second outermost conjunct with the binding found for the
    //-- first one.
    s += "\t\tp[1].bind(b[0]);" + endl;

    //-- Starting from the second outermost conjunct inward, for each conjunct,
    for (j = 1; j < le.length - 1; j++)
    {
      //-- To be used to add appropriate number of tabs to each line of code.
      String tabs;

      //-- Start with the currnet conjunct, and try to find a binding for that
      //-- conjunct. If there is no more binding for that conjunct, try to find
      //-- the next binding for the next outermost conjunct.
      for (i = j, tabs = "\t\t"; i > 0; i--, tabs = tabs + "\t")
      {
        s += tabs + "b[" + i + "] = p[" + i + "].nextBinding();" + endl;
        s += tabs + "while (b[" + i + "] == null)" + endl + tabs + "{" + endl;
      }

      //-- Try the outer most conjunct.
      s += tabs + "b[0] = p[0].nextBinding();" + endl;

      //-- If there is no more binding for the outermost conjunct, return.
      s += tabs + "if (b[0] == null)" + endl + tabs + "\treturn;" + endl;

      //-- Try the second outer most conjunct.
      s += tabs + "p[1].reset();" + endl + tabs + "p[1].bind(b[0]);" + endl;
      s += tabs + "b[1] = p[1].nextBinding();" + endl;

      //-- Going from third outermost conjunct inward all the way to the
      //-- current conjunct, try to apply newly-found bindings for outermost
      //-- conjuncts to each inner conjunct after reseting it, and try to find
      //-- bindings for inner conjuncts.
      tabs = tabs.substring(0, tabs.length() - 1);
      for (i = 2; i <= j; i++, tabs = tabs.substring(0, tabs.length() - 1))
      {
        s += tabs + "}" + endl + tabs + "p[" + i + "].reset();" + endl;
        s += tabs + "p[" + i + "].bind(Term.merge(b, " + i + "));" + endl;
        s += tabs + "b[" + i + "] = p[" + i + "].nextBinding();" + endl;
      }

      //-- Apply the bindings found so far to the current conjunct.
      s += "\t\t}" + endl + endl + "\t\tp[";
      s += (j + 1) + "].bind(Term.merge(b, " + (j + 1) + "));" + endl;
    }

    return s;
  }

  /** To propagate the variable count to all the logical expressions the
   *  conjunction of which this object represents.
  */
  protected void propagateVarCount(int varCount)
  {
    for (int i = 0; i < le.length; i++)
      le[i].setVarCount(varCount);
  }

  /** This function produces the Java code to create an object of the class
   *  that was implemented to represent this conjunction at run time.
  */
  public String toCode()
  {
    return "new Precondition" + cnt + "(unifier)";
  }
}
