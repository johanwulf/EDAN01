import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XgteqC;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

public class SplitSearch {
    private Store store;
    private IntVar[] variablesToReport;
    private IntVar costVariable;
    private boolean trace = true;
    private int costValue = IntDomain.MaxInt;
    private int depth = 0;
    public long N = 0;
    public int failedNodes;
    

    public SplitSearch(Store store) {
        this.store = store;
    }

    public void setVariablesToReport(IntVar[] variablesToReport) {
        this.variablesToReport = variablesToReport;
    }

    public void setCostVariable(IntVar costVariable) {
        this.costVariable = costVariable;
    }

    public boolean label(IntVar[] vars) {
        N++;

        if (trace) {
            for (int i = 0; i < vars.length; i++) 
            System.out.print (vars[i] + " ");
            System.out.println ();
        }
    
        ChoicePoint choice = null;
        boolean consistent;

        if (costVariable != null) {
            try {
                if (costVariable.min() <= costValue - 1) 
                    costVariable.domain.in(store.level, costVariable, costVariable.min(), costValue - 1);
                else
                    return false;
            } catch (FailException f) {
                return false;
            }
        }

        consistent = store.consistency();

        if (!consistent) {
            // Failed leaf of the search tree
            return false;
        } else { // consistent
    
            if (vars.length == 0) {
                // solution found; no more variables to label
                // update cost if minimization
                if (costVariable != null)
                    costValue = costVariable.min();
        
                reportSolution();
        
                return costVariable == null; // true is satisfiability search and false if minimization
            }
    
            choice = new ChoicePoint(vars);
            levelUp();
            store.impose(choice.getConstraint());
    
            // choice point imposed.
            consistent = label(choice.getSearchVariables());
    
            if (consistent) {
                levelDown();
                return true;
            } else {
                failedNodes++;
                restoreLevel();
                store.impose(new Not(choice.getConstraint()));
        
                // negated choice point imposed.
                consistent = label(vars);
        
                levelDown();
        
                if (consistent) {
                    return true;
                } else {
                    return false;
                }
            }
        }
    }

    private void levelDown() {
	    store.removeLevel(depth);
	    store.setLevel(--depth);
    }

    private void levelUp() {
	    store.setLevel(++depth);
    }

    private void restoreLevel() {
        store.removeLevel(depth);
        store.setLevel(store.level);
    }

    public void reportSolution() {
        System.out.println("Nodes visited: " + N);
    
        if (costVariable != null)
            System.out.println ("Cost is " + costVariable);
    
        for (int i = 0; i < variablesToReport.length; i++) 
            System.out.print (variablesToReport[i] + " ");
        
        System.out.println ("\n---------------");
    }

    public class ChoicePoint {
        private final int LOWER_HALF = 0;
        private final int UPPER_HALF = 1;

        IntVar var;
        IntVar[] searchVariables;
        int value;
        int strategy;
        int index;

        public ChoicePoint (IntVar[] v) {
            this.var = selectVariable(v);
            this.value = selectValue(var);
            this.strategy = LOWER_HALF;
            this.index = 0;
        }
    
        public IntVar[] getSearchVariables() {
            return searchVariables;
        }
    
        /**
         * example variable selection; input order
         */ 
        IntVar selectVariable(IntVar[] v) {
            if (v.length != 0) {
                IntVar value = v[0];
                
                if (value.min() == value.max()) {
                    searchVariables = new IntVar[v.length-1];
                    for (int i = 0; i < v.length-1; i++) {
                        searchVariables[i] = v[i+1]; 
                    }
                } else {
                    searchVariables = v;
                }

                return v[0];
            } else {
                System.err.println("Zero length list of variables for labeling");                 
                return new IntVar(store);
            }
        }

        int selectValue(IntVar v) {
            int c = 0;
            if (strategy == LOWER_HALF) {
                c = (v.min() + v.max()) / 2;
            } else if (strategy == UPPER_HALF) {
                if ((v.min() + v.max()) % 2 == 0) {
                    c = (v.min() + v.max()) / 2;
                } else {
                    c = (v.min() + v.max() + 1) / 2;
                }
            } else {
                c = v.min();
            }
            return c;
        }

        public PrimitiveConstraint getConstraint() {
            if (strategy == LOWER_HALF) {
                return new XlteqC(var, value);
            } else if (strategy == UPPER_HALF) {
                return new XgteqC(var, value);
            } else {
                return new XeqC(var, value);
            }
        }
    }
}
