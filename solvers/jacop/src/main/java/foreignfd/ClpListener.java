package foreignfd;

import org.jacop.core.*;
import org.jacop.search.*;

public class ClpListener extends SimpleSolutionListener<IntVar> {
    public Jacop jacop;

    public boolean interrupted = false;

    public ClpListener(Jacop jacop) {
        super();
        this.jacop = jacop;
    }

    public boolean executeAfterSolution(
            Search<IntVar> search, SelectChoicePoint<IntVar> select) {
        try {
            jacop.checkConsistency();
            interrupted = jacop.loop();
            return interrupted;
        }
        catch (Exception exc) {
            exc.printStackTrace(System.err);
            System.exit(1);
            return false;
        }
    }
}
