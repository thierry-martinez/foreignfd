package foreignfd;

import org.jacop.core.*;

import java.util.Collection;

public class IntVarWatched extends IntVar {
    private Collection<IntVar> singletons;

    public IntVarWatched(
            Store store,
            String name,
            IntDomain domain,
            Collection<IntVar> singletons) {
        super(store, name, domain);
        this.singletons = singletons;
    }

    public void domainHasChanged(int event) {
        super.domainHasChanged(event);
        if (singleton()) {
            singletons.add(this);
        }
    }
}
