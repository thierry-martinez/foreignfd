package foreignfd;

import org.jacop.core.*;
import org.jacop.constraints.*;
import org.jacop.search.*;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Scanner;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

public class Jacop {
    public static void main(String[] args) {
        try {
            Jacop jacop = new Jacop();
            jacop.loop();
        }
        catch (Exception exc) {
            exc.printStackTrace(System.err);
            System.exit(1);
        }
    }

    private Store store = new Store();

    private LinkedList<IntVar> singletons = new LinkedList<IntVar>();

    private boolean result;

    public boolean loop() throws Exception {
        DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
        DocumentBuilder builder = factory.newDocumentBuilder();
        Scanner scanner = new Scanner(System.in);
        int startLevel = store.level;
        while (true) {
            String line;
            try {
                line = scanner.nextLine();
            }
            catch (NoSuchElementException _) {
                break;
            }
            byte[] bytes = line.getBytes(StandardCharsets.UTF_8);
            InputStream inputStream = new ByteArrayInputStream(bytes);
            Document document = builder.parse(inputStream);
            Element root = document.getDocumentElement();
            if (executeCommand(root, startLevel)) {
                return result;
            }
        }
        return false;
    }

    private Map<String, IntVar> varMap = new HashMap<String, IntVar>();

    public IntVar findVariable(String name) {
        IntVar result = varMap.get(name);
        if (result == null) {
            throw new Error("Unbound variable " + name);
        }
        return result;
    }

    public boolean executeCommand(Element root, int startLevel) {
        String tagName = root.getTagName();
        if (tagName.equals("IntVar")) {
            String name = root.getAttribute("name");
            NodeList intervals = root.getElementsByTagName("Interval");
            int length = intervals.getLength();
            IntDomain domain = new IntervalDomain(length);
            for (int i = 0; i < length; i++) {
                Element interval = (Element) intervals.item(i);
                int min = Integer.parseInt(interval.getAttribute("min"));
                int max = Integer.parseInt(interval.getAttribute("max"));
                domain.unionAdapt(min, max);
            }
            IntVar var = new IntVarWatched(store, name, domain, singletons);
            varMap.put(name, var);
        }
        else if (tagName.equals("AutoIntVar")) {
            String name = root.getAttribute("name");
            IntDomain domain =
                new IntervalDomain(IntDomain.MinInt, IntDomain.MaxInt);
            IntVar var = new IntVarWatched(store, name, domain, singletons);
            varMap.put(name, var);
        }
        else if (tagName.equals("GetDomain")) {
            IntVar X = findVariable(root.getAttribute("X"));
            IntervalDomain domain = (IntervalDomain) X.dom();
            IntervalEnumeration intervals = domain.intervalEnumeration();
            printInterval(intervals.nextElement());
            while (intervals.hasMoreElements()) {
                System.out.print("\\/");
                printInterval(intervals.nextElement());
            }
            System.out.println(".");
        }
        else if (tagName.equals("Constraint")) {
            Element child = getChildNodesElement(root).iterator().next();
            store.impose(buildConstraint(child));
            checkConsistency();
        }
        else if (tagName.equals("Try")) {
            store.setLevel(store.level + 1);
        }
        else if (tagName.equals("Backtrack")) {
            if (store.level > startLevel) {
                store.removeLevel(store.level);
                store.setLevel(store.level - 1);
            }
            else {
                result = true;
                return true;
            }
        }
        else if (tagName.equals("Labeling")) {
            String varSel = root.getAttribute("varSel");
            String valSel = root.getAttribute("valSel");
            String branching = root.getAttribute("branching");
            NodeList varList = root.getElementsByTagName("Var");
            int length = varList.getLength();
            IntVar[] vars = new IntVar[length];
            for (int i = 0; i < length; i++) {
                Element elt = (Element) varList.item(i);
                vars[i] = findVariable(elt.getAttribute("X"));
            }
            DepthFirstSearch<IntVar> dfs = new DepthFirstSearch<>();
            ComparatorVariable<IntVar> varSelect;
            ComparatorVariable<IntVar> tieSelect = null;
            if (varSel.equals("leftmost")) {
                varSelect = null;
            }
            else if (varSel.equals("ff")) {
                varSelect = new SmallestDomain<IntVar>();
            }
            else if (varSel.equals("ffc")) {
                varSelect = new SmallestDomain<IntVar>();
                tieSelect = new MostConstrainedDynamic<IntVar>();
            }
            else if (varSel.equals("min")) {
                varSelect = new SmallestMin<IntVar>();
            }
            else if (varSel.equals("max")) {
                varSelect = new LargestMax<IntVar>();
            }
            else {
                throw new Error("Unknown variable selection strategy");
            }
            SelectChoicePoint<IntVar> select;
            if (branching.equals("bisect")) {
                Indomain<IntVar> middle = new IndomainMiddle<>();
                SplitSelect<IntVar> split =
                    new SplitSelect<>(vars, varSelect, tieSelect, middle);
                if (valSel.equals("down")) {
                    split.leftFirst = false;
                }
                select = split;
            }
            else {
                Indomain<IntVar> indom;
                if (valSel.equals("up")) {
                    indom = new IndomainMin<IntVar>();
                }
                else if (valSel.equals("middle")) {
                    indom = new IndomainMiddle<IntVar>();
                }
                else {
                    indom = new IndomainMax<IntVar>();
                }
                select =
                    new SimpleSelect<IntVar>(vars, varSelect, tieSelect, indom);
            }
            final Jacop jacop = this;
            ClpListener listener = new ClpListener(this);
            dfs.setSolutionListener(listener);
            dfs.setPrintInfo(false);
            dfs.labeling(store, select);
            if (listener.interrupted) {
                store.removeLevel(store.level);
                store.setLevel(store.level - 1);
            }
            else {
                System.out.println("inconsistent.");
            }
        }
        else if (tagName.equals("Next")) {
            result = false;
            return true;
        }
        return false;
    }

    Constraint buildConstraint(Element elt) {
        String tagName = elt.getTagName();
        if (tagName.equals("Linear")) {
            String rel = elt.getAttribute("rel");
            int constant = Integer.parseInt(elt.getAttribute("constant"));
            NodeList vars = elt.getElementsByTagName("Var");
            int length = vars.getLength();
            IntVar[] list = new IntVar[length];
            int[] weights = new int[length];
            for (int i = 0; i < length; i++) {
                Element var = (Element) vars.item(i);
                list[i] = findVariable(var.getAttribute("X"));
                weights[i] = Integer.parseInt(var.getAttribute("weight"));
            }
            if (rel.equals("=")) {
                if (length == 2) {
                    if (constant == 0 &&
                        (weights[0] == 1 && weights[1] == -1
                         || weights[0] == -1 && weights[1] == 1)) {
                        return new XeqY(list[0], list[1]);
                    }
                    else if (weights[0] == 1 && weights[1] == -1) {
                        return new XplusCeqZ(list[1], constant, list[0]);
                    }
                    else if (weights[0] == -1 && weights[1] == 1) {
                        return new XplusCeqZ(list[0], constant, list[1]);
                    }
                }
            }
            else if (rel.equals("!=")) {
                if (length == 2 && constant == 0 &&
                    (weights[0] == 1 && weights[1] == -1
                     || weights[0] == -1 && weights[1] == 1)) {
                    return new XneqY(list[0], list[1]);
                }
            }
            else if (rel.equals("<")) {
                if (length == 2 && constant == 0) {
                    if (weights[0] == 1 && weights[1] == -1) {
                        return new XltY(list[0], list[1]);
                    }
                    else if (weights[0] == -1 && weights[1] == 1) {
                        return new XltY(list[1], list[0]);
                    }
                }
            }
            else if (rel.equals("<=")) {
                if (length == 2 && constant == 0) {
                    if (weights[0] == 1 && weights[1] == -1) {
                        return new XlteqY(list[0], list[1]);
                    }
                    else if (weights[0] == -1 && weights[1] == 1) {
                        return new XlteqY(list[1], list[0]);
                    }
                }
            }
            else if (rel.equals(">")) {
                if (length == 2 && constant == 0) {
                    if (weights[0] == 1 && weights[1] == -1) {
                        return new XgtY(list[0], list[1]);
                    }
                    else if (weights[0] == -1 && weights[1] == 1) {
                        return new XgtY(list[1], list[0]);
                    }
                }
            }
            else if (rel.equals(">=")) {
                if (length == 2 && constant == 0) {
                    if (weights[0] == 1 && weights[1] == -1) {
                        return new XgteqY(list[0], list[1]);
                    }
                    else if (weights[0] == -1 && weights[1] == 1) {
                        return new XgteqY(list[1], list[0]);
                    }
                }
            }
            /* // Bug with reified linear constraints
              return new Linear(store, list, weights, rel, constant);
            */
            IntVar X;
            if (length == 1 && weights[0] == 1) {
                X = list[0];
            }
            else {
                X = new IntVar(store, IntDomain.MinInt, IntDomain.MaxInt);
                IntVar[] listX = new IntVar[length + 1];
                int[] weightsX = new int[length + 1];
                for (int i = 0; i < length; i++) {
                    listX[i] = list[i];
                    weightsX[i] = weights[i];
                }
                listX[length] = X;
                weightsX[length] = -1;
                store.impose(new Linear(store, listX, weightsX, "=", 0));
            }
            if (rel.equals("=")) {
                return new XeqC(X, constant);
            }
            else if (rel.equals("!=")) {
                return new XneqC(X, constant);
            }
            else if (rel.equals("<")) {
                return new XltC(X, constant);
            }
            else if (rel.equals("<=")) {
                return new XlteqC(X, constant);
            }
            else if (rel.equals(">")) {
                return new XgtC(X, constant);
            }
            else if (rel.equals(">=")) {
                return new XgteqC(X, constant);
            }
            throw new Error("Unknown relation " + rel);
        }
        else if (tagName.equals("XmulYeqZ")) {
            IntVar X = findVariable(elt.getAttribute("X"));
            IntVar Y = findVariable(elt.getAttribute("Y"));
            IntVar Z = findVariable(elt.getAttribute("Z"));
            return new XmulYeqZ(X, Y, Z);
        }
        else if (tagName.equals("XmulYeqC")) {
            IntVar X = findVariable(elt.getAttribute("X"));
            IntVar Y = findVariable(elt.getAttribute("Y"));
            int C = Integer.parseInt(elt.getAttribute("C"));
            return new XmulYeqC(X, Y, C);
        }
        else if (tagName.equals("XmodYeqZ")) {
            IntVar X = findVariable(elt.getAttribute("X"));
            IntVar Y = findVariable(elt.getAttribute("Y"));
            IntVar Z = findVariable(elt.getAttribute("Z"));
            return new XmodYeqZ(X, Y, Z);
        }
        else if (tagName.equals("AllDifferent")) {
            String consistency = elt.getAttribute("consistency");
            Collection<IntVar> vars = getVariables(elt);
            if (consistency.equals("gac")) {
                return new Alldistinct(vars.toArray(new IntVar[vars.size()]));
            }
            else {
                return new Alldifferent(vars.toArray(new IntVar[vars.size()]));
            }
        }
        else if (tagName.equals("Not")) {
            Element child = getChildNodesElement(elt).iterator().next();
            PrimitiveConstraint sub = buildPrimitiveConstraint(child);
            return new Not(sub);
        }
        else if (tagName.equals("And")) {
            PrimitiveConstraint[] children = getChildNodesElement(elt).stream()
                .map(this::buildPrimitiveConstraint)
                .toArray(size -> new PrimitiveConstraint[size]);
            return new And(children);
        }
        else if (tagName.equals("Or")) {
            PrimitiveConstraint[] children = getChildNodesElement(elt).stream()
                .map(this::buildPrimitiveConstraint)
                .toArray(size -> new PrimitiveConstraint[size]);
            return new Or(children);
        }
        else if (tagName.equals("Xor")) {
            PrimitiveConstraint[] children = getChildNodesElement(elt).stream()
                .map(this::buildPrimitiveConstraint)
                .toArray(size -> new PrimitiveConstraint[size]);
            return new Or(children[0], children[1]);
        }
        else if (tagName.equals("Min")) {
            Collection<IntVar> vars = getVariables(elt);
            IntVar X = findVariable(elt.getAttribute("X"));
            return new Min(vars.toArray(new IntVar[vars.size()]), X);
        }
        else if (tagName.equals("Max")) {
            Collection<IntVar> vars = getVariables(elt);
            IntVar X = findVariable(elt.getAttribute("X"));
            return new Max(vars.toArray(new IntVar[vars.size()]), X);
        }
        else if (tagName.equals("AbsXeqY")) {
            IntVar X = findVariable(elt.getAttribute("X"));
            IntVar Y = findVariable(elt.getAttribute("Y"));
            return new AbsXeqY(X, Y);
        }
        return null;
    }

    public PrimitiveConstraint buildPrimitiveConstraint(Element elt) {
        Constraint c = buildConstraint(elt);
        return (PrimitiveConstraint) c;
    }

    public Collection<Element> getChildNodesElement(Element elt) {
        Collection<Element> result = new LinkedList<>();
        NodeList childNodes = elt.getChildNodes();
        int length = childNodes.getLength();
        for (int i = 0; i < length; i++) {
            Node node = childNodes.item(i);
            if (node.getNodeType() == Node.ELEMENT_NODE) {
                result.add((Element) node);
            }
        }
        return result;
    }


    public Collection<IntVar> getVariables(Element elt) {
        Collection<IntVar> result = new LinkedList<>();
        NodeList vars = elt.getElementsByTagName("Var");
        int vars_length = vars.getLength();
        NodeList constants = elt.getElementsByTagName("Constant");
        int constants_length = constants.getLength();
        for (int i = 0; i < vars_length; i++) {
            Element var = (Element) vars.item(i);
            result.add(findVariable(var.getAttribute("X")));
        }
        for (int i = 0; i < constants_length; i++) {
            Element var = (Element) constants.item(i);
            int c = Integer.parseInt(var.getAttribute("C"));
            result.add(new IntVar(store, c, c));
        }
        return result;
    }

    public void printInterval(Interval interval) {
        if (interval.singleton()) {
            System.out.format("%d", interval.min());
        }
        else {
            System.out.format("%d..%d", interval.min(), interval.max());
        }
    }

    public void checkConsistency() {
        if (store.consistency()) {
            /*
            System.out.print("consistent([");
            IntVar x = singletons.poll();
            if (x != null) {
                System.out.format("%s=(%d)", x.id(), x.value());
                while ((x = singletons.poll()) != null) {
                    System.out.format(",%s=(%d)", x.id(), x.value());
                }
            }
            System.out.println("]).");
            */
            IntVar x;
            while ((x = singletons.poll()) != null) {
                System.out.format("equal(%s,%d).\n", x.id(), x.value());
            }
            System.out.println("consistent.");
        }
        else {
            System.out.println("inconsistent.");
        }
    }
}
