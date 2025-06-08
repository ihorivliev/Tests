# Plot_Hasse_Diagram_Tool.py
import networkx as nx
import graphviz
from typing import List, Dict, Tuple, Set

# S_ord elements for Omega=3
S_ORD_ELEMENT_MAP_PLOT: Dict[int, str] = {0: "DFI1s", 1: "DFI2s", 2: "ZUs", 3: "AUs"}
S_ORD_PY_KEYS_PLOT: List[int] = sorted(S_ORD_ELEMENT_MAP_PLOT.keys())

def get_cover_relations_for_hasse(
    nodes: List[int], 
    all_true_relations: Set[Tuple[int,int]]
) -> List[Tuple[int,int]]:
    """Computes cover relations for a Hasse diagram from a FULL set of true <= relations."""
    g = nx.DiGraph()
    for u, v in all_true_relations:
        if u != v: # Hasse diagram doesn't show reflexive loops
            g.add_edge(u,v)

    # Transitive reduction removes edges (u,v) if there's a path u -> ... -> v
    # The edges remaining are the cover relations.
    try:
        tr_graph = nx.transitive_reduction(g)
        cover_relations = list(tr_graph.edges())
        return cover_relations
    except Exception as e:
        print(f"Could not compute transitive reduction: {e}. Plotting all non-reflexive relations instead.")
        return [(u,v) for u,v in all_true_relations if u!=v]

def plot_po_as_hasse(
    po_true_relations_tuples: List[Tuple[int,int]], # FULL list of (u,v) where u<=v
    element_map: Dict[int,str], 
    filename_prefix: str,
    title: str
):
    py_keys = sorted(element_map.keys())
    dot = graphviz.Digraph(comment=title)
    dot.attr(label=title, labelloc="t", fontsize="16", ranksep="0.3", nodesep="0.3")
    dot.attr(rankdir='BT') 

    for node_val_key in py_keys:
        dot.node(str(node_val_key), label=element_map[node_val_key])

    # Convert list of tuples to set for efficient lookup if needed, ensure reflexives included for full PO
    full_po_relations_set = set(po_true_relations_tuples)
    for k in py_keys: # Ensure reflexivity for cover computation if not already present
        full_po_relations_set.add((k,k))

    cover_edges_for_hasse = get_cover_relations_for_hasse(py_keys, full_po_relations_set)

    for u_node, v_node in cover_edges_for_hasse:
        dot.edge(str(u_node), str(v_node)) # Graphviz nodes are strings

    try:
        output_filename = f"{filename_prefix}_hasse"
        dot.render(output_filename, format='pdf', cleanup=True, quiet=True)
        print(f"  Generated Hasse diagram: {output_filename}.pdf")
    except Exception as e:
        print(f"  Error rendering graph with Graphviz for {filename_prefix}: {e}")
        print("  Ensure Graphviz is installed and in your system PATH.")

if __name__ == "__main__":
    print("This script helps visualize Partial Orders (POs) from SMT output as Hasse diagrams.")
    print("You need to provide the 'candidate_po_true_relations' list from SMT script output.")

    # Example: From your T-1 output (Ω=3, tweaked run)
    # Model Pair 1, le_mul: Non-reflexive edges = 6
    # This le_mul seems to be a total order: ZUs < DFI1s < DFI2s < AUs (or similar permutation)
    # Let's reconstruct its full relation set (including reflexives) assuming DFI1s=0, DFI2s=1, ZUs=2, AUs=3
    # Output for Model Pair 1 (le_mul):
    #   AUs     <= AUs          (3,3)
    #   DFIs1   <= AUs          (0,3)
    #   DFIs1   <= DFIs1      (0,0)
    #   DFIs1   <= DFIs2      (0,1)
    #   DFIs2   <= AUs          (1,3)
    #   DFIs2   <= DFIs2      (1,1)
    #   ZUs     <= AUs          (2,3)
    #   ZUs     <= DFI1s      (2,0)
    #   ZUs     <= DFIs2      (2,1) # Implied by ZUs <= DFI1s <= DFI2s
    #   ZUs     <= ZUs          (2,2)
    # This implies order: ZUs (2) < DFI1s (0) < DFI2s (1) < AUs (3)

    le_mul_model_1_relations = [
        (2,2),(0,0),(1,1),(3,3), # Reflexive
        (2,0),(2,1),(2,3),       # ZUs <= DFI1s, DFI2s, AUs
        (0,1),(0,3),             # DFI1s <= DFI2s, AUs
        (1,3)                    # DFI2s <= AUs
    ]
    plot_po_as_hasse(le_mul_model_1_relations, S_ORD_ELEMENT_MAP_PLOT, 
                     "le_mul_Omega3_T1_Pair1", 
                     "le_mul from T1 Model Pair 1 (ZUs < DFI1s < DFI2s < AUs)")

    # Example for a PO_add found (always sparse)
    # le_add for Model Pair 1 was: ZUs <= AUs (plus reflexives)
    le_add_model_1_relations = [(0,0), (1,1), (2,2), (2,3), (3,3)]
    plot_po_as_hasse(le_add_model_1_relations, S_ORD_ELEMENT_MAP_PLOT,
                     "le_add_Omega3_T1_Pair1",
                     "le_add from T1 Model Pair 1 (ZUs <= AUs)")