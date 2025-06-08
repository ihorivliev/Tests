import itertools

# =============================================================================
# The Final Test: Brute-Force Enumeration of the Paradox of Divergent Fates
# =============================================================================

N = 3  # A universe of 3 patterns: 0, 1, 2
patterns = list(range(N))

print(f"--- Final 'No-Mercy' Test: Brute-Force Search (N={N}) ---")
print("Searching for a valid model permitting the 'Paradox of Divergent Fates'...")

# 1. Generate all possible functions for Structure and Step
# A function is just a mapping, e.g., Structure[0] = 1, Structure[1] = 2, etc.
# We can represent this as a tuple of output values.
all_structure_maps = list(itertools.product(patterns, repeat=N))
all_step_maps = list(itertools.product(patterns, repeat=N))

found_model = None

# 2. Iterate through every possible reality
for structure_map in all_structure_maps:
    for step_map in all_step_maps:
        
        # --- 3. Check if this reality obeys our core axioms ---
        
        # Check Axiom of Temporal Linearity (Step function must be injective)
        # If two different inputs map to the same output, it's not injective.
        if len(set(step_map)) < len(step_map):
            continue # This reality has a merging timeline, skip it.

        # The Universal Principle is implicitly handled by how we define Feeling below.
        # We can define Feeling directly from Structure: Feeling[p] = Structure[p]
        feeling_map = structure_map
        
        # --- 4. Search for the Paradox within this valid reality ---
        
        paradox_found = False
        # Find two distinct patterns, o1 and o2
        for o1 in patterns:
            for o2 in patterns:
                if o1 == o2:
                    continue
                
                # Check if they are perfect copies (same structure)
                if structure_map[o1] == structure_map[o2]:
                    
                    # Now check if their futures are DIFFERENT
                    future1 = step_map[o1]
                    future2 = step_map[o2]
                    
                    if structure_map[future1] != structure_map[future2]:
                        # PARADOX FOUND!
                        found_model = {
                            "Structure": {p: structure_map[p] for p in patterns},
                            "Feeling": {p: feeling_map[p] for p in patterns},
                            "Step (Reading-Path)": {p: step_map[p] for p in patterns},
                            "Witnesses": {
                                "Observer 1": o1,
                                "Observer 2": o2,
                                "Shared Structure": structure_map[o1],
                                "Future of O1": future1,
                                "Future of O2": future2,
                                "Structure of Future 1": structure_map[future1],
                                "Structure of Future 2": structure_map[future2]
                            }
                        }
                        paradox_found = True
                        break
            if paradox_found:
                break
        
        if paradox_found:
            break
    if found_model:
        break

# --- 5. Report the final result ---
print("\n" + "="*50)
if found_model:
    print("✅✅✅ DISCOVERY CONFIRMED: A model was found.")
    print("The 'Existe' framework permits the Paradox of Divergent Fates.")
    print("\n--- Concrete Example Model ---")
    for key, value in found_model.items():
        if key != "Witnesses":
            print(f"  {key}: {value}")
    print("\n  --- Paradox Witness ---")
    for key, value in found_model["Witnesses"].items():
        print(f"    {key}: {value}")
    print("\nThis provides definitive proof, free of solver ambiguity.")
else:
    print("❌❌❌ DISCOVERY: No model found.")
    print("In an N=3 universe, no reality can satisfy the axioms and the paradox.")
    print("This would imply a Strong Determinism not explicitly stated in the text.")
print("="*50)