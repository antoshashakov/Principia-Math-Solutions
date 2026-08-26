# Lean formalizations

Each `problems/<id>/Problem<id>.lean` is the machine-checked formalization of that problem's
`solution.md`.

These files are **copies**.  The canonical modules live in the `Principia` library of the
PrincipiaAI repository, at `Principia Application/LeanSandbox/Principia/MathDB/`, because that is
where they are actually built and gated.  A module counts as verified only when all four hold:

1. it builds under Lean 4.31.0 / Mathlib `v4.31.0` on GitHub Actions;
2. every declaration is listed in `Principia/MathDB/Gate.lean` and its `#print axioms` footprint is
   inside `[propext, Classical.choice, Quot.sound]` — so no `sorry`, no `native_decide`;
3. an adversarial statement-faithfulness judge agrees the formal statement renders the informal
   claim (`Website/scripts/comparator.mjs`);
4. any source-level input is a **named hypothesis**, never an `axiom`.

Where a file does carry a hypothesis, its module doc-string names it and says why it is not proved.
