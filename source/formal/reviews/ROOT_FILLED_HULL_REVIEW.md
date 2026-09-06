# Independent filled-hull correspondence review

Reviewer: root, independent of author formalization_preflight. Compared every proof in FilledHull.lean, source SHA-256 37be71e86146f0881b1d2d8b34e57bab5d05ccb649051a2a317a2bc497b1b4b0, with all three exact printed signatures and standard-only axiom outputs. Full passing report: formal/admissions/2026-09-05-empirical-hull-pre-admission-201.json. Exact version hashes are recorded in root-filled-hull-bindings.json.

The first theorem covers every nonnegative real radius, including zero, and the full complex norm exterior. The continuous radial-product image uses the connected unit circle in real dimension two; it does not extend the statement to a one-dimensional ambient space.

For an arbitrary closed complex set and arbitrary point x, the frontier of the complement component through x lies in the original closed set. If x is not in the complement, the component is empty under Mathlib's definition and the statement remains correct. Otherwise local connectedness makes the component open, and a second complement component near a frontier point yields the contradiction. No global connectedness of the original complement is assumed.

For every compact nonempty T the final theorem constructs K as the complement of the component containing a point outside a containing disk. The preceding exterior connectedness includes the entire disk exterior in that component. Consequently K is closed and bounded, contains T and is nonempty, its complement is preconnected, and its frontier lies in T. The exact signature proves these five properties with no geometric or potential hypotheses. It does not claim K contains every point of some larger original source S: in a support application the permitted source becomes T, with T contained in S, and the resulting roots remain in S. This distinction must be preserved in the endpoint.

The proof uses no regularity, capacity, equilibrium, or hidden finiteness assumption. The three statements match their recorded scope. No discrepancy, omitted quantifier, or unauthorized axiom was found. These topological results alone do not establish the small-area endpoint or either main target.
