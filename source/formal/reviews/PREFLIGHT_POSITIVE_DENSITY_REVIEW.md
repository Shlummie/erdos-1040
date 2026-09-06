# Independent correspondence review: PositiveDensity and nested proof helper

Reviewer: `formalization_preflight` (not the proof author).
Frozen PositiveDensity source SHA-256: `2e385fb5ec722ed865971ae29d7d5377835ac31372712139fcefa2ef59799597`.
Machine snapshot: `formal/admissions/2026-09-05-energy-and-area-pre-admission.json`, checked `2026-09-05T04:55:21.050073+00:00`, 140 declarations, machine checks PASS; main target remains incomplete.

I read the entire source and its three current natural-language statements, then independently ran `#print sig` and `#print axioms` through the pinned Lean 4.33.1 toolchain. All six output messages match the immutable passing snapshot exactly. The fresh log is `formal/.audit/preflight-positive-density.log`; exit code 0. All three declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. The bindings file records the actual source, printed-signature, and current source-statement hashes.

| Declaration | Correspondence assessment |
|---|---|
| `Erdos1040.shifted_density_mass_pos` | Every measurable space and probability measure are quantified. The signed real function is measurable and pointwise norm-bounded by C, with explicit C < A. Its actual integral exists by boundedness and finite mass. Integrating the lower bound -C gives strict positivity of the mass after adding A. No independent positivity premise is inserted. |
| `Erdos1040.isProbabilityMeasure_shifted_density` | Uses exactly the same premises. The density is the ENNReal embedding of (f+A)/(integral f+A), including the intended parentheses and denominator. Numerator and denominator are positive under the existing hypotheses, so the embedding does not truncate negative mass. Direct integration proves mass one for the actual withDensity measure. |
| `Erdos1040.integral_shifted_density` | The codomain is any complete real normed vector space, and g is explicitly integrable under the original probability measure. Bounded f makes f times g integrable, so the displayed weighted integral and all linearity steps are actual Bochner integrals. The right side is the inverse shifted mass times (integral f*g plus A times integral g). The source probability, measurability, bound, and C < A are retained. |

No omitted quantifier, altered domain, extra assumption, changed measure, or hidden weakening was found relative to these three registered statements. This module constructs a positive probability from a bounded signed density and supplies its integral identity. It does not establish existence of a useful signed density, a positive source-potential margin, logarithmic capacity, or the main Erdős theorem.

## Checker extension review

Checker source SHA-256 at review: `168890b0cd94602da0dae6920b997d1e47a29d5035c0ed8be15e6216e8a55ca2`. The newly needed proof-helper suffix is `_proof_1_1`. Its accepted pattern is `_proof_[0-9]+(?:_[0-9]+)*`: a finite sequence of nonempty numeric segments. The exact ancestor must already be a tracked declaration. Missing segments, doubled underscores, letters, and intervening namespace segments fail this pattern; six positive/negative assertions were checked.

The saved kernel inventory identifies `Erdos1040.exists_L2_tolerance_for_small_negative_set._proof_1_1` in `Erdos1040.AtomicAreaAssembly` as a theorem with no source declaration range, safe code, and only `propext` and `Quot.sound`. I read its owning source theorem: no custom helper declaration or untracked assumption is present, and the theorem proves the stated L2-to-small-negative-set estimate. The tracked ancestor is present in the same module. The checker continues to reject unsafe constants, custom axioms, nonstandard axiom dependencies, and untracked constants without the permitted helper shape/range combination. The extension therefore admits this actual compiler-generated nested helper without weakening the axiom gate. As before, helper origin is an audited compiler convention; a missing range by itself is never sufficient.

Verdict: the three PositiveDensity statements pass independent correspondence review; the narrowly extended nested-proof pattern passes this audit. Promotion and synchronization of the canonical records remain the parent's responsibility.
