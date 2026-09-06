# Erdős #1040 - isolated declaration index

Publication-package derivative of the unchanged claims manifest.
All 274 entries are retained. Historical unrelated research is omitted.
Review identifiers in the manifest refer to AI agents, not human referees.

## E1040-ROOT-POLYNOMIAL - `Erdos1040.rootPolynomial`

For each finite list of n complex roots, rootPolynomial is the product of X minus those roots, including multiplicities.

Module: `Erdos1040.Basic`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.rootPolynomial : {n : ℕ} → (Fin n → ℂ) → Polynomial.{0} ℂ
```

## E1040-FULL - `Erdos1040.unitLemniscate`

The strict unit sublevel set of the product of z minus the given finite list of complex roots.

Module: `Erdos1040.Basic`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.unitLemniscate : {n : ℕ} → (Fin n → ℂ) → Set.{0} ℂ
```

## E1040-FULL - `Erdos1040.HasArbitrarilySmallLemniscates`

For every positive real tolerance, there is a positive integer degree and that many complex roots in F whose strict unit lemniscate has planar Lebesgue area less than the tolerance.

Module: `Erdos1040.Basic`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.HasArbitrarilySmallLemniscates : Set.{0} ℂ → Prop
```

## E1040-ROOT-POLYNOMIAL - `Erdos1040.rootPolynomial_monic`

For every finite list of complex roots, the product of X minus those roots is monic.

Module: `Erdos1040.Basic`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.rootPolynomial_monic : ∀ {n : ℕ} (roots : Fin n → ℂ),
  Polynomial.Monic.{0} (Erdos1040.rootPolynomial roots)
```

## E1040-ROOT-POLYNOMIAL - `Erdos1040.rootPolynomial_eval`

For every finite list of complex roots and every complex z, evaluating rootPolynomial at z equals the product of z minus those roots.

Module: `Erdos1040.Basic`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.rootPolynomial_eval : ∀ {n : ℕ} (roots : Fin n → ℂ) (z : ℂ),
  Eq.{1} (Polynomial.eval.{0} z (Erdos1040.rootPolynomial roots)) (∏ i, HSub.hSub.{0, 0, 0} z (roots i))
```

## E1040-ROOT-POLYNOMIAL - `Erdos1040.rootPolynomial_natDegree`

For every list indexed by Fin n of complex roots, rootPolynomial has natural degree exactly n.

Module: `Erdos1040.Basic`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.rootPolynomial_natDegree : ∀ {n : ℕ} (roots : Fin n → ℂ),
  Eq.{1} (Polynomial.natDegree.{0} (Erdos1040.rootPolynomial roots)) n
```

## E1040-ROOT-POLYNOMIAL - `Erdos1040.rootPolynomial_isRoot_iff`

For every finite list of complex roots and every complex z, z is a root of rootPolynomial if and only if z equals one of the listed roots.

Module: `Erdos1040.Basic`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.rootPolynomial_isRoot_iff : ∀ {n : ℕ} (roots : Fin n → ℂ) (z : ℂ),
  Polynomial.IsRoot.{0} (Erdos1040.rootPolynomial roots) z ↔ ∃ i, Eq.{1} z (roots i)
```

## E1040-UNBOUNDED - `Erdos1040.quadratic_sublevel_subset_balls`

For any distinct complex a and b, the strict unit sublevel set of (z-a)(z-b) lies in the union of the open balls centered at a and b of radius 2 divided by their distance.

Module: `Erdos1040.Unbounded`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.quadratic_sublevel_subset_balls : ∀ (a b : ℂ),
  Ne.{1} a b →
    (Set.ofPred.{0} fun z =>
        LT.lt.{0} (Norm.norm.{0} (HMul.hMul.{0, 0, 0} (HSub.hSub.{0, 0, 0} z a) (HSub.hSub.{0, 0, 0} z b))) 1) ⊆
      Union.union.{0} (Metric.ball.{0} a (HDiv.hDiv.{0, 0, 0} 2 (Norm.norm.{0} (HSub.hSub.{0, 0, 0} a b))))
        (Metric.ball.{0} b (HDiv.hDiv.{0, 0, 0} 2 (Norm.norm.{0} (HSub.hSub.{0, 0, 0} a b))))
```

## E1040-UNBOUNDED - `Erdos1040.volume_quadratic_sublevel_le`

For any distinct complex a and b, the planar Lebesgue area of the strict unit sublevel set of (z-a)(z-b) is at most 8 pi divided by the square of their distance.

Module: `Erdos1040.Unbounded`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.volume_quadratic_sublevel_le : ∀ (a b : ℂ),
  Ne.{1} a b →
    LE.le.{0}
      (MeasureTheory.MeasureSpace.volume.{0}
        (Set.ofPred.{0} fun z =>
          LT.lt.{0} (Norm.norm.{0} (HMul.hMul.{0, 0, 0} (HSub.hSub.{0, 0, 0} z a) (HSub.hSub.{0, 0, 0} z b))) 1))
      (ENNReal.ofReal
        (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} 8 Real.pi)
          (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} a b)) 2)))
```

## E1040-UNBOUNDED - `Erdos1040.unbounded_exists_quadratic_small_area`

For every unbounded complex set F and every positive real tolerance, there are distinct a and b in F such that the strict unit sublevel set of (z-a)(z-b) has planar Lebesgue area less than the tolerance.

Module: `Erdos1040.Unbounded`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.unbounded_exists_quadratic_small_area : ∀ (F : Set.{0} ℂ),
  ¬Bornology.IsBounded.{0} F →
    ∀ (ε : ℝ),
      LT.lt.{0} 0 ε →
        ∃ a,
          Membership.mem.{0, 0} F a ∧
            ∃ b,
              Membership.mem.{0, 0} F b ∧
                Ne.{1} a b ∧
                  LT.lt.{0}
                    (MeasureTheory.MeasureSpace.volume.{0}
                      (Set.ofPred.{0} fun z =>
                        LT.lt.{0}
                          (Norm.norm.{0} (HMul.hMul.{0, 0, 0} (HSub.hSub.{0, 0, 0} z a) (HSub.hSub.{0, 0, 0} z b))) 1))
                    (ENNReal.ofReal ε)
```

## E1040-UNBOUNDED - `Erdos1040.unbounded_hasArbitrarilySmallLemniscates`

Every unbounded subset of the complex plane satisfies HasArbitrarilySmallLemniscates, with positive degree, roots in the original set, and strict unit sublevel area below every positive real tolerance.

Module: `Erdos1040.Unbounded`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.unbounded_hasArbitrarilySmallLemniscates : ∀ {F : Set.{0} ℂ},
  ¬Bornology.IsBounded.{0} F → Erdos1040.HasArbitrarilySmallLemniscates F
```

## E1040-L2KERNEL - `Erdos1040.exists_pos_integrableOn_log_norm_sq_ball`

There exists a positive radius such that the square of the totalized real logarithm of the complex norm is integrable on the planar open ball of that radius centered at zero.

Module: `Erdos1040.LogKernel`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_pos_integrableOn_log_norm_sq_ball : ∃ r,
  LT.lt.{0} 0 r ∧
    MeasureTheory.IntegrableOn.{0, 0} (fun z => HPow.hPow.{0, 0, 0} (Real.log (Norm.norm.{0} z)) 2)
      (Metric.ball.{0} 0 r) MeasureTheory.MeasureSpace.volume.{0}
```

## E1040-L2KERNEL - `Erdos1040.locallyIntegrable_log_norm_sq`

The square of the totalized real logarithm of the complex norm is locally integrable with respect to planar Lebesgue measure on the complex plane.

Module: `Erdos1040.LogKernel`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.locallyIntegrable_log_norm_sq : MeasureTheory.LocallyIntegrable.{0, 0}
  (fun z => HPow.hPow.{0, 0, 0} (Real.log (Norm.norm.{0} z)) 2) MeasureTheory.MeasureSpace.volume.{0}
```

## E1040-L2KERNEL - `Erdos1040.memLp_log_norm_of_isCompact`

For every compact subset K of the complex plane, the totalized real logarithm of the complex norm belongs to real L2 with respect to planar Lebesgue measure restricted to K.

Module: `Erdos1040.LogKernel`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.memLp_log_norm_of_isCompact : ∀ {K : Set.{0} ℂ},
  IsCompact.{0} K →
    MeasureTheory.MemLp.{0, 0} (fun z => Real.log (Norm.norm.{0} z)) 2
      (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K)
```

## E1040-ATOMIC-LOG - `Erdos1040.atomicLogPotential`

The equally weighted average of the totalized real logarithms of distances to a finite list of complex roots, with denominator the list length. In the empty-list case, Lean totalizes division by zero and both relevant normalized expressions are zero.

Module: `Erdos1040.AtomicPotential`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.atomicLogPotential : {n : ℕ} → (Fin n → ℂ) → ℂ → ℝ
```

## E1040-ATOMIC-LOG - `Erdos1040.atomicLogPotential_eq_log_product`

Away from every listed root, the atomic logarithmic potential equals the logarithm of the modulus of the product divided by the number of roots. In the empty-list case, Lean totalizes division by zero and both relevant normalized expressions are zero.

Module: `Erdos1040.AtomicPotential`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.atomicLogPotential_eq_log_product : ∀ {n : ℕ} (roots : Fin n → ℂ) (z : ℂ),
  (∀ (i : Fin n), Ne.{1} z (roots i)) →
    Eq.{1} (Erdos1040.atomicLogPotential roots z)
      (HDiv.hDiv.{0, 0, 0} (Real.log (Norm.norm.{0} (∏ i, HSub.hSub.{0, 0, 0} z (roots i)))) ↑n)
```

## E1040-ATOMIC-LOG - `Erdos1040.atomicLogPotential_neg_iff`

For a positive number of roots and a point unequal to every root, the atomic logarithmic potential is negative if and only if the point belongs to the strict unit lemniscate.

Module: `Erdos1040.AtomicPotential`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.atomicLogPotential_neg_iff : ∀ {n : ℕ},
  LT.lt.{0} 0 n →
    ∀ (roots : Fin n → ℂ) (z : ℂ),
      (∀ (i : Fin n), Ne.{1} z (roots i)) →
        (LT.lt.{0} (Erdos1040.atomicLogPotential roots z) 0 ↔ Membership.mem.{0, 0} (Erdos1040.unitLemniscate roots) z)
```

## E1040-ATOMIC-LOG - `Erdos1040.ae_ne_roots`

Planar Lebesgue almost every complex point is unequal to every member of a given finite list of roots.

Module: `Erdos1040.AtomicPotential`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.ae_ne_roots : ∀ {n : ℕ} (roots : Fin n → ℂ), ∀ᵐ (z : ℂ), ∀ (i : Fin n), Ne.{1} z (roots i)
```

## E1040-ATOMIC-LOG - `Erdos1040.unitLemniscate_ae_eq_atomicLogPotential_neg`

For every positive finite number of roots, the strict unit lemniscate and the negative set of the totalized atomic logarithmic potential agree almost everywhere for planar Lebesgue measure.

Module: `Erdos1040.AtomicPotential`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.unitLemniscate_ae_eq_atomicLogPotential_neg : ∀ {n : ℕ},
  LT.lt.{0} 0 n →
    ∀ (roots : Fin n → ℂ),
      Erdos1040.unitLemniscate roots =ᵐ[MeasureTheory.MeasureSpace.volume.{0}]
        Set.ofPred.{0} fun z => LT.lt.{0} (Erdos1040.atomicLogPotential roots z) 0
```

## E1040-ATOMIC-LOG - `Erdos1040.volume_unitLemniscate_eq_atomicLogPotential_neg`

For every positive finite number of roots, the planar Lebesgue area of the strict unit lemniscate equals the area of the negative set of the totalized atomic logarithmic potential.

Module: `Erdos1040.AtomicPotential`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.volume_unitLemniscate_eq_atomicLogPotential_neg : ∀ {n : ℕ},
  LT.lt.{0} 0 n →
    ∀ (roots : Fin n → ℂ),
      Eq.{1} (MeasureTheory.MeasureSpace.volume.{0} (Erdos1040.unitLemniscate roots))
        (MeasureTheory.MeasureSpace.volume.{0}
          (Set.ofPred.{0} fun z => LT.lt.{0} (Erdos1040.atomicLogPotential roots z) 0))
```

## E1040-L2KERNEL - `Erdos1040.memLp_log_norm_sub_of_isCompact`

For every complex source w and every compact subset K of the complex plane, the totalized real logarithm of distance to w belongs to real L2 with respect to planar Lebesgue measure restricted to K.

Module: `Erdos1040.LogKernel`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.memLp_log_norm_sub_of_isCompact : ∀ (w : ℂ) {K : Set.{0} ℂ},
  IsCompact.{0} K →
    MeasureTheory.MemLp.{0, 0} (fun z => Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z w))) 2
      (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K)
```

## E1040-L2KERNEL - `Erdos1040.memLp_log_norm_sub_closedBall`

For every complex center c, complex source w, and real radius r, the totalized real logarithm of distance to w belongs to real L2 with respect to planar Lebesgue measure restricted to the closed ball of center c and radius r.

Module: `Erdos1040.LogKernel`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.memLp_log_norm_sub_closedBall : ∀ (c w : ℂ) (r : ℝ),
  MeasureTheory.MemLp.{0, 0} (fun z => Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z w))) 2
    (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} (Metric.closedBall.{0} c r))
```

## E1040-AREA-TRANSFER - `Erdos1040.measure_neg_le_margin_add_sq_eLpNorm`

For any measure on the complex plane, real functions f and g with almost-everywhere strongly measurable difference, and positive nonnegative-real margin delta, the measure where f is negative is at most the measure where g is below delta plus the squared extended nonnegative-real L2 seminorm (possibly infinite) of f minus g divided by delta squared. This is a conditional error-transfer inequality, not the existence of a suitable g or approximation.

Module: `Erdos1040.AreaTransfer`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.measure_neg_le_margin_add_sq_eLpNorm : ∀ (μ : MeasureTheory.Measure.{0} ℂ) (f g : ℂ → ℝ),
  MeasureTheory.AEStronglyMeasurable.{0, 0} (fun z => HSub.hSub.{0, 0, 0} (f z) (g z)) μ →
    ∀ (δ : NNReal),
      LT.lt.{0} 0 δ →
        LE.le.{0} (μ (Set.ofPred.{0} fun z => LT.lt.{0} (f z) 0))
          (HAdd.hAdd.{0, 0, 0} (μ (Set.ofPred.{0} fun z => LT.lt.{0} (g z) ↑δ))
            (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Inv.inv.{0} ↑δ) 2)
              (HPow.hPow.{0, 0, 0} (MeasureTheory.eLpNorm.{0, 0} (fun z => HSub.hSub.{0, 0, 0} (f z) (g z)) 2 μ) 2)))
```

## E1040-L2KERNEL - `Erdos1040.restrictAreaL2`

For any set K of the complex plane, restrictAreaL2 maps a real L2 class for planar Lebesgue measure to its class for planar Lebesgue measure restricted to K, using an almost-everywhere representative.

Module: `Erdos1040.LogContinuity`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.restrictAreaL2 : (K : Set.{0} ℂ) →
  ↥(MeasureTheory.Lp.{0, 0} ℝ 2 MeasureTheory.MeasureSpace.volume.{0}) →
    ↥(MeasureTheory.Lp.{0, 0} ℝ 2 (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K))
```

## E1040-L2KERNEL - `Erdos1040.lipschitzWith_restrictAreaL2`

For any set K of the complex plane, restricting global real area-L2 classes to K is 1-Lipschitz in the L2 norms.

Module: `Erdos1040.LogContinuity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.lipschitzWith_restrictAreaL2 : ∀ (K : Set.{0} ℂ), LipschitzWith.{0, 0} 1 (Erdos1040.restrictAreaL2 K)
```

## E1040-L2KERNEL - `Erdos1040.continuous_translateAreaL2`

For every real L2 class f for global planar Lebesgue measure, translation of its argument by minus a complex source w depends continuously on w in the global L2 norm.

Module: `Erdos1040.LogContinuity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.continuous_translateAreaL2 : ∀
  (f : ↥(MeasureTheory.Lp.{0, 0} ℝ 2 MeasureTheory.MeasureSpace.volume.{0})),
  Continuous.{0, 0} fun w => (MeasureTheory.Lp.compMeasurePreserving.{0, 0, 0} (fun z => HSub.hSub.{0, 0, 0} z w) ⋯) f
```

## E1040-L2KERNEL - `Erdos1040.areaLogKernel`

For every compact planar set K and complex source w, areaLogKernel is the real L2 class for planar Lebesgue measure restricted to K represented by the totalized real logarithm of distance to w.

Module: `Erdos1040.LogContinuity`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.areaLogKernel : {K : Set.{0} ℂ} →
  IsCompact.{0} K →
    ℂ → ↥(MeasureTheory.Lp.{0, 0} ℝ 2 (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K))
```

## E1040-L2KERNEL - `Erdos1040.continuous_areaLogKernel`

For every compact planar set K, the map from an arbitrary complex source w to areaLogKernel K w is continuous in the L2 norm.

Module: `Erdos1040.LogContinuity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.continuous_areaLogKernel : ∀ {K : Set.{0} ℂ} (hK : IsCompact.{0} K),
  Continuous.{0, 0} (Erdos1040.areaLogKernel hK)
```

## E1040-ADJOINT-CONTINUITY - `Erdos1040.adjointAreaPotential`

For a compact planar set K and a real area-L2 density h on K, adjointAreaPotential at w is the real integral over K of h(z) times the totalized real logarithm of the distance from w to z.

Module: `Erdos1040.AdjointPotential`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.adjointAreaPotential : {K : Set.{0} ℂ} →
  IsCompact.{0} K →
    ↥(MeasureTheory.Lp.{0, 0} ℝ 2 (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K)) → ℂ → ℝ
```

## E1040-ADJOINT-CONTINUITY - `Erdos1040.integrable_adjointAreaPotential`

For every compact planar K, every real area-L2 density h on K, and every complex point w, the integrand h(z) log distance(w,z) is integrable for planar Lebesgue measure restricted to K.

Module: `Erdos1040.AdjointPotential`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integrable_adjointAreaPotential : ∀ {K : Set.{0} ℂ},
  IsCompact.{0} K →
    ∀ (h : ↥(MeasureTheory.Lp.{0, 0} ℝ 2 (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K)))
      (w : ℂ),
      MeasureTheory.Integrable.{0, 0}
        (fun z => HMul.hMul.{0, 0, 0} (↑↑h z) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} w z))))
        (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K)
```

## E1040-ADJOINT-CONTINUITY - `Erdos1040.adjointAreaPotential_eq_inner`

For every compact planar K, real area-L2 density h, and complex w, the actual adjoint area potential integral equals the real L2 inner product of h with areaLogKernel K w.

Module: `Erdos1040.AdjointPotential`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.adjointAreaPotential_eq_inner : ∀ {K : Set.{0} ℂ} (hK : IsCompact.{0} K)
  (h : ↥(MeasureTheory.Lp.{0, 0} ℝ 2 (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K)))
  (w : ℂ), Eq.{1} (Erdos1040.adjointAreaPotential hK h w) (Inner.inner.{0, 0} ℝ h (Erdos1040.areaLogKernel hK w))
```

## E1040-ADJOINT-CONTINUITY - `Erdos1040.continuous_adjointAreaPotential`

For every compact planar K and real area-L2 density h on K, the actual adjoint area potential is a continuous real-valued function on the entire complex plane.

Module: `Erdos1040.AdjointPotential`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.continuous_adjointAreaPotential : ∀ {K : Set.{0} ℂ} (hK : IsCompact.{0} K)
  (h : ↥(MeasureTheory.Lp.{0, 0} ℝ 2 (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K))),
  Continuous.{0, 0} (Erdos1040.adjointAreaPotential hK h)
```

## E1040-ADJOINT-CONTINUITY - `Erdos1040.adjointAreaPotential_zero_on_support_of_ae`

For every compact planar K, real area-L2 density h on K, and measure nu on the complex plane, if its adjoint area potential is zero nu-almost everywhere, it is zero at every point of the topological support of nu. The almost-everywhere vanishing is an explicit hypothesis, not established by this theorem.

Module: `Erdos1040.AdjointPotential`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.adjointAreaPotential_zero_on_support_of_ae : ∀ {K : Set.{0} ℂ} (hK : IsCompact.{0} K)
  (h : ↥(MeasureTheory.Lp.{0, 0} ℝ 2 (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K)))
  (ν : MeasureTheory.Measure.{0} ℂ),
  (Erdos1040.adjointAreaPotential hK h =ᵐ[ν] fun x => 0) →
    ∀ (w : ℂ),
      Membership.mem.{0, 0} (MeasureTheory.Measure.support.{0} ν) w → Eq.{1} (Erdos1040.adjointAreaPotential hK h w) 0
```

## E1040-ATOMIC-KERNEL - `Erdos1040.exists_sample_sequence_tendsto_integral`

For any probability measure on a measurable space and any measurable Bochner-integrable function into a real Banach space with its Borel measurable structure, there exists a sequence of source points whose equal-weight prefix means converge in norm to the function integral. The zero-length prefix is totalized; convergence concerns lengths tending to infinity.

Module: `Erdos1040.AtomicApproximation`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_sample_sequence_tendsto_integral.{u_1, u_2} : ∀ {α : Type u_1} {E : Type u_2}
  [inst : MeasurableSpace.{u_1} α] [inst_1 : NormedAddCommGroup.{u_2} E] [inst_2 : NormedSpace.{0, u_2} ℝ E]
  [CompleteSpace.{u_2} E] [inst_4 : MeasurableSpace.{u_2} E] [BorelSpace.{u_2} E] (μ : MeasureTheory.Measure.{u_1} α)
  [MeasureTheory.IsProbabilityMeasure.{u_1} μ] (k : α → E),
  Measurable.{u_1, u_2} k →
    MeasureTheory.Integrable.{u_2, u_1} k μ →
      ∃ points,
        Filter.Tendsto.{0, u_2}
          (fun n => HSMul.hSMul.{0, u_2, u_2} (Inv.inv.{0} ↑n) (∑ i ∈ Finset.range n, k (points i))) Filter.atTop.{0}
          (nhds.{u_2} (∫ (x : α), k x ∂μ))
```

## E1040-ATOMIC-KERNEL - `Erdos1040.exists_equal_weight_average`

For any probability measure on a measurable space and any measurable Bochner-integrable function into a real Banach space with its Borel measurable structure, every positive real tolerance admits a positive number of source points whose equal-weight function average differs from the integral by norm less than the tolerance.

Module: `Erdos1040.AtomicApproximation`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_equal_weight_average.{u_1, u_2} : ∀ {α : Type u_1} {E : Type u_2}
  [inst : MeasurableSpace.{u_1} α] [inst_1 : NormedAddCommGroup.{u_2} E] [inst_2 : NormedSpace.{0, u_2} ℝ E]
  [CompleteSpace.{u_2} E] [inst_4 : MeasurableSpace.{u_2} E] [BorelSpace.{u_2} E] (μ : MeasureTheory.Measure.{u_1} α)
  [MeasureTheory.IsProbabilityMeasure.{u_1} μ] (k : α → E),
  Measurable.{u_1, u_2} k →
    MeasureTheory.Integrable.{u_2, u_1} k μ →
      ∀ (ε : ℝ),
        LT.lt.{0} 0 ε →
          ∃ n,
            LT.lt.{0} 0 n ∧
              ∃ points,
                LT.lt.{0}
                  (Norm.norm.{u_2}
                    (HSub.hSub.{u_2, u_2, u_2} (HSMul.hSMul.{0, u_2, u_2} (Inv.inv.{0} ↑n) (∑ i, k (points i)))
                      (∫ (x : α), k x ∂μ)))
                  ε
```

## E1040-ATOMIC-KERNEL - `Erdos1040.exists_equal_weight_average_on_compact`

For every compact planar set S, every probability measure on the subtype S, every continuous function k from S to an arbitrary real Banach space, and every positive tolerance, there is a positive finite list of points in S whose equal-weight k-average differs from the integral by norm less than the tolerance. Points may repeat; no separability assumption is added.

Module: `Erdos1040.AtomicApproximation`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_equal_weight_average_on_compact.{u_2} : ∀ {E : Type u_2} [inst : NormedAddCommGroup.{u_2} E]
  [inst_1 : NormedSpace.{0, u_2} ℝ E] [CompleteSpace.{u_2} E] {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsProbabilityMeasure.{0} μ] (k : ↑S → E),
      Continuous.{0, u_2} k →
        ∀ (ε : ℝ),
          LT.lt.{0} 0 ε →
            ∃ n,
              LT.lt.{0} 0 n ∧
                ∃ points,
                  LT.lt.{0}
                    (Norm.norm.{u_2}
                      (HSub.hSub.{u_2, u_2, u_2} (HSMul.hSMul.{0, u_2, u_2} (Inv.inv.{0} ↑n) (∑ i, k (points i)))
                        (∫ (x : ↑S), k x ∂μ)))
                    ε
```

## E1040-ATOMIC-KERNEL - `Erdos1040.memLp_atomicLogPotential_of_isCompact`

For every finite complex root list and compact observation set K, the totalized atomic logarithmic potential belongs to real L2 for planar Lebesgue measure restricted to K. The empty-list potential is zero.

Module: `Erdos1040.DiscretePotential`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.memLp_atomicLogPotential_of_isCompact : ∀ {n : ℕ} (roots : Fin n → ℂ) {K : Set.{0} ℂ},
  IsCompact.{0} K →
    MeasureTheory.MemLp.{0, 0} (Erdos1040.atomicLogPotential roots) 2
      (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K)
```

## E1040-ATOMIC-KERNEL - `Erdos1040.areaLogKernel_average_ae_eq_atomicLogPotential`

For every finite complex root list and compact observation set K, the representative of the equal-weight average of its areaLogKernel L2 classes equals atomicLogPotential almost everywhere on K for restricted planar Lebesgue measure. Both empty-list averages are totalized to zero.

Module: `Erdos1040.DiscretePotential`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.areaLogKernel_average_ae_eq_atomicLogPotential : ∀ {n : ℕ} (roots : Fin n → ℂ) {K : Set.{0} ℂ}
  (hK : IsCompact.{0} K),
  ↑↑(HSMul.hSMul.{0, 0, 0} (Inv.inv.{0} ↑n)
          (∑ i,
            Erdos1040.areaLogKernel hK
              (roots i))) =ᵐ[MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K]
    Erdos1040.atomicLogPotential roots
```

## E1040-ATOMIC-KERNEL - `Erdos1040.atomicLogPotential_toLp_eq_average_areaLogKernel`

For every finite complex root list and compact observation set K, the L2 class of the actual totalized atomicLogPotential equals the equal-weight average of areaLogKernel classes, including the totalized empty-list case.

Module: `Erdos1040.DiscretePotential`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.atomicLogPotential_toLp_eq_average_areaLogKernel : ∀ {n : ℕ} (roots : Fin n → ℂ) {K : Set.{0} ℂ}
  (hK : IsCompact.{0} K),
  Eq.{1} (MeasureTheory.MemLp.toLp.{0, 0} (Erdos1040.atomicLogPotential roots) ⋯)
    (HSMul.hSMul.{0, 0, 0} (Inv.inv.{0} ↑n) (∑ i, Erdos1040.areaLogKernel hK (roots i)))
```

## E1040-ATOMIC-KERNEL - `Erdos1040.integrable_areaLogKernel_on_compact`

For compact planar source and observation sets S and K and a probability on subtype S, the map from a source to its areaLogKernel class on K is Bochner integrable.

Module: `Erdos1040.DiscretePotential`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integrable_areaLogKernel_on_compact : ∀ {S K : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (hK : IsCompact.{0} K) (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsProbabilityMeasure.{0} μ],
      MeasureTheory.Integrable.{0, 0} (fun w => Erdos1040.areaLogKernel hK ↑w) μ
```

## E1040-ATOMIC-KERNEL - `Erdos1040.exists_roots_approx_areaLogKernel_integral`

For compact planar source and observation sets S and K, a probability on subtype S, and every positive tolerance, there is a positive finite number of complex roots all in S such that the L2 class of their actual atomicLogPotential differs in norm from the Bochner integral of areaLogKernel by less than the tolerance. No pointwise arbitrary-measure potential identity is asserted.

Module: `Erdos1040.DiscretePotential`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_roots_approx_areaLogKernel_integral : ∀ {S K : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (hK : IsCompact.{0} K) (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsProbabilityMeasure.{0} μ] (ε : ℝ),
      LT.lt.{0} 0 ε →
        ∃ n,
          LT.lt.{0} 0 n ∧
            ∃ roots,
              (∀ (i : Fin n), Membership.mem.{0, 0} S (roots i)) ∧
                LT.lt.{0}
                  (Norm.norm.{0}
                    (HSub.hSub.{0, 0, 0} (MeasureTheory.MemLp.toLp.{0, 0} (Erdos1040.atomicLogPotential roots) ⋯)
                      (∫ (w : ↑S), Erdos1040.areaLogKernel hK ↑w ∂μ)))
                  ε
```

## E1040-ATOMIC-KERNEL - `Erdos1040.exteriorLogKernel`

For disjoint planar source and observation sets S and E, exteriorLogKernel sends a source w in S to the continuous real function on E given by log distance(z,w). No compactness is required for this definition.

Module: `Erdos1040.ExteriorKernel`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.exteriorLogKernel : {S E : Set.{0} ℂ} → Disjoint.{0} S E → ↑S → ContinuousMap.{0, 0} ↑E ℝ
```

## E1040-ATOMIC-KERNEL - `Erdos1040.continuous_exteriorLogKernel`

For disjoint planar S and E, the source-to-exteriorLogKernel map is continuous for the compact-open topology on continuous functions, without assuming compactness.

Module: `Erdos1040.ExteriorKernel`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.continuous_exteriorLogKernel : ∀ {S E : Set.{0} ℂ} (hSE : Disjoint.{0} S E),
  Continuous.{0, 0} (Erdos1040.exteriorLogKernel hSE)
```

## E1040-ATOMIC-KERNEL - `Erdos1040.integrable_exteriorLogKernel_on_compact`

For compact planar S and compact observation subtype E disjoint from S, and a probability on S, the exteriorLogKernel is Bochner integrable in the continuous-function Banach space with its uniform norm. Compactness of E is an explicit CompactSpace typeclass binder.

Module: `Erdos1040.ExteriorKernel`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integrable_exteriorLogKernel_on_compact : ∀ {S E : Set.{0} ℂ} [inst : CompactSpace.{0} ↑E],
  IsCompact.{0} S →
    ∀ (hSE : Disjoint.{0} S E) (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsProbabilityMeasure.{0} μ],
      MeasureTheory.Integrable.{0, 0} (Erdos1040.exteriorLogKernel hSE) μ
```

## E1040-ATOMIC-KERNEL - `Erdos1040.exteriorLogKernel_integral_apply`

For compact planar S and compact observation subtype E disjoint from S and a probability on S, evaluating the continuous-function integral of exteriorLogKernel at any z in E equals the actual scalar source integral of log distance(z,w).

Module: `Erdos1040.ExteriorKernel`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exteriorLogKernel_integral_apply : ∀ {S E : Set.{0} ℂ} [inst : CompactSpace.{0} ↑E],
  IsCompact.{0} S →
    ∀ (hSE : Disjoint.{0} S E) (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsProbabilityMeasure.{0} μ] (z : ↑E),
      Eq.{1} ((∫ (w : ↑S), Erdos1040.exteriorLogKernel hSE w ∂μ) z)
        (∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} ↑z ↑w)) ∂μ)
```

## E1040-ATOMIC-KERNEL - `Erdos1040.exists_roots_approx_area_and_exterior_integrals`

For compact planar source S, compact planar area observation K, compact exterior observation subtype E disjoint from S, a probability on S, and two positive tolerances, one positive finite list of source points in S simultaneously approximates the areaLogKernel Bochner integral in L2 norm and the exteriorLogKernel Bochner integral in uniform norm by their equal-weight averages.

Module: `Erdos1040.ExteriorKernel`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_roots_approx_area_and_exterior_integrals : ∀ {S K E : Set.{0} ℂ} [inst : CompactSpace.{0} ↑E],
  IsCompact.{0} S →
    ∀ (hK : IsCompact.{0} K) (hSE : Disjoint.{0} S E) (μ : MeasureTheory.Measure.{0} ↑S)
      [MeasureTheory.IsProbabilityMeasure.{0} μ] (εA εE : ℝ),
      LT.lt.{0} 0 εA →
        LT.lt.{0} 0 εE →
          ∃ n,
            LT.lt.{0} 0 n ∧
              ∃ points,
                LT.lt.{0}
                    (Norm.norm.{0}
                      (HSub.hSub.{0, 0, 0}
                        (HSMul.hSMul.{0, 0, 0} (Inv.inv.{0} ↑n) (∑ i, Erdos1040.areaLogKernel hK ↑(points i)))
                        (∫ (w : ↑S), Erdos1040.areaLogKernel hK ↑w ∂μ)))
                    εA ∧
                  LT.lt.{0}
                    (Norm.norm.{0}
                      (HSub.hSub.{0, 0, 0}
                        (HSMul.hSMul.{0, 0, 0} (Inv.inv.{0} ↑n) (∑ i, Erdos1040.exteriorLogKernel hSE (points i)))
                        (∫ (w : ↑S), Erdos1040.exteriorLogKernel hSE w ∂μ)))
                    εE
```

## E1040-ATOMIC-KERNEL - `Erdos1040.exists_roots_approx_area_and_exterior_potentials`

For compact planar source S, compact area observation K, compact exterior observation subtype E disjoint from S, a probability on S, and two positive tolerances, one positive finite list of points in S approximates the areaLogKernel Bochner integral in L2 norm, while its actual atomicLogPotential approximates the scalar source log-distance integral uniformly at every z in E. The compact observation subtype has an explicit CompactSpace binder; no capacity condition is assumed.

Module: `Erdos1040.ExteriorKernel`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_roots_approx_area_and_exterior_potentials : ∀ {S K E : Set.{0} ℂ} [CompactSpace.{0} ↑E],
  IsCompact.{0} S →
    ∀ (hK : IsCompact.{0} K),
      Disjoint.{0} S E →
        ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsProbabilityMeasure.{0} μ] (εA εE : ℝ),
          LT.lt.{0} 0 εA →
            LT.lt.{0} 0 εE →
              ∃ n,
                LT.lt.{0} 0 n ∧
                  ∃ points,
                    LT.lt.{0}
                        (Norm.norm.{0}
                          (HSub.hSub.{0, 0, 0}
                            (HSMul.hSMul.{0, 0, 0} (Inv.inv.{0} ↑n) (∑ i, Erdos1040.areaLogKernel hK ↑(points i)))
                            (∫ (w : ↑S), Erdos1040.areaLogKernel hK ↑w ∂μ)))
                        εA ∧
                      ∀ (z : ↑E),
                        LT.lt.{0}
                          (abs.{0}
                            (HSub.hSub.{0, 0, 0} (Erdos1040.atomicLogPotential (fun i => ↑(points i)) ↑z)
                              (∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} ↑z ↑w)) ∂μ)))
                          εE
```

## E1040-CIRCLE-MEAN - `Erdos1040.exists_bound_log_norm_circleMap_sub`

For a compact planar source set strictly inside a circle of positive radius centered at zero, the absolute value of the logarithmic distance from any point on that circle to any source has a uniform finite nonnegative bound.

Module: `Erdos1040.CircleMean`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_bound_log_norm_circleMap_sub : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ {R : ℝ},
      LT.lt.{0} 0 R →
        (∀ (w : ℂ), Membership.mem.{0, 0} S w → LT.lt.{0} (Norm.norm.{0} w) R) →
          ∃ C,
            LE.le.{0} 0 C ∧
              ∀ (θ : ℝ) (w : ↑S),
                LE.le.{0} (Norm.norm.{0} (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} (circleMap 0 R θ) ↑w)))) C
```

## E1040-CIRCLE-MEAN - `Erdos1040.integrable_log_density_at_circleMap`

For a compact planar source set strictly inside a positive-radius circle, a finite measure on the source subtype, and an integrable real density, the actual density times log-distance source integrand is integrable at every point of that circle.

Module: `Erdos1040.CircleMean`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integrable_log_density_at_circleMap : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ {R : ℝ},
      LT.lt.{0} 0 R →
        (∀ (w : ℂ), Membership.mem.{0, 0} S w → LT.lt.{0} (Norm.norm.{0} w) R) →
          ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsFiniteMeasure.{0} μ] (f : ↑S → ℝ),
            MeasureTheory.Integrable.{0, 0} f μ →
              ∀ (θ : ℝ),
                MeasureTheory.Integrable.{0, 0}
                  (fun w =>
                    HMul.hMul.{0, 0, 0} (f w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} (circleMap 0 R θ) ↑w))))
                  μ
```

## E1040-CIRCLE-MEAN - `Erdos1040.integrable_circle_log_density_prod`

Under compact strictly enclosed planar sources, a finite source measure and integrable real density, the density times circle-source logarithmic kernel is integrable for the product of angular Lebesgue measure restricted to the unordered interval from 0 to 2 pi and the source measure.

Module: `Erdos1040.CircleMean`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integrable_circle_log_density_prod : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ {R : ℝ},
      LT.lt.{0} 0 R →
        (∀ (w : ℂ), Membership.mem.{0, 0} S w → LT.lt.{0} (Norm.norm.{0} w) R) →
          ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsFiniteMeasure.{0} μ] (f : ↑S → ℝ),
            MeasureTheory.Integrable.{0, 0} f μ →
              MeasureTheory.Integrable.{0, 0}
                (fun p =>
                  HMul.hMul.{0, 0, 0} (f p.2) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} (circleMap 0 R p.1) ↑p.2))))
                (MeasureTheory.Measure.prod.{0, 0}
                  (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0}
                    (Set.uIoc.{0} 0 (HMul.hMul.{0, 0, 0} 2 Real.pi)))
                  μ)
```

## E1040-CIRCLE-MEAN - `Erdos1040.circleIntegrable_log_density_potential`

For compact strictly enclosed planar sources, a finite source measure and integrable real density, the actual scalar density-weighted source potential is circle-integrable on the given positive-radius circle.

Module: `Erdos1040.CircleMean`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.circleIntegrable_log_density_potential : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ {R : ℝ},
      LT.lt.{0} 0 R →
        (∀ (w : ℂ), Membership.mem.{0, 0} S w → LT.lt.{0} (Norm.norm.{0} w) R) →
          ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsFiniteMeasure.{0} μ] (f : ↑S → ℝ),
            MeasureTheory.Integrable.{0, 0} f μ →
              CircleIntegrable.{0}
                (fun z =>
                  ∫ (w : ↑S), HMul.hMul.{0, 0, 0} (f w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ∂μ)
                0 R
```

## E1040-CIRCLE-MEAN - `Erdos1040.circleAverage_log_density_potential`

For compact planar sources strictly inside the positive-radius circle centered at zero, a finite source measure and integrable real density, the normalized circle average of the actual density-weighted logarithmic source potential equals the integral of the density times the logarithm of the radius.

Module: `Erdos1040.CircleMean`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.circleAverage_log_density_potential : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ {R : ℝ},
      LT.lt.{0} 0 R →
        (∀ (w : ℂ), Membership.mem.{0, 0} S w → LT.lt.{0} (Norm.norm.{0} w) R) →
          ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsFiniteMeasure.{0} μ] (f : ↑S → ℝ),
            MeasureTheory.Integrable.{0, 0} f μ →
              Eq.{1}
                (Real.circleAverage.{0}
                  (fun z =>
                    ∫ (w : ↑S), HMul.hMul.{0, 0, 0} (f w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ∂μ)
                  0 R)
                (HMul.hMul.{0, 0, 0} (∫ (w : ↑S), f w ∂μ) (Real.log R))
```

## E1040-CIRCLE-MEAN - `Erdos1040.circleAverage_log_density_potential_zero_of_integral_zero`

Under compact strictly enclosed planar sources, finite source measure and integrable real density with integral zero, the normalized circle average of the actual density-weighted logarithmic source potential is zero.

Module: `Erdos1040.CircleMean`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.circleAverage_log_density_potential_zero_of_integral_zero : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ {R : ℝ},
      LT.lt.{0} 0 R →
        (∀ (w : ℂ), Membership.mem.{0, 0} S w → LT.lt.{0} (Norm.norm.{0} w) R) →
          ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsFiniteMeasure.{0} μ] (f : ↑S → ℝ),
            MeasureTheory.Integrable.{0, 0} f μ →
              Eq.{1} (∫ (w : ↑S), f w ∂μ) 0 →
                Eq.{1}
                  (Real.circleAverage.{0}
                    (fun z =>
                      ∫ (w : ↑S), HMul.hMul.{0, 0, 0} (f w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ∂μ)
                    0 R)
                  0
```

## E1040-ATOMIC-KERNEL - `Erdos1040.exists_roots_simultaneous_potential_approximation`

For compact planar source S and observation K, compact exterior observation subtype E disjoint from S, a probability on S, and positive area and exterior tolerances, there is one positive finite list of complex roots all in S whose actual atomicLogPotential class approximates the Bochner area-L2 potential integral and whose actual atomicLogPotential values uniformly approximate the scalar source log-distance integral at every point of E. The exact same roots meet both strict error bounds.

Module: `Erdos1040.SimultaneousApproximation`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_roots_simultaneous_potential_approximation : ∀ {S K E : Set.{0} ℂ} [CompactSpace.{0} ↑E],
  IsCompact.{0} S →
    ∀ (hK : IsCompact.{0} K),
      Disjoint.{0} S E →
        ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsProbabilityMeasure.{0} μ] (εA εE : ℝ),
          LT.lt.{0} 0 εA →
            LT.lt.{0} 0 εE →
              ∃ n,
                LT.lt.{0} 0 n ∧
                  ∃ roots,
                    (∀ (i : Fin n), Membership.mem.{0, 0} S (roots i)) ∧
                      LT.lt.{0}
                          (Norm.norm.{0}
                            (HSub.hSub.{0, 0, 0}
                              (MeasureTheory.MemLp.toLp.{0, 0} (Erdos1040.atomicLogPotential roots) ⋯)
                              (∫ (w : ↑S), Erdos1040.areaLogKernel hK ↑w ∂μ)))
                          εA ∧
                        ∀ (z : ↑E),
                          LT.lt.{0}
                            (abs.{0}
                              (HSub.hSub.{0, 0, 0} (Erdos1040.atomicLogPotential roots ↑z)
                                (∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} ↑z ↑w)) ∂μ)))
                            εE
```

## E1040-CIRCLE-MEAN - `Erdos1040.circleAverage_adjointAreaPotential`

For every real area-L2 density h on a compact planar set K and every positive-radius circle centered at zero that strictly encloses K, the normalized circle mean of the actual adjointAreaPotential equals its restricted-area total mass times the logarithm of the radius. No equilibrium or capacity condition is assumed.

Module: `Erdos1040.AdjointCircleMean`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.circleAverage_adjointAreaPotential : ∀ {K : Set.{0} ℂ} (hK : IsCompact.{0} K)
  (h : ↥(MeasureTheory.Lp.{0, 0} ℝ 2 (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K)))
  {R : ℝ},
  LT.lt.{0} 0 R →
    (∀ (z : ℂ), Membership.mem.{0, 0} K z → LT.lt.{0} (Norm.norm.{0} z) R) →
      Eq.{1} (Real.circleAverage.{0} (Erdos1040.adjointAreaPotential hK h) 0 R)
        (HMul.hMul.{0, 0, 0} (∫ (z : ℂ) in K, ↑↑h z) (Real.log R))
```

## E1040-SOURCE-POTENTIAL - `Erdos1040.integral_sq_log_norm_sub_eq_norm_areaLogKernel_sq`

For every compact planar observation set K and every complex source w, the restricted-area integral of the square of the totalized logarithmic distance equals the squared real L2 norm of areaLogKernel K w.

Module: `Erdos1040.SourcePotential`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integral_sq_log_norm_sub_eq_norm_areaLogKernel_sq : ∀ {K : Set.{0} ℂ} (hK : IsCompact.{0} K) (w : ℂ),
  Eq.{1} (∫ (z : ℂ) in K, HPow.hPow.{0, 0, 0} (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z w))) 2)
    (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (Erdos1040.areaLogKernel hK w)) 2)
```

## E1040-SOURCE-POTENTIAL - `Erdos1040.integrable_log_norm_sub_prod`

For any compact planar source and observation sets S and K and any finite measure on subtype S, the actual totalized logarithmic distance kernel is absolutely integrable for the product of that source measure and planar Lebesgue measure restricted to K.

Module: `Erdos1040.SourcePotential`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integrable_log_norm_sub_prod : ∀ {S K : Set.{0} ℂ},
  IsCompact.{0} S →
    IsCompact.{0} K →
      ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsFiniteMeasure.{0} μ],
        MeasureTheory.Integrable.{0, 0} (fun p => Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} p.2 ↑p.1)))
          (MeasureTheory.Measure.prod.{0, 0} μ
            (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K))
```

## E1040-HARMONIC-MAX - `Erdos1040.harmonic_eventually_eq_of_isLocalMax`

A real-valued function harmonic in a neighborhood of a complex point and attaining a local maximum there is equal to that value throughout some neighborhood of the point. The proof uses only a local harmonic conjugate on a disk, not a global conjugate.

Module: `Erdos1040.HarmonicMaximum`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.harmonic_eventually_eq_of_isLocalMax : ∀ {f : ℂ → ℝ} {c : ℂ},
  InnerProductSpace.HarmonicAt.{0, 0} f c → IsLocalMax.{0, 0} f c → ∀ᶠ (z : ℂ) in nhds.{0} c, Eq.{1} (f z) (f c)
```

## E1040-HARMONIC-MAX - `Erdos1040.harmonic_eqOn_of_isPreconnected_of_isMaxOn`

For every open preconnected subset U of the complex plane and every real-valued function harmonic at every point of U, if its maximum on U is attained at a point c in U, then the function equals its value at c everywhere on U. No simply connected or boundary regularity hypothesis is imposed.

Module: `Erdos1040.HarmonicMaximum`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.harmonic_eqOn_of_isPreconnected_of_isMaxOn : ∀ {f : ℂ → ℝ} {U : Set.{0} ℂ} {c : ℂ},
  IsPreconnected.{0} U →
    IsOpen.{0} U →
      InnerProductSpace.HarmonicOnNhd.{0, 0} f U →
        Membership.mem.{0, 0} U c → IsMaxOn.{0, 0} f U c → Set.EqOn.{0, 0} f (fun x => f c) U
```

## E1040-SOURCE-POTENTIAL - `Erdos1040.areaLogKernel_integral_ae_eq_source_potential`

For compact planar source and observation sets S and K and any finite measure on subtype S, the representative of the Bochner integral of areaLogKernel equals the actual totalized logarithmic source integral almost everywhere for planar Lebesgue measure restricted to K.

Module: `Erdos1040.SourcePotential`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.areaLogKernel_integral_ae_eq_source_potential : ∀ {S K : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (hK : IsCompact.{0} K) (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsFiniteMeasure.{0} μ],
      ↑↑(∫ (w : ↑S),
              Erdos1040.areaLogKernel hK
                ↑w ∂μ) =ᵐ[MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K]
        fun z => ∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)) ∂μ
```

## E1040-SOURCE-POTENTIAL - `Erdos1040.memLp_source_potential`

For compact planar source and observation sets S and K and any finite measure on subtype S, the actual totalized logarithmic source integral belongs to real L2 for planar Lebesgue measure restricted to K.

Module: `Erdos1040.SourcePotential`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.memLp_source_potential : ∀ {S K : Set.{0} ℂ},
  IsCompact.{0} S →
    IsCompact.{0} K →
      ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsFiniteMeasure.{0} μ],
        MeasureTheory.MemLp.{0, 0} (fun z => ∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)) ∂μ) 2
          (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K)
```

## E1040-SOURCE-POTENTIAL - `Erdos1040.source_potential_toLp_eq_integral_areaLogKernel`

For compact planar source and observation sets S and K and any finite measure on subtype S, the L2 class of the actual totalized logarithmic source integral equals the Bochner integral of areaLogKernel.

Module: `Erdos1040.SourcePotential`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.source_potential_toLp_eq_integral_areaLogKernel : ∀ {S K : Set.{0} ℂ} (hS : IsCompact.{0} S)
  (hK : IsCompact.{0} K) (μ : MeasureTheory.Measure.{0} ↑S) [inst : MeasureTheory.IsFiniteMeasure.{0} μ],
  Eq.{1}
    (MeasureTheory.MemLp.toLp.{0, 0} (fun z => ∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)) ∂μ) ⋯)
    (∫ (w : ↑S), Erdos1040.areaLogKernel hK ↑w ∂μ)
```

## E1040-POTENTIAL-ASYMPTOTICS - `Erdos1040.abs_log_norm_sub_sub_log_norm_le`

For complex observation z and source w, if the norm of z is positive and at least twice the norm of w, the absolute difference between log norm(z-w) and log norm(z) is at most twice norm(w) divided by norm(z).

Module: `Erdos1040.PotentialAsymptotics`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.abs_log_norm_sub_sub_log_norm_le : ∀ {z w : ℂ},
  LT.lt.{0} 0 (Norm.norm.{0} z) →
    LE.le.{0} (HMul.hMul.{0, 0, 0} 2 (Norm.norm.{0} w)) (Norm.norm.{0} z) →
      LE.le.{0}
        (abs.{0}
          (HSub.hSub.{0, 0, 0} (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z w))) (Real.log (Norm.norm.{0} z))))
        (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 (Norm.norm.{0} w)) (Norm.norm.{0} z))
```

## E1040-POTENTIAL-ASYMPTOTICS - `Erdos1040.integrable_log_density_potential_of_norm_lt`

For a complex source subtype S with all source norms at most a nonnegative M, any measure mu on S and a real mu-integrable density f, the actual logarithmic source integrand f(w) log norm(z-w) is integrable whenever norm(z) is greater than 2M. Finiteness of mu itself is not required; integrability of the density supplies finite absolute mass.

Module: `Erdos1040.PotentialAsymptotics`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integrable_log_density_potential_of_norm_lt : ∀ {S : Set.{0} ℂ} {M : ℝ},
  LE.le.{0} 0 M →
    (∀ (w : ↑S), LE.le.{0} (Norm.norm.{0} ↑w) M) →
      ∀ (μ : MeasureTheory.Measure.{0} ↑S) (f : ↑S → ℝ),
        MeasureTheory.Integrable.{0, 0} f μ →
          ∀ {z : ℂ},
            LT.lt.{0} (HMul.hMul.{0, 0, 0} 2 M) (Norm.norm.{0} z) →
              MeasureTheory.Integrable.{0, 0}
                (fun w => HMul.hMul.{0, 0, 0} (f w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)))) μ
```

## E1040-POTENTIAL-ASYMPTOTICS - `Erdos1040.abs_log_density_potential_sub_mass_log_le`

For a complex source subtype S whose norms are at most a nonnegative M, any measure mu on S, and a real mu-integrable density f, the absolute difference between the actual logarithmic source potential at z and the integral of f times log norm(z) is at most (2M/norm(z)) times the integral of abs(f), whenever norm(z) is greater than 2M. Finiteness of mu itself is not required.

Module: `Erdos1040.PotentialAsymptotics`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.abs_log_density_potential_sub_mass_log_le : ∀ {S : Set.{0} ℂ} {M : ℝ},
  LE.le.{0} 0 M →
    (∀ (w : ↑S), LE.le.{0} (Norm.norm.{0} ↑w) M) →
      ∀ (μ : MeasureTheory.Measure.{0} ↑S) (f : ↑S → ℝ),
        MeasureTheory.Integrable.{0, 0} f μ →
          ∀ {z : ℂ},
            LT.lt.{0} (HMul.hMul.{0, 0, 0} 2 M) (Norm.norm.{0} z) →
              LE.le.{0}
                (abs.{0}
                  (HSub.hSub.{0, 0, 0}
                    (∫ (w : ↑S), HMul.hMul.{0, 0, 0} (f w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ∂μ)
                    (HMul.hMul.{0, 0, 0} (∫ (w : ↑S), f w ∂μ) (Real.log (Norm.norm.{0} z)))))
                (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 M) (Norm.norm.{0} z))
                  (∫ (w : ↑S), abs.{0} (f w) ∂μ))
```

## E1040-POTENTIAL-ASYMPTOTICS - `Erdos1040.tendsto_log_density_potential_sub_mass_log`

For every compact complex source set S, any measure mu on the subtype S, and real mu-integrable density f, the actual logarithmic source potential minus its total real mass times log norm(z) tends to zero as z leaves every compact subset of the complex plane, equivalently as norm(z) tends to infinity. Finiteness of mu itself is not required.

Module: `Erdos1040.PotentialAsymptotics`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.tendsto_log_density_potential_sub_mass_log : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (μ : MeasureTheory.Measure.{0} ↑S) (f : ↑S → ℝ),
      MeasureTheory.Integrable.{0, 0} f μ →
        Filter.Tendsto.{0, 0}
          (fun z =>
            HSub.hSub.{0, 0, 0}
              (∫ (w : ↑S), HMul.hMul.{0, 0, 0} (f w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ∂μ)
              (HMul.hMul.{0, 0, 0} (∫ (w : ↑S), f w ∂μ) (Real.log (Norm.norm.{0} z))))
          (Filter.cocompact.{0} ℂ) (nhds.{0} 0)
```

## E1040-POTENTIAL-ASYMPTOTICS - `Erdos1040.tendsto_log_density_potential_of_integral_zero`

For every compact complex source set S, any measure mu on the subtype S, and real mu-integrable density f whose integral is zero, the actual logarithmic source potential tends to zero as z leaves every compact subset of the complex plane, equivalently as norm(z) tends to infinity. Finiteness of mu itself is not required.

Module: `Erdos1040.PotentialAsymptotics`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.tendsto_log_density_potential_of_integral_zero : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (μ : MeasureTheory.Measure.{0} ↑S) (f : ↑S → ℝ),
      MeasureTheory.Integrable.{0, 0} f μ →
        Eq.{1} (∫ (w : ↑S), f w ∂μ) 0 →
          Filter.Tendsto.{0, 0}
            (fun z => ∫ (w : ↑S), HMul.hMul.{0, 0, 0} (f w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ∂μ)
            (Filter.cocompact.{0} ℂ) (nhds.{0} 0)
```

## E1040-HARMONIC-MAX - `Erdos1040.harmonic_nonpos_of_continuous_majorant`

For every open preconnected unbounded subset U of the complex plane, every real-valued function f harmonic at every point of U, and every globally continuous real-valued majorant g, if g vanishes on the entire frontier of U, f is at most g on U, and f tends to zero along the cocompact filter at infinity, then f is nonpositive everywhere on U. No boundary continuity of f and no regularity of the boundary are assumed.

Module: `Erdos1040.HarmonicMaximum`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.harmonic_nonpos_of_continuous_majorant : ∀ {f g : ℂ → ℝ} {U : Set.{0} ℂ},
  IsPreconnected.{0} U →
    IsOpen.{0} U →
      ¬Bornology.IsBounded.{0} U →
        InnerProductSpace.HarmonicOnNhd.{0, 0} f U →
          Continuous.{0, 0} g →
            (∀ (x : ℂ), Membership.mem.{0, 0} (frontier.{0} U) x → Eq.{1} (g x) 0) →
              (∀ (x : ℂ), Membership.mem.{0, 0} U x → LE.le.{0} (f x) (g x)) →
                Filter.Tendsto.{0, 0} f (Filter.cocompact.{0} ℂ) (nhds.{0} 0) →
                  ∀ (x : ℂ), Membership.mem.{0, 0} U x → LE.le.{0} (f x) 0
```

## E1040-HARMONIC-MAX - `Erdos1040.harmonic_eq_zero_of_nonpos_of_circleAverage_zero`

For every open preconnected subset U of the complex plane and every real-valued function f harmonic and nonpositive on U, if a circle of positive radius lies in U and the actual circle mean of f on that circle equals zero, then f vanishes everywhere on U. The circle mean is integrable because f is continuous on the circle.

Module: `Erdos1040.HarmonicMaximum`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.harmonic_eq_zero_of_nonpos_of_circleAverage_zero : ∀ {f : ℂ → ℝ} {U : Set.{0} ℂ} {c : ℂ} {R : ℝ},
  IsPreconnected.{0} U →
    IsOpen.{0} U →
      InnerProductSpace.HarmonicOnNhd.{0, 0} f U →
        (∀ (z : ℂ), Membership.mem.{0, 0} U z → LE.le.{0} (f z) 0) →
          LT.lt.{0} 0 R →
            Metric.sphere.{0} c R ⊆ U → Eq.{1} (Real.circleAverage.{0} f c R) 0 → Set.EqOn.{0, 0} f (fun x => 0) U
```

## E1040-SOURCE-DENSITY - `Erdos1040.integrable_areaLogKernel_density`

For compact planar source and observation sets S and K, a finite measure mu on subtype S, and a measurable real density f with a pointwise finite norm bound C, the density times areaLogKernel is Bochner integrable in the real area-L2 space.

Module: `Erdos1040.SourceDensity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integrable_areaLogKernel_density : ∀ {S K : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (hK : IsCompact.{0} K) (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsFiniteMeasure.{0} μ] (f : ↑S → ℝ),
      Measurable.{0, 0} f →
        ∀ (C : ℝ),
          (∀ (w : ↑S), LE.le.{0} (Norm.norm.{0} (f w)) C) →
            MeasureTheory.Integrable.{0, 0} (fun w => HSMul.hSMul.{0, 0, 0} (f w) (Erdos1040.areaLogKernel hK ↑w)) μ
```

## E1040-SOURCE-DENSITY - `Erdos1040.integrable_log_density_prod`

For compact planar source and observation sets S and K, a finite measure mu on subtype S, and a measurable real density f with a pointwise finite norm bound C, the actual signed logarithmic source kernel f(w) log norm(z-w) is absolutely integrable for the source-times-restricted-area product measure.

Module: `Erdos1040.SourceDensity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integrable_log_density_prod : ∀ {S K : Set.{0} ℂ},
  IsCompact.{0} S →
    IsCompact.{0} K →
      ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsFiniteMeasure.{0} μ] (f : ↑S → ℝ),
        Measurable.{0, 0} f →
          ∀ (C : ℝ),
            (∀ (w : ↑S), LE.le.{0} (Norm.norm.{0} (f w)) C) →
              MeasureTheory.Integrable.{0, 0}
                (fun p => HMul.hMul.{0, 0, 0} (f p.1) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} p.2 ↑p.1))))
                (MeasureTheory.Measure.prod.{0, 0} μ
                  (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K))
```

## E1040-SOURCE-DENSITY - `Erdos1040.areaLogKernel_density_integral_ae_eq_source_potential`

For compact planar source and observation sets S and K, a finite measure mu on subtype S, and a measurable real density f with a pointwise finite norm bound C, the Bochner integral of f times areaLogKernel is represented area-almost everywhere on K by the actual signed logarithmic source integral.

Module: `Erdos1040.SourceDensity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.areaLogKernel_density_integral_ae_eq_source_potential : ∀ {S K : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (hK : IsCompact.{0} K) (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsFiniteMeasure.{0} μ] (f : ↑S → ℝ),
      Measurable.{0, 0} f →
        ∀ (C : ℝ),
          (∀ (w : ↑S), LE.le.{0} (Norm.norm.{0} (f w)) C) →
            ↑↑(∫ (w : ↑S),
                    HSMul.hSMul.{0, 0, 0} (f w)
                      (Erdos1040.areaLogKernel hK
                        ↑w) ∂μ) =ᵐ[MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K]
              fun z => ∫ (w : ↑S), HMul.hMul.{0, 0, 0} (f w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ∂μ
```

## E1040-SOURCE-DENSITY - `Erdos1040.memLp_source_density_potential`

For compact planar source and observation sets S and K, a finite measure mu on subtype S, and a measurable real density f with a pointwise finite norm bound C, the actual signed logarithmic source potential belongs to real L2 for restricted planar Lebesgue measure on K.

Module: `Erdos1040.SourceDensity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.memLp_source_density_potential : ∀ {S K : Set.{0} ℂ},
  IsCompact.{0} S →
    IsCompact.{0} K →
      ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsFiniteMeasure.{0} μ] (f : ↑S → ℝ),
        Measurable.{0, 0} f →
          ∀ (C : ℝ),
            (∀ (w : ↑S), LE.le.{0} (Norm.norm.{0} (f w)) C) →
              MeasureTheory.MemLp.{0, 0}
                (fun z =>
                  ∫ (w : ↑S), HMul.hMul.{0, 0, 0} (f w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ∂μ)
                2 (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K)
```

## E1040-SOURCE-DENSITY - `Erdos1040.source_density_potential_toLp_eq_integral_areaLogKernel`

For compact planar source and observation sets S and K, a finite measure mu on subtype S, and a measurable real density f with a pointwise finite norm bound C, the L2 class of the actual signed logarithmic source potential equals the Bochner integral of f times areaLogKernel.

Module: `Erdos1040.SourceDensity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.source_density_potential_toLp_eq_integral_areaLogKernel : ∀ {S K : Set.{0} ℂ} (hS : IsCompact.{0} S)
  (hK : IsCompact.{0} K) (μ : MeasureTheory.Measure.{0} ↑S) [inst : MeasureTheory.IsFiniteMeasure.{0} μ] (f : ↑S → ℝ)
  (hf : Measurable.{0, 0} f) (C : ℝ) (hfC : ∀ (w : ↑S), LE.le.{0} (Norm.norm.{0} (f w)) C),
  Eq.{1}
    (MeasureTheory.MemLp.toLp.{0, 0}
      (fun z => ∫ (w : ↑S), HMul.hMul.{0, 0, 0} (f w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ∂μ) ⋯)
    (∫ (w : ↑S), HSMul.hSMul.{0, 0, 0} (f w) (Erdos1040.areaLogKernel hK ↑w) ∂μ)
```

## E1040-SOURCE-DENSITY - `Erdos1040.inner_integral_areaLogKernel_density`

For compact planar source and observation sets S and K, a finite measure mu on subtype S, and a measurable real density f with a pointwise finite norm bound C, pairing any real area-L2 density h with the Bochner source potential equals the source integral of f times the actual adjointAreaPotential of h.

Module: `Erdos1040.SourceDensity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.inner_integral_areaLogKernel_density : ∀ {S K : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (hK : IsCompact.{0} K) (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsFiniteMeasure.{0} μ] (f : ↑S → ℝ),
      Measurable.{0, 0} f →
        ∀ (C : ℝ),
          (∀ (w : ↑S), LE.le.{0} (Norm.norm.{0} (f w)) C) →
            ∀
              (h :
                ↥(MeasureTheory.Lp.{0, 0} ℝ 2
                    (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K))),
              Eq.{1}
                (Inner.inner.{0, 0} ℝ h (∫ (w : ↑S), HSMul.hSMul.{0, 0, 0} (f w) (Erdos1040.areaLogKernel hK ↑w) ∂μ))
                (∫ (w : ↑S), HMul.hMul.{0, 0, 0} (f w) (Erdos1040.adjointAreaPotential hK h ↑w) ∂μ)
```

## E1040-CAP-SEPARATOR - `Erdos1040.capSet`

For real M and a, capSet M a is the set of complex z with norm z at most M and absolute imaginary part at least a.

Module: `Erdos1040.CapPolynomial`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.capSet : ℝ → ℝ → Set.{0} ℂ
```

## E1040-CAP-SEPARATOR - `Erdos1040.isCompact_capSet`

For every pair of real M and a, the two-cap set capSet M a is compact, including empty or degenerate cases.

Module: `Erdos1040.CapPolynomial`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.isCompact_capSet : ∀ (M a : ℝ), IsCompact.{0} (Erdos1040.capSet M a)
```

## E1040-CAP-SEPARATOR - `Erdos1040.cap_denominator_ne_zero`

If a is positive, then for every real M, every real pole b, and every z in capSet M a, b-z is nonzero.

Module: `Erdos1040.CapPolynomial`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.cap_denominator_ne_zero : ∀ {M a : ℝ},
  LT.lt.{0} 0 a → ∀ (b : ℝ) (z : ↑(Erdos1040.capSet M a)), Ne.{1} (HSub.hSub.{0, 0, 0} ↑b ↑z) 0
```

## E1040-CAP-SEPARATOR - `Erdos1040.capResolvent`

For real M and positive a, and every real pole b, capResolvent is the continuous complex function z mapped to the reciprocal of b-z on capSet M a.

Module: `Erdos1040.CapPolynomial`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.capResolvent : (M a : ℝ) → LT.lt.{0} 0 a → ℝ → ContinuousMap.{0, 0} ↑(Erdos1040.capSet M a) ℂ
```

## E1040-CAP-SEPARATOR - `Erdos1040.closed_subalgebra_geometric_inverse_mem`

For any compact topological space K and any closed complex subalgebra A of continuous complex functions on K, if f belongs to A, its uniform norm is less than one, and g times (1-f) equals one, then g belongs to A.

Module: `Erdos1040.CapPolynomial`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.closed_subalgebra_geometric_inverse_mem.{u_1} : ∀ {K : Type u_1} [inst : TopologicalSpace.{u_1} K]
  [inst_1 : CompactSpace.{u_1} K] (A : Subalgebra.{0, u_1} ℂ (ContinuousMap.{u_1, 0} K ℂ)),
  IsClosed.{u_1} ↑A →
    ∀ {f g : ContinuousMap.{u_1, 0} K ℂ},
      Membership.mem.{u_1, u_1} A f →
        LT.lt.{0} (Norm.norm.{u_1} f) 1 →
          Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} g (HSub.hSub.{u_1, u_1, u_1} 1 f)) 1 → Membership.mem.{u_1, u_1} A g
```

## E1040-CAP-SEPARATOR - `Erdos1040.capResolvent_far_mem`

For positive real a and M and a real B greater than M, the resolvent 1/(B-z) on capSet M a lies in the uniform closure of complex polynomial functions.

Module: `Erdos1040.CapPolynomial`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.capResolvent_far_mem : ∀ {M a : ℝ} (ha : LT.lt.{0} 0 a),
  LT.lt.{0} 0 M →
    ∀ (B : ℝ),
      LT.lt.{0} M B →
        Membership.mem.{0, 0} (Subalgebra.topologicalClosure.{0, 0} (polynomialFunctions.{0} (Erdos1040.capSet M a)))
          (Erdos1040.capResolvent M a ha B)
```

## E1040-CAP-SEPARATOR - `Erdos1040.capResolvent_step_mem`

For positive real a, every real M and b, and a real step h with absolute value less than a, membership of 1/(b-z) in the uniform polynomial closure on capSet M a implies membership of 1/(b-h-z) in the same closure.

Module: `Erdos1040.CapPolynomial`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.capResolvent_step_mem : ∀ {M a : ℝ} (ha : LT.lt.{0} 0 a) (b h : ℝ),
  LT.lt.{0} (abs.{0} h) a →
    Membership.mem.{0, 0} (Subalgebra.topologicalClosure.{0, 0} (polynomialFunctions.{0} (Erdos1040.capSet M a)))
        (Erdos1040.capResolvent M a ha b) →
      Membership.mem.{0, 0} (Subalgebra.topologicalClosure.{0, 0} (polynomialFunctions.{0} (Erdos1040.capSet M a)))
        (Erdos1040.capResolvent M a ha (HSub.hSub.{0, 0, 0} b h))
```

## E1040-ANNIHILATOR - `Erdos1040.adjointAreaPotential_ae_zero_of_annihilator`

For compact planar source and observation sets S and K, a finite measure mu on subtype S, and real area-L2 density h on K, if h is orthogonal to every Bochner logarithmic source potential of a bounded measurable real mu-density, then the actual adjointAreaPotential of h vanishes mu-almost everywhere on S. Orthogonality is an explicit conditional hypothesis, not the density theorem.

Module: `Erdos1040.SourceDensity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.adjointAreaPotential_ae_zero_of_annihilator : ∀ {S K : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (hK : IsCompact.{0} K) (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsFiniteMeasure.{0} μ]
      (h : ↥(MeasureTheory.Lp.{0, 0} ℝ 2 (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K))),
      (∀ (f : ↑S → ℝ),
          Measurable.{0, 0} f →
            (∃ C, ∀ (w : ↑S), LE.le.{0} (Norm.norm.{0} (f w)) C) →
              Eq.{1}
                (Inner.inner.{0, 0} ℝ h (∫ (w : ↑S), HSMul.hSMul.{0, 0, 0} (f w) (Erdos1040.areaLogKernel hK ↑w) ∂μ))
                0) →
        (fun w => Erdos1040.adjointAreaPotential hK h ↑w) =ᵐ[μ] fun x => 0
```

## E1040-CAP-SEPARATOR - `Erdos1040.capSet_compactSpace`

For every real M and a, the subtype capSet M a carries a compact-space instance, derived from its proven compactness.

Module: `Erdos1040.CapPolynomial`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.capSet_compactSpace : ∀ (M a : ℝ), CompactSpace.{0} ↑(Erdos1040.capSet M a)
```

## E1040-POTENTIAL-HARMONICITY - `Erdos1040.norm_normalized_log_kernel_le`

For complex center z0, source w, and observation z, if a positive r is at most norm(z0-w) and norm(z-z0) is less than r/2, the norm of the principal complex logarithm of 1+(z-z0)/(z0-w) is at most 1.

Module: `Erdos1040.PotentialHarmonic`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.norm_normalized_log_kernel_le : ∀ {z₀ z w : ℂ} {r : ℝ},
  LT.lt.{0} 0 r →
    LE.le.{0} r (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z₀ w)) →
      LT.lt.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z z₀)) (HDiv.hDiv.{0, 0, 0} r 2) →
        LE.le.{0}
          (Norm.norm.{0}
            (Complex.log
              (HAdd.hAdd.{0, 0, 0} 1 (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} z z₀) (HSub.hSub.{0, 0, 0} z₀ w)))))
          1
```

## E1040-POTENTIAL-HARMONICITY - `Erdos1040.hasDerivAt_normalized_log_kernel`

For complex center z0, source w, and observation z, if a positive r is at most norm(z0-w) and norm(z-z0) is less than r/2, the local normalized logarithm v maps to Complex.log(1+(v-z0)/(z0-w)) has complex derivative (z-w) inverse at z.

Module: `Erdos1040.PotentialHarmonic`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.hasDerivAt_normalized_log_kernel : ∀ {z₀ z w : ℂ} {r : ℝ},
  LT.lt.{0} 0 r →
    LE.le.{0} r (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z₀ w)) →
      LT.lt.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z z₀)) (HDiv.hDiv.{0, 0, 0} r 2) →
        HasDerivAt.{0, 0}
          (fun v =>
            Complex.log
              (HAdd.hAdd.{0, 0, 0} 1 (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} v z₀) (HSub.hSub.{0, 0, 0} z₀ w))))
          (Inv.inv.{0} (HSub.hSub.{0, 0, 0} z w)) z
```

## E1040-POTENTIAL-HARMONICITY - `Erdos1040.integrable_normalized_log_density`

For any complex source subtype S uniformly separated from z0 by a positive r, any measure mu on S, and real mu-integrable density f, the complex integrand f(w) times Complex.log(1+(z-z0)/(z0-w)) is integrable whenever norm(z-z0) is less than r/2.

Module: `Erdos1040.PotentialHarmonic`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integrable_normalized_log_density : ∀ {S : Set.{0} ℂ} {z₀ z : ℂ} {r : ℝ},
  LT.lt.{0} 0 r →
    (∀ (w : ↑S), LE.le.{0} r (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z₀ ↑w))) →
      ∀ (μ : MeasureTheory.Measure.{0} ↑S) (f : ↑S → ℝ),
        MeasureTheory.Integrable.{0, 0} f μ →
          LT.lt.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z z₀)) (HDiv.hDiv.{0, 0, 0} r 2) →
            MeasureTheory.Integrable.{0, 0}
              (fun w =>
                HMul.hMul.{0, 0, 0} (↑(f w))
                  (Complex.log
                    (HAdd.hAdd.{0, 0, 0} 1
                      (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} z z₀) (HSub.hSub.{0, 0, 0} z₀ ↑w)))))
              μ
```

## E1040-POTENTIAL-HARMONICITY - `Erdos1040.differentiableOn_normalized_log_density_integral`

For any complex source subtype S uniformly separated from z0 by a positive r, any measure mu on S, and real mu-integrable density f, the actual complex source integral of f(w) times Complex.log(1+(z-z0)/(z0-w)) is complex differentiable on the open disk centered at z0 of radius r/2. No global logarithm branch is assumed.

Module: `Erdos1040.PotentialHarmonic`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.differentiableOn_normalized_log_density_integral : ∀ {S : Set.{0} ℂ} {z₀ : ℂ} {r : ℝ},
  LT.lt.{0} 0 r →
    (∀ (w : ↑S), LE.le.{0} r (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z₀ ↑w))) →
      ∀ (μ : MeasureTheory.Measure.{0} ↑S) (f : ↑S → ℝ),
        MeasureTheory.Integrable.{0, 0} f μ →
          DifferentiableOn.{0, 0, 0} ℂ
            (fun z =>
              ∫ (w : ↑S),
                HMul.hMul.{0, 0, 0} (↑(f w))
                  (Complex.log
                    (HAdd.hAdd.{0, 0, 0} 1
                      (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} z z₀) (HSub.hSub.{0, 0, 0} z₀ ↑w)))) ∂μ)
            (Metric.ball.{0} z₀ (HDiv.hDiv.{0, 0, 0} r 2))
```

## E1040-POTENTIAL-HARMONICITY - `Erdos1040.integrable_log_density_potential_of_notMem`

For any compact complex source set S, any measure mu on subtype S, any real mu-integrable density f, and every complex observation z outside S, the actual logarithmic source integrand f(w) log norm(z-w) is absolutely integrable. Finiteness of mu itself is not required.

Module: `Erdos1040.PotentialHarmonic`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integrable_log_density_potential_of_notMem : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (μ : MeasureTheory.Measure.{0} ↑S) (f : ↑S → ℝ),
      MeasureTheory.Integrable.{0, 0} f μ →
        ∀ {z : ℂ},
          z ∉ S →
            MeasureTheory.Integrable.{0, 0}
              (fun w => HMul.hMul.{0, 0, 0} (f w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)))) μ
```

## E1040-POTENTIAL-HARMONICITY - `Erdos1040.harmonicAt_log_density_potential`

For every compact complex source set S, any measure mu on subtype S, and real mu-integrable density f, the actual real logarithmic source potential is harmonic at every complex observation outside S. Finiteness of mu itself, boundary smoothness, connectedness, and a global harmonic conjugate are not assumptions.

Module: `Erdos1040.PotentialHarmonic`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.harmonicAt_log_density_potential : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (μ : MeasureTheory.Measure.{0} ↑S) (f : ↑S → ℝ),
      MeasureTheory.Integrable.{0, 0} f μ →
        ∀ {z₀ : ℂ},
          z₀ ∉ S →
            InnerProductSpace.HarmonicAt.{0, 0}
              (fun z => ∫ (w : ↑S), HMul.hMul.{0, 0, 0} (f w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ∂μ)
              z₀
```

## E1040-POTENTIAL-HARMONICITY - `Erdos1040.harmonicOnNhd_log_density_potential_compl`

For every compact complex source set S, any measure mu on subtype S, and real mu-integrable density f, the actual real logarithmic source potential is harmonic on a neighborhood of every point of the complement of S. No assertion of harmonicity at a source point is made.

Module: `Erdos1040.PotentialHarmonic`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.harmonicOnNhd_log_density_potential_compl : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (μ : MeasureTheory.Measure.{0} ↑S) (f : ↑S → ℝ),
      MeasureTheory.Integrable.{0, 0} f μ →
        InnerProductSpace.HarmonicOnNhd.{0, 0}
          (fun z => ∫ (w : ↑S), HMul.hMul.{0, 0, 0} (f w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ∂μ)
          (Compl.compl.{0} S)
```

## E1040-ANNIHILATOR - `Erdos1040.adjointAreaPotential_zero_on_support_of_annihilator`

For compact planar source and observation sets S and K, a finite measure mu on subtype S, and real area-L2 density h on K orthogonal to every Bochner logarithmic source potential of a bounded measurable real mu-density, the actual adjointAreaPotential of h is zero at every complex point in the topological support of the pushforward of mu by subtype inclusion. The orthogonality hypothesis is explicit.

Module: `Erdos1040.SourceDensity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.adjointAreaPotential_zero_on_support_of_annihilator : ∀ {S K : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (hK : IsCompact.{0} K) (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsFiniteMeasure.{0} μ]
      (h : ↥(MeasureTheory.Lp.{0, 0} ℝ 2 (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K))),
      (∀ (f : ↑S → ℝ),
          Measurable.{0, 0} f →
            (∃ C, ∀ (w : ↑S), LE.le.{0} (Norm.norm.{0} (f w)) C) →
              Eq.{1}
                (Inner.inner.{0, 0} ℝ h (∫ (w : ↑S), HSMul.hSMul.{0, 0, 0} (f w) (Erdos1040.areaLogKernel hK ↑w) ∂μ))
                0) →
        ∀ (w : ℂ),
          Membership.mem.{0, 0} (MeasureTheory.Measure.support.{0} (MeasureTheory.Measure.map.{0, 0} Subtype.val.{1} μ))
              w →
            Eq.{1} (Erdos1040.adjointAreaPotential hK h w) 0
```

## E1040-CAP-SEPARATOR - `Erdos1040.capResolvent_zero_mem`

For positive real a and M, the actual resolvent 1/(0-z) on capSet M a lies in the uniform closure of complex polynomial functions, using finitely many real pole moves from a sufficiently distant positive pole.

Module: `Erdos1040.CapPolynomial`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.capResolvent_zero_mem : ∀ {M a : ℝ} (ha : LT.lt.{0} 0 a),
  LT.lt.{0} 0 M →
    Membership.mem.{0, 0} (Subalgebra.topologicalClosure.{0, 0} (polynomialFunctions.{0} (Erdos1040.capSet M a)))
      (Erdos1040.capResolvent M a ha 0)
```

## E1040-CAP-SEPARATOR - `Erdos1040.exists_cap_polynomial`

For every pair of real numbers satisfying 0<a<M, there exists a complex polynomial Q such that Q evaluated at zero equals one and its modulus is strictly less than one quarter at every complex z satisfying norm z at most M and absolute imaginary part at least a. No approximation theorem or separator existence is assumed.

Module: `Erdos1040.CapPolynomial`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_cap_polynomial : ∀ {M a : ℝ},
  LT.lt.{0} 0 a →
    LT.lt.{0} a M →
      ∃ Q,
        Eq.{1} (Polynomial.eval.{0} 0 Q) 1 ∧
          ∀ (z : ℂ),
            LE.le.{0} (Norm.norm.{0} z) M →
              LE.le.{0} a (abs.{0} z.im) → LT.lt.{0} (Norm.norm.{0} (Polynomial.eval.{0} z Q)) (1 / 4)
```

## E1040-POTENTIAL-MOMENTS - `Erdos1040.hasSum_log_density_moments`

For an integrable real source density on a source subtype bounded in norm by a nonnegative M, and every complex u with norm(u) times M less than 1, the series with nth term u^n times the complex nth moment divided by n converges to the actual integral of the density times minus the principal complex logarithm of 1-u*w. The n=0 summand is zero by totalized division; all positive terms are the ordinary logarithmic expansion.

Module: `Erdos1040.PotentialMoments`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.hasSum_log_density_moments : ∀ {S : Set.{0} ℂ} {M : ℝ},
  LE.le.{0} 0 M →
    (∀ (w : ↑S), LE.le.{0} (Norm.norm.{0} ↑w) M) →
      ∀ (μ : MeasureTheory.Measure.{0} ↑S) (f : ↑S → ℝ),
        MeasureTheory.Integrable.{0, 0} f μ →
          ∀ {u : ℂ},
            LT.lt.{0} (HMul.hMul.{0, 0, 0} (Norm.norm.{0} u) M) 1 →
              HasSum.{0, 0}
                (fun n =>
                  HDiv.hDiv.{0, 0, 0}
                    (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} u n)
                      (∫ (w : ↑S), HMul.hMul.{0, 0, 0} (↑(f w)) (HPow.hPow.{0, 0, 0} (↑w) n) ∂μ))
                    ↑n)
                (∫ (w : ↑S),
                  HMul.hMul.{0, 0, 0} (↑(f w))
                    (Neg.neg.{0} (Complex.log (HSub.hSub.{0, 0, 0} 1 (HMul.hMul.{0, 0, 0} u ↑w)))) ∂μ)
```

## E1040-POTENTIAL-MOMENTS - `Erdos1040.hasFPowerSeriesAt_log_density_generating_function`

For every compact complex source set, every measure on its subtype, and every integrable real density, the actual complex logarithmic generating integral has a convergent power series at zero whose nth coefficient is the complex nth moment divided by n. Its zeroth coefficient is zero.

Module: `Erdos1040.PotentialMoments`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.hasFPowerSeriesAt_log_density_generating_function : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (μ : MeasureTheory.Measure.{0} ↑S) (f : ↑S → ℝ),
      MeasureTheory.Integrable.{0, 0} f μ →
        HasFPowerSeriesAt.{0, 0, 0}
          (fun u =>
            ∫ (w : ↑S),
              HMul.hMul.{0, 0, 0} (↑(f w))
                (Neg.neg.{0} (Complex.log (HSub.hSub.{0, 0, 0} 1 (HMul.hMul.{0, 0, 0} u ↑w)))) ∂μ)
          (FormalMultilinearSeries.ofScalars.{0, 0} ℂ fun n =>
            HDiv.hDiv.{0, 0, 0} (∫ (w : ↑S), HMul.hMul.{0, 0, 0} (↑(f w)) (HPow.hPow.{0, 0, 0} (↑w) n) ∂μ) ↑n)
          0
```

## E1040-POTENTIAL-MOMENTS - `Erdos1040.integrable_log_density_generating_function`

For every real integrable source density, every norm bound M on its source subtype, and every complex u with norm(u) times M at most one half, the actual density-weighted complex logarithm generating kernel is integrable.

Module: `Erdos1040.PotentialMoments`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integrable_log_density_generating_function : ∀ {S : Set.{0} ℂ} {M : ℝ},
  (∀ (w : ↑S), LE.le.{0} (Norm.norm.{0} ↑w) M) →
    ∀ (μ : MeasureTheory.Measure.{0} ↑S) (f : ↑S → ℝ),
      MeasureTheory.Integrable.{0, 0} f μ →
        ∀ {u : ℂ},
          LE.le.{0} (HMul.hMul.{0, 0, 0} (Norm.norm.{0} u) M) (1 / 2) →
            MeasureTheory.Integrable.{0, 0}
              (fun w =>
                HMul.hMul.{0, 0, 0} (↑(f w))
                  (Neg.neg.{0} (Complex.log (HSub.hSub.{0, 0, 0} 1 (HMul.hMul.{0, 0, 0} u ↑w)))))
              μ
```

## E1040-POTENTIAL-MOMENTS - `Erdos1040.re_log_density_generating_function`

Under the same source-norm bound and integrable real-density hypotheses, for nonzero u with norm(u) times M at most one half, the real part of the actual generating integral equals the total real source mass times log(norm(inverse u)) minus the actual real logarithmic source potential evaluated at inverse u.

Module: `Erdos1040.PotentialMoments`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.re_log_density_generating_function : ∀ {S : Set.{0} ℂ} {M : ℝ},
  (∀ (w : ↑S), LE.le.{0} (Norm.norm.{0} ↑w) M) →
    ∀ (μ : MeasureTheory.Measure.{0} ↑S) (f : ↑S → ℝ),
      MeasureTheory.Integrable.{0, 0} f μ →
        ∀ {u : ℂ},
          Ne.{1} u 0 →
            LE.le.{0} (HMul.hMul.{0, 0, 0} (Norm.norm.{0} u) M) (1 / 2) →
              Eq.{1}
                (∫ (w : ↑S),
                    HMul.hMul.{0, 0, 0} (↑(f w))
                      (Neg.neg.{0} (Complex.log (HSub.hSub.{0, 0, 0} 1 (HMul.hMul.{0, 0, 0} u ↑w)))) ∂μ).re
                (HSub.hSub.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0} (∫ (w : ↑S), f w ∂μ) (Real.log (Norm.norm.{0} (Inv.inv.{0} u))))
                  (∫ (w : ↑S),
                    HMul.hMul.{0, 0, 0} (f w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} (Inv.inv.{0} u) ↑w))) ∂μ))
```

## E1040-POTENTIAL-MOMENTS - `Erdos1040.integral_eq_of_log_density_potential_eq`

For two arbitrary compact complex source sets with separate finite measures and real integrable densities, if their actual real logarithmic potentials agree at every complex point outside some disk, then their total real masses are equal.

Module: `Erdos1040.PotentialMoments`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integral_eq_of_log_density_potential_eq : ∀ {S T : Set.{0} ℂ},
  IsCompact.{0} S →
    IsCompact.{0} T →
      ∀ (μ : MeasureTheory.Measure.{0} ↑S) (ν : MeasureTheory.Measure.{0} ↑T) [MeasureTheory.IsFiniteMeasure.{0} μ]
        [MeasureTheory.IsFiniteMeasure.{0} ν] (f : ↑S → ℝ) (g : ↑T → ℝ),
        MeasureTheory.Integrable.{0, 0} f μ →
          MeasureTheory.Integrable.{0, 0} g ν →
            ∀ {R₀ : ℝ},
              (∀ (z : ℂ),
                  LT.lt.{0} R₀ (Norm.norm.{0} z) →
                    Eq.{1}
                      (∫ (w : ↑S), HMul.hMul.{0, 0, 0} (f w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ∂μ)
                      (∫ (w : ↑T),
                        HMul.hMul.{0, 0, 0} (g w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ∂ν)) →
                Eq.{1} (∫ (w : ↑S), f w ∂μ) (∫ (w : ↑T), g w ∂ν)
```

## E1040-POTENTIAL-MOMENTS - `Erdos1040.complex_moments_eq_of_log_density_potential_eq`

For two arbitrary compact complex source sets with separate finite measures and real integrable densities, equality of their actual real logarithmic potentials everywhere outside some disk implies equality of their complex nth moments for every natural n, including the zeroth moment. No moment-equality hypothesis is assumed.

Module: `Erdos1040.PotentialMoments`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.complex_moments_eq_of_log_density_potential_eq : ∀ {S T : Set.{0} ℂ},
  IsCompact.{0} S →
    IsCompact.{0} T →
      ∀ (μ : MeasureTheory.Measure.{0} ↑S) (ν : MeasureTheory.Measure.{0} ↑T) [MeasureTheory.IsFiniteMeasure.{0} μ]
        [MeasureTheory.IsFiniteMeasure.{0} ν] (f : ↑S → ℝ) (g : ↑T → ℝ),
        MeasureTheory.Integrable.{0, 0} f μ →
          MeasureTheory.Integrable.{0, 0} g ν →
            ∀ {R₀ : ℝ},
              (∀ (z : ℂ),
                  LT.lt.{0} R₀ (Norm.norm.{0} z) →
                    Eq.{1}
                      (∫ (w : ↑S), HMul.hMul.{0, 0, 0} (f w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ∂μ)
                      (∫ (w : ↑T),
                        HMul.hMul.{0, 0, 0} (g w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ∂ν)) →
                ∀ (n : ℕ),
                  Eq.{1} (∫ (w : ↑S), HMul.hMul.{0, 0, 0} (↑(f w)) (HPow.hPow.{0, 0, 0} (↑w) n) ∂μ)
                    (∫ (w : ↑T), HMul.hMul.{0, 0, 0} (↑(g w)) (HPow.hPow.{0, 0, 0} (↑w) n) ∂ν)
```

## E1040-POTENTIAL-MOMENTS - `Erdos1040.integrable_polynomial_density`

For every compact complex source set, every measure on its subtype, every integrable real density, and every complex polynomial, the density times the polynomial evaluated at the source point is integrable.

Module: `Erdos1040.PotentialMoments`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integrable_polynomial_density : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (μ : MeasureTheory.Measure.{0} ↑S) (f : ↑S → ℝ),
      MeasureTheory.Integrable.{0, 0} f μ →
        ∀ (p : Polynomial.{0} ℂ),
          MeasureTheory.Integrable.{0, 0} (fun w => HMul.hMul.{0, 0, 0} (↑(f w)) (Polynomial.eval.{0} (↑w) p)) μ
```

## E1040-POTENTIAL-MOMENTS - `Erdos1040.polynomial_integrals_eq_of_log_density_potential_eq`

For two arbitrary compact complex source sets with separate finite measures and real integrable densities, equality of their actual real logarithmic potentials everywhere outside some disk implies equality of their density-weighted integrals against every complex polynomial. The sources need not share a set or measure, and no polynomial-moment equality is assumed.

Module: `Erdos1040.PotentialMoments`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.polynomial_integrals_eq_of_log_density_potential_eq : ∀ {S T : Set.{0} ℂ},
  IsCompact.{0} S →
    IsCompact.{0} T →
      ∀ (μ : MeasureTheory.Measure.{0} ↑S) (ν : MeasureTheory.Measure.{0} ↑T) [MeasureTheory.IsFiniteMeasure.{0} μ]
        [MeasureTheory.IsFiniteMeasure.{0} ν] (f : ↑S → ℝ) (g : ↑T → ℝ),
        MeasureTheory.Integrable.{0, 0} f μ →
          MeasureTheory.Integrable.{0, 0} g ν →
            ∀ {R₀ : ℝ},
              (∀ (z : ℂ),
                  LT.lt.{0} R₀ (Norm.norm.{0} z) →
                    Eq.{1}
                      (∫ (w : ↑S), HMul.hMul.{0, 0, 0} (f w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ∂μ)
                      (∫ (w : ↑T),
                        HMul.hMul.{0, 0, 0} (g w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ∂ν)) →
                ∀ (p : Polynomial.{0} ℂ),
                  Eq.{1} (∫ (w : ↑S), HMul.hMul.{0, 0, 0} (↑(f w)) (Polynomial.eval.{0} (↑w) p) ∂μ)
                    (∫ (w : ↑T), HMul.hMul.{0, 0, 0} (↑(g w)) (Polynomial.eval.{0} (↑w) p) ∂ν)
```

## E1040-DENSITY-OPERATOR - `Erdos1040.boundedMeasurableDensities`

For any complex source subtype S, boundedMeasurableDensities is the real vector subspace of all measurable real functions on S whose norms have some finite pointwise real bound.

Module: `Erdos1040.DensityOperator`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.boundedMeasurableDensities : (S : Set.{0} ℂ) → Submodule.{0, 0} ℝ (↑S → ℝ)
```

## E1040-DENSITY-OPERATOR - `Erdos1040.sourceDensityOperator`

For compact source and observation sets S and K and a finite measure mu on subtype S, sourceDensityOperator is the real linear map sending an actual bounded measurable real density to the Bochner area-L2 integral of that density times areaLogKernel.

Module: `Erdos1040.DensityOperator`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.sourceDensityOperator : {S K : Set.{0} ℂ} →
  IsCompact.{0} S →
    IsCompact.{0} K →
      (μ : MeasureTheory.Measure.{0} ↑S) →
        [MeasureTheory.IsFiniteMeasure.{0} μ] →
          LinearMap.{0, 0, 0, 0} (RingHom.id.{0} ℝ) ↥(Erdos1040.boundedMeasurableDensities S)
            ↥(MeasureTheory.Lp.{0, 0} ℝ 2 (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K))
```

## E1040-DENSITY-OPERATOR - `Erdos1040.exists_density_approx_of_annihilator`

For compact source and observation sets S and K, a finite measure mu on subtype S, and a real area-L2 class u on K, if every area-L2 h orthogonal to all bounded measurable logarithmic source-density potentials is also orthogonal to u, then for every positive tolerance u is approximated in L2 norm by the actual Bochner potential of a bounded measurable real density. This is a conditional Hilbert-space closure criterion; the annihilator implication is an explicit hypothesis to be proved separately.

Module: `Erdos1040.DensityOperator`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_density_approx_of_annihilator : ∀ {S K : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (hK : IsCompact.{0} K) (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsFiniteMeasure.{0} μ]
      (u : ↥(MeasureTheory.Lp.{0, 0} ℝ 2 (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K))),
      (∀
          (h :
            ↥(MeasureTheory.Lp.{0, 0} ℝ 2
                (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K))),
          (∀ (f : ↑S → ℝ),
              Measurable.{0, 0} f →
                (∃ C, ∀ (w : ↑S), LE.le.{0} (Norm.norm.{0} (f w)) C) →
                  Eq.{1}
                    (Inner.inner.{0, 0} ℝ h
                      (∫ (w : ↑S), HSMul.hSMul.{0, 0, 0} (f w) (Erdos1040.areaLogKernel hK ↑w) ∂μ))
                    0) →
            Eq.{1} (Inner.inner.{0, 0} ℝ h u) 0) →
        ∀ (ε : ℝ),
          LT.lt.{0} 0 ε →
            ∃ f,
              Measurable.{0, 0} f ∧
                (∃ C, ∀ (w : ↑S), LE.le.{0} (Norm.norm.{0} (f w)) C) ∧
                  LT.lt.{0}
                    (Norm.norm.{0}
                      (HSub.hSub.{0, 0, 0} (∫ (w : ↑S), HSMul.hSMul.{0, 0, 0} (f w) (Erdos1040.areaLogKernel hK ↑w) ∂μ)
                        u))
                    ε
```

## E1040-RUNGE - `Erdos1040.exists_polynomial_rotation_integral`

For every compact complex source set S, finite measure mu on subtype S, and complex polynomial Q, there is a complex polynomial A whose evaluation at every complex u is the actual source integral of Q(u w). The finite coefficients are obtained by integrating polynomial moments.

Module: `Erdos1040.CapRotation`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_polynomial_rotation_integral : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsFiniteMeasure.{0} μ] (Q : Polynomial.{0} ℂ),
      ∃ A, ∀ (u : ℂ), Eq.{1} (Polynomial.eval.{0} u A) (∫ (w : ↑S), Polynomial.eval.{0} (HMul.hMul.{0, 0, 0} u ↑w) Q ∂μ)
```

## E1040-RUNGE - `Erdos1040.exists_unit_rotation_mean_ge_constant`

For every compact complex source set S, probability measure mu on subtype S, and complex polynomial Q, there exists a complex u of norm one for which the source integral of the real part of Q(u w) is at least the real part of Q(0). The source probability measure is unchanged.

Module: `Erdos1040.CapRotation`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_unit_rotation_mean_ge_constant : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsProbabilityMeasure.{0} μ] (Q : Polynomial.{0} ℂ),
      ∃ u,
        Eq.{1} (Norm.norm.{0} u) 1 ∧
          LE.le.{0} (Polynomial.eval.{0} 0 Q).re (∫ (w : ↑S), (Polynomial.eval.{0} (HMul.hMul.{0, 0, 0} u ↑w) Q).re ∂μ)
```

## E1040-RUNGE - `Erdos1040.volume_rotated_strip_le`

For nonnegative real M and a and every complex unit u, the planar Lebesgue area of the set of z with norm(z) at most M and absolute imaginary part of u z at most a is at most 4 M a, interpreted by ENNReal.ofReal.

Module: `Erdos1040.CapRotation`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.volume_rotated_strip_le : ∀ {M a : ℝ},
  LE.le.{0} 0 M →
    LE.le.{0} 0 a →
      ∀ {u : ℂ},
        Eq.{1} (Norm.norm.{0} u) 1 →
          LE.le.{0}
            (MeasureTheory.MeasureSpace.volume.{0}
              (Set.ofPred.{0} fun z =>
                LE.le.{0} (Norm.norm.{0} z) M ∧ LE.le.{0} (abs.{0} (HMul.hMul.{0, 0, 0} u z).im) a))
            (ENNReal.ofReal (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} 4 M) a))
```

## E1040-RUNGE - `Erdos1040.exists_mean_zero_polynomial_large_off_small_area`

For every compact complex source set S, probability measure mu on subtype S, positive observation radius M, and positive area tolerance eta, there exists a complex polynomial P whose real part has source integral zero and for which the planar Lebesgue area of {z : norm(z) at most M and Re(P(z)) at most 3/4} is strictly less than eta. This strengthens candidate Lemma 4 by not requiring the observation disk to contain the compact sources; its real polynomial is harmonic as the real part of a complex polynomial. No source rotation, final root construction, polynomial-degree bound, or full capacity-one conclusion is asserted.

Module: `Erdos1040.CapRotation`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_mean_zero_polynomial_large_off_small_area : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsProbabilityMeasure.{0} μ] {M η : ℝ},
      LT.lt.{0} 0 M →
        LT.lt.{0} 0 η →
          ∃ P,
            Eq.{1} (∫ (w : ↑S), (Polynomial.eval.{0} (↑w) P).re ∂μ) 0 ∧
              LT.lt.{0}
                (MeasureTheory.MeasureSpace.volume.{0}
                  (Set.ofPred.{0} fun z =>
                    LE.le.{0} (Norm.norm.{0} z) M ∧ LE.le.{0} (Polynomial.eval.{0} z P).re (3 / 4)))
                (ENNReal.ofReal η)
```

## E1040-ADJOINT-UNIQUENESS - `Erdos1040.adjointAreaPotential_eq_mass_mul_source_potential_of_annihilator`

Conditional supporting theorem: let S and K be arbitrary compact complex sets with S contained in K, let mu be a probability measure on the subtype S, assume the complement of K is preconnected, assume every point of the frontier of K belongs to the support of mu mapped into the complex plane, and assume the actual real logarithmic source potential of mu is nonnegative everywhere. For every real area-L2 density h on K which annihilates the Bochner area potential of every bounded measurable real source density, the actual adjoint area potential at every z outside K equals the total real area mass of h times the actual mu source potential at z. All mass signs are covered. The support, topology, and global nonnegativity assumptions are explicit classical inputs still to be proved for the capacity-one application.

Module: `Erdos1040.AdjointUniqueness`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.adjointAreaPotential_eq_mass_mul_source_potential_of_annihilator : ∀ {S K : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (hK : IsCompact.{0} K),
      S ⊆ K →
        ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsProbabilityMeasure.{0} μ],
          IsPreconnected.{0} (Compl.compl.{0} K) →
            frontier.{0} K ⊆ MeasureTheory.Measure.support.{0} (MeasureTheory.Measure.map.{0, 0} Subtype.val.{1} μ) →
              (∀ (z : ℂ), LE.le.{0} 0 (∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)) ∂μ)) →
                ∀
                  (h :
                    ↥(MeasureTheory.Lp.{0, 0} ℝ 2
                        (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K))),
                  (∀ (f : ↑S → ℝ),
                      Measurable.{0, 0} f →
                        (∃ C, ∀ (w : ↑S), LE.le.{0} (Norm.norm.{0} (f w)) C) →
                          Eq.{1}
                            (Inner.inner.{0, 0} ℝ h
                              (∫ (w : ↑S), HSMul.hSMul.{0, 0, 0} (f w) (Erdos1040.areaLogKernel hK ↑w) ∂μ))
                            0) →
                    ∀ z ∉ K,
                      Eq.{1} (Erdos1040.adjointAreaPotential hK h z)
                        (HMul.hMul.{0, 0, 0} (∫ (w : ℂ) in K, ↑↑h w)
                          (∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)) ∂μ))
```

## E1040-ADJOINT-UNIQUENESS - `Erdos1040.integral_area_mul_re_polynomial_eq_mass_mul_source_integral_of_annihilator`

Conditional supporting identity under the identical compact-set, probability-measure, preconnected-complement, frontier-support, globally nonnegative actual source-potential, and bounded-measurable-source annihilator hypotheses of adjointAreaPotential_eq_mass_mul_source_potential_of_annihilator: for every complex polynomial p, the actual planar-area integral over K of h(z) times Re(p(z)) equals the total real area mass of h times the mu integral over S of Re(p(w)). The proof uses distinct area-subtype and source measures, actual exterior potential equality, the polynomial-moment theorem, and checked integrability before taking real parts.

Module: `Erdos1040.AdjointUniqueness`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integral_area_mul_re_polynomial_eq_mass_mul_source_integral_of_annihilator : ∀ {S K : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (hK : IsCompact.{0} K),
      S ⊆ K →
        ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsProbabilityMeasure.{0} μ],
          IsPreconnected.{0} (Compl.compl.{0} K) →
            frontier.{0} K ⊆ MeasureTheory.Measure.support.{0} (MeasureTheory.Measure.map.{0, 0} Subtype.val.{1} μ) →
              (∀ (z : ℂ), LE.le.{0} 0 (∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)) ∂μ)) →
                ∀
                  (h :
                    ↥(MeasureTheory.Lp.{0, 0} ℝ 2
                        (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K))),
                  (∀ (f : ↑S → ℝ),
                      Measurable.{0, 0} f →
                        (∃ C, ∀ (w : ↑S), LE.le.{0} (Norm.norm.{0} (f w)) C) →
                          Eq.{1}
                            (Inner.inner.{0, 0} ℝ h
                              (∫ (w : ↑S), HSMul.hSMul.{0, 0, 0} (f w) (Erdos1040.areaLogKernel hK ↑w) ∂μ))
                            0) →
                    ∀ (p : Polynomial.{0} ℂ),
                      Eq.{1} (∫ (z : ℂ) in K, HMul.hMul.{0, 0, 0} (↑↑h z) (Polynomial.eval.{0} z p).re)
                        (HMul.hMul.{0, 0, 0} (∫ (z : ℂ) in K, ↑↑h z) (∫ (w : ↑S), (Polynomial.eval.{0} (↑w) p).re ∂μ))
```

## E1040-LOG-ENERGY - `Erdos1040.nonnegativeLogKernel`

For real D and complex z,w, nonnegativeLogKernel is the nonnegative extended-real part of the extended logarithm of ofReal(D) divided by edist(z,w). When D is positive it has infinite value on the diagonal and equals the nonnegative part of log(D/dist(z,w)) off the diagonal; it is used as a shifted classical energy kernel only on sources whose pair distances are at most D.

Module: `Erdos1040.LogEnergy`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.nonnegativeLogKernel : ℝ → ℂ → ℂ → ENNReal
```

## E1040-LOG-ENERGY - `Erdos1040.nonnegativeLogKernel_self`

For every positive real D and complex z, nonnegativeLogKernel D z z is positive infinity, so point singularities are retained.

Module: `Erdos1040.LogEnergy`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.nonnegativeLogKernel_self : ∀ {D : ℝ},
  LT.lt.{0} 0 D → ∀ (z : ℂ), Eq.{1} (Erdos1040.nonnegativeLogKernel D z z) Top.top.{0}
```

## E1040-LOG-ENERGY - `Erdos1040.nonnegativeLogKernel_of_ne`

For every positive real D and distinct complex z,w, nonnegativeLogKernel D z w equals ENNReal.ofReal of the real logarithm of D divided by their distance.

Module: `Erdos1040.LogEnergy`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.nonnegativeLogKernel_of_ne : ∀ {D : ℝ},
  LT.lt.{0} 0 D →
    ∀ {z w : ℂ},
      Ne.{1} z w →
        Eq.{1} (Erdos1040.nonnegativeLogKernel D z w)
          (ENNReal.ofReal (Real.log (HDiv.hDiv.{0, 0, 0} D (Dist.dist.{0} z w))))
```

## E1040-LOG-ENERGY - `Erdos1040.continuous_nonnegativeLogKernel`

For every real D, the pair map (z,w) to nonnegativeLogKernel D z w is continuous into the extended nonnegative reals with their order topology.

Module: `Erdos1040.LogEnergy`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.continuous_nonnegativeLogKernel : ∀ (D : ℝ),
  Continuous.{0, 0} fun p => Erdos1040.nonnegativeLogKernel D p.1 p.2
```

## E1040-LOG-ENERGY - `Erdos1040.lowerSemicontinuous_lintegral_continuous_ennreal`

On a compact topological space with an opens-measurable Borel-compatible measure structure, the actual nonnegative integral of any continuous extended-nonnegative-real function is lower semicontinuous as a function of a probability measure in the weak topology. Infinite function and integral values are allowed.

Module: `Erdos1040.LogEnergy`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.lowerSemicontinuous_lintegral_continuous_ennreal.{u_1} : ∀ {K : Type u_1}
  [inst : TopologicalSpace.{u_1} K] [inst_1 : MeasurableSpace.{u_1} K] [inst_2 : OpensMeasurableSpace.{u_1} K]
  [CompactSpace.{u_1} K] (k : ContinuousMap.{u_1, 0} K ENNReal),
  LowerSemicontinuous.{u_1, 0} fun μ => ∫⁻ (x : K), k x ∂↑μ
```

## E1040-LOG-ENERGY - `Erdos1040.nonnegativeLogEnergy`

For a real scale D, a planar source set S, and a Borel probability measure mu on subtype S, nonnegativeLogEnergy is the actual nonnegative integral of nonnegativeLogKernel D against the product of mu with itself.

Module: `Erdos1040.LogEnergy`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.nonnegativeLogEnergy : {S : Set.{0} ℂ} → ℝ → MeasureTheory.ProbabilityMeasure.{0} ↑S → ENNReal
```

## E1040-LOG-ENERGY - `Erdos1040.lowerSemicontinuous_nonnegativeLogEnergy`

For every compact planar source S and every real D, the actual nonnegativeLogEnergy functional is lower semicontinuous on probability measures on S in the weak topology.

Module: `Erdos1040.LogEnergy`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.lowerSemicontinuous_nonnegativeLogEnergy : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S → ∀ (D : ℝ), LowerSemicontinuous.{0, 0} (Erdos1040.nonnegativeLogEnergy D)
```

## E1040-LOG-ENERGY - `Erdos1040.exists_minimizer_nonnegativeLogEnergy`

For a nonempty compact planar set S and a real D greater than zero that bounds every pair distance in S, there is a Borel probability measure on S minimizing the actual nonnegative shifted logarithmic energy among all Borel probability measures on S. The attained value may be infinite; no finite energy, uniqueness, support property, or Frostman conclusion is asserted.

Module: `Erdos1040.LogEnergy`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_minimizer_nonnegativeLogEnergy : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    Set.Nonempty.{0} S →
      ∀ (D : ℝ),
        LT.lt.{0} 0 D →
          (∀ (z : ℂ),
              Membership.mem.{0, 0} S z → ∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) D) →
            ∃ μ,
              ∀ (ν : MeasureTheory.ProbabilityMeasure.{0} ↑S),
                LE.le.{0} (Erdos1040.nonnegativeLogEnergy D μ) (Erdos1040.nonnegativeLogEnergy D ν)
```

## E1040-DENSITY - `Erdos1040.memLp_re_polynomial`

For every compact complex observation set K and every complex polynomial p, its real part is in actual planar-area L2 restricted to K.

Module: `Erdos1040.PolynomialDensity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.memLp_re_polynomial : ∀ {K : Set.{0} ℂ},
  IsCompact.{0} K →
    ∀ (p : Polynomial.{0} ℂ),
      MeasureTheory.MemLp.{0, 0} (fun z => (Polynomial.eval.{0} z p).re) 2
        (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K)
```

## E1040-DENSITY - `Erdos1040.inner_re_polynomial_toLp`

For every compact complex observation set K, complex polynomial p, and real area-L2 class h, the real Hilbert inner product with the L2 class of Re p equals the actual area integral of h times Re p.

Module: `Erdos1040.PolynomialDensity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.inner_re_polynomial_toLp : ∀ {K : Set.{0} ℂ} (hK : IsCompact.{0} K) (p : Polynomial.{0} ℂ)
  (h : ↥(MeasureTheory.Lp.{0, 0} ℝ 2 (MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} K))),
  Eq.{1} (Inner.inner.{0, 0} ℝ h (MeasureTheory.MemLp.toLp.{0, 0} (fun z => (Polynomial.eval.{0} z p).re) ⋯))
    (∫ (z : ℂ) in K, HMul.hMul.{0, 0, 0} (↑↑h z) (Polynomial.eval.{0} z p).re)
```

## E1040-DENSITY - `Erdos1040.exists_density_approx_re_polynomial`

Conditional density theorem: for compact source S contained in compact observation K, source probability mu, preconnected complement of K, frontier K contained in the mapped source support, and globally nonnegative actual logarithmic source potential, every complex polynomial whose actual real source mean is zero has its real part approximated in area-L2 norm by actual logarithmic potentials of bounded measurable real source densities, to every positive tolerance. The classical geometric and potential hypotheses are explicit remaining inputs; the annihilator conclusion is proved rather than assumed.

Module: `Erdos1040.PolynomialDensity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_density_approx_re_polynomial : ∀ {S K : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (hK : IsCompact.{0} K),
      S ⊆ K →
        ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsProbabilityMeasure.{0} μ],
          IsPreconnected.{0} (Compl.compl.{0} K) →
            frontier.{0} K ⊆ MeasureTheory.Measure.support.{0} (MeasureTheory.Measure.map.{0, 0} Subtype.val.{1} μ) →
              (∀ (z : ℂ), LE.le.{0} 0 (∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)) ∂μ)) →
                ∀ (p : Polynomial.{0} ℂ),
                  Eq.{1} (∫ (w : ↑S), (Polynomial.eval.{0} (↑w) p).re ∂μ) 0 →
                    ∀ (ε : ℝ),
                      LT.lt.{0} 0 ε →
                        ∃ f,
                          Measurable.{0, 0} f ∧
                            (∃ C, ∀ (w : ↑S), LE.le.{0} (Norm.norm.{0} (f w)) C) ∧
                              LT.lt.{0}
                                (Norm.norm.{0}
                                  (HSub.hSub.{0, 0, 0}
                                    (∫ (w : ↑S), HSMul.hSMul.{0, 0, 0} (f w) (Erdos1040.areaLogKernel hK ↑w) ∂μ)
                                    (MeasureTheory.MemLp.toLp.{0, 0} (fun z => (Polynomial.eval.{0} z p).re) ⋯)))
                                ε
```

## E1040-POSITIVE-DENSITY - `Erdos1040.shifted_density_mass_pos`

For every probability measure on an arbitrary measurable space, every measurable bounded real density f with pointwise norm at most C, and every real A greater than C, the actual integral of f plus A is strictly positive.

Module: `Erdos1040.PositiveDensity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.shifted_density_mass_pos.{u_1} : ∀ {X : Type u_1} [inst : MeasurableSpace.{u_1} X]
  (μ : MeasureTheory.Measure.{u_1} X) [MeasureTheory.IsProbabilityMeasure.{u_1} μ] (f : X → ℝ),
  Measurable.{u_1, 0} f →
    ∀ {C A : ℝ},
      (∀ (w : X), LE.le.{0} (Norm.norm.{0} (f w)) C) →
        LT.lt.{0} C A → LT.lt.{0} 0 (HAdd.hAdd.{0, 0, 0} (∫ (w : X), f w ∂μ) A)
```

## E1040-POSITIVE-DENSITY - `Erdos1040.isProbabilityMeasure_shifted_density`

Under the same probability, measurable density, pointwise bound C, and A greater than C hypotheses, weighting the original measure by ofReal((f+A)/(integral f+A)) constructs an actual probability measure.

Module: `Erdos1040.PositiveDensity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.isProbabilityMeasure_shifted_density.{u_1} : ∀ {X : Type u_1} [inst : MeasurableSpace.{u_1} X]
  (μ : MeasureTheory.Measure.{u_1} X) [MeasureTheory.IsProbabilityMeasure.{u_1} μ] (f : X → ℝ),
  Measurable.{u_1, 0} f →
    ∀ {C A : ℝ},
      (∀ (w : X), LE.le.{0} (Norm.norm.{0} (f w)) C) →
        LT.lt.{0} C A →
          MeasureTheory.IsProbabilityMeasure.{u_1}
            (MeasureTheory.Measure.withDensity.{u_1} μ fun w =>
              ENNReal.ofReal
                (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (f w) A) (HAdd.hAdd.{0, 0, 0} (∫ (w : X), f w ∂μ) A)))
```

## E1040-POSITIVE-DENSITY - `Erdos1040.integral_shifted_density`

For every complete real normed space E and every E-valued integrable kernel g, integration against the actual normalized shifted-density probability equals (integral f+A)^(-1) times the sum of the actual f-weighted kernel integral and A times the original kernel integral. The original measure is a probability and f is measurable with pointwise norm at most C less than A; positivity and normalization are proved, not assumed.

Module: `Erdos1040.PositiveDensity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integral_shifted_density.{u_1, u_2} : ∀ {X : Type u_1} {E : Type u_2} [inst : MeasurableSpace.{u_1} X]
  [inst_1 : NormedAddCommGroup.{u_2} E] [inst_2 : NormedSpace.{0, u_2} ℝ E] [CompleteSpace.{u_2} E]
  (μ : MeasureTheory.Measure.{u_1} X) [MeasureTheory.IsProbabilityMeasure.{u_1} μ] (f : X → ℝ),
  Measurable.{u_1, 0} f →
    ∀ {C A : ℝ},
      (∀ (w : X), LE.le.{0} (Norm.norm.{0} (f w)) C) →
        LT.lt.{0} C A →
          ∀ (g : X → E),
            MeasureTheory.Integrable.{u_2, u_1} g μ →
              Eq.{u_2 + 1}
                (∫ (w : X),
                  g
                    w ∂MeasureTheory.Measure.withDensity.{u_1} μ fun w =>
                    ENNReal.ofReal
                      (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (f w) A) (HAdd.hAdd.{0, 0, 0} (∫ (w : X), f w ∂μ) A)))
                (HSMul.hSMul.{0, u_2, u_2} (Inv.inv.{0} (HAdd.hAdd.{0, 0, 0} (∫ (w : X), f w ∂μ) A))
                  (HAdd.hAdd.{u_2, u_2, u_2} (∫ (w : X), HSMul.hSMul.{0, u_2, u_2} (f w) (g w) ∂μ)
                    (HSMul.hSMul.{0, u_2, u_2} A (∫ (w : X), g w ∂μ))))
```

## E1040-AREA-ASSEMBLY - `Erdos1040.unitLemniscate_subset_closedBall_of_roots_norm_le`

For every finite list of complex roots and every real M bounding all root norms, the strict unit lemniscate is contained in the closed disk centered at zero of radius M+1. This also holds for the empty list, whose strict unit lemniscate is empty.

Module: `Erdos1040.AtomicAreaAssembly`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.unitLemniscate_subset_closedBall_of_roots_norm_le : ∀ {n : ℕ} (roots : Fin n → ℂ) {M : ℝ},
  (∀ (i : Fin n), LE.le.{0} (Norm.norm.{0} (roots i)) M) →
    Erdos1040.unitLemniscate roots ⊆ Metric.closedBall.{0} 0 (HAdd.hAdd.{0, 0, 0} M 1)
```

## E1040-AREA-ASSEMBLY - `Erdos1040.exists_L2_tolerance_for_small_negative_set`

For any measure nu on the complex plane, real L2 function g, positive margin delta, and positive real area tolerance epsilon, if the nu-measure where g is less than delta is strictly below epsilon, then there exists a positive L2 norm tolerance such that every real L2 function f within this distance of g has negative-set nu-measure strictly below epsilon. No existence of a suitable g is asserted.

Module: `Erdos1040.AtomicAreaAssembly`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_L2_tolerance_for_small_negative_set : ∀ (ν : MeasureTheory.Measure.{0} ℂ) (g : ℂ → ℝ)
  (hg : MeasureTheory.MemLp.{0, 0} g 2 ν) (δ : NNReal),
  LT.lt.{0} 0 δ →
    ∀ (ε : ℝ),
      LT.lt.{0} 0 ε →
        LT.lt.{0} (ν (Set.ofPred.{0} fun z => LT.lt.{0} (g z) ↑δ)) (ENNReal.ofReal ε) →
          ∃ r,
            LT.lt.{0} 0 r ∧
              ∀ (f : ℂ → ℝ) (hf : MeasureTheory.MemLp.{0, 0} f 2 ν),
                LT.lt.{0}
                    (Norm.norm.{0}
                      (HSub.hSub.{0, 0, 0} (MeasureTheory.MemLp.toLp.{0, 0} f hf)
                        (MeasureTheory.MemLp.toLp.{0, 0} g hg)))
                    r →
                  LT.lt.{0} (ν (Set.ofPred.{0} fun z => LT.lt.{0} (f z) 0)) (ENNReal.ofReal ε)
```

## E1040-AREA-ASSEMBLY - `Erdos1040.exists_roots_small_area_of_source_margin`

For every compact complex source set S with all norms at most a real M, every probability measure mu on subtype S, positive margin delta, and positive real tolerance epsilon, if the planar area within the closed disk of radius M+1 where the actual logarithmic source potential is less than delta is strictly below epsilon, then a positive finite list of roots in S has strict unit lemniscate area below epsilon. The low-potential area bound is an explicit conditional hypothesis; no capacity or equilibrium condition is assumed or concluded.

Module: `Erdos1040.AtomicAreaAssembly`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_roots_small_area_of_source_margin : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ {M : ℝ},
      (∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Norm.norm.{0} w) M) →
        ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsProbabilityMeasure.{0} μ] (δ : NNReal),
          LT.lt.{0} 0 δ →
            ∀ (ε : ℝ),
              LT.lt.{0} 0 ε →
                LT.lt.{0}
                    ((MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0}
                        (Metric.closedBall.{0} 0 (HAdd.hAdd.{0, 0, 0} M 1)))
                      (Set.ofPred.{0} fun z =>
                        LT.lt.{0} (∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)) ∂μ) ↑δ))
                    (ENNReal.ofReal ε) →
                  ∃ n,
                    LT.lt.{0} 0 n ∧
                      ∃ roots,
                        (∀ (i : Fin n), Membership.mem.{0, 0} S (roots i)) ∧
                          LT.lt.{0} (MeasureTheory.MeasureSpace.volume.{0} (Erdos1040.unitLemniscate roots))
                            (ENNReal.ofReal ε)
```

## E1040-AREA-ASSEMBLY - `Erdos1040.hasArbitrarilySmallLemniscates_of_uniform_source_margin`

For every compact complex source set S with all norms at most a real M, if a probability measure on subtype S has actual logarithmic source potential at least a fixed positive margin at planar-almost-every point in the closed disk of radius M+1, then S satisfies HasArbitrarilySmallLemniscates. The positive-margin hypothesis remains explicit; this is not an unconditional capacity-one or capacity-greater-than-one theorem.

Module: `Erdos1040.AtomicAreaAssembly`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.hasArbitrarilySmallLemniscates_of_uniform_source_margin : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ {M : ℝ},
      (∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Norm.norm.{0} w) M) →
        ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsProbabilityMeasure.{0} μ] (δ : NNReal),
          LT.lt.{0} 0 δ →
            (∀ᵐ (z :
                ℂ) ∂MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0}
                  (Metric.closedBall.{0} 0 (HAdd.hAdd.{0, 0, 0} M 1)),
                LE.le.{0} (↑δ) (∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)) ∂μ)) →
              Erdos1040.HasArbitrarilySmallLemniscates S
```

## E1040-LOG-ENERGY - `Erdos1040.nonnegativeLogKernel_toReal_of_dist_le`

For positive real D and distinct complex z,w whose distance is at most D, the real value of nonnegativeLogKernel D z w is exactly log D minus log of their distance. The distance bound removes nonnegative clipping and distinctness removes the infinite diagonal.

Module: `Erdos1040.LogEnergyIntegrability`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.nonnegativeLogKernel_toReal_of_dist_le : ∀ {D : ℝ},
  LT.lt.{0} 0 D →
    ∀ {z w : ℂ},
      Ne.{1} z w →
        LE.le.{0} (Dist.dist.{0} z w) D →
          Eq.{1} (Erdos1040.nonnegativeLogKernel D z w).toReal
            (HSub.hSub.{0, 0, 0} (Real.log D) (Real.log (Dist.dist.{0} z w)))
```

## E1040-LOG-ENERGY - `Erdos1040.ae_ne_of_finite_nonnegativeLogEnergy`

For positive real D and any Borel probability measure mu on a planar source subtype, finiteness of its actual nonnegativeLogEnergy implies that the two complex source coordinates are unequal for mu-times-mu almost every pair.

Module: `Erdos1040.LogEnergyIntegrability`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.ae_ne_of_finite_nonnegativeLogEnergy : ∀ {S : Set.{0} ℂ} {D : ℝ},
  LT.lt.{0} 0 D →
    ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
      Ne.{1} (Erdos1040.nonnegativeLogEnergy D μ) Top.top.{0} →
        ∀ᵐ (p : Prod.{0, 0} ↑S ↑S) ∂↑(MeasureTheory.ProbabilityMeasure.prod.{0, 0} μ μ), Ne.{1} ↑p.1 ↑p.2
```

## E1040-LOG-ENERGY - `Erdos1040.nullSingletonClass_of_finite_nonnegativeLogEnergy`

For positive real D, every probability measure with finite actual nonnegativeLogEnergy assigns zero mass to every singleton of its source subtype. This is the exact NullSingletonClass conclusion.

Module: `Erdos1040.LogEnergyIntegrability`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.nullSingletonClass_of_finite_nonnegativeLogEnergy : ∀ {S : Set.{0} ℂ} {D : ℝ},
  LT.lt.{0} 0 D →
    ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
      Ne.{1} (Erdos1040.nonnegativeLogEnergy D μ) Top.top.{0} → MeasureTheory.NullSingletonClass.{0} ↑μ
```

## E1040-LOG-ENERGY - `Erdos1040.integrable_log_dist_prod_of_finite_nonnegativeLogEnergy`

For positive real D bounding all pair distances in a planar source S, a Borel probability measure on S with finite actual nonnegativeLogEnergy has an absolutely integrable real log-distance kernel under its product measure. The infinite energy diagonal is first proved product-null.

Module: `Erdos1040.LogEnergyIntegrability`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integrable_log_dist_prod_of_finite_nonnegativeLogEnergy : ∀ {S : Set.{0} ℂ} {D : ℝ},
  LT.lt.{0} 0 D →
    (∀ (z : ℂ), Membership.mem.{0, 0} S z → ∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) D) →
      ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
        Ne.{1} (Erdos1040.nonnegativeLogEnergy D μ) Top.top.{0} →
          MeasureTheory.Integrable.{0, 0} (fun p => Real.log (Dist.dist.{0} ↑p.1 ↑p.2))
            ↑(MeasureTheory.ProbabilityMeasure.prod.{0, 0} μ μ)
```

## E1040-LOG-ENERGY - `Erdos1040.nonnegativeLogEnergy_toReal_eq_log_sub_integral`

For positive real D bounding every pair distance in a planar source S, and a Borel probability measure mu on S with finite actual nonnegativeLogEnergy, its real energy equals log D minus the actual integral of log distance under mu times mu. This supplies the finite-energy sign and scale conversion to classical negative-log energy without assigning finite energy to point masses.

Module: `Erdos1040.LogEnergyIntegrability`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.nonnegativeLogEnergy_toReal_eq_log_sub_integral : ∀ {S : Set.{0} ℂ} {D : ℝ},
  LT.lt.{0} 0 D →
    (∀ (z : ℂ), Membership.mem.{0, 0} S z → ∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) D) →
      ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
        Ne.{1} (Erdos1040.nonnegativeLogEnergy D μ) Top.top.{0} →
          Eq.{1} (Erdos1040.nonnegativeLogEnergy D μ).toReal
            (HSub.hSub.{0, 0, 0} (Real.log D)
              (∫ (p : Prod.{0, 0} ↑S ↑S),
                Real.log (Dist.dist.{0} ↑p.1 ↑p.2) ∂↑(MeasureTheory.ProbabilityMeasure.prod.{0, 0} μ μ)))
```

## E1040-ENERGY-VARIATION - `Erdos1040.probabilityMixture`

For every measurable space, two probability measures mu and nu, and a real t with 0<=t<=1, probabilityMixture is the probability measure whose actual underlying measure is ofReal(1-t) times mu plus ofReal(t) times nu.

Module: `Erdos1040.EnergyVariation`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.probabilityMixture.{u_1} : {Ω : Type u_1} →
  [inst : MeasurableSpace.{u_1} Ω] →
    MeasureTheory.ProbabilityMeasure.{u_1} Ω →
      MeasureTheory.ProbabilityMeasure.{u_1} Ω →
        (t : ℝ) → LE.le.{0} 0 t → LE.le.{0} t 1 → MeasureTheory.ProbabilityMeasure.{u_1} Ω
```

## E1040-ENERGY-VARIATION - `Erdos1040.nonnegativeLogCrossEnergy`

For every complex source set S, real scale D, and source probabilities mu and nu, nonnegativeLogCrossEnergy is the actual extended nonnegative integral of nonnegativeLogKernel D over the product probability mu times nu, retaining infinite values.

Module: `Erdos1040.EnergyVariation`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.nonnegativeLogCrossEnergy : {S : Set.{0} ℂ} →
  ℝ → MeasureTheory.ProbabilityMeasure.{0} ↑S → MeasureTheory.ProbabilityMeasure.{0} ↑S → ENNReal
```

## E1040-ENERGY-VARIATION - `Erdos1040.nonnegativeLogCrossEnergy_comm`

The actual extended nonnegative logarithmic cross energy is symmetric in its two source probabilities, including infinite values.

Module: `Erdos1040.EnergyVariation`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.nonnegativeLogCrossEnergy_comm : ∀ {S : Set.{0} ℂ} (D : ℝ)
  (μ ν : MeasureTheory.ProbabilityMeasure.{0} ↑S),
  Eq.{1} (Erdos1040.nonnegativeLogCrossEnergy D μ ν) (Erdos1040.nonnegativeLogCrossEnergy D ν μ)
```

## E1040-ENERGY-VARIATION - `Erdos1040.nonnegativeLogEnergy_probabilityMixture`

For every source set, real scale, two source probabilities, and 0<=t<=1, the actual extended energy of the probability mixture is ofReal(1-t)^2 E(mu) + 2 ofReal(1-t) ofReal(t) cross(mu,nu) + ofReal(t)^2 E(nu). This identity includes infinite energies without conversion to real numbers.

Module: `Erdos1040.EnergyVariation`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.nonnegativeLogEnergy_probabilityMixture : ∀ {S : Set.{0} ℂ} (D : ℝ)
  (μ ν : MeasureTheory.ProbabilityMeasure.{0} ↑S) (t : ℝ) (ht0 : LE.le.{0} 0 t) (ht1 : LE.le.{0} t 1),
  Eq.{1} (Erdos1040.nonnegativeLogEnergy D (Erdos1040.probabilityMixture.{0} μ ν t ht0 ht1))
    (HAdd.hAdd.{0, 0, 0}
      (HAdd.hAdd.{0, 0, 0}
        (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (ENNReal.ofReal (HSub.hSub.{0, 0, 0} 1 t)) 2)
          (Erdos1040.nonnegativeLogEnergy D μ))
        (HMul.hMul.{0, 0, 0}
          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 (ENNReal.ofReal (HSub.hSub.{0, 0, 0} 1 t))) (ENNReal.ofReal t))
          (Erdos1040.nonnegativeLogCrossEnergy D μ ν)))
      (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (ENNReal.ofReal t) 2) (Erdos1040.nonnegativeLogEnergy D ν)))
```

## E1040-ENERGY-VARIATION - `Erdos1040.toReal_nonnegativeLogEnergy_probabilityMixture`

Under explicit finiteness of both self-energies and the cross energy, the toReal value of the actual mixture energy equals (1-t)^2 E(mu).toReal + 2(1-t)t cross(mu,nu).toReal + t^2 E(nu).toReal for 0<=t<=1.

Module: `Erdos1040.EnergyVariation`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.toReal_nonnegativeLogEnergy_probabilityMixture : ∀ {S : Set.{0} ℂ} (D : ℝ)
  (μ ν : MeasureTheory.ProbabilityMeasure.{0} ↑S),
  Ne.{1} (Erdos1040.nonnegativeLogEnergy D μ) Top.top.{0} →
    Ne.{1} (Erdos1040.nonnegativeLogEnergy D ν) Top.top.{0} →
      Ne.{1} (Erdos1040.nonnegativeLogCrossEnergy D μ ν) Top.top.{0} →
        ∀ (t : ℝ) (ht0 : LE.le.{0} 0 t) (ht1 : LE.le.{0} t 1),
          Eq.{1} (Erdos1040.nonnegativeLogEnergy D (Erdos1040.probabilityMixture.{0} μ ν t ht0 ht1)).toReal
            (HAdd.hAdd.{0, 0, 0}
              (HAdd.hAdd.{0, 0, 0}
                (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (HSub.hSub.{0, 0, 0} 1 t) 2)
                  (Erdos1040.nonnegativeLogEnergy D μ).toReal)
                (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 (HSub.hSub.{0, 0, 0} 1 t)) t)
                  (Erdos1040.nonnegativeLogCrossEnergy D μ ν).toReal))
              (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} t 2) (Erdos1040.nonnegativeLogEnergy D ν).toReal))
```

## E1040-ENERGY-VARIATION - `Erdos1040.nonnegativeLogEnergy_le_crossEnergy_of_minimizer`

For every source set and real scale, if mu globally minimizes the actual nonnegative logarithmic energy among all source probabilities and its energy is finite, then its self-energy is at most its cross energy with every finite-self-energy probability competitor nu. Cross finiteness is not assumed or inferred: the infinite-cross case is handled directly and the finite case uses the checked quadratic variation formula. No Frostman statement or classical untruncated-energy correspondence is asserted.

Module: `Erdos1040.EnergyVariation`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.nonnegativeLogEnergy_le_crossEnergy_of_minimizer : ∀ {S : Set.{0} ℂ} (D : ℝ)
  (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
  Ne.{1} (Erdos1040.nonnegativeLogEnergy D μ) Top.top.{0} →
    (∀ (ρ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
        LE.le.{0} (Erdos1040.nonnegativeLogEnergy D μ) (Erdos1040.nonnegativeLogEnergy D ρ)) →
      ∀ (ν : MeasureTheory.ProbabilityMeasure.{0} ↑S),
        Ne.{1} (Erdos1040.nonnegativeLogEnergy D ν) Top.top.{0} →
          LE.le.{0} (Erdos1040.nonnegativeLogEnergy D μ) (Erdos1040.nonnegativeLogCrossEnergy D μ ν)
```

## E1040-CONDITIONAL-LEMNISCATE - `Erdos1040.exists_L2_tolerance_for_small_sublevel_set`

For any finite measure on the complex plane, real L2 function g, real threshold a, positive margin delta, and positive tolerance epsilon, if the measure where g is below a+delta is below epsilon, then all real L2 functions sufficiently close to g have their sublevel-set measure below threshold a less than epsilon.

Module: `Erdos1040.ConditionalLemniscate`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_L2_tolerance_for_small_sublevel_set : ∀ (ν : MeasureTheory.Measure.{0} ℂ)
  [MeasureTheory.IsFiniteMeasure.{0} ν] (g : ℂ → ℝ) (hg : MeasureTheory.MemLp.{0, 0} g 2 ν) (a : ℝ) (δ : NNReal),
  LT.lt.{0} 0 δ →
    ∀ (ε : ℝ),
      LT.lt.{0} 0 ε →
        LT.lt.{0} (ν (Set.ofPred.{0} fun z => LT.lt.{0} (g z) (HAdd.hAdd.{0, 0, 0} a ↑δ))) (ENNReal.ofReal ε) →
          ∃ r,
            LT.lt.{0} 0 r ∧
              ∀ (f : ℂ → ℝ) (hf : MeasureTheory.MemLp.{0, 0} f 2 ν),
                LT.lt.{0}
                    (Norm.norm.{0}
                      (HSub.hSub.{0, 0, 0} (MeasureTheory.MemLp.toLp.{0, 0} f hf)
                        (MeasureTheory.MemLp.toLp.{0, 0} g hg)))
                    r →
                  LT.lt.{0} (ν (Set.ofPred.{0} fun z => LT.lt.{0} (f z) a)) (ENNReal.ofReal ε)
```

## E1040-CONDITIONAL-LEMNISCATE - `Erdos1040.exists_large_shift_small_exterior_set`

For any finite measure on the complex plane, measurable set K, almost-everywhere measurable real functions U and V, and pointwise strictly positive U outside K, every real lower bound C, real threshold t, and positive tolerance epsilon admit a positive real A greater than C such that the measure of points outside K where V+A U is below t is less than epsilon. This follows from decreasing-set measure continuity and requires no boundary collar regularity.

Module: `Erdos1040.ConditionalLemniscate`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_large_shift_small_exterior_set : ∀ (ν : MeasureTheory.Measure.{0} ℂ)
  [MeasureTheory.IsFiniteMeasure.{0} ν] (K : Set.{0} ℂ),
  MeasurableSet.{0} K →
    ∀ (U V : ℂ → ℝ),
      AEMeasurable.{0, 0} U ν →
        AEMeasurable.{0, 0} V ν →
          (∀ z ∉ K, LT.lt.{0} 0 (U z)) →
            ∀ (C t ε : ℝ),
              LT.lt.{0} 0 ε →
                ∃ A,
                  LT.lt.{0} C A ∧
                    LT.lt.{0} 0 A ∧
                      LT.lt.{0}
                        (ν
                          (Set.ofPred.{0} fun z =>
                            z ∉ K ∧ LT.lt.{0} (HAdd.hAdd.{0, 0, 0} (V z) (HMul.hMul.{0, 0, 0} A (U z))) t))
                        (ENNReal.ofReal ε)
```

## E1040-CONDITIONAL-LEMNISCATE - `Erdos1040.shifted_source_potential_ae_eq`

For compact complex source and observation sets S and D, a probability mu on subtype S, a bounded measurable real density f with pointwise norm bound C, and A greater than C, the actual source potential of the probability with density (f+A)/(integral(f)+A) equals (V_f+A U_mu)/(integral(f)+A) almost everywhere for planar area restricted to D. All potentials are actual totalized real logarithmic source integrals; source integrability is obtained almost everywhere from the product-integrability theorem.

Module: `Erdos1040.ConditionalLemniscate`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.shifted_source_potential_ae_eq : ∀ {S D : Set.{0} ℂ},
  IsCompact.{0} S →
    IsCompact.{0} D →
      ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsProbabilityMeasure.{0} μ] (f : ↑S → ℝ),
        Measurable.{0, 0} f →
          ∀ {C A : ℝ},
            (∀ (w : ↑S), LE.le.{0} (Norm.norm.{0} (f w)) C) →
              LT.lt.{0} C A →
                (fun z =>
                    ∫ (w : ↑S),
                      Real.log
                        (Norm.norm.{0}
                          (HSub.hSub.{0, 0, 0} z
                            ↑w)) ∂MeasureTheory.Measure.withDensity.{0} μ fun w =>
                        ENNReal.ofReal
                          (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (f w) A)
                            (HAdd.hAdd.{0, 0, 0} (∫ (w : ↑S), f w ∂μ)
                              A))) =ᵐ[MeasureTheory.Measure.restrict.{0} MeasureTheory.MeasureSpace.volume.{0} D]
                  fun z =>
                  HMul.hMul.{0, 0, 0} (Inv.inv.{0} (HAdd.hAdd.{0, 0, 0} (∫ (w : ↑S), f w ∂μ) A))
                    (HAdd.hAdd.{0, 0, 0}
                      (∫ (w : ↑S), HMul.hMul.{0, 0, 0} (f w) (Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ∂μ)
                      (HMul.hMul.{0, 0, 0} A (∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)) ∂μ)))
```

## E1040-LOG-ENERGY - `Erdos1040.nonnegativeLogKernel_scale_change`

For all positive real D at most E and all complex z,w with dist(z,w) at most D, the extended nonnegative kernel at E equals its value at D plus ofReal(log(E/D)). This includes the diagonal, where both kernels are positive infinity.

Module: `Erdos1040.LogEnergyScale`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.nonnegativeLogKernel_scale_change : ∀ {D E : ℝ},
  LT.lt.{0} 0 D →
    LE.le.{0} D E →
      ∀ {z w : ℂ},
        LE.le.{0} (Dist.dist.{0} z w) D →
          Eq.{1} (Erdos1040.nonnegativeLogKernel E z w)
            (HAdd.hAdd.{0, 0, 0} (Erdos1040.nonnegativeLogKernel D z w)
              (ENNReal.ofReal (Real.log (HDiv.hDiv.{0, 0, 0} E D))))
```

## E1040-LOG-ENERGY - `Erdos1040.nonnegativeLogEnergy_scale_change`

For every probability measure on a complex source set whose pair distances are at most positive D, and every E at least D, the actual extended nonnegative energy at E equals its energy at D plus ofReal(log(E/D)), including infinite energy.

Module: `Erdos1040.LogEnergyScale`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.nonnegativeLogEnergy_scale_change : ∀ {S : Set.{0} ℂ} {D E : ℝ},
  LT.lt.{0} 0 D →
    LE.le.{0} D E →
      (∀ (z : ℂ), Membership.mem.{0, 0} S z → ∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) D) →
        ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
          Eq.{1} (Erdos1040.nonnegativeLogEnergy E μ)
            (HAdd.hAdd.{0, 0, 0} (Erdos1040.nonnegativeLogEnergy D μ)
              (ENNReal.ofReal (Real.log (HDiv.hDiv.{0, 0, 0} E D))))
```

## E1040-LOG-ENERGY - `Erdos1040.finite_nonnegativeLogEnergy_scale_iff`

For any two positive real scales D,E both bounding every source pair distance, and every probability measure on that source, the energy at D is finite if and only if the energy at E is finite. No compactness or finite-energy assumption is inserted.

Module: `Erdos1040.LogEnergyScale`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.finite_nonnegativeLogEnergy_scale_iff : ∀ {S : Set.{0} ℂ} {D E : ℝ},
  LT.lt.{0} 0 D →
    LT.lt.{0} 0 E →
      (∀ (z : ℂ), Membership.mem.{0, 0} S z → ∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) D) →
        (∀ (z : ℂ),
            Membership.mem.{0, 0} S z → ∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) E) →
          ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
            Ne.{1} (Erdos1040.nonnegativeLogEnergy D μ) Top.top.{0} ↔
              Ne.{1} (Erdos1040.nonnegativeLogEnergy E μ) Top.top.{0}
```

## E1040-LOG-ENERGY - `Erdos1040.nonnegativeLogEnergy_normalized_scale_independent`

For any two positive scales D,E both bounding every source pair distance and every probability measure on that source, embedding the extended nonnegative energy in EReal and subtracting log of its scale gives the same EReal value at D and E. Infinite energy stays positive infinity.

Module: `Erdos1040.LogEnergyScale`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.nonnegativeLogEnergy_normalized_scale_independent : ∀ {S : Set.{0} ℂ} {D E : ℝ},
  LT.lt.{0} 0 D →
    LT.lt.{0} 0 E →
      (∀ (z : ℂ), Membership.mem.{0, 0} S z → ∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) D) →
        (∀ (z : ℂ),
            Membership.mem.{0, 0} S z → ∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) E) →
          ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
            Eq.{1} (HSub.hSub.{0, 0, 0} ↑(Erdos1040.nonnegativeLogEnergy D μ) ↑(Real.log D))
              (HSub.hSub.{0, 0, 0} ↑(Erdos1040.nonnegativeLogEnergy E μ) ↑(Real.log E))
```

## E1040-LOG-ENERGY - `Erdos1040.minimizer_nonnegativeLogEnergy_scale_iff`

For any two positive scales D,E both bounding every source pair distance and any source probability mu, mu minimizes the actual extended energy among all source probabilities at D if and only if it minimizes it at E, including the case where every energy is infinite.

Module: `Erdos1040.LogEnergyScale`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.minimizer_nonnegativeLogEnergy_scale_iff : ∀ {S : Set.{0} ℂ} {D E : ℝ},
  LT.lt.{0} 0 D →
    LT.lt.{0} 0 E →
      (∀ (z : ℂ), Membership.mem.{0, 0} S z → ∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) D) →
        (∀ (z : ℂ),
            Membership.mem.{0, 0} S z → ∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) E) →
          ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
            (∀ (ν : MeasureTheory.ProbabilityMeasure.{0} ↑S),
                LE.le.{0} (Erdos1040.nonnegativeLogEnergy D μ) (Erdos1040.nonnegativeLogEnergy D ν)) ↔
              ∀ (ν : MeasureTheory.ProbabilityMeasure.{0} ↑S),
                LE.le.{0} (Erdos1040.nonnegativeLogEnergy E μ) (Erdos1040.nonnegativeLogEnergy E ν)
```

## E1040-ENERGY-FROSTMAN - `Erdos1040.nonnegativeLogPotential`

For every complex source set S, real scale D, probability mu on S, and complex observation z, this is the actual extended nonnegative integral of nonnegativeLogKernel D z w against mu.

Module: `Erdos1040.EnergyFrostman`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.nonnegativeLogPotential : {S : Set.{0} ℂ} → ℝ → MeasureTheory.ProbabilityMeasure.{0} ↑S → ℂ → ENNReal
```

## E1040-ENERGY-FROSTMAN - `Erdos1040.HasNoFiniteLogEnergyProbability`

For a source-subtype set A and scale D, every source probability nu almost everywhere carried by A has infinite actual nonnegative logarithmic energy. This predicate is not identified with an unformalized classical polar-set definition.

Module: `Erdos1040.EnergyFrostman`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.HasNoFiniteLogEnergyProbability : {S : Set.{0} ℂ} → ℝ → Set.{0} ↑S → Prop
```

## E1040-ENERGY-FROSTMAN - `Erdos1040.measurable_nonnegativeLogPotential`

The actual extended potential is measurable as a function of every complex observation.

Module: `Erdos1040.EnergyFrostman`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.measurable_nonnegativeLogPotential : ∀ {S : Set.{0} ℂ} (D : ℝ)
  (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S), Measurable.{0, 0} (Erdos1040.nonnegativeLogPotential D μ)
```

## E1040-ENERGY-FROSTMAN - `Erdos1040.nonnegativeLogCrossEnergy_eq_lintegral_potential`

For every pair of source probabilities, their actual extended cross energy equals the extended integral of the first potential against the second probability, including infinite values.

Module: `Erdos1040.EnergyFrostman`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.nonnegativeLogCrossEnergy_eq_lintegral_potential : ∀ {S : Set.{0} ℂ} (D : ℝ)
  (μ ν : MeasureTheory.ProbabilityMeasure.{0} ↑S),
  Eq.{1} (Erdos1040.nonnegativeLogCrossEnergy D μ ν) (∫⁻ (z : ↑S), Erdos1040.nonnegativeLogPotential D μ ↑z ∂↑ν)
```

## E1040-ENERGY-FROSTMAN - `Erdos1040.hasNoFiniteLogEnergyProbability_sublevel_of_minimizer`

For every finite global minimizer mu of the actual nonnegative logarithmic energy, the source set where its actual potential is strictly below its energy carries no finite-energy source probability.

Module: `Erdos1040.EnergyFrostman`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.hasNoFiniteLogEnergyProbability_sublevel_of_minimizer : ∀ {S : Set.{0} ℂ} (D : ℝ)
  (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
  Ne.{1} (Erdos1040.nonnegativeLogEnergy D μ) Top.top.{0} →
    (∀ (ρ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
        LE.le.{0} (Erdos1040.nonnegativeLogEnergy D μ) (Erdos1040.nonnegativeLogEnergy D ρ)) →
      Erdos1040.HasNoFiniteLogEnergyProbability D
        (Set.ofPred.{0} fun z =>
          LT.lt.{0} (Erdos1040.nonnegativeLogPotential D μ ↑z) (Erdos1040.nonnegativeLogEnergy D μ))
```

## E1040-ENERGY-FROSTMAN - `Erdos1040.probabilityRestriction`

For every measurable space, probability mu, and set A with mu(A) nonzero, this is the actual normalized restriction, with underlying measure mu(A) inverse times mu restricted to A.

Module: `Erdos1040.EnergyFrostman`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.probabilityRestriction.{u_1} : {Ω : Type u_1} →
  [inst : MeasurableSpace.{u_1} Ω] →
    (μ : MeasureTheory.ProbabilityMeasure.{u_1} Ω) →
      (A : Set.{u_1} Ω) → Ne.{1} (↑μ A) 0 → MeasureTheory.ProbabilityMeasure.{u_1} Ω
```

## E1040-ENERGY-FROSTMAN - `Erdos1040.finite_nonnegativeLogEnergy_probabilityRestriction`

Every positive-measure normalized restriction of a finite-energy source probability has finite actual energy, proved by domination of restricted product measures.

Module: `Erdos1040.EnergyFrostman`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.finite_nonnegativeLogEnergy_probabilityRestriction : ∀ {S : Set.{0} ℂ} (D : ℝ)
  (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
  Ne.{1} (Erdos1040.nonnegativeLogEnergy D μ) Top.top.{0} →
    ∀ (A : Set.{0} ↑S) (hA : Ne.{1} (↑μ A) 0),
      Ne.{1} (Erdos1040.nonnegativeLogEnergy D (Erdos1040.probabilityRestriction.{0} μ A hA)) Top.top.{0}
```

## E1040-ENERGY-FROSTMAN - `Erdos1040.measure_eq_zero_of_hasNoFiniteLogEnergyProbability`

Every measurable source set carrying no finite-energy source probability has measure zero for every finite-energy source probability.

Module: `Erdos1040.EnergyFrostman`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.measure_eq_zero_of_hasNoFiniteLogEnergyProbability : ∀ {S : Set.{0} ℂ} (D : ℝ)
  (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
  Ne.{1} (Erdos1040.nonnegativeLogEnergy D μ) Top.top.{0} →
    ∀ {A : Set.{0} ↑S}, MeasurableSet.{0} A → Erdos1040.HasNoFiniteLogEnergyProbability D A → Eq.{1} (↑μ A) 0
```

## E1040-ENERGY-FROSTMAN - `Erdos1040.nonnegativeLogPotential_ae_eq_energy_of_minimizer`

For every finite global minimizer mu of the actual nonnegative logarithmic energy, its actual extended source potential equals its energy mu-almost everywhere on S. This uses the proved exceptional-set inequality, finite normalized restrictions, and exact potential/energy integration; no Frostman premise is assumed.

Module: `Erdos1040.EnergyFrostman`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.nonnegativeLogPotential_ae_eq_energy_of_minimizer : ∀ {S : Set.{0} ℂ} (D : ℝ)
  (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
  Ne.{1} (Erdos1040.nonnegativeLogEnergy D μ) Top.top.{0} →
    (∀ (ρ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
        LE.le.{0} (Erdos1040.nonnegativeLogEnergy D μ) (Erdos1040.nonnegativeLogEnergy D ρ)) →
      (fun z => Erdos1040.nonnegativeLogPotential D μ ↑z) =ᵐ[↑μ] fun x => Erdos1040.nonnegativeLogEnergy D μ
```

## E1040-CONDITIONAL-LEMNISCATE - `Erdos1040.hasArbitrarilySmallLemniscates_of_potential_properties`

For compact complex source S contained in compact K, a probability mu on subtype S, a preconnected complement of K, and frontier K contained in the support of mu mapped into the plane, if the actual positive-logarithm source potential is nonnegative everywhere and strictly positive outside K, then S has arbitrarily small strict unit-lemniscate area with positive-degree monic polynomials whose roots are all in S. The source-support, topology and global potential inequalities are explicit hypotheses still to be derived from the original transfinite-diameter condition. No zero-potential-on-K, collar regularity, source smoothness, or degree bound is assumed.

Module: `Erdos1040.ConditionalLemniscate`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.hasArbitrarilySmallLemniscates_of_potential_properties : ∀ {S K : Set.{0} ℂ},
  IsCompact.{0} S →
    IsCompact.{0} K →
      S ⊆ K →
        ∀ (μ : MeasureTheory.Measure.{0} ↑S) [MeasureTheory.IsProbabilityMeasure.{0} μ],
          IsPreconnected.{0} (Compl.compl.{0} K) →
            frontier.{0} K ⊆ MeasureTheory.Measure.support.{0} (MeasureTheory.Measure.map.{0, 0} Subtype.val.{1} μ) →
              (∀ (z : ℂ), LE.le.{0} 0 (∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)) ∂μ)) →
                (∀ z ∉ K, LT.lt.{0} 0 (∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)) ∂μ)) →
                  Erdos1040.HasArbitrarilySmallLemniscates S
```

## E1040-TRUNCATED-ENERGY - `Erdos1040.truncatedLogEnergy`

For a complex source set S, real scale D, natural truncation n and probability mu on S, truncatedLogEnergy is the actual extended integral over mu times mu of the minimum of nonnegativeLogKernel D and n. This keeps the full energy separate from every finite truncation.

Module: `Erdos1040.TruncatedEnergy`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.truncatedLogEnergy : {S : Set.{0} ℂ} → ℝ → ℕ → MeasureTheory.ProbabilityMeasure.{0} ↑S → ENNReal
```

## E1040-TRUNCATED-ENERGY - `Erdos1040.lowerSemicontinuous_truncatedLogEnergy`

For each compact complex source, real scale and natural truncation, the actual truncated energy is lower semicontinuous on the source probability space with its weak topology.

Module: `Erdos1040.TruncatedEnergy`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.lowerSemicontinuous_truncatedLogEnergy : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S → ∀ (D : ℝ) (n : ℕ), LowerSemicontinuous.{0, 0} (Erdos1040.truncatedLogEnergy D n)
```

## E1040-TRUNCATED-ENERGY - `Erdos1040.nonnegativeLogEnergy_eq_iSup_truncated`

For every complex source, real scale and source probability, its actual full extended logarithmic energy equals the supremum over all natural finite kernel truncations of their actual energies, including infinite full energy.

Module: `Erdos1040.TruncatedEnergy`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.nonnegativeLogEnergy_eq_iSup_truncated : ∀ {S : Set.{0} ℂ} (D : ℝ)
  (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
  Eq.{1} (Erdos1040.nonnegativeLogEnergy D μ) (⨆ n, Erdos1040.truncatedLogEnergy D n μ)
```

## E1040-TRUNCATED-ENERGY - `Erdos1040.exists_probability_energy_le_of_truncated_bounds`

For a compact complex source, real scale D and extended nonnegative bound B, if each natural kernel truncation has some source probability of truncated energy at most B, then one source probability has full actual logarithmic energy at most B. The probability may depend on the truncation in the hypothesis; compact nested sublevel sets produce a single probability in the conclusion. No finite full energy for atomic approximants is assumed.

Module: `Erdos1040.TruncatedEnergy`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_probability_energy_le_of_truncated_bounds : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (D : ℝ) (B : ENNReal),
      (∀ (n : ℕ), ∃ μ, LE.le.{0} (Erdos1040.truncatedLogEnergy D n μ) B) →
        ∃ μ, LE.le.{0} (Erdos1040.nonnegativeLogEnergy D μ) B
```

## E1040-TRUNCATED-ENERGY - `Erdos1040.exists_probability_energy_le_of_approx_truncated_bounds`

For a compact complex source, real scale D and extended nonnegative bound B, if every natural kernel truncation and every positive real nonnegative error admit some source probability with truncated energy at most B plus that error, then one source probability has full actual logarithmic energy at most B. The proof uses attained truncated minima and nested compact sublevels; it does not require the approximating probabilities to have finite full energy.

Module: `Erdos1040.TruncatedEnergy`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_probability_energy_le_of_approx_truncated_bounds : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (D : ℝ) (B : ENNReal),
      (∀ (n : ℕ) (ε : NNReal),
          LT.lt.{0} 0 ε → ∃ μ, LE.le.{0} (Erdos1040.truncatedLogEnergy D n μ) (HAdd.hAdd.{0, 0, 0} B ↑ε)) →
        ∃ μ, LE.le.{0} (Erdos1040.nonnegativeLogEnergy D μ) B
```

## E1040-EMPIRICAL-ENERGY - `Erdos1040.empiricalSourceProbability`

For every positive natural N and list of N points in a complex source subtype S, empiricalSourceProbability is the actual probability measure with mass 1/N at each listed point, including multiplicities.

Module: `Erdos1040.EmpiricalEnergy`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.empiricalSourceProbability : {S : Set.{0} ℂ} →
  {N : ℕ} → (Fin N → ↑S) → LT.lt.{0} 0 N → MeasureTheory.ProbabilityMeasure.{0} ↑S
```

## E1040-EMPIRICAL-ENERGY - `Erdos1040.lintegral_empiricalSourceProbability`

For every positive source list and every extended nonnegative source function, its actual integral under the empirical probability is the equally weighted sum of its values on the list, including infinite values.

Module: `Erdos1040.EmpiricalEnergy`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.lintegral_empiricalSourceProbability : ∀ {S : Set.{0} ℂ} {N : ℕ} (roots : Fin N → ↑S)
  (hN : LT.lt.{0} 0 N) (f : ↑S → ENNReal),
  Eq.{1} (∫⁻ (w : ↑S), f w ∂↑(Erdos1040.empiricalSourceProbability roots hN))
    (HMul.hMul.{0, 0, 0} (Inv.inv.{0} ↑N) (∑ i, f (roots i)))
```

## E1040-EMPIRICAL-ENERGY - `Erdos1040.truncatedLogEnergy_empirical`

For every positive finite source list, real scale and natural truncation n, the actual truncated energy of its empirical probability equals N^(-2) times the full ordered double sum of min(nonnegativeLogKernel,n), including the diagonal. No diagonal terms are silently removed, and no finite untruncated energy is asserted.

Module: `Erdos1040.EmpiricalEnergy`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.truncatedLogEnergy_empirical : ∀ {S : Set.{0} ℂ} {N : ℕ} (roots : Fin N → ↑S) (hN : LT.lt.{0} 0 N)
  (D : ℝ) (n : ℕ),
  Eq.{1} (Erdos1040.truncatedLogEnergy D n (Erdos1040.empiricalSourceProbability roots hN))
    (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Inv.inv.{0} ↑N) 2)
      (∑ i, ∑ j, Min.min.{0} (Erdos1040.nonnegativeLogKernel D ↑(roots i) ↑(roots j)) ↑n))
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.unorderedPairProduct`

For any finite tuple of complex points, unorderedPairProduct is the product of the Euclidean distances over index pairs i<j. Multiplicities are retained; a repeated point makes an applicable pair factor zero. Empty pair products equal one.

Module: `Erdos1040.GeometricDiameter`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.unorderedPairProduct : {N : ℕ} → (Fin N → ℂ) → ℝ
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.geometricMeanSeparation`

For a tuple of N complex points, geometricMeanSeparation is the real unordered pair-distance product raised to the exact real exponent 2/(N(N-1)). The classical definition applies for N at least 2; at N=0 or 1 the totalized exponent is zero and the empty product gives one.

Module: `Erdos1040.GeometricDiameter`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.geometricMeanSeparation : {N : ℕ} → (Fin N → ℂ) → ℝ
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.finiteDiameter`

For any complex source set S and natural order N, finiteDiameter is the extended nonnegative supremum over all tuples Fin N to S of their exact geometricMeanSeparation. For compact nonempty sources and N at least 2 the supremum is proved to be an attained finite maximum. The extended supremum preserves unbounded values instead of replacing them by a finite default.

Module: `Erdos1040.GeometricDiameter`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.finiteDiameter : Set.{0} ℂ → ℕ → ENNReal
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.transfiniteDiameter`

For any complex source set S, transfiniteDiameter is the extended nonnegative infimum over n of finiteDiameter S (n+2), excluding the degenerate orders zero and one. The separate antitonicity and convergence theorems are required to identify this definition with the classical decreasing limit; it is defined using geometric distance products, not an assumed capacity or energy predicate.

Module: `Erdos1040.GeometricDiameter`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.transfiniteDiameter : Set.{0} ℂ → ENNReal
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.continuous_unorderedPairProduct`

For every natural N, the real unordered pair-distance product is continuous on the space of N complex points, including colliding tuples.

Module: `Erdos1040.GeometricDiameter`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.continuous_unorderedPairProduct : ∀ (N : ℕ), Continuous.{0, 0} Erdos1040.unorderedPairProduct
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.continuous_geometricMeanSeparation`

For every N at least 2, the exact geometric mean of the N-point unordered pair distances is a continuous real function of the tuple, including colliding tuples.

Module: `Erdos1040.GeometricDiameter`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.continuous_geometricMeanSeparation : ∀ {N : ℕ},
  LE.le.{0} 2 N → Continuous.{0, 0} Erdos1040.geometricMeanSeparation
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.finiteDiameter_eq_max_of_compact`

For every nonempty compact complex source set and every N at least 2, there is an actual tuple of N source points at which finiteDiameter equals its finite geometric mean separation. Thus the supremum agrees with the maximum in Saff equation 1.1.

Module: `Erdos1040.GeometricDiameter`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.finiteDiameter_eq_max_of_compact : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    Set.Nonempty.{0} S →
      ∀ {N : ℕ},
        LE.le.{0} 2 N →
          ∃ x,
            Eq.{1} (Erdos1040.finiteDiameter S N) (ENNReal.ofReal (Erdos1040.geometricMeanSeparation fun i => ↑(x i)))
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.finiteDiameter_empty`

For every positive N, the finite diameter of the empty complex source set is zero, as an empty extended nonnegative supremum.

Module: `Erdos1040.GeometricDiameter`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.finiteDiameter_empty : ∀ {N : ℕ},
  LT.lt.{0} 0 N → Eq.{1} (Erdos1040.finiteDiameter EmptyCollection.emptyCollection.{0} N) 0
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.transfiniteDiameter_empty`

The geometric transfinite diameter of the empty complex source set is zero.

Module: `Erdos1040.GeometricDiameter`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.transfiniteDiameter_empty : Eq.{1} (Erdos1040.transfiniteDiameter EmptyCollection.emptyCollection.{0})
  0
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.finiteDiameter_lt_top_of_compact`

For every compact complex source set, including the empty set, and every N at least 2, its geometric finiteDiameter is finite.

Module: `Erdos1040.GeometricDiameter`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.finiteDiameter_lt_top_of_compact : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S → ∀ {N : ℕ}, LE.le.{0} 2 N → LT.lt.{0} (Erdos1040.finiteDiameter S N) Top.top.{0}
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.exists_distinct_configuration_of_one_le_transfiniteDiameter`

For every compact complex source set with geometric transfinite diameter at least one and every N at least 2, an injective tuple Fin N to the original source set has unordered pair-distance product at least one. Nonemptiness and distinctness are derived, not assumed.

Module: `Erdos1040.GeometricDiameter`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_distinct_configuration_of_one_le_transfiniteDiameter : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    LE.le.{0} 1 (Erdos1040.transfiniteDiameter S) →
      ∀ {N : ℕ},
        LE.le.{0} 2 N → ∃ x, Function.Injective.{1, 1} x ∧ LE.le.{0} 1 (Erdos1040.unorderedPairProduct fun i => ↑(x i))
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.sum_offDiag_log_dist_eq_twice_log_unorderedPairProduct`

For every injective finite tuple of complex points, the sum of real log distances over all ordered distinct index pairs equals twice the logarithm of its unordered pair-distance product. All logarithm arguments are nonzero because tuple points are distinct.

Module: `Erdos1040.GeometricDiameter`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.sum_offDiag_log_dist_eq_twice_log_unorderedPairProduct : ∀ {N : ℕ} (x : Fin N → ℂ),
  Function.Injective.{1, 1} x →
    Eq.{1} (∑ p ∈ Finset.offDiag.{0} Finset.univ.{0}, Real.log (Dist.dist.{0} (x p.1) (x p.2)))
      (HMul.hMul.{0, 0, 0} 2 (Real.log (Erdos1040.unorderedPairProduct x)))
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.exists_distinct_configuration_log_sum_nonneg`

For every compact complex source set with geometric transfinite diameter at least one and every N at least 2, there exists an injective tuple Fin N to that original source set whose ordered off-diagonal real log-distance sum is nonnegative.

Module: `Erdos1040.GeometricDiameter`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_distinct_configuration_log_sum_nonneg : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    LE.le.{0} 1 (Erdos1040.transfiniteDiameter S) →
      ∀ {N : ℕ},
        LE.le.{0} 2 N →
          ∃ x,
            Function.Injective.{1, 1} x ∧
              LE.le.{0} 0 (∑ p ∈ Finset.offDiag.{0} Finset.univ.{0}, Real.log (Dist.dist.{0} ↑(x p.1) ↑(x p.2)))
```

## E1040-GLOBAL-FROSTMAN - `Erdos1040.lowerSemicontinuous_nonnegativeLogPotential`

For any complex source set S, real scale D and probability mu on subtype S, the actual extended nonnegative logarithmic observation potential is lower semicontinuous on the whole complex plane. No compactness or finiteness of potential values is assumed.

Module: `Erdos1040.GlobalFrostman`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.lowerSemicontinuous_nonnegativeLogPotential : ∀ {S : Set.{0} ℂ} (D : ℝ)
  (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S), LowerSemicontinuous.{0, 0} (Erdos1040.nonnegativeLogPotential D μ)
```

## E1040-GLOBAL-FROSTMAN - `Erdos1040.nonnegativeLogPotential_le_energy_on_support_of_minimizer`

For any complex source set S, real scale D and finite global minimizer mu of the actual extended nonnegative logarithmic energy among all source probabilities, its actual extended potential at every point of the support of mu pushed forward by inclusion is at most its energy. No pointwise support bound or global potential inequality is assumed.

Module: `Erdos1040.GlobalFrostman`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.nonnegativeLogPotential_le_energy_on_support_of_minimizer : ∀ {S : Set.{0} ℂ} (D : ℝ)
  (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
  Ne.{1} (Erdos1040.nonnegativeLogEnergy D μ) Top.top.{0} →
    (∀ (ν : MeasureTheory.ProbabilityMeasure.{0} ↑S),
        LE.le.{0} (Erdos1040.nonnegativeLogEnergy D μ) (Erdos1040.nonnegativeLogEnergy D ν)) →
      ∀ (z : ℂ),
        Membership.mem.{0, 0} (MeasureTheory.Measure.support.{0} (MeasureTheory.Measure.map.{0, 0} Subtype.val.{1} ↑μ))
            z →
          LE.le.{0} (Erdos1040.nonnegativeLogPotential D μ z) (Erdos1040.nonnegativeLogEnergy D μ)
```

## E1040-GLOBAL-FROSTMAN - `Erdos1040.integrable_log_norm_sub_of_nonnegativeLogPotential_ne_top`

For any source probability mu, positive real scale D, and complex observation z whose distance to every source point is at most D, finiteness of the actual extended potential at z implies actual real source integrability of log norm(z-w). The singular diagonal is removed almost everywhere as a consequence of finiteness.

Module: `Erdos1040.GlobalFrostman`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integrable_log_norm_sub_of_nonnegativeLogPotential_ne_top : ∀ {S : Set.{0} ℂ} {D : ℝ},
  LT.lt.{0} 0 D →
    ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S) {z : ℂ},
      (∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) D) →
        Ne.{1} (Erdos1040.nonnegativeLogPotential D μ z) Top.top.{0} →
          MeasureTheory.Integrable.{0, 0} (fun w => Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ↑μ
```

## E1040-GLOBAL-FROSTMAN - `Erdos1040.nonnegativeLogPotential_toReal_eq_log_sub_integral`

For any source probability mu, positive real scale D, and complex observation z whose distance to every source point is at most D, if the actual extended potential at z is finite then its real value equals log D minus the actual real integral of log norm(z-w) against mu. Actual integrability is proved, not supplied by totalization.

Module: `Erdos1040.GlobalFrostman`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.nonnegativeLogPotential_toReal_eq_log_sub_integral : ∀ {S : Set.{0} ℂ} {D : ℝ},
  LT.lt.{0} 0 D →
    ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S) {z : ℂ},
      (∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) D) →
        Ne.{1} (Erdos1040.nonnegativeLogPotential D μ z) Top.top.{0} →
          Eq.{1} (Erdos1040.nonnegativeLogPotential D μ z).toReal
            (HSub.hSub.{0, 0, 0} (Real.log D) (∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)) ∂↑μ))
```

## E1040-SUPPORT-HULL - `Erdos1040.sourceSupport`

For every probability mu on a complex source subtype S, sourceSupport mu is exactly the topological support of its ambient pushforward by subtype inclusion.

Module: `Erdos1040.SourceSupport`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.sourceSupport : {S : Set.{0} ℂ} → MeasureTheory.ProbabilityMeasure.{0} ↑S → Set.{0} ℂ
```

## E1040-SUPPORT-HULL - `Erdos1040.sourceSupport_subset`

For every closed complex source set S and probability mu on S, its ambient source support is a subset of S.

Module: `Erdos1040.SourceSupport`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.sourceSupport_subset : ∀ {S : Set.{0} ℂ},
  IsClosed.{0} S → ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S), Erdos1040.sourceSupport μ ⊆ S
```

## E1040-SUPPORT-HULL - `Erdos1040.isCompact_sourceSupport`

For every compact complex source set S and probability mu on S, its ambient source support is compact.

Module: `Erdos1040.SourceSupport`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.isCompact_sourceSupport : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S → ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S), IsCompact.{0} (Erdos1040.sourceSupport μ)
```

## E1040-SUPPORT-HULL - `Erdos1040.sourceSupport_nonempty`

For every probability mu on any complex source subtype, its ambient source support is nonempty.

Module: `Erdos1040.SourceSupport`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.sourceSupport_nonempty : ∀ {S : Set.{0} ℂ} (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
  Set.Nonempty.{0} (Erdos1040.sourceSupport μ)
```

## E1040-SUPPORT-HULL - `Erdos1040.sourceProbabilityOnSupport`

The actual probability measure on the subtype of sourceSupport mu obtained by pulling its ambient pushforward back to its closed conull support.

Module: `Erdos1040.SourceSupport`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.sourceProbabilityOnSupport : {S : Set.{0} ℂ} →
  (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S) → MeasureTheory.ProbabilityMeasure.{0} ↑(Erdos1040.sourceSupport μ)
```

## E1040-SUPPORT-HULL - `Erdos1040.map_sourceProbabilityOnSupport`

Pushing sourceProbabilityOnSupport mu to the ambient complex plane gives exactly the ambient pushforward of mu.

Module: `Erdos1040.SourceSupport`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.map_sourceProbabilityOnSupport : ∀ {S : Set.{0} ℂ} (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
  Eq.{1} (MeasureTheory.Measure.map.{0, 0} Subtype.val.{1} ↑(Erdos1040.sourceProbabilityOnSupport μ))
    (MeasureTheory.Measure.map.{0, 0} Subtype.val.{1} ↑μ)
```

## E1040-SUPPORT-HULL - `Erdos1040.integral_sourceProbabilityOnSupport`

For every measurable complex source set S, probability mu on S, complete real normed vector space E, and function f from the complex plane to E, the Bochner integral of f over the constructed support probability equals its integral over mu. This is an exact integral-transport identity with the standard totalized integral convention; integrability is transferred separately.

Module: `Erdos1040.SourceSupport`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integral_sourceProbabilityOnSupport.{u_1} : ∀ {S : Set.{0} ℂ},
  MeasurableSet.{0} S →
    ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S) {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
      [inst_1 : NormedSpace.{0, u_1} ℝ E] [CompleteSpace.{u_1} E] (f : ℂ → E),
      Eq.{u_1 + 1} (∫ (w : ↑(Erdos1040.sourceSupport μ)), f ↑w ∂↑(Erdos1040.sourceProbabilityOnSupport μ))
        (∫ (w : ↑S), f ↑w ∂↑μ)
```

## E1040-SUPPORT-HULL - `Erdos1040.integrable_sourceProbabilityOnSupport_iff`

For every measurable complex source set S, probability mu on S, complete real normed vector space E, and function f from the complex plane to E, f is Bochner integrable under the constructed support probability if and only if it is Bochner integrable under mu.

Module: `Erdos1040.SourceSupport`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integrable_sourceProbabilityOnSupport_iff.{u_1} : ∀ {S : Set.{0} ℂ},
  MeasurableSet.{0} S →
    ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S) {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
      [NormedSpace.{0, u_1} ℝ E] [CompleteSpace.{u_1} E] (f : ℂ → E),
      MeasureTheory.Integrable.{u_1, 0} (fun w => f ↑w) ↑(Erdos1040.sourceProbabilityOnSupport μ) ↔
        MeasureTheory.Integrable.{u_1, 0} (fun w => f ↑w) ↑μ
```

## E1040-SUPPORT-HULL - `Erdos1040.lintegral_sourceProbabilityOnSupport`

For every measurable complex source set S, probability mu on S, and arbitrary nonnegative extended-real function on the complex plane, its actual extended integral under the constructed support probability equals its integral under mu, including infinite values.

Module: `Erdos1040.SourceSupport`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.lintegral_sourceProbabilityOnSupport : ∀ {S : Set.{0} ℂ},
  MeasurableSet.{0} S →
    ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S) (f : ℂ → ENNReal),
      Eq.{1} (∫⁻ (w : ↑(Erdos1040.sourceSupport μ)), f ↑w ∂↑(Erdos1040.sourceProbabilityOnSupport μ))
        (∫⁻ (w : ↑S), f ↑w ∂↑μ)
```

## E1040-SUPPORT-HULL - `Erdos1040.nullSingletonClass_sourceProbabilityOnSupport`

If every singleton has zero measure under a source probability mu, every singleton also has zero measure under the actual probability transported to its ambient support.

Module: `Erdos1040.SourceSupport`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.nullSingletonClass_sourceProbabilityOnSupport : ∀ {S : Set.{0} ℂ}
  (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S) [MeasureTheory.NullSingletonClass.{0} ↑μ],
  MeasureTheory.NullSingletonClass.{0} ↑(Erdos1040.sourceProbabilityOnSupport μ)
```

## E1040-SUPPORT-HULL - `Erdos1040.integrable_source_potential_of_notMem_support`

For every compact complex source S and probability mu on S, the actual real logarithmic distance kernel is integrable against mu at every observation outside its ambient support.

Module: `Erdos1040.SourceSupport`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integrable_source_potential_of_notMem_support : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S) {z : ℂ},
      z ∉ Erdos1040.sourceSupport μ →
        MeasureTheory.Integrable.{0, 0} (fun w => Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ↑μ
```

## E1040-SUPPORT-HULL - `Erdos1040.harmonicOnNhd_source_potential_compl_support`

For every compact complex source S and probability mu on S, its actual real logarithmic source potential is harmonic throughout the complement of its ambient support, proved by actual support transport and the checked compact-source harmonicity theorem.

Module: `Erdos1040.SourceSupport`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.harmonicOnNhd_source_potential_compl_support : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
      InnerProductSpace.HarmonicOnNhd.{0, 0}
        (fun z => ∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)) ∂↑μ)
        (Compl.compl.{0} (Erdos1040.sourceSupport μ))
```

## E1040-EMPIRICAL-ENERGY - `Erdos1040.toReal_truncatedLogEnergy_empirical`

For every positive empirical source probability, real scale and natural truncation, the real value of its actual truncated energy equals N^(-2) times the full ordered sum of the real values of the truncated kernel. The truncation makes every term finite before converting the sums; no untruncated energy or diagonal value is replaced by zero.

Module: `Erdos1040.EmpiricalEnergy`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.toReal_truncatedLogEnergy_empirical : ∀ {S : Set.{0} ℂ} {N : ℕ} (roots : Fin N → ↑S)
  (hN : LT.lt.{0} 0 N) (D : ℝ) (n : ℕ),
  Eq.{1} (Erdos1040.truncatedLogEnergy D n (Erdos1040.empiricalSourceProbability roots hN)).toReal
    (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Inv.inv.{0} ↑N) 2)
      (∑ i, ∑ j, (Min.min.{0} (Erdos1040.nonnegativeLogKernel D ↑(roots i) ↑(roots j)) ↑n).toReal))
```

## E1040-SUPPORT-HULL - `Erdos1040.isPreconnected_complex_norm_gt`

For every nonnegative real R, the complex exterior set of points with norm strictly greater than R is preconnected, proved as the continuous image of a positive radius interval times the unit circle.

Module: `Erdos1040.FilledHull`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.isPreconnected_complex_norm_gt : ∀ {R : ℝ},
  LE.le.{0} 0 R → IsPreconnected.{0} (Set.ofPred.{0} fun z => LT.lt.{0} R (Norm.norm.{0} z))
```

## E1040-SUPPORT-HULL - `Erdos1040.frontier_connectedComponentIn_compl_subset`

For every closed complex set T and every complex point x, the frontier of the connected component of T complement containing x is a subset of T.

Module: `Erdos1040.FilledHull`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.frontier_connectedComponentIn_compl_subset : ∀ {T : Set.{0} ℂ},
  IsClosed.{0} T → ∀ (x : ℂ), frontier.{0} (connectedComponentIn.{0} (Compl.compl.{0} T) x) ⊆ T
```

## E1040-SUPPORT-HULL - `Erdos1040.exists_compact_hull_with_connected_complement`

For every nonempty compact complex set T, there is a nonempty compact complex set K containing T, with preconnected complement and frontier contained in T. The constructed complement is the component of T complement containing the entire exterior of a sufficiently large disk, not a geometric or potential assumption.

Module: `Erdos1040.FilledHull`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_compact_hull_with_connected_complement : ∀ {T : Set.{0} ℂ},
  IsCompact.{0} T →
    Set.Nonempty.{0} T →
      ∃ K, IsCompact.{0} K ∧ Set.Nonempty.{0} K ∧ T ⊆ K ∧ IsPreconnected.{0} (Compl.compl.{0} K) ∧ frontier.{0} K ⊆ T
```

## E1040-EMPIRICAL-ENERGY - `Erdos1040.sum_truncated_kernel_le_of_log_sum_nonneg`

For every injective N-point configuration in a source whose pair distances are at most D >= 1, if its ordered off-diagonal log-distance sum is nonnegative, the full ordered real sum of the kernel truncated at natural n is at most N*n + N^2*log D. The diagonal contributes N*n and is retained; N may be zero in this finite-sum bound.

Module: `Erdos1040.EmpiricalEnergy`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.sum_truncated_kernel_le_of_log_sum_nonneg : ∀ {S : Set.{0} ℂ} {N : ℕ} (roots : Fin N → ↑S),
  Function.Injective.{1, 1} roots →
    ∀ {D : ℝ},
      LE.le.{0} 1 D →
        (∀ (z : ℂ),
            Membership.mem.{0, 0} S z → ∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) D) →
          ∀ (n : ℕ),
            LE.le.{0} 0 (∑ p ∈ Finset.offDiag.{0} Finset.univ.{0}, Real.log (Dist.dist.{0} ↑(roots p.1) ↑(roots p.2))) →
              LE.le.{0} (∑ i, ∑ j, (Min.min.{0} (Erdos1040.nonnegativeLogKernel D ↑(roots i) ↑(roots j)) ↑n).toReal)
                (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} ↑N ↑n)
                  (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑N) 2) (Real.log D)))
```

## E1040-EMPIRICAL-ENERGY - `Erdos1040.truncatedLogEnergy_empirical_le_of_log_sum_nonneg`

For every positive injective N-point configuration in a source with pair distances at most D >= 1 and nonnegative ordered off-diagonal log-distance sum, its actual empirical probability has truncated energy at natural n bounded by ofReal(log D + n/N). The finite truncated double energy retains all diagonal terms.

Module: `Erdos1040.EmpiricalEnergy`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.truncatedLogEnergy_empirical_le_of_log_sum_nonneg : ∀ {S : Set.{0} ℂ} {N : ℕ} (roots : Fin N → ↑S)
  (hN : LT.lt.{0} 0 N),
  Function.Injective.{1, 1} roots →
    ∀ {D : ℝ},
      LE.le.{0} 1 D →
        (∀ (z : ℂ),
            Membership.mem.{0, 0} S z → ∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) D) →
          ∀ (n : ℕ),
            LE.le.{0} 0 (∑ p ∈ Finset.offDiag.{0} Finset.univ.{0}, Real.log (Dist.dist.{0} ↑(roots p.1) ↑(roots p.2))) →
              LE.le.{0} (Erdos1040.truncatedLogEnergy D n (Erdos1040.empiricalSourceProbability roots hN))
                (ENNReal.ofReal (HAdd.hAdd.{0, 0, 0} (Real.log D) (HDiv.hDiv.{0, 0, 0} ↑n ↑N)))
```

## E1040-DIAMETER-ENERGY - `Erdos1040.exists_probability_energy_le_log_of_one_le_transfiniteDiameter`

For every compact complex source S with its exact geometric transfinite diameter at least one, every real scale D >= 1 bounding all source-pair distances admits an actual source probability whose extended nonnegative logarithmic energy is at most ofReal(log D). Bounded truncations include diagonals before compactness yields finite full energy.

Module: `Erdos1040.EnergyDiameter`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_probability_energy_le_log_of_one_le_transfiniteDiameter : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    LE.le.{0} 1 (Erdos1040.transfiniteDiameter S) →
      ∀ {D : ℝ},
        LE.le.{0} 1 D →
          (∀ (z : ℂ),
              Membership.mem.{0, 0} S z → ∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) D) →
            ∃ μ, LE.le.{0} (Erdos1040.nonnegativeLogEnergy D μ) (ENNReal.ofReal (Real.log D))
```

## E1040-DIAMETER-ENERGY - `Erdos1040.exists_finite_minimizer_of_one_le_transfiniteDiameter`

For every compact complex source S with its exact geometric transfinite diameter at least one and every real scale D >= 1 bounding all source-pair distances, there is an actual global minimizing source probability with finite extended energy and energy.toReal <= log D. No equilibrium-potential property is assumed.

Module: `Erdos1040.EnergyDiameter`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_finite_minimizer_of_one_le_transfiniteDiameter : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    LE.le.{0} 1 (Erdos1040.transfiniteDiameter S) →
      ∀ {D : ℝ},
        LE.le.{0} 1 D →
          (∀ (z : ℂ),
              Membership.mem.{0, 0} S z → ∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) D) →
            ∃ μ,
              (∀ (ν : MeasureTheory.ProbabilityMeasure.{0} ↑S),
                  LE.le.{0} (Erdos1040.nonnegativeLogEnergy D μ) (Erdos1040.nonnegativeLogEnergy D ν)) ∧
                Ne.{1} (Erdos1040.nonnegativeLogEnergy D μ) Top.top.{0} ∧
                  LE.le.{0} (Erdos1040.nonnegativeLogEnergy D μ).toReal (Real.log D)
```

## E1040-POLYNOMIAL-CONCLUSION - `Erdos1040.HasArbitrarilySmallLemniscates.mono`

For any complex source sets S contained in F, arbitrarily small positive-degree strict unit lemniscates with every root in S also have every root in F. The same roots and area bound are retained.

Module: `Erdos1040.PolynomialConclusion`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.HasArbitrarilySmallLemniscates.mono : ∀ {S F : Set.{0} ℂ},
  Erdos1040.HasArbitrarilySmallLemniscates S → S ⊆ F → Erdos1040.HasArbitrarilySmallLemniscates F
```

## E1040-POLYNOMIAL-CONCLUSION - `Erdos1040.exists_monic_polynomial_small_area`

If F has the exact arbitrarily-small finite-root lemniscate property, then for every positive real epsilon there exists an actual complex polynomial p which is monic, has positive natural degree, has every complex root in F, and whose strict unit sublevel set has planar Lebesgue volume less than ofReal(epsilon). This is the explicit polynomial formulation, proved using the exact product polynomial, degree, evaluation and root identities.

Module: `Erdos1040.PolynomialConclusion`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_monic_polynomial_small_area : ∀ {F : Set.{0} ℂ},
  Erdos1040.HasArbitrarilySmallLemniscates F →
    ∀ {ε : ℝ},
      LT.lt.{0} 0 ε →
        ∃ p,
          Polynomial.Monic.{0} p ∧
            LT.lt.{0} 0 (Polynomial.natDegree.{0} p) ∧
              (∀ (z : ℂ), Polynomial.IsRoot.{0} p z → Membership.mem.{0, 0} F z) ∧
                LT.lt.{0}
                  (MeasureTheory.MeasureSpace.volume.{0}
                    (Set.ofPred.{0} fun z => LT.lt.{0} (Norm.norm.{0} (Polynomial.eval.{0} z p)) 1))
                  (ENNReal.ofReal ε)
```

## E1040-EXTERIOR-POSITIVITY - `Erdos1040.tendsto_log_source_potential_atTop`

For every compact complex source S and actual probability mu on S, the actual positive-log source potential tends to positive infinity along the cocompact filter on the complex plane. It follows from the proved mass-one logarithmic asymptotic, without an equilibrium assumption.

Module: `Erdos1040.ExteriorPositivity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.tendsto_log_source_potential_atTop : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
      Filter.Tendsto.{0, 0} (fun z => ∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)) ∂↑μ)
        (Filter.cocompact.{0} ℂ) Filter.atTop.{0}
```

## E1040-EXTERIOR-POSITIVITY - `Erdos1040.log_source_potential_pos_on_hull_compl`

For every compact complex source S, compact complex set K, and actual probability mu on S whose ambient support is contained in K, if K has preconnected complement and the actual positive-log source potential is nonnegative everywhere, that potential is strictly positive at every point outside K. Harmonicity off the support and growth at infinity are proved inputs, not additional hypotheses; no boundary regularity or zero-on-hull condition is imposed.

Module: `Erdos1040.ExteriorPositivity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.log_source_potential_pos_on_hull_compl : ∀ {S K : Set.{0} ℂ},
  IsCompact.{0} S →
    IsCompact.{0} K →
      ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
        Erdos1040.sourceSupport μ ⊆ K →
          IsPreconnected.{0} (Compl.compl.{0} K) →
            (∀ (z : ℂ), LE.le.{0} 0 (∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)) ∂↑μ)) →
              ∀ z ∉ K, LT.lt.{0} 0 (∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)) ∂↑μ)
```

## E1040-EQUILIBRIUM-ASSEMBLY - `Erdos1040.hasArbitrarilySmallLemniscates_of_nonnegative_source_potential`

For every compact complex source S and actual probability mu on S, if its actual positive-log source potential is nonnegative at every complex observation, then S has arbitrarily small strict unit lemniscate area with positive degree and every root in S. The ambient support, transported probability, compact hull, frontier inclusion, connected exterior and strict exterior positivity are all constructed and proved; they are not caller-supplied assumptions.

Module: `Erdos1040.NonnegativePotentialLemniscate`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.hasArbitrarilySmallLemniscates_of_nonnegative_source_potential : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
      (∀ (z : ℂ), LE.le.{0} 0 (∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)) ∂↑μ)) →
        Erdos1040.HasArbitrarilySmallLemniscates S
```

## E1040-GLOBAL-FROSTMAN - `Erdos1040.harmonic_nonpos_of_boundary_and_infinity`

For any open subset U of the complex plane and any real harmonic function f on U, if at every frontier point and for every positive epsilon the nearby values of f within U are eventually below epsilon, and f is eventually below every positive epsilon at infinity in the cocompact filter, then f is nonpositive on all of U. No connectedness, unboundedness, continuous boundary extension, or exceptional boundary set is assumed.

Module: `Erdos1040.GlobalFrostman`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.harmonic_nonpos_of_boundary_and_infinity : ∀ {f : ℂ → ℝ} {U : Set.{0} ℂ},
  IsOpen.{0} U →
    InnerProductSpace.HarmonicOnNhd.{0, 0} f U →
      (∀ (ξ : ℂ),
          Membership.mem.{0, 0} (frontier.{0} U) ξ →
            ∀ (ε : ℝ), LT.lt.{0} 0 ε → ∀ᶠ (z : ℂ) in nhds.{0} ξ, Membership.mem.{0, 0} U z → LT.lt.{0} (f z) ε) →
        (∀ (ε : ℝ), LT.lt.{0} 0 ε → ∀ᶠ (z : ℂ) in Filter.cocompact.{0} ℂ, LT.lt.{0} (f z) ε) →
          ∀ (x : ℂ), Membership.mem.{0, 0} U x → LE.le.{0} (f x) 0
```

## E1040-GLOBAL-FROSTMAN - `Erdos1040.eventually_neg_log_potential_lt_of_le_on_source`

For any nonempty compact complex source S, a non-atomic probability mu on subtype S whose actual real logarithmic source kernel is integrable at every complex observation, and a real upper bound M for its negative-log potential at every point of S, near each source point that actual negative-log potential is eventually less than M+epsilon for every positive epsilon. The proof uses nearest source points, the log 2 positive-difference bound, and dominated convergence; the conditional support bound and integrability are explicit.

Module: `Erdos1040.GlobalFrostman`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.eventually_neg_log_potential_lt_of_le_on_source : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    Set.Nonempty.{0} S →
      ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S) [MeasureTheory.NullSingletonClass.{0} ↑μ],
        (∀ (z : ℂ), MeasureTheory.Integrable.{0, 0} (fun w => Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ↑μ) →
          ∀ (M : ℝ),
            (∀ (z : ℂ),
                Membership.mem.{0, 0} S z →
                  LE.le.{0} (Neg.neg.{0} (∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)) ∂↑μ)) M) →
              ∀ {ξ : ℂ},
                Membership.mem.{0, 0} S ξ →
                  ∀ (ε : ℝ),
                    LT.lt.{0} 0 ε →
                      ∀ᶠ (z : ℂ) in nhds.{0} ξ,
                        LT.lt.{0} (Neg.neg.{0} (∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)) ∂↑μ))
                          (HAdd.hAdd.{0, 0, 0} M ε)
```

## E1040-GLOBAL-FROSTMAN - `Erdos1040.integrable_log_norm_sub_of_finite_minimizer`

For any compact complex source S, positive real scale D bounding every source pair distance, and a finite global minimizer mu of the actual extended nonnegative logarithmic energy among all source probabilities, the actual real kernel w maps to log norm(z-w) is integrable against mu at every complex observation z, including source and support points. This is derived from the support potential bound and source-support transport, with no pointwise integrability hypothesis.

Module: `Erdos1040.GlobalFrostman`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.integrable_log_norm_sub_of_finite_minimizer : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ {D : ℝ},
      LT.lt.{0} 0 D →
        (∀ (z : ℂ),
            Membership.mem.{0, 0} S z → ∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) D) →
          ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
            Ne.{1} (Erdos1040.nonnegativeLogEnergy D μ) Top.top.{0} →
              (∀ (ν : MeasureTheory.ProbabilityMeasure.{0} ↑S),
                  LE.le.{0} (Erdos1040.nonnegativeLogEnergy D μ) (Erdos1040.nonnegativeLogEnergy D ν)) →
                ∀ (z : ℂ),
                  MeasureTheory.Integrable.{0, 0} (fun w => Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w))) ↑μ
```

## E1040-GLOBAL-FROSTMAN - `Erdos1040.log_source_potential_ge_of_finite_minimizer`

For any compact complex source S, positive real scale D bounding every source pair distance, and a finite global minimizer mu of the actual extended nonnegative logarithmic energy among all source probabilities, at every complex observation z the actual positive-logarithm source integral is at least log D minus the real value of that minimum energy. Actual integrability at every point is proved separately and used in the proof. No global potential inequality, support bound, boundary regularity, connectedness, or classical polar-set assertion is assumed.

Module: `Erdos1040.GlobalFrostman`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.log_source_potential_ge_of_finite_minimizer : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ {D : ℝ},
      LT.lt.{0} 0 D →
        (∀ (z : ℂ),
            Membership.mem.{0, 0} S z → ∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) D) →
          ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
            Ne.{1} (Erdos1040.nonnegativeLogEnergy D μ) Top.top.{0} →
              (∀ (ν : MeasureTheory.ProbabilityMeasure.{0} ↑S),
                  LE.le.{0} (Erdos1040.nonnegativeLogEnergy D μ) (Erdos1040.nonnegativeLogEnergy D ν)) →
                ∀ (z : ℂ),
                  LE.le.{0} (HSub.hSub.{0, 0, 0} (Real.log D) (Erdos1040.nonnegativeLogEnergy D μ).toReal)
                    (∫ (w : ↑S), Real.log (Norm.norm.{0} (HSub.hSub.{0, 0, 0} z ↑w)) ∂↑μ)
```

## E1040-EQUILIBRIUM-ASSEMBLY - `Erdos1040.hasArbitrarilySmallLemniscates_of_finite_minimizer`

For every compact complex source S, positive scale D bounding every source-pair distance, and actual finite global energy minimizer mu with energy.toReal <= log D, the exact positive-degree roots-in-S strict-small-area lemniscate conclusion holds. The global potential bound and all support/hull geometry are discharged by proved theorems.

Module: `Erdos1040.CompactLemniscate`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.hasArbitrarilySmallLemniscates_of_finite_minimizer : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ {D : ℝ},
      LT.lt.{0} 0 D →
        (∀ (z : ℂ),
            Membership.mem.{0, 0} S z → ∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) D) →
          ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
            Ne.{1} (Erdos1040.nonnegativeLogEnergy D μ) Top.top.{0} →
              (∀ (ν : MeasureTheory.ProbabilityMeasure.{0} ↑S),
                  LE.le.{0} (Erdos1040.nonnegativeLogEnergy D μ) (Erdos1040.nonnegativeLogEnergy D ν)) →
                LE.le.{0} (Erdos1040.nonnegativeLogEnergy D μ).toReal (Real.log D) →
                  Erdos1040.HasArbitrarilySmallLemniscates S
```

## E1040-COMPACT-GEOMETRIC - `Erdos1040.hasArbitrarilySmallLemniscates_of_one_le_transfiniteDiameter`

Every compact complex source S whose exact geometric transfinite diameter is at least one has arbitrarily small strict unit lemniscate area with positive degree and all roots in S. A distance scale and finite minimizing probability are constructed from the geometric hypothesis. No source probability, energy bound, smoothness or potential property is supplied as an assumption.

Module: `Erdos1040.CompactLemniscate`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.hasArbitrarilySmallLemniscates_of_one_le_transfiniteDiameter : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S → LE.le.{0} 1 (Erdos1040.transfiniteDiameter S) → Erdos1040.HasArbitrarilySmallLemniscates S
```

## E1040-FULL - `Erdos1040.erdos1040`

For every closed infinite complex set F with transfinite diameter at least one and every positive real epsilon, there exists an actual complex polynomial p that is monic, has positive natural degree, has every complex root in F, and whose strict unit sublevel set has planar Lebesgue volume less than ofReal(epsilon). The bounded case uses the compact geometric theorem; the unbounded case uses the unconditional quadratic construction. The geometric transfinite diameter is the decreasing limit of the exact finite pair-product diameters, with that limit correspondence proved separately.

Module: `Erdos1040.FullTheorem`. Kind: theorem. Role: target.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.erdos1040 : ∀ {F : Set.{0} ℂ},
  IsClosed.{0} F →
    Set.Infinite.{0} F →
      LE.le.{0} 1 (Erdos1040.transfiniteDiameter F) →
        ∀ {ε : ℝ},
          LT.lt.{0} 0 ε →
            ∃ p,
              Polynomial.Monic.{0} p ∧
                LT.lt.{0} 0 (Polynomial.natDegree.{0} p) ∧
                  (∀ (z : ℂ), Polynomial.IsRoot.{0} p z → Membership.mem.{0, 0} F z) ∧
                    LT.lt.{0}
                      (MeasureTheory.MeasureSpace.volume.{0}
                        (Set.ofPred.{0} fun z => LT.lt.{0} (Norm.norm.{0} (Polynomial.eval.{0} z p)) 1))
                      (ENNReal.ofReal ε)
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.sum_matrix_succAbove_eq`

For any symmetric real matrix indexed by Fin(n+1) with zero diagonal, deleting row and column k leaves the full entry sum minus twice row k. Fin.succAbove is the exact deletion injection; this includes n=0.

Module: `Erdos1040.GeometricDiameterLimit`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.sum_matrix_succAbove_eq : ∀ {n : ℕ}
  (L : Fin (HAdd.hAdd.{0, 0, 0} n 1) → Fin (HAdd.hAdd.{0, 0, 0} n 1) → ℝ),
  (∀ (i j : Fin (HAdd.hAdd.{0, 0, 0} n 1)), Eq.{1} (L i j) (L j i)) →
    (∀ (i : Fin (HAdd.hAdd.{0, 0, 0} n 1)), Eq.{1} (L i i) 0) →
      ∀ (k : Fin (HAdd.hAdd.{0, 0, 0} n 1)),
        Eq.{1} (∑ i, ∑ j, L (k.succAbove i) (k.succAbove j))
          (HSub.hSub.{0, 0, 0} (∑ i, ∑ j, L i j) (HMul.hMul.{0, 0, 0} 2 (∑ j, L k j)))
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.sum_succAbove_matrix_eq`

For any symmetric real matrix indexed by Fin(n+1) with zero diagonal, the sum over all n+1 deleted submatrix entry sums equals (n+1-2) times the full matrix sum.

Module: `Erdos1040.GeometricDiameterLimit`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.sum_succAbove_matrix_eq : ∀ {n : ℕ}
  (L : Fin (HAdd.hAdd.{0, 0, 0} n 1) → Fin (HAdd.hAdd.{0, 0, 0} n 1) → ℝ),
  (∀ (i j : Fin (HAdd.hAdd.{0, 0, 0} n 1)), Eq.{1} (L i j) (L j i)) →
    (∀ (i : Fin (HAdd.hAdd.{0, 0, 0} n 1)), Eq.{1} (L i i) 0) →
      Eq.{1} (∑ k, ∑ i, ∑ j, L (k.succAbove i) (k.succAbove j))
        (HMul.hMul.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (↑n) 1) 2) (∑ i, ∑ j, L i j))
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.sum_log_dist_eq_twice_log_unorderedPairProduct`

For any injective finite complex tuple of any order N, the full double sum of totalized real log distances equals twice the logarithm of its actual unordered-pair distance product. Diagonal terms are exactly zero because Real.log(0)=0; off-diagonal distances are positive.

Module: `Erdos1040.GeometricDiameterLimit`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.sum_log_dist_eq_twice_log_unorderedPairProduct : ∀ {N : ℕ} (x : Fin N → ℂ),
  Function.Injective.{1, 1} x →
    Eq.{1} (∑ i, ∑ j, Real.log (Dist.dist.{0} (x i) (x j)))
      (HMul.hMul.{0, 0, 0} 2 (Real.log (Erdos1040.unorderedPairProduct x)))
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.unorderedPairProduct_pos_of_injective`

The actual unordered-pair distance product of every injective finite complex tuple is strictly positive, including empty pair products for orders zero and one.

Module: `Erdos1040.GeometricDiameterLimit`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.unorderedPairProduct_pos_of_injective : ∀ {N : ℕ} (x : Fin N → ℂ),
  Function.Injective.{1, 1} x → LT.lt.{0} 0 (Erdos1040.unorderedPairProduct x)
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.log_geometricMeanSeparation_eq`

For an injective finite complex tuple, the logarithm of its exact geometric mean separation equals the full double log-distance sum divided by N(N-1). All operations use the already defined totalized real functions, so the identity also holds for orders zero and one.

Module: `Erdos1040.GeometricDiameterLimit`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.log_geometricMeanSeparation_eq : ∀ {N : ℕ} (x : Fin N → ℂ),
  Function.Injective.{1, 1} x →
    Eq.{1} (Real.log (Erdos1040.geometricMeanSeparation x))
      (HDiv.hDiv.{0, 0, 0} (∑ i, ∑ j, Real.log (Dist.dist.{0} (x i) (x j)))
        (HMul.hMul.{0, 0, 0} (↑N) (HSub.hSub.{0, 0, 0} (↑N) 1)))
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.sum_log_geometricMeanSeparation_succAbove`

For every injective tuple of n+3 complex points, the sum over all deletions of the logarithm of the geometric mean separation of the remaining n+2 points equals (n+3) times the logarithm of the original geometric mean separation.

Module: `Erdos1040.GeometricDiameterLimit`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.sum_log_geometricMeanSeparation_succAbove : ∀ {n : ℕ} (x : Fin (HAdd.hAdd.{0, 0, 0} n 3) → ℂ),
  Function.Injective.{1, 1} x →
    Eq.{1} (∑ k, Real.log (Erdos1040.geometricMeanSeparation fun i => x (k.succAbove i)))
      (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (↑n) 3) (Real.log (Erdos1040.geometricMeanSeparation x)))
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.exists_geometricMeanSeparation_le_succAbove`

Every tuple of n+3 complex points has a deletion of one point whose remaining n+2-point geometric mean separation is at least the original. Repeated configurations are included by treating their zero unordered-pair product separately.

Module: `Erdos1040.GeometricDiameterLimit`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_geometricMeanSeparation_le_succAbove : ∀ {n : ℕ} (x : Fin (HAdd.hAdd.{0, 0, 0} n 3) → ℂ),
  ∃ k, LE.le.{0} (Erdos1040.geometricMeanSeparation x) (Erdos1040.geometricMeanSeparation fun i => x (k.succAbove i))
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.finiteDiameter_succ_le`

For every complex source set S and every natural order N at least two, its exact extended finite geometric diameter of order N+1 is no larger than that of order N. Compactness, boundedness, and nonemptiness are not assumed.

Module: `Erdos1040.GeometricDiameterLimit`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.finiteDiameter_succ_le : ∀ (S : Set.{0} ℂ) {N : ℕ},
  LE.le.{0} 2 N → LE.le.{0} (Erdos1040.finiteDiameter S (HAdd.hAdd.{0, 0, 0} N 1)) (Erdos1040.finiteDiameter S N)
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.antitone_finiteDiameter`

For every complex source set S, the sequence of exact extended finite geometric diameters at orders n+2 is antitone in n.

Module: `Erdos1040.GeometricDiameterLimit`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.antitone_finiteDiameter : ∀ (S : Set.{0} ℂ),
  Antitone.{0, 0} fun n => Erdos1040.finiteDiameter S (HAdd.hAdd.{0, 0, 0} n 2)
```

## E1040-GEOMETRIC-DIAMETER - `Erdos1040.tendsto_finiteDiameter_transfiniteDiameter`

For every complex source set S, its exact finite geometric diameters at orders n+2 converge in ENNReal to the previously defined transfinite diameter, the infimum of those diameters. Together with compact maximum attainment and the exact pair-product definition, this identifies the definition with the classical decreasing geometric limit, without replacing it by an energy condition.

Module: `Erdos1040.GeometricDiameterLimit`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.tendsto_finiteDiameter_transfiniteDiameter : ∀ (S : Set.{0} ℂ),
  Filter.Tendsto.{0, 0} (fun n => Erdos1040.finiteDiameter S (HAdd.hAdd.{0, 0, 0} n 2)) Filter.atTop.{0}
    (nhds.{0} (Erdos1040.transfiniteDiameter S))
```

## E1040-LOGARITHMIC-CAPACITY - `Erdos1040.logarithmicCapacityScale`

The canonical real scale max(1, Metric.diam S). This is used as a positive source-distance bound only for compact or bounded planar sets; no standard capacity on unbounded sets is asserted through totalized real diameter.

Module: `Erdos1040.LogarithmicCapacity`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.logarithmicCapacityScale : Set.{0} ℂ → ℝ
```

## E1040-LOGARITHMIC-CAPACITY - `Erdos1040.one_le_logarithmicCapacityScale`

For every planar source set, its canonical logarithmic-capacity scale is at least one and hence positive.

Module: `Erdos1040.LogarithmicCapacity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.one_le_logarithmicCapacityScale : ∀ (S : Set.{0} ℂ),
  LE.le.{0} 1 (Erdos1040.logarithmicCapacityScale S)
```

## E1040-LOGARITHMIC-CAPACITY - `Erdos1040.dist_le_logarithmicCapacityScale`

For every compact planar source set, every pair of points in that original set has Euclidean distance at most its canonical logarithmic-capacity scale.

Module: `Erdos1040.LogarithmicCapacity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.dist_le_logarithmicCapacityScale : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ {z w : ℂ},
      Membership.mem.{0, 0} S z →
        Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) (Erdos1040.logarithmicCapacityScale S)
```

## E1040-LOGARITHMIC-CAPACITY - `Erdos1040.robinConstant`

For compact planar sources, robinConstant is the EReal infimum over all actual source probabilities of nonnegativeLogEnergy at the canonical scale embedded in EReal, minus log of that scale. The singular diagonal stays positive infinity, the energy is the actual product integral, and no equilibrium measure or potential property is included as an assumption. The empty infimum is positive infinity; this definition is interpreted classically only for compact or bounded sets.

Module: `Erdos1040.LogarithmicCapacity`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.robinConstant : Set.{0} ℂ → EReal
```

## E1040-LOGARITHMIC-CAPACITY - `Erdos1040.logarithmicCapacity`

For compact planar sources, logarithmicCapacity is EReal.exp of the negative actual Robin constant, with values in ENNReal and capacity zero when the Robin constant is positive infinity. This is the classical energy definition, not a transfinite-diameter or potential-property predicate; no claim about the unbounded-set convention is made.

Module: `Erdos1040.LogarithmicCapacity`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.logarithmicCapacity : Set.{0} ℂ → ENNReal
```

## E1040-LOGARITHMIC-CAPACITY - `Erdos1040.robinConstant_eq_iInf_energy_sub_log`

For every compact planar source S and every positive real D bounding all its pair distances, its Robin constant equals the EReal infimum over source probabilities of the actual nonnegative energy at D minus log D. The identity follows from checked normalized energy scale independence and includes infinite energies and empty sources.

Module: `Erdos1040.LogarithmicCapacity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.robinConstant_eq_iInf_energy_sub_log : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ {D : ℝ},
      LT.lt.{0} 0 D →
        (∀ (z : ℂ),
            Membership.mem.{0, 0} S z → ∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) D) →
          Eq.{1} (Erdos1040.robinConstant S)
            (⨅ μ, HSub.hSub.{0, 0, 0} ↑(Erdos1040.nonnegativeLogEnergy D μ) ↑(Real.log D))
```

## E1040-LOGARITHMIC-CAPACITY - `Erdos1040.robinConstant_empty`

The Robin constant of the empty planar source is positive infinity because no probability measure is supported on the empty source.

Module: `Erdos1040.LogarithmicCapacity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.robinConstant_empty : Eq.{1} (Erdos1040.robinConstant EmptyCollection.emptyCollection.{0}) Top.top.{0}
```

## E1040-LOGARITHMIC-CAPACITY - `Erdos1040.logarithmicCapacity_empty`

The logarithmic capacity of the empty planar source is zero.

Module: `Erdos1040.LogarithmicCapacity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.logarithmicCapacity_empty : Eq.{1} (Erdos1040.logarithmicCapacity EmptyCollection.emptyCollection.{0})
  0
```

## E1040-LOGARITHMIC-CAPACITY - `Erdos1040.logarithmicCapacity_eq_zero_iff`

The defined logarithmic capacity is zero if and only if its actual Robin constant is positive infinity; the extended exponential preserves the singular infinite-energy convention.

Module: `Erdos1040.LogarithmicCapacity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.logarithmicCapacity_eq_zero_iff : ∀ (S : Set.{0} ℂ),
  Eq.{1} (Erdos1040.logarithmicCapacity S) 0 ↔ Eq.{1} (Erdos1040.robinConstant S) Top.top.{0}
```

## E1040-LOGARITHMIC-CAPACITY - `Erdos1040.one_le_logarithmicCapacity_iff`

The defined logarithmic capacity is at least one if and only if its actual Robin constant is at most zero in EReal.

Module: `Erdos1040.LogarithmicCapacity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.one_le_logarithmicCapacity_iff : ∀ (S : Set.{0} ℂ),
  LE.le.{0} 1 (Erdos1040.logarithmicCapacity S) ↔ LE.le.{0} (Erdos1040.robinConstant S) 0
```

## E1040-LOGARITHMIC-CAPACITY - `Erdos1040.robinConstant_eq_energy_sub_log_of_minimizer`

For every compact planar source, positive pair-distance bound D, and actual source probability minimizing nonnegativeLogEnergy D among all source probabilities, the Robin constant equals that actual extended energy embedded in EReal minus log D. The minimizing energy is allowed to be infinite.

Module: `Erdos1040.LogarithmicCapacity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.robinConstant_eq_energy_sub_log_of_minimizer : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    ∀ {D : ℝ},
      LT.lt.{0} 0 D →
        (∀ (z : ℂ),
            Membership.mem.{0, 0} S z → ∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) D) →
          ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S),
            (∀ (ν : MeasureTheory.ProbabilityMeasure.{0} ↑S),
                LE.le.{0} (Erdos1040.nonnegativeLogEnergy D μ) (Erdos1040.nonnegativeLogEnergy D ν)) →
              Eq.{1} (Erdos1040.robinConstant S)
                (HSub.hSub.{0, 0, 0} ↑(Erdos1040.nonnegativeLogEnergy D μ) ↑(Real.log D))
```

## E1040-LOGARITHMIC-CAPACITY - `Erdos1040.exists_finite_minimizer_of_one_le_logarithmicCapacity`

For every compact planar source with classical energy-defined logarithmic capacity at least one, and every positive real D bounding all source-pair distances, there exists an actual source probability globally minimizing nonnegativeLogEnergy D, with finite energy and energy.toReal at most log D. Nonemptiness and finiteness are proved from the capacity hypothesis; no source-potential property or geometric transfinite-diameter equivalence is assumed.

Module: `Erdos1040.LogarithmicCapacity`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_finite_minimizer_of_one_le_logarithmicCapacity : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    LE.le.{0} 1 (Erdos1040.logarithmicCapacity S) →
      ∀ {D : ℝ},
        LT.lt.{0} 0 D →
          (∀ (z : ℂ),
              Membership.mem.{0, 0} S z → ∀ (w : ℂ), Membership.mem.{0, 0} S w → LE.le.{0} (Dist.dist.{0} z w) D) →
            ∃ μ,
              (∀ (ν : MeasureTheory.ProbabilityMeasure.{0} ↑S),
                  LE.le.{0} (Erdos1040.nonnegativeLogEnergy D μ) (Erdos1040.nonnegativeLogEnergy D ν)) ∧
                Ne.{1} (Erdos1040.nonnegativeLogEnergy D μ) Top.top.{0} ∧
                  LE.le.{0} (Erdos1040.nonnegativeLogEnergy D μ).toReal (Real.log D)
```

## E1040-COMPACT-CAPACITY - `Erdos1040.hasArbitrarilySmallLemniscates_of_one_le_logarithmicCapacity`

For every compact complex source S whose literal logarithmic capacity is at least one, the exact positive-degree roots-in-S strict-small-area lemniscate conclusion holds. Logarithmic capacity is the negative exponential of the infimum of actual normalized singular energies, with scale independence. A finite global minimizing probability, global potential nonnegativity and all support geometry are proved from those hypotheses.

Module: `Erdos1040.CapacityTheorem`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.hasArbitrarilySmallLemniscates_of_one_le_logarithmicCapacity : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S → LE.le.{0} 1 (Erdos1040.logarithmicCapacity S) → Erdos1040.HasArbitrarilySmallLemniscates S
```

## E1040-CAP1 - `Erdos1040.erdos1040_capacity_one`

For every compact complex source S of logarithmic capacity exactly one and every positive real epsilon, there exists an actual complex polynomial p which is monic, has positive natural degree, has every complex root in S, and whose strict unit sublevel set has planar Lebesgue volume less than ofReal(epsilon). Capacity is the literal Robin-infimum energy definition. No boundary smoothness, connectedness, area-zero, source probability or potential property is assumed.

Module: `Erdos1040.CapacityTheorem`. Kind: theorem. Role: target.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.erdos1040_capacity_one : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S →
    Eq.{1} (Erdos1040.logarithmicCapacity S) 1 →
      ∀ {ε : ℝ},
        LT.lt.{0} 0 ε →
          ∃ p,
            Polynomial.Monic.{0} p ∧
              LT.lt.{0} 0 (Polynomial.natDegree.{0} p) ∧
                (∀ (z : ℂ), Polynomial.IsRoot.{0} p z → Membership.mem.{0, 0} S z) ∧
                  LT.lt.{0}
                    (MeasureTheory.MeasureSpace.volume.{0}
                      (Set.ofPred.{0} fun z => LT.lt.{0} (Norm.norm.{0} (Polynomial.eval.{0} z p)) 1))
                    (ENNReal.ofReal ε)
```

## E1040-GT1 - `Erdos1040.hasArbitrarilySmallLemniscates_of_one_lt_logarithmicCapacity`

Every compact complex source S of logarithmic capacity strictly greater than one has arbitrarily small strict unit lemniscate area with positive degree and all roots in S. This is a local nonquantitative proof of the already known greater-than-one case; it asserts no rate or asymptotic optimality.

Module: `Erdos1040.CapacityTheorem`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.hasArbitrarilySmallLemniscates_of_one_lt_logarithmicCapacity : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S → LT.lt.{0} 1 (Erdos1040.logarithmicCapacity S) → Erdos1040.HasArbitrarilySmallLemniscates S
```

## E1040-CAPACITY-ONLY - `Erdos1040.nonnegativeLogEnergy_eq_top_of_countable`

For every countable set S of complex numbers, every positive real scale D, and every actual probability measure mu on subtype S, nonnegativeLogEnergy D mu is positive infinity. No compactness, boundedness, scale-distance bound or minimizer assumption is needed.

Module: `Erdos1040.CountableSources`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.nonnegativeLogEnergy_eq_top_of_countable : ∀ {S : Set.{0} ℂ},
  Set.Countable.{0} S →
    ∀ {D : ℝ},
      LT.lt.{0} 0 D →
        ∀ (μ : MeasureTheory.ProbabilityMeasure.{0} ↑S), Eq.{1} (Erdos1040.nonnegativeLogEnergy D μ) Top.top.{0}
```

## E1040-CAPACITY-ONLY - `Erdos1040.logarithmicCapacity_eq_zero_of_countable`

For every countable set S of complex numbers, the already defined logarithmicCapacity S is zero. This is an identity for the existing literal Robin-infimum definition; its classical-capacity interpretation is asserted only on bounded or compact sets.

Module: `Erdos1040.CountableSources`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.logarithmicCapacity_eq_zero_of_countable : ∀ {S : Set.{0} ℂ},
  Set.Countable.{0} S → Eq.{1} (Erdos1040.logarithmicCapacity S) 0
```

## E1040-CAPACITY-ONLY - `Erdos1040.smallCountableSource`

The explicit complex source consisting of zero together with all reciprocal natural numbers 1/(n+4), with n ranging over every natural number including zero. The denominator n+4 is cast into the complex numbers.

Module: `Erdos1040.CountableSources`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.smallCountableSource : Set.{0} ℂ
```

## E1040-CAPACITY-ONLY - `Erdos1040.smallCountableSource_countable`

The exact set smallCountableSource is countable.

Module: `Erdos1040.CountableSources`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.smallCountableSource_countable : Set.Countable.{0} Erdos1040.smallCountableSource
```

## E1040-CAPACITY-ONLY - `Erdos1040.smallCountableSource_isCompact`

The exact set smallCountableSource is compact in the usual topology on the complex numbers.

Module: `Erdos1040.CountableSources`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.smallCountableSource_isCompact : IsCompact.{0} Erdos1040.smallCountableSource
```

## E1040-CAPACITY-ONLY - `Erdos1040.smallCountableSource_infinite`

The exact set smallCountableSource is infinite.

Module: `Erdos1040.CountableSources`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.smallCountableSource_infinite : Set.Infinite.{0} Erdos1040.smallCountableSource
```

## E1040-CAPACITY-ONLY - `Erdos1040.smallCountableSource_subset_closedBall`

Every member of smallCountableSource lies in the closed Euclidean ball in the complex plane centered at zero and of real radius one quarter.

Module: `Erdos1040.CountableSources`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.smallCountableSource_subset_closedBall : Erdos1040.smallCountableSource ⊆
  Metric.closedBall.{0} 0 (1 / 4)
```

## E1040-CAPACITY-ONLY - `Erdos1040.zero_mem_smallCountableSource`

The complex number zero belongs to the exact set smallCountableSource.

Module: `Erdos1040.CountableSources`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.zero_mem_smallCountableSource : Membership.mem.{0, 0} Erdos1040.smallCountableSource 0
```

## E1040-CAPACITY-ONLY - `Erdos1040.ball_three_quarters_subset_unitLemniscate`

For any positive number n and any complex root list indexed by Fin n, if every root has norm at most 1/4 then the strict unit lemniscate contains the open ball of radius 3/4 centered at zero.

Module: `Erdos1040.AreaObstruction`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.ball_three_quarters_subset_unitLemniscate : ∀ {n : ℕ},
  LT.lt.{0} 0 n →
    ∀ (roots : Fin n → ℂ),
      (∀ (i : Fin n), LE.le.{0} (Norm.norm.{0} (roots i)) (1 / 4)) →
        Metric.ball.{0} 0 (3 / 4) ⊆ Erdos1040.unitLemniscate roots
```

## E1040-CAPACITY-ONLY - `Erdos1040.volume_ball_three_quarters`

The planar Lebesgue measure of the open complex ball centered at zero with radius 3/4 equals ENNReal.ofReal (9*pi/16).

Module: `Erdos1040.AreaObstruction`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.volume_ball_three_quarters : Eq.{1}
  (MeasureTheory.MeasureSpace.volume.{0} (Metric.ball.{0} 0 (3 / 4)))
  (ENNReal.ofReal (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} 9 Real.pi) 16))
```

## E1040-CAPACITY-ONLY - `Erdos1040.volume_unitLemniscate_ge_nine_pi_sixteenths`

For any positive finite root list whose roots have norm at most 1/4, the planar Lebesgue measure of its strict unit lemniscate is at least ENNReal.ofReal (9*pi/16).

Module: `Erdos1040.AreaObstruction`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.volume_unitLemniscate_ge_nine_pi_sixteenths : ∀ {n : ℕ},
  LT.lt.{0} 0 n →
    ∀ (roots : Fin n → ℂ),
      (∀ (i : Fin n), LE.le.{0} (Norm.norm.{0} (roots i)) (1 / 4)) →
        LE.le.{0} (ENNReal.ofReal (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} 9 Real.pi) 16))
          (MeasureTheory.MeasureSpace.volume.{0} (Erdos1040.unitLemniscate roots))
```

## E1040-CAPACITY-ONLY - `Erdos1040.ball_three_quarters_subset_monic_sublevel`

For every monic complex polynomial of positive natural degree whose every complex root has norm at most 1/4, its strict unit sublevel contains the open ball centered at zero of radius 3/4.

Module: `Erdos1040.AreaObstruction`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.ball_three_quarters_subset_monic_sublevel : ∀ (p : Polynomial.{0} ℂ),
  Polynomial.Monic.{0} p →
    LT.lt.{0} 0 (Polynomial.natDegree.{0} p) →
      (∀ (z : ℂ), Polynomial.IsRoot.{0} p z → LE.le.{0} (Norm.norm.{0} z) (1 / 4)) →
        Metric.ball.{0} 0 (3 / 4) ⊆ Set.ofPred.{0} fun z => LT.lt.{0} (Norm.norm.{0} (Polynomial.eval.{0} z p)) 1
```

## E1040-CAPACITY-ONLY - `Erdos1040.volume_monic_sublevel_ge_nine_pi_sixteenths`

For every monic complex polynomial of positive natural degree whose every complex root has norm at most 1/4, its strict unit sublevel has planar Lebesgue measure at least ENNReal.ofReal (9*pi/16).

Module: `Erdos1040.AreaObstruction`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.volume_monic_sublevel_ge_nine_pi_sixteenths : ∀ (p : Polynomial.{0} ℂ),
  Polynomial.Monic.{0} p →
    LT.lt.{0} 0 (Polynomial.natDegree.{0} p) →
      (∀ (z : ℂ), Polynomial.IsRoot.{0} p z → LE.le.{0} (Norm.norm.{0} z) (1 / 4)) →
        LE.le.{0} (ENNReal.ofReal (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} 9 Real.pi) 16))
          (MeasureTheory.MeasureSpace.volume.{0}
            (Set.ofPred.{0} fun z => LT.lt.{0} (Norm.norm.{0} (Polynomial.eval.{0} z p)) 1))
```

## E1040-CAPACITY-ONLY - `Erdos1040.volume_plus_minus_four_quadratic_le`

The strict unit sublevel of the explicit complex function (z-4)*(z-(-4)) has planar Lebesgue measure at most ENNReal.ofReal (pi/8).

Module: `Erdos1040.AreaObstruction`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.volume_plus_minus_four_quadratic_le : LE.le.{0}
  (MeasureTheory.MeasureSpace.volume.{0}
    (Set.ofPred.{0} fun z =>
      LT.lt.{0} (Norm.norm.{0} (HMul.hMul.{0, 0, 0} (HSub.hSub.{0, 0, 0} z 4) (HSub.hSub.{0, 0, 0} z (-4)))) 1))
  (ENNReal.ofReal (HDiv.hDiv.{0, 0, 0} Real.pi 8))
```

## E1040-CAPACITY-ONLY - `Erdos1040.exists_plus_minus_four_monic_small_area`

There exists a monic complex polynomial of positive natural degree whose complex roots are exactly 4 and -4 and whose strict unit sublevel has planar Lebesgue measure at most ENNReal.ofReal (pi/8).

Module: `Erdos1040.AreaObstruction`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.exists_plus_minus_four_monic_small_area : ∃ p,
  Polynomial.Monic.{0} p ∧
    LT.lt.{0} 0 (Polynomial.natDegree.{0} p) ∧
      (∀ (z : ℂ), Polynomial.IsRoot.{0} p z ↔ Eq.{1} z 4 ∨ Eq.{1} z (-4)) ∧
        LE.le.{0}
          (MeasureTheory.MeasureSpace.volume.{0}
            (Set.ofPred.{0} fun z => LT.lt.{0} (Norm.norm.{0} (Polynomial.eval.{0} z p)) 1))
          (ENNReal.ofReal (HDiv.hDiv.{0, 0, 0} Real.pi 8))
```

## E1040-CAPACITY-ONLY - `Erdos1040.plus_minus_four_area_bound_lt_ball_obstruction`

ENNReal.ofReal (pi/8) is strictly less than ENNReal.ofReal (9*pi/16).

Module: `Erdos1040.AreaObstruction`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.plus_minus_four_area_bound_lt_ball_obstruction : LT.lt.{0}
  (ENNReal.ofReal (HDiv.hDiv.{0, 0, 0} Real.pi 8))
  (ENNReal.ofReal (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} 9 Real.pi) 16))
```

## E1040-CAPACITY-ONLY - `Erdos1040.geometricMeanSeparation_dilate`

For every finite complex tuple of order N at least two and every positive real c, multiplying each entry by c multiplies the exact geometric mean separation by c. Repeated entries are allowed.

Module: `Erdos1040.GeometricScaling`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.geometricMeanSeparation_dilate : ∀ {N : ℕ},
  LE.le.{0} 2 N →
    ∀ (x : Fin N → ℂ) {c : ℝ},
      LT.lt.{0} 0 c →
        Eq.{1} (Erdos1040.geometricMeanSeparation fun i => HMul.hMul.{0, 0, 0} (↑c) (x i))
          (HMul.hMul.{0, 0, 0} c (Erdos1040.geometricMeanSeparation x))
```

## E1040-CAPACITY-ONLY - `Erdos1040.finiteDiameter_dilate`

For every complex source S, every finite order N at least two and every positive real c, the exact extended finite diameter of the dilation image c*S equals ofReal(c) times the finite diameter of S. Empty and unbounded sources are included.

Module: `Erdos1040.GeometricScaling`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.finiteDiameter_dilate : ∀ (S : Set.{0} ℂ) {N : ℕ},
  LE.le.{0} 2 N →
    ∀ {c : ℝ},
      LT.lt.{0} 0 c →
        Eq.{1} (Erdos1040.finiteDiameter (Set.image.{0, 0} (fun z => HMul.hMul.{0, 0, 0} (↑c) z) S) N)
          (HMul.hMul.{0, 0, 0} (ENNReal.ofReal c) (Erdos1040.finiteDiameter S N))
```

## E1040-CAPACITY-ONLY - `Erdos1040.transfiniteDiameter_dilate`

For every complex source S and every positive real c, the exact geometric transfinite diameter of the dilation image c*S equals ofReal(c) times that of S, with the extended zero and infinity conventions preserved.

Module: `Erdos1040.GeometricScaling`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.transfiniteDiameter_dilate : ∀ (S : Set.{0} ℂ) {c : ℝ},
  LT.lt.{0} 0 c →
    Eq.{1} (Erdos1040.transfiniteDiameter (Set.image.{0, 0} (fun z => HMul.hMul.{0, 0, 0} (↑c) z) S))
      (HMul.hMul.{0, 0, 0} (ENNReal.ofReal c) (Erdos1040.transfiniteDiameter S))
```

## E1040-CAPACITY-ONLY - `Erdos1040.transfiniteDiameter_eq_zero_of_countable_compact`

Every countable compact set S of complex numbers has geometric transfiniteDiameter S equal to zero. The theorem uses the actual pair-product geometric definition, not logarithmic-capacity equality or a supplied energy hypothesis.

Module: `Erdos1040.GeometricScaling`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.transfiniteDiameter_eq_zero_of_countable_compact : ∀ {S : Set.{0} ℂ},
  IsCompact.{0} S → Set.Countable.{0} S → Eq.{1} (Erdos1040.transfiniteDiameter S) 0
```

## E1040-CAPACITY-ONLY - `Erdos1040.minimalLemniscateArea`

For each complex source F, minimalLemniscateArea F is the extended nonnegative-real infimum of planar Lebesgue areas of strict unit sublevel sets of all actual complex polynomials p that are monic, have positive natural degree, and have every complex root in F. No attainment is asserted; an empty admissible family has infimum infinity.

Module: `Erdos1040.CapacityDependence`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.minimalLemniscateArea : Set.{0} ℂ → ENNReal
```

## E1040-CAPACITY-ONLY - `Erdos1040.minimalLemniscateArea_le_of_monic`

For every complex source F and every actual monic positive-degree complex polynomial with every root in F, the defined area infimum for F is at most the planar Lebesgue area of that polynomial strict unit sublevel set.

Module: `Erdos1040.CapacityDependence`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.minimalLemniscateArea_le_of_monic : ∀ {F : Set.{0} ℂ} (p : Polynomial.{0} ℂ),
  Polynomial.Monic.{0} p →
    LT.lt.{0} 0 (Polynomial.natDegree.{0} p) →
      (∀ (z : ℂ), Polynomial.IsRoot.{0} p z → Membership.mem.{0, 0} F z) →
        LE.le.{0} (Erdos1040.minimalLemniscateArea F)
          (MeasureTheory.MeasureSpace.volume.{0}
            (Set.ofPred.{0} fun z => LT.lt.{0} (Norm.norm.{0} (Polynomial.eval.{0} z p)) 1))
```

## E1040-CAPACITY-ONLY - `Erdos1040.smallCountableSource_minimalLemniscateArea_ge`

The defined area infimum for the exact smallCountableSource is at least ofReal(9*pi/16). This lower bound covers every actual monic positive-degree complex polynomial whose every root belongs to that source.

Module: `Erdos1040.CapacityDependence`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.smallCountableSource_minimalLemniscateArea_ge : LE.le.{0}
  (ENNReal.ofReal (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} 9 Real.pi) 16))
  (Erdos1040.minimalLemniscateArea Erdos1040.smallCountableSource)
```

## E1040-CAPACITY-ONLY - `Erdos1040.largeCountableSource`

The explicit complex source obtained by inserting 4 and -4 into the exact smallCountableSource. The latter contains zero and every reciprocal 1/(n+4) for natural n.

Module: `Erdos1040.CapacityDependence`. Kind: definition. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
def Erdos1040.largeCountableSource : Set.{0} ℂ
```

## E1040-CAPACITY-ONLY - `Erdos1040.largeCountableSource_countable`

The exact set largeCountableSource is countable.

Module: `Erdos1040.CapacityDependence`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.largeCountableSource_countable : Set.Countable.{0} Erdos1040.largeCountableSource
```

## E1040-CAPACITY-ONLY - `Erdos1040.largeCountableSource_isCompact`

The exact set largeCountableSource is compact in the usual complex topology.

Module: `Erdos1040.CapacityDependence`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.largeCountableSource_isCompact : IsCompact.{0} Erdos1040.largeCountableSource
```

## E1040-CAPACITY-ONLY - `Erdos1040.largeCountableSource_infinite`

The exact set largeCountableSource is infinite.

Module: `Erdos1040.CapacityDependence`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.largeCountableSource_infinite : Set.Infinite.{0} Erdos1040.largeCountableSource
```

## E1040-CAPACITY-ONLY - `Erdos1040.largeCountableSource_minimalLemniscateArea_le`

The defined area infimum for the exact largeCountableSource is at most ofReal(pi/8), using an actual monic positive-degree quadratic whose roots are exactly 4 and -4.

Module: `Erdos1040.CapacityDependence`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.largeCountableSource_minimalLemniscateArea_le : LE.le.{0}
  (Erdos1040.minimalLemniscateArea Erdos1040.largeCountableSource) (ENNReal.ofReal (HDiv.hDiv.{0, 0, 0} Real.pi 8))
```

## E1040-CAPACITY-ONLY - `Erdos1040.capacity_only_dependence_counterexample`

There exist two compact infinite complex sources S and T such that each has geometric transfinite diameter zero and literal logarithmic capacity zero, while the exact monic positive-degree strict-lemniscate area infimum of T is strictly smaller than that of S.

Module: `Erdos1040.CapacityDependence`. Kind: theorem. Role: target.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.capacity_only_dependence_counterexample : ∃ S T,
  IsCompact.{0} S ∧
    Set.Infinite.{0} S ∧
      IsCompact.{0} T ∧
        Set.Infinite.{0} T ∧
          Eq.{1} (Erdos1040.transfiniteDiameter S) 0 ∧
            Eq.{1} (Erdos1040.transfiniteDiameter T) 0 ∧
              Eq.{1} (Erdos1040.logarithmicCapacity S) 0 ∧
                Eq.{1} (Erdos1040.logarithmicCapacity T) 0 ∧
                  LT.lt.{0} (Erdos1040.minimalLemniscateArea T) (Erdos1040.minimalLemniscateArea S)
```

## E1040-CAPACITY-ONLY - `Erdos1040.minimalLemniscateArea_not_determined_by_transfiniteDiameter`

There is no function from extended nonnegative reals to extended nonnegative reals whose value at the geometric transfinite diameter of every closed infinite complex source equals that source exact monic positive-degree strict-lemniscate area infimum.

Module: `Erdos1040.CapacityDependence`. Kind: theorem. Role: target.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.minimalLemniscateArea_not_determined_by_transfiniteDiameter : ¬∃ f,
    ∀ (F : Set.{0} ℂ),
      IsClosed.{0} F →
        Set.Infinite.{0} F → Eq.{1} (Erdos1040.minimalLemniscateArea F) (f (Erdos1040.transfiniteDiameter F))
```

## E1040-CAPACITY-ONLY - `Erdos1040.minimalLemniscateArea_not_determined_by_logarithmicCapacity`

There is no function from extended nonnegative reals to extended nonnegative reals whose value at the literal logarithmic capacity of every compact infinite complex source equals that source exact monic positive-degree strict-lemniscate area infimum. The classical-capacity interpretation is restricted to compact sources.

Module: `Erdos1040.CapacityDependence`. Kind: theorem. Role: target.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.minimalLemniscateArea_not_determined_by_logarithmicCapacity : ¬∃ f,
    ∀ (F : Set.{0} ℂ),
      IsCompact.{0} F →
        Set.Infinite.{0} F → Eq.{1} (Erdos1040.minimalLemniscateArea F) (f (Erdos1040.logarithmicCapacity F))
```

## E1040-FULL - `Erdos1040.minimalLemniscateArea_eq_zero_of_arbitrarily_small_polynomials`

For every complex source F, if for every positive real epsilon there is an actual monic positive-degree complex polynomial with every root in F and strict unit-sublevel planar area below epsilon, then the exact area infimum minimalLemniscateArea F is zero. This is an explicitly conditional conversion lemma, not an assumed threshold result.

Module: `Erdos1040.AreaInfimumEndpoints`. Kind: theorem. Role: supporting.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.minimalLemniscateArea_eq_zero_of_arbitrarily_small_polynomials : ∀ {F : Set.{0} ℂ},
  (∀ (ε : ℝ),
      LT.lt.{0} 0 ε →
        ∃ p,
          Polynomial.Monic.{0} p ∧
            LT.lt.{0} 0 (Polynomial.natDegree.{0} p) ∧
              (∀ (z : ℂ), Polynomial.IsRoot.{0} p z → Membership.mem.{0, 0} F z) ∧
                LT.lt.{0}
                  (MeasureTheory.MeasureSpace.volume.{0}
                    (Set.ofPred.{0} fun z => LT.lt.{0} (Norm.norm.{0} (Polynomial.eval.{0} z p)) 1))
                  (ENNReal.ofReal ε)) →
    Eq.{1} (Erdos1040.minimalLemniscateArea F) 0
```

## E1040-FULL - `Erdos1040.minimalLemniscateArea_eq_zero_of_one_le_transfiniteDiameter`

For every closed infinite complex source F with its actual geometric transfinite diameter at least one, its exact monic positive-degree strict-lemniscate area infimum minimalLemniscateArea F equals zero. This is the literal vanishing-infimum formulation of original Problem 4, derived from the previously admitted positive-tolerance theorem.

Module: `Erdos1040.AreaInfimumEndpoints`. Kind: theorem. Role: target.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.minimalLemniscateArea_eq_zero_of_one_le_transfiniteDiameter : ∀ {F : Set.{0} ℂ},
  IsClosed.{0} F →
    Set.Infinite.{0} F → LE.le.{0} 1 (Erdos1040.transfiniteDiameter F) → Eq.{1} (Erdos1040.minimalLemniscateArea F) 0
```

## E1040-CAP1 - `Erdos1040.minimalLemniscateArea_eq_zero_of_one_le_logarithmicCapacity`

For every compact complex source F with its literal Robin-energy logarithmic capacity at least one, its exact monic positive-degree strict-lemniscate area infimum minimalLemniscateArea F equals zero. No regularity, positive-area or supplied measure hypothesis is added; capacity exactly one is included.

Module: `Erdos1040.AreaInfimumEndpoints`. Kind: theorem. Role: target.
Recorded status: machine checks and version-bound AI correspondence review passed.

```text
theorem Erdos1040.minimalLemniscateArea_eq_zero_of_one_le_logarithmicCapacity : ∀ {F : Set.{0} ℂ},
  IsCompact.{0} F → LE.le.{0} 1 (Erdos1040.logarithmicCapacity F) → Eq.{1} (Erdos1040.minimalLemniscateArea F) 0
```
