---
date: 2024-12-23
title: Vanishing Derivatives
---

Suppose we have smooth $f : M \longrightarrow \mathbb{R}$.

$$
g=f \varphi_\alpha^{-1}=f \varphi_\beta^{-1} \varphi_\beta \varphi_\alpha^{-1}=h \varphi_\beta \varphi_\alpha^{-1}
$$

# Transition Maps are Smooth

$$
g=f \varphi_\alpha^{-1}=f \varphi_\beta^{-1} \varphi_\beta \varphi_\alpha^{-1}=h \varphi_\beta \varphi_\alpha^{-1}
$$

```lean4
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.AnalyticManifold
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

open Manifold

open SmoothManifoldWithCorners

theorem mfderivWithin_congr_of_eq_on_open
  {m n : ℕ} {M N : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [SmoothManifoldWithCorners (𝓡 n) N]
  (f g : M → N) (s : Set M)
  (ho : IsOpen s)
  (he : ∀ x ∈ s, f x = g x) :
  ∀ x ∈ s, mfderivWithin (𝓡 m) (𝓡 n) f s x = mfderivWithin (𝓡 m) (𝓡 n) g s x := by
    intros x hy
    exact mfderivWithin_congr (IsOpen.uniqueMDiffWithinAt ho hy) he (he x hy)
```

