import HRS.Whole.CriticalNoise

/-!
# S8.6 `finite_noise`, packet 1 (S86): `IsClassicalAdjointW` does not see negative times

`IsClassicalAdjointW C t φ f` constrains `f r` only for `r ∈ [0,t]` (and `f t = φ`).  Hence
`propagatorW C r t φ = Classical.choose _ r` is an unconstrained junk value for `r < 0`, and the feature
`gradFeature … r x` of the frozen `HRS.Whole.finite_noise` (whose integrand `Φ` uses the raw time `r`, and whose
conclusion `IsHSIntegrand` asks `IsProgressive` on all of `Iic τ`, negative times included) is, for `r < 0`, a
value that depends on the choice made by `Classical.choose`.  The lemma below shows that any solution can be
changed arbitrarily outside `[0,t]`: nothing can be proved about the choice off `[0,t]`.
See `docs/S86_PLAN.md`.  Helper names carry the prefix `s86_`; namespace `HRS.MS.FinNoise`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.FinNoise

open HRS.Whole

variable {d : ℕ}

/-- A classical adjoint solution may be modified arbitrarily outside `[0,t]`. -/
theorem s86_adjoint_modify (C : WholeCoeff d) (t : ℝ) (ht : 0 ≤ t) (φ : Euc d → ℝ)
    (f g : ℝ → Euc d → ℝ) (hf : IsClassicalAdjointW C t φ f)
    (hfg : ∀ r ∈ Set.Icc 0 t, g r = f r) : IsClassicalAdjointW C t φ g where
  c2 := fun r hr => by rw [hfg r hr]; exact hf.c2 r hr
  bdd := fun j hj => by
    obtain ⟨B, hB⟩ := hf.bdd j hj
    exact ⟨B, fun r hr x => by rw [hfg r hr]; exact hB r hr x⟩
  cont_c2 := fun j hj =>
    (hf.cont_c2 j hj).congr fun p => by rw [hfg p.1.1 p.1.2]
  terminal := by
    rw [hfg t ⟨ht, le_rfl⟩]; exact hf.terminal
  time_deriv := fun x r hr => by
    have h1 : HasDerivAt (fun r' => f r' x) (-(generatorW C r (f r) x)) r := hf.time_deriv x r hr
    have h2 : (fun r' => f r' x) =ᶠ[𝓝 r] fun r' => g r' x := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with r' hr'
      rw [hfg r' (Set.Ioo_subset_Icc_self hr')]
    rw [hfg r (Set.Ioo_subset_Icc_self hr)]
    exact h1.congr_of_eventuallyEq h2.symm
  cont_time_deriv :=
    hf.cont_time_deriv.congr fun p => by rw [hfg p.1.1 p.1.2]
  bdd_time_deriv := by
    obtain ⟨B, hB⟩ := hf.bdd_time_deriv
    exact ⟨B, fun r hr x => by rw [hfg r hr]; exact hB r hr x⟩

end HRS.MS.FinNoise
