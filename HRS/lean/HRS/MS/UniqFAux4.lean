import HRS.MS.UniqFAux3
import HRS.MS.StarTie

/-!
# UNIQ-F, part 4: from the hypotheses of `fixed_equation` to the data of `uniqf_unique_pos`

* `uniqf_good_of_density`: a probability density slice `f` of class `C^ℓ` (`ℓ ≥ 1`) with `weightedSupE ℓ L f ≤ ofReal Λ`
  (`L ≥ d + 3`) is a good slice with constants `(A, A, 1)`, `A = (1 + d + 1) max Λ 0`.
* `uniqf_drift_bound`: `cbNormVecE K v ≤ ofReal Λ` gives `‖v x‖ ≤ max Λ 0`.
* `uniqf_unique_of_pos`: uniqueness of classical adjoint solutions of `fixedEqCoeff b.s b.M b.Q ν c ρ` for `ν > 0` under the
  slice hypotheses of `fixed_equation` (no regime, no force, no continuity in time is used).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.UniqF

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Lc HRS.MS.UniqQ HRS.MS.Go

variable {d : ℕ}

theorem uniqf_norm_le_cbNorm {f : Euc d → ℝ} {r : ℕ} (hf : MemCb r f) {j : ℕ} (hj : j ≤ r) (x : Euc d) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ HRS.cbNorm r f := by
  unfold HRS.cbNorm
  have hmem : j ∈ Finset.range (r + 1) := Finset.mem_range.2 (by omega)
  have h1 : ‖iteratedFDeriv ℝ j f x‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j f z‖ :=
    le_ciSup (hf.2 j hj) x
  have h2 : ⨆ z, ‖iteratedFDeriv ℝ j f z‖ ≤ ∑ i ∈ Finset.range (r + 1), ⨆ z, ‖iteratedFDeriv ℝ i f z‖ :=
    Finset.single_le_sum (f := fun i => ⨆ z, ‖iteratedFDeriv ℝ i f z‖)
      (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) hmem
  exact h1.trans h2

theorem uniqf_good_of_density {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {L Λ : ℝ} (hL : (d : ℝ) + 3 ≤ L) {f : Euc d → ℝ}
    (hp : HRS.Whole.IsProbDensity f) (hc : ContDiff ℝ ℓ f) (hw : weightedSupE ℓ L f ≤ ENNReal.ofReal Λ) :
    UqfGood f ((∑ j ∈ Finset.range 2, (d : ℝ) ^ j + 1) * max Λ 0)
      ((∑ j ∈ Finset.range 2, (d : ℝ) ^ j + 1) * max Λ 0) 1 := by
  obtain ⟨hmem, hfin, hle⟩ := s55f_regular_slice (n := ℓ) 1 hℓ hL hc hw
  have hcb : HRS.cbNorm 1 f ≤ (∑ j ∈ Finset.range 2, (d : ℝ) ^ j + 1) * max Λ 0 :=
    (le_add_of_nonneg_right ENNReal.toReal_nonneg).trans hle
  have hint : Integrable f := by
    by_contra h
    have := hp.integral_one
    rw [integral_undef h] at this
    exact zero_ne_one this
  refine ⟨hc.of_le (by exact_mod_cast hℓ), hint, fun y => ?_, fun y => ?_, ?_⟩
  · have := uniqf_norm_le_cbNorm hmem (j := 0) (by norm_num) y
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this.trans hcb
  · have := uniqf_norm_le_cbNorm hmem (j := 1) le_rfl y
    rw [norm_iteratedFDeriv_one] at this
    exact this.trans hcb
  · have : ∀ y, |f y| = f y := fun y => abs_of_nonneg (hp.nonneg y)
    simp_rw [this]
    exact hp.integral_one.le

theorem uniqf_drift_bound {K : ℕ} {Λ : ℝ} {v : Euc d → Euc d} (h : cbNormVecE K v ≤ ENNReal.ofReal Λ) (x : Euc d) :
    ‖v x‖ ≤ max Λ 0 := by
  unfold cbNormVecE at h
  have h0 : (0 : ℕ) ∈ Finset.range (K + 1) := Finset.mem_range.2 (by omega)
  have h1 : (⨆ z : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ 0 v z‖) ≤ ENNReal.ofReal Λ :=
    (Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ j v z‖)
      (fun _ _ => bot_le) h0).trans h
  have h2 : ENNReal.ofReal ‖v x‖ ≤ ENNReal.ofReal Λ := by
    refine le_trans ?_ h1
    have := le_iSup (fun z : Euc d => ENNReal.ofReal ‖iteratedFDeriv ℝ 0 v z‖) x
    simpa [norm_iteratedFDeriv_zero] using this
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
  rwa [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_ofReal'] at this

/-- **uniqueness of classical adjoint solutions of `fixedEqCoeff`, `ν > 0`, under the slice hypotheses of `fixed_equation`** -/
theorem uniqf_unique_of_pos (b : WholeBounds d) (hb : b.Valid) {ν : ℝ} (hν : 0 < ν) {c : ℝ → Euc d → Euc d}
    {ρ : ℝ → Euc d → ℝ} {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hdens : ∀ t ∈ Set.Icc (0 : ℝ) b.T, HRS.Whole.IsProbDensity (ρ t) ∧ ContDiff ℝ ℓ (ρ t) ∧
      weightedSupE ℓ b.L (ρ t) ≤ ENNReal.ofReal b.Λ)
    (hdrift : ∀ t ∈ Set.Icc (0 : ℝ) b.T, cbNormVecE ℓ (c t) ≤ ENNReal.ofReal b.Λ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b.T) {φ : Euc d → ℝ} {f₁ f₂ : ℝ → Euc d → ℝ}
    (h₁ : IsClassicalAdjointW (fixedEqCoeff b.s b.M b.Q ν c ρ) t φ f₁)
    (h₂ : IsClassicalAdjointW (fixedEqCoeff b.s b.M b.Q ν c ρ) t φ f₂) :
    ∀ r ∈ Set.Icc (0 : ℝ) t, f₁ r = f₂ r := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hL := hb.hL
  have hk0 : (0 : ℝ) ≤ b.k := Nat.cast_nonneg b.k
  have hs0 := hb.hs0
  have hdL : (d : ℝ) + 3 ≤ b.L := by linarith
  have hsub : ∀ r ∈ Set.Icc (0 : ℝ) t, r ∈ Set.Icc (0 : ℝ) b.T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  exact uniqf_unique_pos hν hb.hs0 hb.hsd b.M b.Q ht.1
    (fun r hr => uniqf_good_of_density hℓ hdL (hdens r (hsub r hr)).1 (hdens r (hsub r hr)).2.1
      (hdens r (hsub r hr)).2.2)
    (fun r hr x => uniqf_drift_bound (hdrift r (hsub r hr)) x) h₁ h₂

/-- `propagatorW` is the classical solution (`ν > 0`) -/
theorem uniqf_propagatorW_eq_of_pos (b : WholeBounds d) (hb : b.Valid) {ν : ℝ} (hν : 0 < ν)
    {c : ℝ → Euc d → Euc d} {ρ : ℝ → Euc d → ℝ} {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hdens : ∀ t ∈ Set.Icc (0 : ℝ) b.T, HRS.Whole.IsProbDensity (ρ t) ∧ ContDiff ℝ ℓ (ρ t) ∧
      weightedSupE ℓ b.L (ρ t) ≤ ENNReal.ofReal b.Λ)
    (hdrift : ∀ t ∈ Set.Icc (0 : ℝ) b.T, cbNormVecE ℓ (c t) ≤ ENNReal.ofReal b.Λ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b.T) {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW (fixedEqCoeff b.s b.M b.Q ν c ρ) t φ f) :
    ∀ r ∈ Set.Icc (0 : ℝ) t, propagatorW (fixedEqCoeff b.s b.M b.Q ν c ρ) r t φ = f r :=
  uniqf_unique_of_pos b hb hν hℓ hdens hdrift ht (HRS.MS.Fcau.propagatorW_isClassical ⟨f, hf⟩) hf

end HRS.MS.UniqF
