import HRS.Main.Rel513RieszA
import HRS.Equilibrium.QuadraticVariance
import HRS.Equilibrium.ResponseVariance
import HRS.Equilibrium.MarginalDensity
import HRS.Energy.Commutator.AbsConv
import HRS.Duality.PairingExpansion

/-!
# HRS.Main.Rel513RieszB -- packet rel513, part 2: the kernel `h_φ` and measurability of the remainder

Generic facts on `h = commKernel (periodicRieszGrad d s) (Torus.grad φ)` for smooth `φ`
(measurable, symmetric, Lipschitz field with constant `d |cbNorm 2 φ|`, singular envelope with a
constant linear in `cbNorm 2 φ`), the formula `∫ f d(empirical X) = N⁻¹ ∑ f(X_i)`, and
`stationaryRemainder_measurable_proof`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Main

variable {d : ℕ}

theorem rel513_cbNorm_nonneg (k : ℕ) (φ : Torus d → ℝ) : 0 ≤ Torus.cbNorm k φ := by
  unfold Torus.cbNorm
  exact Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem rel513_isCk2 {f : Torus d → ℝ} (hf : Torus.IsSmooth f) : Torus.IsCk 2 f :=
  ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) from hf)
    (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top)

theorem rel513_gradLip {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    HRS.IsLipschitzVF (Torus.cbNorm 2 φ * d) (Torus.grad φ) := by
  have hf := rel513_isCk2 hφ
  intro x y
  have hc : ∀ j, |Torus.partialDeriv j φ x - Torus.partialDeriv j φ y|
      ≤ Torus.cbNorm 2 φ * KernelGrad.tdist x y := fun j => by
    have h := PDE.R2Aux.isLipschitz_partialDeriv hf j x y
    exact h
  have hv := Duality.norm_euc_le_sum (Torus.grad φ x - Torus.grad φ y)
  calc ‖Torus.grad φ x - Torus.grad φ y‖ ≤ ∑ j, |(Torus.grad φ x - Torus.grad φ y) j| := hv
    _ ≤ ∑ _j : Fin d, Torus.cbNorm 2 φ * KernelGrad.tdist x y := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [PiLp.sub_apply, Duality.grad_apply_eq_partialDeriv, Duality.grad_apply_eq_partialDeriv]
        exact hc j
    _ = Torus.cbNorm 2 φ * d * KernelGrad.tdist x y := by simp; ring

theorem rel513_tdist_eq_eucDist (x y : Torus d) :
    KernelGrad.tdist x y = Torus.eucDist x y := by
  obtain ⟨w, hw, hw'⟩ := KernelGrad.exists_mk_box (x - y)
  have h1 : KernelGrad.tdist x y = Torus.eucDist (x - y) 0 := by
    rw [KernelGrad.tdist_eq_sub_zero, ← hw, KernelGrad.tdist_mk hw', PairCorrAux.eucDist_mk_zero' hw']
  rw [h1]
  unfold Torus.eucDist
  simp

/-- The singular envelope of `h_v = commKernel (periodicRieszGrad d s) v`, linear in `L`. -/
theorem rel513_envelope {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (v : Torus d → Euc d), 0 ≤ L → HRS.IsLipschitzVF L v →
      ∀ x y : Torus d, x ≠ y →
        |commKernel (periodicRieszGrad d s) v x y| ≤ (C * L) * singEnvelope s (Torus.eucDist x y) := by
  obtain ⟨C, hC0, hC⟩ := Commutator.commKernel_bound (d := d) (s := s) (by omega) hs0 hsd
  refine ⟨2 * C, by positivity, fun L v hL hv x y hxy => ?_⟩
  have h1 := hC L v hL hv x y hxy
  rw [rel513_tdist_eq_eucDist] at h1
  have hCL : 0 ≤ C * L := mul_nonneg hC0 hL
  refine h1.trans ?_
  by_cases hs : s = 0
  · subst hs
    simp only [singEnvelope, ite_true, neg_zero, Real.rpow_zero]
    have := abs_nonneg (Real.log (Torus.eucDist x y))
    nlinarith
  · simp only [singEnvelope, hs, ite_false]
    have : 0 ≤ Torus.eucDist x y ^ (-s) := by
      by_cases h0 : Torus.eucDist x y = 0
      · rw [h0]
        exact Real.rpow_nonneg le_rfl _
      · exact Real.rpow_nonneg (by unfold Torus.eucDist; positivity) _
    nlinarith

theorem rel513_measurable_comm {s : ℝ} (hsd : s < d) {v : Torus d → Euc d} (hv : Continuous v) :
    Measurable (Function.uncurry (commKernel (periodicRieszGrad d s) v)) := by
  have hmeas : Measurable (fun p : Torus d × Torus d =>
      commKernel (periodicRieszGrad d s) v p.1 p.2) := by
    unfold commKernel
    refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
    refine Measurable.inner ?_ ?_
    · exact (hv.measurable.comp measurable_fst).sub (hv.measurable.comp measurable_snd)
    · exact (KernelGrad.measurable_periodicRieszGrad hsd).comp (measurable_fst.sub measurable_snd)
  exact hmeas

theorem rel513_symm_comm {s : ℝ} (hsd : s < d) (v : Torus d → Euc d) (x y : Torus d) :
    commKernel (periodicRieszGrad d s) v x y = commKernel (periodicRieszGrad d s) v y x := by
  unfold commKernel
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [if_neg hxy, if_neg (Ne.symm hxy)]
    rw [← neg_sub x y, ← neg_sub (v x) (v y), KernelGrad.periodicRieszGrad_neg_of_lt hsd, inner_neg_neg]

theorem rel513_grad_continuous {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Continuous (Torus.grad φ) :=
  Duality.grad_continuous (rel513_isCk2 hφ)

theorem rel513_integral_empirical {N : ℕ} (X : Config d N) (f : Torus d → ℝ) :
    ∫ x, f x ∂(empirical X) = (N : ℝ)⁻¹ * ∑ i, f (X i) := by
  unfold empirical
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, Finset.mul_sum]
  · intro i _
    exact integrable_dirac enorm_lt_top

end HRS.Main

end
