import HRS.Equilibrium.Parametrix.Defs
import HRS.Equilibrium.Parametrix.PX2AuxD
import HRS.Duality.PairingExpansion
import HRS.Energy.Commutator.SliceAux
import HRS.Energy.Coercivity
import HRS.PDE.Toolbox.Kernel

/-!
# Packet PXS: the bound for `a_f` (`aCoef_bound`)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

theorem pxS_P2_le (f : Torus d → ℝ) :
    (⨆ z : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift f) z‖) ≤ posSeminorm 2 f := by
  unfold posSeminorm
  have h0 : ∀ j ∈ Finset.Icc 1 2, 0 ≤ ⨆ x : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift f) x‖ :=
    fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  exact Finset.single_le_sum h0 (by simp)

/-- The gradient of a smooth function is Lipschitz with constant `d · posSeminorm 2 f`. -/
theorem pxS_grad_lip (f : Torus d → ℝ) (hf : Torus.IsSmooth f) (x y : Torus d) :
    ‖Torus.grad f x - Torus.grad f y‖ ≤ d * posSeminorm 2 f * KernelGrad.tdist x y := by
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) := hf
  have hf2 : Torus.IsCk 2 f :=
    ContDiff.of_le hF (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
      WithTop.coe_le_coe.mpr le_top)
  have hbdd : BddAbove (Set.range fun z : Euc d => ‖iteratedFDeriv ℝ 2 (Torus.lift f) z‖) :=
    Torus.bddAbove_norm_iteratedFDeriv_lift 2 f (by simpa [Torus.IsCk] using hf2)
  set P := ⨆ z : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift f) z‖ with hP
  have hP0 : 0 ≤ P := Real.iSup_nonneg fun _ => norm_nonneg _
  have hc : ∀ j, |Torus.partialDeriv j f x - Torus.partialDeriv j f y| ≤ P * KernelGrad.tdist x y := by
    intro j
    have ha : Torus.IsCk 1 (Torus.partialDeriv j f) := PDE.isCk_one_partialDeriv j f hf2
    have h := PDE.Kern.abs_sub_le_iSup_mul_tdist ha x y
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (KernelGrad.tdist_nonneg x y))
    refine ciSup_le fun z => ?_
    rw [← norm_iteratedFDeriv_one]
    refine (norm_lift_partialDeriv_le hf j 1 z).trans ?_
    exact le_ciSup hbdd z
  have hv := Duality.norm_euc_le_sum (Torus.grad f x - Torus.grad f y)
  calc ‖Torus.grad f x - Torus.grad f y‖ ≤ ∑ j, |(Torus.grad f x - Torus.grad f y) j| := hv
    _ ≤ ∑ _j : Fin d, P * KernelGrad.tdist x y := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [PiLp.sub_apply, Duality.grad_apply_eq_partialDeriv, Duality.grad_apply_eq_partialDeriv]
        exact hc j
    _ = d * P * KernelGrad.tdist x y := by simp; ring
    _ ≤ d * posSeminorm 2 f * KernelGrad.tdist x y := by
        have := pxS_P2_le f
        have ht := KernelGrad.tdist_nonneg x y
        gcongr

theorem pxS_aCoef_bound (H : ParxHyp d s V β ρ) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      AEStronglyMeasurable (aCoef d s ρ f) (withDensityReal ρ) ∧
      ∀ x, |aCoef d s ρ f x| ≤ Ca * posSeminorm 2 f := by
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) H.two_le
  have hs0 := H.s_nonneg
  have hsd := H.s_lt
  have hρ := H.rho_smooth
  have hρc : Continuous ρ :=
    PDE.MFAux.continuous_of_isCk (PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1)
  obtain ⟨Cg, hCg⟩ := PDE.periodicRieszGrad_bound_tdist H.two_le hs0 hsd
  obtain ⟨Λ, hΛ0, hΛ⟩ := Duality.bounded_of_continuous hρc
  have hΛ' : ∀ x, ρ x ≤ Λ := fun x => (le_abs_self _).trans (hΛ x)
  set φ : Torus d → ℝ := fun z => KernelGrad.tdist z 0 ^ (-s) + KernelGrad.tdist z 0 with hφ
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => by
    have := Real.rpow_nonneg (KernelGrad.tdist_nonneg z 0) (-s)
    have := KernelGrad.tdist_nonneg z 0
    simp only [hφ]; positivity
  have hφm : Measurable φ :=
    (((CoercAux.continuous_tdist_zero.measurable).pow_const _).add
      CoercAux.continuous_tdist_zero.measurable)
  have hφi : Integrable φ :=
    (Commutator.SliceAux.integrable_tdist_rpow hd0 hs0 hsd).add
      (CoercAux.continuous_tdist_zero.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hI0 : 0 ≤ ∫ z, φ z := integral_nonneg hφ0
  refine ⟨(1 / 2) * d * max Cg 0 * Λ * ∫ z, φ z, by positivity, fun f hf => ?_⟩
  have hf2 : Torus.IsCk 2 f :=
    ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) from hf)
      (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top)
  have hP0 : 0 ≤ posSeminorm 2 f :=
    Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  -- pointwise bound of the transport kernel
  have hpt : ∀ x y : Torus d, ‖hTransport d s f x y‖ ≤
      d * posSeminorm 2 f * max Cg 0 * φ (x - y) := by
    intro x y
    unfold hTransport
    by_cases hxy : x = y
    · subst hxy
      simp only [sub_self, norm_zero, inner_zero_left]
      have := hφ0 (x - x)
      exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hP0) (le_max_right _ _)) (hφ0 _)
    · have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
      have ht : 0 < KernelGrad.tdist (x - y) 0 := by
        rw [KernelGrad.tdist_zero_right]
        refine norm_pos_iff.mpr fun h => hz ?_
        rw [← KernelGrad.mk_centeredRep (x - y), h]
        funext i; simp [Torus.mk]
      set t := KernelGrad.tdist (x - y) 0 with htdef
      have h1 := pxS_grad_lip f hf x y
      rw [KernelGrad.tdist_eq_sub_zero x y] at h1
      have h2 := hCg (x - y) hz
      have h2' : ‖periodicRieszGrad d s (x - y)‖ ≤ max Cg 0 * (t ^ (-s - 1) + 1) :=
        h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      have e : t * (t ^ (-s - 1) + 1) = t ^ (-s) + t := by
        have : t ^ (-s) = t ^ (-s - 1) * t := by
          rw [← Real.rpow_add_one ht.ne']; ring_nf
        rw [this]; ring
      calc ‖inner ℝ (Torus.grad f x - Torus.grad f y) (periodicRieszGrad d s (x - y))‖
          ≤ ‖Torus.grad f x - Torus.grad f y‖ * ‖periodicRieszGrad d s (x - y)‖ :=
            norm_inner_le_norm _ _
        _ ≤ (d * posSeminorm 2 f * t) * (max Cg 0 * (t ^ (-s - 1) + 1)) :=
            mul_le_mul h1 h2' (norm_nonneg _) (by positivity)
        _ = d * posSeminorm 2 f * max Cg 0 * (t * (t ^ (-s - 1) + 1)) := by ring
        _ = d * posSeminorm 2 f * max Cg 0 * φ (x - y) := by rw [e]
  have hgm : Measurable (periodicRieszGrad d s) := KernelGrad.measurable_periodicRieszGrad hsd
  have hgradc : Continuous (Torus.grad f) := Duality.grad_continuous hf2
  have hmeas : Measurable (fun p : Torus d × Torus d => hTransport d s f p.1 p.2) := by
    unfold hTransport
    refine Measurable.inner ?_ (hgm.comp (measurable_fst.sub measurable_snd))
    exact ((hgradc.measurable.comp measurable_fst).sub (hgradc.measurable.comp measurable_snd))
  refine ⟨?_, fun x => ?_⟩
  · have : StronglyMeasurable (fun x => ∫ y, hTransport d s f x y ∂(withDensityReal ρ)) := by
      have h1 : StronglyMeasurable (Function.uncurry fun x y => hTransport d s f x y) :=
        hmeas.stronglyMeasurable
      exact h1.integral_prod_right
    exact (this.const_mul (1 / 2)).aestronglyMeasurable
  · have hgi : Integrable (fun y => d * posSeminorm 2 f * max Cg 0 * φ (x - y)) (withDensityReal ρ) :=
      (CoercAux.integrable_conv_density hΛ' hφm hφi x).const_mul _
    have h1 : ‖∫ y, hTransport d s f x y ∂(withDensityReal ρ)‖ ≤
        ∫ y, d * posSeminorm 2 f * max Cg 0 * φ (x - y) ∂(withDensityReal ρ) :=
      norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall fun y => hpt x y)
    have h2 := CoercAux.integral_conv_density_le hΛ0 hΛ' hφ0 hφm hφi x
    have h3 : ∫ y, d * posSeminorm 2 f * max Cg 0 * φ (x - y) ∂(withDensityReal ρ) ≤
        d * posSeminorm 2 f * max Cg 0 * (Λ * ∫ z, φ z) := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left h2 (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hP0) (le_max_right _ _))
    unfold aCoef
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), ← Real.norm_eq_abs]
    calc 1 / 2 * ‖∫ y, hTransport d s f x y ∂(withDensityReal ρ)‖
        ≤ 1 / 2 * (d * posSeminorm 2 f * max Cg 0 * (Λ * ∫ z, φ z)) :=
          mul_le_mul_of_nonneg_left (h1.trans h3) (by norm_num)
      _ = _ := by ring

end HRS.Parx

end
