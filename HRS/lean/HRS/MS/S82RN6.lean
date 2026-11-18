import HRS.MS.S82RN5
import HRS.MS.S82RM23

/-!
# S8.2 R02 (S82R), N6: the pointwise-weighted pin comparison for the reference ensembles (measure level)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators

namespace HRS.MS.S82R
open HRS.External HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem s82r_pin_measure (hd : 2 ≤ d) {q : Euc d → ℝ} (hq : ShortRangePole d q) (M : ℝ)
    {Mψ M₁ P β γ : ℝ} (hβ : 0 < β) (hγ : 0 ≤ γ)
    (hα : β * γ * (Real.exp (Mψ + (M₁ + P)) + Real.exp (Mψ + (M₁ + P)) ^ 2) < 1) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ ρμ : Euc d → ℝ, HRS.Whole.IsProbDensity ρμ → (∀ x, ρμ x ≤ M) →
      ∀ (μ : Measure (Euc d)), μ = HRS.Whole.withDensityReal ρμ →
      ∀ (V : WeakPotential μ), (∀ x y, V.q x y = q (x - y)) →
      V.γ = γ → ∀ {ψ0 : Euc d → ℝ}, IsField μ ψ0 Mψ M₁ →
      ∀ {m n : ℕ} [NeZero n] (p : Fin m → Euc d) (t : Fin m → ℝ), (∀ ℓ, 0 ≤ t ℓ) →
      ∀ {lam : ℝ}, 0 ≤ lam → (∑ ℓ, t ℓ) * γ + lam * n * γ ≤ P → ((n : ℝ) - 1) * lam ≤ β →
      ∀ (i0 : Fin n) {S : Set (Euc d)}, MeasurableSet S →
      |(fieldLaw V ψ0 lam n).real ((fun x : Fin n → Euc d => x i0) ⁻¹' S) -
        (fieldLaw V (s82r_Fld V p t Finset.univ ψ0) lam n).real ((fun x : Fin n → Euc d => x i0) ⁻¹' S)| ≤
        ∫ z in S, ∑ ℓ, t ℓ * (A * q (z - p ℓ) + B) ∂μ := by
  set K := Real.exp (Mψ + (M₁ + P)) with hK
  have hK0 : 0 < K := Real.exp_pos _
  obtain ⟨A, B, hA, hB, hsuper⟩ := s82r_super_pin hd hq M hβ hK0 hγ hα
  refine ⟨A, B, hA, hB, fun ρμ hρ hM μ hμ V hVq hVγ ψ0 hψ m n _ p t ht lam hlam hP hnl i0 S hS => ?_⟩
  subst hμ
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρμ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hqm : Measurable q := hq.measurable
  have hq0 := hq.nonneg
  have hrow : ∀ u : Euc d, ∫ z, q (z - u) ∂(HRS.Whole.withDensityReal ρμ) ≤ γ := fun u => by
    have := integral_q_left_le V u
    simp only [hVq] at this
    rwa [hVγ] at this
  have hqi : ∀ w : Euc d, Integrable (fun u => q (u - w)) (HRS.Whole.withDensityReal ρμ) := fun w => s82r_row_integrable hd hq hρ hM w
  have hP' : (∑ ℓ, t ℓ) * V.γ + lam * n * V.γ ≤ P := by rw [hVγ]; exact hP
  set ρ' : Euc d → ℝ := fun z => ∑ ℓ, t ℓ * (A * q (z - p ℓ) + B) with hρ'
  have hρm : Measurable ρ' :=
    Finset.measurable_sum _ fun ℓ _ => measurable_const.mul
      ((measurable_const.mul (hqm.comp (measurable_id.sub measurable_const))).add measurable_const)
  have hρ0 : ∀ z, 0 ≤ ρ' z := fun z =>
    Finset.sum_nonneg fun ℓ _ => mul_nonneg (ht ℓ) (add_nonneg (mul_nonneg hA (hq0 _)) hB)
  have hρi : Integrable ρ' (HRS.Whole.withDensityReal ρμ) :=
    integrable_finset_sum _ fun ℓ _ => (((hqi (p ℓ)).const_mul A).add (integrable_const B)).const_mul (t ℓ)
  have hγ1 : 0 ≤ γ := hγ
  have hθ1 : ((n : ℝ) - 1) * (K * (lam * V.γ) + K ^ 2 * (lam * V.γ)) < 1 := by
    rw [hVγ]
    have : ((n : ℝ) - 1) * (K * (lam * γ) + K ^ 2 * (lam * γ)) =
        (((n : ℝ) - 1) * lam) * (γ * (K + K ^ 2)) := by ring
    rw [this]
    have h0 : 0 ≤ γ * (K + K ^ 2) := by positivity
    calc (((n : ℝ) - 1) * lam) * (γ * (K + K ^ 2)) ≤ β * (γ * (K + K ^ 2)) :=
          mul_le_mul_of_nonneg_right hnl h0
      _ < 1 := by nlinarith [hα]
  have hsup : ∀ᵐ z ∂(HRS.Whole.withDensityReal ρμ), (1 - 1 / (n : ℝ)) * ρ' z + (((n : ℝ) - 1) / n) *
      s82r_Gam (HRS.Whole.withDensityReal ρμ) (s82r_Gm V lam K) ρ' z ≤ ρ' z - (1 / (n : ℝ)) * s82r_bm V p t K z := by
    have hatom : ∀ ℓ, ∀ᵐ z ∂(HRS.Whole.withDensityReal ρμ), z ≠ p ℓ := fun ℓ => by
      have h1 : HRS.Whole.withDensityReal ρμ {p ℓ} = 0 :=
        HRS.MS.S82P2.s82p2_mu_singleton hd ρμ (p ℓ)
      rw [ae_iff]
      simpa using h1
    filter_upwards [ae_all_iff.2 hatom] with z hz
    have hΓ : ∀ u, s82r_Gm V lam K u z = K * (1 - Real.exp (-(lam * q (u - z)))) + K ^ 2 * (lam * γ) := by
      intro u; unfold s82r_Gm s82r_d; rw [hVq, hVγ]
    have hΓm : Measurable (fun u => K * (1 - Real.exp (-(lam * q (u - z)))) + K ^ 2 * (lam * γ)) :=
      (measurable_const.mul (measurable_const.sub (Real.measurable_exp.comp
        (measurable_const.mul (hqm.comp (measurable_id.sub measurable_const))).neg))).add measurable_const
    have hd0 : ∀ u, 0 ≤ 1 - Real.exp (-(lam * q (u - z))) := fun u => by
      have : Real.exp (-(lam * q (u - z))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hq0 (u - z)])
      linarith
    have hd1 : ∀ u, 1 - Real.exp (-(lam * q (u - z))) ≤ 1 := fun u => by
      have := Real.exp_pos (-(lam * q (u - z))); linarith
    have hΓ0 : ∀ u, 0 ≤ K * (1 - Real.exp (-(lam * q (u - z)))) + K ^ 2 * (lam * γ) := fun u =>
      add_nonneg (mul_nonneg hK0.le (hd0 u)) (by positivity)
    have hΓb : ∀ u, K * (1 - Real.exp (-(lam * q (u - z)))) + K ^ 2 * (lam * γ) ≤ K * 1 + K ^ 2 * (lam * γ) :=
      fun u => add_le_add (mul_le_mul_of_nonneg_left (hd1 u) hK0.le) le_rfl
    have hσΓ : ∀ ℓ, Integrable (fun u => (A * q (u - p ℓ) + B) *
        (K * (1 - Real.exp (-(lam * q (u - z)))) + K ^ 2 * (lam * γ))) (HRS.Whole.withDensityReal ρμ) := fun ℓ => by
      have hσ : Integrable (fun u => A * q (u - p ℓ) + B) (HRS.Whole.withDensityReal ρμ) := ((hqi (p ℓ)).const_mul A).add (integrable_const B)
      have := hσ.bdd_mul (c := K * 1 + K ^ 2 * (lam * γ)) hΓm.aestronglyMeasurable
        (ae_of_all _ fun u => by rw [Real.norm_eq_abs, abs_of_nonneg (hΓ0 u)]; exact hΓb u)
      exact this.congr (ae_of_all _ fun u => by simp only; ring)
    have hGam : s82r_Gam (HRS.Whole.withDensityReal ρμ) (s82r_Gm V lam K) ρ' z = ∑ ℓ, t ℓ * ∫ u, (A * q (u - p ℓ) + B) *
        (K * (1 - Real.exp (-(lam * q (u - z)))) + K ^ 2 * (lam * γ)) ∂(HRS.Whole.withDensityReal ρμ) := by
      unfold s82r_Gam
      simp_rw [hΓ]
      have : ∀ u, ρ' u * (K * (1 - Real.exp (-(lam * q (u - z)))) + K ^ 2 * (lam * γ)) =
          ∑ ℓ, t ℓ * ((A * q (u - p ℓ) + B) * (K * (1 - Real.exp (-(lam * q (u - z)))) + K ^ 2 * (lam * γ))) := by
        intro u; simp only [hρ']; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun ℓ _ => by ring
      simp_rw [this]
      rw [integral_finset_sum _ fun ℓ _ => (hσΓ ℓ).const_mul _]
      exact Finset.sum_congr rfl fun ℓ _ => by rw [integral_const_mul]
    have hbz : s82r_bm V p t K z ≤ ∑ ℓ, t ℓ * (K * q (z - p ℓ) + K ^ 2 * γ) := by
      unfold s82r_bm
      refine Finset.sum_le_sum fun ℓ _ => ?_
      have h1 := s82r_d_le V (ht ℓ) z (p ℓ)
      rw [hVq] at h1
      rw [hVγ]
      have h2 := mul_le_mul_of_nonneg_left h1 hK0.le
      nlinarith [h2]
    have hkey : ((n : ℝ) - 1) * s82r_Gam (HRS.Whole.withDensityReal ρμ) (s82r_Gm V lam K) ρ' z + s82r_bm V p t K z ≤ ρ' z := by
      rw [hGam, Finset.mul_sum]
      refine le_trans (add_le_add le_rfl hbz) ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun ℓ _ => ?_
      have := hsuper ρμ hρ hM hrow n lam hn1 hlam hnl (p ℓ) z (hz ℓ)
      have h2 := mul_le_mul_of_nonneg_left this (ht ℓ)
      calc ((n : ℝ) - 1) * (t ℓ * ∫ u, (A * q (u - p ℓ) + B) *
              (K * (1 - Real.exp (-(lam * q (u - z)))) + K ^ 2 * (lam * γ)) ∂(HRS.Whole.withDensityReal ρμ)) +
            t ℓ * (K * q (z - p ℓ) + K ^ 2 * γ) =
          t ℓ * (K * q (z - p ℓ) + K ^ 2 * γ + ((n : ℝ) - 1) * ∫ u, (A * q (u - p ℓ) + B) *
              (K * (1 - Real.exp (-(lam * q (u - z)))) + K ^ 2 * (lam * γ)) ∂(HRS.Whole.withDensityReal ρμ)) := by ring
        _ ≤ t ℓ * (A * q (z - p ℓ) + B) := h2
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have : (1 - 1 / (n : ℝ)) * ρ' z + (((n : ℝ) - 1) / n) * s82r_Gam (HRS.Whole.withDensityReal ρμ) (s82r_Gm V lam K) ρ' z =
        ρ' z - (1 / (n : ℝ)) * (ρ' z - ((n : ℝ) - 1) * s82r_Gam (HRS.Whole.withDensityReal ρμ) (s82r_Gm V lam K) ρ' z) := by
      field_simp; ring
    rw [this]
    have h3 := mul_le_mul_of_nonneg_left (by linarith [hkey] : s82r_bm V p t K z ≤
      ρ' z - ((n : ℝ) - 1) * s82r_Gam (HRS.Whole.withDensityReal ρμ) (s82r_Gm V lam K) ρ' z) (one_div_pos.2 hn0).le
    linarith
  have := s82r_field_compare V hψ p t ht hlam hP' hθ1 hρm hρ0 hρi hsup i0 hS
  exact this

end HRS.MS.S82R

end
