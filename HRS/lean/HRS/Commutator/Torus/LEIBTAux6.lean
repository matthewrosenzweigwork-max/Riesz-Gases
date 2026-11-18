import HRS.Commutator.Torus.LEIBTAux5

/-!
# LEIB-T helpers, part 6: decay of `𝓕⁻[(m(a+t·) - m(a)) ψ]`, quantitative in `(a,t)`
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma leibt_invF_decay' (K : ℕ) :
    ∃ (kk nn : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (ρ : SchwartzMap 𝔼 ℂ) (w : 𝔼),
      (1 + ‖w‖) ^ K * ‖(𝓕⁻ ρ : SchwartzMap 𝔼 ℂ) w‖ ≤
        C * ((Finset.Iic (kk, nn)).sup (schwartzSeminormFamily ℂ 𝔼 ℂ)) ρ := by
  obtain ⟨s, C, hC0, hC⟩ := leibt_invF_decay (d := d) K
  refine ⟨s.sup Prod.fst, s.sup Prod.snd, C, hC0, fun ρ w => ?_⟩
  refine (hC ρ w).trans ?_
  gcongr
  have hsub : s ⊆ Finset.Iic (s.sup Prod.fst, s.sup Prod.snd) := by
    intro x hx
    rw [Finset.mem_Iic]
    exact ⟨Finset.le_sup (f := Prod.fst) hx, Finset.le_sup (f := Prod.snd) hx⟩
  exact Seminorm.le_def.1 (Finset.sup_mono hsub) ρ

/-- The Schwartz function `(m(a + t·) - m(a)) ψ`. -/
def leibt_rho (α : ℝ) (ψ : SchwartzMap 𝔼 ℂ) (a : 𝔼) (t : ℝ) : SchwartzMap 𝔼 ℂ :=
  SchwartzMap.smulLeftCLM ℂ (leibt_theta α a t) ψ

lemma leibt_theta_temperate (α : ℝ) (a : 𝔼) (t : ℝ) : (leibt_theta α a t).HasTemperateGrowth := by
  have h1 : (fun ζ : 𝔼 => a + t • ζ).HasTemperateGrowth := by fun_prop
  have h2 := (HRS.Commutator.Whole.XLI.bsymX_temperate (d := d) α).comp h1
  have h3 : (fun _ : 𝔼 => leibt_m α a).HasTemperateGrowth := Function.HasTemperateGrowth.const _
  exact h2.sub h3

lemma leibt_rho_apply (α : ℝ) (ψ : SchwartzMap 𝔼 ℂ) (a : 𝔼) (t : ℝ) (ζ : 𝔼) :
    leibt_rho α ψ a t ζ = leibt_theta α a t ζ * ψ ζ := by
  unfold leibt_rho
  rw [SchwartzMap.smulLeftCLM_apply_apply (leibt_theta_temperate α a t), smul_eq_mul]

lemma leibt_rho_decay (α : ℝ) (ψ : SchwartzMap 𝔼 ℂ) (K : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ (a : 𝔼) (t : ℝ), 0 < t → t ≤ 1 → ∀ w : 𝔼,
      (1 + ‖w‖) ^ K * ‖(𝓕⁻ (leibt_rho α ψ a t) : SchwartzMap 𝔼 ℂ) w‖ ≤ C * t * (1 + ‖a‖) ^ k := by
  obtain ⟨kk, nn, C₁, hC₁, hdec⟩ := leibt_invF_decay' (d := d) K
  obtain ⟨Cθ, kθ, hCθ, hθ⟩ := leibt_theta_bound (d := d) α nn
  set S₀ := ((Finset.Iic (kk + (kθ + 1), nn)).sup (schwartzSeminormFamily ℂ 𝔼 ℂ)) ψ with hS₀
  have hS₀0 : 0 ≤ S₀ := by positivity
  refine ⟨C₁ * (Cθ * 2 ^ nn * 2 ^ (kk + (kθ + 1)) * S₀), kθ, by positivity, fun a t ht ht1 w => ?_⟩
  refine (hdec _ w).trans ?_
  have hsup : ((Finset.Iic (kk, nn)).sup (schwartzSeminormFamily ℂ 𝔼 ℂ)) (leibt_rho α ψ a t) ≤
      Cθ * t * (1 + ‖a‖) ^ kθ * 2 ^ nn * 2 ^ (kk + (kθ + 1)) * S₀ := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun ⟨k, n⟩ hkn => ?_
    rw [Finset.mem_Iic] at hkn
    have hkn1 : k ≤ kk := hkn.1
    have hkn2 : n ≤ nn := hkn.2
    show SchwartzMap.seminorm ℂ k n (leibt_rho α ψ a t) ≤ _
    have hA : 0 ≤ Cθ * t * (1 + ‖a‖) ^ kθ := by positivity
    have h := leibt_seminorm_mul (leibt_theta α a t) (leibt_theta_temperate α a t) ψ k n (kθ + 1) hA
      (fun i hi ζ => by
        have := hθ a t ht ht1 i (hi.trans hkn2) ζ
        simpa [mul_assoc] using this)
    refine h.trans ?_
    have hmono : ((Finset.Iic (k + (kθ + 1), n)).sup (schwartzSeminormFamily ℂ 𝔼 ℂ)) ψ ≤ S₀ := by
      refine Seminorm.le_def.1 (Finset.sup_mono ?_) ψ
      intro x hx
      rw [Finset.mem_Iic] at hx ⊢
      exact ⟨le_trans hx.1 (by omega), le_trans hx.2 hkn2⟩
    have h2n : (2 : ℝ) ^ n ≤ 2 ^ nn := pow_le_pow_right₀ (by norm_num) hkn2
    have h2k : (2 : ℝ) ^ (k + (kθ + 1)) ≤ 2 ^ (kk + (kθ + 1)) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hpos : 0 ≤ ((Finset.Iic (k + (kθ + 1), n)).sup (schwartzSeminormFamily ℂ 𝔼 ℂ)) ψ := by positivity
    gcongr
  refine le_trans (mul_le_mul_of_nonneg_left hsup hC₁) (le_of_eq ?_)
  ring

end HRS.Commutator.TorusNote
