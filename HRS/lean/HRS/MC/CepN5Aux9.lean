import HRS.MC.CepN5Aux7
import HRS.MC.CepN5Aux8

/-!
# Packet N5, helper 9: the localised Itô process coincides with the gap process

The hypotheses of `cep_N5_bessel_hitting` are bundled in `N5H`.  With the drift `n5_b` (the clipped density of
the drift remainder, switched off after `τR`) and the initial value `n5_X0`, the Itô process
`X = X0 + ∫ b + σ Ŵ` coincides with `H` on `[0, τR]` for every path in `A₁`, and stays in `[δ, ε]` up to `τR`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal

namespace HRS.MC.CepN5

open HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- All hypotheses of the packet statement (with `t₁` lifted to `ℝ≥0`; `hpos`, `hκσ` are not needed here). -/
structure N5H (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (B : ℝ≥0 → Ω → ℝ) (G c : ℝ → Ω → ℝ)
    (κ σ C : ℝ) (ρ : Ω → WithTop ℝ) (t₁ : ℝ≥0) (dur ε δ : ℝ) (A : Set Ω) : Prop where
  brown : IsBrownianFiltration P ℱ (fun t ω (_ : Fin 1) => B t ω)
  hκ : 0 < κ
  hσ : 0 < σ
  hC : 0 ≤ C
  hρ : IsStoppingTime ℱ ρ
  hdur : 0 < dur
  hG : ∀ ω, Continuous fun t => G t ω
  hGad : ∀ t, 0 ≤ t → Measurable[ℱ t] (G t)
  hc : ∀ u ω, |c u ω| ≤ C
  hdyn : ∀ᵐ ω ∂P, ∀ s t : ℝ, (t₁ : ℝ) ≤ s → s ≤ t → t ≤ t₁ + dur → ((t : ℝ) : WithTop ℝ) ≤ ρ ω →
    G t ω - G s ω = (∫ u in s..t, (κ / G u ω + c u ω)) + σ * (B (Real.toNNReal t) ω - B (Real.toNNReal s) ω)
  hε : 0 < ε
  hεC : C * ε ≤ κ
  hδ : 0 < δ
  hδε : δ < ε / 2
  hA : MeasurableSet[ℱ (t₁ : ℝ)] A
  hA0 : ∀ ω ∈ A, 0 < G t₁ ω ∧ G t₁ ω ≤ ε / 2

section Objects

variable (G : ℝ → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ρ : Ω → WithTop ℝ) (t₁ : ℝ≥0) (σ δ ε dur M₀ : ℝ) (A : Set Ω)

/-- The drift: the clipped density of `Z`, switched off after `τR`. -/
def n5_b : ℝ → Ω → ℝ := fun s ω =>
  Set.indicator {ω | (s : WithTop ℝ) ≤ n5_tau2 G ρ t₁ δ ε dur A ω} (fun _ => (1 : ℝ)) ω *
    n5_bcl M₀ (n5_dq (fun u => n5_Zp G B t₁ σ u ω) s)

end Objects

section Facts

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {B : ℝ≥0 → Ω → ℝ} {G c : ℝ → Ω → ℝ} {κ σ C : ℝ}
  {ρ : Ω → WithTop ℝ} {t₁ : ℝ≥0} {dur ε δ : ℝ} {A : Set Ω}

theorem N5H.contB (h : N5H P ℱ B G c κ σ C ρ t₁ dur ε δ A) (ω : Ω) : Continuous fun t => B t ω :=
  (continuous_apply (0 : Fin 1)).comp (h.brown.cont ω)

theorem N5H.adaptedB (h : N5H P ℱ B G c κ σ C ρ t₁ dur ε δ A) (t : ℝ≥0) : Measurable[ℱ t] (B t) :=
  (measurable_pi_apply (0 : Fin 1)).comp (h.brown.adapted t)

theorem n5_Zp_progressive (h : N5H P ℱ B G c κ σ C ρ t₁ dur ε δ A) :
    IsProgressive (n5_shF ℱ (t₁ : ℝ)) (n5_Zp G B t₁ σ) :=
  (StronglyAdapted.isStronglyProgressive_of_continuous
    (fun s => (n5_Zp_adapted h.hGad h.adaptedB t₁ σ s).stronglyMeasurable)
    (fun ω => n5_Zp_cont h.hG h.contB t₁ σ ω)).isProgressive

theorem n5_b_prog (h : N5H P ℱ B G c κ σ C ρ t₁ dur ε δ A) (M₀ : ℝ) :
    IsProgressive (n5_shF ℱ (t₁ : ℝ)) (n5_b G B ρ t₁ σ δ ε dur M₀ A) := by
  have h1 := isProgressive_indicator_le_stoppingTime (n5_shF ℱ (t₁ : ℝ))
    (n5_isStoppingTime_tau2 (δ := δ) (ε := ε) (dur := dur) h.hdur.le h.hG h.hGad h.hρ h.hA)
  exact h1.mul (n5_isProgressive_bcl (n5_Zp_progressive h) M₀)

theorem n5_b_nonneg (M₀ : ℝ) (s : ℝ) (ω : Ω) : 0 ≤ n5_b G B ρ t₁ σ δ ε dur M₀ A s ω := by
  unfold n5_b
  exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (n5_bcl_nonneg _ _)

theorem n5_b_le {M₀ : ℝ} (hM : 0 ≤ M₀) (s : ℝ) (ω : Ω) : n5_b G B ρ t₁ σ δ ε dur M₀ A s ω ≤ M₀ := by
  unfold n5_b
  have h1 : Set.indicator {ω | (s : WithTop ℝ) ≤ n5_tau2 G ρ t₁ δ ε dur A ω} (fun _ => (1 : ℝ)) ω ≤ 1 :=
    Set.indicator_le_self' (fun _ _ => zero_le_one) ω
  calc _ ≤ 1 * M₀ := mul_le_mul h1 (n5_bcl_le hM _) (n5_bcl_nonneg _ _) zero_le_one
    _ = M₀ := one_mul _

theorem n5_b_of_le {M₀ s : ℝ} {ω : Ω} (hs : s ≤ n5_tauR G ρ t₁ δ ε dur A ω) :
    n5_b G B ρ t₁ σ δ ε dur M₀ A s ω = n5_bcl M₀ (n5_dq (fun u => n5_Zp G B t₁ σ u ω) s) := by
  unfold n5_b
  have : ω ∈ {ω | (s : WithTop ℝ) ≤ n5_tau2 G ρ t₁ δ ε dur A ω} := by
    show (s : WithTop ℝ) ≤ ((n5_tauR G ρ t₁ δ ε dur A ω : ℝ) : WithTop ℝ)
    exact_mod_cast hs
  rw [Set.indicator_of_mem this, one_mul]

theorem n5_X0_meas (h : N5H P ℱ B G c κ σ C ρ t₁ dur ε δ A) (t : ℝ) :
    Measurable[n5_shF ℱ (t₁ : ℝ) t] (n5_X0 G t₁ δ ε) := by
  have hle : ℱ (t₁ : ℝ) ≤ n5_shF ℱ (t₁ : ℝ) t := by
    rw [n5_shF_apply]
    exact ℱ.mono (le_add_of_nonneg_right (le_max_right _ _))
  have h1 : Measurable[n5_shF ℱ (t₁ : ℝ) t] (G t₁) := (h.hGad (t₁ : ℝ) t₁.2).mono hle le_rfl
  exact measurable_const.max (measurable_const.min h1)

theorem n5_X0_eq {ω : Ω} (h0 : δ < G t₁ ω) (h0' : G t₁ ω ≤ ε / 2) : n5_X0 G t₁ δ ε ω = G t₁ ω := by
  unfold n5_X0
  rw [min_eq_right h0', max_eq_right h0.le]

theorem n5_X0_mem (hδ : 0 < δ) (hδε : δ < ε / 2) (ω : Ω) : n5_X0 G t₁ δ ε ω ∈ Icc δ (ε / 2) := by
  unfold n5_X0
  exact ⟨le_max_left _ _, max_le hδε.le (min_le_left _ _)⟩

end Facts

end HRS.MC.CepN5
