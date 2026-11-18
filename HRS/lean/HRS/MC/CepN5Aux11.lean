import HRS.MC.CepN5Aux10

/-!
# Packet N5, helper 11: Dynkin's formula for the localised process, and the sign of the drift

`n5_app` instantiates `n5_core` for the localised process; `n5_drift_S` / `n5_drift_T` give the
a.e. sign of the generator for `f = n5_S` (scale function, `≤ 0`) and `f = x²` (`≥ σ²`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal

namespace HRS.MC.CepN5

open HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {B : ℝ≥0 → Ω → ℝ} {G c : ℝ → Ω → ℝ} {κ σ C : ℝ}
  {ρ : Ω → WithTop ℝ} {t₁ : ℝ≥0} {dur ε δ : ℝ} {A : Set Ω}

/-- The generator `f' b + σ²/2 f''`. -/
def n5_dr (f : ℝ → ℝ) (σ : ℝ) (X b : ℝ → Ω → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  deriv f (X s ω) * b s ω + σ ^ 2 / 2 * deriv (deriv f) (X s ω)

theorem n5_app [IsProbabilityMeasure P] (h : N5H P ℱ B G c κ σ C ρ t₁ dur ε δ A) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) :
    (∀ᵐ ω ∂P, IntegrableOn (fun s => n5_dr f σ (n5_Xp P ℱ B G κ σ C ρ t₁ dur ε δ A)
        (n5_b G B ρ t₁ σ δ ε dur (κ / δ + C) A) s ω) (Icc 0 (n5_tauR G ρ t₁ δ ε dur A ω))) ∧
    Integrable (fun ω => f (n5_Xp P ℱ B G κ σ C ρ t₁ dur ε δ A (n5_tauR G ρ t₁ δ ε dur A ω) ω)) P ∧
    Integrable (fun ω => f (n5_X0 G t₁ δ ε ω)) P ∧
    Integrable (fun ω => ∫ s in Icc 0 (n5_tauR G ρ t₁ δ ε dur A ω),
      n5_dr f σ (n5_Xp P ℱ B G κ σ C ρ t₁ dur ε δ A) (n5_b G B ρ t₁ σ δ ε dur (κ / δ + C) A) s ω) P ∧
    ∀ A', MeasurableSet[n5_shF ℱ (t₁ : ℝ) 0] A' →
      ∫ ω in A', f (n5_Xp P ℱ B G κ σ C ρ t₁ dur ε δ A (n5_tauR G ρ t₁ δ ε dur A ω) ω) ∂P =
        ∫ ω in A', f (n5_X0 G t₁ δ ε ω) ∂P +
        ∫ ω in A', (∫ s in Icc 0 (n5_tauR G ρ t₁ δ ε dur A ω),
          n5_dr f σ (n5_Xp P ℱ B G κ σ C ρ t₁ dur ε δ A)
            (n5_b G B ρ t₁ σ δ ε dur (κ / δ + C) A) s ω) ∂P := by
  have hM : 0 ≤ κ / δ + C := by have := h.hκ; have := h.hδ; have := h.hC; positivity
  have hb0 : ∀ s ω, 0 ≤ n5_b G B ρ t₁ σ δ ε dur (κ / δ + C) A s ω := fun s ω =>
    n5_b_nonneg _ s ω
  exact n5_core (n5_shift_brownian h.brown t₁) h.hdur.le (n5_X0_meas h)
    (n5_b_prog h (κ / δ + C))
    (fun s ω => abs_le.2 ⟨by linarith [hb0 s ω], n5_b_le hM s ω⟩)
    (n5_isStoppingTime_tau2 (δ := δ) (ε := ε) (dur := dur) h.hdur.le h.hG h.hGad h.hρ h.hA)
    (fun _ => rfl) (n5_tauR_nonneg h.hdur.le) (n5_tauR_le h.hdur.le) (n5_hXK h) hf

/-- A.e. sign of the generator on `[0, τR]`, given a pointwise criterion valid on `A₁ ∩ {s < τR}`. -/
theorem n5_drift_ae [IsProbabilityMeasure P] (h : N5H P ℱ B G c κ σ C ρ t₁ dur ε δ A)
    {f : ℝ → ℝ} {Q : ℝ → ℝ → Prop}
    (hQ : ∀ x b : ℝ, δ < x → 0 ≤ b → b ≤ κ / x + C → Q (deriv f x * b + σ ^ 2 / 2 * deriv (deriv f) x) x) :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Icc 0 (n5_tauR G ρ t₁ δ ε dur A ω))),
      Q (n5_dr f σ (n5_Xp P ℱ B G κ σ C ρ t₁ dur ε δ A) (n5_b G B ρ t₁ σ δ ε dur (κ / δ + C) A) s ω)
        (n5_H G t₁ s ω) := by
  filter_upwards [n5_kc h] with ω hkc
  rw [ae_restrict_iff' measurableSet_Icc]
  have hne : ∀ᵐ s : ℝ, s ≠ n5_tauR G ρ t₁ δ ε dur A ω := by
    simp [ae_iff, measure_singleton]
  by_cases hω : ω ∈ n5_A1 G ρ t₁ δ A
  · filter_upwards [(hkc hω).2, hne] with s hs hsne hsI
    have hlt : s < n5_tauR G ρ t₁ δ ε dur A ω := lt_of_le_of_ne hsI.2 hsne
    have hXs := (hkc hω).1 s hsI
    have hH := n5_H_lt_of_lt h hω hsI.1 hlt
    have hb0 : 0 ≤ n5_b G B ρ t₁ σ δ ε dur (κ / δ + C) A s ω := n5_b_nonneg _ s ω
    have := hQ (n5_H G t₁ s ω) _ hH.1 hb0 (hs hsI)
    unfold n5_dr
    rw [hXs]
    exact this
  · filter_upwards [hne] with s hsne hsI
    exfalso
    apply hsne
    have := hsI.2
    rw [n5_tauR_of_not_mem hω] at this ⊢
    exact le_antisymm this hsI.1

end HRS.MC.CepN5
