import HRS.MC.CepN5Aux11

/-!
# Packet N5, helper 13: the time-out bound

`σ² · dur · P(A₁ ∩ {dur ≤ τR}) ≤ ε² · P(A₁)`, from Dynkin's formula for `f = x²` (generator `≥ σ²`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal

namespace HRS.MC.CepN5

open HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The integrated generator along the localised process. -/
abbrev n5_I (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (B : ℝ≥0 → Ω → ℝ) (G : ℝ → Ω → ℝ) (κ σ C : ℝ)
    (ρ : Ω → WithTop ℝ) (t₁ : ℝ≥0) (dur ε δ : ℝ) (A : Set Ω) (f : ℝ → ℝ) : Ω → ℝ := fun ω =>
  ∫ s in Icc 0 (n5_tauR G ρ t₁ δ ε dur A ω),
    n5_dr f σ (n5_Xp P ℱ B G κ σ C ρ t₁ dur ε δ A)
      (n5_b G B ρ t₁ σ δ ε dur (κ / δ + C) A) s ω

theorem n5_deriv_sq (x : ℝ) : deriv (fun x : ℝ => x ^ 2) x = 2 * x := by
  simp

theorem n5_deriv_deriv_sq (x : ℝ) : deriv (deriv (fun x : ℝ => x ^ 2)) x = 2 := by
  have : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := funext n5_deriv_sq
  rw [this]
  simp

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {B : ℝ≥0 → Ω → ℝ} {G c : ℝ → Ω → ℝ} {κ σ C : ℝ}
  {ρ : Ω → WithTop ℝ} {t₁ : ℝ≥0} {dur ε δ : ℝ} {A : Set Ω}

theorem n5_T_bound [IsProbabilityMeasure P] (h : N5H P ℱ B G c κ σ C ρ t₁ dur ε δ A) :
    σ ^ 2 * dur * (P (n5_A1 G ρ t₁ δ A ∩ {ω | dur ≤ n5_tauR G ρ t₁ δ ε dur A ω})).toReal ≤
      ε ^ 2 * (P (n5_A1 G ρ t₁ δ A)).toReal := by
  have hS : ContDiff ℝ 2 (fun x : ℝ => x ^ 2) := contDiff_id.pow 2
  obtain ⟨c1, c2, c3, c4, c5⟩ := n5_app h hS
  have c4' : Integrable (n5_I P ℱ B G κ σ C ρ t₁ dur ε δ A (fun x : ℝ => x ^ 2)) P := c4
  have c5' : ∀ A', MeasurableSet[n5_shF ℱ (t₁ : ℝ) 0] A' →
      ∫ ω in A', (n5_Xp P ℱ B G κ σ C ρ t₁ dur ε δ A (n5_tauR G ρ t₁ δ ε dur A ω) ω) ^ 2 ∂P =
        ∫ ω in A', (n5_X0 G t₁ δ ε ω) ^ 2 ∂P +
        ∫ ω in A', n5_I P ℱ B G κ σ C ρ t₁ dur ε δ A (fun x : ℝ => x ^ 2) ω ∂P := c5
  have hA1m := n5_A1_meas (δ := δ) h.hGad h.hρ h.hA
  have hA1' : MeasurableSet (n5_A1 G ρ t₁ δ A) := (n5_shF ℱ (t₁ : ℝ)).le 0 _ hA1m
  have key := c5' _ hA1m
  have hdr := n5_drift_ae h (f := fun x : ℝ => x ^ 2) (Q := fun v _ => σ ^ 2 ≤ v)
    (fun x b hx hb _ => by
      rw [n5_deriv_sq, n5_deriv_deriv_sq]
      have : 0 ≤ 2 * x * b := mul_nonneg (by linarith [h.hδ]) hb
      linarith)
  have hlow : ∀ᵐ ω ∂P, σ ^ 2 * n5_tauR G ρ t₁ δ ε dur A ω ≤
      n5_I P ℱ B G κ σ C ρ t₁ dur ε δ A (fun x : ℝ => x ^ 2) ω := by
    filter_upwards [c1, hdr] with ω hint hω
    calc σ ^ 2 * n5_tauR G ρ t₁ δ ε dur A ω
        = ∫ s in Icc 0 (n5_tauR G ρ t₁ δ ε dur A ω), σ ^ 2 := by
          rw [setIntegral_const, Real.volume_real_Icc_of_le (n5_tauR_nonneg h.hdur.le ω)]
          simp [mul_comm]
      _ ≤ _ := setIntegral_mono_ae_restrict (continuous_const.integrableOn_Icc (μ := volume)) hint hω
  have hnn : ∀ᵐ ω ∂P, 0 ≤ n5_I P ℱ B G κ σ C ρ t₁ dur ε δ A (fun x : ℝ => x ^ 2) ω := by
    filter_upwards [hlow] with ω hω
    exact le_trans (mul_nonneg (sq_nonneg σ) (n5_tauR_nonneg h.hdur.le ω)) hω
  -- bound on the integral of the generator
  have hXτ : ∀ᵐ ω ∂P, n5_Xp P ℱ B G κ σ C ρ t₁ dur ε δ A (n5_tauR G ρ t₁ δ ε dur A ω) ω ∈ Icc δ ε := by
    filter_upwards [n5_hXK h] with ω hω
    exact hω _ ⟨n5_tauR_nonneg h.hdur.le ω, n5_tauR_le h.hdur.le ω⟩ le_rfl
  have hconst : ∫ ω in n5_A1 G ρ t₁ δ A, ε ^ 2 ∂P = ε ^ 2 * (P (n5_A1 G ρ t₁ δ A)).toReal := by
    rw [setIntegral_const]; simp [Measure.real, mul_comm]
  have hup : ∫ ω in n5_A1 G ρ t₁ δ A,
      (n5_Xp P ℱ B G κ σ C ρ t₁ dur ε δ A (n5_tauR G ρ t₁ δ ε dur A ω) ω) ^ 2 ∂P ≤
      ε ^ 2 * (P (n5_A1 G ρ t₁ δ A)).toReal := by
    rw [← hconst]
    refine setIntegral_mono_ae c2.integrableOn (integrable_const _).integrableOn ?_
    filter_upwards [hXτ] with ω hω
    exact pow_le_pow_left₀ (h.hδ.le.trans hω.1) hω.2 2
  have hX0nn : 0 ≤ ∫ ω in n5_A1 G ρ t₁ δ A, (n5_X0 G t₁ δ ε ω) ^ 2 ∂P :=
    integral_nonneg fun ω => sq_nonneg _
  have hIup : ∫ ω in n5_A1 G ρ t₁ δ A,
      n5_I P ℱ B G κ σ C ρ t₁ dur ε δ A (fun x : ℝ => x ^ 2) ω ∂P ≤
      ε ^ 2 * (P (n5_A1 G ρ t₁ δ A)).toReal := by
    linarith
  -- Markov
  have hgnn : 0 ≤ᵐ[P.restrict (n5_A1 G ρ t₁ δ A)]
      n5_I P ℱ B G κ σ C ρ t₁ dur ε δ A (fun x : ℝ => x ^ 2) := ae_restrict_of_ae hnn
  have hmk := mul_meas_ge_le_integral_of_nonneg hgnn c4'.integrableOn (σ ^ 2 * dur)
  have hmeas : (P (n5_A1 G ρ t₁ δ A ∩ {ω | dur ≤ n5_tauR G ρ t₁ δ ε dur A ω})).toReal ≤
      (P.restrict (n5_A1 G ρ t₁ δ A)).real {x | σ ^ 2 * dur ≤
        n5_I P ℱ B G κ σ C ρ t₁ dur ε δ A (fun x : ℝ => x ^ 2) x} := by
    rw [measureReal_def, Measure.restrict_apply' hA1']
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
    filter_upwards [hlow] with ω hω hω'
    refine ⟨?_, hω'.1⟩
    have h2 : dur ≤ n5_tauR G ρ t₁ δ ε dur A ω := hω'.2
    have := mul_le_mul_of_nonneg_left h2 (sq_nonneg σ)
    exact le_trans this hω
  have hpos : 0 ≤ σ ^ 2 * dur := by have := h.hdur; positivity
  calc σ ^ 2 * dur * (P (n5_A1 G ρ t₁ δ A ∩ {ω | dur ≤ n5_tauR G ρ t₁ δ ε dur A ω})).toReal
      ≤ σ ^ 2 * dur * (P.restrict (n5_A1 G ρ t₁ δ A)).real {x | σ ^ 2 * dur ≤
        n5_I P ℱ B G κ σ C ρ t₁ dur ε δ A (fun x : ℝ => x ^ 2) x} :=
        mul_le_mul_of_nonneg_left hmeas hpos
    _ ≤ _ := hmk
    _ ≤ _ := hIup

end HRS.MC.CepN5
