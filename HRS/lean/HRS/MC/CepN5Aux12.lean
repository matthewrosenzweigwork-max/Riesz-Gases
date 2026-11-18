import HRS.MC.CepN5Aux11
import HRS.MC.CepN5Aux1

/-!
# Packet N5, helper 12: the scale-function (supermartingale) bound

`S(ε) · P(A₁ ∩ {H_{τR} ≥ ε}) ≤ S(ε/2) · P(A₁)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal

namespace HRS.MC.CepN5

open HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {B : ℝ≥0 → Ω → ℝ} {G c : ℝ → Ω → ℝ} {κ σ C : ℝ}
  {ρ : Ω → WithTop ℝ} {t₁ : ℝ≥0} {dur ε δ : ℝ} {A : Set Ω}

theorem n5_S_bound [IsProbabilityMeasure P] (h : N5H P ℱ B G c κ σ C ρ t₁ dur ε δ A)
    (hθ : 2 * κ / σ ^ 2 < 1) :
    HRS.MC.CepN5b.cep_scale (2 * κ / σ ^ 2) (2 * C / σ ^ 2) ε *
        (P (n5_A1 G ρ t₁ δ A ∩ {ω | ε ≤ n5_H G t₁ (n5_tauR G ρ t₁ δ ε dur A ω) ω})).toReal ≤
      HRS.MC.CepN5b.cep_scale (2 * κ / σ ^ 2) (2 * C / σ ^ 2) (ε / 2) * (P (n5_A1 G ρ t₁ δ A)).toReal := by
  have hlam : 0 ≤ 2 * C / σ ^ 2 := by have := h.hC; positivity
  have hS := n5_S_contDiff h.hδ (2 * κ / σ ^ 2) (2 * C / σ ^ 2)
  obtain ⟨c1, c2, c3, c4, c5⟩ := n5_app h hS
  have hA1m := n5_A1_meas (δ := δ) h.hGad h.hρ h.hA
  have hA1' : MeasurableSet (n5_A1 G ρ t₁ δ A) := (n5_shF ℱ (t₁ : ℝ)).le 0 _ hA1m
  have key := c5 _ hA1m
  have hdr := n5_drift_ae h (f := n5_S (2 * κ / σ ^ 2) (2 * C / σ ^ 2) δ) (Q := fun v _ => v ≤ 0)
    (fun x b hx _ hbb => n5_drift_le h.hδ h.hσ hx hbb)
  have hD : ∀ᵐ ω ∂P, (∫ s in Icc 0 (n5_tauR G ρ t₁ δ ε dur A ω),
      n5_dr (n5_S (2 * κ / σ ^ 2) (2 * C / σ ^ 2) δ) σ (n5_Xp P ℱ B G κ σ C ρ t₁ dur ε δ A)
        (n5_b G B ρ t₁ σ δ ε dur (κ / δ + C) A) s ω) ≤ 0 := by
    filter_upwards [hdr] with ω hω
    exact integral_nonpos_of_ae hω
  have hDA : ∫ ω in n5_A1 G ρ t₁ δ A, (∫ s in Icc 0 (n5_tauR G ρ t₁ δ ε dur A ω),
      n5_dr (n5_S (2 * κ / σ ^ 2) (2 * C / σ ^ 2) δ) σ (n5_Xp P ℱ B G κ σ C ρ t₁ dur ε δ A)
        (n5_b G B ρ t₁ σ δ ε dur (κ / δ + C) A) s ω) ∂P ≤ 0 :=
    integral_nonpos_of_ae (ae_restrict_of_ae hD)
  -- the initial value
  have hX0 : ∀ ω, n5_S (2 * κ / σ ^ 2) (2 * C / σ ^ 2) δ (n5_X0 G t₁ δ ε ω) ≤
      HRS.MC.CepN5b.cep_scale (2 * κ / σ ^ 2) (2 * C / σ ^ 2) (ε / 2) := by
    intro ω
    have hm := n5_X0_mem (G := G) (t₁ := t₁) h.hδ h.hδε ω
    rw [n5_S_eq h.hδ hθ hlam hm.1]
    exact n5_scale_mono hθ hlam (h.hδ.le.trans hm.1) hm.2
  have hini : ∫ ω in n5_A1 G ρ t₁ δ A, n5_S (2 * κ / σ ^ 2) (2 * C / σ ^ 2) δ (n5_X0 G t₁ δ ε ω) ∂P ≤
      HRS.MC.CepN5b.cep_scale (2 * κ / σ ^ 2) (2 * C / σ ^ 2) (ε / 2) * (P (n5_A1 G ρ t₁ δ A)).toReal := by
    calc _ ≤ ∫ ω in n5_A1 G ρ t₁ δ A, HRS.MC.CepN5b.cep_scale (2 * κ / σ ^ 2) (2 * C / σ ^ 2) (ε / 2) ∂P :=
          setIntegral_mono c3.integrableOn (integrable_const _).integrableOn hX0
      _ = _ := by rw [setIntegral_const]; simp [Measure.real, mul_comm]
  have hmain : ∫ ω in n5_A1 G ρ t₁ δ A, n5_S (2 * κ / σ ^ 2) (2 * C / σ ^ 2) δ
      (n5_Xp P ℱ B G κ σ C ρ t₁ dur ε δ A (n5_tauR G ρ t₁ δ ε dur A ω) ω) ∂P ≤
      HRS.MC.CepN5b.cep_scale (2 * κ / σ ^ 2) (2 * C / σ ^ 2) (ε / 2) * (P (n5_A1 G ρ t₁ δ A)).toReal := by
    rw [key]; linarith
  -- Markov on `A₁`
  have hXτ : ∀ᵐ ω ∂P, n5_Xp P ℱ B G κ σ C ρ t₁ dur ε δ A (n5_tauR G ρ t₁ δ ε dur A ω) ω ∈ Icc δ ε := by
    filter_upwards [n5_hXK h] with ω hω
    exact hω _ ⟨n5_tauR_nonneg h.hdur.le ω, n5_tauR_le h.hdur.le ω⟩ le_rfl
  have hgnn : 0 ≤ᵐ[P.restrict (n5_A1 G ρ t₁ δ A)] fun ω =>
      n5_S (2 * κ / σ ^ 2) (2 * C / σ ^ 2) δ
        (n5_Xp P ℱ B G κ σ C ρ t₁ dur ε δ A (n5_tauR G ρ t₁ δ ε dur A ω) ω) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hXτ] with ω hω
    show 0 ≤ _
    rw [n5_S_eq h.hδ hθ hlam hω.1]
    exact n5_scale_nonneg hθ hlam (h.hδ.le.trans hω.1)
  have hmk := mul_meas_ge_le_integral_of_nonneg hgnn c2.integrableOn
    (HRS.MC.CepN5b.cep_scale (2 * κ / σ ^ 2) (2 * C / σ ^ 2) ε)
  have hmeas : (P (n5_A1 G ρ t₁ δ A ∩ {ω | ε ≤ n5_H G t₁ (n5_tauR G ρ t₁ δ ε dur A ω) ω})).toReal ≤
      ((P.restrict (n5_A1 G ρ t₁ δ A)).real {x | HRS.MC.CepN5b.cep_scale (2 * κ / σ ^ 2) (2 * C / σ ^ 2) ε ≤
        n5_S (2 * κ / σ ^ 2) (2 * C / σ ^ 2) δ
          (n5_Xp P ℱ B G κ σ C ρ t₁ dur ε δ A (n5_tauR G ρ t₁ δ ε dur A x) x)}) := by
    rw [measureReal_def, Measure.restrict_apply' hA1']
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
    filter_upwards [n5_kc h] with ω hkc hω
    obtain ⟨hω1, hω2⟩ := hω
    refine ⟨?_, hω1⟩
    have hmem := n5_H_mem_of_le h hω1 (n5_tauR_nonneg h.hdur.le ω) le_rfl
    have hX := (hkc hω1).1 _ ⟨n5_tauR_nonneg h.hdur.le ω, le_rfl⟩
    have hHe : n5_H G t₁ (n5_tauR G ρ t₁ δ ε dur A ω) ω = ε := le_antisymm hmem.2 hω2
    show _ ≤ n5_S _ _ δ _
    rw [hX, hHe, n5_S_eq h.hδ hθ hlam (show δ ≤ ε by linarith [h.hδε, h.hε])]
  have hSε : 0 ≤ HRS.MC.CepN5b.cep_scale (2 * κ / σ ^ 2) (2 * C / σ ^ 2) ε :=
    n5_scale_nonneg hθ hlam h.hε.le
  calc _ ≤ HRS.MC.CepN5b.cep_scale (2 * κ / σ ^ 2) (2 * C / σ ^ 2) ε *
        ((P.restrict (n5_A1 G ρ t₁ δ A)).real {x | HRS.MC.CepN5b.cep_scale (2 * κ / σ ^ 2) (2 * C / σ ^ 2) ε ≤
          n5_S (2 * κ / σ ^ 2) (2 * C / σ ^ 2) δ
            (n5_Xp P ℱ B G κ σ C ρ t₁ dur ε δ A (n5_tauR G ρ t₁ δ ε dur A x) x)}) :=
        mul_le_mul_of_nonneg_left hmeas hSε
    _ ≤ _ := hmk
    _ ≤ _ := hmain

end HRS.MC.CepN5
