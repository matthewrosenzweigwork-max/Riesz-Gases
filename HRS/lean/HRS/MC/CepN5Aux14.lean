import HRS.MC.CepN5Aux11

/-!
# Packet N5, helper 14: the pathwise cover

For `ω ∈ A₁`: either `G` reaches `δ` on `[t₁, t₁+dur]` before `ρ`, or `ρ < t₁ + dur`, or `H_{τR} ≥ ε`,
or `dur ≤ τR`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal

namespace HRS.MC.CepN5

open HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem n5_rhat_bound {ρ : Ω → WithTop ℝ} {t₁ : ℝ≥0} {ω : Ω} (hρω : ((t₁ : ℝ) : WithTop ℝ) ≤ ρ ω)
    {u : ℝ} (hu : (u : WithTop ℝ) ≤ n5_rhat ρ t₁ ω) : (((t₁ : ℝ) + u : ℝ) : WithTop ℝ) ≤ ρ ω := by
  unfold n5_rhat at hu
  cases h : ρ ω with
  | top => exact le_top
  | coe r =>
    rw [h] at hu hρω
    simp only [WithTop.map_coe, WithTop.coe_le_coe] at hu hρω ⊢
    have h2 : r - t₁ ≤ max (r - t₁) 0 := le_max_left _ _
    have h3 : max (r - t₁) 0 = r - t₁ := max_eq_left (by linarith)
    linarith

theorem n5_cover {G : ℝ → Ω → ℝ} {ρ : Ω → WithTop ℝ} {t₁ : ℝ≥0} {dur ε δ : ℝ} {A : Set Ω} {ω : Ω}
    (hdur : 0 < dur) (hG : Continuous fun t => G t ω) (hω : ω ∈ n5_A1 G ρ t₁ δ A) :
    (∃ u ∈ Set.Icc (t₁ : ℝ) ((t₁ : ℝ) + dur), ((u : ℝ) : WithTop ℝ) ≤ ρ ω ∧ G u ω ≤ δ) ∨
      ρ ω < (((t₁ : ℝ) + dur : ℝ) : WithTop ℝ) ∨
      ε ≤ n5_H G t₁ (n5_tauR G ρ t₁ δ ε dur A ω) ω ∨ dur ≤ n5_tauR G ρ t₁ δ ε dur A ω := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hE, hρ', hε', hd⟩ := hcon
  have hT : ((n5_tauR G ρ t₁ δ ε dur A ω : ℝ) : WithTop ℝ) = n5_tau1 G ρ t₁ δ ε dur ω :=
    n5_tauR_of_mem hω
  have hρω : ((t₁ : ℝ) : WithTop ℝ) ≤ ρ ω := hω.1.2
  set T := n5_tauR G ρ t₁ δ ε dur A ω with hTdef
  have hT0 : 0 ≤ T := n5_tauR_nonneg hdur.le ω
  have hτ1 : (T : WithTop ℝ) = min (min (n5_tauE G t₁ δ ε ω) (n5_rhat ρ t₁ ω)) (dur : WithTop ℝ) := hT
  have hTr : (T : WithTop ℝ) ≤ n5_rhat ρ t₁ ω :=
    hτ1.le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h1 : min (n5_tauE G t₁ δ ε ω) (n5_rhat ρ t₁ ω) = (T : WithTop ℝ) := by
    rcases le_total (min (n5_tauE G t₁ δ ε ω) (n5_rhat ρ t₁ ω)) (dur : WithTop ℝ) with hh | hh
    · rw [min_eq_left hh] at hτ1; exact hτ1.symm
    · rw [min_eq_right hh] at hτ1
      exfalso
      have : T = dur := by exact_mod_cast hτ1
      linarith
  rcases le_total (n5_tauE G t₁ δ ε ω) (n5_rhat ρ t₁ ω) with hh | hh
  · rw [min_eq_left hh] at h1
    obtain ⟨-, hH⟩ := n5_exit_mem hG h1
    rcases hH with hH | hH
    · have hu := hE ((t₁ : ℝ) + T) ⟨by linarith, by linarith⟩ (n5_rhat_bound hρω hTr)
      have : n5_H G t₁ T ω = G ((t₁ : ℝ) + T) ω := by simp [n5_H, max_eq_left hT0]
      linarith
    · linarith
  · rw [min_eq_right hh] at h1
    unfold n5_rhat at h1
    cases hρ : ρ ω with
    | top =>
      rw [hρ] at h1
      simp at h1
    | coe r =>
      rw [hρ] at hρ' hρω h1
      simp only [WithTop.map_coe, WithTop.coe_le_coe, WithTop.coe_eq_coe] at hρ' hρω h1
      have h3 : max (r - t₁) 0 = r - t₁ := max_eq_left (by linarith)
      linarith

end HRS.MC.CepN5
