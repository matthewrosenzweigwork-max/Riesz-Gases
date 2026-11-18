import HRS.MC.CepN5Aux9

/-!
# Packet N5, helper 10: identification of the Itô process with the gap on `[0, τR]`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal

namespace HRS.MC.CepN5

open HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {B : ℝ≥0 → Ω → ℝ} {G c : ℝ → Ω → ℝ} {κ σ C : ℝ}
  {ρ : Ω → WithTop ℝ} {t₁ : ℝ≥0} {dur ε δ : ℝ} {A : Set Ω}

/-- The localised Itô process. -/
abbrev n5_Xp (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (B : ℝ≥0 → Ω → ℝ) (G : ℝ → Ω → ℝ) (κ σ C : ℝ)
    (ρ : Ω → WithTop ℝ) (t₁ : ℝ≥0) (dur ε δ : ℝ) (A : Set Ω) : ℝ → Ω → ℝ :=
  n5_X P (n5_shF ℱ (t₁ : ℝ)) (n5_shW B t₁) σ (n5_X0 G t₁ δ ε)
    (n5_b G B ρ t₁ σ δ ε dur (κ / δ + C) A)

theorem n5_H_mem_of_le (h : N5H P ℱ B G c κ σ C ρ t₁ dur ε δ A) {ω : Ω}
    (hω : ω ∈ n5_A1 G ρ t₁ δ A) {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ n5_tauR G ρ t₁ δ ε dur A ω) :
    δ ≤ n5_H G t₁ u ω ∧ n5_H G t₁ u ω ≤ ε := by
  have hT : ((n5_tauR G ρ t₁ δ ε dur A ω : ℝ) : WithTop ℝ) = n5_tau1 G ρ t₁ δ ε dur ω :=
    n5_tauR_of_mem hω
  obtain ⟨⟨hAω, -⟩, hGδ⟩ := hω
  have h1 : (u : WithTop ℝ) ≤ (n5_tauR G ρ t₁ δ ε dur A ω : WithTop ℝ) := by exact_mod_cast huT
  rw [hT] at h1
  exact n5_exit_le (h.hG ω) h.hε hGδ (h.hA0 ω hAω).2 hu
    (h1.trans ((min_le_left _ _).trans (min_le_left _ _)))

theorem n5_H_lt_of_lt (h : N5H P ℱ B G c κ σ C ρ t₁ dur ε δ A) {ω : Ω}
    (hω : ω ∈ n5_A1 G ρ t₁ δ A) {u : ℝ} (hu : 0 ≤ u) (huT : u < n5_tauR G ρ t₁ δ ε dur A ω) :
    δ < n5_H G t₁ u ω ∧ n5_H G t₁ u ω < ε := by
  have hT : ((n5_tauR G ρ t₁ δ ε dur A ω : ℝ) : WithTop ℝ) = n5_tau1 G ρ t₁ δ ε dur ω :=
    n5_tauR_of_mem hω
  have h1 : (u : WithTop ℝ) < (n5_tauR G ρ t₁ δ ε dur A ω : WithTop ℝ) := by exact_mod_cast huT
  rw [hT] at h1
  exact n5_exit_lt hu (lt_of_lt_of_le h1 ((min_le_left _ _).trans (min_le_left _ _)))

/-- Key coincidence: on `A₁`, the localised Itô process equals `H` on `[0, τR]`. -/
theorem n5_kc [IsProbabilityMeasure P] (h : N5H P ℱ B G c κ σ C ρ t₁ dur ε δ A) :
    ∀ᵐ ω ∂P, ω ∈ n5_A1 G ρ t₁ δ A →
      (∀ s ∈ Icc 0 (n5_tauR G ρ t₁ δ ε dur A ω), n5_Xp P ℱ B G κ σ C ρ t₁ dur ε δ A s ω = n5_H G t₁ s ω) ∧
      (∀ᵐ s, s ∈ Icc 0 (n5_tauR G ρ t₁ δ ε dur A ω) →
        n5_b G B ρ t₁ σ δ ε dur (κ / δ + C) A s ω ≤ κ / n5_H G t₁ s ω + C) := by
  have hŴ := n5_shift_brownian h.brown t₁
  filter_upwards [h.hdyn, localItoIntegralE_const hŴ (fun _ : Fin 1 => σ)] with ω hdyn hloc hω
  have hAω : ω ∈ A := hω.1.1
  have hA0 := h.hA0 ω hAω
  have hpw := n5_pathwise (ρ := ρ) (A := A) h.hκ h.hC h.hδ h.hε h.hεC h.hdur hω hA0.2 (h.hG ω)
    (fun u => h.hc u ω) hdyn
  refine ⟨fun s hs => ?_, ?_⟩
  · have hs0 : 0 ≤ s := hs.1
    have hZ := hpw.1 s hs
    have hint : ∫ u in Icc 0 s, n5_b G B ρ t₁ σ δ ε dur (κ / δ + C) A u ω =
        ∫ u in Icc 0 s, n5_bcl (κ / δ + C) (n5_dq (fun u => n5_Zp G B t₁ σ u ω) u) :=
      setIntegral_congr_fun measurableSet_Icc fun u hu => n5_b_of_le (hu.2.trans hs.2)
    have hX : n5_Xp P ℱ B G κ σ C ρ t₁ dur ε δ A s ω =
        n5_X0 G t₁ δ ε ω + (∫ u in Icc 0 s, n5_b G B ρ t₁ σ δ ε dur (κ / δ + C) A u ω) +
          localItoIntegralE P (n5_shF ℱ (t₁ : ℝ)) (n5_shW B t₁) (fun (_ : ℝ) (_ : Ω) (_ : Fin 1) => σ) s ω := rfl
    rw [hX, hint, ← hZ, hloc s, n5_X0_eq (show δ < G t₁ ω from hω.2) hA0.2]
    simp only [Fin.sum_univ_one, ofNNRealTime_apply, n5_shW, n5_Zp, smul_eq_mul, n5_H_zero]
    ring
  · exact hpw.2.mono fun s hs hsI => by
      rw [n5_b_of_le hsI.2]; exact hs hsI

theorem n5_hXK [IsProbabilityMeasure P] (h : N5H P ℱ B G c κ σ C ρ t₁ dur ε δ A) :
    ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 dur, (t : WithTop ℝ) ≤ n5_tau2 G ρ t₁ δ ε dur A ω →
      n5_Xp P ℱ B G κ σ C ρ t₁ dur ε δ A t ω ∈ Icc δ ε := by
  filter_upwards [n5_kc h] with ω hkc t ht htτ
  have htT : t ≤ n5_tauR G ρ t₁ δ ε dur A ω := by
    have : (t : WithTop ℝ) ≤ ((n5_tauR G ρ t₁ δ ε dur A ω : ℝ) : WithTop ℝ) := htτ
    exact_mod_cast this
  by_cases hω : ω ∈ n5_A1 G ρ t₁ δ A
  · rw [(hkc hω).1 t ⟨ht.1, htT⟩]
    exact n5_H_mem_of_le h hω ht.1 htT
  · have h0 : t = 0 := le_antisymm (by rw [n5_tauR_of_not_mem hω] at htT; exact htT) ht.1
    subst h0
    have e : n5_Xp P ℱ B G κ σ C ρ t₁ dur ε δ A 0 ω = n5_X0 G t₁ δ ε ω := itoProcess_zero P _ _ _ _ _ ω
    rw [e]
    have := n5_X0_mem (G := G) (t₁ := t₁) h.hδ h.hδε ω
    exact ⟨this.1, this.2.trans (by linarith [h.hε])⟩

end HRS.MC.CepN5
