import HRS.MS.S21H2_W13B
import HRS.MS.S21F_P00
import HRS.MS.S21F_D02
import HRS.MS.WsPrepAux8
import HRS.MS.R2IidAux1

/-!
# S21H2, packet R26-T3.W13: the actual moving density producer from the native S11Q3 tuple

Tuple at `(j, m) = (1, d/2 + 8)` (W13B), item (1) of S11.4 at these explicit indices (W13A), a trajectory of `Trajectory p δ` lies in the S6.3 small class at these low
indices (`s21p_resulting_in_class_low`, uniqueness of the constructed class solution), a `Particle` has a filtered version (`r26t3_filtered_particle`) with the same
time marginals, and its exact initial law gives `MovPrepared`.  `δ` is chosen below the tuple smallness and with `C₁ δ ≤ r`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.S113BD

theorem r26t3_actual_density (p : Parameters) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ ∃ pinf K : ℝ, 1 < pinf ∧
      ∀ R : Trajectory p δ, ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
        ∀ t : ℝ, 0 ≤ t →
          HasR2ActualDensity p.s p.β pinf K (r26t3_mu R t) (law A.P (A.X t.toNNReal)) := by
  have hd := p.hd
  have hsd : p.s < (p.d : ℝ) := by
    have := p.hs
    have : (0 : ℝ) < p.d := by exact_mod_cast (by omega : 0 < p.d)
    linarith
  by_cases hex : ∃ ρ₁ : Euc p.d → ℝ, IsThermalEquilibrium p.d p.s p.a p.β ρ₁
  swap
  · exact ⟨1 / 2, by norm_num, le_rfl, 2, 0, by norm_num, fun R => absurd ⟨R.ρβ, R.thermal⟩ hex⟩
  obtain ⟨ρ₁, hρ₁⟩ := hex
  obtain ⟨εs, r, c₀, c, C', hOK, hloc⟩ := HRS.MS.S21H2W13.s21h2_tuple hd p.s p.hs0 p.hs p.β p.a p.hβ p.ha ρ₁ hρ₁
  have hlog : p.γ = 0 → S113XLogNormalizer p.d p.s p.a p.β ρ₁ 1 (p.d / 2 + 8) εs r c₀ := by
    intro hγ0
    have hs00 : p.s = 0 := by
      rcases lt_or_eq_of_le p.hs0 with h | h
      · exact absurd hγ0 (p.hγs h).ne'
      · exact h.symm
    obtain ⟨hε, hr, hc₀, hc, hC₁, hNL, -⟩ := hOK
    exact s113x_logNormalizer hd hs00 p.hβ p.ha hρ₁ hC₁ hc₀ hNL
  have hmm : (p.d : ℝ) / 2 + ((1 : ℕ) : ℝ) + 6 < ((p.d / 2 + 8 : ℕ) : ℝ) := by
    have : (p.d : ℝ) ≤ 2 * ((p.d / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast (by omega : p.d ≤ 2 * (p.d / 2) + 1)
    push_cast; linarith
  obtain ⟨pinf, K, hpinf, hAD⟩ := HRS.MS.S21H2W13.s21h2_item1_explicit hd p.s p.hs0 p.hs p.β p.a p.hβ p.ha ρ₁ hρ₁ p.γ p.hγ
    1 (p.d / 2 + 8) le_rfl hmm εs r c₀ c C' hOK hloc hlog
  obtain ⟨hεs, hr, hc₀, hc, hC', hNL, -⟩ := hOK
  set Kc : ℝ := max p.C₁ 1 with hKc
  have hKc1 : 0 < Kc := lt_of_lt_of_le one_pos (le_max_right _ _)
  set δ : ℝ := min (min (1 / 2) εs) (r / Kc) with hδ
  have hδpos : 0 < δ := lt_min (lt_min (by norm_num) hεs) (div_pos hr hKc1)
  have hCr : p.C₁ * δ ≤ r := by
    calc p.C₁ * δ ≤ Kc * δ := mul_le_mul_of_nonneg_right (le_max_left _ _) hδpos.le
      _ ≤ Kc * (r / Kc) := mul_le_mul_of_nonneg_left (min_le_right _ _) hKc1.le
      _ = r := by field_simp
  refine ⟨δ, hδpos, (min_le_left _ _).trans (min_le_left _ _), pinf, K, hpinf, fun R N hN A t ht => ?_⟩
  have hρeq : R.ρβ = ρ₁ := (HRS.MS.Mov0.mv0_rho_eq hd p.hs0 hsd p.ha p.hβ R.thermal).trans
    (HRS.MS.Mov0.mv0_rho_eq hd p.hs0 hsd p.ha p.hβ hρ₁).symm
  have hadm := R.admissible
  have hres := R.resulting
  rw [hρeq] at hadm hres
  have hmb : ((p.d / 2 + 8 : ℕ) : ℝ) ≤ 102 * (p.d : ℝ) + 1020 := by
    have : ((p.d / 2 : ℕ) : ℝ) ≤ p.d := by exact_mod_cast Nat.div_le_self p.d 2
    push_cast; linarith
  obtain ⟨hf0, hcls⟩ := s21p_resulting_in_class_low (by omega) hmb hNL
    ((min_le_left _ _).trans (min_le_right _ _)) hCr hadm hres
  obtain ⟨F⟩ := r26t3_filtered_particle A
  have hsetup : MovParticleSetup A.P p.d p.s p.a p.β N A.X₀ A.W F.X :=
    ⟨A.brownian, A.independent, F.strong, ⟨F.ℱ, F.Wc, F.filtered⟩⟩
  have hP0 : IsProbabilityMeasure (r26t3_mu R 0) := by
    have hdens := (r26t3_reference_data p δ hδpos (by exact (min_le_left _ _).trans (min_le_left _ _)) R).2.2.1 0 le_rfl
    exact s11iid_prob hdens.1.nonneg hdens.1.integral_one
  have hprep : MovPrepared p.d p.s N p.γ (HRS.Whole.withDensityReal (R.ρ 0)) (A.P.map A.X₀) := by
    have hlaw : A.P.map A.X₀ = r26t3_Q R N := A.initial
    rcases lt_or_eq_of_le p.hγ with hpos | h0
    · exact Or.inr ⟨hpos, hlaw⟩
    · refine Or.inl ⟨h0.symm, ?_⟩
      rw [hlaw]
      unfold r26t3_Q
      rw [← h0]
      exact s11iid_gibbs_zero _ N _
  have hD := hAD (fun x => R.ε * R.ψ x) hf0 R.ρ hcls N hN A.P A.X₀ A.W F.X hsetup hprep t ht
  have hlawX : law A.P (A.X t.toNNReal) = A.P.map (F.X t.toNNReal) := by
    refine (Measure.map_congr ?_)
    filter_upwards [F.indist] with ω hω using (hω t.toNNReal).symm
  rw [hlawX]
  exact hD

end HRS.MS.R26T3
