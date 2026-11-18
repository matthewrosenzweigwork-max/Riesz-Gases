import HRS.Equilibrium.Parametrix.PX3aAuxT

/-!
# Packet PX3a auxiliaries U: the canonical projection preserves the conormal class
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma abs_integral_le_cbNorm (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {m : ℕ} {r : Torus d → ℝ}
    (hr : Torus.IsCk (m : WithTop ℕ∞) r) : |∫ x, r x ∂μ| ≤ Torus.cbNorm m r := by
  have hΦ : ContDiff ℝ (m : WithTop ℕ∞) (Torus.lift r) := hr
  have hbdd : BddAbove (Set.range fun x : Euc d => ‖iteratedFDeriv ℝ 0 (Torus.lift r) x‖) := by
    obtain ⟨M, _, hM⟩ := bdd_iteratedFDeriv_lift r 0 (hΦ.of_le (by exact_mod_cast Nat.zero_le m))
    exact ⟨M, by rintro _ ⟨x, rfl⟩; exact hM x⟩
  set R : ℕ → ℝ := fun k => ⨆ y : Euc d, ‖iteratedFDeriv ℝ k (Torus.lift r) y‖ with hR
  have hR0 : ∀ k, 0 ≤ R k := fun k => Real.iSup_nonneg fun _ => norm_nonneg _
  have hcb : Torus.cbNorm m r = ∑ k ∈ Finset.range (m + 1), R k := rfl
  have h1 : R 0 ≤ Torus.cbNorm m r := by
    rw [hcb]
    exact Finset.single_le_sum (f := R) (fun j _ => hR0 j) (Finset.mem_range.mpr (by omega))
  have hx : ∀ x : Torus d, ‖r x‖ ≤ R 0 := by
    intro x
    have h := le_ciSup hbdd (Torus.rep x)
    have e : ‖iteratedFDeriv ℝ 0 (Torus.lift r) (Torus.rep x)‖ = ‖r x‖ := by
      rw [norm_iteratedFDeriv_zero]; simp [Torus.lift, Torus.mk_rep]
    rw [e] at h
    exact h
  have h2 := norm_integral_le_of_norm_le_const (μ := μ) (f := r) (C := R 0)
    (Filter.Eventually.of_forall hx)
  have h3 : ‖∫ x, r x ∂μ‖ ≤ R 0 := by simpa using h2
  rw [← Real.norm_eq_abs]
  exact h3.trans h1

theorem canonical_conormal (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {σ : ℝ}
    (hσ : σ < d) (b0 m : ℕ) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (b : ℕ → ℕ), (∀ c, b c ≤ b0) → ∀ (B : ℝ) (H : Torus d → Torus d → ℝ),
      0 ≤ B → ConormalL σ b m B H →
      ConormalL σ b m (Cc * B) (canonicalCenter (withDensityReal ρ) H) := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨Crow, hCrow0, hCrow⟩ := conormal_row_smooth_aux hd hρ hσ b0 m
  obtain ⟨Cs, hCs0, hCs⟩ := conormal_sigma2 (d := d) σ m
  refine ⟨1 + 2 * Cs * Crow, by positivity, fun b hb B H hB hH => ?_⟩
  have hHc : Conormal σ b0 m B H := conormalL_mono_b hB hb hH
  have hHt : Conormal σ b0 m B (swapK H) := conormalL_mono_b hB hb (conormalL_swap hH)
  obtain ⟨hr1, hcb1⟩ := hCrow B H hB hHc
  obtain ⟨hr2, hcb2⟩ := hCrow B (swapK H) hB hHt
  set r₁ : Torus d → ℝ := fun x => ∫ y, H x y ∂(withDensityReal ρ) with hr₁
  set r₂ : Torus d → ℝ := fun y => ∫ x, swapK H y x ∂(withDensityReal ρ) with hr₂
  set c₀ : ℝ := ∫ x', r₁ x' ∂(withDensityReal ρ) with hc₀
  have hc₀b : |c₀| ≤ Torus.cbNorm m r₁ := abs_integral_le_cbNorm _ hr1
  have hsig := hCs r₁ r₂ hr1 hr2 c₀ hc₀b
  have hsig' : ConormalL σ b m (Cs * (Torus.cbNorm m r₁ + Torus.cbNorm m r₂))
      (fun x y => -r₁ x - r₂ y + c₀) := by
    refine conormalL_mono_b ?_ (fun c => Nat.zero_le _) hsig
    have h1 : 0 ≤ Torus.cbNorm m r₁ := by
      unfold Torus.cbNorm; exact Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ Torus.cbNorm m r₂ := by
      unfold Torus.cbNorm; exact Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
    positivity
  have hsum := conormalL_add hH hsig'
  have hcc : (fun x y => H x y + (-r₁ x - r₂ y + c₀)) = canonicalCenter (withDensityReal ρ) H := by
    funext x y
    unfold canonicalCenter
    simp only [hr₁, hr₂, hc₀, swapK]
    ring
  rw [hcc] at hsum
  refine conormalL_mono_B hsum ?_ ?_
  · have h1 : 0 ≤ Torus.cbNorm m r₁ := by
      unfold Torus.cbNorm; exact Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ Torus.cbNorm m r₂ := by
      unfold Torus.cbNorm; exact Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
    positivity
  · have : Cs * (Torus.cbNorm m r₁ + Torus.cbNorm m r₂) ≤ Cs * (Crow * B + Crow * B) :=
      mul_le_mul_of_nonneg_left (add_le_add hcb1 hcb2) hCs0
    nlinarith

end HRS.Parx

end
