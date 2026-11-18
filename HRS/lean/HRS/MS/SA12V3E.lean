import HRS.MS.SA12V3D

/-!
# S.A.12 N1/N2 (SA12V3 worker), part E: the uniform box bound and the two limit statements for mean-zero tests

* `sa12v3_box_bound`: `|∫ γ_L(x-u) φ(u) du| ≤ C B` uniformly for `L ≥ 1`, `x` in the centred box;
* `sa12v3_loc_conv`: for `‖x‖ ≤ ρ`, `|∫ γ_L(x-u) φ(u) du - ∫ g(x-u) φ(u) du| ≤ η B` for `L` large.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Pointwise

namespace HRS.MH.AdjointRd.Phase2SA12V3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12v3_norm_le_of_coord {x : Euc d} {a : ℝ} (h : ∀ i, |x i| ≤ a) :
    ‖x‖ ≤ Real.sqrt (d * a ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin d, a ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
    _ = d * a ^ 2 := by simp

/-- In the centred box the origin is a nearest lattice point (coordinatewise). -/
theorem sa12v3_box_coord {L : ℝ} {x : Euc d} (hx : x ∈ centeredBox d L) (k : Fin d → ℤ) (i : Fin d) :
    |x i| ≤ |(x - L • latticePt k) i| := by
  have h := hx i
  have e : (x - L • latticePt k) i = x i - L * (k i : ℝ) := by simp [latticePt]
  rw [e]
  by_cases hk : k i = 0
  · simp [hk]
  · have hL : 0 ≤ L := by linarith [h.1, h.2]
    have hk1 : (1 : ℝ) ≤ |(k i : ℝ)| := by
      have : (1 : ℤ) ≤ |k i| := Int.one_le_abs hk
      exact_mod_cast this
    have h1 : L ≤ |L * (k i : ℝ)| := by
      rw [abs_mul, abs_of_nonneg hL]; nlinarith
    have h2 : |L * (k i : ℝ)| ≤ |x i - L * (k i : ℝ)| + |x i| := by
      have := abs_sub_abs_le_abs_sub (L * (k i : ℝ)) (x i)
      calc |L * (k i : ℝ)| = |(x i - (x i - L * (k i : ℝ)))| := by ring_nf
        _ ≤ |x i| + |x i - L * (k i : ℝ)| := abs_sub _ _
        _ = _ := add_comm _ _
    have h3 : |x i| ≤ L / 2 := abs_le.2 ⟨h.1, h.2.le⟩
    linarith

theorem sa12v3_box_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
      ∀ B : ℝ, ∀ φ : Euc d → ℝ, sa12v3_Test R B φ → ∀ x : Euc d, x ∈ centeredBox d L →
        |∫ u, γ (x - u) * φ u| ≤ C * B := by
  obtain ⟨Cf, hCf, hfar⟩ := sa12v3_far hd s hs0 hsd R hR
  set ρ0 : ℝ := Real.sqrt (d * (R + 1) ^ 2) with hρ0
  have hρ0pos : 0 < ρ0 := Real.sqrt_pos.2 (by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity)
  have hr' : 0 < ρ0 + R := by linarith
  obtain ⟨L₁, Cn, hL₁, hCn, hnear⟩ := sa12v3_near_bound hd s hs0 hsd (ρ0 + R) hr'
  obtain ⟨Cb, hCb, hbd⟩ := sa12v3_bounded hd s hs0 hsd L₁ R hL₁ hR
  refine ⟨Cf + Cn + Cb, by positivity, ?_⟩
  intro L hL γ hγ B φ hT x hx
  have hB := hT.B_nonneg
  by_cases hfa : ∀ k : Fin d → ℤ, R + 1 ≤ ‖x - L • latticePt k‖
  · have := hfar L hL γ hγ B φ hT x hfa
    refine this.trans ?_
    nlinarith [mul_nonneg hCn hB, mul_nonneg hCb hB]
  · push_neg at hfa
    obtain ⟨k, hk⟩ := hfa
    have hcoord : ∀ i, |x i| ≤ R + 1 := by
      intro i
      refine (sa12v3_box_coord hx k i).trans ?_
      have : |(x - L • latticePt k) i| ≤ ‖x - L • latticePt k‖ := by
        have := EuclideanSpace.norm_eq (x - L • latticePt k)
        have h1 := (PiLp.norm_apply_le (x - L • latticePt k) i)
        simpa [Real.norm_eq_abs] using h1
      linarith
    have hxn : ‖x‖ ≤ ρ0 := sa12v3_norm_le_of_coord hcoord
    by_cases hLL : L₁ ≤ L
    · have := hnear L hLL γ hγ R B φ hT x (fun u hu => by
        calc ‖x - u‖ ≤ ‖x‖ + ‖u‖ := norm_sub_le _ _
          _ ≤ ρ0 + R := add_le_add hxn hu)
      refine this.trans ?_
      nlinarith [mul_nonneg hCf hB, mul_nonneg hCb hB]
    · have := hbd L hL (not_le.1 hLL).le γ hγ B φ hT x hx
      refine this.trans ?_
      nlinarith [mul_nonneg hCf hB, mul_nonneg hCn hB]

theorem sa12v3_loc_conv (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (R ρ : ℝ) (hR : 0 ≤ R)
    (hρ : 0 ≤ ρ) (η : ℝ) (hη : 0 < η) :
    ∃ L₁ : ℝ, 1 ≤ L₁ ∧ ∀ L : ℝ, L₁ ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
      ∀ B : ℝ, ∀ φ : Euc d → ℝ, sa12v3_Test R B φ → ∀ x : Euc d, ‖x‖ ≤ ρ →
        |(∫ u, γ (x - u) * φ u) - ∫ u, rieszKernel d s (x - u) * φ u| ≤ η * B := by
  obtain ⟨L₁, hL₁, h⟩ := sa12v3_near_conv hd s hs0 hsd (ρ + R + 1) (by linarith) η hη
  refine ⟨L₁, hL₁, fun L hL γ hγ B φ hT x hx => h L hL γ hγ R B φ hT x (fun u hu => ?_)⟩
  calc ‖x - u‖ ≤ ‖x‖ + ‖u‖ := norm_sub_le _ _
    _ ≤ ρ + R + 1 := by linarith

end HRS.MH.AdjointRd.Phase2SA12V3
