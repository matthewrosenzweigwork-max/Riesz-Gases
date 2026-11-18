import HRS.MS.SA12V3A

/-!
# S.A.12 N1/N2 (SA12V3 worker), part B: uniform bounds of `∫ γ_L(x-u) φ(u) du` on the centred box

* far from the lattice (`dist ≥ R + 1`): gradient bound of `γ_L` (C19) and the mean value inequality;
* `L ≤ Lmax`: the scaling `γ_L = L^{-s} g₁(·/L)` and local integrability of `g₁`;
* `L` large near the origin: the decomposition `γ_L = g + c + L^{-s} q(·/L)` (C18).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12V3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

/-- Every point is within `L/2` (coordinatewise) of a point of `L ℤ^d`. -/
theorem sa12v3_reduce {L : ℝ} (hL : 0 < L) (w : Euc d) :
    ∃ k : Fin d → ℤ, ∀ i, |(w - L • latticePt k) i| ≤ L / 2 := by
  refine ⟨fun i => ⌊w i / L + 1 / 2⌋, fun i => ?_⟩
  have h1 := Int.floor_le (w i / L + 1 / 2)
  have h2 := Int.lt_floor_add_one (w i / L + 1 / 2)
  have e : (w - L • latticePt (fun i => ⌊w i / L + 1 / 2⌋)) i = w i - L * (⌊w i / L + 1 / 2⌋ : ℝ) := by
    simp [latticePt]
  rw [e, abs_le]
  constructor
  · have : (⌊w i / L + 1 / 2⌋ : ℝ) * L ≤ (w i / L + 1 / 2) * L := mul_le_mul_of_nonneg_right h1 hL.le
    have e2 : (w i / L + 1 / 2) * L = w i + L / 2 := by field_simp
    nlinarith
  · have : (w i / L + 1 / 2) * L < ((⌊w i / L + 1 / 2⌋ : ℝ) + 1) * L := mul_lt_mul_of_pos_right h2 hL
    have e2 : (w i / L + 1 / 2) * L = w i + L / 2 := by field_simp
    nlinarith

theorem sa12v3_differentiableAt {s L : ℝ} (hL : 0 < L) {γ : Euc d → ℝ} (hγ : IsPeriodicRieszKernel d s L γ)
    {w : Euc d} (hw : ∀ k : Fin d → ℤ, w ≠ L • latticePt k) : DifferentiableAt ℝ γ w :=
  ((hγ.smooth.contDiffAt ((HRS.MS.Ker1.ker1_isOpen_offLattice hL).mem_nhds hw)).differentiableAt (by simp))

/-- Gradient bound at distance `≥ 1` from the lattice. -/
theorem sa12v3_grad_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
      ∀ w : Euc d, (∀ k : Fin d → ℤ, 1 ≤ ‖w - L • latticePt k‖) → ‖fderiv ℝ γ w‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := periodic_kernel_cube hd s hs0 hsd 0
  refine ⟨3 * C, by positivity, fun L hL γ hγ w hw => ?_⟩
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  obtain ⟨k, hk⟩ := sa12v3_reduce hL0 w
  set w' : Euc d := w - L • latticePt k with hw'
  have hn1 : 1 ≤ ‖w'‖ := hw k
  have hw'0 : w' ≠ 0 := by
    intro h; rw [h, norm_zero] at hn1; linarith
  have hshift : fderiv ℝ γ w = fderiv ℝ γ w' := by
    have h1 : (fun x => γ (x + L • latticePt k)) = γ := funext fun x => hγ.periodic x k
    have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := γ) (L • latticePt k) (x := w')
    rw [h1] at h2
    rw [h2, hw']; congr 1; abel
  rw [hshift, ← norm_iteratedFDeriv_one]
  have h := hC L hL γ hγ 1 (by norm_num) (by simp; linarith) w' hw'0 hk
  refine h.trans ?_
  have a1 : ‖w'‖ ^ (-s - ((1 : ℕ) : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by push_cast; linarith)
  have a2 : (if 0 < s then L ^ (-s - ((1 : ℕ) : ℝ)) else 0) ≤ 1 := by
    split_ifs
    · exact Real.rpow_le_one_of_one_le_of_nonpos hL (by push_cast; linarith)
    · norm_num
  have a3 : (if s = 0 then L ^ (-((1 : ℕ) : ℝ)) else 0) ≤ 1 := by
    split_ifs
    · exact Real.rpow_le_one_of_one_le_of_nonpos hL (by push_cast; linarith)
    · norm_num
  nlinarith

/-- Far from the lattice. -/
theorem sa12v3_far (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
      ∀ B : ℝ, ∀ φ : Euc d → ℝ, sa12v3_Test R B φ → ∀ x : Euc d,
        (∀ k : Fin d → ℤ, R + 1 ≤ ‖x - L • latticePt k‖) → |∫ u, γ (x - u) * φ u| ≤ C * B := by
  obtain ⟨C1, hC10, hC1⟩ := sa12v3_grad_bound hd s hs0 hsd
  refine ⟨C1 * R * (volume : Measure (Euc d)).real (Metric.closedBall (0 : Euc d) R), by positivity, ?_⟩
  intro L hL γ hγ B φ hT x hx
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hball : ∀ z ∈ Metric.closedBall x R, ∀ k : Fin d → ℤ, 1 ≤ ‖z - L • latticePt k‖ := by
    intro z hz k
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have h1 := hx k
    have h2 : ‖x - L • latticePt k‖ ≤ ‖x - z‖ + ‖z - L • latticePt k‖ := by
      have := norm_add_le (x - z) (z - L • latticePt k)
      simpa using this
    rw [norm_sub_rev] at hz
    linarith
  have hdiff : ∀ z ∈ Metric.closedBall x R, DifferentiableAt ℝ γ z := fun z hz =>
    sa12v3_differentiableAt hL0 hγ (fun k hk => by
      have := hball z hz k; rw [hk, sub_self, norm_zero] at this; linarith)
  have hder : ∀ z ∈ Metric.closedBall x R, ‖fderiv ℝ γ z‖ ≤ C1 := fun z hz => hC1 L hL γ hγ z (hball z hz)
  have hx0 : x ∈ Metric.closedBall x R := Metric.mem_closedBall_self hR
  have key := sa12v3_conv_le hγ.locInt hT x x (r' := R) (fun u hu => by
      rw [Metric.mem_closedBall, dist_eq_norm]; simpa using hu) (γ x) (fun _ => C1 * R)
    (fun _ => by positivity) (integrableOn_const measure_closedBall_lt_top.ne)
    (Eventually.of_forall fun z hz => by
      have := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hder (convex_closedBall x R) hx0 hz
      rw [Real.norm_eq_abs] at this
      have h3 : ‖z - x‖ ≤ R := by rw [Metric.mem_closedBall, dist_eq_norm] at hz; exact hz
      exact this.trans (by nlinarith [mul_le_mul_of_nonneg_left h3 hC10]))
  rw [setIntegral_const, smul_eq_mul] at key
  have hv : (volume : Measure (Euc d)).real (Metric.closedBall x R) =
      (volume : Measure (Euc d)).real (Metric.closedBall (0 : Euc d) R) := by
    simp [Measure.real_def, Measure.addHaar_closedBall_center]
  rw [hv] at key
  calc _ ≤ _ := key
    _ = _ := by ring

end HRS.MH.AdjointRd.Phase2SA12V3
