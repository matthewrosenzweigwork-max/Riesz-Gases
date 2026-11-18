import HRS.MS.R26T8AP11a2
import HRS.MS.R26T8AP11f9
import HRS.MS.R26T8AP11f8
import HRS.MS.R26T8AP11f2

/-!
# S8.2 T8A packet P11 (helper a3): the divergence source is conormal
Monotonicity (order, constant), finite sums, and `r26t8a_divSource_conormal`: for `Q` `Conormal (K+2) b M σ' A` and a density `ρ` with
bounded jets of order `≤ K+1`, `divSource ρ Q` is `Conormal K b M (σ'+2) (C d K Cρ A)` (`C = 6 d 2^K (K+1)^2`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_conormal_mono_sA {k b : ℕ} {M σ σ' A A' : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ A') (hσ : σ ≤ σ')
    {F : Euc d → Euc d → ℝ} (hF : Conormal k b M σ A F) : Conormal k b M σ' A' F := by
  refine ⟨hF.1, fun p q hpq X z hz => ?_⟩
  refine (hF.2 p q hpq X z hz).trans ?_
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hr0 : 0 < min 1 ‖z‖ := lt_min one_pos hz0
  have hr1 : min 1 ‖z‖ ≤ 1 := min_le_left _ _
  have hW : 0 ≤ HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
    simp only [HRS.MS.Phase2S82.pairWeight]
    exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  have hL : 0 ≤ (1 + |Real.log (min 1 ‖z‖)|) ^ b := by positivity
  have hp : (min 1 ‖z‖) ^ (-(σ + (q : ℝ))) ≤ (min 1 ‖z‖) ^ (-(σ' + (q : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)
  have hE : 1 + (min 1 ‖z‖) ^ (-(σ + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ b ≤
      1 + (min 1 ‖z‖) ^ (-(σ' + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ b := by
    have := mul_le_mul_of_nonneg_right hp hL; linarith
  have hE0 : 0 ≤ 1 + (min 1 ‖z‖) ^ (-(σ' + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ b := by positivity
  have h1 := mul_le_mul_of_nonneg_left hE (mul_nonneg hA0 hW)
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hW) hE0
  exact h1.trans h2

theorem r26t8a_conormal_zero (k b : ℕ) (M σ : ℝ) : Conormal k b M σ 0 (fun _ _ : Euc d => (0 : ℝ)) := by
  have hu : Function.uncurry (fun _ _ : Euc d => (0 : ℝ)) = fun _ => 0 := rfl
  have h := r26t8a_conormal_of_smooth (k := k) (b := b) (σ := σ) (M := M) (B := 0) le_rfl
    (F := fun _ _ : Euc d => (0 : ℝ)) (by rw [hu]; exact contDiff_const) (fun j hj x y => by
      rw [hu, iteratedFDeriv_zero_fun]
      simp)
  simpa using h

theorem r26t8a_conormal_sum {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {ι : Type*} (s : Finset ι) {k b : ℕ} {M σ : ℝ}
    {A : ι → ℝ} {F : ι → Euc d → Euc d → ℝ} (h : ∀ i ∈ s, Conormal k b M σ (A i) (F i)) :
    Conormal k b M σ (∑ i ∈ s, A i) (fun x y => ∑ i ∈ s, F i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using r26t8a_conormal_zero (d := d) k b M σ
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact r26t8a_conormal_add hchi (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end HRS.MS.R26T8A
