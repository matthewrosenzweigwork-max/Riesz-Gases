import HRS.MS.R26T8AP11a
import HRS.MS.R26T8AP01

/-!
# S8.2 nonlocal layer: a globally smooth modification of the Riesz kernel (P11e, part 3b, piece B2)
`Kc(u) = ‖u‖^(alpha-d) (1 - chi(4u/delta))` is `C^infty` on all of `E`, equals the kernel for `‖u‖ >= delta/2`, and has bounded jets on `‖u‖ >= delta`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

/-- The smooth modification of the kernel. -/
def r26t8a_Kc {d : ℕ} (alpha : ℝ) (chi : Euc d → ℝ) (δ : ℝ) (u : Euc d) : ℝ :=
  ‖u‖ ^ (alpha - (d : ℝ)) * (1 - chi ((4 / δ) • u))

theorem r26t8a_Kc_contDiff (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ) (halpha : 0 < alpha) (had : alpha < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ∞ (r26t8a_Kc alpha chi δ) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : ‖u‖ < δ / 4
  · have hev : r26t8a_Kc alpha chi δ =ᶠ[𝓝 u] fun _ => 0 := by
      have hopen : IsOpen {w : Euc d | ‖w‖ < δ / 4} := isOpen_lt continuous_norm continuous_const
      filter_upwards [hopen.mem_nhds hu] with w hw
      have hw' : ‖w‖ < δ / 4 := hw
      have h1 : ‖(4 / δ) • w‖ ≤ 1 := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_eq_mul_div, div_le_one hδ]; linarith
      simp only [r26t8a_Kc, hchi.2.2.2.1 _ h1, sub_self, mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · push Not at hu
    have hne : u ≠ 0 := by intro h; rw [h, norm_zero] at hu; linarith
    have h1 : ContDiffAt ℝ ∞ (fun w : Euc d => ‖w‖ ^ (alpha - (d : ℝ))) u :=
      HRS.contDiffAt_rpow_norm (V := Euc d) (alpha - (d : ℝ)) hne
    have h2 : ContDiffAt ℝ ∞ (fun w : Euc d => 1 - chi ((4 / δ) • w)) u :=
      (contDiff_const.sub (hchi.1.comp (contDiff_const_smul _))).contDiffAt
    exact h1.mul h2

theorem r26t8a_Kc_eq (d : ℕ) (alpha : ℝ) (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) {δ : ℝ} (hδ : 0 < δ)
    {u : Euc d} (hu : δ / 2 ≤ ‖u‖) : r26t8a_Kc alpha chi δ u = ‖u‖ ^ (alpha - (d : ℝ)) := by
  have h : ‖(4 / δ) • u‖ ≥ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hδ]; linarith
  simp only [r26t8a_Kc, hchi.2.2.2.2 _ h, sub_zero, mul_one]

theorem r26t8a_Kc_jets (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ) (halpha : 0 < alpha) (had : alpha < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ k, ∀ u : Euc d, δ ≤ ‖u‖ → ‖iteratedFDeriv ℝ i (r26t8a_Kc alpha chi δ) u‖ ≤ C := by
  obtain ⟨CK, hCK0, -, hKj, -⟩ := r26t8a_riesz_potential_jets d hd alpha halpha had k
  refine ⟨CK * ∑ i ∈ Finset.range (k + 1), δ ^ (alpha - (d : ℝ) - i), mul_nonneg hCK0
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg hδ.le _), ?_⟩
  intro i hi u hu
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu; linarith
  have hev : r26t8a_Kc alpha chi δ =ᶠ[𝓝 u] fun w : Euc d => ‖w‖ ^ (alpha - (d : ℝ)) := by
    have hopen : IsOpen {w : Euc d | δ / 2 < ‖w‖} := isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds (by show δ / 2 < ‖u‖; linarith)] with w hw
    exact r26t8a_Kc_eq d alpha chi hchi hδ (le_of_lt hw)
  rw [(hev.iteratedFDeriv ℝ i).self_of_nhds]
  refine (hKj i hi u hu0).trans ?_
  have hneg : alpha - (d : ℝ) - i ≤ 0 := by
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith
  have h1 : ‖u‖ ^ (alpha - (d : ℝ) - i) ≤ δ ^ (alpha - (d : ℝ) - i) :=
    Real.rpow_le_rpow_of_nonpos hδ hu hneg
  have h2 : δ ^ (alpha - (d : ℝ) - i) ≤ ∑ j ∈ Finset.range (k + 1), δ ^ (alpha - (d : ℝ) - j) :=
    Finset.single_le_sum (f := fun j : ℕ => δ ^ (alpha - (d : ℝ) - j)) (fun j _ => Real.rpow_nonneg hδ.le _)
      (Finset.mem_range.2 (by omega))
  exact mul_le_mul_of_nonneg_left (h1.trans h2) hCK0

end HRS.MS.R26T8A
