import HRS.MS.FixEqP3Aux15
import HRS.MS.ToriCoefAAux1
import HRS.Whole.Window

/-!
# S11.1 / all-tests boundary (S111K4AT), piece C: a functional of `L¹F` type on `C^r` functions with bounded jets

For `z ∈ L¹F` at one time `t0` (`IsR2L1F`), and `C^r` functions whose coordinate derivatives of order `≤ r` are bounded, the
value `|z t0 f - z t0 g|` is bounded by `‖z t0‖_F · C · sup|∂(f-g)|` (native `s57p_eta_sub`, `s57p_initial_bound`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4AT

open HRS HRS.Whole HRS.MS.FixEq

variable {d : ℕ}

theorem k4at_bounded_of_L1F {r : ℕ} {Pw T' : ℝ} {z : ℝ → (Euc d → ℝ) → ℝ} (hz : IsR2L1F r Pw T' z) {t0 : ℝ}
    (ht0 : t0 ∈ Set.Icc (0 : ℝ) T') : IsBoundedLinearOnE r Pw (z t0) := by
  obtain ⟨hadd, hsmul, M, hM⟩ := hz.1 t0 ht0
  refine ⟨fun f g hf hfE hg hgE c => ⟨hadd f g ⟨hf, hfE⟩ ⟨hg, hgE⟩, hsmul c f ⟨hf, hfE⟩⟩, M, fun f hf hfE => ?_⟩
  exact hM f ⟨hf, hfE⟩

theorem k4at_iter_le {r : ℕ} {h : Euc d → ℝ} {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i h x| ≤ b) :
    ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j h x‖ ≤ ((d : ℝ) + 1) ^ r * b := by
  intro j hj x
  refine (HRS.MS.ToriCoefA.tca_norm_iteratedFDeriv_le_sum j h x).trans ?_
  calc ∑ i : Fin j → Fin d, |partialDeriv i h x| ≤ ∑ _i : Fin j → Fin d, b :=
        Finset.sum_le_sum fun i _ => hb j hj i x
    _ = (d : ℝ) ^ j * b := by simp
    _ ≤ ((d : ℝ) + 1) ^ r * b := by
        refine mul_le_mul_of_nonneg_right ?_ hb0
        calc (d : ℝ) ^ j ≤ ((d : ℝ) + 1) ^ j := pow_le_pow_left₀ (Nat.cast_nonneg d) (by linarith) j
          _ ≤ ((d : ℝ) + 1) ^ r := pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]) hj

theorem k4at_z_bound {r : ℕ} {Pw T' : ℝ} (hP : (d : ℝ) < 2 * Pw) {z : ℝ → (Euc d → ℝ) → ℝ}
    (hz : IsR2L1F r Pw T' z) {t0 : ℝ} (ht0 : t0 ∈ Set.Icc (0 : ℝ) T') {f : Euc d → ℝ}
    (hf : ContDiff ℝ r f) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i f x| ≤ b) :
    ENNReal.ofReal |z t0 f| ≤ dualNormE r Pw (z t0) *
      ENNReal.ofReal (s57pC d r Pw * (((d : ℝ) + 1) ^ r * b)) :=
  s57p_initial_bound hP (k4at_bounded_of_L1F hz ht0) hf (k4at_iter_le hb0 hb)

theorem k4at_z_diff_bound {r : ℕ} {Pw T' : ℝ} (hP : (d : ℝ) < 2 * Pw) {z : ℝ → (Euc d → ℝ) → ℝ}
    (hz : IsR2L1F r Pw T' z) {t0 : ℝ} (ht0 : t0 ∈ Set.Icc (0 : ℝ) T') {f g : Euc d → ℝ}
    (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g) {b δ : ℝ} (hb0 : 0 ≤ b) (hδ0 : 0 ≤ δ)
    (hbf : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i f x| ≤ b)
    (hbg : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i g x| ≤ b)
    (hdiff : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i (fun y => f y - g y) x| ≤ δ) :
    ENNReal.ofReal |z t0 f - z t0 g| ≤ dualNormE r Pw (z t0) *
      ENNReal.ofReal (s57pC d r Pw * (((d : ℝ) + 1) ^ r * δ)) := by
  have hη := k4at_bounded_of_L1F hz ht0
  have hs := s57p_eta_sub hP hη hf hg (k4at_iter_le hb0 hbf) (k4at_iter_le hb0 hbg)
  rw [← hs]
  exact s57p_initial_bound hP hη (hf.sub hg) (k4at_iter_le hδ0 hdiff)

end HRS.MS.S111K4AT
