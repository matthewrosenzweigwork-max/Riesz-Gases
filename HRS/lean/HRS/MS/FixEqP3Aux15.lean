import HRS.MS.FixEqP3Aux14

/-!
# S5.7 `fixed_equation` (worker S57P), part 27: the initial part of the linear fluctuation field

`s57pI C m a η t` is the element of `B_m` with coordinates `a η(U^{0,t} φ_α)`.  For a bounded linear `η` on `E_{n,(d+3)/2}` with
`dualNormE < ⊤`: `|η f| ≤ ‖η‖ C ‖f‖_{C^n_b}` (`s57p_eta_bound`), additivity (`s57p_eta_sub`), coordinatewise bounds, the `ℓ²` norm of
`s57pI` and its Lipschitz continuity in `t` (the terminal-time bound `s57p_td_bound` at `r = 0`).
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

theorem s57p_eval_cont {m : ℝ} {φ : Euc d → ℝ} (hφ : MemOsc m φ) : Continuous fun u : OscDual d m => OscDual.eval u φ := by
  have : (fun u : OscDual d m => OscDual.eval u φ) = fun u => OscDual.toDual u (OscSpace.ofFun m φ) :=
    funext fun u => (OscDual.toDual_ofFun u φ hφ).symm
  rw [this]
  exact (OscDual.toDual (d := d) (m := m)).continuous.clm_apply continuous_const

theorem s57p_eval_add {m : ℝ} {φ : Euc d → ℝ} (hφ : MemOsc m φ) (u v : OscDual d m) :
    OscDual.eval (u + v) φ = OscDual.eval u φ + OscDual.eval v φ := by
  have h1 := OscDual.toDual_ofFun (u + v) φ hφ
  have h2 := OscDual.toDual_ofFun u φ hφ
  have h3 := OscDual.toDual_ofFun v φ hφ
  rw [← h1, ← h2, ← h3, map_add, ContinuousLinearMap.add_apply]

theorem s57p_ellVec_norm_sq {m : ℝ} {v g : MultiIndex d → ℝ} (hg : Summable g) (hv : ∀ α, v α ^ 2 ≤ g α) :
    Memℓp v 2 ∧ ‖(ellVec m v : OscDual d m)‖ ^ 2 ≤ ∑' α, g α := by
  have hs : Summable fun α => v α ^ 2 := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hv hg
  have hm : Memℓp v 2 := memℓp_two_iff.2 hs
  refine ⟨hm, ?_⟩
  have := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (show lp (fun _ : MultiIndex d => ℝ) 2 from (ellVec m v : OscDual d m))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at this
  have hc : ∀ i, (show lp (fun _ : MultiIndex d => ℝ) 2 from (ellVec m v : OscDual d m)) i = v i := fun i =>
    s57p_coord_ellVec hm i
  simp_rw [hc, Real.norm_eq_abs, sq_abs] at this
  calc ‖(ellVec m v : OscDual d m)‖ ^ 2 = ∑' i, v i ^ 2 := this
    _ ≤ ∑' α, g α := Summable.tsum_le_tsum hv hs hg

theorem s57p_ellVec_sub {m : ℝ} {v w : MultiIndex d → ℝ} (hv : Memℓp v 2) (hw : Memℓp w 2) :
    (ellVec m v : OscDual d m) - ellVec m w = ellVec m (fun α => v α - w α) := by
  have hvw : Memℓp (fun α => v α - w α) 2 := hv.sub hw
  rw [s57p_ellVec_of_mem hv, s57p_ellVec_of_mem hw, s57p_ellVec_of_mem hvw]
  rfl

section Eta

variable {n : ℕ} {P : ℝ} {η : (Euc d → ℝ) → ℝ}

theorem s57p_eta_bound (hP : (d : ℝ) < 2 * P) (hη : IsBoundedLinearOnE n P η) (hdual : dualNormE n P η < ⊤) {f : Euc d → ℝ}
    (hf : ContDiff ℝ n f) {B : ℝ} (hB : ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B) :
    |η f| ≤ (dualNormE n P η).toReal * (s57pC d n P * B) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (Nat.zero_le _) 0)
  have h := s57p_initial_bound hP hη hf hB
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top hdual.ne ENNReal.ofReal_ne_top) h
  rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg (s57pC_nonneg d n P) hB0)] at h2
  exact h2

theorem s57p_eta_sub (hP : (d : ℝ) < 2 * P) (hη : IsBoundedLinearOnE n P η) {f g : Euc d → ℝ} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    {B : ℝ} (hBf : ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B) (hBg : ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ B) :
    η (fun y => f y - g y) = η f - η g := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hBf 0 (Nat.zero_le _) 0)
  have hfin : ∀ {u : Euc d → ℝ}, (∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j u x‖ ≤ B) → weightedSobolevE n P u < ⊤ :=
    fun hu => lt_of_le_of_lt (s57p_E_le_cb hP hB0 hu) ENNReal.ofReal_lt_top
  have hc : ContDiff ℝ n (fun y => (-1 : ℝ) * g y) := contDiff_const.mul hg
  have hcb : ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (fun y => (-1 : ℝ) * g y) x‖ ≤ B := fun j hj x =>
    (s57p_norm_const_mul (hg.of_le (by exact_mod_cast hj)) (-1) x).trans (by simpa using hBg j hj x)
  have h1 := (hη.1 g g hg (hfin hBg) hg (hfin hBg) (-1)).2
  have h2 := (hη.1 f (fun y => (-1 : ℝ) * g y) hf (hfin hBf) hc (hfin hcb) 0).1
  have e1 : (fun y => f y - g y) = f + fun y => (-1 : ℝ) * g y := by funext y; simp [sub_eq_add_neg]
  have e2 : ((-1 : ℝ) • g) = fun y => (-1 : ℝ) * g y := by funext y; simp
  rw [e2] at h1
  rw [e1, h2, h1]; ring

end Eta

end HRS.MS.FixEq
