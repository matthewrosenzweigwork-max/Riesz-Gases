import HRS.MS.SpecAux27
import HRS.MS.SpecAux22

/-!
# S8P: eigenvectors of `T(1)` are in every `Σ^m` and have `C^J` representatives (S8.7, packet E4)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  If `T` has the smoothing bound `MovSmoothingBounds` at every level `m ≥ a = movA d s`
and `T 1 v = μ v` with `μ ≠ 0`, then `v ∈ Σ^{k a}` for all `k` (bootstrap `v = μ⁻¹ T(1) v`), hence `v` has a `C^J`
representative with bounded derivatives for every `J` (`s8p_osc_smooth`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovLin

variable {d : ℕ} {ρ : Euc d → ℝ}

theorem s8p_memOsc_const_mul {m : ℝ} {f : Euc d → ℝ} (hf : MemOsc m f) (c : ℝ) :
    MemOsc m (fun x => c * f x) := by
  refine ⟨hf.1.const_mul c, ?_⟩
  have : ∀ α : MultiIndex d, oscEigenvalue d α ^ m * hermiteCoeff (fun x => c * f x) α ^ 2 =
      c ^ 2 * (oscEigenvalue d α ^ m * hermiteCoeff f α ^ 2) := by
    intro α; rw [hermiteCoeff_const_mul]; ring
  simp_rw [this]
  exact hf.2.mul_left _

theorem s8p_eigen_memOsc {s : ℝ} (T : ℝ → (MovL2Zero ρ →L[ℝ] MovL2Zero ρ))
    (hall : ∀ m : ℝ, movA d s ≤ m → ∃ c C : ℝ, MovSmoothingBounds d s ρ m c C T)
    {μ : ℝ} (hμ : μ ≠ 0) (v : MovL2Zero ρ) (hv : T 1 v = μ • v) (k : ℕ) :
    MemOsc ((k : ℝ) * movA d s) (movFun v) := by
  induction k with
  | zero => simpa using (movlin_norm_osc0 v).1
  | succ k ih =>
    set a := movA d s with ha
    have ha0 : 0 < a := s8p_movA_pos d s
    have hm : a ≤ ((k + 1 : ℕ) : ℝ) * a := by
      have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
      nlinarith
    obtain ⟨c, C, hb⟩ := hall _ hm
    have hin : MemOsc (((k + 1 : ℕ) : ℝ) * a - a) (movFun v) := by
      have : ((k + 1 : ℕ) : ℝ) * a - a = (k : ℝ) * a := by push_cast; ring
      rwa [this]
    obtain ⟨hmem, -⟩ := hb.2 1 one_pos v hin
    have hae : (movFun v : Euc d → ℝ) =ᵐ[volume] fun x => μ⁻¹ * movFun (T 1 v) x := by
      rw [hv]
      filter_upwards [Lp.coeFn_smul μ (v : Lp ℝ 2 (volume : Measure (Euc d)))] with x hx
      show (v : Lp ℝ 2 (volume : Measure (Euc d))) x = μ⁻¹ * (μ • (v : Lp ℝ 2 (volume : Measure (Euc d)))) x
      rw [hx]; simp only [Pi.smul_apply, smul_eq_mul]; field_simp
    have h1 := s8p_memOsc_const_mul hmem μ⁻¹
    have h2 := mov2b_memOsc_congr hae.symm _ h1
    push_cast at h2 ⊢
    exact h2

theorem s8p_eigen_smooth {s : ℝ} (hd : 1 ≤ d) (T : ℝ → (MovL2Zero ρ →L[ℝ] MovL2Zero ρ))
    (hall : ∀ m : ℝ, movA d s ≤ m → ∃ c C : ℝ, MovSmoothingBounds d s ρ m c C T)
    {μ : ℝ} (hμ : μ ≠ 0) (v : MovL2Zero ρ) (hv : T 1 v = μ • v) (J : ℕ) :
    ∃ v' : Euc d → ℝ, ContDiff ℝ J v' ∧ (∀ k ≤ J, ∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ k v' x‖ ≤ B) ∧
      v' =ᵐ[volume] movFun v := by
  have ha0 : 0 < movA d s := s8p_movA_pos d s
  obtain ⟨k, hk⟩ := exists_nat_gt (((J : ℝ) + 2 * d + 1) / movA d s)
  have hlt : (J : ℝ) + 2 * d < (k : ℝ) * movA d s := by
    rw [div_lt_iff₀ ha0] at hk; linarith
  exact s8p_osc_smooth hd J hlt (s8p_eigen_memOsc T hall hμ v hv k)

end HRS.MS.Spec
