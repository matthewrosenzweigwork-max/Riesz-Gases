import HRS.MS.SA12DE7A
import HRS.MS.SA12CcDenseH
import HRS.Whole.Q09AAux4
import HRS.Whole.Q09AAux5

/-!
# S.A.12(c), packet E7.07 (worker S82Z2), part F: weak first derivatives against `C_c^∞` extend to smooth `L²` tests

`sa12de7_ibp_extend`: a first-order weak-derivative identity for real `C_c^∞` test functions extends (cutoff `ρ_a`,
dominated convergence) to every smooth `ψ` with `ψ, ∂_iψ ∈ L²`.  (The passage to the repository's `WD i f g` with complex
Schwartz tests is part G.)
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MS.SA12DE7

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Limit HRS.Whole.AppendixA HRS.Whole.Q09A

variable {d : ℕ}

theorem sa12de7_ibp_extend {f g : Euc d → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (i : Fin d)
    (h : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      ∫ x, g x * ψ x = -∫ x, f x * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)))
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ2 : MemLp ψ 2 volume)
    (hdψ : MemLp (fun x => fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) 2 volume) :
    ∫ x, g x * ψ x = -∫ x, f x * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) := by
  set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
  have hen : ‖e‖ = 1 := by simp [he]
  obtain ⟨M, hM0, hM⟩ := sa12cc_rho_deriv (d := d) 1
  set ρ : ℕ → Euc d → ℝ := fun n => sa12cc_rho ((n : ℝ) + 1) with hρ
  have hn1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hρsm : ∀ n, ContDiff ℝ ∞ (ρ n) := fun n => sa12cc_rho_contDiff _
  have hρd : ∀ n x, ‖fderiv ℝ (ρ n) x e‖ ≤ M / ((n : ℝ) + 1) := by
    intro n x
    have h1 := hM ((n : ℝ) + 1) (hn1 n) 1 le_rfl le_rfl x
    rw [norm_iteratedFDeriv_one] at h1
    calc ‖fderiv ℝ (ρ n) x e‖ ≤ ‖fderiv ℝ (ρ n) x‖ * ‖e‖ := (fderiv ℝ (ρ n) x).le_opNorm e
      _ ≤ M / ((n : ℝ) + 1) := by rw [hen, mul_one]; exact h1
  have hψn : ∀ n, IsCcInfty (fun x => ρ n x * ψ x) := fun n =>
    ⟨(hρsm n).mul hψ, (sa12cc_rho_compact (by linarith [hn1 n])).mul_right⟩
  have hder : ∀ n x, fderiv ℝ (fun y => ρ n y * ψ y) x e =
      ρ n x * fderiv ℝ ψ x e + fderiv ℝ (ρ n) x e * ψ x := by
    intro n x
    rw [fderiv_fun_mul ((hρsm n).differentiable (by simp) x) (hψ.differentiable (by simp) x)]
    simp [mul_comm]
  have hid : ∀ n, ∫ x, g x * (ρ n x * ψ x) =
      -∫ x, f x * (ρ n x * fderiv ℝ ψ x e + fderiv ℝ (ρ n) x e * ψ x) := by
    intro n
    have := h _ (hψn n)
    simp_rw [hder] at this
    exact this
  -- limits
  have hint1 : Integrable (fun x => g x * ψ x) volume := hg.integrable_mul hψ2
  have hlim1 : Tendsto (fun n => ∫ x, g x * (ρ n x * ψ x)) atTop (𝓝 (∫ x, g x * ψ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖g x * ψ x‖) (fun n => ?_) hint1.norm
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · exact (hg.aestronglyMeasurable.mul (((hρsm n).continuous.aestronglyMeasurable).mul hψ2.aestronglyMeasurable))
    · rw [norm_mul, norm_mul, norm_mul]
      have h0 := sa12cc_rho_nonneg ((n : ℝ) + 1) x
      have h1 := sa12cc_rho_le_one ((n : ℝ) + 1) x
      have hρ1 : ‖ρ n x‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg h0]; simpa [hρ] using h1
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg (ψ x)) hρ1) (norm_nonneg (g x))
    · have h1 : Tendsto (fun n : ℕ => ρ n x) atTop (𝓝 1) :=
        (sa12cc_rho_tendsto x).comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds |>.congr fun n => rfl)
      simpa [mul_assoc] using (h1.mul_const (ψ x)).const_mul (g x)
  have hint2 : Integrable (fun x => ‖f x‖ * (‖fderiv ℝ ψ x e‖ + M * ‖ψ x‖)) volume := by
    have h1 : Integrable (fun x => ‖f x‖ * ‖fderiv ℝ ψ x e‖) volume := (hf.integrable_mul hdψ).norm.congr
      (Eventually.of_forall fun x => by simp [norm_mul])
    have h2 : Integrable (fun x => ‖f x‖ * ‖ψ x‖) volume := (hf.integrable_mul hψ2).norm.congr
      (Eventually.of_forall fun x => by simp [norm_mul])
    have := h1.add (h2.const_mul M)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]; ring
  have hlim2 : Tendsto (fun n => ∫ x, f x * (ρ n x * fderiv ℝ ψ x e + fderiv ℝ (ρ n) x e * ψ x)) atTop
      (𝓝 (∫ x, f x * fderiv ℝ ψ x e)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖f x‖ * (‖fderiv ℝ ψ x e‖ + M * ‖ψ x‖))
      (fun n => ?_) hint2 (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · have hm1 : AEStronglyMeasurable (fun x => fderiv ℝ ψ x e) volume := hdψ.aestronglyMeasurable
      have hm2 : AEStronglyMeasurable (fun x => fderiv ℝ (ρ n) x e) volume :=
        (((hρsm n).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
      exact hf.aestronglyMeasurable.mul ((((hρsm n).continuous.aestronglyMeasurable).mul hm1).add (hm2.mul hψ2.aestronglyMeasurable))
    · have h0 := sa12cc_rho_nonneg ((n : ℝ) + 1) x
      have h1 := sa12cc_rho_le_one ((n : ℝ) + 1) x
      have hMn : M / ((n : ℝ) + 1) ≤ M := div_le_self hM0 (hn1 n)
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc ‖ρ n x * fderiv ℝ ψ x e + fderiv ℝ (ρ n) x e * ψ x‖
          ≤ ‖ρ n x * fderiv ℝ ψ x e‖ + ‖fderiv ℝ (ρ n) x e * ψ x‖ := norm_add_le _ _
        _ ≤ ‖fderiv ℝ ψ x e‖ + M * ‖ψ x‖ := by
          rw [norm_mul, norm_mul, Real.norm_eq_abs (ρ n x), abs_of_nonneg h0]
          exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) (by simpa [hρ] using h1))
            (mul_le_mul ((hρd n x).trans hMn) le_rfl (norm_nonneg _) hM0)
    · have h1 : Tendsto (fun n : ℕ => ρ n x) atTop (𝓝 1) :=
        (sa12cc_rho_tendsto x).comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds |>.congr fun n => rfl)
      have h2 : Tendsto (fun n : ℕ => fderiv ℝ (ρ n) x e) atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun n => hρd n x) ?_
        exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      have := (((h1.mul_const (fderiv ℝ ψ x e)).add (h2.mul_const (ψ x))).const_mul (f x))
      simpa using this
  have h3 := hlim1.congr hid
  have h4 := hlim2.neg
  exact tendsto_nhds_unique h3 h4

end HRS.MS.SA12DE7
