import HRS.MS.GenPathAux22

/-!
# S5.6 packet P7a: classical adjoint solutions of oscillator data; line integral identity
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

theorem s56_osc_classical (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) b.T) (α : MultiIndex d) :
    IsClassicalAdjointW (S.coeff N) t (oscTestFun b.m α)
      (fun r => propagatorW (S.coeff N) r t (oscTestFun b.m α)) := by
  have hceil := HRS.MS.Go.s55f_ceil_half_le d
  have hJ : b.J = 4 * b.k + 4 * d + 40 := rfl
  set R : ℕ := b.k + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ with hR
  have hc1 : ⌈(1 + (((0 : ℕ) : ℝ))) / 2⌉₊ = 1 := by norm_num
  obtain ⟨C0, hC0, hosc⟩ := HRS.MS.Go.s55_osc_bounds hbv.hθ b.m R 0 1 (by norm_num) b.J (by omega)
    (by rw [hc1]; omega)
  obtain ⟨hsm, hul, -⟩ := hosc α
  have hφ : ContDiff ℝ (R : WithTop ℕ∞) (oscTestFun b.m α) := HRS.MS.Go.s55_cd_of_inf R hsm
  have hulfin : ulNormE R b.θ (oscTestFun b.m α) < ⊤ := lt_of_le_of_lt hul ENNReal.ofReal_lt_top
  obtain ⟨hex, -, -⟩ := S.adjoint N 0 t le_rfl ht.1 ht.2 _ hφ hulfin
  exact HRS.MS.Fcau.propagatorW_isClassical hex

/-- `∫_0^1 ∇h(y + θ(x-y))·(x-y) dθ = h(x) - h(y)` for a `C¹` function. -/
theorem s56_line_ftc {h : Euc d → ℝ} (hh : ContDiff ℝ 1 h) (x y : Euc d) :
    ∫ θ in Set.Icc (0 : ℝ) 1, ∑ a, (x - y) a * gradComp a h (y + θ • (x - y)) = h x - h y := by
  have hder : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => h (y + θ • (x - y)))
      (∑ a, (x - y) a * gradComp a h (y + θ • (x - y))) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ : ℝ => y + θ • (x - y)) (x - y) θ := by
      simpa using ((hasDerivAt_id θ).smul_const (x - y)).const_add y
    have h2 : HasFDerivAt h (fderiv ℝ h (y + θ • (x - y))) (y + θ • (x - y)) :=
      ((hh.differentiable one_ne_zero) _).hasFDerivAt
    have h3 := h2.comp_hasDerivAt θ h1
    refine HasDerivAt.congr_deriv h3 ?_
    have : fderiv ℝ h (y + θ • (x - y)) (x - y) =
        inner ℝ (gradient h (y + θ • (x - y))) (x - y) := by
      rw [gradient, InnerProductSpace.toDual_symm_apply]
    rw [this, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [gradComp, RCLike.inner_apply, conj_trivial]
  have hcont : Continuous fun θ : ℝ => ∑ a, (x - y) a * gradComp a h (y + θ • (x - y)) := by
    have : Continuous fun z : Euc d => fderiv ℝ h z := hh.continuous_fderiv one_ne_zero
    refine continuous_finsetSum _ fun a _ => continuous_const.mul ?_
    have hg : Continuous fun z : Euc d => gradient h z := by
      unfold gradient
      exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp this
    have : Continuous fun z : Euc d => gradComp a h z := by
      unfold gradComp
      exact (continuous_apply a).comp (PiLp.continuous_ofLp 2 _) |>.comp hg
    exact this.comp (continuous_const.add (continuous_id.smul continuous_const))
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hder θ) (hcont.intervalIntegrable _ _)]
  simp

end HRS.MS.GenPath
