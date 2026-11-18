import HRS.MS.SA16TLm1
import HRS.MS.SA16TMo3

/-!
# S.A.16 (SA16T) Lm2: pointwise convergence and a uniform bound for the nonlocal test functions of the mollified densities

`sa16t_nl_tendsto`: `nonlocalTestRd (D.coeff (ρ_n ⋆ μ)) τ' ψ x → nonlocalTestRd (D.coeff μ) τ' ψ x` for `μ τ' ∈ C^1`.
`sa16t_nl_bound`: `|nonlocalTestRd (D.coeff (ρ_n ⋆ μ)) τ' ψ x| ≤ K A (1+|x|)^{-(d+3)} (1+|x|)` uniformly in `n`, when
`‖D^j μ τ'‖ ≤ A (1+|y|)^{-(d+3)}` for `j ≤ 1` (so `K A w(x)(1+|x|) ∈ L^q`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16P

section Lm2
variable {d : ℕ}

lemma sa16t_D1_eq_pd (j : Fin d) (f : Euc d → ℝ) (x : Euc d) :
    HRS.MS.UniqT3.D1 j f x = partialDeriv (fun _ : Fin 1 => j) f x := by
  unfold HRS.MS.UniqT3.D1 partialDeriv
  rw [iteratedFDeriv_one_apply]

lemma sa16t_D1_tendsto {g : Euc d → ℝ} (hg : ContDiff ℝ 1 g) (j : Fin d) (x : Euc d) :
    Tendsto (fun n => HRS.MS.UniqT3.D1 j (sa16j_conv (sa16y_rho d n) g) x) atTop
      (𝓝 (HRS.MS.UniqT3.D1 j g x)) := by
  have hg' : ContDiff ℝ ((1 + 0 : ℕ) : WithTop ℕ∞) g := by simpa using hg
  have hpc : Continuous (partialDeriv (fun _ : Fin 1 => j) g) := (sa16y_pd_contDiffN hg' _).continuous
  simp only [sa16t_D1_eq_pd]
  refine (sa16y_mollify_tendsto hpc x).congr' (Eventually.of_forall fun n => ?_)
  have hsupp : ∀ z, 1 / ((n : ℝ) + 1) < ‖z‖ → sa16y_rho d n z = 0 := fun z hz => sa16y_rho_supp n z hz
  have h1 := sa16y_conv_pdN hsupp (by positivity) (sa16y_rho_integrable n) 1 0 (fun _ : Fin 1 => j) g hg'
  exact (congrFun h1 x).symm

theorem sa16t_nl_tendsto (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ)
    {D : WholeDyn d} (hDs : D.s = s) {μ : ℝ → Euc d → ℝ} {τ' : ℝ} (hμ : ContDiff ℝ 1 (μ τ')) (x : Euc d) :
    Tendsto (fun n => nonlocalTestRd (D.coeff (sa16t_mu d n μ)) τ' ψ x) atTop
      (𝓝 (nonlocalTestRd (D.coeff μ) τ' ψ x)) := by
  obtain ⟨CH, -, -, -, hrep⟩ := sa16t_nl_rep hd s hs0 hsd hψ
  have hsm : ∀ n, ContDiff ℝ 1 ((D.coeff (sa16t_mu d n μ)).ρ τ') := fun n =>
    (contDiff_infty.1 (sa16y_mollify_smooth n hμ.continuous)) 1
  have e1 : ∀ n, nonlocalTestRd (D.coeff (sa16t_mu d n μ)) τ' ψ x = ∑ i : Fin d, ∑ j : Fin d, D.M j i *
      (HRS.MS.UniqT3.D1 j (sa16j_conv (sa16y_rho d n) (μ τ')) x * kernelConvDeriv d s i ψ x +
        sa16j_conv (sa16y_rho d n) (μ τ') x * HRS.MS.UniqT3.D1 j (kernelConvDeriv d s i ψ) x) :=
    fun n => hrep _ τ' hDs (hsm n) x
  have e2 := hrep (D.coeff μ) τ' hDs hμ x
  rw [e2]
  simp_rw [e1]
  refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => ?_
  refine Tendsto.const_mul _ ?_
  exact ((sa16t_D1_tendsto hμ j x).mul_const _).add ((sa16y_mollify_tendsto hμ.continuous x).mul_const _)

theorem sa16t_nl_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ)
    (MB : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (D : WholeDyn d), D.s = s → (∀ i j, |D.M i j| ≤ MB) →
      ∀ (μ : ℝ → Euc d → ℝ) (τ' : ℝ) (A : ℝ), ContDiff ℝ 1 (μ τ') →
      (∀ j ≤ 1, ∀ y, ‖iteratedFDeriv ℝ j (μ τ') y‖ ≤ A * sa16p_w d y) → ∀ n x,
        |nonlocalTestRd (D.coeff (sa16t_mu d n μ)) τ' ψ x| ≤ K * A * (sa16p_w d x * (1 + ‖x‖)) := by
  obtain ⟨CH, hCH0, hH, hHH, hrep⟩ := sa16t_nl_rep hd s hs0 hsd hψ
  refine ⟨(d : ℝ) * d * (2 * max MB 0 * (((d : ℝ) + 1) ^ 1 * 2 ^ ((d : ℝ) + 3)) * CH), by positivity,
    fun D hDs hM μ τ' A hμ1 hdec n x => ?_⟩
  have hA : 0 ≤ A := sa16t_w_nonneg_aux (ρ := iteratedFDeriv ℝ 0 (μ τ')) (hdec 0 (Nat.zero_le _) 0)
  have hsm : ContDiff ℝ 1 ((D.coeff (sa16t_mu d n μ)).ρ τ') :=
    (contDiff_infty.1 (sa16y_mollify_smooth n hμ1.continuous)) 1
  rw [hrep _ τ' hDs hsm x]
  set ρn : Euc d → ℝ := sa16j_conv (sa16y_rho d n) (μ τ') with hρn
  have hd1 : ∀ j ≤ 1, ‖iteratedFDeriv ℝ j ρn x‖ ≤ ((((d : ℝ) + 1) ^ 1) * (2 ^ ((d : ℝ) + 3) * A)) * sa16p_w d x :=
    fun j hj => sa16t_conv_decay_unif hμ1 hdec n hj x
  set A1 : ℝ := ((((d : ℝ) + 1) ^ 1) * (2 ^ ((d : ℝ) + 3) * A)) * sa16p_w d x with hA1
  have hA10 : 0 ≤ A1 := by have := sa16p_w_pos (d := d) x; rw [hA1]; positivity
  have hρ0 : |ρn x| ≤ A1 := by
    have := hd1 0 (Nat.zero_le _)
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hρ1 : ∀ j : Fin d, |HRS.MS.UniqT3.D1 j ρn x| ≤ A1 := fun j =>
    (HRS.MS.UniqN2b.n2b_D1_le j ρn x).trans (by rw [Phase2SA16P.sa16p_norm_fderiv_eq]; exact hd1 1 le_rfl)
  have hterm : ∀ i j : Fin d, |D.M j i * (HRS.MS.UniqT3.D1 j ρn x * kernelConvDeriv d s i ψ x + ρn x *
      HRS.MS.UniqT3.D1 j (kernelConvDeriv d s i ψ) x)| ≤ 2 * max MB 0 * A1 * (CH * (1 + ‖x‖)) := by
    intro i j
    rw [abs_mul]
    have h1 : |HRS.MS.UniqT3.D1 j ρn x * kernelConvDeriv d s i ψ x + ρn x *
        HRS.MS.UniqT3.D1 j (kernelConvDeriv d s i ψ) x| ≤ 2 * A1 * (CH * (1 + ‖x‖)) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have hc : 0 ≤ CH * (1 + ‖x‖) := by positivity
      nlinarith [mul_le_mul (hρ1 j) (hH i x) (abs_nonneg _) hA10, mul_le_mul hρ0 (hHH i j x) (abs_nonneg _) hA10]
    calc |D.M j i| * |_| ≤ max MB 0 * (2 * A1 * (CH * (1 + ‖x‖))) :=
          mul_le_mul ((hM j i).trans (le_max_left _ _)) h1 (abs_nonneg _) (le_max_right _ _)
      _ = _ := by ring
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i : Fin d, |∑ j : Fin d, D.M j i * (HRS.MS.UniqT3.D1 j ρn x * kernelConvDeriv d s i ψ x + ρn x *
          HRS.MS.UniqT3.D1 j (kernelConvDeriv d s i ψ) x)|
      ≤ ∑ i : Fin d, ∑ j : Fin d, 2 * max MB 0 * A1 * (CH * (1 + ‖x‖)) :=
        Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hterm i j)
    _ = (d : ℝ) * d * (2 * max MB 0 * A1 * (CH * (1 + ‖x‖))) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ = _ := by rw [hA1]; ring

end Lm2

end HRS.Whole.AppendixA.Phase2SA16R
