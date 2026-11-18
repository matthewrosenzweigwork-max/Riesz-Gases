import HRS.PDE.MovCAux5
import HRS.Energy.KIDFinal
import HRS.Stochastic.Bridge

/-!
# G336C1, helper file 1: the truncated kernels `g_M = b15c_gReg` as a `GoodKernel` family

For the zero-temperature Grönwall (Prop 3.36 (C1)), the smooth even kernels are the truncations
`g_M := b15c_gReg d s M` (smooth, even, `= g` where `g ≤ M`).  Here: `∇g_M = (1 - smoothTransition(g - M)) ∇g`
off `0` (so `‖∇g_M‖ ≤ ‖∇g‖`), hence `∇g_M` is a `GoodKernel` with the constant of `∇g`, uniformly in `M`,
and `∇g_M → ∇g` pointwise off `0` along `M = n`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

theorem g336c1_trunc_hasDerivAt (M u : ℝ) :
    HasDerivAt (b15c_trunc M) (1 - Real.smoothTransition (u - M)) u := by
  have h1 : HasDerivAt (fun v : ℝ => v - M) 1 u := (hasDerivAt_id' u).sub_const M
  have h2 : HasDerivAt (fun v : ℝ => b15c_phi (v - M)) (Real.smoothTransition (u - M) * 1) u :=
    HasDerivAt.comp (h₂ := b15c_phi) u (b15c_phi_hasDerivAt (u - M)) h1
  have h3 : HasDerivAt (fun v : ℝ => v - b15c_phi (v - M)) (1 - Real.smoothTransition (u - M) * 1) u :=
    (hasDerivAt_id' u).sub h2
  rw [mul_one] at h3
  exact h3

theorem g336c1_grad_gReg_eq_smul (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ)
    {z : Torus d} (hz : z ≠ 0) :
    Torus.grad (b15c_gReg d s M) z =
      (1 - Real.smoothTransition (periodicRiesz d s z - M)) • Torus.grad (periodicRiesz d s) z := by
  have hy : Torus.mk (Torus.rep z) ≠ 0 := by rw [Torus.mk_rep]; exact hz
  have hdiff : DifferentiableAt ℝ (Torus.lift (periodicRiesz d s)) (Torus.rep z) :=
    (b15c_contDiffAt_lift_periodicRiesz hd hs0 hsd hy).differentiableAt (by simp)
  have hF := hdiff.hasFDerivAt
  have hcomp := (g336c1_trunc_hasDerivAt M (Torus.lift (periodicRiesz d s) (Torus.rep z))).comp_hasFDerivAt
    (Torus.rep z) hF
  have hopen : IsOpen {y : Euc d | Torus.mk y ≠ 0} :=
    isOpen_compl_singleton.preimage Torus.continuous_mk
  have hev : (b15c_trunc M ∘ Torus.lift (periodicRiesz d s)) =ᶠ[𝓝 (Torus.rep z)]
      Torus.lift (b15c_gReg d s M) := by
    filter_upwards [hopen.mem_nhds hy] with y' hy'
    show b15c_trunc M (periodicRiesz d s (Torus.mk y')) = b15c_gReg d s M (Torus.mk y')
    rw [b15c_gReg_of_ne s M hy']
  have hG := hcomp.congr_of_eventuallyEq hev.symm
  unfold Torus.grad gradient
  rw [hG.fderiv, map_smul]
  have : Torus.lift (periodicRiesz d s) (Torus.rep z) = periodicRiesz d s z := by
    simp [Torus.lift, Torus.mk_rep]
  rw [this]

theorem g336c1_norm_grad_gReg_le (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ)
    {z : Torus d} (hz : z ≠ 0) :
    ‖Torus.grad (b15c_gReg d s M) z‖ ≤ ‖periodicRieszGrad d s z‖ := by
  rw [g336c1_grad_gReg_eq_smul hd hs0 hsd M hz, b15c_periodicRieszGrad_eq_grad hd hs0 hsd hz |>.symm,
    norm_smul, Real.norm_eq_abs]
  have h0 := Real.smoothTransition.nonneg (periodicRiesz d s z - M)
  have h1 := Real.smoothTransition.le_one (periodicRiesz d s z - M)
  rw [abs_of_nonneg (by linarith)]
  have : 1 - Real.smoothTransition (periodicRiesz d s z - M) ≤ 1 := by linarith
  exact mul_le_of_le_one_left (norm_nonneg _) this

theorem g336c1_goodKernel_grad_gReg (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {C : ℝ}
    (hG : KernelGrad.GoodKernel d s C (periodicRieszGrad d s)) (M : ℝ) :
    KernelGrad.GoodKernel d s C (Torus.grad (b15c_gReg d s M)) := by
  have hsm := b15c_gReg_isSmooth hd hs0 hsd M
  have h1 := HRS.KID.isCk1_of_smooth hsm
  have hev : ∀ x, b15c_gReg d s M (-x) = b15c_gReg d s M x := fun x => b15c_gReg_neg s M x
  refine ⟨hG.pos, hs0, hsd, hG.hC0, (HRS.PDE.MFLinear.continuous_grad h1).measurable,
    fun z => HRS.KID.grad_odd h1 hev z, fun z hz => ?_⟩
  exact (g336c1_norm_grad_gReg_le hd hs0 hsd M hz).trans (hG.bound z hz)

theorem g336c1_grad_gReg_tendsto (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {z : Torus d} (hz : z ≠ 0) :
    Tendsto (fun n : ℕ => Torus.grad (b15c_gReg d s (n : ℝ)) z) atTop
      (𝓝 (periodicRieszGrad d s z)) := by
  obtain ⟨M₀, hM₀⟩ := b15c_grad_gReg_eq hd hs0 hsd (r := Torus.tdist z 0)
    (Torus.tdist_pos_of_ne hz)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈M₀⌉₊] with n hn
  exact (hM₀ n (le_trans (Nat.le_ceil _) (by exact_mod_cast hn)) z le_rfl).symm

end HRS
