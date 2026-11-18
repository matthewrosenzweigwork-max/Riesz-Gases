import HRS.PDE.MovSXAux5
import HRS.Appendix.B15CAux1

/-!
# MOVSX Aux6: the regularised kernel `g_M` for the uniform pressure bound (packet `movT_source_exp_uniform`)

* `movsx_grad_gReg`: `∇g_M(z) = λ_M(z) ∇g(z)` for `z ≠ 0`, `λ_M(z) = 1 - smoothTransition(g(z) - M) ∈ [0,1]`, `λ_M = 0` on `{g ≥ M+1}`
  (chain rule through the truncation profile `trunc_M`).
* `movsx_commKernel_gReg`: hence `C^M`-kernel `= λ_M(x-y) ·` (the kernel with `∇g`); the envelope, measurability and
  symmetry of the regularised commutator kernel follow from those of `commKernel (periodicRieszGrad)`.
* `movsx_qM_props`: the decomposition `g_M = g_L + q^M - c_0` with `0 ≤ q^M ≤ q₀` for `M ≥ sup g_L`.
* `movsx_gReg_L1_le`: `‖g - g_M‖_{L¹} ≤ ‖g - g_0‖_{L¹}` for `M ≥ 0`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movsx_grad_gReg (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ) {z : Torus d}
    (hz : z ≠ 0) :
    Torus.grad (b15c_gReg d s M) z =
      (1 - Real.smoothTransition (periodicRiesz d s z - M)) • periodicRieszGrad d s z := by
  rw [← b15c_periodicRieszGrad_eq_grad hd hs0 hsd hz]
  unfold Torus.grad
  set y := Torus.rep z with hy
  have hmk : Torus.mk y = z := Torus.mk_rep z
  have hyne : Torus.mk y ≠ 0 := by rw [hmk]; exact hz
  have hopen : IsOpen {y' : Euc d | Torus.mk y' ≠ 0} :=
    (isClosed_singleton.preimage Torus.continuous_mk).isOpen_compl
  have hev : Torus.lift (b15c_gReg d s M) =ᶠ[𝓝 y]
      fun y' => b15c_trunc M (Torus.lift (periodicRiesz d s) y') := by
    filter_upwards [hopen.mem_nhds hyne] with y' hy'
    simp only [Torus.lift, Function.comp]
    exact b15c_gReg_of_ne s M hy'
  have hdiff : DifferentiableAt ℝ (Torus.lift (periodicRiesz d s)) y :=
    (b15c_contDiffAt_lift_periodicRiesz hd hs0 hsd hyne).differentiableAt (by simp)
  have hlift : Torus.lift (periodicRiesz d s) y = periodicRiesz d s z := by
    simp [Torus.lift, hmk]
  have hT : HasDerivAt (b15c_trunc M) (1 - Real.smoothTransition (periodicRiesz d s z - M))
      (Torus.lift (periodicRiesz d s) y) := by
    rw [hlift]
    have h1 := (b15c_phi_hasDerivAt (periodicRiesz d s z - M)).comp_sub_const (periodicRiesz d s z) M
    exact (hasDerivAt_id (periodicRiesz d s z)).sub h1 |>.congr_deriv (by simp)
  have hcomp := hT.comp_hasFDerivAt y hdiff.hasFDerivAt
  unfold gradient
  rw [hev.fderiv_eq]
  have h2 : fderiv ℝ (fun y' => b15c_trunc M (Torus.lift (periodicRiesz d s) y')) y =
      (1 - Real.smoothTransition (periodicRiesz d s z - M)) • fderiv ℝ (Torus.lift (periodicRiesz d s)) y :=
    hcomp.fderiv
  rw [h2, map_smul]

/-- The cutoff factor `λ_M(z) = 1 - smoothTransition (g z - M)`. -/
def movsx_lam (d : ℕ) (s M : ℝ) (z : Torus d) : ℝ := 1 - Real.smoothTransition (periodicRiesz d s z - M)

theorem movsx_lam_nonneg (s M : ℝ) (z : Torus d) : 0 ≤ movsx_lam d s M z := by
  unfold movsx_lam; linarith [Real.smoothTransition.le_one (periodicRiesz d s z - M)]

theorem movsx_lam_le_one (s M : ℝ) (z : Torus d) : movsx_lam d s M z ≤ 1 := by
  unfold movsx_lam; linarith [Real.smoothTransition.nonneg (periodicRiesz d s z - M)]

theorem movsx_lam_neg (s M : ℝ) (z : Torus d) : movsx_lam d s M (-z) = movsx_lam d s M z := by
  unfold movsx_lam; rw [periodicRiesz_neg]

theorem movsx_lam_eq_zero (s M : ℝ) {z : Torus d} (h : M + 1 ≤ periodicRiesz d s z) :
    movsx_lam d s M z = 0 := by
  unfold movsx_lam
  rw [Real.smoothTransition.one_of_one_le (by linarith)]; ring

theorem movsx_lam_measurable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ) :
    Measurable (movsx_lam d s M) := by
  unfold movsx_lam
  exact measurable_const.sub (Real.smoothTransition.continuous.measurable.comp
    ((CoercAux.measurable_periodicRiesz_one hd hs0 hsd).sub_const M))

theorem movsx_commKernel_gReg (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ)
    (v : Torus d → Euc d) (x y : Torus d) :
    commKernel (Torus.grad (b15c_gReg d s M)) v x y =
      movsx_lam d s M (x - y) * commKernel (periodicRieszGrad d s) v x y := by
  unfold commKernel
  by_cases hxy : x = y
  · simp [hxy]
  · simp only [hxy, if_false]
    rw [movsx_grad_gReg hd hs0 hsd M (sub_ne_zero.2 hxy), inner_smul_right]
    rfl

theorem movsx_lip_mono {L L' : ℝ} {v : Torus d → Euc d} (hv : IsLipschitzVF L v) (h : L ≤ L') :
    IsLipschitzVF L' v := fun x y =>
  (hv x y).trans (mul_le_mul_of_nonneg_right h (KernelGrad.tdist_nonneg x y))

open Classical in
/-- The positive part `q^M = g_M - g_L + c_0` of the regularised kernel, set to `0` on the diagonal. -/
def movsx_qM (d : ℕ) (s M cc : ℝ) (Λf : Finset (Lattice d)) (af : Lattice d → ℝ) (z : Torus d) : ℝ :=
  if z = 0 then 0 else b15c_gReg d s M z - ∑ k ∈ Λf, af k * Torus.cosMode k z + cc

theorem movsx_gReg_continuous (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ) :
    Continuous (b15c_gReg d s M) :=
  b15c_isSmooth_continuous (b15c_gReg_isSmooth hd hs0 hsd M)

theorem movsx_qM_props (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {Λf : Finset (Lattice d)}
    {af : Lattice d → ℝ} {q₀ : Torus d → ℝ} {cc Sa M : ℝ} (haf : ∀ k ∈ Λf, 0 ≤ af k)
    (hSa : Sa = ∑ k ∈ Λf, af k) (hq₀0 : ∀ x, 0 ≤ q₀ x) (hcc : 0 ≤ cc)
    (hsplit : ∀ x : Torus d, x ≠ 0 →
      periodicRiesz d s x = ∑ k ∈ Λf, af k * Torus.cosMode k x + q₀ x - cc) (hM : Sa ≤ M) :
    Measurable (movsx_qM d s M cc Λf af) ∧ (∀ x, 0 ≤ movsx_qM d s M cc Λf af x) ∧
      (∀ x, movsx_qM d s M cc Λf af x ≤ q₀ x) ∧
      (∀ x, movsx_qM d s M cc Λf af (-x) = movsx_qM d s M cc Λf af x) ∧
      (∀ x : Torus d, x ≠ 0 →
        b15c_gReg d s M x = ∑ k ∈ Λf, af k * Torus.cosMode k x + movsx_qM d s M cc Λf af x - cc) := by
  have hcosle : ∀ z : Torus d, |∑ k ∈ Λf, af k * Torus.cosMode k z| ≤ Sa := by
    intro z
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hSa]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [abs_mul, abs_of_nonneg (haf k hk)]
    exact mul_le_of_le_one_right (haf k hk) (abs_cosMode_le k z)
  have hcosm : Measurable (fun z : Torus d => ∑ k ∈ Λf, af k * Torus.cosMode k z) :=
    Finset.measurable_sum _ fun k _ => measurable_const.mul (Torus.continuous_cosMode k).measurable
  have hq : ∀ x : Torus d, x ≠ 0 → movsx_qM d s M cc Λf af x =
      b15c_gReg d s M x - ∑ k ∈ Λf, af k * Torus.cosMode k x + cc := by
    intro x hx; unfold movsx_qM; simp [hx]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold movsx_qM
    exact Measurable.ite (measurableSet_singleton (0 : Torus d)) measurable_const
      ((((movsx_gReg_continuous hd hs0 hsd M).measurable.sub hcosm).add measurable_const))
  · intro x
    by_cases hx : x = 0
    · simp [movsx_qM, hx]
    · rw [hq x hx]
      have h1 := b15c_min_le_trunc M (periodicRiesz d s x)
      rw [← b15c_gReg_of_ne s M hx] at h1
      have h2 := hsplit x hx
      have h3 := hq₀0 x
      have h4 := (abs_le.1 (hcosle x)).2
      have h5 : min (periodicRiesz d s x) M ≥ ∑ k ∈ Λf, af k * Torus.cosMode k x - cc :=
        le_min (by linarith) (by linarith)
      linarith
  · intro x
    by_cases hx : x = 0
    · simp [movsx_qM, hx, hq₀0 0]
    · rw [hq x hx]
      have h1 := b15c_gReg_le (d := d) s M hx
      have h2 := hsplit x hx
      linarith
  · intro x
    by_cases hx : x = 0
    · simp [movsx_qM, hx]
    · have hx' : -x ≠ 0 := neg_ne_zero.2 hx
      rw [hq x hx, hq (-x) hx', b15c_gReg_neg]
      congr 2
      exact Finset.sum_congr rfl fun k _ => by rw [StaticLimitAux.cosMode_neg_arg]
  · intro x hx
    rw [hq x hx]; ring

theorem movsx_gReg_L1_le (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {M : ℝ} (hM : 0 ≤ M) :
    Integrable (fun z : Torus d => |periodicRiesz d s z - b15c_gReg d s M z|) ∧
      ∫ z : Torus d, |periodicRiesz d s z - b15c_gReg d s M z| ≤
        ∫ z : Torus d, |periodicRiesz d s z - b15c_gReg d s 0 z| := by
  have hgi : Integrable (periodicRiesz d s) := CoercAux.integrable_periodicRiesz_one hd hs0 hsd
  have hint : ∀ M' : ℝ, Integrable (fun z : Torus d => |periodicRiesz d s z - b15c_gReg d s M' z|) := by
    intro M'
    have hc := movsx_gReg_continuous hd hs0 hsd M'
    have : Integrable (b15c_gReg d s M') :=
      hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    exact (hgi.sub this).abs
  refine ⟨hint M, ?_⟩
  refine integral_mono_ae (hint M) (hint 0) ?_
  have hae : ∀ᵐ z : Torus d, z ≠ 0 := by
    have := volume_singleton_torus hd (0 : Torus d)
    rw [ae_iff]; simpa using this
  filter_upwards [hae] with z hz
  have h1 := b15c_gReg_le (d := d) s M hz
  have h2 := b15c_gReg_mono (d := d) s z hM
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith : 0 ≤ periodicRiesz d s z - b15c_gReg d s 0 z)]
  linarith

end HRS

end
