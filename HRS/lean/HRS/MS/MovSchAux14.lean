import HRS.MS.MovSchAux13

/-!
# S64 (S6.9), part 9: the forward Kolmogorov operator applied to a translate of the canonical density

Namespace `HRS.MS.MovSch`, prefix `s64_`.  `s64_Qc = Z_can⁻¹ e^{-βH_N}`.  For `f(Y) = Qc(Y - a)` and a non-collision
`Z = X - a`: `movFP f X = ∑_{i,k} (q a_k) (-β drift_{ik}(Z) Qc(Z))` (`s64_movFP_Qc`), by the one-dimensional identity
`β⁻¹ φ'' + (φ (Dr + c))' = c φ'` for `φ' = -β Dr φ` (`s64_1d`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovSch

open HRS.Whole
open HRS (Euc)

variable {d N : ℕ}

/-- The canonical Gibbs density `Z_can⁻¹ e^{-βH_N}`. -/
def s64_Qc (d : ℕ) (s q β : ℝ) (N : ℕ) (W : EucConfig d N) : ℝ :=
  (HRS.Whole.canonicalPartition (rieszKernel d s) (confinement q) N β)⁻¹ *
    Real.exp (-β * HRS.Whole.canonicalHamiltonian (rieszKernel d s) (confinement q) W)

lemma s64_1d {β : ℝ} (hβ : β ≠ 0) {φ Dr : ℝ → ℝ} (c : ℝ)
    (hφ : ∀ᶠ τ in 𝓝 (0 : ℝ), HasDerivAt φ (-β * Dr τ * φ τ) τ) (hDr : DifferentiableAt ℝ Dr 0) :
    β⁻¹ * deriv (deriv φ) 0 + deriv (fun τ => φ τ * (Dr τ + c)) 0 = c * deriv φ 0 := by
  have h0 : HasDerivAt φ (-β * Dr 0 * φ 0) 0 := hφ.self_of_nhds
  have hdd : deriv φ =ᶠ[𝓝 0] fun τ => -β * Dr τ * φ τ := by
    filter_upwards [hφ] with τ hτ using hτ.deriv
  have hprod : HasDerivAt (fun τ => -β * Dr τ * φ τ)
      (-β * deriv Dr 0 * φ 0 + -β * Dr 0 * (-β * Dr 0 * φ 0)) 0 := by
    have h1 : HasDerivAt (fun τ => -β * Dr τ) (-β * deriv Dr 0) 0 := hDr.hasDerivAt.const_mul (-β)
    exact h1.mul h0
  have hprod2 : HasDerivAt (fun τ => φ τ * (Dr τ + c))
      ((-β * Dr 0 * φ 0) * (Dr 0 + c) + φ 0 * deriv Dr 0) 0 := by
    have h1 : HasDerivAt (fun τ => Dr τ + c) (deriv Dr 0) 0 := hDr.hasDerivAt.add_const c
    exact h0.mul h1
  rw [hdd.deriv_eq, hprod.deriv, hprod2.deriv, h0.deriv]
  field_simp
  ring

lemma s64_NC_eventually {Z : EucConfig d N} (hZ : s64_NC Z) (i : Fin N) (k : Fin d) :
    ∀ᶠ τ in 𝓝 (0 : ℝ), s64_NC (s64_ell Z i k τ) := by
  have : ∀ a b : Fin N, ∀ᶠ τ in 𝓝 (0 : ℝ), a ≠ b → s64_ell Z i k τ a ≠ s64_ell Z i k τ b := by
    intro a b
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall fun τ h => absurd hab h
    · have hc : Continuous (fun τ : ℝ => s64_ell Z i k τ a - s64_ell Z i k τ b) := by
        have : (fun τ : ℝ => s64_ell Z i k τ a - s64_ell Z i k τ b) = fun τ : ℝ =>
            (Z a - Z b) + τ • ((if a = i then EuclideanSpace.single k (1 : ℝ) else 0) -
              (if b = i then EuclideanSpace.single k (1 : ℝ) else 0)) := by
          funext τ; rw [s64_ell_apply, s64_ell_apply, smul_sub]; abel
        rw [this]; fun_prop
      have h0 : (fun τ : ℝ => s64_ell Z i k τ a - s64_ell Z i k τ b) 0 ≠ 0 := by
        simp only [s64_ell_zero]; exact sub_ne_zero.2 (hZ a b hab)
      filter_upwards [hc.continuousAt.eventually_ne h0] with τ hτ _ h
      exact hτ (sub_eq_zero.2 h)
  have h2 := Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => this a b
  filter_upwards [h2] with τ hτ a b hab using hτ a b hab

lemma s64_drift_add (s q : ℝ) (i : Fin N) (k : Fin d) (Y : EucConfig d N) (a : Euc d) :
    s64_drift d s q N i k (fun j => Y j + a) = s64_drift d s q N i k Y + q * a k := by
  unfold s64_drift
  simp only [add_sub_add_right_eq_sub, PiLp.add_apply]
  ring

lemma s64_ell_shift (X : EucConfig d N) (a : Euc d) (i : Fin N) (k : Fin d) (τ : ℝ) :
    s64_ell X i k τ = fun j => s64_ell (fun j => X j - a) i k τ j + a := by
  funext j
  rw [s64_ell_apply, s64_ell_apply]
  abel

lemma s64_Dr_diff (s q : ℝ) {Z : EucConfig d N} (hZ : s64_NC Z) (i : Fin N) (k : Fin d) :
    DifferentiableAt ℝ (fun τ : ℝ => s64_drift d s q N i k (s64_ell Z i k τ)) 0 := by
  unfold s64_drift
  refine DifferentiableAt.add ?_ ?_
  · have : (fun τ : ℝ => q * s64_ell Z i k τ i k) = fun τ : ℝ => q * (Z i k + τ) := by
      funext τ; rw [s64_ell_apply]; simp
    rw [this]
    fun_prop
  · refine DifferentiableAt.const_mul (DifferentiableAt.fun_sum fun j hj => ?_) _
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hz : Z i - Z j ≠ 0 := sub_ne_zero.2 (hZ i j hji.symm)
    have hline : DifferentiableAt ℝ (fun τ : ℝ => s64_ell Z i k τ i - s64_ell Z i k τ j) 0 := by
      have : (fun τ : ℝ => s64_ell Z i k τ i - s64_ell Z i k τ j) =
          fun τ : ℝ => (Z i - Z j) + τ • EuclideanSpace.single k (1 : ℝ) := by
        funext τ; rw [s64_ell_apply, s64_ell_apply]; simp [hji]; abel
      rw [this]; fun_prop
    have hG : DifferentiableAt ℝ (fun y : Euc d => rieszKernelGrad d s y k)
        ((fun τ : ℝ => s64_ell Z i k τ i - s64_ell Z i k τ j) 0) := by
      simp only [s64_ell_zero]; exact s64_G_diff s k hz
    exact hG.comp (0 : ℝ) hline

end HRS.MS.MovSch

end
