import HRS.MC.E213U16c

/-!
# Packet e213u16, file d: the noise coordinates `N(t,φ) = η^t(φ) - η^0(U^{0,t}φ)` of the limit field

* `Nrv`, `covK`: definitions;
* `u16_gauss_part`: `gaussian_part` for the limit field `η` (with `η^0` in place of the abstract initial value);
* `u16_psd`: the covariance matrices are positive semidefinite (Gram matrices of `canonFut _ 0`);
* `u16_N_cov`: second moments of the noise coordinates.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Q HRS.MC.E213U13 HRS.MC.E213Plan

variable {d : ℕ}

/-- The evaluation functional at a smooth test function, as an element of the dual of `E_r`. -/
def u16_ev (r : ℝ) {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) : StrongDual ℝ (NegSobolev d r) :=
  e213qEvalCLM r (HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hψ r)

theorem u16_ev_apply (r : ℝ) {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) (F : NegSobolev d r) :
    u16_ev r hψ F = NegSobolev.eval F ψ :=
  e213qEvalCLM_apply r _ F

/-- The covariance kernel of the noise coordinates (`gaussian_part`, `IsFutureGaussian` with `u = 0`). -/
def covK (D : DynData d) (ρ : ℝ → Torus d → ℝ) (ta tb : ℝ) (φa φb : Torus d → ℝ) : ℝ :=
  2 * D.invβ * ∫ r in Set.Icc 0 (min ta tb), ∫ x,
    inner ℝ (Torus.grad (propagator D ρ r ta φa) x) (Torus.grad (propagator D ρ r tb φb) x) * ρ r x

section Noise

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

/-- The noise coordinate `N(t,φ) = η^t(φ) - η^0(U^{0,t}φ)`. -/
def Nrv (t : ℝ) (φ : Torus d → ℝ) (ω : gd.Ω₀) : ℝ :=
  NegSobolev.eval (gd.η t ω) φ - NegSobolev.eval (gd.η 0 ω) (propagator S.dyn S.ρ 0 t φ)

theorem u16_prop_smooth {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) :
    Torus.IsSmooth (propagator S.dyn S.ρ r t φ) :=
  (HRS.MC.L2C0.l2c0_proof (HRS.MC.E213A.regimeOfPrepared S β₀ hE) φ hφ r t hr hrt).1

theorem u16_eta_meas (t : ℝ) : Measurable (gd.η t) := by
  obtain ⟨Y₀, -, hlin⟩ := gd.limit
  exact (hlin t).meas t

theorem u16_eval_meas (t : ℝ) {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    Measurable fun ω => NegSobolev.eval (gd.η t ω) ψ := by
  have := (u16_ev (rLvl d) hψ).continuous.measurable.comp (u16_eta_meas gd t)
  simpa [Function.comp_def, u16_ev_apply] using this

theorem u16_Nrv_meas {t : ℝ} (ht : 0 ≤ t) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Measurable (Nrv gd t φ) :=
  (u16_eval_meas gd t hφ).sub (u16_eval_meas gd 0 (u16_prop_smooth hE hφ le_rfl ht))

/-- `gaussian_part` for the limit field. -/
theorem u16_gauss_part (H : ℝ) (hH : 0 ≤ H) {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ)
    (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) H) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    IndepFun (fun ω => (WithLp.toLp 2 fun a => Nrv gd (ts a) (φ a) ω : EuclideanSpace ℝ (Fin p))) (gd.η 0) gd.P₀ ∧
    gd.P₀.map (fun ω => (WithLp.toLp 2 fun a => Nrv gd (ts a) (φ a) ω : EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (Matrix.of fun a b => covK S.dyn S.ρ (ts a) (ts b) (φ a) (φ b)) := by
  obtain ⟨Y₀, -, hlin⟩ := gd.limit
  obtain ⟨hind, hlaw⟩ := (hlin H).gaussian_part p ts φ hts hφ
  have hae : gd.η 0 =ᵐ[gd.P₀] Y₀ := (hlin 0).init
  have hGae : (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (gd.η (ts a) ω) (φ a) -
        NegSobolev.eval (Y₀ ω) (propagator S.dyn S.ρ 0 (ts a) (φ a)) : EuclideanSpace ℝ (Fin p))) =ᵐ[gd.P₀]
      (fun ω => (WithLp.toLp 2 fun a => Nrv gd (ts a) (φ a) ω : EuclideanSpace ℝ (Fin p))) := by
    filter_upwards [hae] with ω hω
    simp only [Nrv, hω]
  refine ⟨hind.congr hGae hae.symm, ?_⟩
  rw [← Measure.map_congr hGae]
  exact hlaw


/-- The covariance matrices of the noise coordinates are positive semidefinite (Gram matrices under `canonFut _ 0`). -/
theorem u16_psd {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m) (H : ℝ) (hH : 0 < H) {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ)
    (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) H) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    (Matrix.of fun a b => covK S.dyn S.ρ (ts a) (ts b) (φ a) (φ b)).PosSemidef := by
  obtain ⟨hfg, hprob⟩ := HRS.MC.E213U5.e213u5_canonFut_spec hE H hH 0 ⟨le_rfl, hH.le⟩
  haveI := hprob
  haveI : IsGaussian (canonFut hE H 0) := hfg.1.1
  choose ℓ hℓ using fun a : Fin p =>
    pathObservation_bounded m H ⟨ts a, hts a⟩ (φ a) (HRS.A33.a33_memSob m (hφ a))
  have hcov : ∀ a b, covK S.dyn S.ρ (ts a) (ts b) (φ a) (φ b) = ∫ z, ℓ a z * ℓ b z ∂(canonFut hE H 0) := by
    intro a b
    have := hfg.2 (ts a) (ts b) (φ a) (φ b) (hφ a) (hφ b) (hts a) (hts b)
    simp only [(hℓ a).1, (hℓ b).1, ← HRS.MC.E213U4.u4_pathAt_coe] at this ⊢
    exact this.symm
  have hmem : ∀ a, MemLp (fun z => ℓ a z) 2 (canonFut hE H 0) := fun a =>
    IsGaussian.memLp_dual (canonFut hE H 0) (ℓ a) 2 (by simp)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    rw [hcov, hcov]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)
  · have h2 : 0 ≤ ∫ z, (∑ a, x a * ℓ a z) ^ 2 ∂(canonFut hE H 0) := integral_nonneg fun z => sq_nonneg _
    have hint : ∀ a b, Integrable (fun z => x a * x b * (ℓ a z * ℓ b z)) (canonFut hE H 0) := fun a b =>
      ((hmem a).integrable_mul (hmem b)).const_mul _
    have h3 : ∫ z, (∑ a, x a * ℓ a z) ^ 2 ∂(canonFut hE H 0) = star x ⬝ᵥ ((Matrix.of fun a b =>
        covK S.dyn S.ρ (ts a) (ts b) (φ a) (φ b)) *ᵥ x) := by
      have e1 : ∀ z, (∑ a, x a * ℓ a z) ^ 2 = ∑ a, ∑ b, x a * x b * (ℓ a z * ℓ b z) := by
        intro z
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      simp_rw [e1]
      rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ fun b _ => hint a b)]
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, star_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finset_sum _ (fun b _ => hint a b)]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_const_mul, hcov a b]
      ring
    rw [← h3]; exact h2

/-- Mean and second moments of the noise coordinates. -/
theorem u16_N_cov {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m) (H : ℝ) (hH : 0 < H) {p : ℕ} (ts : Fin p → ℝ)
    (φ : Fin p → Torus d → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) H) (hφ : ∀ a, Torus.IsSmooth (φ a))
    (a b : Fin p) :
    ∫ ω, Nrv gd (ts a) (φ a) ω ∂gd.P₀ = 0 ∧
    ∫ ω, Nrv gd (ts a) (φ a) ω * Nrv gd (ts b) (φ b) ω ∂gd.P₀ =
      covK S.dyn S.ρ (ts a) (ts b) (φ a) (φ b) := by
  obtain ⟨-, hlaw⟩ := u16_gauss_part gd H hH.le ts φ hts hφ
  have hPSD := u16_psd hE H hH ts φ hts hφ
  set vec : gd.Ω₀ → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a => Nrv gd (ts a) (φ a) ω with hvec
  have hvm : Measurable vec := by
    refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun a => ?_)
    exact u16_Nrv_meas gd (hts a).1 (hφ a)
  set Mg := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p))
    (Matrix.of fun a b => covK S.dyn S.ρ (ts a) (ts b) (φ a) (φ b)) with hMg
  have hmean : ∀ c : Fin p, ∫ x, x c ∂Mg = 0 := by
    intro c
    have h := (measurePreserving_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin p))) hPSD
      (i := c)).map_eq
    have h2 : ∫ y, y ∂(Mg.map (fun x => x c)) = ∫ x, x c ∂Mg :=
      integral_map (by fun_prop) aestronglyMeasurable_id
    rw [← h2, h, integral_id_gaussianReal]
    simp
  have hI : ∀ f : EuclideanSpace ℝ (Fin p) → ℝ, Measurable f → ∫ ω, f (vec ω) ∂gd.P₀ = ∫ x, f x ∂Mg := by
    intro f hf
    rw [← hlaw, integral_map hvm.aemeasurable hf.aestronglyMeasurable]
  have e1 : ∫ ω, Nrv gd (ts a) (φ a) ω ∂gd.P₀ = ∫ x, x a ∂Mg := hI (fun x => x a) (by fun_prop)
  refine ⟨by rw [e1, hmean], ?_⟩
  have e2 : ∫ ω, Nrv gd (ts a) (φ a) ω * Nrv gd (ts b) (φ b) ω ∂gd.P₀ = ∫ x, x a * x b ∂Mg :=
    hI (fun x => x a * x b) (by fun_prop)
  rw [e2]
  have hc := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin p))) hPSD a b
  rw [covariance, ← hMg] at hc
  simp only [integral_id_multivariateGaussian] at hc
  have hm : ∀ c : Fin p, ∫ x, (fun x : EuclideanSpace ℝ (Fin p) => x c) x ∂Mg = 0 := hmean
  simpa [hm] using hc

end Noise

end HRS.MC.E213U16

end
