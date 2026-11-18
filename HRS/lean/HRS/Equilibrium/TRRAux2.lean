/-
# TRR helper 2: `N`, `Λ` on `C(T^d, ℝ)` — smoothness and derivative formulas.
-/
import HRS.Equilibrium.TRRAux1

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.TRR

variable {d : ℕ}

/-- `C^∞` order. -/
abbrev InfOrd : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Mean value as a continuous linear functional. -/
def intC : Cb d →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun w => ∫ x, w x
      map_add' := fun v w => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (v.continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)) (w.continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c v => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
    1 (fun w => by
      have h := norm_integral_le_of_norm_le_const (μ := (volume : Measure (Torus d)))
        (f := fun x => w x) (C := ‖w‖)
        (Filter.Eventually.of_forall fun x => w.norm_coe_le_norm x)
      simpa using h)

lemma intC_apply (w : Cb d) : intC w = ∫ x, w x := rfl

/-- pointwise exponential -/
def expC (w : Cb d) : Cb d := NormedSpace.exp w

lemma expC_apply (w : Cb d) (x : Torus d) : expC w x = Real.exp (w x) := by
  have h := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℝ ℝ x : Cb d →ₐ[ℝ] ℝ)
    (continuous_eval_const x) w
  simpa [expC, Real.exp_eq_exp_ℝ] using h

lemma contDiff_expC {n : WithTop ℕ∞} : ContDiff ℝ n (expC : Cb d → Cb d) :=
  contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt

lemma hasFDerivAt_expC (w : Cb d) :
    HasFDerivAt (expC : Cb d → Cb d) (expC w • (1 : Cb d →L[ℝ] Cb d)) w :=
  hasFDerivAt_exp


/-- normalising constant -/
def Zc (w : Cb d) : ℝ := intC (expC w)

lemma Zc_pos (w : Cb d) : 0 < Zc w := by
  unfold Zc
  rw [intC_apply]
  simp only [expC_apply]
  exact integral_exp_pos (by
    exact (Real.continuous_exp.comp w.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

/-- the density `exp w / ∫ exp w` -/
def Nc (w : Cb d) : Cb d := (Zc w)⁻¹ • expC w

lemma Nc_apply (w : Cb d) (x : Torus d) : Nc w x = Real.exp (w x) / Zc w := by
  simp [Nc, expC_apply, div_eq_inv_mul]

lemma Nc_pos (w : Cb d) (x : Torus d) : 0 < Nc w x := by
  rw [Nc_apply]; exact div_pos (Real.exp_pos _) (Zc_pos w)

lemma intC_Nc (w : Cb d) : intC (Nc w) = 1 := by
  unfold Nc
  rw [map_smul, smul_eq_mul]
  exact inv_mul_cancel₀ (Zc_pos w).ne'

lemma contDiff_Zc {n : WithTop ℕ∞} : ContDiff ℝ n (Zc : Cb d → ℝ) :=
  intC.contDiff.comp contDiff_expC

lemma contDiff_Nc {n : WithTop ℕ∞} : ContDiff ℝ n (Nc : Cb d → Cb d) := by
  refine contDiff_iff_contDiffAt.2 fun w => ?_
  exact ((contDiff_Zc.contDiffAt).inv (Zc_pos w).ne').smul contDiff_expC.contDiffAt

/-- derivative of `Nc` at `w`: `h ↦ ρ h - (∫ρ h) ρ`. -/
def Nder (w : Cb d) : Cb d →L[ℝ] Cb d :=
  ContinuousLinearMap.mul ℝ (Cb d) (Nc w) -
    (intC.comp (ContinuousLinearMap.mul ℝ (Cb d) (Nc w))).smulRight (Nc w)

lemma Nder_apply (w h : Cb d) : Nder w h = Nc w * h - intC (Nc w * h) • Nc w := rfl

lemma hasFDerivAt_Nc (w : Cb d) : HasFDerivAt (Nc : Cb d → Cb d) (Nder w) w := by
  have hZ : HasFDerivAt (Zc : Cb d → ℝ) (intC.comp (expC w • (1 : Cb d →L[ℝ] Cb d))) w :=
    intC.hasFDerivAt.comp w (hasFDerivAt_expC w)
  have hinv := (hasDerivAt_inv (Zc_pos w).ne').comp_hasFDerivAt w hZ
  have hN := hinv.smul (hasFDerivAt_expC w)
  refine hN.congr_fderiv ?_
  ext1 h
  ext1 x
  have hm : intC (Nc w * h) = (Zc w)⁻¹ * intC (expC w * h) := by
    simp [Nc, smul_mul_assoc, map_smul]
  simp only [Function.comp_apply, Nder_apply, hm, ContinuousMap.add_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.one_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    ContinuousMap.mul_apply, smul_eq_mul, Nc_apply]
  field_simp
  simp only [expC_apply]
  ring


section Lam

variable {g : Torus d → ℝ}

/-- `Λ w = w + β g ⋆ N(w)`; the thermal equation for potential `ψ` is `Λ w = ψ`. -/
def Lam (hg : Integrable g) (β : ℝ) (w : Cb d) : Cb d := w + β • convCLM hg (Nc w)

/-- the derivative `I + β G ∘ N'(w)` -/
def Dlam (hg : Integrable g) (β : ℝ) (w : Cb d) : Cb d →L[ℝ] Cb d :=
  ContinuousLinearMap.id ℝ (Cb d) + β • (convCLM hg).comp (Nder w)

lemma contDiff_Lam (hg : Integrable g) (β : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (Lam hg β) :=
  contDiff_id.add (((convCLM hg).contDiff.comp contDiff_Nc).const_smul β)

lemma hasFDerivAt_Lam (hg : Integrable g) (β : ℝ) (w : Cb d) :
    HasFDerivAt (Lam hg β) (Dlam hg β w) w :=
  (hasFDerivAt_id w).add (((convCLM hg).hasFDerivAt.comp w (hasFDerivAt_Nc w)).const_smul β)

end Lam

end HRS.TRR
