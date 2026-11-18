import HRS.Commutator.Torus.NRSTAux20

/-!
# NRS-T, part 21: a Schwartz cutoff with compactly supported Fourier transform
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- A bump of radius `1/8` around `0`. -/
def nrstr_bump : ContDiffBump (0 : 𝔼) := ⟨1 / 16, 1 / 8, by norm_num, by norm_num⟩

/-- The even bump `v ↦ b(v) b(-v)`. -/
def nrstr_bumpE (v : 𝔼) : ℝ := (nrstr_bump (d := d)) v * (nrstr_bump (d := d)) (-v)

lemma nrstr_bumpE_neg (v : 𝔼) : nrstr_bumpE (d := d) (-v) = nrstr_bumpE (d := d) v := by
  unfold nrstr_bumpE; rw [neg_neg, mul_comm]

lemma nrstr_bumpE_nonneg (v : 𝔼) : 0 ≤ nrstr_bumpE (d := d) v :=
  mul_nonneg (nrstr_bump (d := d)).nonneg (nrstr_bump (d := d)).nonneg

lemma nrstr_bumpE_cont : Continuous (nrstr_bumpE (d := d)) :=
  (nrstr_bump (d := d)).continuous.mul ((nrstr_bump (d := d)).continuous.comp continuous_neg)

lemma nrstr_bumpE_cs : HasCompactSupport (nrstr_bumpE (d := d)) :=
  (nrstr_bump (d := d)).hasCompactSupport.mul_right

lemma nrstr_bumpE_smooth : ContDiff ℝ ∞ (nrstr_bumpE (d := d)) :=
  (nrstr_bump (d := d)).contDiff.mul ((nrstr_bump (d := d)).contDiff.comp contDiff_neg)

lemma nrstr_bumpE_zero_of_far {v : 𝔼} (hv : 1 / 8 ≤ ‖v‖) : nrstr_bumpE (d := d) v = 0 := by
  have : (nrstr_bump (d := d)) v = 0 := by
    apply ContDiffBump.zero_of_le_dist
    simpa [nrstr_bump, dist_zero_right] using hv
  simp [nrstr_bumpE, this]

lemma nrstr_bumpE_zero : nrstr_bumpE (d := d) 0 = 1 := by
  have : (nrstr_bump (d := d)) 0 = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    simp [nrstr_bump]
  simp [nrstr_bumpE, this]

lemma nrstr_bump_cs : HasCompactSupport (fun v : 𝔼 => (((nrstr_bumpE (d := d)) v : ℝ) : ℂ)) :=
  (nrstr_bumpE_cs (d := d)).comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)

lemma nrstr_bump_cd : ContDiff ℝ ∞ (fun v : 𝔼 => (((nrstr_bumpE (d := d)) v : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (nrstr_bumpE_smooth (d := d))

/-- The Fourier-side cutoff `θ₀` as a Schwartz function. -/
def nrstr_theta0 : SchwartzMap 𝔼 ℂ := (nrstr_bump_cs (d := d)).toSchwartzMap (nrstr_bump_cd (d := d))

lemma nrstr_theta0_apply (v : 𝔼) : nrstr_theta0 (d := d) v = (((nrstr_bumpE (d := d)) v : ℝ) : ℂ) := rfl

lemma nrstr_theta0_zero_of_far {v : 𝔼} (hv : 1 / 8 ≤ ‖v‖) : nrstr_theta0 (d := d) v = 0 := by
  rw [nrstr_theta0_apply, nrstr_bumpE_zero_of_far hv]
  simp

/-- The spatial cutoff `φ = 𝓕⁻ θ₀`. -/
def nrstr_phi : SchwartzMap 𝔼 ℂ := 𝓕⁻ (nrstr_theta0 (d := d))

lemma fourier_nrstr_phi : 𝓕 (⇑(nrstr_phi (d := d))) = ⇑(nrstr_theta0 (d := d)) := by
  have h : (𝓕 (𝓕⁻ (nrstr_theta0 (d := d)) : SchwartzMap 𝔼 ℂ) : SchwartzMap 𝔼 ℂ) = nrstr_theta0 :=
    FourierTransform.fourier_fourierInv_eq _
  rw [← SchwartzMap.fourier_coe]
  exact congrArg (fun f : SchwartzMap 𝔼 ℂ => (⇑f : 𝔼 → ℂ)) h

lemma nrstr_phi_zero : nrstr_phi (d := d) 0 = ((∫ v : 𝔼, ((nrstr_bumpE (d := d)) v : ℝ)  : ℝ) : ℂ) := by
  unfold nrstr_phi
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul,
    nrstr_theta0_apply]
  rw [integral_complex_ofReal]

lemma nrstr_phi_zero_pos : 0 < ∫ v : 𝔼, ((nrstr_bumpE (d := d)) v : ℝ) := by
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (0 : 𝔼))
    (nrstr_bumpE_cont (d := d)) (nrstr_bumpE_cs (d := d))
    (fun v => nrstr_bumpE_nonneg v) ?_
  rw [nrstr_bumpE_zero]
  norm_num

end HRS.Commutator.TorusNote
