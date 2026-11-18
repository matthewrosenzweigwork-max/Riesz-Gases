import HRS.MS.S113X2C4
import HRS.MS.S113EndAux4

/-!
# S11.3 X2 wiring (worker S11W), C5: the source `R` in `ℝ^{Nd}` coordinates

* `s113c_movFP_local`: `movFP f X = β⁻¹ ∑_k D²f(e_k,e_k) - ∑_k D(f b_k)(e_k)` for `f` of class `C²` near a collision-free `X`.
* `s113c_R_eq`: for a `C²` space-time density `q̃` agreeing with `movQDensity ∘ Jc` on an open set, and a drift `b̃` agreeing with
  the physical drift there, `s113b_R (β⁻¹) b̃ q̃ τ z = s113x_source τ (Jc z)`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2C

open HRS HRS.Whole HRS.MS.S113X2 HRS.MS.S113X2B
open HRS.MC.CepP3 (Jc Jc_single fderiv2_comp_clm)

variable {d N : ℕ}

theorem s113c_drift_contDiffAt (s q β : ℝ) {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) (i : Fin N) (k : Fin d) :
    ContDiffAt ℝ ∞ (fun Y : EucConfig d N => particleDriftW (quadraticGradientDyn d s q β) Y i k) X := by
  have h1 := (s113a_drift_contDiffOn (d := d) (N := N) s q β).contDiffAt
    ((s113a_isOpen_free d N).mem_nhds hX)
  have h2 := (contDiffAt_pi.1 h1) i
  exact ((EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).contDiff.contDiffAt).comp X h2

theorem s113c_movFP_local (s q β : ℝ) {f : EucConfig d N → ℝ} {X : EucConfig d N}
    (hf : ContDiffAt ℝ 2 f X) (hX : X ∉ eucCollisionSet d N) :
    movFP d s q β N f X =
      β⁻¹ * ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ f) X (HRS.configBasis d N k) (HRS.configBasis d N k) -
        ∑ k : Fin N × Fin d, fderiv ℝ (fun Y => f Y * particleDriftW (quadraticGradientDyn d s q β) Y k.1 k.2) X
          (HRS.configBasis d N k) := by
  have hdk : ∀ k : Fin N × Fin d,
      ContDiffAt ℝ 2 (fun Y : EucConfig d N => particleDriftW (quadraticGradientDyn d s q β) Y k.1 k.2) X :=
    fun k => (s113c_drift_contDiffAt s q β hX k.1 k.2).of_le (by simp)
  have hdiff : ∀ k : Fin N × Fin d,
      DifferentiableAt ℝ (fun Y => f Y * particleDriftW (quadraticGradientDyn d s q β) Y k.1 k.2) X :=
    fun k => (hf.differentiableAt (by norm_num)).mul ((hdk k).differentiableAt (by norm_num))
  have hA : ∀ k : Fin N × Fin d, movPartial (movPartial f k.1 k.2) k.1 k.2 X =
      fderiv ℝ (fderiv ℝ f) X (HRS.configBasis d N k) (HRS.configBasis d N k) := fun k =>
    s113a_movPartial2 hf k.1 k.2
  have hB : ∀ k : Fin N × Fin d,
      movPartial (fun Y => f Y * (q * (Y k.1) k.2 + (1 / (N : ℝ)) *
        ∑ j ∈ Finset.univ.erase k.1, rieszKernelGrad d s (Y k.1 - Y j) k.2)) k.1 k.2 X =
      -fderiv ℝ (fun Y => f Y * particleDriftW (quadraticGradientDyn d s q β) Y k.1 k.2) X
        (HRS.configBasis d N k) := by
    intro k
    have hfun : (fun Y : EucConfig d N => f Y * (q * (Y k.1) k.2 + (1 / (N : ℝ)) *
        ∑ j ∈ Finset.univ.erase k.1, rieszKernelGrad d s (Y k.1 - Y j) k.2)) =
        fun Y => -(f Y * particleDriftW (quadraticGradientDyn d s q β) Y k.1 k.2) := by
      funext Y
      rw [s113a_weight_eq s q β Y k.1 k.2]
      ring
    have hnd : DifferentiableAt ℝ (fun Y : EucConfig d N =>
        -(f Y * particleDriftW (quadraticGradientDyn d s q β) Y k.1 k.2)) X := (hdiff k).neg
    rw [hfun, s113a_movPartial_eq hnd k.1 k.2, fderiv_fun_neg, ContinuousLinearMap.neg_apply]
  unfold movFP
  rw [← Fintype.sum_prod_type' (f := fun i k => β⁻¹ * movPartial (movPartial f i k) i k X +
      movPartial (fun Y => f Y * (q * (Y i) k + (1 / (N : ℝ)) *
        ∑ j ∈ Finset.univ.erase i, rieszKernelGrad d s (Y i - Y j) k)) i k X)]
  simp only [hA, hB]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_neg_distrib]
  ring

theorem s113c_Jsymm_apply (Y : EucConfig d N) (m : Fin (N * d)) :
    (Jc d N).symm Y m = Y (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2 := rfl

/-- The spatial Fokker-Planck expression of a `C²` density in `ℝ^{Nd}` coordinates. -/
theorem s113c_FP_E (s q β : ℝ) {F : EucConfig d N → ℝ} {qt : s113b_E (N * d) → ℝ} (hqt : ContDiff ℝ 2 qt)
    {G' : Set (s113b_E (N * d))} (hG' : IsOpen G') (hmatch : ∀ z ∈ G', qt z = F (Jc d N z))
    {b' : s113b_E (N * d) → s113b_E (N * d)} {G : Set (s113b_E (N * d))} (hG : IsOpen G)
    (hb' : ∀ z ∈ G, b' z = s113c_bE d s q β N z) {z : s113b_E (N * d)} (hzG : z ∈ G) (hzG' : z ∈ G')
    (hz : Jc d N z ∉ eucCollisionSet d N) :
    movFP d s q β N F (Jc d N z) = β⁻¹ * s113b_lap qt z - s113b_div (fun y => qt y • b' y) z := by
  set X := Jc d N z with hXdef
  set φ : EucConfig d N → ℝ := fun x => qt ((Jc d N).symm x) with hφ
  have hφ2 : ContDiff ℝ 2 φ := hqt.comp (Jc d N).symm.contDiff
  have hφJ : (fun y => φ (Jc d N y)) = qt := funext fun y => by simp [hφ]
  have hFφ : F =ᶠ[𝓝 X] φ := by
    have hopen : IsOpen {Y : EucConfig d N | (Jc d N).symm Y ∈ G'} := hG'.preimage (Jc d N).symm.continuous
    have hmem : X ∈ {Y : EucConfig d N | (Jc d N).symm Y ∈ G'} := by simpa [hXdef] using hzG'
    filter_upwards [hopen.mem_nhds hmem] with Y hY
    have := hmatch _ hY
    simp only [hφ]
    rw [this]
    simp
  have hFc : ContDiffAt ℝ 2 F X := hφ2.contDiffAt.congr_of_eventuallyEq hFφ
  rw [s113c_movFP_local s q β hFc hz]
  have hD2 : fderiv ℝ (fderiv ℝ F) X = fderiv ℝ (fderiv ℝ φ) X := hFφ.fderiv.fderiv_eq
  have hlap : ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ F) X (HRS.configBasis d N k) (HRS.configBasis d N k) =
      s113b_lap qt z := by
    rw [hD2, ← hφJ, s113c_lap_comp hφ2]
  have hdk : ∀ k : Fin N × Fin d,
      ContDiffAt ℝ 2 (fun Y : EucConfig d N => particleDriftW (quadraticGradientDyn d s q β) Y k.1 k.2) X :=
    fun k => (s113c_drift_contDiffAt s q β hz k.1 k.2).of_le (by simp)
  have hprod : ∀ k : Fin N × Fin d,
      fderiv ℝ (fun Y => F Y * particleDriftW (quadraticGradientDyn d s q β) Y k.1 k.2) X =
      fderiv ℝ (fun Y => φ Y * particleDriftW (quadraticGradientDyn d s q β) Y k.1 k.2) X :=
    fun k => (hFφ.mul Filter.EventuallyEq.rfl).fderiv_eq
  have hdiv : s113b_div (fun y => qt y • b' y) z =
      ∑ k : Fin N × Fin d, fderiv ℝ (fun Y => φ Y * particleDriftW (quadraticGradientDyn d s q β) Y k.1 k.2) X
        (HRS.configBasis d N k) := by
    unfold s113b_div
    have hm : ∀ m : Fin (N * d),
        fderiv ℝ (fun y => (qt y • b' y) m) z (EuclideanSpace.single m 1) =
        fderiv ℝ (fun Y => φ Y * particleDriftW (quadraticGradientDyn d s q β) Y
          (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2) X
          (HRS.configBasis d N (finProdFinEquiv.symm m)) := by
      intro m
      set k := finProdFinEquiv.symm m with hk
      have hev : (fun y => (qt y • b' y) m) =ᶠ[𝓝 z] fun y =>
          (fun Y => φ Y * particleDriftW (quadraticGradientDyn d s q β) Y k.1 k.2) (Jc d N y) := by
        filter_upwards [hG.mem_nhds hzG] with y hy
        simp only [PiLp.smul_apply, smul_eq_mul]
        rw [hb' y hy]
        simp only [hφ, s113c_bE, s113c_Jsymm_apply, ContinuousLinearEquiv.symm_apply_apply, hk]
      rw [hev.fderiv_eq]
      have hdf : DifferentiableAt ℝ (fun Y => φ Y * particleDriftW (quadraticGradientDyn d s q β) Y k.1 k.2) X :=
        (hφ2.differentiable (by norm_num) X).mul ((hdk k).differentiableAt (by norm_num))
      have h1 := hdf.hasFDerivAt.comp z (Jc d N).hasFDerivAt
      have e : fderiv ℝ (fun y => (fun Y => φ Y * particleDriftW (quadraticGradientDyn d s q β) Y k.1 k.2)
          (Jc d N y)) z = (fderiv ℝ (fun Y => φ Y * particleDriftW (quadraticGradientDyn d s q β) Y k.1 k.2)
            X).comp (Jc d N : s113b_E (N * d) →L[ℝ] EucConfig d N) := h1.fderiv
      rw [e]
      show fderiv ℝ _ X (Jc d N (EuclideanSpace.single m 1)) = _
      rw [Jc_single]
    rw [Finset.sum_congr rfl fun m _ => hm m]
    exact Equiv.sum_comp (finProdFinEquiv.symm : Fin (N * d) ≃ Fin N × Fin d)
      (fun k => fderiv ℝ (fun Y => φ Y * particleDriftW (quadraticGradientDyn d s q β) Y k.1 k.2) X
        (HRS.configBasis d N k))
  rw [hlap, hdiv]
  simp only [hprod]

open HRS.MS.S113BD (s113x_source) in
/-- **The source in `ℝ^{Nd}` coordinates.**  For a space-time density `q̃` of class `C²` agreeing with `movQDensity ∘ Jc` on
an open set `G'` for times in `[0,T+1]`, and a drift `b'` agreeing with the physical drift on an open set `G`:
`s113b_R (β⁻¹) b' q̃ τ z = s113x_source τ (Jc z)` for `z ∈ G ∩ G'` away from collisions and `τ ∈ [0,T]`. -/
theorem s113c_R_eq (s q β : ℝ) {ρ : ℝ → Euc d → ℝ} {T : ℝ}
    {qt : ℝ → s113b_E (N * d) → ℝ} (hq : ContDiff ℝ 2 (fun z : ℝ × s113b_E (N * d) => qt z.1 z.2))
    {G' : Set (s113b_E (N * d))} (hG' : IsOpen G')
    (hmatch : ∀ t ∈ Set.Icc (0 : ℝ) (T + 1), ∀ z ∈ G', qt t z = movQDensity d s β N (ρ t) (Jc d N z))
    {b' : s113b_E (N * d) → s113b_E (N * d)} {G : Set (s113b_E (N * d))} (hG : IsOpen G)
    (hb' : ∀ z ∈ G, b' z = s113c_bE d s q β N z)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T) {z : s113b_E (N * d)} (hzG : z ∈ G) (hzG' : z ∈ G')
    (hz : Jc d N z ∉ eucCollisionSet d N) :
    s113b_R β⁻¹ b' qt τ z = s113x_source d s q β N ρ τ (Jc d N z) := by
  have hτ1 : τ ∈ Set.Icc (0 : ℝ) (T + 1) := ⟨hτ.1, by linarith [hτ.2]⟩
  have hqτ : ContDiff ℝ 2 (qt τ) := hq.comp (contDiff_const.prodMk contDiff_id)
  have hFP := s113c_FP_E s q β (F := movQDensity d s β N (ρ τ)) hqτ hG' (fun w hw => hmatch τ hτ1 w hw) hG hb' hzG
    hzG' hz
  have hden : movQDensity d s β N (ρ τ) (Jc d N z) = qt τ z := (hmatch τ hτ1 z hzG').symm
  have hd : HasDerivAt (fun σ => qt σ z) (deriv (fun σ => qt σ z) τ) τ :=
    (((hq.comp (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num)) τ).hasDerivAt
  have hev : (fun σ => qt σ z) =ᶠ[𝓝[Set.Ici τ] τ] fun σ => movQDensity d s β N (ρ σ) (Jc d N z) := by
    have hmem : Set.Icc τ (T + 1) ∈ 𝓝[Set.Ici τ] τ := Icc_mem_nhdsGE (by linarith [hτ.2])
    filter_upwards [hmem] with σ hσ
    exact hmatch σ ⟨hτ.1.trans hσ.1, hσ.2⟩ z hzG'
  have hdw : HasDerivWithinAt (fun σ => movQDensity d s β N (ρ σ) (Jc d N z)) (deriv (fun σ => qt σ z) τ)
      (Set.Ici τ) τ :=
    hd.hasDerivWithinAt.congr_of_eventuallyEq hev.symm (hmatch τ hτ1 z hzG').symm
  have htime := hdw.derivWithin (uniqueDiffWithinAt_Ici τ)
  unfold s113b_R s113x_source
  rw [if_neg hz, hFP, htime, hden]

end HRS.MS.S113X2C

end
