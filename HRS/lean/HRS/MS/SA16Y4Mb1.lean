import HRS.MS.SA16Y3Yg2
import HRS.MS.SA16StrongLeib

/-!
# S.A.16 (SA16Y4) Mb1: derivatives of the mollification `x ↦ ∫ ρ(y) b(x-y)` of a non-compactly supported `C^k` field

`sa16y4_convL_fderiv`: `∂_v ∫ η(y) g(x-y) = ∫ η(y) ∂_v g(x-y)` for `η` locally integrable, `g ∈ C_c^∞`
(copy of `sa16y3_conv_fderiv` with `LocallyIntegrable`, so `η` may grow).
`sa16y4_convL_ibp`: `∫ b(y) ∂_v ρ(x-y) = ∫ ∂_v b(y) ρ(x-y)` for `b ∈ C^1` (no decay of `b`), `ρ ∈ C_c^∞`.
`sa16y4_mol_pd`: for `b ∈ C^j`, `∂^κ (x ↦ ∫ b(y) ρ(x-y)) = x ↦ ∫ ∂^κ b(y) ρ(x-y)` for every multi-index of length `j`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Mb1
variable {d : ℕ}

lemma sa16y4_convL_fderiv {η g : EuclideanSpace ℝ (Fin d) → ℝ} (hη : LocallyIntegrable η volume)
    (hg : IsCcInfty g) (x v : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun x => ∫ y, η y * g (x - y)) x v = ∫ y, η y * fderiv ℝ g (x - y) v := by
  have hdiff := HasCompactSupport.hasFDerivAt_convolution_right (μ := volume)
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hg.2 hη (hg.1.of_le (by simp)) x
  have hcg' : HasCompactSupport (fderiv ℝ g) := hg.2.fderiv ℝ
  have hcont' : Continuous (fderiv ℝ g) := hg.1.continuous_fderiv (by simp)
  have hconv := hcg'.convolutionExists_right ((ContinuousLinearMap.lsmul ℝ ℝ).precompR
    (EuclideanSpace ℝ (Fin d))) hη hcont'
  rw [sa16y3_conv_eq, hdiff.fderiv]
  simp only [convolution]
  rw [ContinuousLinearMap.integral_apply (hconv x)]
  congr 1

lemma sa16y4_cc_shift {ρ : EuclideanSpace ℝ (Fin d) → ℝ} (hρ : IsCcInfty ρ) (x : EuclideanSpace ℝ (Fin d)) :
    HasCompactSupport (fun y => ρ (x - y)) :=
  hρ.2.comp_homeomorph (Homeomorph.subLeft x)

lemma sa16y4_convL_ibp {b ρ : EuclideanSpace ℝ (Fin d) → ℝ} (hb : ContDiff ℝ 1 b) (hρ : IsCcInfty ρ)
    (x v : EuclideanSpace ℝ (Fin d)) :
    ∫ y, b y * fderiv ℝ ρ (x - y) v = ∫ y, fderiv ℝ b y v * ρ (x - y) := by
  set G : EuclideanSpace ℝ (Fin d) → ℝ := fun y => ρ (x - y) with hG
  have hGs : HasCompactSupport G := sa16y4_cc_shift hρ x
  have hρd : Differentiable ℝ ρ := hρ.1.differentiable (by simp)
  have hGd : ∀ y, HasFDerivAt G ((fderiv ℝ ρ (x - y)).comp (-(ContinuousLinearMap.id ℝ _))) y := by
    intro y
    have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) => x - y) (-(ContinuousLinearMap.id ℝ _)) y :=
      (hasFDerivAt_id y).const_sub x
    exact (hρd (x - y)).hasFDerivAt.comp y h1
  have hGv : ∀ y, fderiv ℝ G y v = -fderiv ℝ ρ (x - y) v := by
    intro y
    rw [(hGd y).fderiv]
    simp
  have hGc : Continuous G := hρ.1.continuous.comp (continuous_const.sub continuous_id)
  have hdG : Continuous (fun y => fderiv ℝ G y v) := by
    simp_rw [hGv]
    exact ((hρ.1.continuous_fderiv (by simp)).comp (continuous_const.sub continuous_id)).clm_apply
      continuous_const |>.neg
  have hbc : Continuous b := hb.continuous
  have hdb : Continuous (fun y => fderiv ℝ b y v) :=
    (hb.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdGs : HasCompactSupport (fun y => fderiv ℝ G y v) :=
    (hGs.fderiv ℝ).comp_left (g := fun A : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ => A v) (by simp)
  have h1 : Integrable (fun y => fderiv ℝ b y v * G y) :=
    (hdb.mul hGc).integrable_of_hasCompactSupport hGs.mul_left
  have h2 : Integrable (fun y => b y * fderiv ℝ G y v) :=
    (hbc.mul hdG).integrable_of_hasCompactSupport hdGs.mul_left
  have h3 : Integrable (fun y => b y * G y) := (hbc.mul hGc).integrable_of_hasCompactSupport hGs.mul_left
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := v) h1 h2 h3
    (fun y _ => (hb.differentiable (by simp)) y) (fun y _ => (hGd y).differentiableAt)
  have e : ∫ y, b y * fderiv ℝ G y v = -∫ y, b y * fderiv ℝ ρ (x - y) v := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hGv]; ring
  linarith

lemma sa16y4_pd_cons_Ck {f : EuclideanSpace ℝ (Fin d) → ℝ} {j : ℕ} (hf : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) f)
    (i : Fin d) (idx : Fin j → Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    partialDeriv (Fin.cons i idx : Fin (j + 1) → Fin d) f x =
      fderiv ℝ (partialDeriv idx f) x (EuclideanSpace.single i 1) := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j f) x :=
    (hf.differentiable_iteratedFDeriv (m := j) (by exact_mod_cast Nat.lt_succ_self j)) x
  unfold partialDeriv
  rw [iteratedFDeriv_succ_apply_left]
  have hL : HasFDerivAt (fun y => iteratedFDeriv ℝ j f y (fun l => EuclideanSpace.single (idx l) 1))
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => EuclideanSpace ℝ (Fin d)) ℝ
        (fun l => EuclideanSpace.single (idx l) 1)).comp (fderiv ℝ (iteratedFDeriv ℝ j f) x)) x :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => EuclideanSpace ℝ (Fin d)) ℝ
      (fun l => EuclideanSpace.single (idx l) 1)).hasFDerivAt.comp x hd.hasFDerivAt
  rw [hL.fderiv]
  have htail : (Fin.tail fun l : Fin (j + 1) => (EuclideanSpace.single
      ((Fin.cons i idx : Fin (j + 1) → Fin d) l) (1 : ℝ) : EuclideanSpace ℝ (Fin d))) =
      fun l => EuclideanSpace.single (idx l) 1 := by
    funext l
    simp [Fin.tail]
  simp [htail]

lemma sa16y4_pd_contDiff1 {f : EuclideanSpace ℝ (Fin d) → ℝ} {j : ℕ} (hf : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) f)
    (idx : Fin j → Fin d) : ContDiff ℝ 1 (partialDeriv idx f) := by
  have h1 : ContDiff ℝ 1 (iteratedFDeriv ℝ j f) :=
    hf.iteratedFDeriv_right (m := 1) (i := j) (by norm_cast; omega)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => EuclideanSpace ℝ (Fin d)) ℝ
      (fun l => EuclideanSpace.single (idx l) 1)).contDiff.comp h1

lemma sa16y4_mol_pd {ρ : EuclideanSpace ℝ (Fin d) → ℝ} (hρ : IsCcInfty ρ) :
    ∀ (j : ℕ) (b : EuclideanSpace ℝ (Fin d) → ℝ), ContDiff ℝ (j : WithTop ℕ∞) b → ∀ κ : Fin j → Fin d,
      partialDeriv κ (fun x => ∫ y, b y * ρ (x - y)) = fun x => ∫ y, partialDeriv κ b y * ρ (x - y) := by
  intro j
  induction j with
  | zero =>
    intro b hb κ
    funext x
    simp only [partialDeriv, iteratedFDeriv_zero_apply]
  | succ j ih =>
    intro b hb κ
    obtain ⟨i, κ', rfl⟩ : ∃ (i : Fin d) (κ' : Fin j → Fin d), κ = Fin.cons i κ' :=
      ⟨κ 0, Fin.tail κ, (Fin.cons_self_tail κ).symm⟩
    funext x
    have hb' : ContDiff ℝ (j : WithTop ℕ∞) b := hb.of_le (by exact_mod_cast Nat.le_succ j)
    have hA : ContDiff ℝ ∞ (fun x => ∫ y, b y * ρ (x - y)) :=
      sa16y3_conv_contDiff (hb.continuous.locallyIntegrable) hρ
    rw [sa16s_pd_cons hA i κ' x, ih b hb' κ']
    have h1 : ContDiff ℝ 1 (partialDeriv κ' b) := sa16y4_pd_contDiff1 (by simpa using hb) κ'
    rw [sa16y4_convL_fderiv ((h1.continuous).locallyIntegrable) hρ x]
    rw [sa16y4_convL_ibp h1 hρ x]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show fderiv ℝ (partialDeriv κ' b) y (EuclideanSpace.single i 1) * ρ (x - y) =
      partialDeriv (Fin.cons i κ' : Fin (j + 1) → Fin d) b y * ρ (x - y)
    rw [sa16y4_pd_cons_Ck (by simpa using hb) i κ' y]

end Mb1

end HRS.Whole.AppendixA.Phase2SA16R
