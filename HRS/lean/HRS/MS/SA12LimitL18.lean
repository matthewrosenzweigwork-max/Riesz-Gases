import HRS.MS.SA12CcDenseH
import HRS.MS.SA12LimitL12
import HRS.MS.MovBridgeAux6
import HRS.MP.RdInit
import HRS.MS.UniqT3
import HRS.MS.SA12LimitL11

/-!
# S.A.12 L18: weak continuity in `H^m` from continuity against `C_c^∞` tests
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MP.RdInit

variable {d : ℕ}

theorem sa12y_fourier_partial {k : ℕ} {u : Euc d → ℝ} (hu : ContDiff ℝ k u) (hc : HasCompactSupport u)
    {j : ℕ} (hj : j ≤ k) (idx : Fin j → Fin d) (ξ : Euc d) :
    𝓕 (fun x => ((partialDeriv idx u x : ℝ) : ℂ)) ξ =
      ((2 * Real.pi * Complex.I) ^ j * ∏ i, ((ξ (idx i) : ℝ) : ℂ)) * 𝓕 (fun x => ((u x : ℝ) : ℂ)) ξ := by
  set f : Euc d → ℂ := fun x => ((u x : ℝ) : ℂ) with hf
  have hfC : ContDiff ℝ (k : ℕ∞) f := by
    have := Complex.ofRealCLM.contDiff.comp hu
    exact this
  have hfc : HasCompactSupport f := hc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hint : ∀ n : ℕ, (n : ℕ∞) ≤ (k : ℕ∞) → Integrable (iteratedFDeriv ℝ n f) volume := by
    intro n hn
    have hcn : Continuous (iteratedFDeriv ℝ n f) := by
      refine hfC.continuous_iteratedFDeriv ?_
      exact_mod_cast hn
    exact hcn.integrable_of_hasCompactSupport (hfc.iteratedFDeriv n)
  have hjk : (j : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast hj
  have h1 := Real.fourier_iteratedFDeriv hfC hint hjk
  have hcomp : ∀ x, iteratedFDeriv ℝ j f x (mri_e idx) = ((partialDeriv idx u x : ℝ) : ℂ) := by
    intro x
    have : iteratedFDeriv ℝ j f x = Complex.ofRealCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ j u x) := by
      have := Complex.ofRealCLM.iteratedFDeriv_comp_left (x := x) (f := u) (n := (k : WithTop ℕ∞))
        hu.contDiffAt (i := j) (by exact_mod_cast hj)
      exact this
    rw [this]
    rfl
  have h2 : 𝓕 (fun x => ((partialDeriv idx u x : ℝ) : ℂ)) ξ = 𝓕 (iteratedFDeriv ℝ j f) ξ (mri_e idx) := by
    have h3 := Real.fourierIntegral_continuousMultilinearMap_apply' (L := innerSL ℝ) (μ := volume)
      (hf := hint j hjk) (m := mri_e idx) (w := ξ)
    have h4 : (fun x => ((partialDeriv idx u x : ℝ) : ℂ)) = fun x => iteratedFDeriv ℝ j f x (mri_e idx) := by
      funext x; exact (hcomp x).symm
    rw [h4]
    exact h3.symm
  rw [h2, h1]
  simp only [VectorFourier.fourierPowSMulRight_apply]
  have hin : ∀ a : Fin d, innerSL ℝ ξ (EuclideanSpace.single a (1 : ℝ)) = ξ a := by
    intro a
    rw [innerSL_apply_apply, EuclideanSpace.inner_single_right]
    simp
  simp [mri_e, hin]
  rw [Finset.prod_neg, neg_pow (2 * (Real.pi : ℂ) * Complex.I) j]
  simp only [Finset.card_univ, Fintype.card_fin]
  have h1 : ((-1 : ℂ) ^ j) * ((-1 : ℂ) ^ j) = 1 := by rw [← mul_pow]; norm_num
  linear_combination ((2 * (Real.pi : ℂ) * Complex.I) ^ j * (∏ i, ((ξ (idx i) : ℝ) : ℂ)) * 𝓕 f ξ) * h1

theorem sa12y_fourier_sub {f g : Euc d → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : Euc d) :
    𝓕 (fun x => f x - g x) ξ = 𝓕 f ξ - 𝓕 g ξ := by
  have h1 := (VectorFourier.fourierIntegral_convergent_iff (L := innerₗ (Euc d))
    Real.continuous_fourierChar continuous_inner ξ).2 hf
  have h2 := (VectorFourier.fourierIntegral_convergent_iff (L := innerₗ (Euc d))
    Real.continuous_fourierChar continuous_inner ξ).2 hg
  have h1' : Integrable (fun v => 𝐞 (-inner ℝ v ξ) • f v) volume := h1
  have h2' : Integrable (fun v => 𝐞 (-inner ℝ v ξ) • g v) volume := h2
  simp only [Real.fourier_eq, smul_sub]
  exact integral_sub h1' h2'

theorem sa12y_fourier_sum {ι : Type*} (s : Finset ι) {f : ι → Euc d → ℂ}
    (hf : ∀ i ∈ s, Integrable (f i)) (ξ : Euc d) :
    𝓕 (fun x => ∑ i ∈ s, f i x) ξ = ∑ i ∈ s, 𝓕 (f i) ξ := by
  have h : ∀ i ∈ s, Integrable (fun v => 𝐞 (-inner ℝ v ξ) • f i v) volume := fun i hi =>
    (VectorFourier.fourierIntegral_convergent_iff (L := innerₗ (Euc d))
      Real.continuous_fourierChar continuous_inner ξ).2 (hf i hi)
  simp only [Real.fourier_eq, Finset.smul_sum]
  exact integral_finset_sum s h

theorem sa12y_D1_eq_partial (i : Fin d) (f : Euc d → ℝ) :
    HRS.MS.UniqT3.D1 i f = partialDeriv (fun _ : Fin 1 => i) f := by
  funext x
  unfold partialDeriv HRS.MS.UniqT3.D1
  rw [iteratedFDeriv_one_apply]

theorem sa12y_D1_cc {f : Euc d → ℝ} (hf : IsCcInfty f) (i : Fin d) :
    IsCcInfty (HRS.MS.UniqT3.D1 i f) :=
  ⟨(hf.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, HRS.MS.UniqT3.D1_supp hf.2 i⟩

theorem sa12y_cc_integrable {f : Euc d → ℝ} (hf : IsCcInfty f) :
    Integrable (fun x => ((f x : ℝ) : ℂ)) :=
  (hf.1.continuous.integrable_of_hasCompactSupport hf.2).ofReal

theorem sa12y_fourier_D1 {f : Euc d → ℝ} (hf : IsCcInfty f) (i : Fin d) (ξ : Euc d) :
    𝓕 (fun x => ((HRS.MS.UniqT3.D1 i f x : ℝ) : ℂ)) ξ =
      (2 * Real.pi * Complex.I * ((ξ i : ℝ) : ℂ)) * 𝓕 (fun x => ((f x : ℝ) : ℂ)) ξ := by
  have := sa12y_fourier_partial (k := 1) (hf.1.of_le (by simp)) hf.2 (le_refl 1) (fun _ : Fin 1 => i) ξ
  rw [← sa12y_D1_eq_partial] at this
  simpa using this

/-- The operator `ψ ↦ ψ - Δψ` on test functions. -/
def sa12y_Q (f : Euc d → ℝ) : Euc d → ℝ := fun x => f x - Laplacian.laplacian f x

theorem sa12y_Q_cc {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) : IsCcInfty (sa12y_Q ψ) := by
  have hlap : Laplacian.laplacian ψ = fun x => ∑ i, HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i ψ) x :=
    funext fun y => HRS.MS.UniqT3.lap_eq (hψ.1.of_le (by simp)) y
  have hs : IsCcInfty (fun x => ∑ i, HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i ψ) x) := by
    refine ⟨?_, ?_⟩
    · exact ContDiff.sum fun i _ => (sa12y_D1_cc (sa12y_D1_cc hψ i) i).1
    · have := HasCompactSupport.finset_sum (s := Finset.univ)
        (f := fun i => HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i ψ)) fun i _ =>
          (sa12y_D1_cc (sa12y_D1_cc hψ i) i).2
      convert this using 1
      funext x
      simp [Finset.sum_apply]
  unfold sa12y_Q
  rw [hlap]
  exact ⟨hψ.1.sub hs.1, hψ.2.sub hs.2⟩

theorem sa12y_Q_fourier {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) (ξ : Euc d) :
    𝓕 (fun x => ((sa12y_Q ψ x : ℝ) : ℂ)) ξ =
      ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * 𝓕 (fun x => ((ψ x : ℝ) : ℂ)) ξ := by
  have hlap : Laplacian.laplacian ψ = fun x => ∑ i, HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i ψ) x :=
    funext fun y => HRS.MS.UniqT3.lap_eq (hψ.1.of_le (by simp)) y
  have hint : ∀ i ∈ Finset.univ, Integrable (fun x => ((HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i ψ) x : ℝ) : ℂ)) :=
    fun i _ => sa12y_cc_integrable (sa12y_D1_cc (sa12y_D1_cc hψ i) i)
  have e : (fun x => ((sa12y_Q ψ x : ℝ) : ℂ)) = fun x => ((ψ x : ℝ) : ℂ) -
      ∑ i ∈ Finset.univ, ((HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i ψ) x : ℝ) : ℂ) := by
    funext x
    unfold sa12y_Q
    rw [hlap]
    push_cast
    rfl
  rw [e, sa12y_fourier_sub (sa12y_cc_integrable hψ) (integrable_finset_sum _ hint),
    sa12y_fourier_sum Finset.univ hint]
  have h2 : ∀ i : Fin d, 𝓕 (fun x => ((HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i ψ) x : ℝ) : ℂ)) ξ =
      (2 * Real.pi * Complex.I * ((ξ i : ℝ) : ℂ)) ^ 2 * 𝓕 (fun x => ((ψ x : ℝ) : ℂ)) ξ := by
    intro i
    rw [sa12y_fourier_D1 (sa12y_D1_cc hψ i) i ξ, sa12y_fourier_D1 hψ i ξ]
    ring
  simp_rw [h2]
  rw [← Finset.sum_mul]
  have h3 : ∑ i : Fin d, (2 * (Real.pi : ℂ) * Complex.I * ((ξ i : ℝ) : ℂ)) ^ 2 =
      -(((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) := by
    have : ‖ξ‖ ^ 2 = ∑ i : Fin d, (ξ i) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      exact Finset.sum_congr rfl fun i _ => by simp
    rw [this]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : Complex.I ^ 2 = -1 := Complex.I_sq
    calc _ = (2 * (Real.pi : ℂ)) ^ 2 * Complex.I ^ 2 * ((ξ i : ℝ) : ℂ) ^ 2 := by ring
      _ = _ := by rw [this]; ring
  rw [h3]
  push_cast
  ring

theorem sa12y_Qiter_cc (k : ℕ) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) : IsCcInfty (sa12y_Q^[k] ψ) := by
  induction k generalizing ψ with
  | zero => simpa using hψ
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact ih (sa12y_Q_cc hψ)

theorem sa12y_Qiter_fourier (k : ℕ) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) (ξ : Euc d) :
    𝓕 (fun x => ((sa12y_Q^[k] ψ x : ℝ) : ℂ)) ξ =
      (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ k : ℝ) : ℂ) * 𝓕 (fun x => ((ψ x : ℝ) : ℂ)) ξ := by
  induction k generalizing ψ with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih (sa12y_Q_cc hψ), sa12y_Q_fourier hψ]
    push_cast
    ring

theorem sa12y_inner_eq (m : ℕ) {G : Euc d → ℝ} (hG : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) G)
    {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) :
    sobolevInnerRd m G ψ = ∫ x, G x * (sa12y_Q^[m] ψ) x := by
  set f := sa12y_Q^[m] ψ with hf
  have hfc : IsCcInfty f := sa12y_Qiter_cc m hψ
  have hψL2 : MemLp ψ 2 volume := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2
  have hψL1 : Integrable ψ volume := hψ.1.continuous.integrable_of_hasCompactSupport hψ.2
  have hfL2 : MemLp f 2 volume := hfc.1.continuous.memLp_of_hasCompactSupport hfc.2
  have hfL1 : Integrable f volume := hfc.1.continuous.integrable_of_hasCompactSupport hfc.2
  have h1 := HRS.Commutator.Whole.energyAux_fourierL2_eq f hfL1 hfL2
  have h2 := HRS.Commutator.Whole.energyAux_fourierL2_eq ψ hψL1 hψL2
  rw [HRS.PDE.ToolboxRd.FourierAux.integral_mul_eq_re_fourierL2 hG.1 hfL2]
  unfold sobolevInnerRd HRS.PDE.ToolboxRd.symbolForm
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h1, h2] with ξ e1 e2
  have e3 : HRS.PDE.ToolboxRd.fourierL2 f ξ =
      (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ m : ℝ) : ℂ) * HRS.PDE.ToolboxRd.fourierL2 ψ ξ := by
    rw [e1, e2, hf, sa12y_Qiter_fourier m hψ ξ]
  rw [e3, map_mul, Complex.conj_ofReal, Real.rpow_natCast]
  ring

/-- Cauchy–Schwarz for the `H^m` inner product. -/
theorem sa12y_inner_cs (m : ℕ) {G v : Euc d → ℝ} (hG : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) G)
    (hv : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) v) :
    |sobolevInnerRd m G v| ≤ Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) G) *
      Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) v) := by
  open HRS.MS.MovOsc in
  obtain ⟨hGL, hGI⟩ := (mova3b1_memSobolev_iff (m : ℝ) G).1 hG
  obtain ⟨hvL, hvI⟩ := (mova3b1_memSobolev_iff (m : ℝ) v).1 hv
  set P : Euc d → ℝ := fun ξ => HRS.MS.MovOsc.mova3b1_W ξ ^ ((m : ℝ) / 2) *
    ‖HRS.PDE.ToolboxRd.fourierL2 G ξ‖ with hP
  set Q : Euc d → ℝ := fun ξ => HRS.MS.MovOsc.mova3b1_W ξ ^ ((m : ℝ) / 2) *
    ‖HRS.PDE.ToolboxRd.fourierL2 v ξ‖ with hQ
  have hP0 : ∀ ξ, 0 ≤ P ξ := fun ξ =>
    mul_nonneg (Real.rpow_nonneg (HRS.MS.MovOsc.mova3b1_W_pos ξ).le _) (norm_nonneg _)
  have hQ0 : ∀ ξ, 0 ≤ Q ξ := fun ξ =>
    mul_nonneg (Real.rpow_nonneg (HRS.MS.MovOsc.mova3b1_W_pos ξ).le _) (norm_nonneg _)
  have hPm : AEStronglyMeasurable P volume :=
    (HRS.MS.MovOsc.mova3b1_W_rpow_cont ((m : ℝ) / 2)).aestronglyMeasurable.mul
      (HRS.PDE.ToolboxRd.FourierAux.aestronglyMeasurable_fourierL2 hGL).norm
  have hQm : AEStronglyMeasurable Q volume :=
    (HRS.MS.MovOsc.mova3b1_W_rpow_cont ((m : ℝ) / 2)).aestronglyMeasurable.mul
      (HRS.PDE.ToolboxRd.FourierAux.aestronglyMeasurable_fourierL2 hvL).norm
  have hPsq : ∀ ξ, P ξ ^ 2 = HRS.MS.MovOsc.mova3b1_W ξ ^ (m : ℝ) *
      ‖HRS.PDE.ToolboxRd.fourierL2 G ξ‖ ^ 2 := fun ξ => by
    rw [hP]; simp only; rw [mul_pow, HRS.MS.MovInterp.mova3_rpow_half_sq (HRS.MS.MovOsc.mova3b1_W_pos ξ)]
  have hQsq : ∀ ξ, Q ξ ^ 2 = HRS.MS.MovOsc.mova3b1_W ξ ^ (m : ℝ) *
      ‖HRS.PDE.ToolboxRd.fourierL2 v ξ‖ ^ 2 := fun ξ => by
    rw [hQ]; simp only; rw [mul_pow, HRS.MS.MovInterp.mova3_rpow_half_sq (HRS.MS.MovOsc.mova3b1_W_pos ξ)]
  have hP2 : Integrable (fun ξ => P ξ ^ 2) volume :=
    hGI.congr (Eventually.of_forall fun ξ => (hPsq ξ).symm)
  have hQ2 : Integrable (fun ξ => Q ξ ^ 2) volume :=
    hvI.congr (Eventually.of_forall fun ξ => (hQsq ξ).symm)
  have hCS := HRS.MS.MovOsc.mova3b1_CS hP0 hQ0 hPm hQm hP2 hQ2
  have hPQ : ∀ ξ, ‖(((HRS.MS.MovOsc.mova3b1_W ξ ^ (m : ℝ) : ℝ) : ℂ)) *
      (HRS.PDE.ToolboxRd.fourierL2 G ξ * (starRingEnd ℂ) (HRS.PDE.ToolboxRd.fourierL2 v ξ))‖ = P ξ * Q ξ := by
    intro ξ
    have hW := HRS.MS.MovOsc.mova3b1_W_pos ξ
    have h1 : HRS.MS.MovOsc.mova3b1_W ξ ^ ((m : ℝ) / 2) * HRS.MS.MovOsc.mova3b1_W ξ ^ ((m : ℝ) / 2) =
        HRS.MS.MovOsc.mova3b1_W ξ ^ (m : ℝ) := by
      rw [← Real.rpow_add hW]; congr 1; ring
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hW.le _)]
    calc _ = (HRS.MS.MovOsc.mova3b1_W ξ ^ ((m : ℝ) / 2) * HRS.MS.MovOsc.mova3b1_W ξ ^ ((m : ℝ) / 2)) *
          (‖HRS.PDE.ToolboxRd.fourierL2 G ξ‖ * ‖HRS.PDE.ToolboxRd.fourierL2 v ξ‖) := by rw [h1]
      _ = _ := by simp only [hP, hQ]; ring
  unfold sobolevInnerRd HRS.PDE.ToolboxRd.symbolForm
  calc |(∫ ξ, (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (m : ℝ) : ℝ) : ℂ) *
        (HRS.PDE.ToolboxRd.fourierL2 G ξ * (starRingEnd ℂ) (HRS.PDE.ToolboxRd.fourierL2 v ξ))).re|
      ≤ ‖∫ ξ, (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (m : ℝ) : ℝ) : ℂ) *
        (HRS.PDE.ToolboxRd.fourierL2 G ξ * (starRingEnd ℂ) (HRS.PDE.ToolboxRd.fourierL2 v ξ))‖ :=
          Complex.abs_re_le_norm _
    _ ≤ ∫ ξ, ‖(((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (m : ℝ) : ℝ) : ℂ) *
        (HRS.PDE.ToolboxRd.fourierL2 G ξ * (starRingEnd ℂ) (HRS.PDE.ToolboxRd.fourierL2 v ξ))‖ :=
          norm_integral_le_integral_norm _
    _ = ∫ ξ, P ξ * Q ξ := integral_congr_ae (Eventually.of_forall fun ξ => hPQ ξ)
    _ ≤ Real.sqrt (∫ ξ, P ξ ^ 2) * Real.sqrt (∫ ξ, Q ξ ^ 2) := hCS
    _ = _ := by
        rw [HRS.MS.MovOsc.mova3b1_sobolevNormSq_eq, HRS.MS.MovOsc.mova3b1_sobolevNormSq_eq]
        congr 2
        · exact integral_congr_ae (Eventually.of_forall hPsq)
        · exact integral_congr_ae (Eventually.of_forall hQsq)

/-- The integrand of the `H^m` inner product is integrable. -/
theorem sa12y_inner_integrable (m : ℕ) {G v : Euc d → ℝ}
    (hG : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) G) (hv : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) v) :
    Integrable (fun ξ : Euc d => (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (m : ℝ) : ℝ) : ℂ) *
      (HRS.PDE.ToolboxRd.fourierL2 G ξ * (starRingEnd ℂ) (HRS.PDE.ToolboxRd.fourierL2 v ξ))) volume := by
  obtain ⟨hGL, hGI⟩ := (HRS.MS.MovOsc.mova3b1_memSobolev_iff (m : ℝ) G).1 hG
  obtain ⟨hvL, hvI⟩ := (HRS.MS.MovOsc.mova3b1_memSobolev_iff (m : ℝ) v).1 hv
  set P : Euc d → ℝ := fun ξ => HRS.MS.MovOsc.mova3b1_W ξ ^ ((m : ℝ) / 2) *
    ‖HRS.PDE.ToolboxRd.fourierL2 G ξ‖ with hP
  set Q : Euc d → ℝ := fun ξ => HRS.MS.MovOsc.mova3b1_W ξ ^ ((m : ℝ) / 2) *
    ‖HRS.PDE.ToolboxRd.fourierL2 v ξ‖ with hQ
  have hPm : AEStronglyMeasurable P volume :=
    (HRS.MS.MovOsc.mova3b1_W_rpow_cont ((m : ℝ) / 2)).aestronglyMeasurable.mul
      (HRS.PDE.ToolboxRd.FourierAux.aestronglyMeasurable_fourierL2 hGL).norm
  have hQm : AEStronglyMeasurable Q volume :=
    (HRS.MS.MovOsc.mova3b1_W_rpow_cont ((m : ℝ) / 2)).aestronglyMeasurable.mul
      (HRS.PDE.ToolboxRd.FourierAux.aestronglyMeasurable_fourierL2 hvL).norm
  have hPsq : ∀ ξ, P ξ ^ 2 = HRS.MS.MovOsc.mova3b1_W ξ ^ (m : ℝ) *
      ‖HRS.PDE.ToolboxRd.fourierL2 G ξ‖ ^ 2 := fun ξ => by
    rw [hP]; simp only; rw [mul_pow, HRS.MS.MovInterp.mova3_rpow_half_sq (HRS.MS.MovOsc.mova3b1_W_pos ξ)]
  have hQsq : ∀ ξ, Q ξ ^ 2 = HRS.MS.MovOsc.mova3b1_W ξ ^ (m : ℝ) *
      ‖HRS.PDE.ToolboxRd.fourierL2 v ξ‖ ^ 2 := fun ξ => by
    rw [hQ]; simp only; rw [mul_pow, HRS.MS.MovInterp.mova3_rpow_half_sq (HRS.MS.MovOsc.mova3b1_W_pos ξ)]
  have hP2 : Integrable (fun ξ => P ξ ^ 2) volume :=
    hGI.congr (Eventually.of_forall fun ξ => (hPsq ξ).symm)
  have hQ2 : Integrable (fun ξ => Q ξ ^ 2) volume :=
    hvI.congr (Eventually.of_forall fun ξ => (hQsq ξ).symm)
  have hmeas : AEStronglyMeasurable (fun ξ : Euc d => (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (m : ℝ) : ℝ) : ℂ) *
      (HRS.PDE.ToolboxRd.fourierL2 G ξ * (starRingEnd ℂ) (HRS.PDE.ToolboxRd.fourierL2 v ξ))) volume := by
    refine (Complex.continuous_ofReal.comp ?_).aestronglyMeasurable.mul
      ((HRS.PDE.ToolboxRd.FourierAux.aestronglyMeasurable_fourierL2 hGL).mul
        ((Complex.continuous_conj.comp_aestronglyMeasurable
          (HRS.PDE.ToolboxRd.FourierAux.aestronglyMeasurable_fourierL2 hvL))))
    exact HRS.MS.MovOsc.mova3b1_W_rpow_cont (m : ℝ)
  refine Integrable.mono' ((hP2.add hQ2).div_const 2) hmeas (Eventually.of_forall fun ξ => ?_)
  have hW := HRS.MS.MovOsc.mova3b1_W_pos ξ
  have h1 : HRS.MS.MovOsc.mova3b1_W ξ ^ ((m : ℝ) / 2) * HRS.MS.MovOsc.mova3b1_W ξ ^ ((m : ℝ) / 2) =
      HRS.MS.MovOsc.mova3b1_W ξ ^ (m : ℝ) := by
    rw [← Real.rpow_add hW]; congr 1; ring
  have h2 : ‖(((HRS.MS.MovOsc.mova3b1_W ξ ^ (m : ℝ) : ℝ) : ℂ)) *
      (HRS.PDE.ToolboxRd.fourierL2 G ξ * (starRingEnd ℂ) (HRS.PDE.ToolboxRd.fourierL2 v ξ))‖ = P ξ * Q ξ := by
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hW.le _)]
    calc _ = (HRS.MS.MovOsc.mova3b1_W ξ ^ ((m : ℝ) / 2) * HRS.MS.MovOsc.mova3b1_W ξ ^ ((m : ℝ) / 2)) *
          (‖HRS.PDE.ToolboxRd.fourierL2 G ξ‖ * ‖HRS.PDE.ToolboxRd.fourierL2 v ξ‖) := by rw [h1]
      _ = _ := by simp only [hP, hQ]; ring
  show ‖(((HRS.MS.MovOsc.mova3b1_W ξ ^ (m : ℝ) : ℝ) : ℂ)) *
      (HRS.PDE.ToolboxRd.fourierL2 G ξ * (starRingEnd ℂ) (HRS.PDE.ToolboxRd.fourierL2 v ξ))‖ ≤ _
  rw [h2]
  show P ξ * Q ξ ≤ (P ξ ^ 2 + Q ξ ^ 2) / 2
  nlinarith [sq_nonneg (P ξ - Q ξ)]

theorem sa12y_inner_sub (m : ℕ) {G h ψ : Euc d → ℝ} (hG : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) G)
    (hh : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) h) (hψ : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) ψ) :
    sobolevInnerRd m G (fun x => h x - ψ x) = sobolevInnerRd m G h - sobolevInnerRd m G ψ := by
  unfold sobolevInnerRd HRS.PDE.ToolboxRd.symbolForm
  rw [← Complex.sub_re, ← integral_sub (sa12y_inner_integrable m hG hh) (sa12y_inner_integrable m hG hψ)]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [HRS.PDE.ToolboxRd.FourierAux.fourierL2_sub hh.1 hψ.1] with ξ e
  rw [e, map_sub]
  ring

theorem sa12y_schwartz_jets (u : SchwartzMap (Euc d) ℝ) (j : ℕ) :
    Integrable (fun x => ‖iteratedFDeriv ℝ j u x‖ ^ 2) volume := by
  set C : ℝ := SchwartzMap.seminorm ℝ 0 j u with hC
  have hb : ∀ x, ‖iteratedFDeriv ℝ j u x‖ ≤ C := fun x => SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ u j x
  have hi := u.integrable_pow_mul_iteratedFDeriv volume 0 j
  have hcont : Continuous fun x => ‖iteratedFDeriv ℝ j u x‖ ^ 2 :=
    (((u.smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm).pow 2
  refine Integrable.mono' (hi.const_mul C) hcont.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simp only [pow_zero, one_mul]
  nlinarith [hb x, norm_nonneg (iteratedFDeriv ℝ j u x)]

/-- Density of `C_c^∞` in `H^m` (strong sense). -/
theorem sa12y_ccdense (m : ℕ) {h : Euc d → ℝ} (hh : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) h) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ψ : Euc d → ℝ, IsCcInfty ψ ∧ HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) (fun x => ψ x - h x) ∧
      HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) (fun x => ψ x - h x) ≤ ε ^ 2 := by
  obtain ⟨hL, hI⟩ := (HRS.MS.MovOsc.mova3b1_memSobolev_iff (m : ℝ) h).1 hh
  obtain ⟨u, hu1, hu2⟩ := HRS.MS.MovOsc.mova3b2_dense h (t := (m : ℝ)) (Nat.cast_nonneg m) hL hI
    (ε := ε / 2) (by positivity)
  have hf : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) (fun x => u x - h x) :=
    (HRS.MS.MovOsc.mova3b1_memSobolev_iff (m : ℝ) _).2 ⟨(u.memLp 2 volume).sub hL, hu1⟩
  have hSf : HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) (fun x => u x - h x) ≤ (ε / 2) ^ 2 := by
    rw [HRS.MS.MovOsc.mova3b1_sobolevNormSq_eq]; exact hu2
  have hus : ContDiff ℝ ∞ (u : Euc d → ℝ) := u.smooth _
  obtain ⟨hmem, hlim⟩ := sa12cc_remainder m hus (fun j _ => sa12y_schwartz_jets u j)
  have hev : ∀ᶠ a : ℝ in atTop, 1 ≤ a ∧
      HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) (fun x => u x - sa12cc_rho a x * u x) < (ε / 2) ^ 2 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < (ε / 2) ^ 2))] with a ha1 ha2
    exact ⟨ha1, ha2⟩
  obtain ⟨a, ha1, ha2⟩ := hev.exists
  have ha0 : 0 < a := by linarith
  set ψ : Euc d → ℝ := fun x => sa12cc_rho a x * u x with hψ
  have hψcc : IsCcInfty ψ := ⟨(sa12cc_rho_contDiff a).mul hus, (sa12cc_rho_compact ha0).mul_right⟩
  have hg : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) (fun x => u x - ψ x) := hmem a ha1
  obtain ⟨hsub, hS⟩ := sa12l12_sq_split (m : ℝ) hf hg (t := 1) one_pos
  have e : (fun x => (u x - h x) - (u x - ψ x)) = fun x => ψ x - h x := funext fun x => by ring
  rw [e] at hsub hS
  refine ⟨ψ, hψcc, hsub, hS.trans ?_⟩
  have := ha2.le
  norm_num
  nlinarith [hSf, this, sq_nonneg ε]

-- BEGIN SA12.L18
theorem sobolev_weak_continuity (hd : 1 ≤ d) (m : ℕ) (t B : ℝ) (G : ℝ → Euc d → ℝ)
    (hG : ∀ τ ∈ Icc (0 : ℝ) t, HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) (G τ) ∧
      Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) (G τ)) ≤ B)
    (hcont : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ContinuousOn (fun τ => ∫ x, G τ x * ψ x) (Icc (0 : ℝ) t)) :
    ∀ h : Euc d → ℝ, HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) h →
      ContinuousOn (fun τ => sobolevInnerRd m (G τ) h) (Icc (0 : ℝ) t) := by
  intro h hh
  set B' : ℝ := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have hψcont : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      ContinuousOn (fun τ => sobolevInnerRd m (G τ) ψ) (Icc (0 : ℝ) t) := by
    intro ψ hψ
    exact (hcont _ (sa12y_Qiter_cc m hψ)).congr fun τ hτ => sa12y_inner_eq m (hG τ hτ).1 hψ
  intro τ0 hτ0
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hden : 0 < 3 * (B' + 1) := by positivity
  obtain ⟨ψ, hψcc, hψmem, hψS⟩ := sa12y_ccdense m hh (ε := ε / (3 * (B' + 1))) (by positivity)
  have hψM : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) ψ := sa12y_memSob hψcc _
  have hsub : ∀ τ ∈ Icc (0 : ℝ) t, |sobolevInnerRd m (G τ) h - sobolevInnerRd m (G τ) ψ| ≤ ε / 3 := by
    intro τ hτ
    have e := sa12y_inner_sub m (hG τ hτ).1 hψM hh
    have hcs := sa12y_inner_cs m (hG τ hτ).1 hψmem
    have h1 : Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) (fun x => ψ x - h x)) ≤
        ε / (3 * (B' + 1)) := by
      calc _ ≤ Real.sqrt ((ε / (3 * (B' + 1))) ^ 2) := Real.sqrt_le_sqrt hψS
        _ = _ := Real.sqrt_sq (by positivity)
    have h2 : Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) (G τ)) ≤ B' :=
      (hG τ hτ).2.trans (le_max_left _ _)
    have h3 : |sobolevInnerRd m (G τ) (fun x => ψ x - h x)| ≤ B' * (ε / (3 * (B' + 1))) :=
      hcs.trans (mul_le_mul h2 h1 (Real.sqrt_nonneg _) hB'0)
    rw [e] at h3
    rw [abs_sub_comm]
    refine h3.trans ?_
    rw [mul_div_assoc', div_le_div_iff₀ hden (by norm_num)]
    nlinarith [hε, hB'0]
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1 (hψcont ψ hψcc τ0 hτ0) (ε / 3) (by positivity)
  refine ⟨δ, hδ, fun τ hτ hτd => ?_⟩
  have h4 := hδ' hτ hτd
  rw [Real.dist_eq] at h4 ⊢
  have h5 := hsub τ hτ
  have h6 := hsub τ0 hτ0
  have e : sobolevInnerRd m (G τ) h - sobolevInnerRd m (G τ0) h =
      (sobolevInnerRd m (G τ) h - sobolevInnerRd m (G τ) ψ) +
      (sobolevInnerRd m (G τ) ψ - sobolevInnerRd m (G τ0) ψ) -
      (sobolevInnerRd m (G τ0) h - sobolevInnerRd m (G τ0) ψ) := by ring
  rw [e]
  calc _ ≤ |(sobolevInnerRd m (G τ) h - sobolevInnerRd m (G τ) ψ) +
        (sobolevInnerRd m (G τ) ψ - sobolevInnerRd m (G τ0) ψ)| +
        |sobolevInnerRd m (G τ0) h - sobolevInnerRd m (G τ0) ψ| := abs_sub _ _
    _ ≤ |sobolevInnerRd m (G τ) h - sobolevInnerRd m (G τ) ψ| +
        |sobolevInnerRd m (G τ) ψ - sobolevInnerRd m (G τ0) ψ| +
        |sobolevInnerRd m (G τ0) h - sobolevInnerRd m (G τ0) ψ| := by
          gcongr; exact abs_add_le _ _
    _ < ε := by linarith
-- END SA12.L18

end HRS.MH.AdjointRd.Phase2SA12Limit
