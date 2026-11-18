import HRS.MC.SEdgeB5b

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B12

open HRS.Sec7

section Aux

variable {p : ℕ}

theorem b12_stdVec_norm (a : Fin p) : ‖stdVec (p := p) a‖ = 1 := by simp [stdVec]

theorem b12_contDiff_fderiv {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)

theorem b12_psi_contDiff {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : ContDiff ℝ 3 f) (a : Fin p) :
    ContDiff ℝ 2 (fun x => fderiv ℝ f x (stdVec a)) :=
  (b12_contDiff_fderiv hf).clm_apply contDiff_const

theorem b12_psi_memCb {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : sed_StBdd f 3) (a : Fin p) :
    MemCb 1 (fun x => fderiv ℝ f x (stdVec a)) := by
  obtain ⟨hf3, hb⟩ := hf
  refine ⟨(b12_psi_contDiff hf3 a).of_le (by norm_num), ?_⟩
  intro j hj
  obtain ⟨M, hM⟩ := hb (j + 1) (by omega) (by omega)
  refine ⟨‖(ContinuousLinearMap.apply ℝ ℝ (stdVec (p := p) a))‖ * M, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hcd : ContDiffAt ℝ j (fderiv ℝ f) x :=
    ((b12_contDiff_fderiv hf3).of_le (by exact_mod_cast (by omega : j ≤ 2))).contDiffAt
  have h1 : ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ f x (stdVec a)) x‖ ≤
      ‖(ContinuousLinearMap.apply ℝ ℝ (stdVec (p := p) a))‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ f) x‖ :=
    (ContinuousLinearMap.apply ℝ ℝ (stdVec (p := p) a)).norm_iteratedFDeriv_comp_left
      (n := j) hcd le_rfl
  have h2 : ‖iteratedFDeriv ℝ j (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ (j + 1) f x‖ :=
    norm_iteratedFDeriv_fderiv
  refine le_trans h1 ?_
  rw [h2]
  exact mul_le_mul_of_nonneg_left (hM x) (ContinuousLinearMap.opNorm_nonneg _)

theorem b12_fderiv_psi {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : ContDiff ℝ 3 f) (a c : Fin p)
    (x : EuclideanSpace ℝ (Fin p)) :
    fderiv ℝ (fun x => fderiv ℝ f x (stdVec a)) x (stdVec c) =
      iteratedFDeriv ℝ 2 f x ![stdVec c, stdVec a] := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((b12_contDiff_fderiv hf).differentiable (by norm_num)) x
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp [iteratedFDeriv_two_apply]

theorem b12_second_facts {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : sed_StBdd f 3) (a b : Fin p) :
    Continuous (fun x => iteratedFDeriv ℝ 2 f x ![stdVec b, stdVec a]) ∧
      ∃ M : ℝ, ∀ x, |iteratedFDeriv ℝ 2 f x ![stdVec b, stdVec a]| ≤ M := by
  obtain ⟨hf3, hb⟩ := hf
  constructor
  · have : (fun x => iteratedFDeriv ℝ 2 f x ![stdVec b, stdVec a]) =
        fun x => fderiv ℝ (fun x => fderiv ℝ f x (stdVec a)) x (stdVec b) :=
      funext fun x => (b12_fderiv_psi hf3 a b x).symm
    rw [this]
    have h1 : ContDiff ℝ 1 (fun x => fderiv ℝ f x (stdVec a)) :=
      (b12_psi_contDiff hf3 a).of_le (by norm_num)
    exact (h1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  · obtain ⟨M, hM⟩ := hb 2 (by norm_num) (by norm_num)
    refine ⟨M, fun x => ?_⟩
    have h := (iteratedFDeriv ℝ 2 f x).le_opNorm ![stdVec b, stdVec a]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      b12_stdVec_norm, mul_one] at h
    rw [← Real.norm_eq_abs]
    exact h.trans (hM x)

theorem b12_second_symm {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : ContDiff ℝ 3 f) (a b : Fin p)
    (x : EuclideanSpace ℝ (Fin p)) :
    iteratedFDeriv ℝ 2 f x ![stdVec a, stdVec b] = iteratedFDeriv ℝ 2 f x ![stdVec b, stdVec a] := by
  have h : IsSymmSndFDerivAt ℝ f x :=
    (hf.contDiffAt).isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num)
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact h _ _

theorem b12_Y_facts {d N : ℕ} (hN : 1 ≤ N) {w : Torus d → ℝ} (hw : Measurable w)
    (hwb : ∃ M, ∀ x, |w x| ≤ M) (Q : Measure (Config d N)) [IsProbabilityMeasure Q] :
    Measurable (sed_Y Q w) ∧ ∃ M, ∀ X, |sed_Y Q w X| ≤ M := by
  obtain ⟨Mw, hMw⟩ := hwb
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  have hPm := B5b.b5b_pair_meas hN hw
  refine ⟨measurable_const.mul (hPm.sub measurable_const), 2 * (Real.sqrt N * Mw), fun X => ?_⟩
  have hMw0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw 0)
  have hm : |∫ Y, pair (empirical Y) w ∂Q| ≤ Mw := by
    have := norm_integral_le_of_norm_le_const (μ := Q) (f := fun Y : Config d N => pair (empirical Y) w)
      (C := Mw) (Eventually.of_forall fun Y => by
        simpa [Real.norm_eq_abs] using B5b.b5b_pair_bdd hN hMw Y)
    simpa using this
  unfold sed_Y
  rw [abs_mul, abs_of_pos hsN]
  have := (abs_sub _ _).trans (add_le_add (B5b.b5b_pair_bdd hN hMw X) hm)
  nlinarith

theorem b12_A_facts {d N : ℕ} (hN : 1 ≤ N) {v : Fin d → Torus d → ℝ}
    (hv : ∀ j, Torus.IsSmooth (v j)) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Measurable (fun X : Config d N => sed_A v φ X) ∧ ∃ M, ∀ X : Config d N, |sed_A v φ X| ≤ M := by
  have hpdc : ∀ k, Continuous (Torus.partialDeriv k φ) := fun k =>
    HRS.Q66.q66_cont_of_smooth (HRS.Q66.q66_isSmooth_partialDeriv hφ k)
  have hdriftc : Continuous (sed_drift v φ) := by
    unfold sed_drift
    exact continuous_finset_sum _ fun k _ => (HRS.Q66.q66_cont_of_smooth (hv k)).mul (hpdc k)
  refine ⟨B5b.b5b_pair_meas hN hdriftc.measurable, ?_⟩
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hdriftc.continuousOn
  exact ⟨M, fun X => B5b.b5b_pair_bdd hN (fun x => by simpa using hM x (Set.mem_univ _)) X⟩

end Aux

section Master

variable {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
  {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
include hd hs0 hs hβ hρ

theorem sed_B12_master_proof {N : ℕ} (hN : 1 ≤ N) {p : ℕ} {φ : Fin p → Torus d → ℝ}
    (hφ : ∀ a, Torus.IsSmooth (φ a)) {r : Fin p → Torus d → ℝ}
    (hr : ∀ a, Torus.IsSmooth (r a)) {v : Fin p → Fin d → Torus d → ℝ}
    (hv : ∀ a j, Torus.IsSmooth (v a j))
    (hdiv : ∀ a x, ∑ j, Torus.partialDeriv j (fun y => ρ y * v a j y) x = -(ρ x * r a x))
    (hresp : ∀ a x, r a x + β * Kop (periodicRiesz d s) (withDensityReal ρ) (r a) x =
      projMean (withDensityReal ρ) (φ a) x)
    (hint : ∀ a, Integrable
      (fun X : Config d N => modulatedEnergy (Q66.q66_hv d s (v a)) X (withDensityReal ρ))
      (sed_Q d s N β ρ))
    {F f : EuclideanSpace ℝ (Fin p) → ℝ} (hFc : Continuous F) (hFb : ∃ M, ∀ z, |F z| ≤ M)
    (hf : sed_StBdd f 3)
    (hstein : ∀ x, ∑ a, ∑ b, sed_Cmat d s β ρ φ a b * iteratedFDeriv ℝ 2 f x ![stdVec a, stdVec b] -
        ∑ a, x a * fderiv ℝ f x (stdVec a) =
      F x - ∫ z, F z ∂(multivariateGaussian 0 (sed_Cmat d s β ρ φ))) :
    ∫ X, F (centeredStat (sed_Q d s N β ρ) φ X) ∂(sed_Q d s N β ρ) -
        ∫ z, F z ∂(multivariateGaussian 0 (sed_Cmat d s β ρ φ)) =
      ∑ a, ∑ b, ∫ X, (sed_Cmat d s β ρ φ a b - sed_A (v a) (φ b) X) *
          iteratedFDeriv ℝ 2 f (centeredStat (sed_Q d s N β ρ) φ X) ![stdVec b, stdVec a]
          ∂(sed_Q d s N β ρ) +
        β / Real.sqrt N * ∑ a, ∫ X, sed_B d s ρ β (v a) X *
          fderiv ℝ f (centeredStat (sed_Q d s N β ρ) φ X) (stdVec a) ∂(sed_Q d s N β ρ) := by
  haveI hQ : IsProbabilityMeasure (sed_Q d s N β ρ) := B5a.b5a_Q_prob hd hs0 hs hβ hρ hN
  set Q := sed_Q d s N β ρ with hQdef
  set C := sed_Cmat d s β ρ φ with hCdef
  set c0 : ℝ := ∫ z, F z ∂(multivariateGaussian 0 C) with hc0
  have hφc : ∀ a, Continuous (φ a) := fun a => HRS.Q66.q66_cont_of_smooth (hφ a)
  have hWm : Measurable (centeredStat Q φ) := by
    unfold centeredStat
    exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun a =>
      measurable_const.mul ((B5b.b5b_pair_meas hN (hφc a).measurable).sub measurable_const))
  have hYW : ∀ X a, centeredStat Q φ X a = sed_Y Q (φ a) X := fun _ _ => rfl
  -- integrability facts
  have hI2 : ∀ a b, Integrable (fun X => iteratedFDeriv ℝ 2 f (centeredStat Q φ X) ![stdVec b, stdVec a]) Q := by
    intro a b
    obtain ⟨hc, M, hM⟩ := b12_second_facts hf a b
    exact Integrable.of_bound (hc.measurable.comp hWm).aestronglyMeasurable M
      (Eventually.of_forall fun X => by simpa [Real.norm_eq_abs] using hM _)
  have hIA : ∀ a b, Integrable (fun X => sed_A (v a) (φ b) X *
      iteratedFDeriv ℝ 2 f (centeredStat Q φ X) ![stdVec b, stdVec a]) Q := by
    intro a b
    obtain ⟨hc, M, hM⟩ := b12_second_facts hf a b
    obtain ⟨hAm, MA, hMA⟩ := b12_A_facts (N := N) hN (hv a) (hφ b)
    refine Integrable.of_bound (hAm.mul (hc.measurable.comp hWm)).aestronglyMeasurable (MA * M)
      (Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hMA X) (hM _) (abs_nonneg _) ((abs_nonneg _).trans (hMA X))
  have hψm : ∀ a, Measurable (fun X => fderiv ℝ f (centeredStat Q φ X) (stdVec a)) := by
    intro a
    exact (((b12_psi_memCb hf a).1.continuous).measurable).comp hWm
  have hψb : ∀ a, ∃ M, ∀ X, |fderiv ℝ f (centeredStat Q φ X) (stdVec a)| ≤ M := by
    intro a
    obtain ⟨M0, hM0⟩ := (b12_psi_memCb hf a).2 0 (Nat.zero_le _)
    refine ⟨M0, fun X => ?_⟩
    have := hM0 ⟨centeredStat Q φ X, rfl⟩
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using this
  have hIY : ∀ a, Integrable (fun X => sed_Y Q (φ a) X *
      fderiv ℝ f (centeredStat Q φ X) (stdVec a)) Q := by
    intro a
    obtain ⟨hYm, MY, hMY⟩ := b12_Y_facts hN (hφc a).measurable
      (HRS.Q66.q66_bound_of_smooth (hφ a)) Q
    obtain ⟨M, hM⟩ := hψb a
    refine Integrable.of_bound (hYm.mul (hψm a)).aestronglyMeasurable (MY * M)
      (Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hMY X) (hM X) (abs_nonneg _) ((abs_nonneg _).trans (hMY X))
  have hFi : Integrable (fun X => F (centeredStat Q φ X)) Q := by
    obtain ⟨M, hM⟩ := hFb
    exact Integrable.of_bound (hFc.measurable.comp hWm).aestronglyMeasurable M
      (Eventually.of_forall fun X => by simpa [Real.norm_eq_abs] using hM _)
  -- Step 1: integrate the Stein equation
  have h1 : ∫ X, F (centeredStat Q φ X) ∂Q - c0 =
      ∑ a, ∑ b, C a b * ∫ X, iteratedFDeriv ℝ 2 f (centeredStat Q φ X) ![stdVec b, stdVec a] ∂Q -
        ∑ a, ∫ X, sed_Y Q (φ a) X * fderiv ℝ f (centeredStat Q φ X) (stdVec a) ∂Q := by
    have hpt : ∀ X : Config d N, F (centeredStat Q φ X) - c0 =
        ∑ a, ∑ b, C a b * iteratedFDeriv ℝ 2 f (centeredStat Q φ X) ![stdVec b, stdVec a] -
          ∑ a, sed_Y Q (φ a) X * fderiv ℝ f (centeredStat Q φ X) (stdVec a) := by
      intro X
      rw [← hstein (centeredStat Q φ X)]
      congr 1
      · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [b12_second_symm hf.1 a b]
    have hL : ∫ X, (F (centeredStat Q φ X) - c0) ∂Q = ∫ X, F (centeredStat Q φ X) ∂Q - c0 := by
      rw [integral_sub hFi (integrable_const c0)]
      simp
    have hS1 : Integrable (fun X : Config d N => ∑ a, ∑ b, C a b *
        iteratedFDeriv ℝ 2 f (centeredStat Q φ X) ![stdVec b, stdVec a]) Q :=
      integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hI2 a b).const_mul (C a b)
    have hS2 : Integrable (fun X : Config d N => ∑ a, sed_Y Q (φ a) X *
        fderiv ℝ f (centeredStat Q φ X) (stdVec a)) Q :=
      integrable_finsetSum _ fun a _ => hIY a
    rw [← hL]
    simp_rw [hpt]
    rw [integral_sub hS1 hS2]
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => (hI2 a b).const_mul (C a b)),
      integral_finsetSum _ (fun a _ => hIY a)]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ (fun b _ => (hI2 a b).const_mul (C a b))]
    exact Finset.sum_congr rfl fun b _ => integral_const_mul _ _
  -- Step 2: B5b for each a
  have h2 : ∀ a, ∫ X, sed_Y Q (φ a) X * fderiv ℝ f (centeredStat Q φ X) (stdVec a) ∂Q =
      ∑ c, ∫ X, sed_A (v a) (φ c) X *
        iteratedFDeriv ℝ 2 f (centeredStat Q φ X) ![stdVec c, stdVec a] ∂Q -
      β / Real.sqrt N * ∫ X, sed_B d s ρ β (v a) X *
        fderiv ℝ f (centeredStat Q φ X) (stdVec a) ∂Q := by
    intro a
    have := B5b.sed_B5b_stein_centred_proof hd hs0 hs hβ hρ hN (hr a) (hv a) (hdiv a) (hresp a)
      (hint a) hφ (ψ := fun x => fderiv ℝ f x (stdVec a)) (b12_psi_memCb hf a)
    have hcongr : ∑ c, ∫ X, sed_A (v a) (φ c) X *
          fderiv ℝ (fun x => fderiv ℝ f x (stdVec a)) (centeredStat Q φ X) (stdVec c) ∂Q =
        ∑ c, ∫ X, sed_A (v a) (φ c) X *
          iteratedFDeriv ℝ 2 f (centeredStat Q φ X) ![stdVec c, stdVec a] ∂Q := by
      refine Finset.sum_congr rfl fun c _ => ?_
      refine integral_congr_ae (Eventually.of_forall fun X => ?_)
      simp only [b12_fderiv_psi hf.1]
    rw [this, hcongr]
  -- Step 3: assemble
  rw [h1]
  simp_rw [h2]
  have h3 : ∀ a b, ∫ X, (C a b - sed_A (v a) (φ b) X) *
      iteratedFDeriv ℝ 2 f (centeredStat Q φ X) ![stdVec b, stdVec a] ∂Q =
      C a b * ∫ X, iteratedFDeriv ℝ 2 f (centeredStat Q φ X) ![stdVec b, stdVec a] ∂Q -
      ∫ X, sed_A (v a) (φ b) X *
        iteratedFDeriv ℝ 2 f (centeredStat Q φ X) ![stdVec b, stdVec a] ∂Q := by
    intro a b
    simp_rw [sub_mul]
    rw [integral_sub ((hI2 a b).const_mul _) (hIA a b), integral_const_mul]
  simp_rw [h3]
  simp only [Finset.sum_sub_distrib, Finset.mul_sum]
  ring

end Master


end HRS.MC.SEdge.B12
