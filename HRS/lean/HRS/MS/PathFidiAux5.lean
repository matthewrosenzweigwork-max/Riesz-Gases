import HRS.MS.PathFidiAux4

/-!
# SA26 packet P4b: the integrated pair bounds and the covariance discrepancy
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.PathFidi

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

section Cov3

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ} {𝔈 : ℕ → ℝ}

set_option maxHeartbeats 400000 in
/-- the abstract integrated test bound for one pair `(a,b)` -/
theorem sa26_pair_int (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {m₂ : ℝ} (hm₂ : 0 ≤ m₂)
    (hm2 : PropagatedSecondMoment S R m₂) {N : ℕ} (hN : 2 ≤ N) {p : ℕ} (ts : Fin p → ℝ)
    (φ : Fin p → Euc d → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T)
    (hex : ∀ a, ∃ f, IsClassicalAdjointW (S.coeff N) (ts a) (φ a) f)
    {ℱ : Filtration ℝ (R N).mΩ} (hprog : IsProgressive ℱ (ofNNRealTime (R N).X))
    (hinj : ∀ᵐ ζ ∂(R N).P, ∀ᵐ r' ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
      Function.Injective ((R N).X (Real.toNNReal r') ζ))
    (a b : Fin p) {cc o' Λ' : ℝ} (hcc : 0 ≤ cc)
    (hpath : ∀ r' ∈ Set.Icc (0 : ℝ) S.T, ∀ X : EucConfig d N, Function.Injective X → ∀ R' : ℝ, 1 ≤ R' →
      |HRS.Whole.pair (HRS.Whole.empirical X) (sa26_hab S N ts φ a b r') -
        HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N r')) (sa26_hab S N ts φ a b r')| ≤
        cc * (R' ^ ((d : ℝ) / 2) * (smearScale d N Λ' + Real.sqrt (rieszModulatedEnergy d S.s X
            (HRS.Whole.withDensityReal (S.ρ N r')) + o')) +
          (secondMomentOf (HRS.Whole.empirical X) + secondMomentOf (HRS.Whole.withDensityReal (S.ρ N r'))) / R' ^ 2))
    (hEnn : ∀ r' ∈ Set.Icc (0 : ℝ) S.T, ∀ X : EucConfig d N, Function.Injective X →
      0 ≤ rieszModulatedEnergy d S.s X (HRS.Whole.withDensityReal (S.ρ N r')) + o')
    (hcomp : o' ≤ oNΛ d S.s C₀ Λ N) (hsm : smearScale d N Λ' ≤ (N : ℝ) ^ (-(1 : ℝ) / d))
    (hΛ'0 : 0 ≤ smearScale d N Λ') :
    ∫⁻ q, ENNReal.ofReal |sa26_Lab S R N ts φ a b q| ∂((R N).P.prod (sa26_μT S.T)) ≤
      ENNReal.ofReal (cc * wN d N (𝔈 N) m₂) := by
  classical
  have hN1 : 1 ≤ N := by omega
  have hN0 : 0 < N := by omega
  have hT : 0 < S.T := S.hT
  haveI := sa26_μT_prob hT
  have h𝔈 : 0 < 𝔈 N := hS.energy.pos N hN1
  have hXq : Measurable fun q : (R N).Ω × ℝ =>
      (R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T q.2)) q.1 :=
    (HRS.MP.RdRem.mrr_prog_meas ℱ (R N).X hprog hT.le).comp measurable_swap
  set Pt := (R N).P.prod (sa26_μT S.T) with hPt
  set Efun : (R N).Ω × ℝ → ℝ := fun q => rieszModulatedEnergy d S.s
    ((R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T q.2)) q.1)
    (HRS.Whole.withDensityReal (S.ρ N (HRS.MP.RdRem.mrrClamp S.T q.2))) + o' with hEfun
  set mq : (R N).Ω × ℝ → ℝ := fun q => secondMomentOf
    (HRS.Whole.empirical ((R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T q.2)) q.1)) +
    secondMomentOf (HRS.Whole.withDensityReal (S.ρ N (HRS.MP.RdRem.mrrClamp S.T q.2))) with hmq
  have hmm : Measurable mq := by
    refine (Q09A.measurable_secondMoment_empirical hN0 hXq).add ?_
    have := sa26_pair_rho_meas hS hN1 (fun _ y => ‖y‖ ^ 2) (by fun_prop)
    exact this.comp measurable_snd
  have hEfun0 : Measurable fun q : (R N).Ω × ℝ => rieszModulatedEnergy d S.s
      ((R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T q.2)) q.1)
      (HRS.Whole.withDensityReal (S.ρ N (HRS.MP.RdRem.mrrClamp S.T q.2))) + oNΛ d S.s C₀ Λ N := by
    have h1 : Measurable fun p : ℝ × EucConfig d N => rieszModulatedEnergy d S.s p.2
        (HRS.Whole.withDensityReal (S.ρ N (HRS.MP.RdRem.mrrClamp S.T p.1))) + oNΛ d S.s C₀ Λ N :=
      HRS.MP.RdRem.mrr_energy_meas hS hN1
    have hh := h1.comp (measurable_snd.prodMk hXq)
    exact hh
  have hEfun' := hEfun0.ennreal_ofReal
  have hEint : ∫⁻ q, ENNReal.ofReal (Efun q) ∂Pt ≤ ENNReal.ofReal (𝔈 N) := by
    calc ∫⁻ q, ENNReal.ofReal (Efun q) ∂Pt
        ≤ ∫⁻ q, ENNReal.ofReal (rieszModulatedEnergy d S.s
            ((R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T q.2)) q.1)
            (HRS.Whole.withDensityReal (S.ρ N (HRS.MP.RdRem.mrrClamp S.T q.2))) + oNΛ d S.s C₀ Λ N) ∂Pt :=
          lintegral_mono fun q => ENNReal.ofReal_le_ofReal (by simp only [hEfun]; linarith)
      _ ≤ ENNReal.ofReal (𝔈 N) := by
          refine sa26_lintegral_prod_le (R N).P hT _ hEfun' _ fun r' hr' => ?_
          have hb := hS.energy.bound N hN1 r' hr'
          simp only [HRS.MP.RdRem.mrrClamp_of_mem hr']
          exact hb
  have hmint : ∫⁻ q, ENNReal.ofReal (mq q) ∂Pt ≤ ENNReal.ofReal m₂ := by
    refine sa26_lintegral_prod_le (R N).P hT _ hmm.ennreal_ofReal _ fun r' hr' => ?_
    have hb := hm2 N hN1 r' hr'
    simp only [hmq, HRS.MP.RdRem.mrrClamp_of_mem hr']
    exact hb
  have hinj_iff : ∀ X : EucConfig d N, Function.Injective X ↔ X ∉ eucCollisionSet d N := fun X =>
    ⟨fun hX ⟨i, j, hij, h⟩ => hij (hX h), fun hX i j h => by
      by_contra hne
      exact hX ⟨i, j, hne, h⟩⟩
  have hinjP : ∀ᵐ q ∂Pt, Function.Injective
      ((R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T q.2)) q.1) := by
    have hA : MeasurableSet {q : (R N).Ω × ℝ | Function.Injective
        ((R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T q.2)) q.1)} := by
      have e : {q : (R N).Ω × ℝ | Function.Injective
          ((R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T q.2)) q.1)} =
          (fun q : (R N).Ω × ℝ => (R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T q.2)) q.1) ⁻¹'
            (eucCollisionSet d N)ᶜ := Set.ext fun q => hinj_iff _
      rw [e]
      exact hXq (HRS.MP.RdRem.mrr_measurableSet_coll N).compl
    refine sa26_ae_prod (R N).P hT hA ?_
    filter_upwards [hinj] with ζ hζ
    filter_upwards [hζ, ae_restrict_mem measurableSet_Icc] with r' hr' hrm
    show Function.Injective ((R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T r')) ζ)
    rw [HRS.MP.RdRem.mrrClamp_of_mem hrm]
    exact hr'
  have hmemP : ∀ᵐ q ∂Pt, q.2 ∈ Set.Icc (0 : ℝ) S.T := by
    refine sa26_ae_prod (R N).P hT (A := {q : (R N).Ω × ℝ | q.2 ∈ Set.Icc (0 : ℝ) S.T})
      (measurableSet_Icc.preimage measurable_snd) ?_
    exact Eventually.of_forall fun ζ => ae_restrict_mem measurableSet_Icc
  have hE : ∀ᵐ q ∂Pt, 0 ≤ Efun q :=
    hinjP.mono fun q hq => hEnn _ (HRS.MP.RdRem.mrrClamp_mem hT.le q.2) _ hq
  have hm0 : ∀ q, 0 ≤ mq q := fun q =>
    add_nonneg (Q09A.secondMomentOf_nonneg _) (Q09A.secondMomentOf_nonneg _)
  have hL : ∀ R' : ℝ, 1 ≤ R' → ∀ᵐ q ∂Pt, |sa26_Lab S R N ts φ a b q| ≤
      cc * (R' ^ ((d : ℝ) / 2) * (smearScale d N Λ' + Real.sqrt (Efun q)) + mq q / R' ^ 2) := by
    intro R' hR'
    filter_upwards [hinjP, hmemP] with q hq hm
    have hc := HRS.MP.RdRem.mrrClamp_of_mem hm
    have := hpath q.2 hm _ hq R' hR'
    simp only [sa26_Lab, hEfun, hmq, hc] at this ⊢
    exact this
  have hbound : ∀ R' : {R' : ℝ // 1 ≤ R'}, ∫⁻ q, ENNReal.ofReal |sa26_Lab S R N ts φ a b q| ∂Pt ≤
      ENNReal.ofReal (cc * (R'.1 ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 : ℝ) / d) + (𝔈 N) ^ ((1 : ℝ) / 2)) +
        m₂ / R'.1 ^ 2)) := by
    intro R'
    have hR0 : 0 < R'.1 := lt_of_lt_of_le one_pos R'.2
    refine le_trans (Q09A.lintegral_bound Pt (sa26_Lab S R N ts φ a b) Efun mq hmm cc
      (R'.1 ^ ((d : ℝ) / 2)) (smearScale d N Λ') R'.1 (𝔈 N) m₂ hcc (Real.rpow_nonneg hR0.le _) hΛ'0 hR0
      h𝔈 hm₂ hE hm0 hEint hmint (hL R'.1 R'.2)) (ENNReal.ofReal_le_ofReal ?_)
    have h2 : Real.sqrt (𝔈 N) = (𝔈 N) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
    rw [h2]
    have h3 : 0 ≤ R'.1 ^ ((d : ℝ) / 2) := Real.rpow_nonneg hR0.le _
    have := mul_le_mul_of_nonneg_left (add_le_add_right hsm ((𝔈 N) ^ ((1 : ℝ) / 2))) h3
    exact mul_le_mul_of_nonneg_left (by linarith) hcc
  unfold wN
  refine Q09A.inf_bound _ ?_ _ _ hcc hbound
  intro R'
  have hR0 : 0 < R'.1 := by have := R'.2; linarith
  have : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have : 0 ≤ (𝔈 N) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg h𝔈.le _
  positivity

end Cov3


section Cov4

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ} {𝔈 : ℕ → ℝ}

theorem sa26_ofReal_integral_le {μ : Measure ℝ} {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases h : Integrable f μ
  · exact (ofReal_integral_eq_lintegral_ofReal h (Eventually.of_forall hf)).le
  · rw [integral_undef h]
    simp

theorem sa26_Icc_to_prod {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T) (f : Ω × ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ ζ, (∫⁻ σ in Set.Icc (0 : ℝ) T, f (ζ, σ)) ∂P =
      ENNReal.ofReal T * ∫⁻ q, f q ∂(P.prod (sa26_μT T)) := by
  haveI := sa26_μT_prob hT
  have h1 : ∀ ζ : Ω, ∫⁻ σ in Set.Icc (0 : ℝ) T, f (ζ, σ) =
      ENNReal.ofReal T * ∫⁻ σ, f (ζ, σ) ∂(sa26_μT T) := fun ζ => sa26_lintegral_μT hT (fun σ => f (ζ, σ))
  rw [lintegral_congr h1, lintegral_const_mul _ hf.lintegral_prod_right', lintegral_prod _ hf.aemeasurable]

theorem sa26_lintegral_sum_sum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    {ι : Type*} [Fintype ι] (ν : Measure ℝ) [SFinite ν] (c : ℝ≥0∞) (F : ι → ι → Ω × ℝ → ℝ≥0∞)
    (hF : ∀ a b, Measurable (F a b)) :
    ∫⁻ ζ, ∫⁻ σ, ∑ a, ∑ b, c * F a b (ζ, σ) ∂ν ∂P =
      ∑ a, ∑ b, c * ∫⁻ ζ, ∫⁻ σ, F a b (ζ, σ) ∂ν ∂P := by
  have hmσ : ∀ (ζ : Ω) (a b : ι), Measurable fun σ : ℝ => F a b (ζ, σ) := fun ζ a b =>
    (hF a b).comp measurable_prodMk_left
  have hG : ∀ a b, Measurable fun ζ : Ω => ∫⁻ σ, F a b (ζ, σ) ∂ν := fun a b =>
    (hF a b).lintegral_prod_right'
  have h1 : ∀ ζ : Ω, ∫⁻ σ, ∑ a, ∑ b, c * F a b (ζ, σ) ∂ν = ∑ a, ∑ b, c * ∫⁻ σ, F a b (ζ, σ) ∂ν := by
    intro ζ
    rw [lintegral_finset_sum _ fun a _ => Finset.measurable_sum _ fun b _ => (hmσ ζ a b).const_mul c]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [lintegral_finset_sum _ fun b _ => (hmσ ζ a b).const_mul c]
    exact Finset.sum_congr rfl fun b _ => lintegral_const_mul _ (hmσ ζ a b)
  rw [lintegral_congr h1,
    lintegral_finset_sum _ fun a _ => Finset.measurable_sum _ fun b _ => (hG a b).const_mul c]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [lintegral_finset_sum _ fun b _ => (hG a b).const_mul c]
  exact Finset.sum_congr rfl fun b _ => lintegral_const_mul _ (hG a b)

/-- the covariance discrepancy from the integrated pair bounds -/
theorem sa26_covDisc_le (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} (hN : 2 ≤ N) {p : ℕ}
    (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T)
    (hex : ∀ a, ∃ f, IsClassicalAdjointW (S.coeff N) (ts a) (φ a) f)
    {ℱ : Filtration ℝ (R N).mΩ} (hprog : IsProgressive ℱ (ofNNRealTime (R N).X))
    (hsig : Measurable (Function.uncurry (killedCovMatrix (fun a => sa26_K S N ts φ (R N).X a) ts)))
    {cc : Fin p → Fin p → ℝ} {W : ℝ} (hcc : ∀ a b, 0 ≤ cc a b) (hW : 0 ≤ W)
    (hpairs : ∀ a b, ∫⁻ q, ENNReal.ofReal |sa26_Lab S R N ts φ a b q| ∂((R N).P.prod (sa26_μT S.T)) ≤
      ENNReal.ofReal (cc a b * W)) :
    covDiscrepancyMatrix (R N).P S.T (killedCovMatrix (fun a => sa26_K S N ts φ (R N).X a) ts)
      (sa26SigBar ts (sa26_G S N ts φ) (fun r' => S.ρ N (HRS.MP.RdRem.mrrClamp S.T r')) (2 * S.qN N)) ≤
      2 * S.qN N * S.T * ∑ a, ∑ b, cc a b * W := by
  classical
  have hN1 : 1 ≤ N := by omega
  have hT : 0 < S.T := S.hT
  haveI := sa26_μT_prob hT
  have hq0 : 0 ≤ 2 * S.qN N := by
    have := sa26_qN_nonneg S N
    positivity
  set P := (R N).P with hP
  set Sg := killedCovMatrix (fun a => sa26_K S N ts φ (R N).X a) ts with hSg
  set sb := sa26SigBar ts (sa26_G S N ts φ) (fun r' => S.ρ N (HRS.MP.RdRem.mrrClamp S.T r'))
    (2 * S.qN N) with hsb
  have hGm : ∀ a, Measurable fun q : ℝ × Euc d => sa26_G S N ts φ a q.1 q.2 := fun a =>
    sa26_G_meas ts φ a (hts a).1 (hex a)
  have hρm := HRS.MP.RdRem.mrr_rho_meas hS hN1
  have hsbm : Measurable sb := sa26_sigBar_meas hGm hρm
  set Fz : (R N).Ω → ℝ → ℝ := fun ζ σ => s1Norm (Sg σ ζ - sb σ) with hFz
  have hFnn : ∀ ζ σ, 0 ≤ Fz ζ σ := fun ζ σ => traceNormMatrix_nonneg _
  have hFm : Measurable fun q : (R N).Ω × ℝ => Fz q.1 q.2 := by
    refine measurable_traceNormMatrix (fun q : (R N).Ω × ℝ => Sg q.2 q.1 - sb q.2) (fun i j => ?_)
    have h1 : Measurable fun q : (R N).Ω × ℝ => Sg q.2 q.1 := hsig.comp measurable_swap
    have h2 : Measurable fun q : (R N).Ω × ℝ => sb q.2 := hsbm.comp measurable_snd
    exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp h1)).sub
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp h2))
  have hgm : AEStronglyMeasurable (fun ζ => ∫ σ in Set.Icc (0 : ℝ) S.T, Fz ζ σ) P :=
    (hFm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) S.T))).aestronglyMeasurable
  unfold covDiscrepancyMatrix
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun ζ => setIntegral_nonneg measurableSet_Icc fun σ _ => hFnn ζ σ) hgm]
  -- pointwise bound of the integrand by the pair functionals
  have hpt : ∀ ζ, ∀ σ ∈ Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (Fz ζ σ) ≤
      ∑ a, ∑ b, ENNReal.ofReal (2 * S.qN N) * ENNReal.ofReal |sa26_Lab S R N ts φ a b (ζ, σ)| := by
    intro ζ σ hσ
    have hc := HRS.MP.RdRem.mrrClamp_of_mem hσ
    have hρσ : HRS.Whole.IsProbDensity (S.ρ N (HRS.MP.RdRem.mrrClamp S.T σ)) :=
      (hS.mean_field.solution N hN1).density _ (HRS.MP.RdRem.mrrClamp_mem hT.le σ)
    calc ENNReal.ofReal (Fz ζ σ) ≤ ENNReal.ofReal (∑ a, ∑ b, |(Sg σ ζ - sb σ) a b|) :=
          ENNReal.ofReal_le_ofReal (sa26_s1Norm_le_sum _)
      _ = ∑ a, ∑ b, ENNReal.ofReal |(Sg σ ζ - sb σ) a b| := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => Finset.sum_nonneg fun b _ =>
            abs_nonneg ((Sg σ ζ - sb σ) a b))]
          refine Finset.sum_congr rfl fun a _ => ?_
          exact ENNReal.ofReal_sum_of_nonneg fun b _ => abs_nonneg ((Sg σ ζ - sb σ) a b)
      _ ≤ ∑ a, ∑ b, ENNReal.ofReal (2 * S.qN N) * ENNReal.ofReal |sa26_Lab S R N ts φ a b (ζ, σ)| := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
          rw [← ENNReal.ofReal_mul hq0]
          refine ENNReal.ofReal_le_ofReal ?_
          have he := sa26_cov_entry hN1 ts φ (R N).X ζ a b σ hρσ
          rw [he]
          split_ifs
          · rw [abs_mul, abs_of_nonneg hq0]
            simp only [sa26_Lab, hc]
            exact le_rfl
          · simp only [abs_zero]
            positivity
  have hLm : ∀ a b, Measurable fun q : (R N).Ω × ℝ => ENNReal.ofReal |sa26_Lab S R N ts φ a b q| :=
    fun a b => ENNReal.measurable_ofReal.comp
      (sa26_Lab_meas hS hN1 ts φ (fun a => (hts a).1) hex hprog a b).abs
  have hnn : ∀ a b, 0 ≤ cc a b * W := fun a b => mul_nonneg (hcc a b) hW
  have hq2 : 0 ≤ 2 * S.qN N * S.T := mul_nonneg hq0 hT.le
  refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg hq2
    (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hnn a b)) ?_
  calc ∫⁻ ζ, ENNReal.ofReal (∫ σ in Set.Icc (0 : ℝ) S.T, Fz ζ σ) ∂P
      ≤ ∫⁻ ζ, (∫⁻ σ in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (Fz ζ σ)) ∂P :=
        lintegral_mono fun ζ => sa26_ofReal_integral_le fun σ => hFnn ζ σ
    _ ≤ ∫⁻ ζ, (∫⁻ σ in Set.Icc (0 : ℝ) S.T, ∑ a, ∑ b, ENNReal.ofReal (2 * S.qN N) *
          ENNReal.ofReal |sa26_Lab S R N ts φ a b (ζ, σ)|) ∂P :=
        lintegral_mono fun ζ => setLIntegral_mono' measurableSet_Icc fun σ hσ => hpt ζ σ hσ
    _ = ∑ a, ∑ b, ENNReal.ofReal (2 * S.qN N) *
          ∫⁻ ζ, (∫⁻ σ in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal |sa26_Lab S R N ts φ a b (ζ, σ)|) ∂P :=
        sa26_lintegral_sum_sum P (volume.restrict (Set.Icc (0 : ℝ) S.T)) (ENNReal.ofReal (2 * S.qN N))
          (fun a b q => ENNReal.ofReal |sa26_Lab S R N ts φ a b q|) hLm
    _ ≤ ∑ a, ∑ b, ENNReal.ofReal (2 * S.qN N) * (ENNReal.ofReal S.T * ENNReal.ofReal (cc a b * W)) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [sa26_Icc_to_prod P hT _ (hLm a b)]
        exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (hpairs a b))
    _ = ENNReal.ofReal (2 * S.qN N * S.T * ∑ a, ∑ b, cc a b * W) := by
        have e : ∀ a b, ENNReal.ofReal (2 * S.qN N) * (ENNReal.ofReal S.T * ENNReal.ofReal (cc a b * W)) =
            ENNReal.ofReal (2 * S.qN N * S.T * (cc a b * W)) := fun a b => by
          rw [← ENNReal.ofReal_mul hT.le, ← ENNReal.ofReal_mul hq0]
          congr 1; ring
        simp_rw [e]
        have e3 : 2 * S.qN N * S.T * ∑ a, ∑ b, cc a b * W =
            ∑ a, ∑ b, 2 * S.qN N * S.T * (cc a b * W) := by
          simp [Finset.mul_sum]
        rw [e3, ENNReal.ofReal_sum_of_nonneg (fun a _ =>
          Finset.sum_nonneg fun b _ => mul_nonneg hq2 (hnn a b))]
        exact Finset.sum_congr rfl fun a _ =>
          (ENNReal.ofReal_sum_of_nonneg fun b _ => mul_nonneg hq2 (hnn a b)).symm

end Cov4

end HRS.MS.PathFidi
