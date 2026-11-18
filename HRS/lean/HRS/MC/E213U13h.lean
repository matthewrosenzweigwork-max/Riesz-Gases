import HRS.MC.E213U13g
import HRS.MC.S7PICMain

/-!
# Packet e213u13, file h: first chaos elements have centred Gaussian laws; first chaos of path-valued fields
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U13

section GaussLimit

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- An `L²` limit (in the `lintegral` sense) of centred Gaussians is a centred Gaussian. -/
theorem gaussian_of_L2_limit {f : Ω → ℝ} {fn : ℕ → Ω → ℝ} (hf : AEStronglyMeasurable f P)
    (hfn : ∀ n, MemLp (fn n) 2 P) (hg : ∀ n, ∃ v : ℝ≥0, P.map (fn n) = gaussianReal 0 v)
    (hlim : Tendsto (fun n => ∫⁻ ω, ‖fn n ω - f ω‖ₑ ^ (2 : ℝ) ∂P) atTop (𝓝 0)) :
    ∃ v : ℝ≥0, P.map f = gaussianReal 0 v := by
  have hsub : ∀ n, AEStronglyMeasurable (fun ω => fn n ω - f ω) P := fun n =>
    ((hfn n).aestronglyMeasurable).sub hf
  have h2 := (tendsto_lintegral_iff_eLpNorm hsub (by norm_num : (0 : ℝ) < 2)).1 hlim
  simp only [ENNReal.ofReal_ofNat] at h2
  have hfin : ∀ᶠ n in atTop, eLpNorm (fun ω => fn n ω - f ω) 2 P < ∞ :=
    h2.eventually (gt_mem_nhds ENNReal.zero_lt_top)
  obtain ⟨n0, hn0⟩ := hfin.exists
  have hf2 : MemLp f 2 P := by
    have h1 : MemLp (fun ω => fn n0 ω - f ω) 2 P := hn0
    have := (hfn n0).sub h1
    refine this.ae_eq (Eventually.of_forall fun ω => ?_)
    simp
  have hdist : Tendsto (fun n => dist ((hfn n).toLp (fn n)) (hf2.toLp f)) atTop (𝓝 0) := by
    have h3 : ∀ n, ENNReal.ofReal (dist ((hfn n).toLp (fn n)) (hf2.toLp f)) =
        eLpNorm (fun ω => fn n ω - f ω) 2 P := fun n => by
      rw [← eLpNorm_sub_eq_dist ((hfn n).toLp (fn n)) hf2]
      refine eLpNorm_congr_ae ?_
      filter_upwards [(hfn n).coeFn_toLp] with ω h
      simp [h]
    have h4 : Tendsto (fun n => ENNReal.ofReal (dist ((hfn n).toLp (fn n)) (hf2.toLp f))) atTop (𝓝 0) := by
      simp_rw [h3]; exact h2
    have h5 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h4
    simpa [Function.comp_def] using h5
  have hlimLp : Tendsto (fun n => (hfn n).toLp (fn n)) atTop (𝓝 (hf2.toLp f)) :=
    tendsto_iff_dist_tendsto_zero.2 hdist
  have hmem : ∀ n, (hfn n).toLp (fn n) ∈ {z : Lp ℝ 2 P | ∃ v : ℝ≥0, P.map (z : Ω → ℝ) = gaussianReal 0 v} := by
    intro n
    obtain ⟨v, hv⟩ := hg n
    refine ⟨v, ?_⟩
    rw [Measure.map_congr (MemLp.coeFn_toLp (hfn n))]
    exact hv
  obtain ⟨v, hv⟩ := isClosed_gaussian.mem_of_tendsto hlimLp (Eventually.of_forall hmem)
  refine ⟨v, ?_⟩
  rw [← hv]
  exact Measure.map_congr (MemLp.coeFn_toLp hf2).symm

end GaussLimit

section FirstChaosLaw

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}

theorem xi_hasGaussianLaw (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i)) (N : ℕ) :
    HasGaussianLaw (fun ω (i : Fin N) => ξ i ω) P := by
  have hX2 : iIndepFun (fun (i : Fin N) => ξ i) P := hξ.1.precomp Fin.val_injective
  refine iIndepFun.hasGaussianLaw (fun i => ?_) hX2
  haveI : IsGaussian (P.map (ξ i)) := by
    have : P.map (ξ i) = gaussianReal 0 1 := hξ.2 i
    rw [this]; infer_instance
  exact IsGaussian.hasGaussianLaw (hm i).aemeasurable

theorem xi_linear_gauss (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i)) (N : ℕ) (c : ℕ → ℝ) :
    ∃ v : ℝ≥0, P.map (fun ω => ∑ i ∈ Finset.range N, ξ i ω * c i) = gaussianReal 0 v := by
  classical
  have hX := xi_hasGaussianLaw hξ hm N
  set L : (Fin N → ℝ) →L[ℝ] ℝ := ∑ j : Fin N, c j • (ContinuousLinearMap.proj j : (Fin N → ℝ) →L[ℝ] ℝ) with hL
  have hG := hX.map L
  have hfun : (L ∘ fun ω (j : Fin N) => ξ j ω) = fun ω => ∑ i ∈ Finset.range N, ξ i ω * c i := by
    funext ω
    simp only [hL, Function.comp_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [Finset.sum_range]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hfun] at hG
  have hmean : ∫ ω, ∑ i ∈ Finset.range N, ξ i ω * c i ∂P = 0 := by
    rw [integral_finset_sum]
    · simp [integral_mul_const, integral_xi hξ hm]
    · intro i _
      exact ((memLp_xi hξ hm i).integrable (by norm_num)).mul_const _
  refine ⟨(Var[fun ω => ∑ i ∈ Finset.range N, ξ i ω * c i; P]).toNNReal, ?_⟩
  rw [hG.map_eq_gaussianReal, hmean]

theorem law_gaussian_of_inFirstChaos {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i)) {W : Ω → B} (h : InFirstChaos P ξ 2 W) :
    IsCenteredGaussian (law P W) := by
  classical
  obtain ⟨hW, n, c, hlim⟩ := h
  have hWm : AEMeasurable W P := hW.aemeasurable
  have key : ∀ L : StrongDual ℝ B, ∃ v : ℝ≥0, P.map (fun ω => L (W ω)) = gaussianReal 0 v := by
    intro L
    have hlim' := tendsto_clm_lintegral (P := P) L (by norm_num : (0 : ℝ) < 2)
      (f := fun m ω => (∑ i ∈ Finset.range (n m), ξ i ω • c m i) - W ω) hlim
    refine gaussian_of_L2_limit (fn := fun m ω => ∑ i ∈ Finset.range (n m), ξ i ω * L (c m i))
      (L.continuous.comp_aestronglyMeasurable hW) (fun m => ?_) (fun m => ?_) ?_
    · exact memLp_finset_sum _ fun i _ => (memLp_xi hξ hm i).mul_const _
    · exact xi_linear_gauss hξ hm (n m) (fun i => L (c m i))
    · refine hlim'.congr fun m => ?_
      refine lintegral_congr fun ω => ?_
      simp [map_sub, map_sum, map_smul]
  refine ⟨?_, fun L => ?_⟩
  · have : IsProbabilityMeasure (P.map W) := (Measure.isProbabilityMeasure_map_iff hWm).2 inferInstance
    refine isGaussian_of_map_eq_gaussianReal fun L => ?_
    obtain ⟨v, hv⟩ := key L
    refine ⟨0, v, ?_⟩
    rw [AEMeasurable.map_map_of_aemeasurable L.continuous.aemeasurable hWm]
    exact hv
  · obtain ⟨v, hv⟩ := key L
    show ∫ z, L z ∂(P.map W) = 0
    rw [integral_map hWm L.continuous.aestronglyMeasurable]
    have := integral_map (μ := P) (φ := fun ω => L (W ω)) (f := fun x : ℝ => x)
      (L.continuous.measurable.comp_aemeasurable hWm) aestronglyMeasurable_id
    simp only [id] at this
    rw [← this, hv, integral_id_gaussianReal]

end FirstChaosLaw

section PathChaos

open HRS HRS.Sec7 HRS.MC.Sec7.S7PIC

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem pathproj_data (r R : ℝ) (hR : 0 < R) :
    ∃ (Pn : ℕ → PathSpace d r R →L[ℝ] PathSpace d r R) (S : ℕ → Finset (ℕ × ℕ × NonzeroLattice d))
      (ℓ : ℕ × ℕ × NonzeroLattice d → StrongDual ℝ (PathSpace d r R))
      (b : ℕ → ℕ × ℕ × NonzeroLattice d → PathSpace d r R),
      (∀ n x, ‖Pn n x‖ ≤ ‖x‖) ∧ (∀ x, Tendsto (fun n => Pn n x) atTop (𝓝 x)) ∧
      (∀ n x, Pn n x = ∑ s ∈ S n, ℓ s x • b n s) ∧
      ∀ s, ∃ (t : Set.Icc (0 : ℝ) R) (k : NonzeroLattice d), ∀ x, ℓ s x = NegSobolev.fourierCoeff (PathSpace.at' x t) k := by
  classical
  obtain ⟨Pj, hPj, hnorm, hlim, -⟩ := projection_strong_proof (d := d) r R hR
  refine ⟨Pj, fun n => ((Finset.range (2 ^ n + 1)) ×ˢ S7PIC_box d n).image (fun p => (n, p.1, p.2)),
    fun s => S7PIC_lf r R (S7PIC_node R hR.le s.1 s.2.1) s.2.2,
    fun n s => S7PIC_vpath r R s.1 s.2.1 s.2.2, fun n x => ?_, hlim, fun n x => ?_, fun s => ?_⟩
  · exact ((Pj n).le_opNorm x).trans (by nlinarith [hnorm n, norm_nonneg x, (Pj n).opNorm_nonneg])
  · rw [hPj, S7PIC_projPoly_eq_sum hR.le n x, Finset.sum_image]
    · rw [Fintype.sum_prod_type, Finset.sum_product]
      rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ k ∈ S7PIC_box d n,
        S7PIC_lf r R (S7PIC_node R hR.le n i) k x • S7PIC_vpath r R n i k)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_coe_sort (S7PIC_box d n) (fun k => S7PIC_lf r R (S7PIC_node R hR.le n i) k x •
        S7PIC_vpath r R n i k)]
    · intro p _ p' _ h
      simp only [Prod.mk.injEq, true_and] at h
      exact Prod.ext h.1 h.2
  · exact ⟨S7PIC_node R hR.le s.1 s.2.1, s.2.2, fun x => S7PIC_lf_apply _ _ x⟩

theorem inFirstChaos_path {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i)) {r R : ℝ}
    (hR : 0 < R) {W : Ω → PathSpace d r R} (hW : AEStronglyMeasurable W P)
    (hWr : ∀ q : ℝ, 1 ≤ q → MemLp W (ENNReal.ofReal q) P)
    (hcoord : ∀ (t : Set.Icc (0 : ℝ) R) (k : NonzeroLattice d),
      InQ1 hξ hm (fun ω => NegSobolev.fourierCoeff (PathSpace.at' (W ω) t) k))
    {q : ℝ} (hq : 2 ≤ q) : InFirstChaos P ξ q W := by
  obtain ⟨Pn, S, ℓ, b, hPn, hlim, hfin, hs⟩ := pathproj_data (d := d) r R hR
  refine inFirstChaos_of_approx hξ hm hW hq (lt_add_one q) (hWr (q + 1) (by linarith)) Pn hPn hlim S ℓ b
    hfin fun n s _ => ?_
  obtain ⟨t, k, h⟩ := hs s
  simp_rw [h]
  exact hcoord t k

end PathChaos

end HRS.MC.E213U13
