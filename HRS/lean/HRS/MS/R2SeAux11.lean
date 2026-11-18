import HRS.MS.R2SeAux10

/-!
# S9.9 `r2_static_edgeworth`, packet 11: Gaussian contraction and Euler identities in `ℓ²`, covariance identities

Worker S99, namespace `S99`.

* `s99_contraction`: for `f ∈ C²` with `D²f` bounded and a centered Gaussian `γ` on `ℓ²` whose coordinate covariances `C` are absolutely
  summable on `ℕ × ℕ`: `∫ D²f(x)[z,z] dγ(z) = ∑'_j ∑'_k C_{jk} D²f(x)[e_j,e_k]`;
* `s99_euler`: `Df(x)[x] = ∑'_j x_j ∂_j f(x)`;
* `s99_cov_symm`, `s99_cov_ibp`, `s99_cov_corr`: the covariance identities of the proof.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s99_seqBasis_eq (j : ℕ) : s45_seqBasis j = s45_e1 j (1 : ℝ) := by
  have h := HilbertBasis.repr_symm_single s45_seqBasis j
  exact h.symm

theorem s99_coord_hasSum (z : SeqL2) :
    HasSum (fun j => SeqL2.coord z j • s45_e1 j (1 : ℝ)) z := by
  have h := s45_seqBasis.hasSum_repr z
  convert h using 2 with j
  rw [s99_seqBasis_eq, HilbertBasis.repr_apply_apply, s45_inner_seqBasis]

theorem s99_proj_eq (n : ℕ) (z : SeqL2) :
    hilbertProj s45_seqBasis n z = ∑ j ∈ Finset.range n, SeqL2.coord z j • s45_e1 j (1 : ℝ) := by
  unfold hilbertProj
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [s45_inner_seqBasis, s99_seqBasis_eq]

theorem s99_euler {f : SeqL2 → ℝ} (x : SeqL2) :
    fderiv ℝ f x x = ∑' j, SeqL2.coord x j * pd f j x := by
  have h := (s99_coord_hasSum x).mapL (fderiv ℝ f x)
  rw [← h.tsum_eq]
  refine tsum_congr fun j => ?_
  rw [map_smul, smul_eq_mul]
  rfl

theorem s99_contraction {γ : Measure SeqL2} [IsProbabilityMeasure γ] {C : ℕ → ℕ → ℝ}
    (hγ : IsCenteredGaussianSeq γ C) (hCs : Summable fun p : ℕ × ℕ => ‖C p.1 p.2‖)
    {f : SeqL2 → ℝ} (hf : ContDiff ℝ 2 f) (x : SeqL2) :
    ∫ z, iteratedFDeriv ℝ 2 f x ![z, z] ∂γ =
      ∑' j, ∑' k, C j k * fderiv ℝ (fderiv ℝ f) x (s45_e1 k (1 : ℝ)) (s45_e1 j (1 : ℝ)) := by
  have hγG : IsGaussian γ := hγ.1.1
  set H := fderiv ℝ (fderiv ℝ f) x with hH
  have hiter : ∀ z : SeqL2, iteratedFDeriv ℝ 2 f x ![z, z] = H z z := fun z => by
    rw [iteratedFDeriv_two_apply]; rfl
  simp_rw [hiter]
  -- finite sections
  have hsec : ∀ n : ℕ, ∫ z, H (hilbertProj s45_seqBasis n z) (hilbertProj s45_seqBasis n z) ∂γ =
      ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
        C j k * H (s45_e1 k (1 : ℝ)) (s45_e1 j (1 : ℝ)) := by
    intro n
    have e : ∀ z : SeqL2, H (hilbertProj s45_seqBasis n z) (hilbertProj s45_seqBasis n z) =
        ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, (SeqL2.coord z j * SeqL2.coord z k) *
          H (s45_e1 k (1 : ℝ)) (s45_e1 j (1 : ℝ)) := by
      intro z
      rw [s99_proj_eq]
      simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    simp_rw [e]
    rw [integral_finsetSum _ fun j _ => ?_]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_finsetSum _ fun k _ => ?_]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_mul_const, (hγ.2 j k).2]
      · exact ((hγ.2 j k).1.mul_const _)
    · exact integrable_finsetSum _ fun k _ => ((hγ.2 j k).1.mul_const _)
  -- dominated convergence
  have hbound : Integrable (fun z : SeqL2 => ‖H‖ * ‖z‖ ^ 2) γ :=
    (HRS.gaussian_sqnorm_integrable (γ := γ) hγ.1).const_mul _
  have hPc : ∀ n, Continuous (hilbertProj s45_seqBasis n : SeqL2 → SeqL2) := fun n =>
    HRS.Whole.Stein.hproj_continuous s45_seqBasis n
  have hlim : Tendsto (fun n : ℕ => ∫ z, H (hilbertProj s45_seqBasis n z)
      (hilbertProj s45_seqBasis n z) ∂γ) atTop (𝓝 (∫ z, H z z ∂γ)) := by
    refine tendsto_integral_of_dominated_convergence (fun z => ‖H‖ * ‖z‖ ^ 2) (fun n => ?_) hbound
      (fun n => Filter.Eventually.of_forall fun z => ?_) (Filter.Eventually.of_forall fun z => ?_)
    · exact ((H.continuous.comp (hPc n)).clm_apply (hPc n)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, ← Real.norm_eq_abs]
      refine (H.le_opNorm₂ _ _).trans ?_
      have h1 := HRS.Whole.Stein.norm_hproj_le s45_seqBasis n z
      have h2 : ‖hilbertProj s45_seqBasis n z‖ ≤ ‖z‖ := h1
      calc ‖H‖ * ‖hilbertProj s45_seqBasis n z‖ * ‖hilbertProj s45_seqBasis n z‖
          ≤ ‖H‖ * ‖z‖ * ‖z‖ := by gcongr
        _ = ‖H‖ * ‖z‖ ^ 2 := by ring
    · have hc : Continuous fun p : SeqL2 × SeqL2 => H p.1 p.2 :=
        (H.continuous.comp continuous_fst).clm_apply continuous_snd
      exact (hc.tendsto (z, z)).comp ((s45_hproj_tendsto z).prodMk_nhds (s45_hproj_tendsto z))
  -- the series
  set fp : ℕ × ℕ → ℝ := fun p => C p.1 p.2 * H (s45_e1 p.2 (1 : ℝ)) (s45_e1 p.1 (1 : ℝ)) with hfp
  have hsumm : Summable fp := by
    refine Summable.of_norm_bounded (hCs.mul_right ‖H‖) fun p => ?_
    rw [hfp]; simp only [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (H.le_opNorm₂ _ _).trans ?_
    rw [s99_e1_norm, s99_e1_norm]; simp
  have hfin : Tendsto (fun n : ℕ => (Finset.range n) ×ˢ (Finset.range n)) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun t => ?_
    refine ⟨t.sup (fun p => max p.1 p.2) + 1, fun n hn p hp => ?_⟩
    have h1 : max p.1 p.2 ≤ t.sup (fun p => max p.1 p.2) := Finset.le_sup (f := fun p => max p.1 p.2) hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    have h2 := le_max_left p.1 p.2
    have h3 := le_max_right p.1 p.2
    constructor <;> omega
  have hsq : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
      C j k * H (s45_e1 k (1 : ℝ)) (s45_e1 j (1 : ℝ))) atTop (𝓝 (∑' p, fp p)) := by
    have := hsumm.hasSum.comp hfin
    convert this using 2 with n
    rw [Function.comp_apply, Finset.sum_product]
  have hu := tendsto_nhds_unique (hlim.congr hsec) hsq
  rw [hu, hsumm.tsum_prod]

/-! ### Covariance identities -/

section Cov

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β γ C c BU : ℝ} (hγ : 0 < γ)
  (hT : ThermalData d s a β C c BU)

include hd hs0 hsd hγ hT

theorem s99_cov_symm {φ ψ : Euc d → ℝ} (hφ : MemLp φ 2 (thermalMeasure d s a β))
    (hψ : MemLp ψ 2 (thermalMeasure d s a β)) :
    susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) γ φ ψ =
      susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) γ ψ φ := by
  have hd1 : 1 ≤ d := by omega
  haveI hprob : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  obtain ⟨L, hL⟩ := S45.s45_thermal_logmoment2 hT
  have hM : ∀ x, thermalDensity d s a β x ≤ C := fun x => (le_abs_self _).trans
    ((hT.h0 x).trans (by
      have : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖, hT.hc])
      nlinarith [hT.C0]))
  obtain ⟨K, hK⟩ : ∃ K : Lp ℝ 2 (thermalMeasure d s a β) →L[ℝ] Lp ℝ 2 (thermalMeasure d s a β),
      IsKData (thermalMeasure d s a β) (rieszKernel d s) K :=
    S45.s45_kdata hd1 hs0 hsd hT.prob hM (L := L) (fun _ => hL)
  rw [S45.s45_susceptibilityCov_eq hK hγ hφ hψ, S45.s45_susceptibilityCov_eq hK hγ hψ hφ]
  exact S45.s45_inner_Rr_comm hK hγ.le _ _

/-- `Cov(w, ψ) = ∫ w a dμ` for a bounded `C¹` observable `w` and a corrected feature `ψ` (`L_μ χ = γ a`). -/
theorem s99_cov_ibp {w ψ χ af : Euc d → ℝ} {B : ℝ} (hw : ContDiff ℝ 1 w) {Bw Dw : ℝ}
    (hBw : ∀ x, |w x| ≤ Bw) (hDw : ∀ x, ‖fderiv ℝ w x‖ ≤ Dw)
    (hψ : MemLp ψ 2 (thermalMeasure d s a β)) (hf : S46.S46Feat d s a β γ ψ χ B)
    (hgen : ∀ x, thermalGen d s a β χ x = γ * af x) :
    susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) γ w ψ =
      ∫ x, w x * af x ∂(thermalMeasure d s a β) := by
  haveI hprob : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  have hwL2 : MemLp w 2 (thermalMeasure d s a β) :=
    MemLp.of_bound hw.continuous.aestronglyMeasurable Bw
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hBw x)
  rw [s99_cov_symm hd hs0 hsd hγ hT hwL2 hψ,
    S46.s46_cov_identity hd hs0 hsd hγ hT hf.smooth hf.B1 hf.B2 hψ hf.r2 hf.corr hw hBw hDw]
  have h3 := S45.s45_ibp_mu hT hf.smooth hf.B1 hf.B2 hw hBw hDw
  have e : ∫ y, ⟪gradient χ y, gradient w y⟫ ∂(thermalMeasure d s a β) =
      ∫ y, w y * thermalGen d s a β χ y ∂(thermalMeasure d s a β) := by
    rw [h3]; congr 1; funext y; exact real_inner_comm _ _
  rw [e]
  simp_rw [hgen]
  have : ∀ y, w y * (γ * af y) = γ * (w y * af y) := fun y => by ring
  simp_rw [this]
  rw [integral_const_mul, ← mul_assoc, inv_mul_cancel₀ hγ.ne', one_mul]

/-- `Cov(w, φ') = ∫ γ⁻¹ ⟨∇χ_w, ∇φ'⟩ dμ` for a corrected observable `w`. -/
theorem s99_cov_corr {w χ φ' : Euc d → ℝ} {B : ℝ} (hw : MemLp w 2 (thermalMeasure d s a β))
    (hf : S46.S46Feat d s a β γ w χ B) (hφ' : ContDiff ℝ 1 φ') {Bφ Dφ : ℝ} (hBφ : ∀ x, |φ' x| ≤ Bφ)
    (hDφ : ∀ x, ‖fderiv ℝ φ' x‖ ≤ Dφ) :
    susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) γ w φ' =
      ∫ x, γ⁻¹ * ⟪gradient χ x, gradient φ' x⟫ ∂(thermalMeasure d s a β) := by
  rw [S46.s46_cov_identity hd hs0 hsd hγ hT hf.smooth hf.B1 hf.B2 hw hf.r2 hf.corr hφ' hBφ hDφ,
    integral_const_mul]

end Cov

end S99

end
