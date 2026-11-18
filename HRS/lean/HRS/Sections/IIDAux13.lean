import HRS.Sections.IIDAux12

/-!
# IID helper chain, part 13: finite-mode comparison with sampling density `q` and Gaussian of
covariance `ρ` (`|q - ρ| ≤ κ ρ`); coupling data and smooth distance.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.IID

section Mix

open HRS.InitialDataAux

variable {d : ℕ} {m : ℝ}

lemma w1_mvG_close {q ρ : Torus d → ℝ} (hq : IsProbDensity q) (hρ : IsProbDensity ρ)
    {κ : ℝ} (hκ : 0 ≤ κ) (hqρ : ∀ x, |q x - ρ x| ≤ κ * ρ x) (T : Finset (NonzeroLattice d))
    {N : ℕ} (hN : 1 ≤ N) :
    wassersteinE 1 (multivariateGaussian (0 : EuclideanSpace ℝ (Fin T.card))
        (∑ _i : Fin N, Yurinskii.momentMatrix
          ((withDensityReal q).map (xiVec (withDensityReal q) N (blk m T)))))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin T.card))
        (∑ _i : Fin N, Yurinskii.momentMatrix
          ((withDensityReal ρ).map (xiVec (withDensityReal ρ) N (blk m T))))) ≤
      ENNReal.ofReal (Real.sqrt (20 * κ ^ 2 * ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m)))) := by
  obtain ⟨P, hP, h1, h2, hI, h3⟩ := gaussT_close (m := m) hq hρ hκ hqρ T hN
  have hcoup : IsCoupling P _ _ := ⟨h1, h2⟩
  refine (wassersteinE_one_le_two _ _).trans ?_
  refine HRS.HilbertCLTAux.wE2_le_of_cost hcoup ?_
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · exact ENNReal.ofReal_le_ofReal h3
  · exact hI
  · exact Filter.Eventually.of_forall fun z => by positivity


lemma d2_mvG_close {q ρ : Torus d → ℝ} (hq : IsProbDensity q) (hρ : IsProbDensity ρ)
    {κ : ℝ} (hκ : 0 ≤ κ) (hqρ : ∀ x, |q x - ρ x| ≤ κ * ρ x) (T : Finset (NonzeroLattice d))
    {N : ℕ} (hN : 1 ≤ N) {Φ : EuclideanSpace ℝ (Fin T.card) → ℝ} (hΦ : ContDiff ℝ 2 Φ)
    (h0 : ∀ z, |Φ z| ≤ 1) (h1 : ∀ z, ‖fderiv ℝ Φ z‖ ≤ 1) :
    |∫ z, Φ z ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin T.card))
        (∑ _i : Fin N, Yurinskii.momentMatrix
          ((withDensityReal q).map (xiVec (withDensityReal q) N (blk m T))))) -
      ∫ z, Φ z ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin T.card))
        (∑ _i : Fin N, Yurinskii.momentMatrix
          ((withDensityReal ρ).map (xiVec (withDensityReal ρ) N (blk m T)))))| ≤
      Real.sqrt (20 * κ ^ 2 * ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m))) := by
  obtain ⟨P, hP, h1', h2', hI, h3⟩ := gaussT_close (m := m) hq hρ hκ hqρ T hN
  have hΦc : Continuous Φ := hΦ.continuous
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hlip : LipschitzWith 1 Φ :=
    lipschitzWith_of_nnnorm_fderiv_le hΦd (fun x => by rw [← NNReal.coe_le_coe]; simpa using h1 x)
  rw [← h1', ← h2', integral_map measurable_fst.aemeasurable hΦc.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable hΦc.aestronglyMeasurable]
  have hb : ∀ z : EuclideanSpace ℝ (Fin T.card) × EuclideanSpace ℝ (Fin T.card) → ℝ, True := fun _ => trivial
  have i1 : Integrable (fun z : EuclideanSpace ℝ (Fin T.card) × EuclideanSpace ℝ (Fin T.card) => Φ z.1) P :=
    Integrable.of_bound (hΦc.measurable.comp measurable_fst).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using h0 z.1)
  have i2 : Integrable (fun z : EuclideanSpace ℝ (Fin T.card) × EuclideanSpace ℝ (Fin T.card) => Φ z.2) P :=
    Integrable.of_bound (hΦc.measurable.comp measurable_snd).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using h0 z.2)
  have hnm : Measurable fun z : EuclideanSpace ℝ (Fin T.card) × EuclideanSpace ℝ (Fin T.card) => ‖z.1 - z.2‖ :=
    (measurable_fst.sub measurable_snd).norm
  have hsq : Integrable (fun z : EuclideanSpace ℝ (Fin T.card) × EuclideanSpace ℝ (Fin T.card) => ‖z.1 - z.2‖ ^ 2) P := hI
  have hn1 : Integrable (fun z : EuclideanSpace ℝ (Fin T.card) × EuclideanSpace ℝ (Fin T.card) => ‖z.1 - z.2‖) P := by
    have : MemLp (fun z : EuclideanSpace ℝ (Fin T.card) × EuclideanSpace ℝ (Fin T.card) => ‖z.1 - z.2‖) 2 P :=
      (memLp_two_iff_integrable_sq hnm.aestronglyMeasurable).2 hsq
    exact this.integrable (by norm_num)
  rw [← integral_sub i1 i2]
  calc |∫ z, (Φ z.1 - Φ z.2) ∂P| ≤ ∫ z, ‖z.1 - z.2‖ ∂P := by
        refine (abs_integral_le_integral_abs).trans (integral_mono (i1.sub i2).abs hn1 fun z => ?_)
        have := hlip.dist_le_mul z.1 z.2
        simpa [Real.dist_eq, dist_eq_norm] using this
    _ ≤ Real.sqrt (∫ z, ‖z.1 - z.2‖ ^ 2 ∂P) := by
        have := integral_mul_le_sqrt (μ := P) (f := fun z : EuclideanSpace ℝ (Fin T.card) × EuclideanSpace ℝ (Fin T.card) => ‖z.1 - z.2‖)
          (g := fun _ => (1 : ℝ)) (fun z => norm_nonneg _) (fun _ => zero_le_one) hnm.aestronglyMeasurable
          aestronglyMeasurable_const hsq (by simp)
        simpa using this
    _ ≤ _ := Real.sqrt_le_sqrt h3


theorem iid_T_d2_mix (hm : (d : ℝ) < 2 * m) {c : ℝ} (hc : 0 < c) {q ρ : Torus d → ℝ}
    (hq : IsProbDensity q) (hqc : ∀ x, c ≤ q x) (hρ : IsProbDensity ρ)
    {κ : ℝ} (hκ : 0 ≤ κ) (hqρ : ∀ x, |q x - ρ x| ≤ κ * ρ x)
    {γ : Measure (NegSobolev d m)} [IsProbabilityMeasure γ]
    (hγ : IsCenteredGaussianWithCov m γ (iidCov (withDensityReal ρ)))
    (T : Finset (NonzeroLattice d)) {N : ℕ} (hN : 1 ≤ N) :
    smoothDist 2 ((Measure.pi fun _ : Fin N => withDensityReal q).map (fld m N (withDensityReal q))) γ ≤
      8 * (∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m))) / N *
        (2 * Real.sqrt T.card * Real.sqrt N + 1) +
      Real.sqrt (20 * κ ^ 2 * ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m))) + 2 * Real.sqrt (tailR d m T) := by
  haveI : IsProbabilityMeasure (withDensityReal q) := isProb_withDensityReal hq
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  obtain ⟨B, binv, hBs, hBb, hbB, hMM, hnu, hbd⟩ := iid_setup (m := m) hc hq hqc T hN
  set S : ℝ := ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m)) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => Real.rpow_nonneg (Torus.jp_pos _).le _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have key := fm_d2 hm hγ T hN _ (gauss_law_coordVec hγ T hN)
    (J2 := 8 * S / N * (2 * Real.sqrt T.card * Real.sqrt N + 1) + Real.sqrt (20 * κ ^ 2 * S)) (by
      intro Φ' hcd h0 h1 h2
      have a := fd_C2 hBs hBb hbB hN hMM (Real.sqrt_nonneg _) hbd hcd h0 h1 h2
      rw [Real.sq_sqrt (by positivity), one_mul] at a
      rw [hnu] at a
      have b := d2_mvG_close (m := m) hq hρ hκ hqρ T hN hcd h0 h1
      calc _ ≤ |∫ z, Φ' z ∂(cpow _ N) - ∫ z, Φ' z ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin T.card))
              (∑ _i : Fin N, Yurinskii.momentMatrix
                ((withDensityReal q).map (xiVec (withDensityReal q) N (blk m T)))))| +
            |∫ z, Φ' z ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin T.card))
              (∑ _i : Fin N, Yurinskii.momentMatrix
                ((withDensityReal q).map (xiVec (withDensityReal q) N (blk m T))))) -
              ∫ z, Φ' z ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin T.card))
              (∑ _i : Fin N, Yurinskii.momentMatrix
                ((withDensityReal ρ).map (xiVec (withDensityReal ρ) N (blk m T)))))| := abs_sub_le _ _ _
        _ ≤ _ := add_le_add a b)
  linarith


theorem iid_T_coupling_mix (hm : (d : ℝ) < 2 * m) {c : ℝ} (hc : 0 < c) {q ρ : Torus d → ℝ}
    (hq : IsProbDensity q) (hqc : ∀ x, c ≤ q x) (hρ : IsProbDensity ρ)
    {κ : ℝ} (hκ : 0 ≤ κ) (hqρ : ∀ x, |q x - ρ x| ≤ κ * ρ x)
    {γ : Measure (NegSobolev d m)} [IsProbabilityMeasure γ]
    (hγ : IsCenteredGaussianWithCov m γ (iidCov (withDensityReal ρ)))
    (T : Finset (NonzeroLattice d)) {N : ℕ} (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η) :
    ∃ P : Measure (Config d N × NegSobolev d m), IsProbabilityMeasure P ∧
      P.map Prod.fst = Measure.pi (fun _ : Fin N => withDensityReal q) ∧ P.map Prod.snd = γ ∧
      ∫⁻ ω, ‖fld m N (withDensityReal q) ω.1 - ω.2‖ₑ ∂P ≤
        ENNReal.ofReal (Real.sqrt (8 * (∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m))) / N) *
          (T.card * Real.log (Real.exp 1 * N) + 2) +
          Real.sqrt (20 * κ ^ 2 * ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m))) + η +
          2 * Real.sqrt (tailR d m T)) := by
  haveI : IsProbabilityMeasure (withDensityReal q) := isProb_withDensityReal hq
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  obtain ⟨B, binv, hBs, hBb, hbB, hMM, hnu, hbd⟩ := iid_setup (m := m) hc hq hqc T hN
  set S : ℝ := ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m)) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => Real.rpow_nonneg (Torus.jp_pos _).le _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hw := w1_cpow_nuS hBs hBb hbB hN hMM (Real.sqrt_nonneg _) hbd
  rw [hnu] at hw
  have hlog : 0 ≤ Real.log (Real.exp 1 * N) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' hNpos.ne', Real.log_exp]
    have : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    linarith
  have hJ0 : 0 ≤ Real.sqrt (8 * S / N) * (T.card * Real.log (Real.exp 1 * N) + 2) +
      Real.sqrt (20 * κ ^ 2 * S) := by positivity
  have hmix := w1_mvG_close (m := m) hq hρ hκ hqρ T hN
  have hΓ := gauss_law_coordVec hγ T hN
  haveI : IsProbabilityMeasure (γ.map (coordVec T)) :=
    ⟨by rw [Measure.map_apply (continuous_coordVec T).measurable MeasurableSet.univ]; simp⟩
  have hJ : wassersteinE 1 (cpow ((withDensityReal q).map (xiVec (withDensityReal q) N (blk m T))) N)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin T.card))
        (∑ _i : Fin N, Yurinskii.momentMatrix
          ((withDensityReal ρ).map (xiVec (withDensityReal ρ) N (blk m T))))) ≤
      ENNReal.ofReal (Real.sqrt (8 * S / N) * (T.card * Real.log (Real.exp 1 * N) + 2) +
        Real.sqrt (20 * κ ^ 2 * S)) := by
    refine (wassersteinE_triangle 1 le_rfl _ (multivariateGaussian (0 : EuclideanSpace ℝ (Fin T.card))
        (∑ _i : Fin N, Yurinskii.momentMatrix
          ((withDensityReal q).map (xiVec (withDensityReal q) N (blk m T))))) _).trans ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    exact add_le_add hw hmix
  have := fm_coupling hm hγ T hN _ hΓ hJ0 hJ hη
  simpa [add_assoc] using this


theorem CB_T_mix (hm : (d : ℝ) < 2 * m) {c : ℝ} (hc : 0 < c) {q ρ : Torus d → ℝ}
    (hq : IsProbDensity q) (hqc : ∀ x, c ≤ q x) (hρ : IsProbDensity ρ)
    {κ : ℝ} (hκ : 0 ≤ κ) (hqρ : ∀ x, |q x - ρ x| ≤ κ * ρ x)
    {γ : Measure (NegSobolev d m)} [IsProbabilityMeasure γ]
    (hγ : IsCenteredGaussianWithCov m γ (iidCov (withDensityReal ρ)))
    (T : Finset (NonzeroLattice d)) {N : ℕ} (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η) :
    CB ((Measure.pi fun _ : Fin N => withDensityReal q).map (fld m N (withDensityReal q))) γ
      (Real.sqrt (8 * (∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m))) / N) *
          (T.card * Real.log (Real.exp 1 * N) + 2) +
          Real.sqrt (20 * κ ^ 2 * ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m))) + η +
          2 * Real.sqrt (tailR d m T))
      (1632 * (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) ^ 2) := by
  haveI := negSobolev_secondCountable d m
  haveI : IsProbabilityMeasure (withDensityReal q) := isProb_withDensityReal hq
  obtain ⟨P, hP, hP1, hP2, hPc⟩ := iid_T_coupling_mix hm hc hq hqc hρ hκ hqρ hγ T hN hη
  set μ := withDensityReal q with hμ
  set Z : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) with hZ
  have hF : Measurable (fld m N μ) := (continuous_fld hm hN μ).measurable
  have hm' : Measurable fun ω : Config d N × NegSobolev d m => (fld m N μ ω.1, ω.2) :=
    (hF.comp measurable_fst).prodMk measurable_snd
  have hf4 := lintegral_enorm_pow4_le (Measure.pi fun _ : Fin N => μ) (fld m N μ)
    (integrable_fld4 hm hN μ) (fourth_fld hm hN μ)
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hg4 := lintegral_enorm_pow4_le γ id
    (by simpa using HRS.EdgeAux.gaussian_integrable_pow hγ.1 4) (M := 12 * Z ^ 2)
    (by simpa using fourth_gauss hm hγ)
  simp only [id] at hg4
  refine ⟨P.map fun ω => (fld m N μ ω.1, ω.2), ⟨?_, ?_⟩, ⟨?_⟩, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hm', ← hP1, Measure.map_map hF measurable_fst]; rfl
  · rw [Measure.map_map measurable_snd hm', ← hP2]; rfl
  · rw [Measure.map_apply hm' MeasurableSet.univ]; simp
  · rw [lintegral_map (by fun_prop) hm']; exact hPc
  · rw [lintegral_map (by fun_prop) hm']
    have e1 : ∫⁻ ω, ‖fld m N μ ω.1‖ₑ ^ 4 ∂P = ∫⁻ X, ‖fld m N μ X‖ₑ ^ 4 ∂(Measure.pi fun _ : Fin N => μ) := by
      rw [← hP1, lintegral_map (by fun_prop) measurable_fst]
    have e2 : ∫⁻ ω, ‖ω.2‖ₑ ^ 4 ∂P = ∫⁻ F, ‖F‖ₑ ^ 4 ∂γ := by
      rw [← hP2, lintegral_map (by fun_prop) measurable_snd]
    have hme : Measurable fun ω : Config d N × NegSobolev d m => ‖fld m N μ ω.1‖ₑ ^ 4 :=
      ((hF.comp measurable_fst).enorm).pow_const 4
    calc ∫⁻ ω, ‖(fld m N μ ω.1, ω.2).1 - (fld m N μ ω.1, ω.2).2‖ₑ ^ 4 ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal 8 * ‖fld m N μ ω.1‖ₑ ^ 4 + ENNReal.ofReal 8 * ‖ω.2‖ₑ ^ 4) ∂P :=
          lintegral_mono fun ω => enorm_sub_pow4_le _ _
      _ = ENNReal.ofReal 8 * ∫⁻ ω, ‖fld m N μ ω.1‖ₑ ^ 4 ∂P + ENNReal.ofReal 8 * ∫⁻ ω, ‖ω.2‖ₑ ^ 4 ∂P := by
          rw [lintegral_add_left (hme.const_mul _), lintegral_const_mul _ hme,
            lintegral_const_mul _ (measurable_snd.enorm.pow_const 4)]
      _ ≤ ENNReal.ofReal 8 * ENNReal.ofReal (192 * Z ^ 2) + ENNReal.ofReal 8 * ENNReal.ofReal (12 * Z ^ 2) := by
          rw [e1, e2]; gcongr
      _ = ENNReal.ofReal (1632 * Z ^ 2) := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring

end Mix

end HRS.IID
