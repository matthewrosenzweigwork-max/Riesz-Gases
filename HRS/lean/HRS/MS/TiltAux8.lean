import HRS.MS.TiltAux7

/-!
# S4.7 packet P5c: the Stein identity for `Q = canonicalGibbs g V₀ N γ`

`s47_stein_id` (copy of `s46_stein_id`): for a corrector `χ` of `φ` (in the sense of `s47_star`), a `C¹` functional `F` of the
configuration with bounded `F, dF`, `P = s47_P`, `ν = firstMarginal P`:
`E[(μ_N(φ) - ν(φ)) F] = E[R F] + (γ N)⁻¹ E[dF(∇χ(x_1), …, ∇χ(x_N))]`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S47

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s47_stein_id (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ} {q γ C c BU BB Cs : ℝ}
    {Bd : Euc d → Euc d} (hq : 0 < q) (hγ : 0 < γ) (hN : 2 ≤ N) (hT : TRef d s ρ q C c BU BB Bd)
    (hS : S47Static d s ρ γ Cs N) {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ) {B1 B2 : ℝ}
    (hB1 : ∀ x, ‖gradient χ x‖ ≤ B1) (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2)
    {φ : Euc d → ℝ} (hφm : Measurable φ) {Bφ : ℝ} (hBφ : ∀ x, |φ x| ≤ Bφ) {c0 : ℝ}
    (hstar : ∀ᵐ x ∂(volume : Measure (Euc d)), Laplacian.laplacian χ x - q * ⟪x, gradient χ x⟫ +
      ⟪Bd x + γ • gradient (convMeasure (rieszKernel d s) (withDensityReal ρ)) x, gradient χ x⟫ -
      γ * ∫ y, commutatorKernel d s (gradient χ) x y ∂(withDensityReal ρ) = -γ * φ x + c0)
    {F : EucConfig d N → ℝ} (hF : ContDiff ℝ 1 F) {BF DF : ℝ} (hBF : ∀ X, |F X| ≤ BF)
    (hDF : ∀ X, ‖fderiv ℝ F X‖ ≤ DF) :
    ∫ X, (pair (empirical X) φ - pair (s47_nu d s ρ γ N) φ) * F X ∂(s47_P d s ρ γ N) =
      ∫ X, ((pair (empirical X) (fun x => (∫ y, commutatorKernel d s (gradient χ) x y
          ∂(withDensityReal ρ)) - ∫ y, commutatorKernel d s (gradient χ) x y
          ∂(s47_nu d s ρ γ N)) -
        pair (s47_nu d s ρ γ N)
          (fun x => (∫ y, commutatorKernel d s (gradient χ) x y ∂(withDensityReal ρ)) -
            ∫ y, commutatorKernel d s (gradient χ) x y
              ∂(s47_nu d s ρ γ N))) -
        (1 / 2) * (centeredPairFunctional (commutatorKernel d s (gradient χ)) X
            (s47_nu d s ρ γ N) -
          ∫ X', centeredPairFunctional (commutatorKernel d s (gradient χ)) X'
            (s47_nu d s ρ γ N)
            ∂(s47_P d s ρ γ N))) * F X
        ∂(s47_P d s ρ γ N) +
      (γ * N)⁻¹ * ∫ X, fderiv ℝ F X (fun k => gradient χ (X k))
        ∂(s47_P d s ρ γ N) := by
  have hd1 : 1 ≤ d := by omega
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set P := s47_P d s ρ γ N with hPdef
  set μ := withDensityReal ρ with hμdef
  set v := gradient χ with hvdef
  set h := commutatorKernel d s v with hhdef
  haveI hP : IsProbabilityMeasure P := hS.prob
  set ν := firstMarginal P with hνdef
  haveI hνprob : IsProbabilityMeasure ν := by
    have : ν = P.map (fun X : EucConfig d N => X ⟨0, by omega⟩) := by
      rw [hνdef]; unfold firstMarginal; rw [dif_pos (by omega)]
    rw [this]
    constructor
    rw [Measure.map_apply (measurable_pi_apply _) MeasurableSet.univ]
    simp
  have hv1 : ContDiff ℝ 1 v := s45_contDiff_gradient hχ
  have hvd : Differentiable ℝ v := hv1.differentiable (by norm_num)
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  have hBφ0 : 0 ≤ Bφ := (abs_nonneg _).trans (hBφ 0)
  have hBF0 : 0 ≤ BF := (abs_nonneg _).trans (hBF 0)
  have hDF0 : 0 ≤ DF := (norm_nonneg _).trans (hDF 0)
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  set Λ : ℝ≥0 := ⟨B2, hB20⟩ with hΛdef
  have hLip : LipschitzWith Λ v := lipschitzWith_of_nnnorm_fderiv_le hvd (fun x => by
    have := hB2 x
    rw [← NNReal.coe_le_coe, coe_nnnorm]; exact this)
  have hsym : ∀ x y, h x y = h y x := HRS.MS.Comm.comm_symm v
  have hhm : Measurable (Function.uncurry h) := HRS.MS.Comm.comm_meas (s := s) v hv1.continuous.measurable
  obtain ⟨φN, hφNm, hνeq, hφNb, -, -⟩ := hS.marg
  obtain ⟨Bh, hBh0, hBh⟩ := s47_Hbounds hd hs0 hsd hT hLip hφNb hφNm ν hνeq
  haveI hμprob : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  -- row functions
  set Hd : Euc d → ℝ := fun x => (∫ y, h x y ∂μ) - ∫ y, h x y ∂ν with hHd
  have hHm_meas : Measurable fun x => ∫ y, h x y ∂μ :=
    (hhm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have hHn_meas : Measurable fun x => ∫ y, h x y ∂ν :=
    (hhm.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have hHd_meas : Measurable Hd := hHm_meas.sub hHn_meas
  have hHd_bd : ∀ x, |Hd x| ≤ 2 * Bh := fun x => by
    obtain ⟨h1, h2⟩ := hBh x
    calc |Hd x| ≤ |∫ y, h x y ∂μ| + |∫ y, h x y ∂ν| := abs_sub _ _
      _ ≤ 2 * Bh := by linarith
  -- the pair functional
  set D : EucConfig d N → ℝ := fun X => centeredPairFunctional h X ν with hD
  have hDm : Measurable D := HRS.MS.Wr.wr14a_measurable_D hhm ν
  have hDint : Integrable D P := by
    obtain ⟨-, hq⟩ := hS.comm Λ v hLip
    have hlt : evariance D P < ⊤ := lt_of_le_of_lt hq.2.2 ENNReal.ofReal_lt_top
    exact ((evariance_lt_top_iff_memLp hDm.aestronglyMeasurable).1 hlt).integrable one_le_two
  set ED : ℝ := ∫ X, D X ∂P with hED
  -- centred statistics
  have hφint : ∀ f : Euc d → ℝ, Measurable f → ∀ {B : ℝ}, (∀ x, |f x| ≤ B) →
      Integrable (fun X : EucConfig d N => pair (empirical X) f - pair ν f) P := by
    intro f hf B hB
    refine Integrable.of_bound ((s45_measurable_pair_empirical hN1 hf).sub measurable_const).aestronglyMeasurable
      (2 * B) (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs]
    have h1 := s45_abs_pair_empirical_le hN1 hB X
    have h2 : |pair ν f| ≤ B := HRS.MS.Tc5.tc5_pair_le (fun x => by rw [Real.norm_eq_abs]; exact hB x)
    calc _ ≤ |pair (empirical X) f| + |pair ν f| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  have hφmean : ∀ f : Euc d → ℝ, Measurable f → ∀ {B : ℝ}, (∀ x, |f x| ≤ B) →
      ∫ X, (pair (empirical X) f - pair ν f) ∂P = 0 := by
    intro f hf B hB
    have hint1 : Integrable (fun X : EucConfig d N => pair (empirical X) f) P :=
      Integrable.of_bound (s45_measurable_pair_empirical hN1 hf).aestronglyMeasurable B
        (Filter.Eventually.of_forall fun X => by
          rw [Real.norm_eq_abs]; exact s45_abs_pair_empirical_le hN1 hB X)
    rw [integral_sub hint1 (integrable_const _), s45_E_pair_empirical hN1 hS.exch hf hB, integral_const]
    simp only [probReal_univ, one_smul]
    exact sub_self _
  have hHdB : ∀ x, |Hd x| ≤ 2 * Bh := hHd_bd
  have hXpI := hφint φ hφm hBφ
  have hRbI := hφint Hd hHd_meas hHd_bd
  have hDc : Integrable (fun X => D X - ED) P := hDint.sub (integrable_const _)
  have hRpI : Integrable (fun X : EucConfig d N =>
      (pair (empirical X) Hd - pair ν Hd) - (1 / 2) * (D X - ED)) P := hRbI.sub (hDc.const_mul _)
  have hERp : ∫ X, ((pair (empirical X) Hd - pair ν Hd) - (1 / 2) * (D X - ED)) ∂P = 0 := by
    rw [integral_sub hRbI (hDc.const_mul _), hφmean Hd hHd_meas hHd_bd, integral_const_mul,
      integral_sub hDint (integrable_const _), integral_const]
    simp [hED]
  have hEXp := hφmean φ hφm hBφ
  -- the generator functional
  set Uc : Euc d → ℝ := convMeasure (rieszKernel d s) (withDensityReal ρ) with hUc
  set w : Euc d → ℝ := fun x => (q / γ) * ⟪x, v x⟫ - γ⁻¹ * ⟪Bd x + γ • gradient Uc x, v x⟫ with hw
  have hγw : ∀ x, γ * w x = q * ⟪x, v x⟫ - ⟪Bd x + γ • gradient Uc x, v x⟫ := by
    intro x; simp only [hw]; field_simp
  set S1 : EucConfig d N → ℝ := fun X => (∑ k, Laplacian.laplacian χ (X k)) -
    γ * (∑ k, w (X k)) -
    (γ / N) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), h (X i) (X j) with hS1
  set K0 : ℝ := c0 - γ * pair ν φ + γ * pair ν Hd - (γ / 2) * ED +
    (γ / 2) * ∫ x, ∫ y, h x y ∂ν ∂ν with hK0
  have hA : ∀ᵐ X ∂P, S1 X = N * (-γ * (pair (empirical X) φ - pair ν φ) +
      γ * ((pair (empirical X) Hd - pair ν Hd) - (1 / 2) * (D X - ED))) + N * K0 := by
    have hstar' : ∀ᵐ x ∂(volume : Measure (Euc d)), Laplacian.laplacian χ x - γ * w x -
        γ * ∫ y, h x y ∂μ = -γ * φ x + c0 := by
      filter_upwards [hstar] with x hx
      rw [hγw x]; linarith
    have hst := s45_ae_P (g := rieszKernel d s) (V := s47_V0 d s ρ γ) (β := γ) (N := N)
      (E := fun x => Laplacian.laplacian χ x - γ * w x - γ * ∫ y, h x y ∂μ = -γ * φ x + c0)
      hstar'
    filter_upwards [hst] with X hX
    exact s45_claimA hN1 hsym (ν := ν) (Lap := Laplacian.laplacian χ) (w := w)
      (Hm := fun x => ∫ y, h x y ∂μ) (φ := φ) (c0 := c0) (ED := ED) X hX
  have hGint : Integrable (fun X : EucConfig d N => N * (-γ * (pair (empirical X) φ - pair ν φ) +
      γ * ((pair (empirical X) Hd - pair ν Hd) - (1 / 2) * (D X - ED))) + N * K0) P :=
    (((hXpI.const_mul (-γ)).add (hRpI.const_mul γ)).const_mul (N : ℝ)).add (integrable_const _)
  have hS1int : Integrable S1 P := hGint.congr (hA.mono fun X hX => hX.symm)
  -- the Gibbs identity in expectation form
  have hgm : Measurable (rieszKernel d s : Euc d → ℝ) := by
    rw [← movtr_gEps_zero d s]; exact movtr_gEps_measurable s 0
  have hVm : Measurable (s47_V0 d s ρ γ : Euc d → ℝ) :=
    (measurable_const.mul (Real.measurable_log.comp hT.smooth.continuous.measurable)).sub
      hT.Usmooth.continuous.measurable
  have hW : ∀ (G : EucConfig d N → ℝ), ContDiff ℝ 1 G → ∀ {BG DG : ℝ}, (∀ X, |G X| ≤ BG) →
      (∀ X, ‖fderiv ℝ G X‖ ≤ DG) →
      ∫ X, (S1 X * G X + fderiv ℝ G X (fun k => v (X k))) ∂P = 0 := by
    intro G hG BG DG hBG hDG
    have hI := s47_gibbs_ibp hd1 hs0 hq hγ hT hN1 hv1 hB1 hB2 hG hBG hDG
    rw [hPdef, s45_integral_P hgm hVm hP]
    have hpt : ∀ X : EucConfig d N, (S1 X * G X + fderiv ℝ G X (fun k => v (X k))) *
        Real.exp (-γ * canonicalHamiltonian (rieszKernel d s) (s47_V0 d s ρ γ) X) =
        (((∑ k, s45_div v (X k)) * G X + fderiv ℝ G X (fun k => v (X k))) -
        G X * (∑ i, (q * ⟪X i, v (X i)⟫ - (⟪Bd (X i), v (X i)⟫ + γ * ⟪gradient Uc (X i), v (X i)⟫)) +
          γ * ((1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          ⟪rieszKernelGrad d s (X i - X j), v (X i) - v (X j)⟫))) *
        Real.exp (-γ * canonicalHamiltonian (rieszKernel d s) (s47_V0 d s ρ γ) X) := by
      intro X
      congr 1
      have e1 : ∑ k, s45_div v (X k) = ∑ k, Laplacian.laplacian χ (X k) :=
        Finset.sum_congr rfl fun k _ => s45_div_gradient hχ (X k)
      have e2 : ∀ i j, ⟪rieszKernelGrad d s (X i - X j), v (X i) - v (X j)⟫ = h (X i) (X j) :=
        fun i j => real_inner_comm _ _
      simp only [e1, e2, hS1]
      have e3 : γ * ∑ k, w (X k) = ∑ k, (q * ⟪X k, v (X k)⟫ - (⟪Bd (X k), v (X k)⟫ +
          γ * ⟪gradient Uc (X k), v (X k)⟫)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hγw]
        simp only [inner_add_left, real_inner_smul_left]
      have : (γ / N) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), h (X i) (X j) =
          γ * ((1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), h (X i) (X j)) := by ring
      rw [this, e3]; ring
    simp_rw [hpt]
    rw [hI, mul_zero]
  -- `F = 1`: `E S₁ = 0`, hence `K₀ = 0`
  have h1 : ∫ X, S1 X ∂P = 0 := by
    have := hW (fun _ => (1 : ℝ)) contDiff_const (BG := 1) (DG := 0) (fun _ => by simp) (fun _ => by simp)
    simpa using this
  have hfAB : Integrable (fun X : EucConfig d N => -γ * (pair (empirical X) φ - pair ν φ) +
      γ * ((pair (empirical X) Hd - pair ν Hd) - (1 / 2) * (D X - ED))) P :=
    (hXpI.const_mul (-γ)).add (hRpI.const_mul γ)
  have hES : ∫ X, S1 X ∂P = N * K0 := by
    rw [integral_congr_ae hA, integral_add (hfAB.const_mul (N : ℝ)) (integrable_const _),
      integral_const_mul, integral_add (hXpI.const_mul (-γ)) (hRpI.const_mul γ), integral_const_mul,
      integral_const_mul, hEXp, hERp]
    simp
  have hK0z : K0 = 0 := by
    have : (N : ℝ) * K0 = 0 := hES.symm.trans h1
    exact (mul_eq_zero.1 this).resolve_left hN0.ne'
  -- general `F`
  have hFm : AEStronglyMeasurable F P := hF.continuous.aestronglyMeasurable
  have hXF : Integrable (fun X => (pair (empirical X) φ - pair ν φ) * F X) P :=
    hXpI.mul_bdd hFm (c := BF) (Filter.Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hBF X)
  have hRF : Integrable (fun X => ((pair (empirical X) Hd - pair ν Hd) - (1 / 2) * (D X - ED)) * F X) P :=
    hRpI.mul_bdd hFm (c := BF) (Filter.Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hBF X)
  have hSF : Integrable (fun X => S1 X * F X) P :=
    hS1int.mul_bdd hFm (c := BF) (Filter.Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hBF X)
  have hdF : Integrable (fun X : EucConfig d N => fderiv ℝ F X (fun k => v (X k))) P := by
    refine Integrable.of_bound ?_ (DF * B1) (Filter.Eventually.of_forall fun X => ?_)
    · exact ((hF.continuous_fderiv one_ne_zero).clm_apply
        (continuous_pi fun k => hv1.continuous.comp (continuous_apply k))).aestronglyMeasurable
    · calc ‖fderiv ℝ F X (fun k => v (X k))‖ ≤ ‖fderiv ℝ F X‖ * ‖(fun k => v (X k) : EucConfig d N)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ DF * B1 := mul_le_mul (hDF X) ((pi_norm_le_iff_of_nonneg hB10).2 fun k => hB1 _)
            (norm_nonneg _) hDF0
  have hWF := hW F hF hBF hDF
  rw [integral_add hSF hdF] at hWF
  have hSFeq : ∫ X, S1 X * F X ∂P = N * (-γ * ∫ X, (pair (empirical X) φ - pair ν φ) * F X ∂P +
      γ * ∫ X, ((pair (empirical X) Hd - pair ν Hd) - (1 / 2) * (D X - ED)) * F X ∂P) := by
    have hae : ∀ᵐ X ∂P, S1 X * F X = N * (-γ * ((pair (empirical X) φ - pair ν φ) * F X) +
        γ * (((pair (empirical X) Hd - pair ν Hd) - (1 / 2) * (D X - ED)) * F X)) := by
      filter_upwards [hA] with X hX
      rw [hX, hK0z]; ring
    rw [integral_congr_ae hae, integral_const_mul, integral_add (hXF.const_mul (-γ)) (hRF.const_mul γ),
      integral_const_mul, integral_const_mul]
  rw [hSFeq] at hWF
  have hγN : γ * (N : ℝ) ≠ 0 := by positivity
  generalize ∫ X, (pair (empirical X) φ - pair ν φ) * F X ∂P = a1 at *
  generalize ∫ X, ((pair (empirical X) Hd - pair ν Hd) - (1 / 2) * (D X - ED)) * F X ∂P = b1 at *
  generalize ∫ X, fderiv ℝ F X (fun k => v (X k)) ∂P = c1 at *
  field_simp
  linear_combination (-1 : ℝ) * hWF


end S47

end
