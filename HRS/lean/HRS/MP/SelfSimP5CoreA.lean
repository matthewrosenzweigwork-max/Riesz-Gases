import HRS.MP.SelfSimP5CoreSpec

/-!
# MP-SSP5CORE (part A): lower semicontinuity of `fisherCptW` under the Gaussian mollification

Copy of `p4m_psi_le`, `p4m_psi_cont`, `p4m_fisher_lsc` of `SelfSimP4MolLsc.lean` with the test-field class
`ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ` (the disjointness from collisions was never used).
Namespace `HRS.MP.SelfSimP5Core`, helpers `p5c_`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory Set
open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS HRS.MP.SelfSimP4
open HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP5Core

variable {d N : ℕ}

theorem p5c_psi_le {θ : ℝ} (hθ : 0 < θ) {W u : EucConfig d N → ℝ} (hW : ContDiff ℝ 1 W)
    (hu : ContDiff ℝ 1 u) (hu0 : ∀ x, 0 < u x) {ζ : EucConfig d N → EucConfig d N}
    (hζ : ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ) :
    ENNReal.ofReal (∫ X, p4m_psi (p4GibbsOf θ W) ζ X * u X) ≤ p4Diss θ W u := by
  obtain ⟨K, hKc, hKz⟩ : ∃ K : Set (EucConfig d N), IsCompact K ∧ ∀ X, X ∉ K → ζ X = 0 :=
    ⟨tsupport ζ, hζ.2, fun X hX => image_eq_zero_of_notMem_tsupport hX⟩
  have hζs : ContDiff ℝ ∞ ζ := hζ.1
  have hζc : Continuous ζ := hζs.continuous
  set e : Fin N × Fin d → EucConfig d N := fun k => configBasis d N k with he
  set ζk : Fin N × Fin d → EucConfig d N → ℝ := fun k Z => ζ Z k.1 k.2 with hζk
  have hzk : ∀ k, ContDiff ℝ ∞ (ζk k) := fun k =>
    ((EuclideanSpace.proj k.2).comp (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin N => Euc d) k.1)).contDiff.comp hζs
  have hzkc : ∀ k, Continuous (ζk k) := fun k => (hzk k).continuous
  have hzkK : ∀ k X, X ∉ K → ζk k X = 0 := fun k X hX => by simp [hζk, hKz X hX]
  have hDk : ∀ k, ContDiff ℝ 1 (ζk k) := fun k => (hzk k).of_le (by norm_num)
  have hDc : ∀ k, Continuous (fderiv ℝ (ζk k)) := fun k => (hDk k).continuous_fderiv (by simp)
  have hdzK : ∀ k X, X ∉ K → fderiv ℝ (ζk k) X = 0 := fun k X hX => by
    have hev : (ζk k) =ᶠ[𝓝 X] fun _ => (0 : ℝ) := by
      filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hX] with Z hZ
      exact hzkK k Z hZ
    rw [hev.fderiv_eq]; simp
  have hu1 : ContDiff ℝ 1 u := hu
  have hucont : Continuous u := hu.continuous
  have hu'c : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by simp)
  have hW'c : Continuous (fderiv ℝ W) := hW.continuous_fderiv (by simp)
  have hudiff : ∀ x, DifferentiableAt ℝ u x := fun x => hu.differentiable (by simp) x
  have hWdiff : ∀ x, DifferentiableAt ℝ W x := fun x => hW.differentiable (by simp) x
  have hudiff' : ∀ x, HasFDerivAt u (fderiv ℝ u x) x := fun x => (hudiff x).hasFDerivAt
  have hzdiff : ∀ k x, DifferentiableAt ℝ (ζk k) x := fun k x => (hDk k).differentiable (by simp) x
  -- compact supports
  have hcs : ∀ (f : EucConfig d N → ℝ), Continuous f → (∀ X, X ∉ K → f X = 0) → Integrable f :=
    fun f hf hz => hf.integrable_of_hasCompactSupport (HasCompactSupport.intro hKc hz)
  -- integration by parts
  have hibp : ∀ k, ∫ X, u X * fderiv ℝ (ζk k) X (e k) = -∫ X, fderiv ℝ u X (e k) * ζk k X := by
    intro k
    refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ (fun x _ => hudiff x)
      (fun x _ => hzdiff k x)
    · exact hcs _ ((hu'c.clm_apply continuous_const).mul (hzkc k)) fun X hX => by
        simp [hzkK k X hX]
    · exact hcs _ (hucont.mul ((hDc k).clm_apply continuous_const)) fun X hX => by
        simp [hdzK k X hX]
    · exact hcs _ (hucont.mul (hzkc k)) fun X hX => by simp [hzkK k X hX]
  -- the pieces
  have hdiv : ∀ X, configDivW ζ X = ∑ k, fderiv ℝ (ζk k) X (e k) := fun X => rfl
  have hζK : ∀ X, X ∉ K → ζ X = 0 := hKz
  have hdivc : Continuous (configDivW ζ) := by
    have : configDivW ζ = fun X => ∑ k, fderiv ℝ (ζk k) X (e k) := funext hdiv
    rw [this]
    exact continuous_finset_sum _ fun k _ => (hDc k).clm_apply continuous_const
  have hdivK : ∀ X, X ∉ K → configDivW ζ X = 0 := fun X hX => by
    rw [hdiv]; simp [hdzK _ X hX]
  have hnormc : Continuous fun X : EucConfig d N => ∑ i, ‖ζ X i‖ ^ 2 :=
    continuous_finset_sum _ fun i _ => (((continuous_apply i).comp hζc).norm).pow 2
  have hnormK : ∀ X, X ∉ K → ∑ i, ‖ζ X i‖ ^ 2 = 0 := fun X hX => by simp [hζK X hX]
  set P1 : EucConfig d N → ℝ := fun X => u X * configDivW ζ X with hP1
  set P2 : EucConfig d N → ℝ := fun X => fderiv ℝ u X (ζ X) with hP2
  set P3 : EucConfig d N → ℝ := fun X => u X * fderiv ℝ W X (ζ X) with hP3
  set P4 : EucConfig d N → ℝ := fun X => u X * ∑ i, ‖ζ X i‖ ^ 2 with hP4
  have iP1 : Integrable P1 := hcs _ (hucont.mul hdivc) fun X hX => by simp [hP1, hdivK X hX]
  have iP2 : Integrable P2 := hcs _ (hu'c.clm_apply hζc) fun X hX => by simp [hP2, hζK X hX]
  have iP3 : Integrable P3 := hcs _ (hucont.mul (hW'c.clm_apply hζc)) fun X hX => by
    simp [hP3, hζK X hX]
  have iP4 : Integrable P4 := hcs _ (hucont.mul hnormc) fun X hX => by simp [hP4, hnormK X hX]
  -- ∫ P1 = - ∫ P2
  have hexp2 : ∀ X, P2 X = ∑ k, fderiv ℝ u X (e k) * ζk k X := fun X => by
    simp only [hP2]
    rw [p4m_coord_expand (fderiv ℝ u X) (ζ X)]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have iA : ∀ k, Integrable (fun X => u X * fderiv ℝ (ζk k) X (e k)) := fun k =>
    hcs _ (hucont.mul ((hDc k).clm_apply continuous_const)) fun X hX => by simp [hdzK k X hX]
  have iB : ∀ k, Integrable (fun X => fderiv ℝ u X (e k) * ζk k X) := fun k =>
    hcs _ ((hu'c.clm_apply continuous_const).mul (hzkc k)) fun X hX => by simp [hzkK k X hX]
  have hI1 : ∫ X, P1 X = -∫ X, P2 X := by
    have e1 : ∀ X, P1 X = ∑ k, u X * fderiv ℝ (ζk k) X (e k) := fun X => by
      simp only [hP1]; rw [hdiv, Finset.mul_sum]
    simp_rw [e1, hexp2]
    rw [integral_finset_sum _ (fun k _ => iA k), integral_finset_sum _ (fun k _ => iB k),
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => hibp k
  -- the integral of the functional
  have hpsi : ∀ X, p4m_psi (p4GibbsOf θ W) ζ X * u X = -2 * P1 X + 2 * θ⁻¹ * P3 X - P4 X := by
    intro X
    unfold p4m_psi
    rw [p4m_fderiv_log hWdiff X]
    simp only [hP1, hP3, hP4, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  set H : EucConfig d N → ℝ := fun X => 2 * P2 X + 2 * θ⁻¹ * P3 X - P4 X with hH
  have iH : Integrable H := ((iP2.const_mul 2).add (iP3.const_mul (2 * θ⁻¹))).sub iP4
  have hint : ∫ X, p4m_psi (p4GibbsOf θ W) ζ X * u X = ∫ X, H X := by
    simp_rw [hpsi]
    have hA : Integrable (fun X => -2 * P1 X + 2 * θ⁻¹ * P3 X) :=
      (iP1.const_mul (-2)).add (iP3.const_mul (2 * θ⁻¹))
    rw [integral_sub hA iP4, integral_add (iP1.const_mul (-2)) (iP3.const_mul (2 * θ⁻¹)),
      integral_const_mul, integral_const_mul]
    simp only [hH]
    have hA2 : Integrable (fun X => 2 * P2 X + 2 * θ⁻¹ * P3 X) :=
      (iP2.const_mul 2).add (iP3.const_mul (2 * θ⁻¹))
    rw [integral_sub hA2 iP4,
      integral_add (iP2.const_mul 2) (iP3.const_mul (2 * θ⁻¹)), integral_const_mul, integral_const_mul,
      hI1]
    ring
  -- pointwise bound
  have hle : ∀ X, H X ≤ u X * ∑ k : Fin N × Fin d,
      ((u X)⁻¹ * fderiv ℝ u X (configBasis d N k) + θ⁻¹ * fderiv ℝ W X (configBasis d N k)) ^ 2 := by
    intro X
    have hux := hu0 X
    have e2 : P2 X = ∑ k, ζ X k.1 k.2 * fderiv ℝ u X (e k) := by
      simp only [hP2]; exact p4m_coord_expand (fderiv ℝ u X) (ζ X)
    have e3 : P3 X = u X * ∑ k, ζ X k.1 k.2 * fderiv ℝ W X (e k) := by
      simp only [hP3]; rw [p4m_coord_expand (fderiv ℝ W X) (ζ X)]
    have e4 : P4 X = u X * ∑ k : Fin N × Fin d, (ζ X k.1 k.2) ^ 2 := by
      simp only [hP4]; rw [p4m_norm_sq_sum]
    have hsum : H X = ∑ k : Fin N × Fin d, (2 * (ζ X k.1 k.2 * fderiv ℝ u X (e k)) +
        2 * θ⁻¹ * (u X * (ζ X k.1 k.2 * fderiv ℝ W X (e k))) - u X * (ζ X k.1 k.2) ^ 2) := by
      simp only [hH, e2, e3, e4]
      simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hsum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    set a : ℝ := ζ X k.1 k.2
    set p : ℝ := fderiv ℝ u X (e k)
    set q : ℝ := fderiv ℝ W X (e k)
    set ux : ℝ := u X
    have hw : p + θ⁻¹ * ux * q = ux * (ux⁻¹ * p + θ⁻¹ * q) := by
      field_simp
    have hsq := mul_nonneg hux.le (sq_nonneg ((ux⁻¹ * p + θ⁻¹ * q) - a))
    have e5 : 2 * (a * p) + 2 * θ⁻¹ * (ux * (a * q)) = 2 * a * (ux * (ux⁻¹ * p + θ⁻¹ * q)) := by
      rw [← hw]; ring
    rw [e5]
    nlinarith [hsq]
  -- conclusion
  rw [hint]
  refine (p4m_ofReal_integral_le iH).trans ?_
  unfold p4Diss
  exact lintegral_mono fun X => ENNReal.ofReal_le_ofReal (hle X)



theorem p5c_psi_cont {θ : ℝ} {W : EucConfig d N → ℝ} (hW : ContDiff ℝ 1 W)
    {ζ : EucConfig d N → EucConfig d N} (hζ : ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ) :
    Continuous (p4m_psi (p4GibbsOf θ W) ζ) ∧ ∃ C : ℝ, ∀ X, |p4m_psi (p4GibbsOf θ W) ζ X| ≤ C := by
  obtain ⟨K, hKc, hKz⟩ : ∃ K : Set (EucConfig d N), IsCompact K ∧ ∀ X, X ∉ K → ζ X = 0 :=
    ⟨tsupport ζ, hζ.2, fun X hX => image_eq_zero_of_notMem_tsupport hX⟩
  have hζs : ContDiff ℝ ∞ ζ := hζ.1
  have hζc : Continuous ζ := hζs.continuous
  set e : Fin N × Fin d → EucConfig d N := fun k => configBasis d N k with he
  set ζk : Fin N × Fin d → EucConfig d N → ℝ := fun k Z => ζ Z k.1 k.2 with hζk
  have hzk : ∀ k, ContDiff ℝ ∞ (ζk k) := fun k =>
    ((EuclideanSpace.proj k.2).comp (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin N => Euc d) k.1)).contDiff.comp hζs
  have hzkK : ∀ k X, X ∉ K → ζk k X = 0 := fun k X hX => by simp [hζk, hKz X hX]
  have hDk : ∀ k, ContDiff ℝ 1 (ζk k) := fun k => (hzk k).of_le (by norm_num)
  have hDc : ∀ k, Continuous (fderiv ℝ (ζk k)) := fun k => (hDk k).continuous_fderiv (by simp)
  have hdzK : ∀ k X, X ∉ K → fderiv ℝ (ζk k) X = 0 := fun k X hX => by
    have hev : (ζk k) =ᶠ[𝓝 X] fun _ => (0 : ℝ) := by
      filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hX] with Z hZ
      exact hzkK k Z hZ
    rw [hev.fderiv_eq]; simp
  have hW'c : Continuous (fderiv ℝ W) := hW.continuous_fderiv (by simp)
  have hWdiff : ∀ x, DifferentiableAt ℝ W x := fun x => hW.differentiable (by simp) x
  have hdiv : ∀ X, configDivW ζ X = ∑ k, fderiv ℝ (ζk k) X (e k) := fun X => rfl
  have hdivc : Continuous (configDivW ζ) := by
    have : configDivW ζ = fun X => ∑ k, fderiv ℝ (ζk k) X (e k) := funext hdiv
    rw [this]
    exact continuous_finset_sum _ fun k _ => (hDc k).clm_apply continuous_const
  have hdivK : ∀ X, X ∉ K → configDivW ζ X = 0 := fun X hX => by
    rw [hdiv]; simp [hdzK _ X hX]
  have hnormc : Continuous fun X : EucConfig d N => ∑ i, ‖ζ X i‖ ^ 2 :=
    continuous_finset_sum _ fun i _ => (((continuous_apply i).comp hζc).norm).pow 2
  have hpsi : p4m_psi (p4GibbsOf θ W) ζ = fun X => -2 * configDivW ζ X -
      2 * ((-θ⁻¹) * fderiv ℝ W X (ζ X)) - ∑ i, ‖ζ X i‖ ^ 2 := by
    funext X
    unfold p4m_psi
    rw [p4m_fderiv_log hWdiff X]
    simp
  have hc : Continuous (p4m_psi (p4GibbsOf θ W) ζ) := by
    rw [hpsi]
    exact ((continuous_const.mul hdivc).sub
      (continuous_const.mul (continuous_const.mul (hW'c.clm_apply hζc)))).sub hnormc
  have hcs : HasCompactSupport (p4m_psi (p4GibbsOf θ W) ζ) :=
    HasCompactSupport.intro hKc fun X hX => by
      rw [hpsi]; simp [hdivK X hX, hKz X hX]
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  exact ⟨hc, C, fun X => by simpa [Real.norm_eq_abs] using hC X⟩

/-- Lower semicontinuity of the Fisher information under the Gaussian mollification. -/
theorem p5c_fisher_lsc {θ : ℝ} (hθ : 0 < θ) {W : EucConfig d N → ℝ} (hW : ContDiff ℝ 1 W)
    (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ] {v : ℕ → ℝ} (hv : ∀ n, 0 < v n)
    (hv0 : Tendsto v atTop (𝓝 0)) :
    fisherCptW (p4GibbsOf θ W) μ ≤ liminf (fun n => p4Diss θ W (p4Mol (v n) μ)) atTop := by
  have hdef : fisherCptW (p4GibbsOf θ W) μ = ⨆ (ζ : EucConfig d N → EucConfig d N)
      (_ : ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ), ENNReal.ofReal (∫ X, p4m_psi (p4GibbsOf θ W) ζ X ∂μ) := rfl
  rw [hdef]
  refine iSup_le fun ζ => iSup_le fun hζ => ?_
  obtain ⟨hψc, C, hC⟩ := p5c_psi_cont (θ := θ) hW hζ
  haveI : ∀ n, IsProbabilityMeasure (p4m_molMeas (v n) μ) := fun n => p4m_molMeas_prob (hv n) μ
  have hlim := p4m_molMeas_tendsto μ hv hv0 hψc hC
  have hlim' := ENNReal.tendsto_ofReal hlim
  rw [← hlim'.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
  have h1 : ∫ z, p4m_psi (p4GibbsOf θ W) ζ z ∂(p4m_molMeas (v n) μ) =
      ∫ X, p4m_psi (p4GibbsOf θ W) ζ X * p4Mol (v n) μ X := by
    unfold p4m_molMeas
    rw [p4j_integral_dMeas (p4j_mol_continuous (hv n) μ).measurable
      (fun x => (p4m_mol_pos' (hv n) μ x).le)]
    exact integral_congr_ae (ae_of_all _ fun X => mul_comm _ _)
  rw [h1]
  exact p5c_psi_le hθ hW (p4m_mol_contDiff (hv n) μ) (p4m_mol_pos' (hv n) μ) hζ

end HRS.MP.SelfSimP5Core
