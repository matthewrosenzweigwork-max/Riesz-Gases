import HRS.Sections.Sec5
import HRS.Stochastic.DualityProof
import HRS.Stochastic.QuadraticVariation
import HRS.Sections.Q40bAux1
import HRS.Sections.Q40bAux2
import HRS.Sections.Q40bAux3
import HRS.Sections.Q40bAux4
import HRS.Sections.Q40bAux5
import HRS.Sections.Q40bAux6
import HRS.Sections.Q40bAux7
import HRS.Sections.Q40bAux8
import HRS.Sections.Q40bAux9

/-!
# Packet Q40b, part 10: the comparison inequality for one particle system

`q40b_master`: for the `p`-tuple of tests `φ_a` and times `t_a ≥ 0`,
`ofReal 𝖽_{C²}(law(⟨φ_a, ζ_N^{t_a}⟩)_a, law(⟨U^{0,t_a}φ_a, ζ_N^∘⟩ + G_a)_a) ≤ ∑_a E|𝓡_N(t_a,φ_a)| +
(1/2) C_br √(2(H + log 2)/N)`, where `H` bounds the two relative entropies and `C_br` depends only on the
adjoint gradient decay constants (TeX proof of `C:prop:criterion`: centered duality identity, `L¹` bound of
the remainder, conditional Gaussian interpolation with the bracket error of `P:eq:noneq-trace`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section
namespace HRS.Q40b

variable {d N : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

section Perturb

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {p : ℕ}

theorem q40b_smoothDist_perturb {A B : Ω → (ℝ^p)} (hA : AEMeasurable A P) (hB : AEMeasurable B P) :
    ENNReal.ofReal (smoothDist 2 (law P A) (law P B)) ≤ ∫⁻ ω, ‖A ω - B ω‖ₑ ∂P := by
  by_cases hT : ∫⁻ ω, ‖A ω - B ω‖ₑ ∂P = ⊤
  · rw [hT]; exact le_top
  have hmeas : AEStronglyMeasurable (fun ω => ‖A ω - B ω‖) P :=
    ((hA.sub hB).aestronglyMeasurable).norm
  have hint : Integrable (fun ω => ‖A ω - B ω‖) P :=
    ⟨hmeas, by
      unfold HasFiniteIntegral
      simpa using lt_top_iff_ne_top.2 hT⟩
  have hreal : smoothDist 2 (law P A) (law P B) ≤ ∫ ω, ‖A ω - B ω‖ ∂P := by
    refine Real.iSup_le (fun Φ => ?_) (integral_nonneg fun ω => norm_nonneg _)
    obtain ⟨hΦ, hb, hc⟩ := Φ.2
    have hΦ1 : Φ.1 ∈ CbUnitBall (ℝ^p) 1 := cbUnitBall_mono Φ.2
    have hΦc : Continuous Φ.1 := hΦ.continuous
    have hbd : ∀ y, |Φ.1 y| ≤ 1 := fun y => abs_apply_le_of_mem Φ.2 y
    have hi : ∀ Y : Ω → (ℝ^p), AEMeasurable Y P → Integrable (fun ω => Φ.1 (Y ω)) P := fun Y hY =>
      Integrable.of_bound (hΦc.measurable.comp_aemeasurable hY).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun ω => by simpa using hbd (Y ω))
    have e1 : ∫ z, Φ.1 z ∂(law P A) = ∫ ω, Φ.1 (A ω) ∂P :=
      integral_map hA hΦc.aestronglyMeasurable
    have e2 : ∫ z, Φ.1 z ∂(law P B) = ∫ ω, Φ.1 (B ω) ∂P :=
      integral_map hB hΦc.aestronglyMeasurable
    rw [e1, e2, ← integral_sub (hi A hA) (hi B hB), ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono ((hi A hA).sub (hi B hB)).norm hint fun ω => ?_
    exact norm_sub_le_of_mem_one hΦ1 _ _
  calc ENNReal.ofReal (smoothDist 2 (law P A) (law P B))
      ≤ ENNReal.ofReal (∫ ω, ‖A ω - B ω‖ ∂P) := ENNReal.ofReal_le_ofReal hreal
    _ = ∫⁻ ω, ‖A ω - B ω‖ₑ ∂P := by
        have := integral_norm_eq_lintegral_enorm (μ := P) (f := fun ω => A ω - B ω)
          (hA.sub hB).aestronglyMeasurable
        rw [this, ENNReal.ofReal_toReal hT]

end Perturb


section Master

variable {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {p : ℕ}

theorem q40b_master (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (hN : 2 ≤ N) [NeZero N] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hsol : ∀ T : ℝ, 0 ≤ T → IsStrongSolution P htr.dyn T X₀ W X)
    (hfilt : IsFilteredSolution P ℱ W' W X) {H₁ : ℝ} (hH₁ : 0 ≤ H₁)
    (hentQ : ∀ r : ℝ, 0 ≤ r → relEntropy (P.map (X r.toNNReal))
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ r))) ≤ ENNReal.ofReal H₁)
    (hentP : ∀ r : ℝ, 0 ≤ r → relEntropy (P.map (X r.toNNReal))
      (Measure.pi fun _ : Fin N => withDensityReal (ρ r)) ≤ ENNReal.ofReal H₁)
    (t : Fin p → ℝ) (ht : ∀ a, 0 ≤ t a) (φ : Fin p → Torus d → ℝ)
    (hφ : ∀ a, Torus.IsSmooth (φ a)) (Ca : Fin p → ℝ) (m : ℝ) (hC0 : ∀ a, 0 ≤ Ca a) (hm : 0 < m)
    (hclass : ∀ a, ∀ τ : ℝ, 0 ≤ τ → ∃ F : ℝ → Torus d → ℝ,
      IsClassicalAdjointSolution htr.dyn ρ τ (φ a) F ∧
        ∀ r ∈ Set.Icc 0 τ, propagator htr.dyn ρ r τ (φ a) = F r)
    (hgrad : ∀ a, ∀ τ : ℝ, 0 ≤ τ → ∀ r ∈ Set.Icc 0 τ, ∀ x,
      ‖Torus.grad (propagator htr.dyn ρ r τ (φ a)) x‖ ≤ Ca a * Real.exp (-m * (τ - r)))
    (G : Ω → (ℝ^p)) (hGm : Measurable G)
    (hG : law P G = multivariateGaussian 0 (noiseCovMatrix htr.dyn ρ β⁻¹ t φ))
    (hind : IndepFun (X 0) G P) :
    ENNReal.ofReal (smoothDist 2
        (law P fun ω => (WithLp.toLp 2 fun a => zetaStat P X (t a) (φ a) ω : ℝ^p))
        (law P fun ω => (WithLp.toLp 2 fun a =>
          zetaStat P X 0 (propagator htr.dyn ρ 0 (t a) (φ a)) ω + G ω a : ℝ^p))) ≤
      ∑ a, ∫⁻ ω, ENNReal.ofReal |integratedRemainder htr.dyn ρ P X (t a) (φ a) ω| ∂P +
        ENNReal.ofReal ((1 / 2) * (∑ a, ∑ b, 2 * β⁻¹ * Ca a * Ca b / (2 * m)) *
          Real.sqrt (2 * (H₁ + Real.log 2) / N)) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hN0 : 0 < N := by omega
  choose F hFcl hFp using fun a => hclass a (t a) (ht a)
  set T0 : ℝ := ∑ a, t a with hT0
  have hT0nn : 0 ≤ T0 := Finset.sum_nonneg fun a _ => ht a
  have htT : ∀ a, t a ≤ T0 := fun a =>
    Finset.single_le_sum (f := t) (fun a _ => ht a) (Finset.mem_univ a)
  set D := htr.dyn with hDdef
  have hXm : ∀ r : ℝ≥0, Measurable (X r) := fun r => (hfilt.adapted r).mono (ℱ.le _) le_rfl
  -- progressive integrands
  have hΨ : ∀ a, IsProgressiveL2 P ℱ (empiricalNoiseIntegrand D (t a) (F a) X) := fun a =>
    isProgressiveL2_empiricalNoiseIntegrand hfilt.progressive (ht a) (hFcl a).isC12Test
  have hΦ : ∀ a, IsProgressiveL2 P ℱ (qPhi D t F X a) := fun a => (hΨ a).smul (Real.sqrt N)
  have hvec := vectorItoIntegral_isVectorMartingaleWithCovariation hfilt.brownian (qPhi D t F X) hΦ T0
  -- the bracket data
  obtain ⟨c₀, hc₀, Λ, hΛ⟩ := q40b_rho_bounds hd1 htr
  have hBr : Br D ρ t F (fun a r x => -(backwardGenerator D (ρ r) (F a r) x)) Ca m :=
    { t0 := ht
      hF := fun a => (hFcl a).isC12Test
      hC0 := hC0
      hm := hm
      grad := fun a σ hσ x => by
        rw [← hFp a σ hσ]; exact hgrad a (t a) (ht a) σ hσ x
      rhoJ := fun T => q40b_jointCont hd1 htr T
      rhoP := fun σ hσ => (hΛ σ hσ).1
      rhoC := fun σ hσ => PDE.MFLinear.continuous_of_isSmooth (hΛ σ hσ).2.1 }
  have hsb := q40b_isDet hBr T0
  have hGlaw : law P G = multivariateGaussian 0 (integratedCov T0 (qsb D ρ t F)) := by
    rw [hG, q40b_integratedCov D ρ t F htT hFp]
    rfl
  -- the initial statistic `ζ_N^∘` as a function of `X 0`
  set ψ : Fin p → Torus d → ℝ := fun a => propagator D ρ 0 (t a) (φ a) with hψdef
  have hψc : ∀ a, Continuous (ψ a) := by
    intro a
    have h1 : ψ a = F a 0 := hFp a 0 ⟨le_rfl, ht a⟩
    rw [h1]
    exact PDE.MFAux.continuous_of_isCk (PDE.ClassicalAux.isCk_of_le (by norm_num)
      ((hFcl a).c2 0 ⟨le_rfl, ht a⟩))
  set Zf : Config d N → (ℝ^p) := fun x => WithLp.toLp 2 fun a => Real.sqrt N *
    ((1 / (N : ℝ)) * ∑ i, ψ a (x i) - pair (meanEmpirical (P.map (X 0))) (ψ a)) with hZf
  have hZfm : Measurable Zf := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp (measurable_pi_iff.2 fun a => ?_)
    refine measurable_const.mul (Measurable.sub (measurable_const.mul ?_) measurable_const)
    exact Finset.measurable_sum _ fun i _ => (hψc a).measurable.comp (measurable_pi_apply i)
  have hZeq : (fun ω => (WithLp.toLp 2 fun a => zetaStat P X 0 (ψ a) ω : ℝ^p)) = fun ω => Zf (X 0 ω) := by
    funext ω
    simp only [hZf, zetaStat, Real.toNNReal_zero]
  have hZmeas : Measurable[ℱ 0] (fun ω => Zf (X 0 ω)) :=
    @Measurable.comp Ω (Config d N) (ℝ^p) (ℱ 0) _ _ Zf (X 0) hZfm (hfilt.adapted 0)
  have hZind : IndepFun (fun ω => Zf (X 0 ω)) G P := hind.comp hZfm measurable_id
  -- the a.s. identity, componentwise
  set Mv := vectorItoIntegral P ℱ W' (qPhi D t F X) with hMv
  set R : Fin p → Ω → ℝ := fun a ω => integratedRemainder D ρ P X (t a) (φ a) ω with hR
  have hid : ∀ a, ∀ᵐ ω ∂P, zetaStat P X (t a) (φ a) ω = zetaStat P X 0 (ψ a) ω +
      Real.sqrt N * itoIntegral P ℱ W' (empiricalNoiseIntegrand D (t a) (F a) X) (t a) ω - R a ω :=
    fun a => q40b_ae_identity hd htr hN hsol hfilt (ht a) (hφ a) (hFcl a) (hFp a)
      (fun r hr => hentQ r hr.1)
  have hstop : ∀ a, ∀ᵐ ω ∂P, itoIntegral P ℱ W' (empiricalNoiseIntegrand D (t a) (F a) X) T0 ω =
      itoIntegral P ℱ W' (empiricalNoiseIntegrand D (t a) (F a) X) (t a) ω := by
    intro a
    refine q40b_ito_stop hfilt.brownian (hΨ a) (ht a) (htT a) fun s' ω k hs => ?_
    unfold empiricalNoiseIntegrand
    have : s' ∉ Set.Icc 0 (t a) := fun h => absurd h.2 (not_le.2 hs)
    simp [this]
  have hsm : ∀ a, ∀ᵐ ω ∂P, ∀ τ : ℝ, itoIntegral P ℱ W' (qPhi D t F X a) τ ω =
      Real.sqrt N * itoIntegral P ℱ W' (empiricalNoiseIntegrand D (t a) (F a) X) τ ω :=
    fun a => itoIntegral_smul hfilt.brownian (hΨ a) (Real.sqrt N)
  have hAE : ∀ᵐ ω ∂P, ∀ a, zetaStat P X (t a) (φ a) ω = zetaStat P X 0 (ψ a) ω + Mv T0 ω a - R a ω := by
    have h1 := ae_all_iff.2 hid
    have h2 := ae_all_iff.2 hstop
    have h3 := ae_all_iff.2 hsm
    filter_upwards [h1, h2, h3] with ω a1 a2 a3 a
    rw [a1 a]
    have : Mv T0 ω a = Real.sqrt N * itoIntegral P ℱ W' (empiricalNoiseIntegrand D (t a) (F a) X) (t a) ω := by
      show itoIntegral P ℱ W' (qPhi D t F X a) T0 ω = _
      rw [a3 a T0, a2 a]
    rw [this]
  -- measurability of the statistics
  have hζm : ∀ (τ : ℝ) (ψ' : Torus d → ℝ), Continuous ψ' →
      Measurable (fun ω => zetaStat P X τ ψ' ω) := by
    intro τ ψ' hψ'
    unfold zetaStat
    refine measurable_const.mul (Measurable.sub (measurable_const.mul ?_) measurable_const)
    exact Finset.measurable_sum _ fun i _ => hψ'.measurable.comp ((measurable_pi_apply i).comp (hXm _))
  have hφc : ∀ a, Continuous (φ a) := fun a => PDE.MFLinear.continuous_of_isSmooth (hφ a)
  have hMvm : AEMeasurable (Mv T0) P :=
    (hvec.sq_int T0 ⟨hT0nn, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hAm : Measurable (fun ω => (WithLp.toLp 2 fun a => zetaStat P X (t a) (φ a) ω : ℝ^p)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun a => hζm (t a) (φ a) (hφc a))
  have hZvm : Measurable (fun ω => Zf (X 0 ω)) := hZfm.comp (hXm 0)
  have hBm : AEMeasurable (fun ω => Zf (X 0 ω) + Mv T0 ω) P := hZvm.aemeasurable.add hMvm
  have hCeq : (fun ω => (WithLp.toLp 2 fun a => zetaStat P X 0 (propagator htr.dyn ρ 0 (t a) (φ a)) ω +
      G ω a : ℝ^p)) = fun ω => Zf (X 0 ω) + G ω := by
    funext ω
    ext a
    have := congrFun hZeq ω
    have h2 := congrArg (fun v : ℝ^p => v a) this
    simp only [hψdef] at h2
    simp only [PiLp.add_apply]
    rw [← h2]
  rw [hCeq]
  -- the remainder is a.e. a measurable function
  have hRm : ∀ a, AEMeasurable (fun ω => ENNReal.ofReal |R a ω|) P := by
    intro a
    have hIm : Measurable (fun ω => itoIntegral P ℱ W' (empiricalNoiseIntegrand D (t a) (F a) X) (t a) ω) :=
      (adapted_itoIntegral P ℱ W' _ (t a)).mono (ℱ.le _) le_rfl
    have hGm' : Measurable (fun ω => zetaStat P X 0 (ψ a) ω +
        Real.sqrt N * itoIntegral P ℱ W' (empiricalNoiseIntegrand D (t a) (F a) X) (t a) ω -
        zetaStat P X (t a) (φ a) ω) :=
      ((hζm 0 (ψ a) (hψc a)).add (measurable_const.mul hIm)).sub (hζm (t a) (φ a) (hφc a))
    have hmeasR : AEMeasurable (R a) P :=
      hGm'.aemeasurable.congr ((hid a).mono fun ω h => by beta_reduce; linarith [h])
    exact ENNReal.measurable_ofReal.comp_aemeasurable hmeasR.abs
  -- the two steps of the comparison
  set Avec : Ω → (ℝ^p) := fun ω => (WithLp.toLp 2 fun a => zetaStat P X (t a) (φ a) ω : ℝ^p) with hAvec
  set Bvec : Ω → (ℝ^p) := fun ω => Zf (X 0 ω) + Mv T0 ω with hBvec
  set Cvec : Ω → (ℝ^p) := fun ω => Zf (X 0 ω) + G ω with hCvec
  have hstep1 : ENNReal.ofReal (smoothDist 2 (law P Avec) (law P Bvec)) ≤
      ∑ a, ∫⁻ ω, ENNReal.ofReal |R a ω| ∂P := by
    refine (q40b_smoothDist_perturb hAm.aemeasurable hBm).trans ?_
    calc ∫⁻ ω, ‖Avec ω - Bvec ω‖ₑ ∂P ≤ ∫⁻ ω, ∑ a, ENNReal.ofReal |R a ω| ∂P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hAE] with ω hω
          have hcomp : ∀ a, (Avec ω - Bvec ω) a = -(R a ω) := by
            intro a
            simp only [hAvec, hBvec, PiLp.sub_apply, PiLp.add_apply]
            have := hω a
            have hZ := congrFun hZeq ω
            have hZa := congrArg (fun v : ℝ^p => v a) hZ
            simp only [hψdef] at hZa
            rw [this, ← hZa]
            ring
          rw [← ofReal_norm_eq_enorm]
          have hn : ‖Avec ω - Bvec ω‖ ≤ ∑ a, |R a ω| := by
            refine (PDE.MFLinear.norm_euclid_le_sum _).trans (le_of_eq ?_)
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [hcomp a, abs_neg]
          calc ENNReal.ofReal ‖Avec ω - Bvec ω‖ ≤ ENNReal.ofReal (∑ a, |R a ω|) :=
                ENNReal.ofReal_le_ofReal hn
            _ = ∑ a, ENNReal.ofReal |R a ω| :=
                ENNReal.ofReal_sum_of_nonneg fun a _ => abs_nonneg _
      _ = ∑ a, ∫⁻ ω, ENNReal.ofReal |R a ω| ∂P := lintegral_finset_sum' _ fun a _ => hRm a
  have hstep2 : smoothDist 2 (law P Bvec) (law P Cvec) ≤
      (1 / 2) * (∑ a, ∑ b, 2 * β⁻¹ * Ca a * Ca b / (2 * m)) *
        Real.sqrt (2 * (H₁ + Real.log 2) / N) := by
    have h1 := q40b_smoothDist_interp ℱ hT0nn hvec hsb hZmeas hGm hGlaw hZind
    have h2 := q40b_cov_bound hBr hN0 hXm hvec.sigma_meas hH₁ hentP hT0nn htT
    calc smoothDist 2 (law P Bvec) (law P Cvec) ≤ (1 / 2) * covDiscrepancyMatrix P T0
          (covMatrixProcess (qPhi D t F X)) (qsb D ρ t F) := h1
      _ ≤ (1 / 2) * ((∑ a, ∑ b, 2 * D.invβ * Ca a * Ca b / (2 * m)) *
          Real.sqrt (2 * (H₁ + Real.log 2) / N)) := by gcongr
      _ = _ := by rw [← mul_assoc]; rfl
  have htri := smoothDist_triangle 2 (law P Avec) (law P Bvec) (law P Cvec)
  calc ENNReal.ofReal (smoothDist 2 (law P Avec) (law P Cvec))
      ≤ ENNReal.ofReal (smoothDist 2 (law P Avec) (law P Bvec) + smoothDist 2 (law P Bvec) (law P Cvec)) :=
        ENNReal.ofReal_le_ofReal htri
    _ = ENNReal.ofReal (smoothDist 2 (law P Avec) (law P Bvec)) +
        ENNReal.ofReal (smoothDist 2 (law P Bvec) (law P Cvec)) :=
        ENNReal.ofReal_add (smoothDist_nonneg _ _ _) (smoothDist_nonneg _ _ _)
    _ ≤ _ := add_le_add hstep1 (ENNReal.ofReal_le_ofReal hstep2)

end Master

end HRS.Q40b
