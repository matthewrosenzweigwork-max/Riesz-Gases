import HRS.Sections.DynCmpAux5
import HRS.Sections.DynCmpAux6

/-!
# DYNCMP: Theorem 5.4 `dynamic_comparison`, step (5a): the master inequality for one particle system

`dyncmp_master`: for one particle system (`N ≥ 2`, strong solution on `[0,T]`, filtered), entropy bounds `H(f^r|Q^r) ≤ H₁`,
`H(f^r|(μ^r)^{⊗N}) ≤ H₁` for `r ∈ [0,T]`, the pair-entropy moment bound `hpair` (uniform constant `C_f`), the adjoint data
(classical solutions, uniform gradient bound, Lipschitz bound), and a Gaussian `G` independent of `X 0`:
`d_{C²}(Law(⟨φ_a, η^{t_a}⟩), Law(⟨f_a^0, η^∘⟩ + G)) ≤ ∑_a t_a C_f (H₁ + Nδ_N)/√N + ½ C_br √(2(H₁ + log 2)/N)`.
Chain: a.s. duality identity (`dyncmp_ae_identity`) → remainder `L¹` bound (`dyncmp_R_bound`) → Gaussian comparison on the
enlargement (`dyncmp_gaussian_comparison`) → bracket error (`dyncmp_cov_bound`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open HRS.Q40b in
theorem dyncmp_master (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {T : ℝ} (hT : 0 ≤ T) (htr' : MovTraj htr.dyn T ρ)
    {N : ℕ} (hN : 2 ≤ N) [NeZero N]
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N}
    (hsol : IsStrongSolution P htr.dyn T X₀ W X) (hfilt : IsFilteredSolution P ℱ W' W X)
    {H₁ : ℝ} (hH₁ : 0 ≤ H₁)
    (hentQ : ∀ r ∈ Set.Icc (0 : ℝ) T, relEntropy (P.map (X r.toNNReal))
      (movT_Q (periodicRiesz d htr.dyn.s) htr.dyn N ρ r) ≤ ENNReal.ofReal H₁)
    (hentP : ∀ r ∈ Set.Icc (0 : ℝ) T, relEntropy (P.map (X r.toNNReal))
      (Measure.pi fun _ : Fin N => withDensityReal (ρ r)) ≤ ENNReal.ofReal H₁)
    {L Cf : ℝ} (hCf : 0 ≤ Cf)
    (hpair : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ v : Torus d → Euc d, IsLipschitzVF L v →
      Measurable (fun x : Config d N => modulatedEnergy (commKernel (periodicRieszGrad d htr.dyn.s) v) x
        (withDensityReal (ρ r))) ∧
      ∀ ν : Measure (Config d N), IsProbabilityMeasure ν →
        relEntropy ν (movT_Q (periodicRiesz d htr.dyn.s) htr.dyn N ρ r) ≠ ⊤ →
        ∫⁻ x, ENNReal.ofReal ((N : ℝ) * |modulatedEnergy (commKernel (periodicRieszGrad d htr.dyn.s) v) x
            (withDensityReal (ρ r))|) ∂ν ≤ ENNReal.ofReal Cf *
          (relEntropy ν (movT_Q (periodicRiesz d htr.dyn.s) htr.dyn N ρ r) +
            ENNReal.ofReal (N * deltaN d htr.dyn.s N)))
    {p : ℕ} (t : Fin p → ℝ) (ht : ∀ a, t a ∈ Set.Icc (0 : ℝ) T) (φ : Fin p → Torus d → ℝ)
    (hφ : ∀ a, Torus.IsSmooth (φ a)) (Ca : Fin p → ℝ) (hC0 : ∀ a, 0 ≤ Ca a)
    (hclass : ∀ a, IsClassicalAdjointSolution htr.dyn ρ (t a) (φ a)
      (fun r => propagator htr.dyn ρ r (t a) (φ a)))
    (hgrad : ∀ a, ∀ r ∈ Set.Icc 0 (t a), ∀ x,
      ‖Torus.grad (propagator htr.dyn ρ r (t a) (φ a)) x‖ ≤ Ca a)
    (hLip : ∀ a, ∀ r ∈ Set.Icc 0 (t a), IsLipschitzVF L (Torus.grad (propagator htr.dyn ρ r (t a) (φ a))))
    (G : Ω → ℝ^p) (hGm : AEMeasurable G P)
    (hG : law P G = multivariateGaussian 0 (noiseCovMatrix htr.dyn ρ β⁻¹ t φ))
    (hind : IndepFun (X 0) G P) :
    smoothDist 2
        (law P fun ω => (WithLp.toLp 2 fun a =>
          linCoord (withDensityReal (ρ (t a))) (φ a) (X (t a).toNNReal ω) : ℝ^p))
        (law P fun ω => (WithLp.toLp 2 fun a =>
          linCoord (withDensityReal (ρ 0)) (propagator htr.dyn ρ 0 (t a) (φ a)) (X 0 ω) + G ω a : ℝ^p)) ≤
      ∑ a, t a * (Cf * (H₁ + N * deltaN d htr.dyn.s N)) / Real.sqrt N +
        (1 / 2) * ((∑ a, ∑ b, 2 * β⁻¹ * (Ca a * Real.exp T) * (Ca b * Real.exp T) / (2 * 1)) *
          Real.sqrt (2 * (H₁ + Real.log 2) / N)) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hN0 : 0 < N := by omega
  set D := htr.dyn with hDdef
  set F : Fin p → ℝ → Torus d → ℝ := fun a r => propagator D ρ r (t a) (φ a) with hFdef
  have hFcl : ∀ a, IsClassicalAdjointSolution D ρ (t a) (φ a) (F a) := hclass
  have ht0 : ∀ a, 0 ≤ t a := fun a => (ht a).1
  have htT : ∀ a, t a ≤ T := fun a => (ht a).2
  have hXm : ∀ r : ℝ≥0, Measurable (X r) := fun r => (hfilt.adapted r).mono (ℱ.le _) le_rfl
  have hΨ : ∀ a, IsProgressiveL2 P ℱ (empiricalNoiseIntegrand D (t a) (F a) X) := fun a =>
    isProgressiveL2_empiricalNoiseIntegrand hfilt.progressive (ht0 a) (hFcl a).isC12Test
  have hΦ : ∀ a, IsProgressiveL2 P ℱ (qPhi D t F X a) := fun a => (hΨ a).smul (Real.sqrt N)
  have hvec := vectorItoIntegral_isVectorMartingaleWithCovariation hfilt.brownian (qPhi D t F X) hΦ T
  obtain ⟨c₀, hc₀, Λ, hΛ⟩ := q40b_rho_bounds hd1 htr
  obtain ⟨Λ3, hreg⟩ := q40b_regular hd1 htr T
  have hBr : Br D ρ t F (fun a r x => -(backwardGenerator D (ρ r) (F a r) x)) (fun a => Ca a * Real.exp T) 1 :=
    { t0 := ht0
      hF := fun a => (hFcl a).isC12Test
      hC0 := fun a => mul_nonneg (hC0 a) (Real.exp_pos _).le
      hm := one_pos
      grad := fun a σ hσ x => by
        refine (hgrad a σ hσ x).trans ?_
        have h1 : 1 ≤ Real.exp T * Real.exp (-1 * (t a - σ)) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by linarith [hσ.1, htT a])
        calc Ca a = Ca a * 1 := (mul_one _).symm
          _ ≤ Ca a * (Real.exp T * Real.exp (-1 * (t a - σ))) := mul_le_mul_of_nonneg_left h1 (hC0 a)
          _ = _ := by ring
      rhoJ := fun T' => q40b_jointCont hd1 htr T'
      rhoP := fun σ hσ => (hΛ σ hσ).1
      rhoC := fun σ hσ => PDE.MFLinear.continuous_of_isSmooth (hΛ σ hσ).2.1 }
  have hsb := q40b_isDet hBr T
  have hGlaw : law P G = multivariateGaussian 0 (integratedCov T (qsb D ρ t F)) := by
    rw [hG, q40b_integratedCov D ρ t F htT (fun a r hr => rfl)]
    rfl
  -- the initial statistic as a function of `X 0`
  set ψ : Fin p → Torus d → ℝ := fun a => F a 0 with hψdef
  have hψc : ∀ a, Continuous (ψ a) := fun a =>
    PDE.MFAux.continuous_of_isCk (PDE.ClassicalAux.isCk_of_le (by norm_num)
      ((hFcl a).c2 0 ⟨le_rfl, ht0 a⟩))
  set Af : Config d N → (ℝ^p) := fun x => WithLp.toLp 2 fun a =>
    linCoord (withDensityReal (ρ 0)) (ψ a) x with hAf
  have hAfm : Measurable Af := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp (measurable_pi_iff.2 fun a => ?_)
    unfold linCoord
    refine measurable_const.mul (Measurable.sub (measurable_const.mul ?_) measurable_const)
    exact Finset.measurable_sum _ fun i _ => (hψc a).measurable.comp (measurable_pi_apply i)
  set A : Ω → (ℝ^p) := fun ω => Af (X 0 ω) with hA
  have hAmeas0 : Measurable[ℱ 0] A :=
    @Measurable.comp Ω (Config d N) (ℝ^p) (ℱ 0) _ _ Af (X 0) hAfm (hfilt.adapted 0)
  have hAind : IndepFun A G P := hind.comp hAfm measurable_id
  set ℓ : Ω → (ℝ^p) := fun ω => WithLp.toLp 2 fun a =>
    linCoord (withDensityReal (ρ (t a))) (φ a) (X (t a).toNNReal ω) with hℓ
  set Rv : Ω → (ℝ^p) := fun ω => WithLp.toLp 2 fun a => Real.sqrt N *
    ∫ r in (0 : ℝ)..t a, flucInteraction D (F a r) (X r.toNNReal ω) (ρ r) with hRv
  set Mv := vectorItoIntegral P ℱ W' (qPhi D t F X) with hMv
  -- the a.s. identity
  have hid : ∀ a, ∀ᵐ ω ∂P, linCoord (withDensityReal (ρ (t a))) (φ a) (X (t a).toNNReal ω) =
      linCoord (withDensityReal (ρ 0)) (F a 0) (X 0 ω) +
        Real.sqrt N * itoIntegral P ℱ W' (empiricalNoiseIntegrand D (t a) (F a) X) (t a) ω +
        Real.sqrt N * ∫ r in (0 : ℝ)..t a, flucInteraction D (F a r) (X r.toNNReal ω) (ρ r) := fun a =>
    dyncmp_ae_identity hd1 htr'.gradient htr'.V_reg htr'.mf hreg hN hsol hfilt (ht a)
      (mova_isCk_two_of_smooth (hφ a)) (hFcl a) (fun r _ => rfl)
  have hstop : ∀ a, ∀ᵐ ω ∂P, itoIntegral P ℱ W' (empiricalNoiseIntegrand D (t a) (F a) X) T ω =
      itoIntegral P ℱ W' (empiricalNoiseIntegrand D (t a) (F a) X) (t a) ω := by
    intro a
    refine q40b_ito_stop hfilt.brownian (hΨ a) (ht0 a) (htT a) fun s' ω k hs => ?_
    unfold empiricalNoiseIntegrand
    have : s' ∉ Set.Icc 0 (t a) := fun h => absurd h.2 (not_le.2 hs)
    simp [this]
  have hsm : ∀ a, ∀ᵐ ω ∂P, ∀ τ : ℝ, itoIntegral P ℱ W' (qPhi D t F X a) τ ω =
      Real.sqrt N * itoIntegral P ℱ W' (empiricalNoiseIntegrand D (t a) (F a) X) τ ω :=
    fun a => itoIntegral_smul hfilt.brownian (hΨ a) (Real.sqrt N)
  have hAE : ℓ =ᵐ[P] fun ω => A ω + Mv T ω + Rv ω := by
    filter_upwards [ae_all_iff.2 hid, ae_all_iff.2 hstop, ae_all_iff.2 hsm] with ω h1 h2 h3
    ext a
    have hM : Mv T ω a = Real.sqrt N *
        itoIntegral P ℱ W' (empiricalNoiseIntegrand D (t a) (F a) X) (t a) ω := by
      show itoIntegral P ℱ W' (qPhi D t F X a) T ω = _
      rw [h3 a T, h2 a]
    simp only [hℓ, hA, hAf, hRv, hψdef, PiLp.add_apply, hM]
    rw [h1 a]
  -- the remainder
  have hδ : 1 ≤ (N : ℝ) * deltaN d D.s N := one_le_mul_deltaN D.hs0 N (by omega)
  set Cm : ℝ := Cf * (H₁ + N * deltaN d D.s N) with hCm
  have hCm0 : 0 ≤ Cm := mul_nonneg hCf (by linarith)
  have hRa : ∀ a, Integrable (fun ω => Real.sqrt N *
      ∫ r in (0 : ℝ)..t a, flucInteraction D (F a r) (X r.toNNReal ω) (ρ r)) P ∧
      ∫ ω, |Real.sqrt N * ∫ r in (0 : ℝ)..t a, flucInteraction D (F a r) (X r.toNNReal ω) (ρ r)| ∂P ≤
        t a * Cm / Real.sqrt N := by
    intro a
    have hB : ∀ r ∈ Set.Icc (0 : ℝ) (t a), ∀ x, ρ r x ≤ Λ 0 := by
      intro r hr x
      have h0 : Torus.IsCk 0 (ρ r) :=
        PDE.ClassicalAux.isCk_of_le (WithTop.coe_le_coe.2 zero_le) (mova_isCk_of_le
          (by exact_mod_cast (le_top : (0 : ℕ∞) ≤ ⊤)) (hΛ r hr.1).2.1)
      exact (le_abs_self _).trans ((Cor516Aux.abs_le_cbNorm' h0 x).trans ((hΛ r hr.1).2.2.2 0))
    refine dyncmp_R_bound hd1 htr'.gradient (ht0 a) (hFcl a).isC12Test hN hfilt.progressive
      (q40b_jointCont hd1 htr (t a)) (fun r hr => htr'.mf.density r ⟨hr.1, hr.2.trans (htT a)⟩) hB hCm0 ?_
    intro r hr
    have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.trans (htT a)⟩
    obtain ⟨hmeas, hν⟩ := hpair r hrT (Torus.grad (F a r)) (hLip a r ⟨hr.1.le, hr.2⟩)
    haveI : IsProbabilityMeasure (P.map (X r.toNNReal)) :=
      (Measure.isProbabilityMeasure_map_iff (hXm _).aemeasurable).2 inferInstance
    have hH := hentQ r hrT
    have hν' := hν (P.map (X r.toNNReal)) inferInstance (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH)
    have hg : Measurable (fun x : Config d N => ENNReal.ofReal ((N : ℝ) * |modulatedEnergy
        (commKernel (periodicRieszGrad d D.s) (Torus.grad (F a r))) x (withDensityReal (ρ r))|)) :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul hmeas.abs)
    have hconv := lintegral_map (μ := P) hg (hXm r.toNNReal)
    calc ∫⁻ ω, ENNReal.ofReal ((N : ℝ) * |Fm d D.s (F a) ρ X r ω|) ∂P
        = ∫⁻ x, ENNReal.ofReal ((N : ℝ) * |modulatedEnergy
            (commKernel (periodicRieszGrad d D.s) (Torus.grad (F a r))) x (withDensityReal (ρ r))|)
            ∂(P.map (X r.toNNReal)) := hconv.symm
      _ ≤ ENNReal.ofReal Cf * (relEntropy (P.map (X r.toNNReal))
            (movT_Q (periodicRiesz d D.s) D N ρ r) + ENNReal.ofReal (N * deltaN d D.s N)) := hν'
      _ ≤ ENNReal.ofReal Cf * (ENNReal.ofReal H₁ + ENNReal.ofReal (N * deltaN d D.s N)) :=
          mul_le_mul' le_rfl (add_le_add_left hH _)
      _ = ENNReal.ofReal Cm := by
          rw [hCm, ← ENNReal.ofReal_add hH₁ (by linarith), ← ENNReal.ofReal_mul hCf]
  have hRint : Integrable Rv P := by
    refine integrable_piLp_iff.2 fun a => ?_
    exact (hRa a).1
  have hRnorm : ∫ ω, ‖Rv ω‖ ∂P ≤ ∑ a, t a * Cm / Real.sqrt N := by
    have hle : ∀ ω, ‖Rv ω‖ ≤ ∑ a, |Real.sqrt N *
        ∫ r in (0 : ℝ)..t a, flucInteraction D (F a r) (X r.toNNReal ω) (ρ r)| := by
      intro ω
      refine (PDE.MFLinear.norm_euclid_le_sum _).trans (le_of_eq ?_)
      rfl
    calc ∫ ω, ‖Rv ω‖ ∂P ≤ ∫ ω, ∑ a, |Real.sqrt N *
          ∫ r in (0 : ℝ)..t a, flucInteraction D (F a r) (X r.toNNReal ω) (ρ r)| ∂P :=
          integral_mono hRint.norm (integrable_finsetSum _ fun a _ => (hRa a).1.abs) hle
      _ = ∑ a, ∫ ω, |Real.sqrt N *
          ∫ r in (0 : ℝ)..t a, flucInteraction D (F a r) (X r.toNNReal ω) (ρ r)| ∂P :=
          integral_finsetSum _ fun a _ => (hRa a).1.abs
      _ ≤ ∑ a, t a * Cm / Real.sqrt N := Finset.sum_le_sum fun a _ => (hRa a).2
  -- the comparison on the enlargement
  have hcmp := dyncmp_gaussian_comparison P ℱ hT hvec hsb hAmeas0 hGm hGlaw hAind hRint hAE
  have hcov := dyncmp_cov_bound hBr hN0 hXm hvec.sigma_meas hH₁ hT htT hentP
  have hlaw : (law P fun ω => (WithLp.toLp 2 fun a =>
      linCoord (withDensityReal (ρ 0)) (propagator htr.dyn ρ 0 (t a) (φ a)) (X 0 ω) + G ω a : ℝ^p)) =
      law P fun ω => A ω + G ω := by
    congr 1
  rw [hlaw]
  have hcm0 : 0 ≤ covDiscrepancyMatrix P T (covMatrixProcess (qPhi D t F X)) (qsb D ρ t F) :=
    integral_nonneg fun ω => setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormMatrix_nonneg _
  refine hcmp.trans ?_
  have hRn : ∑ a, t a * Cm / Real.sqrt N = ∑ a, t a * (Cf * (H₁ + N * deltaN d htr.dyn.s N)) / Real.sqrt N :=
    rfl
  have hcv' : (1 / 2) * covDiscrepancyMatrix P T (covMatrixProcess (qPhi D t F X)) (qsb D ρ t F) ≤
      (1 / 2) * ((∑ a, ∑ b, 2 * β⁻¹ * (Ca a * Real.exp T) * (Ca b * Real.exp T) / (2 * 1)) *
        Real.sqrt (2 * (H₁ + Real.log 2) / N)) :=
    mul_le_mul_of_nonneg_left hcov (by norm_num)
  linarith [hRnorm, hcv', hRn]

end HRS

end
