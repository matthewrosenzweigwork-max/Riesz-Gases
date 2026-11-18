import HRS.MS.Fp81S21GaussianPhysicalPackage
import HRS.MS.Fp81S21GaussianSourceDensity
import HRS.MS.S21E_Uniq
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Packet 37, unit 5. The thermal representative is the adjoint of the
selected operator applied to the endpoint observation. All times and tests
remain universal after the radius. The explicit `ha` and `hχ` binders below
repair the plan's untyped proof binders without changing its statement. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S21E HRS.MC.E213U13 HRS.MC.QRSpec.Wick

variable {p : Parameters} {δ : ℝ} {R : Trajectory p δ}

/-- Endpoint observation of the retained physical window. -/
def fp81s21_cross37_X (Q : fp81s21_Physical35 p R) (a : ℝ)
    (τ : Fin 3 → Icc (0 : ℝ) p.T) (φ : Fin 3 → Euc p.d → ℝ)
    (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i))
    (i : Fin 3) : Q.src.G0.Ω → ℝ :=
  fun ω => s21eObs (wholeSpaceIndex p.d : ℝ) p.T (hφ i).2 (τ i)
    (r26t3_Zpath Q.src.G0 a ω)

/-- Exact selected-field cross-density contract of packet 37. -/
def fp81s21_Cross37 (Q : fp81s21_Physical35 p R) (a : ℝ)
    (τ : Fin 3 → Icc (0 : ℝ) p.T) (φ : Fin 3 → Euc p.d → ℝ)
    (χ : Fin 3 → ℝ → Euc p.d → ℝ)
    (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)) : Prop :=
  let X := fp81s21_cross37_X Q a τ φ hφ
  ∃ 𝒢 : Submodule ℝ (Q.src.G0.Ω → ℝ), QrpwG4 Q.src.G0.P 𝒢 ∧
    (∀ r : ℝ, 0 ≤ r → ∀ f : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ),
      (Q.S.T Q.src.G0 r f : Q.src.G0.Ω → ℝ) ∈ 𝒢) ∧
    (∀ i, X i ∈ 𝒢) ∧
    ∃ u : Fin 3 → ℝ → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ),
      ∀ i, ∀ r ∈ Icc (0 : ℝ) (a + p.T),
        (∀ f : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ),
          Integrable (fun ω => Q.S.T Q.src.G0 r f ω * X i ω) Q.src.G0.P ∧
          (∫ ω, Q.S.T Q.src.G0 r f ω * X i ω ∂Q.src.G0.P) =
            ∫ x, f x * u i r x ∂HRS.Whole.withDensityReal R.ρβ) ∧
        (fun x => u i r x * R.ρβ x) =ᵐ[volume] χ i r

private theorem fp81s21_cross37_endpoint_ae
    (Q : fp81s21_Physical35 p R) (a : ℝ) (ha : 0 ≤ a)
    (τ : Fin 3 → Icc (0 : ℝ) p.T) (φ : Fin 3 → Euc p.d → ℝ)
    (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)) (i : Fin 3) :
    fp81s21_cross37_X Q a τ φ hφ i =ᵐ[Q.src.G0.P]
      fun ω => OscDual.eval (Q.src.G0.Z (a + τ i) ω) (φ i) := by
  have hshift : ContinuousOn (fun u : ℝ => a + u) (Icc (0 : ℝ) p.T) :=
    (continuous_const.add continuous_id).continuousOn
  have hmaps : MapsTo (fun u : ℝ => a + u) (Icc (0 : ℝ) p.T)
      (Icc (0 : ℝ) (a + p.T)) := by
    intro u hu
    exact ⟨add_nonneg ha hu.1, by linarith [hu.2]⟩
  filter_upwards [(Q.src.G0.evolution (a + p.T)).cont] with ω hω
  have hc : Continuous (fun t : Icc (0 : ℝ) p.T => Q.src.G0.Z (a + t) ω) :=
    continuousOn_iff_continuous_domRestrict.mp (hω.comp hshift hmaps)
  change s21eObs (wholeSpaceIndex p.d : ℝ) p.T (hφ i).2 (τ i)
    (r26t3_Zpath Q.src.G0 a ω) = _
  refine (s21eObs_apply (wholeSpaceIndex p.d : ℝ) p.T (hφ i).2 (τ i)
    (r26t3_Zpath Q.src.G0 a ω)).trans ?_
  simp [r26t3_Zpath, processWindow, windowPathOf, OscPath.at', hc]

/-- The selected thermal field and all endpoint observations share one scalar
first-chaos space; no replacement of the selected operator is made. -/
theorem fp81s21_cross37_common_source
    (Q : fp81s21_Physical35 p R) (a : ℝ) (ha : 0 ≤ a)
    (τ : Fin 3 → Icc (0 : ℝ) p.T) (φ : Fin 3 → Euc p.d → ℝ)
    (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)) :
    ∃ 𝒢 : Submodule ℝ (Q.src.G0.Ω → ℝ), QrpwG4 Q.src.G0.P 𝒢 ∧
      (∀ r : ℝ, 0 ≤ r → ∀ f : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ),
        (Q.S.T Q.src.G0 r f : Q.src.G0.Ω → ℝ) ∈ 𝒢) ∧
      (∀ i, fp81s21_cross37_X Q a τ φ hφ i ∈ 𝒢) ∧
      (∀ i, MemLp (fp81s21_cross37_X Q a τ φ hφ i) 2 Q.src.G0.P) := by
  obtain ⟨hm, hs, -, heval⟩ :=
    fp81s21_gaussian_source_measurable_eval_firstChaos Q.src
  -- Use the explicit first-chaos space so that null-set changes of endpoints
  -- preserve membership without requiring saturation of an arbitrary witness.
  let G := fp81s21_scalarFirstChaosSpace
    (P := Q.src.G0.P) (fp81s21_gaussian_source_measurableXi Q.src) hs hm
  have hX : ∀ i, fp81s21_cross37_X Q a τ φ hφ i ∈ G := by
    intro i
    exact InQ1_congr (fp81s21_cross37_endpoint_ae Q a ha τ φ hφ i).symm
      (s21l_inQ1_of_first hs hm
        (heval (a + τ i) (add_nonneg ha (τ i).2.1) ⟨φ i, hφ i⟩))
  have hTG : ∀ r : ℝ, 0 ≤ r → ∀ f : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ),
      (Q.S.T Q.src.G0 r f : Q.src.G0.Ω → ℝ) ∈ G := by
    intro r hr f
    have hfirst := fp81s21_gaussianSourceSpace_oscTest_dense p R
    have hclosed := (Submodule.isClosed_topologicalClosure
      (⨆ n, K1 hs hm n)).preimage (Q.S.T Q.src.G0 r).continuous
    have htests : Set.range (fp81s21_gaussianSourceSpace_oscTestLp p R) ⊆
        {x | Q.S.T Q.src.G0 r x ∈ Qc (K1 hs hm)} := by
      rintro _ ⟨ψ, rfl⟩
      have hq := InQ1_congr
        (Q.T_oscillator r hr ψ.1 ψ.2
          (fp81s21_gaussianSourceSpace_oscTest_memLp p R ψ)).symm
        (s21l_inQ1_of_first hs hm (heval r hr ψ))
      obtain ⟨hmem, hmemQ⟩ := hq
      rw [Lp.toLp_coeFn] at hmemQ
      exact hmemQ
    refine ⟨Lp.memLp _, ?_⟩
    rw [Lp.toLp_coeFn]
    exact closure_minimal htests hclosed (hfirst f)
  exact ⟨G, fp81s21_scalarFirstChaos_QrpwG4 _ hs hm, hTG, hX, fun i => (hX i).1⟩

private theorem fp81s21_cross37_adjoint
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {d : ℕ} (μ : Measure (Euc d))
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) {X : Ω → ℝ} (hX : MemLp X 2 P) :
    ∃ u : Lp ℝ 2 μ, ∀ f : Lp ℝ 2 μ,
      Integrable (fun ω => T f ω * X ω) P ∧
      (∫ ω, T f ω * X ω ∂P) = ∫ x, f x * u x ∂μ := by
  refine ⟨T.adjoint (hX.toLp X), fun f => ⟨(Lp.memLp _).integrable_mul hX, ?_⟩⟩
  have heq : (∫ ω, T f ω * X ω ∂P) = inner ℝ (T f) (hX.toLp X) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hX.coeFn_toLp] with ω hω
    simp [hω, RCLike.inner_apply, mul_comm]
  rw [heq, ← T.adjoint_inner_right]
  simp [L2.inner_def, RCLike.inner_apply, mul_comm]

/-- Exact physical cross-densities for every supplied packet-35 realization.
The radius precedes the realization and every window/test choice. -/
theorem fp81s21_gaussian_cross_density (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
        ∀ Q : fp81s21_Physical35 p R, ∀ (a : ℝ) (_ha : 0 ≤ a)
          (τ : Fin 3 → Icc (0 : ℝ) p.T) (φ : Fin 3 → Euc p.d → ℝ)
          (χ : Fin 3 → ℝ → Euc p.d → ℝ)
          (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)),
          S21eChiClause p.d p.s p.a p.β p.γ R.ρ p.T a τ φ χ →
          fp81s21_Cross37 Q a τ φ χ hφ := by
  refine ⟨1 / 2, by norm_num, le_rfl, ?_⟩
  intro δ hδ hδhalf R Q a ha τ φ χ hφ hχ
  let : IsProbabilityMeasure (r26t3_mu R 0) := fp81s21_initialMeasure_isProbability p R
  obtain ⟨G, h4, hT, hX, hXm⟩ := fp81s21_cross37_common_source Q a ha τ φ hφ
  have hu := fun i r => fp81s21_cross37_adjoint Q.src.G0.P
    (HRS.Whole.withDensityReal R.ρβ) (Q.S.T Q.src.G0 r) (hXm i)
  choose u hu using hu
  refine ⟨G, h4, hT, hX, u, ?_⟩
  intro i r hr
  refine ⟨hu i r, ?_⟩
  have hm : Measurable R.ρβ := R.thermal.1.1.measurable
  have hn : ∀ x, 0 ≤ R.ρβ x := R.thermal.1.1.nonneg
  have hfin : ∀ᵐ x ∂(volume : Measure (Euc p.d)), ENNReal.ofReal (R.ρβ x) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hpair (ψ : Euc p.d → ℝ) (hψ : IsOscTest (wholeSpaceIndex p.d : ℝ) ψ) :
      Integrable (fun x => ψ x * (u i r x * R.ρβ x)) ∧
      (∫ x, ψ x * (u i r x * R.ρβ x)) =
        s21eCov p.d p.s p.a p.β p.γ R.ρ r (a + τ i) ψ (φ i) := by
    let ψL := fp81s21_gaussianSourceSpace_oscTestLp p R ⟨ψ, hψ⟩
    have hψm := fp81s21_gaussianSourceSpace_oscTest_memLp p R ⟨ψ, hψ⟩
    have hint := hψm.integrable_mul (Lp.memLp (u i r))
    have hint' := (integrable_withDensity_iff_integrable_smul'
      hm.ennreal_ofReal hfin (g := fun x => ψ x * u i r x)).1 hint
    refine ⟨hint'.congr (Eventually.of_forall fun x => ?_), ?_⟩
    · simp only [smul_eq_mul, ENNReal.toReal_ofReal (hn x)]
      ring
    have hw : (∫ x, ψ x * (u i r x * R.ρβ x)) =
        ∫ x, ψL x * u i r x ∂HRS.Whole.withDensityReal R.ρβ := by
      rw [integral_congr_ae (show (fun x => ψL x * u i r x) =ᵐ[HRS.Whole.withDensityReal R.ρβ]
        (fun x => ψ x * u i r x) from by
          filter_upwards [hψm.coeFn_toLp] with x hx
          exact congrArg (fun z => z * u i r x) hx)]
      unfold HRS.Whole.withDensityReal
      rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal hfin]
      apply integral_congr_ae
      filter_upwards with x
      simp only [smul_eq_mul, ENNReal.toReal_ofReal (hn x)]
      ring
    rw [hw, ← (hu i r ψL).2]
    have hleft := (Q.T_oscillator r hr.1 ψ hψ hψm).trans
      (Q.src.sourceEvaluation r hr.1 ψ hψ)
    have hright := (fp81s21_cross37_endpoint_ae Q a ha τ φ hφ i).trans
      (Q.src.sourceEvaluation (a + τ i) (add_nonneg ha (τ i).2.1) (φ i) (hφ i))
    calc
      _ = ∫ ω, Q.src.W (Q.src.J (fp81s21_combinedFeature p R Q.src.hK r ψ)) ω *
          Q.src.W (Q.src.J (fp81s21_combinedFeature p R Q.src.hK (a + τ i) (φ i))) ω
          ∂Q.src.G0.P := by
        apply integral_congr_ae
        filter_upwards [hleft, hright] with ω hl hr'
        exact congrArg₂ (· * ·) hl hr'
      _ = _ := by
        rw [Q.src.allFeatureCovariance, Q.src.J.inner_map_map]
        exact fp81s21_combinedFeature_gram p hδ hδhalf R Q.src.hK hr.1
          (add_nonneg ha (τ i).2.1) hψ (hφ i)
  exact s21e_chi_ae_eq (wholeSpaceIndex p.d : ℝ)
    (fun ψ hψ => (hpair ψ hψ).1)
    (fun ψ hψ => ((hχ i r hr).2 ψ hψ).1)
    (fun ψ hψ => (hpair ψ hψ).2.trans (((hχ i r hr).2 ψ hψ).2.symm))

#print axioms fp81s21_cross37_common_source
#print axioms fp81s21_gaussian_cross_density
end HRS.Fp81.S21
end
