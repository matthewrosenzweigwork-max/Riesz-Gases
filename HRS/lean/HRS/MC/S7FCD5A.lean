import HRS.MC.S7FCF5IE2
import HRS.MC.S7FCW12B
import HRS.MC.S7FCW2Aux
import HRS.MC.L2C0
import HRS.Energy.StaticLimitBasic

/-!
# Packet fcf5p, D5 helpers: coupling bound, coordinate calculus on `E_m`, centred means

Generic helpers for `S7FCD5B.lean` (proof of `s7_FC_D5_mean`).  Sorry-free; no sorried module is imported.

* `S7FCD5A_coupling_bound`: for a coupling `π` of `μ, ν` on a second countable Banach space with `μ` integrable,
  `ofReal ‖∫x dμ - ∫y dν‖ ≤ (∫⁻ ‖x - y‖^2 dπ)^{1/2}` (Cauchy-Schwarz through the variance).
* coordinate calculus: `S7FCD5A_ext`, `S7FCD5A_ofMD_triangle`.
* `S7FCD5A_zeta_integral_zero`: the exactly centred field has mean zero in `E_r`.
* `S7FCD5A_eta_integral_zero`: the Gaussian limit has mean zero in `E_r` at every time `t ≥ 0`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCD5A

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec

variable {d : ℕ}

/-- Coupling bound for the mean difference: `‖∫x dμ - ∫y dν‖ ≤ (∫⁻ ‖x-y‖^2 dπ)^{1/2}`. -/
theorem S7FCD5A_coupling_bound {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [SecondCountableTopology B]
    (μ ν : Measure B) [IsProbabilityMeasure μ] (hμ : Integrable (fun x : B => x) μ)
    (π : Measure (B × B)) (hπ : IsCoupling π μ ν) :
    ENNReal.ofReal ‖∫ x, x ∂μ - ∫ y, y ∂ν‖ ≤
      (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π) ^ (1 / (2 : ℝ)) := by
  haveI : IsProbabilityMeasure π := IsCoupling.isProbabilityMeasure hπ
  by_cases hfin : ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π = ⊤
  · rw [hfin, ENNReal.top_rpow_of_pos (by norm_num)]
    exact le_top
  have hmeas_d : Measurable fun z : B × B => z.1 - z.2 := measurable_fst.sub measurable_snd
  have hmeas_h : Measurable fun z : B × B => ‖z.1 - z.2‖ := hmeas_d.norm
  have hsq_lin : ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ 2) ∂π < ⊤ := by
    have h2 : ∀ z : B × B, ‖z.1 - z.2‖ ^ (2 : ℝ) = ‖z.1 - z.2‖ ^ 2 := fun z => Real.rpow_two _
    simp only [h2] at hfin
    exact lt_top_iff_ne_top.2 hfin
  have hsq : Integrable (fun z : B × B => ‖z.1 - z.2‖ ^ 2) π := by
    refine ⟨(hmeas_h.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => by positivity)]
    exact hsq_lin
  have hL2 : MemLp (fun z : B × B => ‖z.1 - z.2‖) 2 π :=
    (memLp_two_iff_integrable_sq hmeas_h.aestronglyMeasurable).2 hsq
  have hint : Integrable (fun z : B × B => ‖z.1 - z.2‖) π := by
    have hg : Integrable (fun z : B × B => (‖z.1 - z.2‖ ^ 2 + 1) / 2) π :=
      (hsq.add (integrable_const (1 : ℝ))).div_const 2
    refine Integrable.mono' hg hmeas_h.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    nlinarith [sq_nonneg (‖z.1 - z.2‖ - 1)]
  have hdiff : Integrable (fun z : B × B => z.1 - z.2) π :=
    (integrable_norm_iff hmeas_d.aestronglyMeasurable).1 hint
  have hx : Integrable (fun z : B × B => z.1) π := by
    have h : Integrable (fun x : B => x) (π.map Prod.fst) := by rw [hπ.1]; exact hμ
    exact (integrable_map_measure aestronglyMeasurable_id measurable_fst.aemeasurable).1 h
  have hy : Integrable (fun z : B × B => z.2) π := by
    refine (hx.sub hdiff).congr (Eventually.of_forall fun z => ?_)
    simp
  have e1 : ∫ x, x ∂μ = ∫ z, z.1 ∂π := by
    have h := integral_map (μ := π) (f := fun x : B => x) measurable_fst.aemeasurable
      aestronglyMeasurable_id
    rw [hπ.1] at h
    exact h
  have e2 : ∫ y, y ∂ν = ∫ z, z.2 ∂π := by
    have h := integral_map (μ := π) (f := fun x : B => x) measurable_snd.aemeasurable
      aestronglyMeasurable_id
    rw [hπ.2] at h
    exact h
  rw [e1, e2, ← integral_sub hx hy]
  have hnorm : ‖∫ z, (z.1 - z.2) ∂π‖ ≤ ∫ z, ‖z.1 - z.2‖ ∂π := norm_integral_le_integral_norm _
  have hvar := variance_nonneg (fun z : B × B => ‖z.1 - z.2‖) π
  rw [variance_eq_sub hL2] at hvar
  have hcs : (∫ z, ‖z.1 - z.2‖ ∂π) ^ 2 ≤ ∫ z, ‖z.1 - z.2‖ ^ 2 ∂π := by
    simp only [Pi.pow_apply] at hvar
    linarith
  have hh0 : 0 ≤ ∫ z, ‖z.1 - z.2‖ ∂π := integral_nonneg fun z => norm_nonneg _
  have hsqrt : ∫ z, ‖z.1 - z.2‖ ∂π ≤ Real.sqrt (∫ z, ‖z.1 - z.2‖ ^ 2 ∂π) :=
    le_trans (le_abs_self _) (Real.abs_le_sqrt hcs)
  have hsq0 : 0 ≤ ∫ z, ‖z.1 - z.2‖ ^ 2 ∂π := integral_nonneg fun z => by positivity
  calc ENNReal.ofReal ‖∫ z, (z.1 - z.2) ∂π‖ ≤ ENNReal.ofReal (∫ z, ‖z.1 - z.2‖ ∂π) :=
        ENNReal.ofReal_le_ofReal hnorm
    _ ≤ ENNReal.ofReal (Real.sqrt (∫ z, ‖z.1 - z.2‖ ^ 2 ∂π)) := ENNReal.ofReal_le_ofReal hsqrt
    _ = ENNReal.ofReal (∫ z, ‖z.1 - z.2‖ ^ 2 ∂π) ^ (1 / (2 : ℝ)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hsq0 (by norm_num), Real.sqrt_eq_rpow]
    _ = (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ 2) ∂π) ^ (1 / (2 : ℝ)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hsq (Eventually.of_forall fun z => by positivity)]
    _ = (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π) ^ (1 / (2 : ℝ)) := by
        simp only [Real.rpow_two]

/-! ### Coordinate calculus on `E_m` -/

/-- Two elements of `E_m` with the same real Fourier coordinates coincide. -/
theorem S7FCD5A_ext {m : ℝ} {F G : NegSobolev d m}
    (h : ∀ k : NonzeroLattice d, NegSobolev.coord F k = NegSobolev.coord G k) : F = G :=
  Subtype.ext (funext fun k => h k)

/-- The mode coordinates of a difference of embedded measures (`d < 2m`, finite measures). -/
theorem S7FCD5A_ofMD_triangle {m : ℝ} (hm : (d : ℝ) < 2 * m) (e μ M : Measure (Torus d))
    [IsFiniteMeasure e] [IsFiniteMeasure μ] [IsFiniteMeasure M] :
    NegSobolev.ofMeasureDiff m e μ = NegSobolev.ofMeasureDiff m e M + NegSobolev.ofMeasureDiff m M μ := by
  apply S7FCD5A_ext
  intro k
  have h1 := HRS.coord_ofMeasureDiff hm e μ k
  have h2 := HRS.coord_ofMeasureDiff hm e M k
  have h3 := HRS.coord_ofMeasureDiff hm M μ k
  have hadd : ∀ F G : NegSobolev d m, NegSobolev.coord (F + G) k = NegSobolev.coord F k + NegSobolev.coord G k :=
    fun F G => rfl
  rw [hadd, h1, h2, h3]
  ring

/-- The `k`-th coordinate of a scalar multiple. -/
theorem S7FCD5A_coord_smul {m : ℝ} (c : ℝ) (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (c • F) k = c * NegSobolev.coord F k := rfl

/-- The `k`-th coordinate of the zero element. -/
theorem S7FCD5A_coord_zero {m : ℝ} (k : NonzeroLattice d) : NegSobolev.coord (0 : NegSobolev d m) k = 0 := rfl

/-! ### The exactly centred field has mean zero -/

/-- Uniform bound of the exactly centred field `ζ_N^t` (probability measures, `N ≥ 1`). -/
theorem S7FCD5A_zetaAt_norm_le {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (r : ℝ) (hr : (d : ℝ) < 2 * r)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → Config d N) (hadapt : ∀ t : ℝ≥0, Measurable (X t))
    (hN : 1 ≤ N) (t : ℝ) (ω : Ω) :
    ‖zetaAt r P X t ω‖ ≤ Real.sqrt N * Real.sqrt (8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * r))) := by
  haveI : IsProbabilityMeasure (P.map (X t.toNNReal)) :=
    (Measure.isProbabilityMeasure_map_iff (hadapt _).aemeasurable).2 inferInstance
  haveI := HRS.isProbabilityMeasure_meanEmpirical (P.map (X t.toNNReal)) hN
  haveI := HRS.empirical_isProbabilityMeasure (show 0 < N by omega) (X t.toNNReal ω)
  unfold zetaAt zetaE
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (HRS.norm_ofMeasureDiff_le hr _ _) (Real.sqrt_nonneg _)

/-- The `k`-th coordinate of a real mode: `coord F k = jp^{-m} · F(e_k)` (unweighted coefficient `F(e_k)`). -/
theorem S7FCD5A_coord_eq_eval {m : ℝ} (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord F k = Lattice.jp k.1 ^ (-m) * NegSobolev.eval F (Torus.realMode k) := by
  rw [HRS.MC.QRSpec.Marg.qm_eval_realMode]
  unfold NegSobolev.fourierCoeff
  rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1), neg_add_cancel, Real.rpow_zero, one_mul]

/-- Bounded measurable real modes of the particles are integrable. -/
theorem S7FCD5A_integrable_realMode {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → Config d N) (hY : Measurable Y) (k : NonzeroLattice d) (i : Fin N) :
    Integrable (fun ω => Torus.realMode k (Y ω i)) P := by
  refine (integrable_const (Real.sqrt 2)).mono'
    ((continuous_realMode' k).measurable.comp ((measurable_pi_apply i).comp hY)).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact Torus.abs_realMode_le k _

/-- The exactly centred field has mean zero: `∫ ζ_N^t dP = 0` in `E_r` (`N ≥ 1`, `d < 2r`). -/
theorem S7FCD5A_zeta_integral_zero {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (r : ℝ) (hr : (d : ℝ) < 2 * r)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → Config d N)
    (hadapt : ∀ t : ℝ≥0, Measurable (X t)) (hN : 1 ≤ N) (t : ℝ) :
    ∫ ω, zetaAt r P X t ω ∂P = 0 := by
  have hN0 : 0 < N := by omega
  have hmeas : Measurable fun ω => zetaAt r P X t ω :=
    HRS.MC.Sec7.S7FCW12.s7fcw12_zetaAt_measurable r P X hadapt hN0 t
  have hint : Integrable (fun ω => zetaAt r P X t ω) P :=
    (integrable_const _).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall fun ω => S7FCD5A_zetaAt_norm_le r hr P X hadapt hN t ω)
  apply S7FCD5A_ext
  intro k
  rw [S7FCD5A_coord_zero, ← HRS.negCoordCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hint]
  simp only [HRS.negCoordCLM_apply]
  -- the coordinates of `ζ_N^t(ω)`
  have hco : ∀ ω, NegSobolev.coord (zetaAt r P X t ω) k =
      Real.sqrt N * (Lattice.jp k.1 ^ (-r) *
        (Torus.measureRealCoeff (empirical (X t.toNNReal ω)) k -
          Torus.measureRealCoeff (meanEmpirical (P.map (X t.toNNReal))) k)) := by
    intro ω
    haveI : IsProbabilityMeasure (P.map (X t.toNNReal)) :=
      (Measure.isProbabilityMeasure_map_iff (hadapt _).aemeasurable).2 inferInstance
    haveI := HRS.isProbabilityMeasure_meanEmpirical (P.map (X t.toNNReal)) hN
    haveI := HRS.empirical_isProbabilityMeasure hN0 (X t.toNNReal ω)
    unfold zetaAt zetaE
    rw [S7FCD5A_coord_smul, HRS.coord_ofMeasureDiff hr]
  simp_rw [hco]
  -- the centred real coefficients
  have hce : ∀ ω, Torus.measureRealCoeff (empirical (X t.toNNReal ω)) k =
      (N : ℝ)⁻¹ * ∑ i, Torus.realMode k (X t.toNNReal ω i) := by
    intro ω
    unfold Torus.measureRealCoeff
    exact HRS.integral_empirical _ (continuous_realMode' k)
  have hcM : Torus.measureRealCoeff (meanEmpirical (P.map (X t.toNNReal))) k =
      (N : ℝ)⁻¹ * ∑ i, ∫ ω, Torus.realMode k (X t.toNNReal ω i) ∂P := by
    unfold Torus.measureRealCoeff
    rw [HRS.integral_meanEmpirical _ (continuous_realMode' k)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_map (hadapt _).aemeasurable
      ((continuous_realMode' k).comp (continuous_apply i)).aestronglyMeasurable
  have hcs : Integrable (fun ω => (N : ℝ)⁻¹ * ∑ i, Torus.realMode k (X t.toNNReal ω i)) P :=
    (integrable_finset_sum _ fun i _ => S7FCD5A_integrable_realMode P (X t.toNNReal) (hadapt _) k i).const_mul _
  rw [integral_const_mul, integral_const_mul]
  simp_rw [hce]
  rw [integral_sub hcs (integrable_const _), integral_const, integral_const_mul,
    integral_finset_sum _ (fun i _ => S7FCD5A_integrable_realMode P (X t.toNNReal) (hadapt _) k i), ← hcM]
  simp

/-- Mean zero of the test-function pairing of the Gaussian limit at time `t` (one-dimensional version of
`S7FCW2_fgc`, same ingredients: the centred initial law and the centred noise part `G`). -/
theorem S7FCD5A_eval_integral_zero {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (D : DynData d) (ρ : ℝ → Torus d → ℝ) (r q t : ℝ)
    (C : (Torus d → ℝ) → (Torus d → ℝ) → ℝ) (Y₀ : Ω' → NegSobolev d r) (η : ℝ → Ω' → NegSobolev d r)
    (hY : IsCenteredGaussianWithCov r (P'.map Y₀) C)
    (hLin : IsLinearFluctuationSolution P' D ρ r q t Y₀ η) (ht : 0 ≤ t)
    (hψ : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → Torus.IsSmooth (propagator D ρ 0 t φ))
    (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) :
    ∫ ω, NegSobolev.eval (η t ω) φ ∂P' = 0 := by
  have hmY : AEMeasurable Y₀ P' := (hLin.meas 0).aemeasurable.congr hLin.init
  have hmη : Measurable (η t) := hLin.meas t
  haveI : IsGaussian (P'.map Y₀) := hY.1.1
  have hYg : HasGaussianLaw Y₀ P' := HRS.MC.QRSpec.Marg.qm_hasGaussianLaw_of_map hmY rfl
  have m0 := HRS.MC.QRSpec.Marg.qm_integral_dual_zero hYg hY.1.2
  have hs := hLin.gaussian_part 1 (fun _ => t) (fun _ => φ) (fun _ => ⟨ht, le_rfl⟩) (fun _ => hφ)
  let G : Ω' → EuclideanSpace ℝ (Fin 1) := fun ω => WithLp.toLp 2 fun a : Fin 1 =>
    NegSobolev.eval (η t ω) φ - NegSobolev.eval (Y₀ ω) (propagator D ρ 0 t φ)
  have hind : IndepFun G Y₀ P' := hs.1
  obtain ⟨Cv, hlaw⟩ : ∃ Cv : Matrix (Fin 1) (Fin 1) ℝ, P'.map G = multivariateGaussian 0 Cv := ⟨_, hs.2⟩
  obtain ⟨cφ, hcφ⟩ := HRS.MC.Sec7.S7FCW2.S7FCW2_ev r φ hφ
  obtain ⟨aψ, haψ⟩ := HRS.MC.Sec7.S7FCW2.S7FCW2_ev r _ (hψ φ hφ)
  have hmG : AEMeasurable G P' := by
    have h1 : ∀ a : Fin 1, AEMeasurable (fun ω => G ω a) P' := by
      intro a
      have h : (fun ω => G ω a) = fun ω => cφ (η t ω) - aψ (Y₀ ω) := by
        funext ω
        simp only [G, hcφ, haψ]
      rw [h]
      exact ((cφ.continuous.measurable.comp hmη).aemeasurable).sub
        ((aψ.continuous.measurable.comp_aemeasurable hmY))
    exact (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).measurable.comp_aemeasurable (aemeasurable_pi_iff.2 h1)
  have hGg : HasGaussianLaw G P' := HRS.MC.QRSpec.Marg.qm_hasGaussianLaw_of_map hmG hlaw
  have m2 := fun g : StrongDual ℝ (EuclideanSpace ℝ (Fin 1)) =>
    HRS.MC.QRSpec.Marg.qm_mvg_dual_zero Cv hmG hlaw g
  have core := HRS.MC.Sec7.S7FCW2.S7FCW2_core hYg hGg hind m0 m2 (ι := Fin 1) (fun _ => aψ)
    (fun _ => (EuclideanSpace.proj (0 : Fin 1) : StrongDual ℝ (EuclideanSpace ℝ (Fin 1))))
  have hc := core.2 0
  have hfun : (fun ω => NegSobolev.eval (η t ω) φ) =
      fun ω => aψ (Y₀ ω) + (EuclideanSpace.proj (0 : Fin 1) : StrongDual ℝ (EuclideanSpace ℝ (Fin 1))) (G ω) := by
    funext ω
    simp [G, haψ]
  rw [hfun]
  exact hc

/-- The Gaussian limit field has mean zero in `E_r` at every time `t ≥ 0`: `∫ η^t dP' = 0`. -/
theorem S7FCD5A_eta_integral_zero {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (D : DynData d) (ρ : ℝ → Torus d → ℝ) (r q t : ℝ)
    (C : (Torus d → ℝ) → (Torus d → ℝ) → ℝ) (Y₀ : Ω' → NegSobolev d r) (η : ℝ → Ω' → NegSobolev d r)
    (hY : IsCenteredGaussianWithCov r (P'.map Y₀) C)
    (hLin : IsLinearFluctuationSolution P' D ρ r q t Y₀ η) (ht : 0 ≤ t)
    (hψ : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → Torus.IsSmooth (propagator D ρ 0 t φ)) :
    ∫ ω, η t ω ∂P' = 0 := by
  by_cases hint : Integrable (fun ω => η t ω) P'
  · apply S7FCD5A_ext
    intro k
    rw [S7FCD5A_coord_zero, ← HRS.negCoordCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hint]
    simp only [HRS.negCoordCLM_apply]
    have hfc : ∀ ω, NegSobolev.coord (η t ω) k =
        Lattice.jp k.1 ^ (-r) * NegSobolev.eval (η t ω) (Torus.realMode k) :=
      fun ω => S7FCD5A_coord_eq_eval _ k
    simp_rw [hfc]
    rw [integral_const_mul]
    have h0 := S7FCD5A_eval_integral_zero P' D ρ r q t C Y₀ η hY hLin ht hψ (Torus.realMode k)
      (HRS.FieldSingAux.isSmooth_realMode k)
    rw [h0, mul_zero]
  · rw [integral_undef hint]


end HRS.MC.Sec7.S7FCD5A

end
