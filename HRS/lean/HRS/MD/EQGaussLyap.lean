import HRS.MD.EQGaussLyapDet
import HRS.MD.EQGaussLyapDet2
import HRS.MD.EQGaussLyapCov
import HRS.MD.EQGaussLyapProb
import HRS.Uniform.Evolution
import HRS.Energy.Modulated
import HRS.Sections.Sec3

/-!
# EQ-GAUSS (a): the Lyapunov step

`t ↦ Vev(t,0) Z⁰ + Zb_t` is an `IsStationaryGaussianField`.  The finite-dimensional vector splits as `A + B`, with
`A = (⟨Vev(τ_a,0)Z⁰, φ_a⟩)_a = (⟨Z⁰, U^{0,τ_a}φ_a⟩)_a` centered Gaussian with covariance `𝒞_β(U^{0,τ_a}φ_a, U^{0,τ_b}φ_b)`
(`eqgl_A_gauss`), and `B = (⟨Zb_{τ_a}, φ_a⟩)_a` centered Gaussian with the noise covariance and independent of `Z⁰`
(`EQGaussLyapProb.eqgp_package`).  The sum of the two covariance matrices is `PDE.stationaryLagCov`
(`EQGaussLyapDet2.eqgld_cov_total`, the Lyapunov identity).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.MD.EQGaussLyap

open HRS HRS.PDE HRS.Uniform HRS.Uniform.Q54c HRS.Uniform.Q45 HRS.GF
open HRS.MD.EQGaussLyapDet HRS.MD.EQGaussLyapDet2 HRS.MD.EQGaussLyapCov HRS.MD.EQGaussLyapProb

variable {d : ℕ}

/-- Uniform bound of a strongly continuous evolution on a compact time window (Banach-Steinhaus). -/
theorem eqgl_bound {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (Vev : ℝ → ℝ → H →L[ℝ] H) {S : ℝ}
    (hc : ∀ x : H, ContinuousOn (fun p : ℝ × ℝ => Vev p.1 p.2 x) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ S}) :
    ∃ K : ℝ, ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ S → ‖Vev t r‖ ≤ K := by
  set Kset : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ S} with hKset
  have hcl : IsClosed Kset :=
    (isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le continuous_snd continuous_fst).inter (isClosed_le continuous_fst continuous_const))
  have hcpt : IsCompact Kset := by
    refine ((isCompact_Icc (a := (0 : ℝ)) (b := S)).prod (isCompact_Icc (a := (0 : ℝ)) (b := S))).of_isClosed_subset
      hcl ?_
    intro p hp
    exact ⟨⟨hp.1.trans hp.2.1, hp.2.2⟩, ⟨hp.1, hp.2.1.trans hp.2.2⟩⟩
  have hpt : ∀ x : H, ∃ C : ℝ, ∀ i : Kset, ‖Vev i.1.1 i.1.2 x‖ ≤ C := fun x => by
    obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn (hc x)
    exact ⟨C, fun i => hC i.1 i.2⟩
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun i : Kset => Vev i.1.1 i.1.2) hpt
  exact ⟨C, fun r t hr hrt ht => hC ⟨(t, r), ⟨hr, hrt, ht⟩⟩⟩

/-- Continuity of `t ↦ Vev(t,0)x` on `[0,∞)`. -/
theorem eqgl_cont_Vev {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Vev : ℝ → ℝ → H →L[ℝ] H)
    (hc : ∀ T : ℝ, 0 ≤ T → ∀ x : H, ContinuousOn (fun p : ℝ × ℝ => Vev p.1 p.2 x)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}) (x : H) :
    ContinuousOn (fun t => Vev t 0 x) (Set.Ici 0) := by
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht
  have hmap : Set.MapsTo (fun r : ℝ => (r, (0 : ℝ))) (Set.Icc 0 (t + 1))
      {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ t + 1} := fun r hr => ⟨le_rfl, hr.1, hr.2⟩
  have h1 : ContinuousOn (fun r : ℝ => Vev r 0 x) (Set.Icc 0 (t + 1)) :=
    (hc (t + 1) (by linarith) x).comp (Continuous.continuousOn (by fun_prop)) hmap
  have h2 := h1.continuousWithinAt (show t ∈ Set.Icc 0 (t + 1) from ⟨ht0, by linarith⟩)
  refine h2.mono_of_mem_nhdsWithin ?_
  have h3 := inter_mem_nhdsWithin (Set.Ici (0 : ℝ)) (Iio_mem_nhds (show t < t + 1 by linarith))
  exact Filter.mem_of_superset h3 (fun r hr => ⟨hr.1, hr.2.le⟩)

theorem eqgl_eval_cont {M : ℝ} {φ : Torus d → ℝ} (hφ : MemSobolev M φ) :
    Continuous (fun z : NegSobolev d M => NegSobolev.eval z φ) := by
  have : (fun z : NegSobolev d M => NegSobolev.eval z φ) = gfb4_ell M φ :=
    funext fun z => (gfb4_ell_apply hφ z).symm
  rw [this]
  exact (gfb4_ell M φ).continuous

/-- The centered Gaussian vector `(⟨Z⁰, ψ_a⟩)_a`. -/
theorem eqgl_A_gauss {M : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z0 : Ω → NegSobolev d M) (hZ0m : Measurable Z0) (C : (Torus d → ℝ) → (Torus d → ℝ) → ℝ)
    (hlaw : IsCenteredGaussianWithCov M (P.map Z0) C) {p : ℕ} (ψ : Fin p → Torus d → ℝ)
    (hψ : ∀ a, Torus.IsSmooth (ψ a)) :
    (Matrix.of fun a b => C (ψ a) (ψ b)).PosSemidef ∧
    ∀ ξ : EuclideanSpace ℝ (Fin p),
      charFun (P.map (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Z0 ω) (ψ a) :
        EuclideanSpace ℝ (Fin p)))) ξ =
      Complex.exp (-((ξ ⬝ᵥ (Matrix.of fun a b => C (ψ a) (ψ b)) *ᵥ ξ : ℝ) : ℂ) / 2) := by
  classical
  haveI hγP : IsProbabilityMeasure (P.map Z0) := (Measure.isProbabilityMeasure_map_iff hZ0m.aemeasurable).2 inferInstance
  set γ : Measure (NegSobolev d M) := P.map Z0 with hγ
  haveI hG : IsGaussian γ := hlaw.1.1
  have hmemS : ∀ a, MemSobolev M (ψ a) := fun a => HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hψ a) _
  set ℓ : Fin p → NegSobolev d M →L[ℝ] ℝ := fun a => gfb4_ell M (ψ a) with hℓ
  have hev : ∀ a z, NegSobolev.eval z (ψ a) = ℓ a z := fun a z => (gfb4_ell_apply (hmemS a) z).symm
  have hL2 : ∀ a, MemLp (ℓ a) 2 γ := fun a => IsGaussian.memLp_dual γ (ℓ a) 2 (by simp)
  have hcov : ∀ a b, ∫ z, ℓ a z * ℓ b z ∂γ = C (ψ a) (ψ b) := by
    intro a b
    rw [← hlaw.2 (ψ a) (ψ b) (hψ a) (hψ b)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hev]
  set S : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun a b => C (ψ a) (ψ b) with hS
  have hint : ∀ a b, Integrable (fun z => ℓ a z * ℓ b z) γ := fun a b =>
    (hL2 a).integrable_mul (hL2 b)
  have hquad : ∀ ξ : Fin p → ℝ, ∫ z, (∑ a, ξ a * ℓ a z) ^ 2 ∂γ = ξ ⬝ᵥ S *ᵥ ξ := by
    intro ξ
    have e : ∀ z, (∑ a, ξ a * ℓ a z) ^ 2 = ∑ a, ∑ b, ξ a * ξ b * (ℓ a z * ℓ b z) := by
      intro z
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    simp_rw [e]
    rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ fun b _ => (hint a b).const_mul _)]
    simp only [dotProduct, Matrix.mulVec, hS, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finset_sum _ (fun b _ => (hint a b).const_mul _)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, hcov a b]
    ring
  have hSsymm : ∀ a b, S a b = S b a := by
    intro a b
    simp only [hS, Matrix.of_apply]
    rw [← hcov a b, ← hcov b a]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)
  have hPSD : S.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · ext a b
      simp [Matrix.conjTranspose_apply, hSsymm a b]
    · have := hquad x
      have h0 : 0 ≤ ∫ z, (∑ a, x a * ℓ a z) ^ 2 ∂γ := integral_nonneg fun z => sq_nonneg _
      rw [this] at h0
      simpa using h0
  refine ⟨hPSD, fun ξ => ?_⟩
  -- the linear functional
  set L : StrongDual ℝ (NegSobolev d M) := ∑ a, ξ a • ℓ a with hL
  have hLapp : ∀ z, L z = ∑ a, ξ a * ℓ a z := by
    intro z
    simp [hL, ContinuousLinearMap.sum_apply]
  have hcf : charFun (P.map (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Z0 ω) (ψ a) :
      EuclideanSpace ℝ (Fin p)))) ξ = charFunDual γ L := by
    have hAm : Measurable (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Z0 ω) (ψ a) :
        EuclideanSpace ℝ (Fin p))) :=
      measurable_toLp_eval fun a => (eqgl_eval_cont (hmemS a)).measurable.comp hZ0m
    rw [charFun_apply, integral_map hAm.aemeasurable (by fun_prop), charFunDual_apply, hγ,
      integral_map hZ0m.aemeasurable (by fun_prop)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hLapp, PiLp.inner_apply, hev]
    congr 2
  rw [hcf, IsGaussian.charFunDual_eq_of_forall_strongDual_eq_zero hlaw.1.2 L]
  have hvar : Var[L; γ] = ξ ⬝ᵥ S *ᵥ ξ := by
    have hLm : AEMeasurable L γ := L.continuous.measurable.aemeasurable
    rw [variance_of_integral_eq_zero hLm (hlaw.1.2 L)]
    simp only [Pi.pow_apply]
    rw [← hquad ξ]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only [hLapp])
  rw [hvar]

/-- The Riesz representative of `ℓ_a ∘ Vev(t,σ)` is `lpFun M (U^{σ,t} φ)`. -/
theorem eqgl_pullback_eq {M : ℝ} {D : DynData d} {ρ : ℝ → Torus d → ℝ}
    (Vev : ℝ → ℝ → NegSobolev d M →L[ℝ] NegSobolev d M) (hVev : IsDualEvolution D ρ M Vev)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {σ t : ℝ} (hσ : 0 ≤ σ) (hσt : σ ≤ t)
    (hU : MemSobolev M (propagator D ρ σ t φ)) :
    pullbackVec (eqgp_ev Vev) t σ (gfb4_ell M φ) = lpFun M (propagator D ρ σ t φ) := by
  have hmem : MemSobolev M φ := HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hφ _
  refine ext_inner_right ℝ fun x => ?_
  rw [pullback_inner]
  show gfb4_ell M φ (Vev t σ x) = _
  rw [gfb4_ell_apply hmem, hVev σ t hσ hσt x φ hφ, eval_lpFun x hU, real_inner_comm]

theorem eq_gauss_lyapunov_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (M : ℝ) (hM : (d : ℝ) / 2 + 1 < M)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (Z0 : Ω → NegSobolev d M) (hZ0 : Measurable[ℱ 0] Z0)
    (hZ0law : IsCenteredGaussianWithCov M (P.map Z0)
      (susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β))
    (G : ℝ → Ω → NegSobolev d M)
    (hG : ∀ S : ℝ, 0 ≤ S →
      IsHilbertMartingaleWithCovariation P ℱ S G (fun _ _ => covForm M β⁻¹ (withDensityReal ρβ)))
    (Vev : ℝ → ℝ → NegSobolev d M →L[ℝ] NegSobolev d M)
    (hVev : IsDualEvolution (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) M Vev)
    (hVp : ∀ T' : ℝ, 0 ≤ T' → IsPlainEvolution Vev T')
    (Zb : ℝ → Ω → NegSobolev d M)
    (hZb : ∀ t : ℝ, 0 ≤ t →
      IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d M)) G 0 t (Zb t))
    (hZbm : ∀ t, Measurable (Zb t)) (hZbc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zb t ω) (Set.Ici 0)) :
    IsStationaryGaussianField P s β hs0 hsd hβ V ρβ M (fun t ω => Vev t 0 (Z0 ω) + Zb t ω) := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hpos, hρC, -⟩ := eqgld_frozen hd hs0 hsd V hV hβ ρβ hρβ
  have hprob := hρβ.1
  have hZ0m : Measurable Z0 := hZ0.mono (ℱ.le 0) le_rfl
  have hcV := eqgl_cont_Vev Vev (fun T hT => (hVp T hT).2.2)
  refine ⟨fun t => ?_, ?_, ?_⟩
  · exact ((Vev t 0).continuous.measurable.comp hZ0m).add (hZbm t)
  · filter_upwards [hZbc] with ω hω
    exact (hcV (Z0 ω)).add hω
  intro p τ φ hτ hφ
  show P.map _ = _
  set D := PDE.mfData d s hs0 hsd V β hβ with hD
  set S : ℝ := 1 + ∑ a, τ a with hSdef
  have hsum0 : 0 ≤ ∑ a, τ a := Finset.sum_nonneg fun a _ => hτ a
  have hS : 0 < S := by rw [hSdef]; linarith
  have hτS : ∀ a, τ a ∈ Set.Icc (0 : ℝ) S := fun a =>
    ⟨hτ a, by
      have := Finset.single_le_sum (f := τ) (fun b _ => hτ b) (Finset.mem_univ a)
      rw [hSdef]; linarith⟩
  obtain ⟨K, hK⟩ := eqgl_bound Vev (hVp S hS.le).2.2
  have hmem : ∀ a, MemSobolev M (φ a) := fun a => HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hφ a) _
  set ℓ : Fin p → NegSobolev d M →L[ℝ] ℝ := fun a => gfb4_ell M (φ a) with hℓ
  set ψ : Fin p → Torus d → ℝ := fun a => propagator D (fun _ => ρβ) 0 (τ a) (φ a) with hψdef
  have hψ : ∀ a, Torus.IsSmooth (ψ a) := fun a =>
    eqgld_prop_smooth hd1 hs0 hsd V hV hβ ρβ hprob hρC hpos (φ a) (hφ a) 0 (τ a) le_rfl (hτ a)
  have hψmem : ∀ a, MemSobolev M (ψ a) := fun a => HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hψ a) _
  obtain ⟨hPSDB, hlawB, hindB⟩ := eqgp_package P ℱ G (covForm M β⁻¹ (withDensityReal ρβ)) hS (hG S hS.le)
    Vev hK (hVp S hS.le).2.2 Zb (fun t ht => hZb t ht.1) hZbm Z0 hZ0 τ hτS ℓ
  obtain ⟨hPSDA, hcharA⟩ := eqgl_A_gauss P Z0 hZ0m _ hZ0law ψ hψ
  set A : Ω → EuclideanSpace ℝ (Fin p) := fun ω =>
    (WithLp.toLp 2 fun a => NegSobolev.eval (Z0 ω) (ψ a) : EuclideanSpace ℝ (Fin p)) with hA
  set B : Ω → EuclideanSpace ℝ (Fin p) := fun ω =>
    (WithLp.toLp 2 fun a => ℓ a (Zb (τ a) ω) : EuclideanSpace ℝ (Fin p)) with hB
  have hTm : Measurable (fun z : NegSobolev d M =>
      (WithLp.toLp 2 fun a => NegSobolev.eval z (ψ a) : EuclideanSpace ℝ (Fin p))) :=
    measurable_toLp_eval fun a => (eqgl_eval_cont (hψmem a)).measurable
  have hAm : Measurable A := hTm.comp hZ0m
  have hBm : Measurable B := measurable_toLp_eval fun a => (ℓ a).continuous.measurable.comp (hZbm _)
  have hindAB : IndepFun B A P := hindB.comp measurable_id hTm
  have hX : (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Vev (τ a) 0 (Z0 ω) + Zb (τ a) ω) (φ a) :
      EuclideanSpace ℝ (Fin p))) = fun ω => A ω + B ω := by
    funext ω
    refine PiLp.ext fun a => ?_
    simp only [hA, hB, PiLp.add_apply]
    rw [← gfb4_ell_apply (hmem a), map_add, gfb4_ell_apply (hmem a),
      hVev 0 (τ a) le_rfl (hτ a) (Z0 ω) (φ a) (hφ a)]
  have hXm : Measurable (fun ω => A ω + B ω) := hAm.add hBm
  -- the two covariance matrices
  set SA : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun a b =>
    susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β (ψ a) (ψ b) with hSA
  set SB : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun a b => ∫ σ in Set.Icc 0 (min (τ a) (τ b)),
        covForm M β⁻¹ (withDensityReal ρβ) (pullbackVec (eqgp_ev Vev) (τ a) σ (ℓ a))
          (pullbackVec (eqgp_ev Vev) (τ b) σ (ℓ b)) with hSB
  have hcharB : ∀ ξ : EuclideanSpace ℝ (Fin p), charFun (P.map B) ξ =
      Complex.exp (-((ξ ⬝ᵥ SB *ᵥ ξ : ℝ) : ℂ) / 2) := by
    intro ξ
    rw [hlawB, charFun_multivariateGaussian hPSDB]
    simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, neg_div]
  have hPSD : (SA + SB).PosSemidef := hPSDA.add hPSDB
  have hchar : ∀ ξ : EuclideanSpace ℝ (Fin p), charFun (P.map (fun ω => A ω + B ω)) ξ =
      Complex.exp (-((ξ ⬝ᵥ (SA + SB) *ᵥ ξ : ℝ) : ℂ) / 2) := by
    intro ξ
    have h1 := congrFun (hindAB.symm.charFun_map_fun_add_eq_mul hAm.aemeasurable hBm.aemeasurable) ξ
    rw [h1, Pi.mul_apply, hcharA ξ, hcharB ξ, ← Complex.exp_add, Matrix.add_mulVec, dotProduct_add]
    congr 1
    push_cast
    ring
  have hlaw : P.map (fun ω => A ω + B ω) = multivariateGaussian 0 (SA + SB) :=
    eq_multivariateGaussian P hXm hPSD hchar
  -- identification with the stationary lag covariance
  have hSBeq : SB = Matrix.of fun a b => 2 * β⁻¹ * ∫ σ in Set.Icc 0 (min (τ a) (τ b)),
      eqgld_E D ρβ (φ a) (φ b) (τ a) (τ b) σ := by
    ext a b
    simp only [hSB, Matrix.of_apply]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    have hσa : σ ≤ τ a := hσ.2.trans (min_le_left _ _)
    have hσb : σ ≤ τ b := hσ.2.trans (min_le_right _ _)
    have hsa := eqgld_prop_smooth hd1 hs0 hsd V hV hβ ρβ hprob hρC hpos (φ a) (hφ a) σ (τ a) hσ.1 hσa
    have hsb := eqgld_prop_smooth hd1 hs0 hsd V hV hβ ρβ hprob hρC hpos (φ b) (hφ b) σ (τ b) hσ.1 hσb
    simp only [hℓ]
    rw [eqgl_pullback_eq Vev hVev (hφ a) hσ.1 hσa (HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hsa _),
      eqgl_pullback_eq Vev hVev (hφ b) hσ.1 hσb (HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hsb _),
      eqglc_covForm_lpFun hM (inv_nonneg.2 hβ.le) (MFLinear.continuous_of_isSmooth hρC)
        (fun x => (hpos x).le) hsa hsb]
    rfl
  have htot := eqgld_cov_total hd hs0 hsd V hV hβ ρβ hρβ τ hτ φ hφ
  rw [hX, hlaw]
  congr 1
  rw [← htot, hSBeq]
  ext a b
  simp only [hSA, Matrix.add_apply, Matrix.of_apply]
  rfl

end HRS.MD.EQGaussLyap

end
