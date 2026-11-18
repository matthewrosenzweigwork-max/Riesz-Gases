import HRS.MC.E213Q2
import HRS.Main.ThermLin2St1

/-!
# Packet e213r, part 2: finite-dimensional laws and covariance of a stochastic convolution

For a stochastic convolution `Zb_t = ∫_0^t V(t,σ) dG(σ)` of a continuous Hilbert martingale `G` with deterministic covariation
density `Cd` against a plain evolution `V` (`t25p_Zb_gaussian`, positive semidefiniteness `tl2St_cov_psd`):

* `e213r_fdd_of_vec_law`: a family of Gaussian vector laws for smooth tests gives `FddGaussian`;
* `e213r_conv_fdd_cov`: `Zb` is finite-dimensionally Gaussian on `[0,T]` and
  `E[Zb_{ta}(φa) Zb_{tb}(φb)] = ∫_{[0,ta∧tb]} Cd_σ(pullback φa, pullback φb) dσ` for smooth tests.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213R

open HRS HRS.Sec7 HRS.Uniform HRS.Uniform.Q54c HRS.GF HRS.T25P HRS.ThermLin.Plan2 HRS.MC.E213Q

variable {d : ℕ}

/-- Gaussian vector laws for smooth tests give finite-dimensional Gaussianity of the Fourier coordinates. -/
theorem e213r_fdd_of_vec_law {m T : ℝ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → Ω → NegSobolev d m) (hZm : ∀ t, Measurable (Z t))
    (hvec : ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ), (∀ a, ts a ∈ Set.Icc (0 : ℝ) T) →
      (∀ a, Torus.IsSmooth (φ a)) → ∃ S : Matrix (Fin p) (Fin p) ℝ,
        P.map (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Z (ts a) ω) (φ a) :
          EuclideanSpace ℝ (Fin p))) = multivariateGaussian 0 S) :
    FddGaussian P Z (Set.Icc 0 T) := by
  classical
  intro ι _ τ hτ J
  set N := Fintype.card (ι × J) with hN
  let e : ι × J ≃ Fin N := Fintype.equivFin _
  set ts : Fin N → ℝ := fun a => τ (e.symm a).1 with hts_def
  set φ : Fin N → Torus d → ℝ := fun a => Torus.realMode ((e.symm a).2 : NonzeroLattice d) with hφdef
  have hts : ∀ a, ts a ∈ Set.Icc 0 T := fun a => hτ _
  have hφ : ∀ a, Torus.IsSmooth (φ a) := fun a => HRS.Uniform.Q48b.q48b_isSmooth_realMode _
  have hmemφ : ∀ a, MemSobolev m (φ a) := fun a =>
    HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hφ a) m
  obtain ⟨S, hlaw⟩ := hvec N ts φ hts hφ
  set Gy : Ω → EuclideanSpace ℝ (Fin N) := fun ω => WithLp.toLp 2 fun a =>
    NegSobolev.eval (Z (ts a) ω) (φ a) with hGy
  have hGym : Measurable Gy :=
    measurable_toLp_eval fun a => (continuous_eval_const (hmemφ a)).measurable.comp (hZm _)
  haveI : IsGaussian (P.map Gy) := by
    rw [hlaw]; infer_instance
  have hGG : HasGaussianLaw Gy P := IsGaussian.hasGaussianLaw hGym.aemeasurable
  let Ψ : EuclideanSpace ℝ (Fin N) →L[ℝ] (ι × J → ℝ) :=
    ContinuousLinearMap.pi fun p =>
      (EuclideanSpace.proj (e p) : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
  have hvecΨ : (fun ω (p : ι × J) => NegSobolev.fourierCoeff (Z (τ p.1) ω) p.2) = fun ω => Ψ (Gy ω) := by
    funext ω p
    simp only [Ψ, ContinuousLinearMap.pi_apply, EuclideanSpace.coe_proj, hGy, WithLp.ofLp_toLp]
    have h1 : ts (e p) = τ p.1 := by simp [hts_def]
    have h2 : φ (e p) = Torus.realMode ((p.2 : J) : NonzeroLattice d) := by simp [hφdef]
    rw [h1, h2, HRS.Uniform.Q54c.eval_realMode]
  refine ⟨?_, ?_⟩
  · rw [hvecΨ]
    exact hGG.map_fun Ψ
  · have hintG : ∀ a, Integrable (fun ω => Gy ω a) P := fun a => by
      have := (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).integrable_comp hGG.integrable
      exact this
    have hmeanG : ∀ a, ∫ ω, Gy ω a ∂P = 0 := fun a => by
      have h0 : ∫ ω, Gy ω ∂P = 0 := by
        have : ∫ x, x ∂(P.map Gy) = ∫ ω, Gy ω ∂P :=
          integral_map hGym.aemeasurable aestronglyMeasurable_id
        rw [← this, hlaw]
        exact integral_id_multivariateGaussian
      have := (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).integral_comp_comm
        hGG.integrable
      simp only [EuclideanSpace.coe_proj] at this
      rw [this, h0]; rfl
    intro p
    have hp : (fun ω => NegSobolev.fourierCoeff (Z (τ p.1) ω) p.2) = fun ω => Gy ω (e p) := by
      funext ω
      have h1 : ts (e p) = τ p.1 := by simp [hts_def]
      have h2 : φ (e p) = Torus.realMode ((p.2 : J) : NonzeroLattice d) := by simp [hφdef]
      simp only [hGy, WithLp.ofLp_toLp]
      rw [h1, h2, HRS.Uniform.Q54c.eval_realMode]
    rw [hp, hmeanG]

/-- Second moments of a Gaussian vector law (positive semidefinite covariance). -/
theorem e213r_second_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p : ℕ}
    (W : Ω → EuclideanSpace ℝ (Fin p)) (hW : AEMeasurable W P) (S : Matrix (Fin p) (Fin p) ℝ)
    (hS : S.PosSemidef) (h : Measure.map W P = multivariateGaussian 0 S) (a b : Fin p) :
    ∫ ω, W ω a * W ω b ∂P = S a b :=
  HRS.Qch.gauss_prod_fin P W hW S hS h a b

/-- **Stochastic convolutions: fdd Gaussianity and covariance.** -/
theorem e213r_conv_fdd_cov {m T K : ℝ} (hK : 0 ≤ K) (hT0 : 0 < T)
    (V : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hVc : ∀ y : NegSobolev d m, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 y)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})
    (hVb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ‖V t r‖ ≤ K) {Ω' : Type} {mΩ' : MeasurableSpace Ω'}
    (P' : Measure Ω') [IsProbabilityMeasure P'] {ℱ'' : Filtration ℝ mΩ'} (G : ℝ → Ω' → NegSobolev d m)
    (Cd : ℝ → NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ)
    (hG : IsHilbertMartingaleWithCovariation P' ℱ'' T G (fun r _ => Cd r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0)
    (Zb : ℝ → Ω' → NegSobolev d m)
    (hZb : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P' V (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zb t))
    (hZbm : ∀ t, Measurable (Zb t)) :
    FddGaussian P' Zb (Set.Icc 0 T) ∧
    ∀ (ta tb : ℝ) (φa φb : Torus d → ℝ), Torus.IsSmooth φa → Torus.IsSmooth φb →
      ta ∈ Set.Icc (0 : ℝ) T → tb ∈ Set.Icc (0 : ℝ) T →
      ∫ ω, NegSobolev.eval (Zb ta ω) φa * NegSobolev.eval (Zb tb ω) φb ∂P' =
        ∫ σ in Set.Icc 0 (min ta tb),
          Cd σ (pullbackVec (HRS.Uniform.Comp28.plainData V) ta σ (gfb4_ell m φa))
            (pullbackVec (HRS.Uniform.Comp28.plainData V) tb σ (gfb4_ell m φb)) := by
  have hmemS : ∀ {φ : Torus d → ℝ}, Torus.IsSmooth φ → MemSobolev m φ := fun hφ =>
    HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hφ m
  -- the vector law with its positive semidefinite covariance, for all smooth tests
  have hlawpsd : ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ), (∀ a, ts a ∈ Set.Icc (0 : ℝ) T) →
      (∀ a, Torus.IsSmooth (φ a)) →
      (Matrix.of fun a b => ∫ σ in Set.Icc 0 (min (ts a) (ts b)),
          Cd σ (pullbackVec (HRS.Uniform.Comp28.plainData V) (ts a) σ (gfb4_ell m (φ a)))
            (pullbackVec (HRS.Uniform.Comp28.plainData V) (ts b) σ (gfb4_ell m (φ b)))).PosSemidef ∧
      P'.map (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Zb (ts a) ω) (φ a) :
          EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun a b => ∫ σ in Set.Icc 0 (min (ts a) (ts b)),
          Cd σ (pullbackVec (HRS.Uniform.Comp28.plainData V) (ts a) σ (gfb4_ell m (φ a)))
            (pullbackVec (HRS.Uniform.Comp28.plainData V) (ts b) σ (gfb4_ell m (φ b)))) := by
    intro p ts φ hts hφ
    refine ⟨?_, t25p_Zb_gaussian hK hT0 V hVc hVb P' G Cd hG hGc hGz Zb hZb hZbm ts hts φ
      (fun a => hmemS (hφ a))⟩
    refine tl2St_cov_psd (B := K * ∑ b, ‖gfb4_ell m (φ b)‖) hG hGc hGz hT0 ts hts
      (fun a σ => pullbackVec (HRS.Uniform.Comp28.plainData V) (ts a) σ (gfb4_ell m (φ a))) ?_ ?_
    · intro a σ hσ
      have h1 := t25p_norm_pullback_le V hVb hK hσ.1 hσ.2 (hts a).2 (gfb4_ell m (φ a))
      refine h1.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hK
      exact Finset.single_le_sum (f := fun b => ‖gfb4_ell m (φ b)‖) (fun b _ => norm_nonneg _)
        (Finset.mem_univ a)
    · intro a x
      exact t25p_pullback_weak V hVc (hts a) _ x
  refine ⟨e213r_fdd_of_vec_law P' Zb hZbm fun p ts φ hts hφ => ⟨_, (hlawpsd p ts φ hts hφ).2⟩, ?_⟩
  intro ta tb φa φb hφa hφb hta htb
  obtain ⟨hpsd, hlaw⟩ := hlawpsd 2 ![ta, tb] ![φa, φb]
    (by intro a; fin_cases a <;> simp [hta, htb])
    (by intro a; fin_cases a <;> simp [hφa, hφb])
  have hWm : Measurable (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Zb (![ta, tb] a) ω) (![φa, φb] a) :
      EuclideanSpace ℝ (Fin 2))) :=
    measurable_toLp_eval fun a => by
      fin_cases a
      · exact (continuous_eval_const (hmemS hφa)).measurable.comp (hZbm _)
      · exact (continuous_eval_const (hmemS hφb)).measurable.comp (hZbm _)
  have := e213r_second_moment P' _ hWm.aemeasurable _ hpsd hlaw 0 1
  simpa using this

end HRS.MC.E213R
