import HRS.MC.QRPMargAux2
import HRS.MC.L2C0
import HRS.MC.QRVocab
import HRS.Sections.Sec7Setting

/-!
# S7FCW2 helpers: finite-dimensional Gaussianity of the Fourier coordinates of one linear solution

Helpers for `s7_FC_C1_coeffs` (FC-C1, relocated proof in `HRS/MC/S7FCW2.lean`).  Route: for a finite set `S`
of nonzero frequencies, `η̂^t_k = Y₀(U^{0,t}e_k) + G_k` where `G` is the noise part of `gaussian_part`
(centred Gaussian, independent of `Y₀`), and `Y₀(U^{0,t}e_k)` is a continuous linear functional of `Y₀`.
The bookkeeping lemmas are the generic `HRS.MC.QRSpec.Marg.*` ones (`QRPMargAux1/2`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.S7FCW2

open HRS HRS.Sec7 HRS.MC.QRSpec

variable {d : ℕ}

/-- Joint Gaussianity and mean zero of `(a_i(Y) + g_i(G))_i` for a Gaussian `Y` and a Gaussian `G` independent of `Y`
(the one-field analogue of `HRS.MC.QRSpec.Marg.qm_core`). -/
theorem S7FCW2_core {H E : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
    [SecondCountableTopology H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [SecondCountableTopology E]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → H} {G : Ω → E}
    (hY : HasGaussianLaw Y P) (hG : HasGaussianLaw G P) (hind : IndepFun G Y P)
    (m0 : ∀ a : StrongDual ℝ H, ∫ ω, a (Y ω) ∂P = 0)
    (m2 : ∀ g : StrongDual ℝ E, ∫ ω, g (G ω) ∂P = 0)
    {ι : Type*} [Fintype ι] (a : ι → StrongDual ℝ H) (g : ι → StrongDual ℝ E) :
    HasGaussianLaw (fun ω i => a i (Y ω) + g i (G ω)) P ∧
      ∀ i, ∫ ω, (a i (Y ω) + g i (G ω)) ∂P = 0 := by
  have hW : HasGaussianLaw (fun ω => (G ω, Y ω)) P := hind.hasGaussianLaw hG hY
  refine ⟨?_, fun i => ?_⟩
  · let L : (E × H) →L[ℝ] (ι → ℝ) := ContinuousLinearMap.pi fun i =>
      (g i).comp (ContinuousLinearMap.fst ℝ E H) + (a i).comp (ContinuousLinearMap.snd ℝ E H)
    have := hW.map_fun L
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    funext i
    simp [L, add_comm]
  · have i1 : Integrable (fun ω => a i (Y ω)) P := (hY.map_fun (a i)).integrable
    have i2 : Integrable (fun ω => g i (G ω)) P := (hG.map_fun (g i)).integrable
    rw [integral_add i1 i2, m0 (a i), m2 (g i)]
    simp

/-- Evaluation against a smooth test function is a continuous linear functional on `E_r`. -/
theorem S7FCW2_ev (r : ℝ) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) :
    ∃ ℓ : StrongDual ℝ (NegSobolev d r), ∀ F, ℓ F = NegSobolev.eval F φ :=
  HRS.MC.QRSpec.Marg.qm_evCLM r φ (HRS.StaticLimitAux.summable_weighted_smooth r hφ)

/-- Finite-dimensional Gaussianity of the real Fourier coordinates `η̂^t_k` of a single centred Gaussian
linear solution at a time `t ≥ 0`: the one-field version of `HRS.MC.QRSpec.Marg.qrs_gauss_marginals_proof`. -/
theorem S7FCW2_fgc {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : DynData d) (ρ : ℝ → Torus d → ℝ) (r q t : ℝ) (C : (Torus d → ℝ) → (Torus d → ℝ) → ℝ)
    (Y₀ : Ω → NegSobolev d r) (η : ℝ → Ω → NegSobolev d r)
    (hY : IsCenteredGaussianWithCov r (P.map Y₀) C)
    (hLin : IsLinearFluctuationSolution P D ρ r q t Y₀ η) (ht : 0 ≤ t)
    (hψ : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → Torus.IsSmooth (propagator D ρ 0 t φ)) :
    HasFiniteGaussianCoeffs P (η t) := by
  have hGauss : IsGaussian (P.map Y₀) := hY.1.1
  have hmY : AEMeasurable Y₀ P := (hLin.meas 0).aemeasurable.congr hLin.init
  have hmη : Measurable (η t) := hLin.meas t
  have hYg : HasGaussianLaw Y₀ P := HRS.MC.QRSpec.Marg.qm_hasGaussianLaw_of_map hmY rfl
  have m0 := HRS.MC.QRSpec.Marg.qm_integral_dual_zero hYg hY.1.2
  have key : ∀ S : Finset (NonzeroLattice d),
      HasGaussianLaw (fun ω (k : S) => NegSobolev.fourierCoeff (η t ω) k.1) P ∧
        ∀ k : S, ∫ ω, NegSobolev.fourierCoeff (η t ω) k.1 ∂P = 0 := by
    intro S
    let e : S ≃ Fin S.card := S.equivFin
    let φ : Fin S.card → Torus d → ℝ := fun a => Torus.realMode (e.symm a).1
    have hφ : ∀ a, Torus.IsSmooth (φ a) := fun a => HRS.FieldSingAux.isSmooth_realMode _
    have hs := hLin.gaussian_part S.card (fun _ => t) φ (fun _ => ⟨ht, le_rfl⟩) hφ
    let G : Ω → EuclideanSpace ℝ (Fin S.card) := fun ω => WithLp.toLp 2 fun a =>
      NegSobolev.eval (η t ω) (φ a) - NegSobolev.eval (Y₀ ω) (propagator D ρ 0 t (φ a))
    have hind : IndepFun G Y₀ P := hs.1
    obtain ⟨Cv, hlaw⟩ : ∃ Cv : Matrix (Fin S.card) (Fin S.card) ℝ, P.map G = multivariateGaussian 0 Cv :=
      ⟨_, hs.2⟩
    have hGa : ∀ ω a, G ω a = NegSobolev.eval (η t ω) (φ a) -
        NegSobolev.eval (Y₀ ω) (propagator D ρ 0 t (φ a)) := fun ω a => rfl
    -- continuous linear functionals
    have hcφ : ∀ a : Fin S.card, ∃ ℓ : StrongDual ℝ (NegSobolev d r),
        ∀ F, ℓ F = NegSobolev.eval F (φ a) := fun a => S7FCW2_ev r (φ a) (hφ a)
    have haψ : ∀ a : Fin S.card, ∃ ℓ : StrongDual ℝ (NegSobolev d r),
        ∀ F, ℓ F = NegSobolev.eval F (propagator D ρ 0 t (φ a)) :=
      fun a => S7FCW2_ev r _ (hψ _ (hφ a))
    choose cφ hcφ using hcφ
    choose aψ haψ using haψ
    have hmG : AEMeasurable G P := by
      have h1 : ∀ a, AEMeasurable (fun ω => G ω a) P := by
        intro a
        have h : (fun ω => G ω a) = fun ω => cφ a (η t ω) - aψ a (Y₀ ω) := by
          funext ω
          rw [hGa, hcφ, haψ]
        rw [h]
        exact ((cφ a).continuous.measurable.comp hmη).aemeasurable.sub
          ((aψ a).continuous.measurable.comp_aemeasurable hmY)
      exact (MeasurableEquiv.toLp 2 (Fin S.card → ℝ)).measurable.comp_aemeasurable
        (aemeasurable_pi_iff.2 h1)
    have hGg : HasGaussianLaw G P := HRS.MC.QRSpec.Marg.qm_hasGaussianLaw_of_map hmG hlaw
    have m2 := HRS.MC.QRSpec.Marg.qm_mvg_dual_zero Cv hmG hlaw
    have core := S7FCW2_core hYg hGg hind m0 m2 (ι := S) (fun k => aψ (e k))
      (fun k => EuclideanSpace.proj (e k))
    have hpt : ∀ ω (k : S), NegSobolev.fourierCoeff (η t ω) k.1 =
        aψ (e k) (Y₀ ω) + (EuclideanSpace.proj (e k) :
          StrongDual ℝ (EuclideanSpace ℝ (Fin S.card))) (G ω) := by
      intro ω k
      have hk : φ (e k) = Torus.realMode k.1 := by simp [φ, e]
      have e1 : NegSobolev.fourierCoeff (η t ω) k.1 = NegSobolev.eval (η t ω) (φ (e k)) := by
        rw [hk, HRS.MC.QRSpec.Marg.qm_eval_realMode]
      have e2 : aψ (e k) (Y₀ ω) = NegSobolev.eval (Y₀ ω) (propagator D ρ 0 t (φ (e k))) :=
        haψ (e k) (Y₀ ω)
      have e3 : (EuclideanSpace.proj (e k) : StrongDual ℝ (EuclideanSpace ℝ (Fin S.card))) (G ω)
          = G ω (e k) := rfl
      rw [e1, e2, e3, hGa]
      ring
    refine ⟨?_, fun k => ?_⟩
    · have hfun : (fun ω (k : S) => NegSobolev.fourierCoeff (η t ω) k.1) =
          fun ω (i : S) => aψ (e i) (Y₀ ω) + (EuclideanSpace.proj (e i) :
            StrongDual ℝ (EuclideanSpace ℝ (Fin S.card))) (G ω) :=
        funext fun ω => funext fun k => hpt ω k
      rw [hfun]
      exact core.1
    · have hfun : (fun ω => NegSobolev.fourierCoeff (η t ω) k.1) =
          fun ω => aψ (e k) (Y₀ ω) + (EuclideanSpace.proj (e k) :
            StrongDual ℝ (EuclideanSpace ℝ (Fin S.card))) (G ω) :=
        funext fun ω => hpt ω k
      rw [hfun]
      exact core.2 k
  unfold HasFiniteGaussianCoeffs
  refine fun S => ⟨(key S).1, fun k => ?_⟩
  have := (key {k}).2 ⟨k, by simp⟩
  simpa using this

end HRS.MC.Sec7.S7FCW2

end
