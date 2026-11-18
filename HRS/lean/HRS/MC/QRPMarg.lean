import HRS.MC.QRVocab
import HRS.MC.L2C0
import HRS.MC.QRPMargAux1
import HRS.MC.QRPMargAux2

/-!
# QRPMarg: `qrs_gauss_marginals_proof` (finite-dimensional Gaussianity of `η^t`, `η̄^t`, `η^t - η̄^t`)

Relocated proof of `HRS.MC.QRSpec.qrs_gauss_marginals`.  Route: `η̂_k^t = G_k + Y₀(U^{0,t}e_k)`; the propagator is smooth
(`HRS.MC.L2C0.l2c0_proof`), so `Y₀(U^{0,t}e_k)` is a continuous linear functional of `Y₀`; `IsSameNoise` gives the
joint centred Gaussian noise vector independent of `(Y₀, Ys₀)`, and `(Y₀, Ys₀)` are independent Gaussians; the three
families are linear functionals of `((Y₀, Ys₀), G)` (`QRPMargAux1.qm_core`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.QRSpec.Marg

open HRS.Sec7

variable {d : ℕ}

theorem qrs_gauss_marginals_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Y₀ Ys₀ : Ω → NegSobolev d r) (η ηs : ℝ → Ω → NegSobolev d r),
      IsCenteredGaussianWithCov r (P.map Y₀)
        (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρ₀) R.β₀) →
      IsCenteredGaussianWithCov r (P.map Ys₀)
        (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρβ) R.β) →
      IndepFun Y₀ Ys₀ P →
      (∀ T : ℝ, IsLinearFluctuationSolution P R.D R.ρ r R.D.invβ T Y₀ η) →
      (∀ T : ℝ, IsLinearFluctuationSolution P R.D (fun _ => R.ρβ) r R.D.invβ T Ys₀ ηs) →
      IsSameNoise R.D R.ρ (fun _ => R.ρβ) r P Y₀ Ys₀ η ηs →
      ∀ t : ℝ, 0 ≤ t →
        HasFiniteGaussianCoeffs P (η t) ∧ HasFiniteGaussianCoeffs P (ηs t) ∧
        HasFiniteGaussianCoeffs P (fun ω => η t ω - ηs t ω) := by
  intro Ω _ P _ Y₀ Ys₀ η ηs hY hYs hind hη hηs hsame t ht
  have hmY : AEMeasurable Y₀ P := by
    have h0 := hη 0
    exact (h0.meas 0).aemeasurable.congr h0.init
  have hmYs : AEMeasurable Ys₀ P := by
    have h0 := hηs 0
    exact (h0.meas 0).aemeasurable.congr h0.init
  have hmη : Measurable (η t) := (hη t).meas t
  have hmηs : Measurable (ηs t) := (hηs t).meas t
  have := hY.1.1
  have := hYs.1.1
  have hYg : HasGaussianLaw Y₀ P := qm_hasGaussianLaw_of_map hmY rfl
  have hYsg : HasGaussianLaw Ys₀ P := qm_hasGaussianLaw_of_map hmYs rfl
  have m0 := qm_integral_dual_zero hYg hY.1.2
  have m1 := qm_integral_dual_zero hYsg hYs.1.2
  have hprop : ∀ k : NonzeroLattice d, ∃ a b c : StrongDual ℝ (NegSobolev d r),
      (∀ F, a F = NegSobolev.eval F (propagator R.D R.ρ 0 t (Torus.realMode k))) ∧
      (∀ F, b F = NegSobolev.eval F (propagator R.D (fun _ => R.ρβ) 0 t (Torus.realMode k))) ∧
      (∀ F, c F = NegSobolev.fourierCoeff F k) := by
    intro k
    obtain ⟨h1, h2⟩ := HRS.MC.L2C0.l2c0_proof R _ (HRS.FieldSingAux.isSmooth_realMode k) 0 t le_rfl ht
    obtain ⟨a, ha⟩ := qm_evCLM r _ (HRS.StaticLimitAux.summable_weighted_smooth r h1)
    obtain ⟨b, hb⟩ := qm_evCLM r _ (HRS.StaticLimitAux.summable_weighted_smooth r h2)
    obtain ⟨c, hc⟩ := qm_evCLM r _
      (HRS.StaticLimitAux.summable_weighted_smooth r (HRS.FieldSingAux.isSmooth_realMode k))
    exact ⟨a, b, c, ha, hb, fun F => by rw [hc, qm_eval_realMode]⟩
  choose aL bL cL haL hbL hcL using hprop
  have key : ∀ S : Finset (NonzeroLattice d),
      (HasGaussianLaw (fun ω (k : S) => NegSobolev.fourierCoeff (η t ω) k.1) P ∧
        ∀ k : S, ∫ ω, NegSobolev.fourierCoeff (η t ω) k.1 ∂P = 0) ∧
      (HasGaussianLaw (fun ω (k : S) => NegSobolev.fourierCoeff (ηs t ω) k.1) P ∧
        ∀ k : S, ∫ ω, NegSobolev.fourierCoeff (ηs t ω) k.1 ∂P = 0) ∧
      (HasGaussianLaw (fun ω (k : S) => NegSobolev.fourierCoeff (η t ω - ηs t ω) k.1) P ∧
        ∀ k : S, ∫ ω, NegSobolev.fourierCoeff (η t ω - ηs t ω) k.1 ∂P = 0) := by
    intro S
    let e : S ≃ Fin S.card := S.equivFin
    let φ : Fin S.card → Torus d → ℝ := fun a => Torus.realMode (e.symm a).1
    have hφ : ∀ a, Torus.IsSmooth (φ a) := fun a => HRS.FieldSingAux.isSmooth_realMode _
    have hs := hsame S.card S.card (fun _ => t) φ (fun _ => t) φ (fun _ => ht) (fun _ => ht) hφ hφ
    obtain ⟨G, hGl, hGr, hind2, Cv, hlaw⟩ : ∃ G : Ω → EuclideanSpace ℝ (Fin S.card ⊕ Fin S.card),
        (∀ ω a, G ω (Sum.inl a) = noisePart R.D R.ρ Y₀ η t (φ a) ω) ∧
        (∀ ω a, G ω (Sum.inr a) = noisePart R.D (fun _ => R.ρβ) Ys₀ ηs t (φ a) ω) ∧
        IndepFun (fun ω => (Y₀ ω, Ys₀ ω)) G P ∧
        ∃ Cv, law P G = multivariateGaussian 0 Cv :=
      ⟨fun ω => WithLp.toLp 2 (Sum.elim (fun a => noisePart R.D R.ρ Y₀ η t (φ a) ω)
        (fun b => noisePart R.D (fun _ => R.ρβ) Ys₀ ηs t (φ b) ω)), fun _ _ => rfl, fun _ _ => rfl,
        hs.1, _, hs.2⟩
    have hGl' : ∀ ω (k : S), G ω (Sum.inl (e k)) = cL k.1 (η t ω) - aL k.1 (Y₀ ω) := by
      intro ω k
      rw [hGl]; unfold noisePart
      simp only [φ, e, Equiv.symm_apply_apply]
      rw [qm_eval_realMode, haL, hcL]
    have hGr' : ∀ ω (k : S), G ω (Sum.inr (e k)) = cL k.1 (ηs t ω) - bL k.1 (Ys₀ ω) := by
      intro ω k
      rw [hGr]; unfold noisePart
      simp only [φ, e, Equiv.symm_apply_apply]
      rw [qm_eval_realMode, hbL, hcL]
    have hmG : AEMeasurable G P := by
      have h1 : ∀ i, AEMeasurable (fun ω => G ω i) P := by
        rintro (a | b)
        · have h : (fun ω => G ω (Sum.inl a)) =
              fun ω => cL (e.symm a).1 (η t ω) - aL (e.symm a).1 (Y₀ ω) := by
            funext ω
            simpa using hGl' ω (e.symm a)
          rw [h]
          exact ((cL _).continuous.measurable.comp hmη).aemeasurable.sub
            ((aL _).continuous.measurable.comp_aemeasurable hmY)
        · have h : (fun ω => G ω (Sum.inr b)) =
              fun ω => cL (e.symm b).1 (ηs t ω) - bL (e.symm b).1 (Ys₀ ω) := by
            funext ω
            simpa using hGr' ω (e.symm b)
          rw [h]
          exact ((cL _).continuous.measurable.comp hmηs).aemeasurable.sub
            ((bL _).continuous.measurable.comp_aemeasurable hmYs)
      exact (MeasurableEquiv.toLp 2 (Fin S.card ⊕ Fin S.card → ℝ)).measurable.comp_aemeasurable
        (aemeasurable_pi_iff.2 h1)
    have hGg : HasGaussianLaw G P := qm_hasGaussianLaw_of_map hmG hlaw
    have m2 := qm_mvg_dual_zero Cv hmG hlaw
    have c1 := qm_core hYg hYsg hGg hind hind2 m0 m1 m2 (ι := S) (fun k => aL k.1)
      (fun _ => 0) (fun k => EuclideanSpace.proj (Sum.inl (e k)))
    have c2 := qm_core hYg hYsg hGg hind hind2 m0 m1 m2 (ι := S) (fun _ => 0) (fun k => bL k.1)
      (fun k => EuclideanSpace.proj (Sum.inr (e k)))
    have c3 := qm_core hYg hYsg hGg hind hind2 m0 m1 m2 (ι := S) (fun k => aL k.1)
      (fun k => - bL k.1) (fun k => EuclideanSpace.proj (Sum.inl (e k)) -
        EuclideanSpace.proj (Sum.inr (e k)))
    have eq1 : ∀ ω (k : S), NegSobolev.fourierCoeff (η t ω) k.1 =
        aL k.1 (Y₀ ω) + (0 : StrongDual ℝ (NegSobolev d r)) (Ys₀ ω) +
          (EuclideanSpace.proj (Sum.inl (e k)) :
            StrongDual ℝ (EuclideanSpace ℝ (Fin S.card ⊕ Fin S.card))) (G ω) := by
      intro ω k
      simp [hGl', ← hcL]
    have eq2 : ∀ ω (k : S), NegSobolev.fourierCoeff (ηs t ω) k.1 =
        (0 : StrongDual ℝ (NegSobolev d r)) (Y₀ ω) + bL k.1 (Ys₀ ω) +
          (EuclideanSpace.proj (Sum.inr (e k)) :
            StrongDual ℝ (EuclideanSpace ℝ (Fin S.card ⊕ Fin S.card))) (G ω) := by
      intro ω k
      simp [hGr', ← hcL]
    have eq3 : ∀ ω (k : S), NegSobolev.fourierCoeff (η t ω - ηs t ω) k.1 =
        aL k.1 (Y₀ ω) + (- bL k.1) (Ys₀ ω) +
          ((EuclideanSpace.proj (Sum.inl (e k)) - EuclideanSpace.proj (Sum.inr (e k)) :
            StrongDual ℝ (EuclideanSpace ℝ (Fin S.card ⊕ Fin S.card)))) (G ω) := by
      intro ω k
      rw [qm_fc_sub]
      simp [hGl', hGr', ← hcL]
      ring
    refine ⟨⟨?_, fun k => ?_⟩, ⟨?_, fun k => ?_⟩, ⟨?_, fun k => ?_⟩⟩
    · have h : (fun ω (k : S) => NegSobolev.fourierCoeff (η t ω) k.1) = fun ω k =>
          aL k.1 (Y₀ ω) + (0 : StrongDual ℝ (NegSobolev d r)) (Ys₀ ω) +
          (EuclideanSpace.proj (Sum.inl (e k)) :
            StrongDual ℝ (EuclideanSpace ℝ (Fin S.card ⊕ Fin S.card))) (G ω) :=
        funext fun ω => funext fun k => eq1 ω k
      rw [h]; exact c1.1
    · simp_rw [eq1]; exact c1.2 k
    · have h : (fun ω (k : S) => NegSobolev.fourierCoeff (ηs t ω) k.1) = fun ω k =>
          (0 : StrongDual ℝ (NegSobolev d r)) (Y₀ ω) + bL k.1 (Ys₀ ω) +
          (EuclideanSpace.proj (Sum.inr (e k)) :
            StrongDual ℝ (EuclideanSpace ℝ (Fin S.card ⊕ Fin S.card))) (G ω) :=
        funext fun ω => funext fun k => eq2 ω k
      rw [h]; exact c2.1
    · simp_rw [eq2]; exact c2.2 k
    · have h : (fun ω (k : S) => NegSobolev.fourierCoeff (η t ω - ηs t ω) k.1) = fun ω k =>
          aL k.1 (Y₀ ω) + (- bL k.1) (Ys₀ ω) +
          ((EuclideanSpace.proj (Sum.inl (e k)) - EuclideanSpace.proj (Sum.inr (e k)) :
            StrongDual ℝ (EuclideanSpace ℝ (Fin S.card ⊕ Fin S.card)))) (G ω) :=
        funext fun ω => funext fun k => eq3 ω k
      rw [h]; exact c3.1
    · simp_rw [eq3]; exact c3.2 k
  exact ⟨fun S => ⟨(key S).1.1, fun k => by simpa using (key {k}).1.2 ⟨k, by simp⟩⟩,
    fun S => ⟨(key S).2.1.1, fun k => by simpa using (key {k}).2.1.2 ⟨k, by simp⟩⟩,
    fun S => ⟨(key S).2.2.1, fun k => by simpa using (key {k}).2.2.2 ⟨k, by simp⟩⟩⟩

end HRS.MC.QRSpec.Marg

end
