import HRS.Main.GFB4Aux9
import HRS.Uniform.Q45Smooth

/-!
# GFB4, part 10: `gf_law_identification` (relocated proof)

Route: replace `G` by an everywhere continuous version for the augmented filtration (`gfb4_modify`); the pairings
`⟨Z̄_{t_a}, φ_a⟩` are `L²`-limits of Itô sums against the weakly continuous test paths `σ ↦ V(t_a,σ)^*ℓ_a`, hence jointly
Gaussian with the covariance `∫ C̄_σ(ψ_a, ψ_b) dσ` (`gfb4_Zb_gaussian`) and independent of `X₀'` (`gfb4_indep_pairing`);
`ψ_a(σ) = lpFun (U^{σ,t_a} φ_a)` identifies this covariance with the one of the linear equation (`gfb4_cov_eq`); the
finite-dimensional laws agree (`gfb4_fdd`) and `Q54c.toPath_law_eq` gives the equality of path laws.
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.GF

open HRS HRS.Uniform HRS.Uniform.Q45 HRS.Uniform.Q07c

variable {d : ℕ}

theorem gf_law_identification_proof (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ)
    (hN : 2 ≤ N) (m K : ℝ) (hm : (S.γ : ℝ) ≤ m)
    (EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d m)) (hEV : GFEvo S M N m K EV)
    {Ω Ω' : Type} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (ℱ' : Filtration ℝ mΩ') (X₀' : Ω' → NegSobolev d (S.γ : ℝ)) (hX₀' : Measurable X₀')
    (G : ℝ → Ω' → NegSobolev d (S.γ : ℝ))
    (hG : IsHilbertMartingaleWithCovariation P' ℱ' S.T G
      (fun r _ => covDensT (S.γ : ℝ) (qN S N) S.T (S.ρ N) r))
    (hGind : Indep (MeasurableSpace.comap X₀' inferInstance)
      (⨆ τ ∈ Set.Icc (0 : ℝ) S.T, MeasurableSpace.comap (G τ) inferInstance) P')
    (Zb : ℝ → Ω' → NegSobolev d m) (hZb : ∀ t ∈ Set.Icc (0 : ℝ) S.T, IsStochConv P' EV.VE EV.j G 0 t (Zb t))
    (hZbc : ∀ᵐ ω ∂P', ContinuousOn (fun t => Zb t ω) (Set.Icc 0 S.T)) (hZbm : ∀ t, Measurable (Zb t))
    (Y₀ : Ω → NegSobolev d m) (hY₀ : Measurable Y₀) (hlaw : P.map Y₀ = P'.map (fun ω' => EV.j (X₀' ω')))
    (Y : ℝ → Ω → NegSobolev d m)
    (hY : IsLinearFluctuationSolution P (S.dynM M N) (S.ρ N) m (qN S N) S.T Y₀ Y) :
    law P (toPath m S.T Y) =
      law P' (windowPath 0 S.T (fun t ω' => EV.VE t 0 (EV.j (X₀' ω')) + Zb t ω')) := by
  have hT0 : 0 < S.T := S.hT
  have hCd0 : ∀ σ, σ ∉ Set.Icc 0 S.T → covDensT (S.γ : ℝ) (qN S N) S.T (S.ρ N) σ = 0 := by
    intro σ hσ
    simp [covDensT, hσ]
  obtain ⟨G', hG', hGc, hGz, hGG⟩ := gfb4_modify P' ℱ' hT0.le G
    (fun r => covDensT (S.γ : ℝ) (qN S N) S.T (S.ρ N) r) hCd0 hG
  have hZb' : ∀ t ∈ Set.Icc (0 : ℝ) S.T, IsStochConv P' EV.VE EV.j G' 0 t (Zb t) := fun t ht =>
    gfb4_isStochConv_congr P' EV.VE EV.j ht.1 (fun τ hτ => hGG τ ⟨hτ.1, hτ.2.trans ht.2⟩) (hZb t ht)
  have hG0m : ∀ τ ∈ Set.Icc (0 : ℝ) S.T, Measurable (G τ) := fun τ _ => measurable_of_isHM hG τ
  have hfdd := gfb4_fdd S M hMF N m K hm EV hEV P P' (gfb4_aug P' ℱ') X₀' hX₀' G' G hG' hGc hGz hG0m hGG hGind
    Zb hZb' hZbm Y₀ hY₀ hlaw Y hY
  have hmY := hY.meas
  have hmXb : ∀ t, Measurable (fun ω' => EV.VE t 0 (EV.j (X₀' ω')) + Zb t ω') := fun t =>
    (((EV.VE t 0).continuous.comp EV.j.continuous).measurable.comp hX₀').add (hZbm t)
  have hcXb : ∀ᵐ ω' ∂P', ContinuousOn (fun t => EV.VE t 0 (EV.j (X₀' ω')) + Zb t ω') (Set.Icc 0 S.T) := by
    filter_upwards [hZbc] with ω' hω'
    exact (continuousOn_VE_zero EV hEV.maxHyp.1 (X₀' ω')).add hω'
  have key := Q54c.toPath_law_eq (m := m) (T := S.T) hT0.le P P' Y
    (fun t ω' => EV.VE t 0 (EV.j (X₀' ω')) + Zb t ω') hmY hmXb hY.cont hcXb hfdd
  rw [key]
  congr 1
  funext ω'
  exact toPath_eq_windowPath m S.T _ ω'

example := (@gf_law_identification_proof : type_of% @HRS.GF.gf_law_identification)

end HRS.GF
