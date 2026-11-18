import HRS.Sections.ScrnAux21
import HRS.PDE.MovFFinal
import HRS.Appendix.B15Final
import HRS.Stochastic.Particle

/-!
# Packet SCRN, part 22: the energy bound `E[F_N(X^t)] ≤ 0` for the Haar-started free dynamics

For `V = 0`, `ρ ≡ 1`: `U_N = N F_N(·, dx)` pointwise (the kernel has mean zero), `gibbsRef D N` is the
modulated Gibbs measure `Q_{N,β}(dx)`, and the B.15 entropy inequality
`𝓗_G(P^t) ≤ 𝓗_G(P^0)` together with the relative-entropy splitting `movT_relEntropy_split_proof` gives
`H(P^t | dx) + β N E[F_N(X^t)] ≤ β N E[F_N(X^0)] = 0` (`expectation_modulatedEnergy_iid` and `∬ g = 0`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

section Energy

variable {s : ℝ}

lemma scrn_isProbDensity_one : IsProbDensity (fun _ : Torus d => (1 : ℝ)) :=
  ⟨fun _ => zero_le_one, measurable_const, by simp⟩

lemma scrn_rowOK (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    RowOK (volume : Measure (Torus d)) (fun x y => periodicRiesz d s (x - y)) := by
  have hgm : Measurable (periodicRiesz d s) := CoercAux.measurable_periodicRiesz_one hd hs0 hsd
  have hgi : Integrable (periodicRiesz d s) := CoercAux.integrable_periodicRiesz_one hd hs0 hsd
  have hkm : Measurable (Function.uncurry fun x y : Torus d => periodicRiesz d s (x - y)) := by
    show Measurable (fun p : Torus d × Torus d => periodicRiesz d s (p.1 - p.2))
    exact hgm.comp (measurable_fst.sub measurable_snd)
  have := (rowOK_of_dom (ρ := fun _ : Torus d => (1 : ℝ)) (Λ₀ := 1) zero_le_one (fun _ => le_rfl)
    hgi.abs hkm (fun x y => le_rfl)).1
  rwa [scrn_withDensityReal_one] at this

lemma scrn_int_g_sub (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (x : Torus d) :
    ∫ y, periodicRiesz d s (x - y) = 0 := by
  rw [integral_sub_left_eq_self (fun z => periodicRiesz d s z) (volume : Measure (Torus d)) x]
  exact (CoercAux.integral_periodicRiesz_one hd hs0 hsd).2

lemma scrn_energy_eq (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (X : Config d N) :
    rieszEnergy d s X (volume : Measure (Torus d)) =
      (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, periodicRiesz d s (X i - X j) := by
  unfold rieszEnergy modulatedEnergyKernel modulatedEnergy
  simp only [scrn_int_g_sub hd hs0 hsd, Finset.sum_const_zero, mul_zero, sub_zero, integral_zero,
    add_zero]

lemma scrn_haar_energy (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hN : 1 ≤ N) :
    Integrable (fun X : Config d N => rieszEnergy d s X (volume : Measure (Torus d)))
        (Measure.pi fun _ : Fin N => (volume : Measure (Torus d))) ∧
      ∫ X : Config d N, rieszEnergy d s X (volume : Measure (Torus d))
        ∂(Measure.pi fun _ : Fin N => (volume : Measure (Torus d))) = 0 := by
  have hk := scrn_rowOK (d := d) (s := s) hd hs0 hsd
  have hI : Integrable (fun X : Config d N => modulatedEnergy (fun x y => periodicRiesz d s (x - y)) X
      (volume : Measure (Torus d))) (Measure.pi fun _ : Fin N => (volume : Measure (Torus d))) :=
    integrable_modulatedEnergy_pair hk
  refine ⟨hI, ?_⟩
  have h := expectation_modulatedEnergy_iid (periodicRiesz d s) (volume : Measure (Torus d)) hN
    hk.integrable_prod hk.int
  unfold rieszEnergy
  have hint : Integrable (fun p : Torus d × Torus d => periodicRiesz d s (p.1 - p.2))
      ((volume : Measure (Torus d)).prod (volume : Measure (Torus d))) := hk.integrable_prod
  rw [h, integral_prod _ hint]
  simp only [scrn_int_g_sub hd hs0 hsd, integral_zero, mul_zero]

lemma scrn_totalPotential_eq (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (hN : 1 ≤ N) (X : Config d N) :
    totalPotential (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) X =
      N * rieszEnergy d s X (volume : Measure (Torus d)) := by
  rw [scrn_energy_eq hd hs0 hsd]
  unfold totalPotential
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have e1 : (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ).s = s := rfl
  have e2 : ∀ x, (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ).V x = 0 := fun _ => rfl
  simp only [e1, e2, Finset.sum_const_zero, add_zero]
  field_simp

lemma scrn_gibbsRef_eq (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (hN : 1 ≤ N) :
    gibbsRef (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) N =
      modulatedGibbs (periodicRiesz d s) N β (volume : Measure (Torus d)) := by
  set D := PDE.mfData d s hs0 hsd (fun _ => 0) β hβ with hD
  have hDi : D.invβ⁻¹ = β := by simp [hD, PDE.mfData]
  rw [b15c_gibbsRef_eq_gen]
  unfold b15c_gibbsRefGen modulatedGibbs gibbsNormalizer b15c_gibbsPartitionGen b15c_gibbsWeightGen
  have hρ := (scrn_isProbDensity_one (d := d))
  obtain ⟨hFm, C, hC⟩ := movf_energy_facts hd hs0 hsd hρ continuous_const (by omega : 0 < N) (N := N)
  rw [scrn_withDensityReal_one] at hFm hC
  have hvol : (volume : Measure (Config d N)) = Measure.pi fun _ : Fin N => (volume : Measure (Torus d)) :=
    volume_pi
  have hU : ∀ X : Config d N, -(D.invβ⁻¹) * totalPotential D X = -β * N * rieszEnergy d s X volume := by
    intro X
    rw [scrn_totalPotential_eq hd hs0 hsd β hβ hN, hDi]; ring
  simp only [hU]
  rw [hvol]
  have hint : Integrable (fun X : Config d N => Real.exp (-β * N * rieszEnergy d s X volume))
      (Measure.pi fun _ : Fin N => (volume : Measure (Torus d))) := by
    refine Integrable.of_bound (C := Real.exp (β * N * C)) ?_ ?_
    · have hFm' : Measurable (fun X : Config d N => rieszEnergy d s X (volume : Measure (Torus d))) := hFm
      exact (Real.measurable_exp.comp (measurable_const.mul hFm')).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun X => ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.2 ?_
      have h1 : -C ≤ rieszEnergy d s X (volume : Measure (Torus d)) := hC X
      have h0 : 0 ≤ β * N := by positivity
      nlinarith
  have hZ : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N * rieszEnergy d s X volume))
      ∂(Measure.pi fun _ : Fin N => (volume : Measure (Torus d))) =
      ENNReal.ofReal (∫ X : Config d N, Real.exp (-β * N * rieszEnergy d s X volume)
        ∂(Measure.pi fun _ : Fin N => (volume : Measure (Torus d)))) :=
    (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)).symm
  rw [hZ]
  rfl

/-- Transfer `a - L ≤ b - L` (in `EReal`) to `a ≤ b` (in `ℝ≥0∞`). -/
lemma scrn_ereal_cancel {a b : ℝ≥0∞} {L : ℝ}
    (h : ((a : ℝ≥0∞) : EReal) - (L : EReal) ≤ ((b : ℝ≥0∞) : EReal) - (L : EReal)) : a ≤ b := by
  have h2 := add_le_add_left h (L : EReal)
  rw [EReal.sub_add_cancel, EReal.sub_add_cancel] at h2
  exact EReal.coe_ennreal_le_coe_ennreal_iff.1 h2

/-- The energy bound: `E[F_N(X^t)] ≤ 0` (and integrability) for the Haar-started free dynamics. -/
theorem scrn_energy_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → Config d N) (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t : ℝ≥0 => W t ω) P)
    (hlaw : P.map X₀ = Measure.pi (fun _ : Fin N => (volume : Measure (Torus d))))
    (hsol : ∀ T' : ℝ, 0 ≤ T' → IsStrongSolution P (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) T' X₀ W X)
    (hfil : ∃ (ℱ : MeasureTheory.Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
      IsFilteredSolution P ℱ W' W X) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun ω => rieszEnergy d s (X t.toNNReal ω) (volume : Measure (Torus d))) P ∧
      ∫ ω, rieszEnergy d s (X t.toNNReal ω) (volume : Measure (Torus d)) ∂P ≤ 0 := by
  have hd1 : 1 ≤ d := by omega
  have hN1 : 1 ≤ N := by omega
  haveI : NeZero N := ⟨by omega⟩
  set D := PDE.mfData d s hs0 hsd (fun _ => 0) β hβ with hD
  have hDi : D.invβ = β⁻¹ := rfl
  have hDs : D.s = s := rfl
  have hDM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ) := rfl
  have hinvpos : 0 < D.invβ := by rw [hDi]; exact inv_pos.2 hβ
  have hDV : Torus.IsCk 2 D.V := by
    show Torus.IsCk 2 (fun _ : Torus d => (0 : ℝ))
    unfold Torus.IsCk Torus.lift; exact contDiff_const
  have hρ := (scrn_isProbDensity_one (d := d))
  have hρc : Torus.IsCk 2 (fun _ : Torus d => (1 : ℝ)) := by
    unfold Torus.IsCk Torus.lift; exact contDiff_const
  have hρpos : ∀ x : Torus d, 0 < (fun _ : Torus d => (1 : ℝ)) x := fun _ => one_pos
  -- the Haar-started process, restarted at `X 0`
  set X₀' : Ω → Config d N := X 0 with hX₀'
  have hXm : ∀ r : ℝ≥0, Measurable (X r) := fun r => (hsol 0 le_rfl).adapted r
  have hae : X₀' =ᵐ[P] X₀ := (hsol 0 le_rfl).init
  have hsol' : ∀ T' : ℝ, 0 ≤ T' → IsStrongSolution P D T' X₀' W X := fun T' hT' =>
    { (hsol T' hT') with init := Filter.Eventually.of_forall fun _ => rfl }
  have hlaw' : P.map X₀' = Measure.pi (fun _ : Fin N => (volume : Measure (Torus d))) := by
    rw [← hlaw]; exact Measure.map_congr hae
  have hind' : IndepFun X₀' (fun ω => fun t : ℝ≥0 => W t ω) P := hind.congr hae.symm
    (Filter.EventuallyEq.refl _ _)
  have hvol : (volume : Measure (Config d N)) = Measure.pi fun _ : Fin N => (volume : Measure (Torus d)) :=
    volume_pi
  -- the time horizon
  set T : ℝ := t + 1 with hT
  have hT0 : 0 < T := by rw [hT]; linarith
  have hdist : ∀ᵐ ω ∂P, X₀' ω ∉ collisionSet d N := by
    filter_upwards [(hsol' T hT0.le).no_collision] with ω hω
    exact hω 0 (by simp [hT0.le])
  have hsymn : Torus.SymNonpos (-1 : Matrix (Fin d) (Fin d) ℝ) := by
    unfold Torus.SymNonpos Torus.symPart
    have : (1 / 2 : ℝ) • ((-1 : Matrix (Fin d) (Fin d) ℝ) +
        (-1 : Matrix (Fin d) (Fin d) ℝ).transpose) = -1 := by
      rw [Matrix.transpose_neg, Matrix.transpose_one,
        ← two_smul ℝ (-1 : Matrix (Fin d) (Fin d) ℝ), smul_smul]
      norm_num
    rw [this, neg_neg]
    exact Matrix.PosSemidef.one
  obtain ⟨-, hU⟩ := particle_wellposed_proof P D hd hN hsymn hDV X₀' (hXm 0) hdist W hW hind' T hT0
  obtain ⟨ℱ, W', hF⟩ := hfil
  -- finiteness and the Haar energy
  have hpi : IsProbabilityMeasure (Measure.pi fun _ : Fin N => (volume : Measure (Torus d))) :=
    inferInstance
  obtain ⟨hIntH, hEH⟩ := scrn_haar_energy (d := d) (s := s) hd1 hs0 hsd hN1 (N := N)
  have hmfe0 : MFEFinite d D.s (Measure.pi fun _ : Fin N => (volume : Measure (Torus d)))
      (withDensityReal (fun _ : Torus d => (1 : ℝ))) := by
    refine ⟨?_, ?_⟩
    · rw [scrn_withDensityReal_one]
      unfold relEntropy
      rw [klDiv_self]; exact ENNReal.zero_ne_top
    · rw [scrn_withDensityReal_one]; exact hIntH
  have hsplit0 := movT_relEntropy_split_proof hN hinvpos hρ hρc hρpos
    (ν := Measure.pi fun _ : Fin N => (volume : Measure (Torus d)))
  have hβeq : D.invβ⁻¹ = β := by rw [hDi, inv_inv]
  have hQ : modulatedGibbs (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (fun _ : Torus d => (1 : ℝ))) =
      modulatedGibbs (periodicRiesz d s) N β (volume : Measure (Torus d)) := by
    rw [hβeq, hDs, scrn_withDensityReal_one]
  have hgR : gibbsRef D N = modulatedGibbs (periodicRiesz d s) N β (volume : Measure (Torus d)) :=
    scrn_gibbsRef_eq hd1 hs0 hsd β hβ hN1
  have hrel0 : relEntropy (Measure.pi fun _ : Fin N => (volume : Measure (Torus d)))
      (modulatedGibbs (periodicRiesz d s) N β (volume : Measure (Torus d))) ≠ ⊤ := by
    rw [← hQ]; exact hsplit0.1.2 hmfe0
  have hsel0 : selectedLaw P X 0 = Measure.pi fun _ : Fin N => (volume : Measure (Torus d)) := by
    unfold selectedLaw
    rw [Real.toNNReal_zero]
    exact hlaw'
  have hdens0 : HasSelectedDensity P X 0 := by
    unfold HasSelectedDensity
    rw [hsel0, ← hvol]
  have hH0 : gibbsEntropy D (selectedLaw P X 0) < ⊤ := by
    unfold gibbsEntropy
    rw [hgR, hsel0, sub_eq_add_neg, ← EReal.coe_neg]
    have h1 : ((relEntropy (Measure.pi fun _ : Fin N => (volume : Measure (Torus d)))
        (modulatedGibbs (periodicRiesz d s) N β (volume : Measure (Torus d))) : ℝ≥0∞) : EReal) ≠ ⊤ := by
      simpa using hrel0
    exact lt_top_iff_ne_top.2 (EReal.add_ne_top h1 (EReal.coe_ne_top _))
  have hmain := (b15_sde_entropy_law_free_proof (D := D) hN hDM hinvpos hDV hT0 (hXm 0) hdist hW hind'
    (hsol' T hT0.le) hU hF hdens0 hH0).1
  have htT : t ∈ Set.Icc 0 T := ⟨ht, by rw [hT]; linarith⟩
  -- the entropy inequality for the relative entropy to the Gibbs reference
  have hle : relEntropy (selectedLaw P X t) (modulatedGibbs (periodicRiesz d s) N β (volume : Measure (Torus d))) ≤
      relEntropy (Measure.pi fun _ : Fin N => (volume : Measure (Torus d)))
        (modulatedGibbs (periodicRiesz d s) N β (volume : Measure (Torus d))) := by
    have h := (hmain t htT).2
    unfold gibbsEntropy at h
    rw [hgR, hsel0] at h
    have h' := le_trans (le_add_of_nonneg_right (EReal.coe_ennreal_nonneg _)) h
    exact scrn_ereal_cancel h'
  have hprobt : IsProbabilityMeasure (selectedLaw P X t) := by
    unfold selectedLaw
    exact (Measure.isProbabilityMeasure_map_iff (hXm _).aemeasurable).2 inferInstance
  have hnet : relEntropy (selectedLaw P X t) (modulatedGibbs (periodicRiesz d D.s) N D.invβ⁻¹
      (withDensityReal (fun _ : Torus d => (1 : ℝ)))) ≠ ⊤ := by
    rw [hQ]; exact ne_top_of_le_ne_top hrel0 hle
  have hsplit := movT_relEntropy_split_proof hN hinvpos hρ hρc hρpos (ν := selectedLaw P X t)
  have hmfe := hsplit.1.1 hnet
  have hfin0 := hsplit.2 hmfe
  have hfin00 := (movT_relEntropy_split_proof hN hinvpos hρ hρc hρpos
    (ν := Measure.pi fun _ : Fin N => (volume : Measure (Torus d)))).2 hmfe0
  simp only [hDs, hβeq, scrn_withDensityReal_one] at hmfe hfin0 hfin00 hnet
  have hz : (relEntropy (Measure.pi fun _ : Fin N => (volume : Measure (Torus d)))
      (Measure.pi fun _ : Fin N => (volume : Measure (Torus d)))) = 0 := by
    unfold relEntropy; exact klDiv_self _
  rw [hz, ENNReal.toReal_zero, hEH, mul_zero, zero_add] at hfin00
  have hmono := ENNReal.toReal_mono hrel0 hle
  have hHt : 0 ≤ (relEntropy (selectedLaw P X t) (Measure.pi fun _ : Fin N => (volume : Measure (Torus d)))).toReal :=
    ENNReal.toReal_nonneg
  have hβN : 0 < β * N := by positivity
  have hEt : ∫ X : Config d N, rieszEnergy d s X (volume : Measure (Torus d)) ∂(selectedLaw P X t) ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    have := mul_pos hβN hpos
    nlinarith [hfin0, hfin00, hmono]
  -- transfer to `P`
  have hFm : Measurable (fun X : Config d N => rieszEnergy d s X (volume : Measure (Torus d))) := by
    obtain ⟨hm, -⟩ := movf_energy_facts hd1 hs0 hsd hρ continuous_const (by omega : 0 < N) (N := N)
    rw [scrn_withDensityReal_one] at hm
    exact hm
  have hXt : Measurable (X t.toNNReal) := hXm _
  have hint : Integrable (fun X : Config d N => rieszEnergy d s X (volume : Measure (Torus d)))
      (selectedLaw P X t) := hmfe.2
  refine ⟨?_, ?_⟩
  · exact (integrable_map_measure hFm.aestronglyMeasurable hXt.aemeasurable).1 hint
  · have e : ∫ X : Config d N, rieszEnergy d s X (volume : Measure (Torus d)) ∂(selectedLaw P X t) =
        ∫ ω, rieszEnergy d s (X t.toNNReal ω) (volume : Measure (Torus d)) ∂P := by
      unfold selectedLaw
      exact integral_map hXt.aemeasurable hFm.aestronglyMeasurable
    rw [← e]; exact hEt

end Energy

end HRS
