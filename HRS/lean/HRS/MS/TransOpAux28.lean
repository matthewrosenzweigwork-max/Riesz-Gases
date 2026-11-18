import HRS.MS.TransOpAux27

/-!
# S611 packet P5e: the tie `mov_translated_prepared_of_S21`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

theorem mov_translated_prepared_of_S21 (h21 : HRS.Whole.WholeSpacePreparedStatement) :
    type_of% @HRS.Whole.mov_translated_prepared := by
  intro d s hd hs0 hs β q hβ hq T hT b γ hγ ρ₀ hρ
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨εstar, hε, C₀, C, hc1, hmain⟩ := h21 hd s hs0 hs q β hq hβ γ hγ T hT 1 1
  obtain ⟨ψ, hψ⟩ := s611_exists_admissible hd hs0 hsd hq hβ hρ εstar hε
  have hres := s611_resulting_const hd hs0 hsd hq hβ hρ hε ψ
  have hprob : HRS.Whole.IsProbDensity ρ₀ := hρ.2.1
  have hm : 1 ≤ wholeSpaceIndex d := by unfold wholeSpaceIndex; omega
  have hdm : (d : ℝ) < ((wholeSpaceIndex d : ℕ) : ℝ) := by
    unfold wholeSpaceIndex; push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  set m := wholeSpaceIndex d with hmdef
  have hK1 : 1 ≤ s611_K m b := s611_one_le_K m b
  refine ⟨C₀, s611_K m b ^ 2 * C, ?_, ?_⟩
  · have hc : ∀ N : ℕ, 2 ≤ N → ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
        0 ≤ rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ₀) + oN d s C₀ N :=
      fun N hN X hX => (hc1 ρ₀ hρ 0 ψ hψ (fun _ => ρ₀) hres N hN 0 le_rfl X hX)
    intro N hN t _ X hX
    exact HRS.MS.MovSch.s64_completion_translated hprob b hc N hN t X hX
  intro N hN hCon Ω _ P _ X₀ W X hset hprep Ω' _ P' _ Z hZ a₀ ha₀
  have hN1 : 1 ≤ N := by omega
  set Y₀ : Ω → EucConfig d N := fun ζ i => X₀ ζ i - b with hY₀
  set Y : ℝ≥0 → Ω → EucConfig d N := fun t ζ i => X t ζ i - movShift q b (t : ℝ) with hY
  have hXm : ∀ t, Measurable (X t) := fun t => (hset.sol 0).adapted t
  have hsolY : ∀ T' : ℝ, IsWholeStrongSolution P (quadraticGradientDyn d s q β) T' Y₀ W Y := by
    intro T'
    have := (HRS.Whole.mov_translation_proof hd hs0 hsd β q hβ hq (-b)).1 N T' P X₀ W X (hset.sol T')
    have e1 : Y₀ = fun ζ i => X₀ ζ i + -b := by funext ζ i; simp [hY₀, sub_eq_add_neg]
    have e2 : Y = fun t ζ i => X t ζ i + movShift q (-b) (t : ℝ) := by
      funext t ζ i
      simp [hY, movShift, sub_eq_add_neg]
    rw [e1, e2]; exact this
  have hX₀m : AEMeasurable X₀ P :=
    (hXm 0).aemeasurable.congr (hset.sol 0).init
  have hsh : Measurable (fun Z : EucConfig d N => fun i => Z i - b) := s611_measurable_unshift b
  have hind : ProbabilityTheory.IndepFun Y₀ (fun ζ t => W t ζ) P := hset.indep.comp hsh measurable_id
  have hlawY : HRS.law P Y₀ = HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N γ (HRS.Whole.withDensityReal ((fun _ => ρ₀) 0)) :=
    s611_prep_law hd hs0 hsd hβ hq b hγ hprob P X₀ hX₀m hprep
  have hZ' : ∀ T' : ℝ, IsLinearGaussianEvolutionW P'
      ((quadraticGradientDyn d s q β).coeff (fun _ => ρ₀)) (m : ℝ) β⁻¹ T'
      (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ((fun _ => ρ₀) 0)) γ)
      (fun t ζ => s611_Lam m hm (-(movShift q b t)) (Z t ζ)) := fun T' =>
    s611_gaussian_conj m hm s q β ρ₀ b γ T' (s611_uniq_of_thermal hd hs0 hsd hq hβ hρ T')
      (s611_hsus_of_thermal hd hs0 hsd hq hβ hρ hγ) P' Z (hZ T')
  obtain ⟨hm1, hm2, hsd2, hW⟩ := hmain ρ₀ hρ 0 ψ hψ (fun _ => ρ₀) hres N hN hCon P Y₀ W Y hset.brownian
    hind hlawY hsolY P' (fun t ζ => s611_Lam m hm (-(movShift q b t)) (Z t ζ)) hZ' a₀ ha₀
  have hFX : ∀ ζ, flucPathW (m : ℝ) T a₀ (Real.sqrt N) X (movTranslatedDensity q b ρ₀) ζ =
      s611_S m hm hq.le b ha₀ T (flucPathW (m : ℝ) T a₀ (Real.sqrt N) Y (fun _ => ρ₀) ζ) := by
    intro ζ
    unfold flucPathW
    refine s611_window_conj m hm (movShift q b) (s611_continuous_movShift q b) a₀ T (s611_K m b) ha₀
      (s611_K_pos m b).le _ _ _ ?_
    intro t ht
    exact s611_fluc_pointwise m hm hdm hN1 q b X ρ₀ hprob ζ t ht _
  have hFX' : ∀ ζ, processWindow (m : ℝ) T a₀ Z ζ =
      s611_S m hm hq.le b ha₀ T (processWindow (m : ℝ) T a₀
        (fun t ζ => s611_Lam m hm (-(movShift q b t)) (Z t ζ)) ζ) := by
    intro ζ
    unfold processWindow
    refine s611_window_conj m hm (movShift q b) (s611_continuous_movShift q b) a₀ T (s611_K m b) ha₀
      (s611_K_pos m b).le _ _ _ ?_
    intro t ht
    exact s611_Z_conj m hm q b t (Z t ζ)
  obtain ⟨r1, r2, r3, r4⟩ := s611_dist_transfer P P' (s611_S m hm hq.le b ha₀ T) hK1
    (s611_norm_S_le m hm hq.le b ha₀ T) _ _ _ _ hm1 hm2 hFX hFX' hsd2 hW
  refine ⟨r1, r2, ?_, ?_⟩
  · simpa [mul_assoc] using r3
  · simpa [mul_assoc] using r4

end HRS.MS.TransOp

end
