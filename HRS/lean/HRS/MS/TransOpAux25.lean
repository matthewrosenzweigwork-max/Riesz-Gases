import HRS.MS.TransOpAux24

/-!
# S611 packet P5b: the tie `mov_translated_stationary_of_S21`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

theorem mov_translated_stationary_of_S21 (h21 : HRS.Whole.WholeSpaceStationaryStatement) :
    type_of% @HRS.Whole.mov_translated_stationary := by
  intro d s hd hs0 hsd β q hβ hq T hT b ρ₀ hρ
  obtain ⟨C₀, C, hc1, hmain⟩ := h21 hd s hs0 hsd q β hq hβ T hT
  have hm : 1 ≤ wholeSpaceIndex d := by unfold wholeSpaceIndex; omega
  have hdm : (d : ℝ) < ((wholeSpaceIndex d : ℕ) : ℝ) := by
    unfold wholeSpaceIndex; push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  set m := wholeSpaceIndex d with hmdef
  have hK1 : 1 ≤ s611_K m b := s611_one_le_K m b
  refine ⟨C₀, s611_K m b ^ 2 * C, hc1 ρ₀ hρ, ?_⟩
  intro N hN hInv Ω _ P _ X₀ W X hset hlaw Ω' _ P' _ Z hZ
  have hN1 : 1 ≤ N := by omega
  set Y₀ : Ω → EucConfig d N := fun ζ i => X₀ ζ i - b with hY₀
  set Y : ℝ≥0 → Ω → EucConfig d N := fun t ζ i => X t ζ i - movShift q b (t : ℝ) with hY
  have hXm : ∀ t, Measurable (X t) := fun t => (hset.sol T).adapted t
  have hsolY : IsWholeStrongSolution P (quadraticGradientDyn d s q β) T Y₀ W Y := by
    have := (HRS.Whole.mov_translation_proof hd hs0 hsd β q hβ hq (-b)).1 N T P X₀ W X (hset.sol T)
    have e1 : Y₀ = fun ζ i => X₀ ζ i + -b := by funext ζ i; simp [hY₀, sub_eq_add_neg]
    have e2 : Y = fun t ζ i => X t ζ i + movShift q (-b) (t : ℝ) := by
      funext t ζ i
      simp [hY, movShift, sub_eq_add_neg]
    rw [e1, e2]; exact this
  have hX₀m : AEMeasurable X₀ P :=
    (hXm 0).aemeasurable.congr (hset.sol T).init
  have hsh : Measurable (fun Z : EucConfig d N => fun i => Z i - b) := s611_measurable_unshift b
  have hind : ProbabilityTheory.IndepFun Y₀ (fun ζ t => W t ζ) P := hset.indep.comp hsh measurable_id
  have hlawY : HRS.law P Y₀ = HRS.Whole.canonicalGibbs (HRS.Whole.rieszKernel d s) (HRS.Whole.confinement q) N β := by
    have e : Y₀ = (fun Z : EucConfig d N => fun i => Z i - b) ∘ X₀ := rfl
    show P.map Y₀ = _
    rw [e, ← AEMeasurable.map_map_of_aemeasurable hsh.aemeasurable hX₀m, hlaw,
      Measure.map_map hsh (s611_measurable_shift b)]
    have : ((fun Z : EucConfig d N => fun i => Z i - b) ∘ fun (Y : EucConfig d N) i => Y i + b) = id := by
      funext Y i; simp
    rw [this, Measure.map_id]
  have hZ' := s611_gaussian_conj m hm s q β ρ₀ b β T (s611_uniq_of_thermal hd hs0 hsd hq hβ hρ T)
    (s611_hsus_of_thermal hd hs0 hsd hq hβ hρ hβ.le) P' Z (hZ T)
  obtain ⟨hm1, hm2, hsd2, hW⟩ := hmain ρ₀ hρ N hN hInv P Y₀ W Y hset.brownian hind hlawY hsolY P'
    (fun t ζ => s611_Lam m hm (-(movShift q b t)) (Z t ζ)) hZ'
  have hFX : ∀ ζ, zetaPathW (m : ℝ) T 0 P X ζ =
      s611_S m hm hq.le b (le_refl (0 : ℝ)) T (zetaPathW (m : ℝ) T 0 P Y ζ) := by
    intro ζ
    unfold zetaPathW
    refine s611_window_conj m hm (movShift q b) (s611_continuous_movShift q b) 0 T (s611_K m b) le_rfl
      (s611_K_pos m b).le _ _ _ ?_
    intro t ht
    exact s611_zeta_pointwise m hm hdm hN1 q b P X hXm ζ t ht
  have hFX' : ∀ ζ, processWindow (m : ℝ) T 0 Z ζ =
      s611_S m hm hq.le b (le_refl (0 : ℝ)) T (processWindow (m : ℝ) T 0
        (fun t ζ => s611_Lam m hm (-(movShift q b t)) (Z t ζ)) ζ) := by
    intro ζ
    unfold processWindow
    refine s611_window_conj m hm (movShift q b) (s611_continuous_movShift q b) 0 T (s611_K m b) le_rfl
      (s611_K_pos m b).le _ _ _ ?_
    intro t ht
    exact s611_Z_conj m hm q b t (Z t ζ)
  obtain ⟨r1, r2, r3, r4⟩ := s611_dist_transfer P P' (s611_S m hm hq.le b (le_refl (0 : ℝ)) T) hK1
    (s611_norm_S_le m hm hq.le b (le_refl (0 : ℝ)) T) _ _ _ _ hm1 hm2 hFX hFX' hsd2 hW
  refine ⟨r1, r2, ?_, ?_⟩
  · simpa [mul_assoc] using r3
  · simpa [mul_assoc] using r4

end HRS.MS.TransOp

end
