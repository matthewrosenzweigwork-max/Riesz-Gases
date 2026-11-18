import HRS.MS.Fp81S21IntervalRS
import HRS.MS.Fp81S21IntervalRS2
import HRS.MS.R2InterpAux15
import HRS.MS.R2InterpAux63

/-!
# HRS S2.1(iii), packet 17c: fixed-space BV adapter for interval Riemann--Stieltjes integrals

For `q < r`, a path `F` of bounded variation on `[q,r]` and a continuous operator-valued integrand `A` on `[q,r]`,
there is an interval Riemann--Stieltjes value `I` for the integrand `(τ,u,v) ↦ A τ (F v - F u)` on `[q,r]`
(`fp81s21_IsRSOn`), and every such value satisfies `|I| ≤ (sup_{τ∈[q,r]} ‖A τ‖) · TV(F; [q,r])`.
The proof shifts `[q,r]` to `[0,r-q]` and reuses `HRS.MS.R2Interp.s102_RS_exists` and `s102_rs_bound_mono`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R2Interp

/- Exact exported type:
   fp81s21_eVariationOn_shift {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) {q r : ℝ} (hqr : q ≤ r) :
     eVariationOn (fun t => F (q + t) - F q) (Icc 0 (r - q)) = eVariationOn F (Icc q r)
-/
theorem fp81s21_eVariationOn_shift {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) {q r : ℝ}
    (hqr : q ≤ r) :
    eVariationOn (fun t => F (q + t) - F q) (Icc 0 (r - q)) = eVariationOn F (Icc q r) := by
  have hqr' : q + (r - q) = r := by ring
  have hImg : (fun t : ℝ => q + t) '' Icc 0 (r - q) = Icc q r := by
    rw [Set.image_const_add_Icc, add_zero, hqr']
  have hmono : MonotoneOn (fun t : ℝ => q + t) (Icc 0 (r - q)) := by
    intro x _ y _ hxy
    show q + x ≤ q + y
    linarith
  have h1 : (fun t : ℝ => F (q + t) - F q) = (fun x : ℝ => F x - F q) ∘ (fun t : ℝ => q + t) := rfl
  rw [h1, eVariationOn.comp_eq_of_monotoneOn (fun x : ℝ => F x - F q) (fun t : ℝ => q + t) hmono, hImg]
  unfold eVariationOn
  simp only [edist_dist, dist_sub_right]

/- Exact exported type:
   fp81s21_bv_shift {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) {q r : ℝ} (hqr : q ≤ r)
     (hF : BoundedVariationOn F (Icc q r)) :
     BoundedVariationOn (fun t => F (q + t) - F q) (Icc 0 (r - q))
-/
theorem fp81s21_bv_shift {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) {q r : ℝ}
    (hqr : q ≤ r) (hF : BoundedVariationOn F (Icc q r)) :
    BoundedVariationOn (fun t => F (q + t) - F q) (Icc 0 (r - q)) := by
  unfold BoundedVariationOn
  rw [fp81s21_eVariationOn_shift F hqr]
  exact hF

/- Exact exported type:
   fp81s21_norm_le_var_incr {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) {q r x y : ℝ}
     (hF : BoundedVariationOn F (Icc q r)) (hqx : q ≤ x) (hxy : x ≤ y) (hyr : y ≤ r) :
     ‖F y - F x‖ ≤ (eVariationOn F (Icc q y)).toReal - (eVariationOn F (Icc q x)).toReal
-/
theorem fp81s21_norm_le_var_incr {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) {q r x y : ℝ}
    (hF : BoundedVariationOn F (Icc q r)) (hqx : q ≤ x) (hxy : x ≤ y) (hyr : y ≤ r) :
    ‖F y - F x‖ ≤ (eVariationOn F (Icc q y)).toReal - (eVariationOn F (Icc q x)).toReal := by
  have hF' : eVariationOn F (Icc q r) ≠ ⊤ := hF
  have hxr : x ≤ r := hxy.trans hyr
  have hadd : eVariationOn F (Icc q y) = eVariationOn F (Icc q x) + eVariationOn F (Icc x y) := by
    have h := eVariationOn.Icc_add_Icc F (s := univ) hqx hxy (Set.mem_univ x)
    simp only [Set.univ_inter] at h
    exact h.symm
  have hxfin : eVariationOn F (Icc q x) ≠ ⊤ :=
    ne_top_of_le_ne_top hF' (eVariationOn.mono F (Icc_subset_Icc le_rfl hxr))
  have hxyfin : eVariationOn F (Icc x y) ≠ ⊤ :=
    ne_top_of_le_ne_top hF' (eVariationOn.mono F (Icc_subset_Icc hqx hyr))
  have hedge : edist (F y) (F x) ≤ eVariationOn F (Icc x y) :=
    eVariationOn.edist_le F ⟨hxy, le_rfl⟩ ⟨le_rfl, hxy⟩
  have hnorm : ‖F y - F x‖ ≤ (eVariationOn F (Icc x y)).toReal := by
    have h1 : ‖F y - F x‖ = (edist (F y) (F x)).toReal := by
      rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg, dist_eq_norm]
    rw [h1]
    exact ENNReal.toReal_mono hxyfin hedge
  have hsplit : (eVariationOn F (Icc q y)).toReal
      = (eVariationOn F (Icc q x)).toReal + (eVariationOn F (Icc x y)).toReal := by
    rw [hadd, ENNReal.toReal_add hxfin hxyfin]
  rw [hsplit]
  linarith

/- Exact exported type:
   fp81s21_IsR2RS_congr {T I : ℝ} {S S2 : ℝ → ℝ → ℝ → ℝ}
     (h : ∀ τ a b, S τ a b = S2 τ a b) (hS : IsR2RS T S I) : IsR2RS T S2 I
-/
theorem fp81s21_IsR2RS_congr {T I : ℝ} {S S2 : ℝ → ℝ → ℝ → ℝ}
    (h : ∀ τ a b, S τ a b = S2 τ a b) (hS : IsR2RS T S I) : IsR2RS T S2 I := by
  have hfun : S = S2 := funext fun τ => funext fun a => funext fun b => h τ a b
  rw [← hfun]
  exact hS


/- Exact exported type:
   fp81s21_rsOn_bv_exists {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
     {q r : ℝ} (hqr : q < r) (F : ℝ → E) (A : ℝ → E →L[ℝ] ℝ)
     (hF : BoundedVariationOn F (Icc q r)) (hA : ContinuousOn A (Icc q r)) :
     ∃ I : ℝ, fp81s21_IsRSOn q r (fun τ u v => A τ (F v - F u)) I
-/
theorem fp81s21_rsOn_bv_exists {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {q r : ℝ} (hqr : q < r) (F : ℝ → E) (A : ℝ → E →L[ℝ] ℝ)
    (hF : BoundedVariationOn F (Icc q r)) (hA : ContinuousOn A (Icc q r)) :
    ∃ I : ℝ, fp81s21_IsRSOn q r (fun τ u v => A τ (F v - F u)) I := by
  have hF0 : (fun t : ℝ => F (q + t) - F q) 0 = 0 := by
    show F (q + 0) - F q = 0
    rw [add_zero, sub_self]
  have hmaps : MapsTo (fun t : ℝ => q + t) (Icc 0 (r - q)) (Icc q r) := by
    intro t ht
    show q + t ∈ Icc q r
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hf : ContinuousOn (fun t : ℝ => q + t) (Icc 0 (r - q)) :=
    (continuous_const.add continuous_id).continuousOn
  have hA' : ContinuousOn (fun t : ℝ => A (q + t)) (Icc 0 (r - q)) :=
    hA.comp hf hmaps
  have hF' : BoundedVariationOn (fun t : ℝ => F (q + t) - F q) (Icc 0 (r - q)) :=
    fp81s21_bv_shift F hqr.le hF
  obtain ⟨I, hI⟩ := s102_RS_exists (T := r - q) (by linarith) (fun t : ℝ => F (q + t) - F q) hF' hF0
    (fun t : ℝ => A (q + t)) hA'
  refine ⟨I, ?_⟩
  unfold fp81s21_IsRSOn
  refine fp81s21_IsR2RS_congr (S := fun τ a b : ℝ => A (q + τ) (F (q + b) - F q - (F (q + a) - F q))) ?_ hI
  intro τ a b
  show A (q + τ) (F (q + b) - F q - (F (q + a) - F q)) = A (q + τ) (F (q + b) - F (q + a))
  rw [sub_sub_sub_cancel_right]


/- Exact exported type:
   fp81s21_rsOn_bv_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
     {q r : ℝ} (hqr : q < r) (F : ℝ → E) (A : ℝ → E →L[ℝ] ℝ)
     (hF : BoundedVariationOn F (Icc q r)) (hA : ContinuousOn A (Icc q r))
     {I : ℝ} (hI : fp81s21_IsRSOn q r (fun τ u v => A τ (F v - F u)) I) :
     |I| ≤ (⨆ τ : Icc q r, ‖A τ‖) * (eVariationOn F (Icc q r)).toReal
-/
theorem fp81s21_rsOn_bv_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q r : ℝ} (hqr : q < r) (F : ℝ → E) (A : ℝ → E →L[ℝ] ℝ)
    (hF : BoundedVariationOn F (Icc q r)) (hA : ContinuousOn A (Icc q r))
    {I : ℝ} (hI : fp81s21_IsRSOn q r (fun τ u v => A τ (F v - F u)) I) :
    |I| ≤ (⨆ τ : Icc q r, ‖A τ‖) * (eVariationOn F (Icc q r)).toReal := by
  have hcompact : BddAbove ((fun τ => ‖A τ‖) '' Icc q r) :=
    isCompact_Icc.bddAbove_image (continuous_norm.comp_continuousOn hA)
  have hbdd : BddAbove (Set.range (fun τ : Icc q r => ‖A τ‖)) := by
    obtain ⟨C, hC⟩ := hcompact
    refine ⟨C, ?_⟩
    rintro _ ⟨τ, rfl⟩
    exact hC ⟨(τ : ℝ), τ.2, rfl⟩
  have hM : ∀ z ∈ Icc q r, ‖A z‖ ≤ ⨆ τ : Icc q r, ‖A τ‖ := fun z hz => le_ciSup hbdd ⟨z, hz⟩
  have hM0 : 0 ≤ ⨆ τ : Icc q r, ‖A τ‖ := (norm_nonneg _).trans (hM q ⟨le_rfl, hqr.le⟩)
  have hI' : HRS.Sec7.IsRS (r - q) (fun τ a b => A (q + τ) (F (q + b) - F (q + a))) I := by
    unfold fp81s21_IsRSOn at hI
    exact hI
  have hS : ∀ τ a b : ℝ, 0 ≤ a → a ≤ τ → τ ≤ b → b ≤ r - q →
      |A (q + τ) (F (q + b) - F (q + a))| ≤ (⨆ τ : Icc q r, ‖A τ‖) *
        ((eVariationOn F (Icc q (q + b))).toReal - (eVariationOn F (Icc q (q + a))).toReal) := by
    intro τ a b ha haτ hτb hbT
    have hz : q + τ ∈ Icc q r := ⟨by linarith, by linarith⟩
    have hAz : ‖A (q + τ)‖ ≤ ⨆ τ : Icc q r, ‖A τ‖ := hM (q + τ) hz
    have hw : ‖F (q + b) - F (q + a)‖ ≤
        (eVariationOn F (Icc q (q + b))).toReal - (eVariationOn F (Icc q (q + a))).toReal :=
      fp81s21_norm_le_var_incr F hF (by linarith) (by linarith) (by linarith)
    calc |A (q + τ) (F (q + b) - F (q + a))|
        = ‖A (q + τ) (F (q + b) - F (q + a))‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖A (q + τ)‖ * ‖F (q + b) - F (q + a)‖ := (A (q + τ)).le_opNorm _
      _ ≤ (⨆ τ : Icc q r, ‖A τ‖) * ‖F (q + b) - F (q + a)‖ :=
          mul_le_mul_of_nonneg_right hAz (norm_nonneg _)
      _ ≤ (⨆ τ : Icc q r, ‖A τ‖) *
            ((eVariationOn F (Icc q (q + b))).toReal - (eVariationOn F (Icc q (q + a))).toReal) :=
          mul_le_mul_of_nonneg_left hw hM0
  have hbound : |I| ≤ (⨆ τ : Icc q r, ‖A τ‖) *
      ((eVariationOn F (Icc q (q + (r - q)))).toReal - (eVariationOn F (Icc q (q + 0))).toReal) :=
    s102_rs_bound_mono (T := r - q) (by linarith)
      (fun t : ℝ => (eVariationOn F (Icc q (q + t))).toReal) hI' hS
  have hqr' : q + (r - q) = r := by ring
  have hv0 : (eVariationOn F (Icc q (q + 0))).toReal = 0 := by
    rw [add_zero, Set.Icc_self, eVariationOn.subsingleton F Set.subsingleton_singleton,
      ENNReal.toReal_zero]
  rw [hqr', hv0, sub_zero] at hbound
  exact hbound


/- Exact exported type:
   fp81s21_rsOn_bv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
     {q r : ℝ} (hqr : q < r) (F : ℝ → E) (A : ℝ → E →L[ℝ] ℝ)
     (hF : BoundedVariationOn F (Set.Icc q r)) (hA : ContinuousOn A (Set.Icc q r)) :
     ∃ I : ℝ, fp81s21_IsRSOn q r (fun τ u v => A τ (F v - F u)) I ∧
       |I| ≤ (⨆ τ : Set.Icc q r, ‖A τ‖) * (eVariationOn F (Set.Icc q r)).toReal
-/
theorem fp81s21_rsOn_bv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {q r : ℝ} (hqr : q < r) (F : ℝ → E) (A : ℝ → E →L[ℝ] ℝ)
    (hF : BoundedVariationOn F (Set.Icc q r)) (hA : ContinuousOn A (Set.Icc q r)) :
    ∃ I : ℝ, fp81s21_IsRSOn q r (fun τ u v => A τ (F v - F u)) I ∧
      |I| ≤ (⨆ τ : Set.Icc q r, ‖A τ‖) * (eVariationOn F (Set.Icc q r)).toReal := by
  obtain ⟨I, hI⟩ := fp81s21_rsOn_bv_exists hqr F A hF hA
  exact ⟨I, hI, fp81s21_rsOn_bv_bound hqr F A hF hA hI⟩

#print axioms fp81s21_eVariationOn_shift
#print axioms fp81s21_bv_shift
#print axioms fp81s21_norm_le_var_incr
#print axioms fp81s21_IsR2RS_congr
#print axioms fp81s21_rsOn_bv_exists
#print axioms fp81s21_rsOn_bv_bound
#print axioms fp81s21_rsOn_bv

end HRS.Fp81.S21

end
