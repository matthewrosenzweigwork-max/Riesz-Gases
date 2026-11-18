import HRS.Uniform.Q45Fin3

/-!
# Q45: finite-dimensional comparison for block sums of two Hilbert martingales
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

lemma zeta_eq_blockProc {m q : ℕ} {T : ℝ} (hT : 0 < T) {Nb : ℕ} (α : Fin m → ℕ → H)
    (fH : Fin q → H) (A : ℕ → Matrix (Fin m) (Fin q) ℝ)
    (hspan : ∀ k < Nb, ∀ j v, ∑ c, A k j c * inner ℝ (fH c) v = inner ℝ (α j k) v)
    (M : ℝ → Ω → H) (ω : Ω) :
    blockProc A Nb T (fun τ ω => hmCoordCLM fH (M τ ω)) T ω = zeta α T Nb M ω := by
  ext j
  rw [blockProc_apply]
  simp only [zeta]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  have h1 : min T (rr Nb T (k + 1)) = rr Nb T (k + 1) :=
    min_eq_right (unifPart_le hT.le (Nat.succ_le_of_lt hk'))
  have h0 : min T (rr Nb T k) = rr Nb T k := min_eq_right (unifPart_le hT.le hk'.le)
  rw [h1, h0, ← hspan k hk' j (M (rr Nb T (k + 1)) ω - M (rr Nb T k) ω)]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [hmCoordCLM_apply, inner_sub_right]

/-- The gauge `u ↦ ‖L u‖`. -/
def rhoL {m : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (L : (ℝ^m) →L[ℝ] W)
    (u : Fin m → ℝ) : ℝ := ‖L (WithLp.toLp 2 u)‖

lemma rhoL_nonneg {m : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (L : (ℝ^m) →L[ℝ] W)
    (u : Fin m → ℝ) : 0 ≤ rhoL L u := norm_nonneg _

lemma rhoL_le {m : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {L : (ℝ^m) →L[ℝ] W}
    (hL : ‖L‖ ≤ 1) (u : Fin m → ℝ) : rhoL L u ≤ 1 * Real.sqrt (u ⬝ᵥ u) := by
  have h1 : ‖(WithLp.toLp 2 u : ℝ^m)‖ = Real.sqrt (u ⬝ᵥ u) := by
    rw [EuclideanSpace.norm_eq]
    simp [dotProduct, sq]
  unfold rhoL
  calc ‖L (WithLp.toLp 2 u)‖ ≤ ‖L‖ * ‖(WithLp.toLp 2 u : ℝ^m)‖ := L.le_opNorm _
    _ ≤ 1 * Real.sqrt (u ⬝ᵥ u) := by
        rw [h1]; exact mul_le_mul_of_nonneg_right hL (Real.sqrt_nonneg _)

lemma hpair_L {m : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {L : (ℝ^m) →L[ℝ] W}
    (hL : ‖L‖ ≤ 1) {Φ : W → ℝ} (hΦ : Φ ∈ CbUnitBall W 2) (x : ℝ^m) (Q' : Matrix (Fin m) (Fin m) ℝ) :
    |hessPair (Φ ∘ L) x Q'| ≤ 1 * nuRho (rhoL L) Q' := by
  obtain ⟨hc, -, -, hH2⟩ := cbUnit_bounds hΦ
  set Hm : Matrix (Fin m) (Fin m) ℝ := fun i j =>
    iteratedFDeriv ℝ 2 (Φ ∘ L) x ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] with hHm
  have hmem : Hm ∈ admForms (rhoL L) := by
    intro u v
    have e : u ⬝ᵥ (Hm.mulVec v) = iteratedFDeriv ℝ 2 (Φ ∘ L) x ![WithLp.toLp 2 u, WithLp.toLp 2 v] := by
      rw [cmm_expand (iteratedFDeriv ℝ 2 (Φ ∘ L) x) (WithLp.toLp 2 u) (WithLp.toLp 2 v)]
      simp only [dotProduct, Matrix.mulVec, hHm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [e, L.iteratedFDeriv_comp_right hc x (le_refl _)]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have h1 := (iteratedFDeriv ℝ 2 Φ (L x)).le_opNorm (fun i => L (![WithLp.toLp 2 u, WithLp.toLp 2 v] i))
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h1
    rw [Real.norm_eq_abs] at h1
    refine h1.trans ?_
    calc ‖iteratedFDeriv ℝ 2 Φ (L x)‖ * (‖L (WithLp.toLp 2 u)‖ * ‖L (WithLp.toLp 2 v)‖)
        ≤ 1 * (‖L (WithLp.toLp 2 u)‖ * ‖L (WithLp.toLp 2 v)‖) :=
          mul_le_mul_of_nonneg_right (hH2 _) (by positivity)
      _ = rhoL L u * rhoL L v := by unfold rhoL; ring
  have := nu_pair_le (⟨Hm, hmem⟩ : admForms (rhoL L)) (rhoL_nonneg L) (rhoL_le hL) zero_le_one Q'
  simpa [hessPair, hHm] using this

end HRS.Uniform.Q45
