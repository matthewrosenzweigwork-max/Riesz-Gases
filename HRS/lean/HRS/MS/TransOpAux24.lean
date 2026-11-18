import HRS.MS.TransOpAux23
import HRS.MS.SuppA0

/-!
# S611 packet P5a: `mov_translated_stationary` from S2.1 (i)

`mov_translated_stationary_of_S21 : type_of% @whole_space_stationary → type_of% @mov_translated_stationary`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s611_K_movShift_le (m : ℕ) {q : ℝ} (hq : 0 ≤ q) (b : Euc d) {r : ℝ} (hr : 0 ≤ r) :
    s611_K m (movShift q b r) ≤ s611_K m b := by
  unfold s611_K
  refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by positivity))
  have h1 : Real.exp (-q * r) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  show |(Real.exp (-q * r) • b) j| ≤ |b j|
  have : (Real.exp (-q * r) • b) j = Real.exp (-q * r) * b j := rfl
  rw [this, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (abs_nonneg _) h1

/-- The path operator of the shift `movShift q b` on the window starting at `a ≥ 0`. -/
def s611_S (m : ℕ) (hm : 1 ≤ m) {q : ℝ} (hq : 0 ≤ q) (b : Euc d) {a : ℝ} (ha : 0 ≤ a) (T : ℝ) :
    OscPath d (m : ℝ) T →L[ℝ] OscPath d (m : ℝ) T :=
  s611_pathOp m hm (movShift q b) (s611_continuous_movShift q b) a T (s611_K m b)
    (s611_K_pos m b).le (fun t ht => s611_K_movShift_le m hq b (add_nonneg ha ht.1))

theorem s611_norm_S_le (m : ℕ) (hm : 1 ≤ m) {q : ℝ} (hq : 0 ≤ q) (b : Euc d) {a : ℝ} (ha : 0 ≤ a)
    (T : ℝ) : ‖s611_S m hm hq b ha T‖ ≤ s611_K m b := by
  unfold s611_S s611_pathOp
  exact LinearMap.mkContinuous_norm_le _ (s611_K_pos m b).le _

theorem s611_Z_conj (m : ℕ) (hm : 1 ≤ m) (q : ℝ) (b : Euc d) (t : ℝ) (u : OscDual d (m : ℝ)) :
    u = s611_Lam m hm (movShift q b t) (s611_Lam m hm (-(movShift q b t)) u) := by
  have := s611_Lam_neg m hm (-(movShift q b t)) u
  rw [neg_neg] at this
  exact this.symm

theorem s611_measurable_unshift {N : ℕ} (c : Euc d) :
    Measurable (fun Z : EucConfig d N => fun i => Z i - c) :=
  by fun_prop

/-- The exact field transformation for the exactly centered window, pointwise in `t ≥ 0`. -/
theorem s611_zeta_pointwise (m : ℕ) (hm : 1 ≤ m) (hdm : (d : ℝ) < m) {N : ℕ} (hN : 1 ≤ N) (q : ℝ)
    (b : Euc d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → EucConfig d N) (hXm : ∀ t, Measurable (X t)) (ζ : Ω) (t : ℝ) (ht : 0 ≤ t) :
    HRS.Whole.zetaB (m : ℝ) (P.map (X t.toNNReal)) (X t.toNNReal ζ) =
      s611_Lam m hm (movShift q b t)
        (HRS.Whole.zetaB (m : ℝ) (P.map (fun ζ' i => X t.toNNReal ζ' i - movShift q b (t.toNNReal : ℝ)))
          (fun i => X t.toNNReal ζ i - movShift q b (t.toNNReal : ℝ))) := by
  have ht' : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht
  set c := movShift q b t with hc
  rw [ht']
  set Ym : Ω → EucConfig d N := fun ζ' i => X t.toNNReal ζ' i - c with hYm
  have hYmeas : Measurable Ym := (s611_measurable_unshift c).comp (hXm _)
  haveI : IsProbabilityMeasure (P.map Ym) := inferInstance
  have e1 : X t.toNNReal = (fun Z : EucConfig d N => fun i => Z i + c) ∘ Ym := by
    funext ζ' i; simp [hYm]
  have e2 : P.map (X t.toNNReal) = (P.map Ym).map (fun Z : EucConfig d N => fun i => Z i + c) := by
    rw [Measure.map_map (s611_measurable_shift c) hYmeas, ← e1]
  have e3 : X t.toNNReal ζ = fun i => Ym ζ i + c := by
    funext i; simp [hYm]
  rw [e2]
  conv_lhs => rw [e3]
  exact s611_zeta_shift m hm hdm hN (P.map Ym) (Ym ζ) c

end HRS.MS.TransOp

end
