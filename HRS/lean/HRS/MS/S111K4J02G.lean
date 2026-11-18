import HRS.MS.S111K4J02F

/-!
# S11.1 / J02, piece G (S111K4): congruence lemmas for the per-`ω` coordinate identities

A.e. changes of the forcing do not change the coordinate integrals (`ShiftedJValue`, the drift coordinate integral).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole HRS.MS.S111K2

theorem k4j_ShiftedJValue_congr {d : ℕ} {C : WholeCoeff d} {m T u a b : ℝ}
    {z z' : ℝ → (Euc d → ℝ) → ℝ} (ha : 0 ≤ a) (hb : b ≤ u + T)
    (h : ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) (u + T))), z r = z' r)
    {J : projTensor (OscPath d m T) 2} (hJ : ShiftedJValue C m T u z a b J) :
    ShiftedJValue C m T u z' a b J := by
  intro ta tb phi psi l1 l2 h1 h2 hl1 hl2
  rw [hJ ta tb phi psi l1 l2 h1 h2 hl1 hl2]
  congr 1
  refine setIntegral_congr_ae (measurableSet_Ioc.inter measurableSet_Icc) ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 h] with r hr hrS
  rw [hr ⟨ha.trans hrS.1.1.le, hrS.1.2.trans hb⟩]

theorem k4j_drift_coord_congr {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) {C : WholeCoeff d} {T u : ℝ}
    {Q : TimeCoeff (u + T)} {s : ℝ → Coeff} (hs : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) (u + T))),
      (Q : ℝ → Coeff) x = s x) {v : ℝ} (hv : v ≤ u + T) (tau : Set.Icc (0 : ℝ) T) (phi : Euc d → ℝ) :
    ∫ z in Set.Ioc 0 v ∩ Set.Icc 0 (u + tau), coefficientField E (Q : ℝ → Coeff) z (propagatorW C z (u + tau) phi) =
      ∫ z in Set.Ioc 0 v ∩ Set.Icc 0 (u + tau), coefficientField E s z (propagatorW C z (u + tau) phi) := by
  refine setIntegral_congr_ae (measurableSet_Ioc.inter measurableSet_Icc) ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hs] with x hx hxS
  have := hx ⟨hxS.1.1.le, hxS.1.2.trans hv⟩
  simp only [coefficientField, this]

end HRS.MS.S111K4J01
