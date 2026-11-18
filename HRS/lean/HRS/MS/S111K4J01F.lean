import HRS.MS.S111K4J01E

/-!
# S11.1 / J01 piece: the drift interval path of an `L¹` coefficient path, additivity in `q` and the norm bound (S11K4)

`Dq q a b = s111k2_Dpath (hdata q) a b` is the B04 drift path of the zero-mass forcing `zq E q`.  Because the integrand of
B04's `Dfun` only sees `z v` for a.e. `v` and `((q + q') v) = q v + q' v` a.e., `Dq` is additive and homogeneous in `q`; and
`‖Dq q a b‖ ≤ K ∫_{(a,b]} age ‖q‖`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole HRS.MS.S111K2

section drift
variable {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) {C : WholeCoeff d} {c0 S T u : ℝ}
  {b : MultiIndex d → ℝ}
  (hdata : ∀ q : TimeCoeff (u + T),
    S111k2Drift C (wholeSpaceIndex d : ℝ) c0 r b S T u Pw (zq E q))

/-- The drift interval path of the coefficient path `q`. -/
def Dq (q : TimeCoeff (u + T)) (a b' : ℝ) : OscPath d (wholeSpaceIndex d : ℝ) T :=
  s111k2_Dpath (hdata q) a b'

theorem zq_dual_lt_top (q : TimeCoeff (u + T)) (v : ℝ) : dualNormE r Pw (zq E q v) < ⊤ :=
  lt_of_le_of_lt (dualNormE_coefficientField_le E (qr E q) v) ENNReal.ofReal_lt_top

theorem Dq_at {q : TimeCoeff (u + T)} {a b' : ℝ} (ha : 0 ≤ a) (hab : a ≤ b') (hb : b' ≤ u + T)
    (τ : Set.Icc (0 : ℝ) T) :
    OscPath.at' (Dq E hdata q a b') τ = s111k2_Dfun C (wholeSpaceIndex d : ℝ) (zq E q) u a b' τ :=
  s111k2_Dpath_at (hdata q) ha hab hb τ

include hdata in
/-- Linear combinations of coefficient paths: the integrand `W` is linear for a.e. time. -/
theorem W_lin {q q' q'' : TimeCoeff (u + T)} {c : ℝ} (hlin : ∀ᵐ v ∂(volume.restrict (Set.Icc (0 : ℝ) (u + T))),
      (q'' : ℝ → Coeff) v = (q : ℝ → Coeff) v + c • (q' : ℝ → Coeff) v)
    {a b' : ℝ} (ha : 0 ≤ a) (hb : b' ≤ u + T) (τ : ℝ) :
    ∀ᵐ v ∂(volume.restrict (Set.Ioc a b')),
      s111k2_W C (wholeSpaceIndex d : ℝ) (zq E q'') u v τ =
        s111k2_W C (wholeSpaceIndex d : ℝ) (zq E q) u v τ +
          c • s111k2_W C (wholeSpaceIndex d : ℝ) (zq E q') u v τ := by
  have hsub : Set.Ioc a b' ⊆ Set.Icc (0 : ℝ) (u + T) := fun v hv => ⟨ha.trans hv.1.le, hv.2.trans hb⟩
  have h1 : ∀ᵐ v ∂(volume.restrict (Set.Ioc a b')), (q'' : ℝ → Coeff) v =
      (q : ℝ → Coeff) v + c • (q' : ℝ → Coeff) v := ae_restrict_of_ae_restrict_of_subset hsub hlin
  filter_upwards [h1, ae_restrict_mem measurableSet_Ioc] with v hv hvI
  have hvH : v ∈ Set.Icc (0 : ℝ) (u + T) := hsub hvI
  unfold s111k2_W
  by_cases hvτ : v ≤ u + τ
  · rw [if_pos hvτ, if_pos hvτ, if_pos hvτ]
    unfold s111k2_Y
    have hm1 := s111k2_Ycoord_memell (hdata q).hW (hdata q).hbs (hdata q).hP (hdata q).hz hvH
      (zq_mass E q v) (zq_dual_lt_top E q v) hvτ
    have hm2 := s111k2_Ycoord_memell (hdata q').hW (hdata q').hbs (hdata q').hP (hdata q').hz hvH
      (zq_mass E q' v) (zq_dual_lt_top E q' v) hvτ
    have e : (fun α => zq E q'' v (propagatorW C v (u + τ) (oscTestFun (wholeSpaceIndex d : ℝ) α))) =
        fun α => zq E q v (propagatorW C v (u + τ) (oscTestFun (wholeSpaceIndex d : ℝ) α)) +
          c * zq E q' v (propagatorW C v (u + τ) (oscTestFun (wholeSpaceIndex d : ℝ) α)) := by
      funext α
      simp only [zq, coefficientField, qr]
      rw [hv, map_add, map_smul, inner_add_left, inner_smul_left]
      simp
    have hm3 : Memℓp (fun α => c * zq E q' v (propagatorW C v (u + τ)
        (oscTestFun (wholeSpaceIndex d : ℝ) α))) 2 := by
      have := hm2.const_smul c
      exact this
    rw [e, HRS.MS.CovMeas.s101_ellVec_add hm1 hm3, HRS.MS.CovMeas.s101_ellVec_smul c hm2]
  · rw [if_neg hvτ, if_neg hvτ, if_neg hvτ]; simp

end drift

end HRS.MS.S111K4J01
