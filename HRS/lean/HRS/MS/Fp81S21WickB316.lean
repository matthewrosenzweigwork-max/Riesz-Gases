import HRS.MS.Fp81S21WickB315

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

/-- The full operator agrees with the finite half-Wick polynomial for arbitrary
L² factors and arbitrary coefficient matrices. -/
theorem fp81s21_wickB316_finite_rank_agreement
    {d m : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (Kstar : ℝ)
    (hL : ‖L‖ ≤ Kstar)
    (hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
      HRS.IsCenteredGaussian (P.map fun ω => fun i => (L (v i)) ω))
    (u : Fin m → Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (c : Fin m → Fin m → ℝ)
    (hk : MemLp (fp81s21_wickG_finite_rank_kernel u c) 2 (μ.prod μ))
    (hW : MemLp (fp81s21_wickG_finite_rank_polynomial L u hu c) 2 P) :
    fp81s21_wickG_operator L Kstar hL hJoint
        (hk.toLp (fp81s21_wickG_finite_rank_kernel u c)) =
      hW.toLp (fp81s21_wickG_finite_rank_polynomial L u hu c) := by
  let s := fp81s21_wickB23_symmCoeff c
  let hs := (fp81s21_wickG_finite_rank_bound L Kstar hL hJoint u hu s).1
  have hclass := fp81s21_wickB23_symmetrize_finite_rank u hu c hk hs
  have hfixed : fp81s21_wickB23_symmetrize μ
      (hs.toLp (fp81s21_wickG_finite_rank_kernel u s)) =
      hs.toLp (fp81s21_wickG_finite_rank_kernel u s) := by
    calc
      _ = fp81s21_wickB23_symmetrize μ (fp81s21_wickB23_symmetrize μ
          (hk.toLp (fp81s21_wickG_finite_rank_kernel u c))) := congrArg _ hclass.symm
      _ = fp81s21_wickB23_symmetrize μ (hk.toLp (fp81s21_wickG_finite_rank_kernel u c)) :=
        fp81s21_wickB23_symmetrize_idempotent μ _
      _ = _ := hclass
  let z : fp81s21_wickB313_symmetricRepresentable μ :=
    ⟨hs.toLp (fp81s21_wickG_finite_rank_kernel u s),
      ⟨⟨m, u, hu, s, hs, rfl⟩, by
        change fp81s21_wickB23_symmetrize μ
          (hs.toLp (fp81s21_wickG_finite_rank_kernel u s)) -
          hs.toLp (fp81s21_wickG_finite_rank_kernel u s) = 0
        rw [hfixed, sub_self]⟩⟩
  have hp : fp81s21_wickB22_polynomialLp L Kstar hL hJoint u hu s =
      hW.toLp (fp81s21_wickG_finite_rank_polynomial L u hu c) := by
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun ω => congrFun (fp81s21_wickB3_polynomial_symmCoeff L u hu c) ω
  calc
    fp81s21_wickG_operator L Kstar hL hJoint
        (hk.toLp (fp81s21_wickG_finite_rank_kernel u c)) =
      fp81s21_wickG_operator L Kstar hL hJoint
        (fp81s21_wickB23_symmetrize μ (hk.toLp (fp81s21_wickG_finite_rank_kernel u c))) :=
      fp81s21_wickB311_operator_symmetrize L Kstar hL hJoint _
    _ = fp81s21_wickB315_operator L Kstar hL hJoint z := by
      rw [← fp81s21_wickB315_operator_eq L Kstar hL hJoint, hclass]
    _ = fp81s21_wickB314_linear L Kstar hL hJoint z :=
      fp81s21_wickB315_operator_finite L Kstar hL hJoint z
    _ = fp81s21_wickB22_polynomialLp L Kstar hL hJoint u hu s :=
      fp81s21_wickB314_operator_eq L Kstar hL hJoint z u hu s hs rfl
    _ = _ := hp

#print axioms fp81s21_wickB316_finite_rank_agreement

end HRS.Fp81.S21
end
