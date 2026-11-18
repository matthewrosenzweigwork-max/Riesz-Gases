import HRS.MS.R2InterpAux10
import HRS.MS.CovMeasAux2

/-!
# S10.2 (worker S102), part 11 (packet I3): the coordinates and the Lipschitz continuity of `V^{t,u}z`

With `hlin` (linearity of the propagator on finite combinations of the dual tests; the hypothesis of S10.1) and the orbit data:
`coord (r2Vprop C m t u z) α = z(U^{u,t}φ_α)`, the sequence is in `ℓ²` (so `OscDual.ofSeq` is not junk), and
`‖V^{t,u}z - V^{t',u}z‖ ≤ K (t - t')`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MS.FixEq

variable {d : ℕ}

/-- The linearity hypothesis of S10.1 on the propagator. -/
def S102Lin (C : WholeCoeff d) (m T : ℝ) : Prop :=
  ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ, IsR2DualCombo m φ → IsR2DualCombo m ψ →
    propagatorW C u t (φ + c • ψ) = propagatorW C u t φ + c • propagatorW C u t ψ

theorem s102_U_zero {C : WholeCoeff d} {m T : ℝ} (hlin : S102Lin C m T) {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t)
    (htT : t ≤ T) : propagatorW C u t (0 : Euc d → ℝ) = 0 := by
  have := hlin u t hu hut htT 0 0 1 (s101_isCombo_zero m) (s101_isCombo_zero m)
  simp only [one_smul, add_zero] at this
  funext x
  have hx := congrFun this x
  simp only [Pi.add_apply] at hx
  show propagatorW C u t 0 x = (0 : ℝ)
  linarith

theorem s102_U_herm {C : WholeCoeff d} {m T : ℝ} (hlin : S102Lin C m T) {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t)
    (htT : t ≤ T) (α : MultiIndex d) :
    propagatorW C u t (hermiteFunD α) = oscEigenvalue d α ^ (m / 2) • propagatorW C u t (oscTestFun m α) := by
  have h1 : (hermiteFunD α : Euc d → ℝ) = (0 : Euc d → ℝ) + (oscEigenvalue d α ^ (m / 2)) • oscTestFun m α := by
    funext x
    simp only [Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, zero_add, oscTestFun]
    rw [← mul_assoc, mul_comm (oscEigenvalue d α ^ (m / 2)) (oscEigenvalue d α ^ (-(m / 2))),
      rpow_neg_half_mul _ _ (oscEv_pos α), one_mul]
  rw [h1, hlin u t hu hut htT 0 (oscTestFun m α) _ (s101_isCombo_zero m) (s101_isCombo_single m α),
    s102_U_zero hlin hu hut htT, zero_add]

theorem s102_coord_sub {m : ℝ} (u v : OscDual d m) (α : MultiIndex d) :
    OscDual.coord (u - v) α = OscDual.coord u α - OscDual.coord v α := by
  rw [sub_eq_add_neg, OscDual.coord_add, show (-v) = (-1 : ℝ) • v by simp, OscDual.coord_smul]
  ring

section V

variable {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ} {z : (Euc d → ℝ) → ℝ}

theorem s102_z_orbit_memℓp (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hz : S102Z r Pw z)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) {t : ℝ} (ht : t ∈ Icc u T) :
    Memℓp (fun α : MultiIndex d => z (propagatorW C u t (oscTestFun m α))) 2 := by
  obtain ⟨M, hM⟩ := hz.bdd
  have hs : Summable fun α : MultiIndex d => (|M| * (s57pC d r Pw * c α)) ^ 2 :=
    (hD.summable.mul_left ((|M| * s57pC d r Pw) ^ 2)).congr (fun α => by ring)
  exact s101_memℓp_of_bound (c := fun α => z (propagatorW C u t (oscTestFun m α)))
    (b := fun α => |M| * (s57pC d r Pw * c α)) hs (fun α => s102_z_orbit_bound hP hD hz hM hu ht α)

theorem s102_Vprop_coord (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hz : S102Z r Pw z)
    (hlin : S102Lin C m T) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) {t : ℝ} (ht : t ∈ Icc u T) (α : MultiIndex d) :
    OscDual.coord (r2Vprop C m t u z) α = z (propagatorW C u t (oscTestFun m α)) := by
  have hmem := s102_z_orbit_memℓp hP hD hz hu ht
  have hseq : (fun α : MultiIndex d => oscEigenvalue d α ^ (-(m / 2)) *
      z (propagatorW C u t (hermiteFunD α))) = fun α => z (propagatorW C u t (oscTestFun m α)) := by
    funext β
    rw [s102_U_herm hlin hu.1 ht.1 ht.2 β, hz.smul _ _ (s102_orbit_test hP hD hu ht β).1,
      ← mul_assoc, rpow_neg_half_mul _ _ (oscEv_pos β), one_mul]
  have hmem' : Memℓp (fun α : MultiIndex d => oscEigenvalue d α ^ (-(m / 2)) *
      z (propagatorW C u t (hermiteFunD α))) 2 := by rw [hseq]; exact hmem
  unfold r2Vprop
  rw [OscDual.coord_ofSeq_of_mem _ hmem']
  exact congrFun hseq α

/-- Lipschitz continuity of `t ↦ V^{t,u}z` on `[u,T]`. -/
theorem s102_Vprop_lip (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hz : S102Z r Pw z)
    (hlin : S102Lin C m T) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t' t : ℝ}, t' ∈ Icc u T → t ∈ Icc u T → t' ≤ t →
      ‖r2Vprop C m t u z - r2Vprop C m t' u z‖ ≤ K * (t - t') := by
  obtain ⟨M, hM⟩ := hz.bdd
  set A : ℝ := |M| * s57pC d r Pw with hA
  have hA0 : 0 ≤ A := mul_nonneg (abs_nonneg M) (s57pC_nonneg d r Pw)
  set S : ℝ := ∑' α, c α ^ 2 with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun α => sq_nonneg _
  refine ⟨A * Real.sqrt S, mul_nonneg hA0 (Real.sqrt_nonneg _), fun {t' t} ht' ht htt => ?_⟩
  have hcoord : ∀ α, |OscDual.coord (r2Vprop C m t u z - r2Vprop C m t' u z) α| ≤ A * (t - t') * c α := by
    intro α
    rw [s102_coord_sub, s102_Vprop_coord hP hD hz hlin hu ht, s102_Vprop_coord hP hD hz hlin hu ht']
    refine (s102_z_orbit_diff hP hD hz hM hu ht' ht htt α).trans (le_of_eq ?_)
    rw [hA]; ring
  have hsq : Summable fun α => (A * (t - t') * c α) ^ 2 :=
    (hD.summable.mul_left ((A * (t - t')) ^ 2)).congr (fun α => by ring)
  rw [OscDual.norm_eq_coord]
  have h1 : ∑' α, OscDual.coord (r2Vprop C m t u z - r2Vprop C m t' u z) α ^ 2 ≤
      (A * (t - t')) ^ 2 * S := by
    calc _ ≤ ∑' α, (A * (t - t') * c α) ^ 2 :=
          Summable.tsum_le_tsum (fun α => by
            have := hcoord α
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) this 2)
            (OscDual.coord_sq_summable' _) hsq
      _ = (A * (t - t')) ^ 2 * S := by
          simp_rw [mul_pow]
          rw [tsum_mul_left]
  calc Real.sqrt _ ≤ Real.sqrt ((A * (t - t')) ^ 2 * S) := Real.sqrt_le_sqrt h1
    _ = A * (t - t') * Real.sqrt S := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hA0 (sub_nonneg.2 htt))]
    _ = A * Real.sqrt S * (t - t') := by ring

end V

end HRS.MS.R2Interp

end
