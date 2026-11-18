import HRS.MS.UniqN4bF
import HRS.MS.UniqM1Moll

/-!
# N4b of `UniqPlan.md`, part G: numerical helper lemmas for the pair estimate

* `n4b_prod_bound`: exponent bookkeeping for `a^{1-κ} b^κ ≤ c A^{1-κ} (A+G)^κ`.
* `n4b_near_final`: from the Young step to `ε G² + C A²`.
* `n4b_psi_L1`: `∫ |ς f| ≤ K₁ A`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN4b

open HRS HRS.Whole HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqM1 HRS.MS.UniqNDefs
  HRS.MS.UniqN2b HRS.MS.UniqN0

variable {d : ℕ}

theorem n4b_prod_bound {κ cb A G m b : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcb : 0 ≤ cb) (hA : 0 ≤ A)
    (hG : 0 ≤ G) (hm0 : 0 ≤ m) (hm : m ≤ cb * A) (hb : b ≤ cb * (A + G)) (hb0 : 0 ≤ b) :
    m ^ (1 - κ) * b ^ κ ≤ cb * (A ^ (1 - κ) * (A + G) ^ κ) := by
  have e1 : m ^ (1 - κ) ≤ (cb * A) ^ (1 - κ) := Real.rpow_le_rpow hm0 hm (by linarith)
  have e2 : b ^ κ ≤ (cb * (A + G)) ^ κ := Real.rpow_le_rpow hb0 hb hκ0
  rw [Real.mul_rpow hcb hA] at e1
  rw [Real.mul_rpow hcb (by positivity)] at e2
  have e3 : cb ^ (1 - κ) * cb ^ κ = cb := by
    rw [← Real.rpow_add' hcb (by norm_num)]; simp
  have hpA : 0 ≤ A ^ (1 - κ) := Real.rpow_nonneg hA _
  have hpAG : 0 ≤ (A + G) ^ κ := Real.rpow_nonneg (by positivity) _
  have hpc : 0 ≤ cb ^ (1 - κ) := Real.rpow_nonneg hcb _
  calc m ^ (1 - κ) * b ^ κ
      ≤ ((cb ^ (1 - κ) * A ^ (1 - κ)) * (cb ^ κ * (A + G) ^ κ)) := by
        exact mul_le_mul e1 e2 (Real.rpow_nonneg hb0 _) (by positivity)
    _ = (cb ^ (1 - κ) * cb ^ κ) * (A ^ (1 - κ) * (A + G) ^ κ) := by ring
    _ = _ := by rw [e3]

theorem n4b_near_final {κ Cρ C₂ cb Lθ N A G ε Cy : ℝ} (hκ1 : κ < 1) (hCρ : 0 ≤ Cρ) (hC₂ : 0 ≤ C₂)
    (hcb : 0 ≤ cb) (hLθ : 0 ≤ Lθ) (hN : 0 ≤ N) (hA : 0 ≤ A) (hG : 0 ≤ G) (hε : 0 < ε)
    (hy : G * A ^ (1 - κ) * (A + G) ^ κ + A ^ (2 - κ) * (A + G) ^ κ ≤
      ε / (Cρ * C₂ * cb * max 1 (Lθ * N) + 1) * G ^ 2 + Cy * A ^ 2) :
    Cρ * (C₂ * (cb * (A ^ (1 - κ) * (A + G) ^ κ))) * (G + Lθ * (N * A)) ≤
      ε * G ^ 2 + Cρ * C₂ * cb * max 1 (Lθ * N) * Cy * A ^ 2 := by
  set Mx : ℝ := max 1 (Lθ * N) with hMx
  have hMx1 : 1 ≤ Mx := le_max_left _ _
  set Q0 : ℝ := Cρ * C₂ * cb * Mx with hQ0def
  have hQ0 : 0 ≤ Q0 := by positivity
  have hAq : A * A ^ (1 - κ) = A ^ (2 - κ) := by
    rw [← Real.rpow_one_add' hA (by linarith)]
    congr 1; ring
  have hGm : G + Lθ * (N * A) ≤ Mx * (G + A) := by
    have : Lθ * (N * A) ≤ Mx * A := by
      calc Lθ * (N * A) = (Lθ * N) * A := by ring
        _ ≤ Mx * A := mul_le_mul_of_nonneg_right (le_max_right _ _) hA
    nlinarith [mul_nonneg (sub_nonneg.2 hMx1) hG]
  have hq : 0 ≤ A ^ (1 - κ) * (A + G) ^ κ :=
    mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg (by positivity) _)
  have hQ1 : Q0 * (ε / (Q0 + 1)) ≤ ε := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  calc Cρ * (C₂ * (cb * (A ^ (1 - κ) * (A + G) ^ κ))) * (G + Lθ * (N * A))
      ≤ Cρ * (C₂ * (cb * (A ^ (1 - κ) * (A + G) ^ κ))) * (Mx * (G + A)) := by gcongr
    _ = Q0 * (G * A ^ (1 - κ) * (A + G) ^ κ + A * A ^ (1 - κ) * (A + G) ^ κ) := by
        rw [hQ0def]; ring
    _ = Q0 * (G * A ^ (1 - κ) * (A + G) ^ κ + A ^ (2 - κ) * (A + G) ^ κ) := by rw [hAq]
    _ ≤ Q0 * (ε / (Q0 + 1) * G ^ 2 + Cy * A ^ 2) := by
        gcongr
    _ = (Q0 * (ε / (Q0 + 1))) * G ^ 2 + Q0 * Cy * A ^ 2 := by ring
    _ ≤ ε * G ^ 2 + Q0 * Cy * A ^ 2 := by gcongr

theorem n4b_psi_L1 {p : Euc d} {L : ℝ} {ς f : Euc d → ℝ} {A K1 : ℝ} (hA : 0 ≤ A)
    (hς01 : ∀ y, 0 ≤ ς y ∧ ς y ≤ 1) (hςs : tsupport ς ⊆ closedBall p (2 * L))
    (hf : Continuous f) (hψ : Continuous (fun x => ς x * f x))
    (hψc : HasCompactSupport (fun x => ς x * f x))
    (hK1 : ∫ y in closedBall p (2 * L), ‖f y‖ ≤ K1 * A) :
    ∫ x, |ς x * f x| ≤ K1 * A := by
  have hI0 : Integrable (fun x => |ς x * f x|) volume :=
    (hψ.integrable_of_hasCompactSupport hψc).abs
  have hsub : Function.support (fun x => ς x * f x) ⊆ closedBall p (2 * L) :=
    (Function.support_mul_subset_left ς f).trans ((subset_tsupport ς).trans hςs)
  have hI1 : IntegrableOn (fun y => ‖f y‖) (closedBall p (2 * L)) volume :=
    (hf.norm.continuousOn).integrableOn_compact (isCompact_closedBall _ _)
  have hz : ∀ y ∉ closedBall p (2 * L), |ς y * f y| = 0 := fun y hy => by
    have : ς y * f y = 0 := by
      by_contra h0; exact hy (hsub (Function.mem_support.2 h0))
    simp [this]
  calc ∫ x, |ς x * f x| = ∫ x in closedBall p (2 * L), |ς x * f x| :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hz).symm
    _ ≤ ∫ x in closedBall p (2 * L), ‖f x‖ :=
        setIntegral_mono_on hI0.integrableOn hI1 measurableSet_closedBall
          (fun y _ => by
            simp only [Real.norm_eq_abs]
            rw [abs_mul]
            calc |ς y| * |f y| ≤ 1 * |f y| := by
                  gcongr; rw [abs_of_nonneg (hς01 y).1]; exact (hς01 y).2
              _ = _ := one_mul _)
    _ ≤ K1 * A := hK1

end HRS.MS.UniqN4b
