import HRS.MS.SA12X3C7C10

/-!
# S.A.12 C7 (SA12X3), part C11 (7C): row and weighted column bounds of `Kfin`
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12x3_Kfin_row {κ : ℤ} (K : (Fin d → ℤ) → (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0) {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ r ∈ sa12x3_Rset d κ, ∀ q, ∑' y, (K r q y : ℝ≥0∞) ≤ ENNReal.ofReal C) (hκ : 1 ≤ κ)
    (z : Fin d → ℤ) :
    ∑' z'', (sa12x3_Kfin κ K z z'' : ℝ≥0∞) ≤ ENNReal.ofReal (2 ^ d * C) := by
  have := sa12x3_Kfin_mass (κ := κ) K z (fun _ => 1)
  simp only [mul_one] at this
  have h2 : ∑' y, (K (fun i => z i % κ) (fun i => z i / κ) y : ℝ≥0∞) *
      ∑ ε : Fin d → Fin 2, (1 : ℝ≥0∞) = (2 ^ d : ℝ≥0∞) * ∑' y, (K (fun i => z i % κ) (fun i => z i / κ) y : ℝ≥0∞) := by
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun y => ?_
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, mul_comm]
  rw [this, h2]
  have h3 := hrow _ (sa12x3_res_mem hκ z) (fun i => z i / κ)
  calc (2 ^ d : ℝ≥0∞) * ∑' y, (K (fun i => z i % κ) (fun i => z i / κ) y : ℝ≥0∞)
      ≤ (2 ^ d : ℝ≥0∞) * ENNReal.ofReal C := by gcongr
    _ = ENNReal.ofReal (2 ^ d * C) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        simp

theorem sa12x3_Kfin_col {κ : ℤ} (hκ : 1 ≤ κ) (K : (Fin d → ℤ) → (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0) {C : ℝ}
    (hC : 0 ≤ C)
    (hcol : ∀ r ∈ sa12x3_Rset d κ, ∀ y, ∑' q, ENNReal.ofReal (cellWeight d q) * (K r q y : ℝ≥0∞) ≤
      ENNReal.ofReal C * ENNReal.ofReal (cellWeight d y)) (z'' : Fin d → ℤ) :
    ∑' z, ENNReal.ofReal (cellWeight d z) * (sa12x3_Kfin κ K z z'' : ℝ≥0∞) ≤
      ENNReal.ofReal (2 ^ d * (1 + κ * Real.sqrt d) ^ ((d : ℝ) + 3) * (sa12x3_Rset d κ).card * C *
        (1 + Real.sqrt d) ^ ((d : ℝ) + 3)) * ENNReal.ofReal (cellWeight d z'') := by
  set A : ℝ := (1 + κ * Real.sqrt d) ^ ((d : ℝ) + 3) with hA
  set B : ℝ := (1 + Real.sqrt d) ^ ((d : ℝ) + 3) with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  unfold sa12x3_Kfin
  simp_rw [ENNReal.coe_finset_sum, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun ε _ => ENNReal.summable)]
  -- bound for one shift
  have hε : ∀ ε : Fin d → Fin 2,
      ∑' z, ENNReal.ofReal (cellWeight d z) * (K (fun i => z i % κ) (fun i => z i / κ)
        (z'' - fun i => ((ε i : ℕ) : ℤ)) : ℝ≥0∞) ≤
      ENNReal.ofReal (A * (sa12x3_Rset d κ).card * C * B) * ENNReal.ofReal (cellWeight d z'') := by
    intro ε
    set y : Fin d → ℤ := z'' - fun i => ((ε i : ℕ) : ℤ) with hy
    obtain ⟨G, hG⟩ : ∃ G : (Fin d → ℤ) → ↥(sa12x3_Rset d κ) → ℝ≥0∞, G = fun (a : Fin d → ℤ) (b : ↥(sa12x3_Rset d κ)) =>
      ENNReal.ofReal A * (ENNReal.ofReal (cellWeight d a) * (K b.1 a y : ℝ≥0∞)) := ⟨_, rfl⟩
    obtain ⟨φ, hφ⟩ : ∃ φ : (Fin d → ℤ) → (Fin d → ℤ) × ↥(sa12x3_Rset d κ), φ = fun z =>
      (((fun i => z i / κ) : Fin d → ℤ), (⟨(fun i => z i % κ), sa12x3_res_mem hκ z⟩ : ↥(sa12x3_Rset d κ))) :=
      ⟨_, rfl⟩
    have hstep : ∀ z : Fin d → ℤ, ENNReal.ofReal (cellWeight d z) *
        (K (fun i => z i % κ) (fun i => z i / κ) y : ℝ≥0∞) ≤ G (φ z).1 (φ z).2 := by
      intro z
      rw [hG, hφ]
      dsimp only
      rw [← mul_assoc, ← ENNReal.ofReal_mul hA0]
      gcongr
      exact sa12x3_w_quo hκ z
    have hinj : Function.Injective φ := by
      intro z z' h
      rw [hφ] at h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      funext i
      have h1 := congrFun h.1 i
      have h2 := congrFun h.2 i
      rw [← Int.mul_ediv_add_emod (z i) κ, ← Int.mul_ediv_add_emod (z' i) κ, h1, h2]
    have hsum : ∑' p : (Fin d → ℤ) × ↥(sa12x3_Rset d κ), G p.1 p.2 =
        ∑ r : ↥(sa12x3_Rset d κ), ENNReal.ofReal A * ∑' q, ENNReal.ofReal (cellWeight d q) *
          (K (r : Fin d → ℤ) q y : ℝ≥0∞) := by
      rw [ENNReal.tsum_prod, ENNReal.tsum_comm, tsum_fintype]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hG]
      exact ENNReal.tsum_mul_left
    calc ∑' z, ENNReal.ofReal (cellWeight d z) * (K (fun i => z i % κ) (fun i => z i / κ) y : ℝ≥0∞)
        ≤ ∑' z, G (φ z).1 (φ z).2 := ENNReal.tsum_le_tsum hstep
      _ ≤ ∑' p : (Fin d → ℤ) × ↥(sa12x3_Rset d κ), G p.1 p.2 :=
          ENNReal.tsum_comp_le_tsum_of_injective hinj (fun p => G p.1 p.2)
      _ = _ := hsum
      _ ≤ ∑ r : ↥(sa12x3_Rset d κ), ENNReal.ofReal A * (ENNReal.ofReal C * ENNReal.ofReal (cellWeight d y)) := by
          refine Finset.sum_le_sum fun r _ => ?_
          gcongr
          exact hcol r r.2 y
      _ ≤ ENNReal.ofReal (A * (sa12x3_Rset d κ).card * C * B) * ENNReal.ofReal (cellWeight d z'') := by
          have hw : ENNReal.ofReal (cellWeight d y) ≤ ENNReal.ofReal B * ENNReal.ofReal (cellWeight d z'') := by
            rw [← ENNReal.ofReal_mul hB0]
            refine ENNReal.ofReal_le_ofReal ?_
            have := sa12x3_w_shift y ε
            rwa [show y + (fun i => ((ε i : ℕ) : ℤ)) = z'' by simp [hy]] at this
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
          have e : ENNReal.ofReal (A * (sa12x3_Rset d κ).card * C * B) =
              ENNReal.ofReal A * ((sa12x3_Rset d κ).card : ℝ≥0∞) * ENNReal.ofReal C * ENNReal.ofReal B := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
          rw [e]
          calc ((sa12x3_Rset d κ).card : ℝ≥0∞) * (ENNReal.ofReal A * (ENNReal.ofReal C * ENNReal.ofReal (cellWeight d y)))
              ≤ ((sa12x3_Rset d κ).card : ℝ≥0∞) * (ENNReal.ofReal A * (ENNReal.ofReal C *
                (ENNReal.ofReal B * ENNReal.ofReal (cellWeight d z'')))) := by gcongr
            _ = _ := by ring
  have hfin : ∑ ε : Fin d → Fin 2, ENNReal.ofReal (A * (sa12x3_Rset d κ).card * C * B) *
      ENNReal.ofReal (cellWeight d z'') =
      ENNReal.ofReal (2 ^ d * A * (sa12x3_Rset d κ).card * C * B) * ENNReal.ofReal (cellWeight d z'') := by
    have e : 2 ^ d * A * ((sa12x3_Rset d κ).card : ℝ) * C * B = 2 ^ d * (A * (sa12x3_Rset d κ).card * C * B) := by ring
    have h2d : ENNReal.ofReal (2 ^ d * (A * (sa12x3_Rset d κ).card * C * B)) =
        2 ^ d * ENNReal.ofReal (A * (sa12x3_Rset d κ).card * C * B) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
      simp
    rw [e, h2d, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul]
    simp only [Nat.cast_pow, Nat.cast_ofNat, mul_assoc]
  exact (Finset.sum_le_sum fun ε _ => hε ε).trans hfin.le

end HRS.MH.AdjointRd.Phase2SA12Near
