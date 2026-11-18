import HRS.MS.MfeConfAux110

/-!
# S.B.1, packet F9 (part 14): the envelope of the level-`M` commutator energy (D05 of the Pro note)

`sb1_Ck_env`: `|C^M_r(Z)| ≤ K_r (A₁ (P_M(Z) + ℓ₀(Z)) + A₂)` with `P_M = (2N²)⁻¹ ∑_{i≠j} k_M(Z_i - Z_j)`, `ℓ₀` a logarithmic correction
and `A₁, A₂` independent of `M`, `Z`, `r`: the singular pair energy is controlled by the (regularised) Gibbs exponent `P_M`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- the regularised pair energy `P_M(Z) = (2N²)⁻¹ ∑_{i≠j} k(Z_i - Z_j)` -/
def sb1PM (k : Euc d → ℝ) (N : ℕ) (Z : Whole.EucConfig d N) : ℝ :=
  (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, k (Z i - Z j)

/-- the logarithmic correction -/
def sb1ell (d : ℕ) (N : ℕ) (Z : Whole.EucConfig d N) : ℝ :=
  (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, (Real.log (1 + ‖Z i - Z j‖) + 1)

theorem sb1_Ck_env {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ)
    (hN : 1 ≤ N) :
    ∃ A₁ A₂ : ℝ, 0 < A₁ ∧ 0 ≤ A₂ ∧ ∀ (M : ℕ) {r : ℝ}, r ∈ Set.Icc (0 : ℝ) T → ∀ {Kr : ℝ}, 0 ≤ Kr →
      (∀ x y, ‖Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y‖ ≤ Kr * ‖x - y‖) →
      ∀ Z : Whole.EucConfig d N, |sb1_lv_Ck D (sb1kM d D.s M) N ρ r Z| ≤
        Kr * (A₁ * (sb1PM (sb1kM d D.s M) N Z + sb1ell d N Z) + A₂) := by
  have hs0 := H.tr.hs0
  have hd := H.tr.hd
  have hsd := H.tr.hsd
  obtain ⟨A1, hA10, hA1⟩ := sb1kM_grad_env (d := d) D.s hs0
  obtain ⟨A2, hA20, hA2⟩ := sb1kM_hk_bound (d := d) D.s hs0
  have hCs : 0 ≤ sb1Cs d D.s C3 := by
    unfold sb1Cs; have := H.C3nn; have := sb1Isig_nonneg (d := d) D.s; positivity
  refine ⟨A1 + 1, 3 / 2 * (A2 * sb1Cs d D.s C3), by linarith, by positivity, fun M r hr Kr hKr hL Z => ?_⟩
  have R := H.rho hd hr
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  set k := sb1kM d D.s M with hk
  set v := Whole.mfeTransportW D (ρ r) with hv
  -- pair kernel bound
  have hpair : ∀ x y : Euc d, |fderiv ℝ k (x - y) (v x - v y)| ≤
      Kr * (A1 + 1) * (k (x - y) + Real.log (1 + ‖x - y‖) + 1) := by
    intro x y
    have h1 := hA1 M (x - y)
    have hnn : 0 ≤ k (x - y) + Real.log (1 + ‖x - y‖) + 1 := by
      have hl := (sb1kM_ker (d := d) D.s hs0 M).lower (x - y)
      have hlog : 0 ≤ Real.log (1 + ‖x - y‖) := Real.log_nonneg (by linarith [norm_nonneg (x - y)])
      have hκ0 := sb1kap_nonneg D.s
      have hκ1 : sb1kap D.s ≤ 1 := by unfold sb1kap; split_ifs <;> norm_num
      nlinarith
    have h1' : ‖x - y‖ * ‖gradient k (x - y)‖ ≤ (A1 + 1) * (k (x - y) + Real.log (1 + ‖x - y‖) + 1) :=
      h1.trans (mul_le_mul_of_nonneg_right (by linarith) hnn)
    rw [← p4k_inner_grad, ← Real.norm_eq_abs]
    calc ‖inner ℝ (gradient k (x - y)) (v x - v y)‖ ≤ ‖gradient k (x - y)‖ * ‖v x - v y‖ := norm_inner_le_norm _ _
      _ ≤ ‖gradient k (x - y)‖ * (Kr * ‖x - y‖) := mul_le_mul_of_nonneg_left (hL x y) (norm_nonneg _)
      _ = Kr * (‖x - y‖ * ‖gradient k (x - y)‖) := by ring
      _ ≤ Kr * ((A1 + 1) * (k (x - y) + Real.log (1 + ‖x - y‖) + 1)) := mul_le_mul_of_nonneg_left h1' hKr
      _ = _ := by ring
  have hPG : ∀ x, |sb1PG (fun x y => fderiv ℝ k (x - y) (v x - v y)) (ρ r) x| ≤ A2 * Kr * sb1Cs d D.s C3 := fun x =>
    sb1_PG_abs_le hd hs0 hsd R (mul_nonneg hA20 hKr) (fun x y => hA2 M hKr hL x y) x
  have hcPG : |∫ x, ρ r x * sb1PG (fun x y => fderiv ℝ k (x - y) (v x - v y)) (ρ r) x| ≤
      A2 * Kr * sb1Cs d D.s C3 := by
    have hb : Integrable (fun x => ρ r x * (A2 * Kr * sb1Cs d D.s C3)) := R.integrable.mul_const _
    have := norm_integral_le_of_norm_le hb (f := fun x => ρ r x * sb1PG (fun x y => fderiv ℝ k (x - y) (v x - v y)) (ρ r) x)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (R.dens.nonneg x)]
        exact mul_le_mul_of_nonneg_left (hPG x) (R.dens.nonneg x))
    rw [Real.norm_eq_abs, integral_mul_const, R.int_one, one_mul] at this
    exact this
  unfold sb1_lv_Ck
  rw [sb1_pairEnergy_eq R.dens]
  have hS : |(1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (Z i - Z j) (v (Z i) - v (Z j))| ≤
      Kr * (A1 + 1) * (sb1PM k N Z + sb1ell d N Z) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * (N : ℝ) ^ 2))]
    calc (1 / (2 * (N : ℝ) ^ 2)) * |∑ i, ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (Z i - Z j) (v (Z i) - v (Z j))|
        ≤ (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
            Kr * (A1 + 1) * (k (Z i - Z j) + Real.log (1 + ‖Z i - Z j‖) + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hpair _ _)
      _ = Kr * (A1 + 1) * (sb1PM k N Z + sb1ell d N Z) := by
          unfold sb1PM sb1ell
          have e1 : ∑ i, ∑ j ∈ Finset.univ.erase i, Kr * (A1 + 1) * (k (Z i - Z j) + Real.log (1 + ‖Z i - Z j‖) + 1) =
              Kr * (A1 + 1) * (∑ i, ∑ j ∈ Finset.univ.erase i, k (Z i - Z j) +
                ∑ i, ∑ j ∈ Finset.univ.erase i, (Real.log (1 + ‖Z i - Z j‖) + 1)) := by
            rw [← Finset.sum_add_distrib, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Finset.sum_add_distrib, Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
          rw [e1]
          ring
  have hG : |(1 / (N : ℝ)) * ∑ i, sb1PG (fun x y => fderiv ℝ k (x - y) (v x - v y)) (ρ r) (Z i)| ≤
      A2 * Kr * sb1Cs d D.s C3 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))]
    calc 1 / (N : ℝ) * |∑ i, sb1PG (fun x y => fderiv ℝ k (x - y) (v x - v y)) (ρ r) (Z i)|
        ≤ 1 / (N : ℝ) * ∑ _i : Fin N, A2 * Kr * sb1Cs d D.s C3 :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hPG _))
            (by positivity)
      _ = A2 * Kr * sb1Cs d D.s C3 := by simp; field_simp
  have hA0 : 0 ≤ A2 * Kr * sb1Cs d D.s C3 := by positivity
  calc |(1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (Z i - Z j) (v (Z i) - v (Z j)) -
        (1 / (N : ℝ)) * ∑ i, sb1PG (fun x y => fderiv ℝ k (x - y) (v x - v y)) (ρ r) (Z i) +
        (1 / 2) * ∫ x, ρ r x * sb1PG (fun x y => fderiv ℝ k (x - y) (v x - v y)) (ρ r) x|
      ≤ |(1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (Z i - Z j) (v (Z i) - v (Z j))| +
        |(1 / (N : ℝ)) * ∑ i, sb1PG (fun x y => fderiv ℝ k (x - y) (v x - v y)) (ρ r) (Z i)| +
        |(1 / 2) * ∫ x, ρ r x * sb1PG (fun x y => fderiv ℝ k (x - y) (v x - v y)) (ρ r) x| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ Kr * (A1 + 1) * (sb1PM k N Z + sb1ell d N Z) + A2 * Kr * sb1Cs d D.s C3 + (1 / 2) * (A2 * Kr * sb1Cs d D.s C3) := by
        refine add_le_add (add_le_add hS hG) ?_
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        exact mul_le_mul_of_nonneg_left hcPG (by norm_num)
    _ = _ := by ring

end HRS.MS.MfeConf
