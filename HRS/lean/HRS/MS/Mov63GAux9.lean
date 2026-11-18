import HRS.MS.Mov63GAux8

/-!
# S6.3, packet N8 (part 9): crude growth of the derivatives of `Q`

Namespace `HRS.MS.Mov63`, prefix `mng_`.  `wfun ρ = ρ^{-1/2} = exp(-½ log ρ)`: `‖D^i w(y)‖ ≤ i! w(y) (L(1+‖y‖))^i` (Faà di Bruno bound
`norm_iteratedFDeriv_comp_le`), `w(y) ≤ C exp((βq/4)‖y‖² + (βM₀/2)‖y‖)` (`mnf_rho_lower`), hence `‖D^i Q_u(y)‖ ≤ C_c e^{K₁‖y‖²}` for every
`K₁ > βq/4` and `‖u‖ ≤ B₀` (`mng_crude`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

/-- `ρ^{-1/2}`. -/
def mngW (ρ : Euc d → ℝ) : Euc d → ℝ := fun y => Real.exp (-(1 / 2) * Real.log (ρ y))

lemma mngW_eq (H : Mov2dTh d s β q ρ) (y : Euc d) : mngW ρ y = (Real.sqrt (ρ y))⁻¹ := by
  have hpos := (mnb_rhoData H).pos y
  unfold mngW
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hpos.le, Real.rpow_def_of_pos hpos]
  congr 1; ring

lemma mng_logrho_cd (H : Mov2dTh d s β q ρ) : ContDiff ℝ ∞ (fun y => Real.log (ρ y)) :=
  (mnc_rho_smooth H).log (fun x => ((mnb_rhoData H).pos x).ne')

lemma mngW_cd (H : Mov2dTh d s β q ρ) : ContDiff ℝ ∞ (mngW ρ) :=
  Real.contDiff_exp.comp (contDiff_const.mul (mng_logrho_cd H))

lemma mng_norm_iter_grad {f : Euc d → ℝ} (k : ℕ) (y : Euc d) :
    ‖iteratedFDeriv ℝ k (fun z => gradient f z) y‖ = ‖iteratedFDeriv ℝ (k + 1) f y‖ := by
  have : (fun z => gradient f z) = ((InnerProductSpace.toDual ℝ (Euc d)).symm : (Euc d →L[ℝ] ℝ) ≃ₗᵢ[ℝ] Euc d) ∘
      (fderiv ℝ f) := rfl
  rw [this, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, norm_iteratedFDeriv_fderiv]

/-- Derivative bounds of `log ρ`. -/
lemma mng_dlog (H : Mov2dTh d s β q ρ) :
    (∀ k : ℕ, ∃ C : ℝ, 1 ≤ k → ∀ y, ‖iteratedFDeriv ℝ (k + 1) (fun z => Real.log (ρ z)) y‖ ≤ C) ∧
      ∃ M : ℝ, ∀ y, ‖iteratedFDeriv ℝ 1 (fun z => Real.log (ρ z)) y‖ ≤ β * q * ‖y‖ + M := by
  obtain ⟨B, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  have hq' : 0 < β * q := mul_pos H.hβ H.hq
  obtain ⟨hdlog, M, hM⟩ := HRS.MS.Mov0.mv0_dlog_bounds hq'.le hR
  refine ⟨fun k => ?_, M, fun y => ?_⟩
  · by_cases hk : 1 ≤ k
    · obtain ⟨C, hC⟩ := hdlog k hk
      exact ⟨C, fun _ y => by rw [← mng_norm_iter_grad]; exact hC y⟩
    · exact ⟨0, fun h => absurd h hk⟩
  · have := hM y
    have h2 : ‖iteratedFDeriv ℝ 1 (fun z => Real.log (ρ z)) y‖ = ‖gradient (fun z => Real.log (ρ z)) y‖ := by
      have := mng_norm_iter_grad (f := fun z => Real.log (ρ z)) 0 y
      rw [norm_iteratedFDeriv_zero] at this
      exact this.symm
    rw [h2]; exact this

lemma mngW_iter (H : Mov2dTh d s β q ρ) (N : ℕ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ i ≤ N, ∀ y, ‖iteratedFDeriv ℝ i (mngW ρ) y‖ ≤
      (i.factorial : ℝ) * mngW ρ y * (L * (1 + ‖y‖)) ^ i := by
  obtain ⟨hC, M, hM⟩ := mng_dlog H
  choose C hC using hC
  set L : ℝ := 1 + (β * q + |M|) / 2 + ∑ k ∈ Finset.range (N + 1), |C k| / 2 with hL
  have hL1 : 1 ≤ L := by
    have : 0 ≤ (β * q + |M|) / 2 := by have := mul_pos H.hβ H.hq; positivity
    have h2 : 0 ≤ ∑ k ∈ Finset.range (N + 1), |C k| / 2 := Finset.sum_nonneg fun _ _ => by positivity
    linarith
  refine ⟨L, hL1, fun i hi y => ?_⟩
  have hlog := mng_logrho_cd H
  have hg : ContDiff ℝ ∞ (fun z => -(1 / 2 : ℝ) * Real.log (ρ z)) := contDiff_const.mul hlog
  have hcomp := norm_iteratedFDeriv_comp_le (g := Real.exp) (f := fun z => -(1 / 2 : ℝ) * Real.log (ρ z))
    (n := i) (N := ∞) Real.contDiff_exp hg (by exact_mod_cast le_top) y
    (C := Real.exp (-(1 / 2 : ℝ) * Real.log (ρ y))) (D := L * (1 + ‖y‖))
    (fun k hk => by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have : iteratedDeriv k Real.exp = Real.exp := by simpa using iteratedDeriv_exp_const_mul k 1
      rw [this, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)])
    (fun k hk1 hki => by
      have hkN : k ≤ N := hki.trans hi
      have hy1 : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
      have e1 : ‖iteratedFDeriv ℝ k (fun z => -(1 / 2 : ℝ) * Real.log (ρ z)) y‖ =
          (1 / 2) * ‖iteratedFDeriv ℝ k (fun z => Real.log (ρ z)) y‖ := by
        have h1 : (fun z => -(1 / 2 : ℝ) * Real.log (ρ z)) = (-(1 / 2 : ℝ)) • (fun z => Real.log (ρ z)) := by
          funext z; simp
        rw [h1, iteratedFDeriv_const_smul_apply (hlog.of_le (by exact_mod_cast le_top)).contDiffAt, norm_smul]
        simp
      rw [e1]
      have hDk : 1 ≤ L * (1 + ‖y‖) := by nlinarith
      refine le_trans ?_ (le_self_pow₀ hDk (by omega : k ≠ 0))
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      by_cases hk0 : k' = 0
      · subst hk0
        have h1 : ‖iteratedFDeriv ℝ (0 + 1) (fun z => Real.log (ρ z)) y‖ ≤ β * q * ‖y‖ + M := hM y
        have hLM : (1 / 2) * (β * q * ‖y‖ + M) ≤ L * (1 + ‖y‖) := by
          have h2 : 0 ≤ ∑ k ∈ Finset.range (N + 1), |C k| / 2 := Finset.sum_nonneg fun _ _ => by positivity
          have hb : 0 < β * q := mul_pos H.hβ H.hq
          have hLq : β * q / 2 ≤ L := by
            have := abs_nonneg M
            linarith
          have hLM0 : M / 2 ≤ L := by
            have := le_abs_self M
            linarith
          nlinarith [mul_le_mul_of_nonneg_right hLq (norm_nonneg y)]
        linarith
      · have hk'1 : 1 ≤ k' := Nat.one_le_iff_ne_zero.2 hk0
        have h1 := hC k' hk'1 y
        have hmem : k' ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
        have h2 : |C k'| / 2 ≤ ∑ k ∈ Finset.range (N + 1), |C k| / 2 :=
          Finset.single_le_sum (f := fun k => |C k| / 2) (fun _ _ => by positivity) hmem
        have hb : 0 < β * q := mul_pos H.hβ H.hq
        have hL' : (1 / 2) * |C k'| ≤ L := by
          have := abs_nonneg M
          linarith [h2]
        have : (1 / 2) * ‖iteratedFDeriv ℝ (k' + 1) (fun z => Real.log (ρ z)) y‖ ≤ (1 / 2) * |C k'| := by
          have := le_trans h1 (le_abs_self _)
          linarith
        have h3 : L ≤ L * (1 + ‖y‖) := by nlinarith [norm_nonneg y]
        linarith)
  have e : (Real.exp ∘ fun z => -(1 / 2 : ℝ) * Real.log (ρ z)) = mngW ρ := rfl
  rw [e] at hcomp
  unfold mngW at hcomp ⊢
  calc _ ≤ _ := hcomp
    _ = _ := by ring
section Crude

variable (H : Mov2dTh d s β q ρ)

include H in
lemma mng_w_upper {M0 : ℝ} (hM0 : ∀ x, ‖movForce d s ρ x‖ ≤ M0) (y : Euc d) :
    mngW ρ y ≤ (Real.sqrt (ρ 0))⁻¹ * Real.exp ((β * q / 4) * ‖y‖ ^ 2 + (β * M0 / 2) * ‖y‖) := by
  have hpos := (mnb_rhoData H).pos
  have hlow := mnf_rho_lower H hM0 y
  rw [mngW_eq H y]
  have hs0 : 0 < Real.sqrt (ρ 0) := Real.sqrt_pos.2 (hpos 0)
  have hsy : 0 < Real.sqrt (ρ y) := Real.sqrt_pos.2 (hpos y)
  set E : ℝ := (β * q / 4) * ‖y‖ ^ 2 + (β * M0 / 2) * ‖y‖ with hE
  have h1 : Real.sqrt (ρ 0) * Real.exp (-E) ≤ Real.sqrt (ρ y) := by
    have h2 : Real.sqrt (ρ 0 * Real.exp (-(β * q / 2) * ‖y‖ ^ 2 - β * M0 * ‖y‖)) ≤ Real.sqrt (ρ y) :=
      Real.sqrt_le_sqrt hlow
    rw [Real.sqrt_mul (hpos 0).le] at h2
    have h3 : Real.sqrt (Real.exp (-(β * q / 2) * ‖y‖ ^ 2 - β * M0 * ‖y‖)) = Real.exp (-E) := by
      rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
      congr 1; rw [hE]; ring
    rwa [h3] at h2
  have h4 : (Real.sqrt (ρ y))⁻¹ ≤ (Real.sqrt (ρ 0) * Real.exp (-E))⁻¹ :=
    inv_anti₀ (by positivity) h1
  refine h4.trans (le_of_eq ?_)
  rw [mul_inv, ← Real.exp_neg, neg_neg]

lemma mng_poly_exp (L b η : ℝ) (hL : 0 ≤ L) (hb : 0 ≤ b) (hη : 0 < η) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → (L * (1 + r)) ^ n * Real.exp (b * r) ≤ C * Real.exp (η * r ^ 2) := by
  refine ⟨n.factorial * Real.exp (L + (L + b) ^ 2 / (4 * η)), by positivity, fun r hr => ?_⟩
  have hx : 0 ≤ L * (1 + r) := by positivity
  have h1 : (L * (1 + r)) ^ n ≤ n.factorial * Real.exp (L * (1 + r)) := by
    have := Real.pow_div_factorial_le_exp (L * (1 + r)) hx n
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have h2 : (L + b) * r ≤ η * r ^ 2 + (L + b) ^ 2 / (4 * η) := by
    have : 0 ≤ (η * r - (L + b) / 2) ^ 2 / η := by positivity
    have e : (η * r - (L + b) / 2) ^ 2 / η = η * r ^ 2 - (L + b) * r + (L + b) ^ 2 / (4 * η) := by
      field_simp; ring
    linarith
  calc (L * (1 + r)) ^ n * Real.exp (b * r) ≤ (n.factorial * Real.exp (L * (1 + r))) * Real.exp (b * r) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = n.factorial * Real.exp (L + (L + b) * r) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ n.factorial * Real.exp (L + (L + b) ^ 2 / (4 * η) + η * r ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

end Crude

section Crude2

variable (H : Mov2dTh d s β q ρ) {m : ℕ}

include H in
/-- **Crude growth** of the derivatives of `Q_u = 1 + V_u/√ρ`. -/
lemma mng_crude (hm : (d : ℝ) / 2 + 3 < m) {N : ℕ} (hN : (d : ℝ) / 2 + N + 2 < m) {K1 : ℝ} (hK1 : β * q / 4 < K1)
    (B0 : ℝ) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ u : OscSpace d (m : ℝ), ‖u‖ ≤ B0 → ∀ i, 1 ≤ i → i ≤ N + 1 → ∀ y : Euc d,
      ‖iteratedFDeriv ℝ i (mneQ ρ hm u) y‖ ≤ Cc * Real.exp (K1 * ‖y‖ ^ 2) := by
  obtain ⟨M0, hM00, hM0⟩ := mnf_M0 hm H
  obtain ⟨L, hL1, hLw⟩ := mngW_iter H (N + 1)
  obtain ⟨CV, hCV0, hCV⟩ := mn_force_bound H.hd H.hs0 H.hsd β q H.hβ H.hq ρ H.hρ N m hN
  have hη : 0 < K1 - β * q / 4 := by linarith
  have hb : 0 ≤ β * M0 / 2 := by have := H.hβ; positivity
  obtain ⟨Cp, hCp0, hCp⟩ := mng_poly_exp L (β * M0 / 2) (K1 - β * q / 4) (by linarith) hb hη (N + 1)
  have hs0 : 0 < Real.sqrt (ρ 0) := Real.sqrt_pos.2 ((mnb_rhoData H).pos 0)
  set B1 : ℝ := max B0 0 with hB1
  have hB10 : 0 ≤ B1 := le_max_right _ _
  set A : ℝ := 2 ^ (N + 1) * ((N + 1).factorial : ℝ) with hA
  refine ⟨A * CV * B1 * (Real.sqrt (ρ 0))⁻¹ * Cp, by positivity, fun u hu i hi1 hiN y => ?_⟩
  have hu1 : ‖u‖ ≤ B1 := hu.trans (le_max_left _ _)
  -- the function
  have hQ : mneQ ρ hm u = fun z => 1 + mngW ρ z * mneV hm u z := by
    funext z
    rw [mnf_Q_eq hm H u z, mngW_eq H z, div_eq_inv_mul]
  obtain ⟨hVcd, hVb, -⟩ := hCV (mneV hm u) (mneV_cd hm u).continuous (mneV_memOsc hm u)
  rw [mneV_norm hm u] at hVb
  have hwcd : ContDiff ℝ i (mngW ρ) := (mngW_cd H).of_le (by exact_mod_cast le_top)
  have hVcd' : ContDiff ℝ i (mneV hm u) := hVcd.of_le (by exact_mod_cast (by omega : i ≤ N + 2))
  have hprod : ContDiff ℝ i (fun z => mngW ρ z * mneV hm u z) := hwcd.mul hVcd'
  have e1 : iteratedFDeriv ℝ i (mneQ ρ hm u) y = iteratedFDeriv ℝ i (fun z => mngW ρ z * mneV hm u z) y := by
    rw [hQ]
    have : (fun z => 1 + mngW ρ z * mneV hm u z) = (fun _ : Euc d => (1 : ℝ)) + (fun z => mngW ρ z * mneV hm u z) := by
      funext z; simp
    rw [this, iteratedFDeriv_add_apply contDiffAt_const hprod.contDiffAt, iteratedFDeriv_const_of_ne (by omega),
      Pi.zero_apply, zero_add]
  rw [e1]
  refine (norm_iteratedFDeriv_mul_le hwcd hVcd' y (le_refl _)).trans ?_
  set r : ℝ := ‖y‖ with hr
  have hL0 : 0 < L := by linarith
  have hw0 : 0 ≤ mngW ρ y := (Real.exp_pos _).le
  have hD1 : 1 ≤ L * (1 + r) := by nlinarith [norm_nonneg y]
  have hterm : ∀ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l (mngW ρ) y‖ *
      ‖iteratedFDeriv ℝ (i - l) (mneV hm u) y‖ ≤ (i.choose l : ℝ) * (((N + 1).factorial : ℝ) * mngW ρ y *
        (L * (1 + r)) ^ (N + 1)) * (CV * B1) := by
    intro l hl
    have hl' : l ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    have h1 := hLw l (by omega) y
    have h2 : (l.factorial : ℝ) * mngW ρ y * (L * (1 + r)) ^ l ≤
        ((N + 1).factorial : ℝ) * mngW ρ y * (L * (1 + r)) ^ (N + 1) := by
      have hf : (l.factorial : ℝ) ≤ ((N + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_le (by omega)
      have hp : (L * (1 + r)) ^ l ≤ (L * (1 + r)) ^ (N + 1) := pow_le_pow_right₀ hD1 (by omega)
      calc (l.factorial : ℝ) * mngW ρ y * (L * (1 + r)) ^ l
          ≤ ((N + 1).factorial : ℝ) * mngW ρ y * (L * (1 + r)) ^ l := by
            apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hf hw0) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
    have h3 : ‖iteratedFDeriv ℝ (i - l) (mneV hm u) y‖ ≤ CV * B1 :=
      (hVb (i - l) (by omega) y).trans (mul_le_mul_of_nonneg_left hu1 hCV0)
    have hch : (0 : ℝ) ≤ (i.choose l : ℝ) := Nat.cast_nonneg _
    have h4 : ‖iteratedFDeriv ℝ l (mngW ρ) y‖ ≤ ((N + 1).factorial : ℝ) * mngW ρ y * (L * (1 + r)) ^ (N + 1) :=
      h1.trans h2
    exact mul_le_mul (mul_le_mul_of_nonneg_left h4 hch) h3 (norm_nonneg _)
      (mul_nonneg hch (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hw0) (pow_nonneg (by positivity) _)))
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hsum : ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) = 2 ^ i := by
    exact_mod_cast Nat.sum_range_choose i
  have h2i : (2 : ℝ) ^ i ≤ 2 ^ (N + 1) := pow_le_pow_right₀ (by norm_num) hiN
  rw [hsum]
  have hwup := mng_w_upper H hM0 y
  have hpe := hCp r (norm_nonneg y)
  have hfinal : mngW ρ y * (L * (1 + r)) ^ (N + 1) ≤ (Real.sqrt (ρ 0))⁻¹ * Cp * Real.exp (K1 * r ^ 2) := by
    calc mngW ρ y * (L * (1 + r)) ^ (N + 1)
        ≤ ((Real.sqrt (ρ 0))⁻¹ * Real.exp ((β * q / 4) * r ^ 2 + (β * M0 / 2) * r)) * (L * (1 + r)) ^ (N + 1) :=
          mul_le_mul_of_nonneg_right hwup (by positivity)
      _ = (Real.sqrt (ρ 0))⁻¹ * ((L * (1 + r)) ^ (N + 1) * Real.exp ((β * M0 / 2) * r)) * Real.exp ((β * q / 4) * r ^ 2) := by
          rw [Real.exp_add]; ring
      _ ≤ (Real.sqrt (ρ 0))⁻¹ * (Cp * Real.exp ((K1 - β * q / 4) * r ^ 2)) * Real.exp ((β * q / 4) * r ^ 2) := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpe (by positivity)) (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc, mul_assoc, mul_assoc, ← Real.exp_add]; congr 2; ring_nf
  have hCVB : 0 ≤ CV * B1 := by positivity
  calc (2 : ℝ) ^ i * (((N + 1).factorial : ℝ) * mngW ρ y * (L * (1 + r)) ^ (N + 1)) * (CV * B1)
      = (2 : ℝ) ^ i * ((N + 1).factorial : ℝ) * (mngW ρ y * (L * (1 + r)) ^ (N + 1)) * (CV * B1) := by ring
    _ ≤ A * (mngW ρ y * (L * (1 + r)) ^ (N + 1)) * (CV * B1) := by
        apply mul_le_mul_of_nonneg_right _ hCVB
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [hA]
        exact mul_le_mul_of_nonneg_right h2i (by positivity)
    _ ≤ A * ((Real.sqrt (ρ 0))⁻¹ * Cp * Real.exp (K1 * r ^ 2)) * (CV * B1) := by
        apply mul_le_mul_of_nonneg_right _ hCVB
        exact mul_le_mul_of_nonneg_left hfinal (by positivity)
    _ = _ := by ring

end Crude2


end HRS.MS.Mov63

end
