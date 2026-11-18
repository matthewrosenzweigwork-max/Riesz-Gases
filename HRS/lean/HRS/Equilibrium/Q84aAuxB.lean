/-
# HRS.Equilibrium.Q84aAuxB — packet Q84a helpers (pair bounds, algebra)
-/
import HRS.Equilibrium.Q84aAuxA

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.Q84a

variable {d : ℕ} {s : ℝ}

/-! ### Real-variable inequalities -/

theorem q84a_rpow_split {r : ℝ} (hr : 0 < r) (s : ℝ) : r ^ (1 - s) = r * r ^ (-s) := by
  rw [show (1 - s) = 1 + (-s) by ring, Real.rpow_add hr, Real.rpow_one]

theorem q84a_one_add_le {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hs : 1 ≤ s) :
    1 + r ^ (1 - s) ≤ 2 * (r * r ^ (-s)) := by
  have h1 : 1 ≤ r ^ (1 - s) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by linarith)
  rw [q84a_rpow_split hr] at h1 ⊢
  linarith

theorem q84a_rpow_mul {r : ℝ} (hr : 0 < r) (s : ℝ) : r ^ (-s - 1) * r = r ^ (-s) := by
  rw [Real.rpow_sub_one hr.ne']
  field_simp

theorem q84a_GD {D dd : ℝ} (hs : 0 < s) (hD : 0 < D) (hDd : D ≤ dd) :
    D ^ (-s) + D ≤ (1 + dd) * (1 + (min 1 D) ^ (-s)) := by
  have hdd : 0 ≤ dd := hD.le.trans hDd
  have hp : 0 ≤ (min 1 D) ^ (-s) := Real.rpow_nonneg (le_min zero_le_one hD.le) _
  have hq : 0 ≤ D ^ (-s) := Real.rpow_nonneg hD.le _
  rcases le_or_gt D 1 with h | h
  · rw [min_eq_right h]
    nlinarith [mul_nonneg hdd hq]
  · have h1 : D ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h.le (by linarith)
    nlinarith [mul_nonneg hdd hp]

theorem q84a_min_le {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ 2 * y) : min 1 x ≤ 2 * min 1 y := by
  rcases le_or_gt 1 y with h1 | h1
  · rw [min_eq_left h1]; exact (min_le_left _ _).trans (by norm_num)
  · rw [min_eq_right h1.le]; exact (min_le_right _ _).trans h

/-! ### Gradients -/

theorem q84a_gradSnd_eq {ψ : Torus d → Torus d → ℝ} (hψ : IsSymmPair ψ) (x y : Torus d) :
    gradSnd ψ x y = gradFst ψ y x := by
  unfold gradSnd gradFst
  have : (fun z => ψ x z) = fun z => ψ z x := funext fun z => hψ x z
  rw [this]

theorem q84a_grad_le_w {ψ : Torus d → Torus d → ℝ} {K : ℝ} (hs1 : 1 ≤ s) (hψ : PsiSize s K ψ)
    {a c : Torus d} (hac : a ≠ c) : ‖gradFst ψ a c‖ ≤ K * wEnv s a c := by
  have hK : 0 ≤ K := q84a_K_nonneg hψ hac
  refine (q84a_grad_norm hψ hac).trans (mul_le_mul_of_nonneg_left ?_ hK)
  have hr := PairCorrAux.rTrunc_pos hac
  have hr1 := PairCorrAux.rTrunc_le_one a c
  rw [q84a_rpow_split hr]
  unfold wEnv
  have : 0 ≤ rTrunc a c ^ (-s) := Real.rpow_nonneg hr.le _
  nlinarith

theorem q84a_force_term {ψ : Torus d → Torus d → ℝ} {K M : ℝ} (hs1 : 1 ≤ s) (hψ : PsiSize s K ψ)
    {F : Euc d} (hF : ‖F‖ ≤ M) {a c : Torus d} (hac : a ≠ c) :
    |inner ℝ F (gradFst ψ a c)| ≤ M * K * wEnv s a c := by
  have hK : 0 ≤ K := q84a_K_nonneg hψ hac
  have hM : 0 ≤ M := (norm_nonneg _).trans hF
  refine (abs_real_inner_le_norm _ _).trans ?_
  have h1 := q84a_grad_le_w hs1 hψ hac
  calc ‖F‖ * ‖gradFst ψ a c‖ ≤ M * (K * wEnv s a c) :=
        mul_le_mul hF h1 (norm_nonneg _) hM
    _ = M * K * wEnv s a c := by ring

/-- The bound for `∇g`: `‖∇g(z)‖ ≤ Cg (|z|^{-s-1} + 1)` in terms of `eucDist`. -/
theorem q84a_gg_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ z : Torus d, z ≠ 0 →
      ‖periodicRieszGrad d s z‖ ≤ Cg * (Torus.eucDist z 0 ^ (-s - 1) + 1) := by
  obtain ⟨C, hC⟩ := HRS.KernelGrad.periodicRieszGrad_bound_tdist_aux hd hs0 hsd
  refine ⟨|C|, abs_nonneg _, fun z hz => ?_⟩
  obtain ⟨w, hw, hw'⟩ := q84a_exists_centered z
  have h1 : HRS.KernelGrad.tdist z 0 = Torus.eucDist z 0 := by
    rw [← hw, HRS.KernelGrad.tdist_mk hw', PairCorrAux.eucDist_mk_zero' hw']
  have := hC z hz
  rw [h1] at this
  refine this.trans ?_
  exact mul_le_mul_of_nonneg_right (le_abs_self C)
    (add_nonneg (Real.rpow_nonneg (PairCorrAux.eucDist_nonneg' _ _) _) zero_le_one)

/-! ### Pair bound -/

theorem q84a_Gb_bound {Cg : ℝ} (hCg0 : 0 ≤ Cg) (hs : 0 < s)
    (hCg : ∀ z : Torus d, z ≠ 0 → ‖periodicRieszGrad d s z‖ ≤
      Cg * (Torus.eucDist z 0 ^ (-s - 1) + 1))
    {a b : Torus d} (hab : a ≠ b) :
    ‖periodicRieszGrad d s (a - b)‖ ≤ 2 * Cg * rTrunc a b ^ (-s - 1) := by
  have hGb : ‖periodicRieszGrad d s (a - b)‖ ≤ Cg * (Torus.eucDist a b ^ (-s - 1) + 1) := by
    have := hCg (a - b) (sub_ne_zero.2 hab)
    rwa [← PairCorrAux.eucDist_sub_zero] at this
  have hrab_pos := PairCorrAux.rTrunc_pos hab
  have hrab1 := PairCorrAux.rTrunc_le_one a b
  have hrabD := PairCorrAux.rTrunc_le_dist a b
  have hG1 : Torus.eucDist a b ^ (-s - 1) ≤ rTrunc a b ^ (-s - 1) :=
    Real.rpow_le_rpow_of_nonpos hrab_pos hrabD (by linarith)
  have hG2 : 1 ≤ rTrunc a b ^ (-s - 1) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hrab_pos hrab1 (by linarith)
  refine hGb.trans ?_
  have : Cg * (Torus.eucDist a b ^ (-s - 1) + 1) ≤ Cg * (2 * rTrunc a b ^ (-s - 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) hCg0
  linarith

theorem q84a_caseNear {ψ : Torus d → Torus d → ℝ} {K : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) {Cg : ℝ}
    (hCg0 : 0 ≤ Cg) (hψ : PsiSize s K ψ) {a b c : Torus d} (hab : a ≠ b) (hac : a ≠ c)
    (h : Torus.eucDist a b ≤ Torus.eucDist a c / 2) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : G ≤ Cg * (Torus.eucDist a b ^ (-s - 1) + 1)) :
    G * ‖gradFst ψ a c - gradFst ψ b c‖ ≤
      Cg * (1 + d) * 2 ^ s * K * (wEnv s a b * wEnv s a c) := by
  have hK : 0 ≤ K := q84a_K_nonneg hψ hac
  have hDpos : 0 < Torus.eucDist a b :=
    lt_of_le_of_ne (PairCorrAux.eucDist_nonneg' a b)
      (fun h0 => hab ((PairCorrAux.eucDist_eq_zero' a b).1 h0.symm))
  have hΔ := q84a_grad_diff hψ hs hac h
  have h2s : 1 ≤ (2 : ℝ) ^ s := Real.one_le_rpow (by norm_num) hs.le
  have hprac : 0 ≤ rTrunc a c ^ (-s) := Real.rpow_nonneg (PairCorrAux.rTrunc_nonneg a c) _
  have hwac0 : 0 ≤ wEnv s a c := zero_le_one.trans (PairCorrAux.one_le_wEnv s a c)
  have hΔ' : ‖gradFst ψ a c - gradFst ψ b c‖ ≤
      K * 2 ^ s * wEnv s a c * Torus.eucDist a b := by
    refine hΔ.trans ?_
    have : K * (1 + 2 ^ s * rTrunc a c ^ (-s)) ≤ K * 2 ^ s * wEnv s a c := by
      unfold wEnv
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hK
      nlinarith
    exact mul_le_mul_of_nonneg_right this hDpos.le
  have hGD : G * Torus.eucDist a b ≤ Cg * (1 + d) * wEnv s a b := by
    have h1 : G * Torus.eucDist a b ≤
        Cg * (Torus.eucDist a b ^ (-s - 1) + 1) * Torus.eucDist a b :=
      mul_le_mul_of_nonneg_right hG hDpos.le
    have h2 : Cg * (Torus.eucDist a b ^ (-s - 1) + 1) * Torus.eucDist a b =
        Cg * (Torus.eucDist a b ^ (-s) + Torus.eucDist a b) := by
      rw [mul_assoc, add_mul, q84a_rpow_mul hDpos, one_mul]
    have h3 := q84a_GD (s := s) (dd := (d : ℝ)) hs hDpos (q84a_eucDist_le hd1 a b)
    have h4 : Torus.eucDist a b ^ (-s) + Torus.eucDist a b ≤ (1 + d) * wEnv s a b := by
      unfold wEnv rTrunc
      exact h3
    calc G * Torus.eucDist a b
        ≤ Cg * (Torus.eucDist a b ^ (-s - 1) + 1) * Torus.eucDist a b := h1
      _ = Cg * (Torus.eucDist a b ^ (-s) + Torus.eucDist a b) := h2
      _ ≤ Cg * ((1 + d) * wEnv s a b) := mul_le_mul_of_nonneg_left h4 hCg0
      _ = Cg * (1 + d) * wEnv s a b := by ring
  calc G * ‖gradFst ψ a c - gradFst ψ b c‖
      ≤ G * (K * 2 ^ s * wEnv s a c * Torus.eucDist a b) := mul_le_mul_of_nonneg_left hΔ' hG0
    _ = (G * Torus.eucDist a b) * (K * 2 ^ s * wEnv s a c) := by ring
    _ ≤ (Cg * (1 + d) * wEnv s a b) * (K * 2 ^ s * wEnv s a c) :=
        mul_le_mul_of_nonneg_right hGD
          (mul_nonneg (mul_nonneg hK (by positivity)) hwac0)
    _ = Cg * (1 + d) * 2 ^ s * K * (wEnv s a b * wEnv s a c) := by ring

theorem q84a_Pq_bound {ψ : Torus d → Torus d → ℝ} {K : ℝ} (hd : 2 ≤ d) (hs1 : 1 ≤ s)
    {Cg : ℝ} (hCg0 : 0 ≤ Cg)
    (hCg : ∀ z : Torus d, z ≠ 0 → ‖periodicRieszGrad d s z‖ ≤
      Cg * (Torus.eucDist z 0 ^ (-s - 1) + 1))
    (hψ : PsiSize s K ψ) {a b c : Torus d} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    |inner ℝ (periodicRieszGrad d s (a - b)) (gradFst ψ a c - gradFst ψ b c)| ≤
      8 * Cg * (1 + d) * 2 ^ s * K *
        (wEnv s a b * wEnv s a c + wEnv s a b * wEnv s b c) := by
  have hs : 0 < s := by linarith
  have hK : 0 ≤ K := q84a_K_nonneg hψ hac
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hDpos : 0 < Torus.eucDist a b :=
    lt_of_le_of_ne (PairCorrAux.eucDist_nonneg' a b)
      (fun h0 => hab ((PairCorrAux.eucDist_eq_zero' a b).1 h0.symm))
  have hGb : ‖periodicRieszGrad d s (a - b)‖ ≤ Cg * (Torus.eucDist a b ^ (-s - 1) + 1) := by
    have := hCg (a - b) (sub_ne_zero.2 hab)
    rwa [← PairCorrAux.eucDist_sub_zero] at this
  have hinner := abs_real_inner_le_norm (periodicRieszGrad d s (a - b))
    (gradFst ψ a c - gradFst ψ b c)
  have hwab := PairCorrAux.one_le_wEnv s a b
  have hwac := PairCorrAux.one_le_wEnv s a c
  have hwbc := PairCorrAux.one_le_wEnv s b c
  have hwab0 : 0 < wEnv s a b := by linarith
  have hwac0 : 0 < wEnv s a c := by linarith
  have hwbc0 : 0 < wEnv s b c := by linarith
  have h2s : 1 ≤ (2 : ℝ) ^ s := Real.one_le_rpow (by norm_num) hs.le
  have hcoef : 1 ≤ (1 + (d : ℝ)) * 2 ^ s := by nlinarith
  have hP : 0 ≤ Cg * (1 + (d : ℝ)) * 2 ^ s * K :=
    mul_nonneg (mul_nonneg (mul_nonneg hCg0 (by linarith)) (by positivity)) hK
  have hab_ac : 0 ≤ wEnv s a b * wEnv s a c := by positivity
  have hab_bc : 0 ≤ wEnv s a b * wEnv s b c := by positivity
  by_cases h1 : Torus.eucDist a b ≤ Torus.eucDist a c / 2
  · have := q84a_caseNear hd1 hs hCg0 hψ hab hac h1 (norm_nonneg _) hGb
    calc |inner ℝ (periodicRieszGrad d s (a - b)) (gradFst ψ a c - gradFst ψ b c)|
        ≤ _ := hinner
      _ ≤ Cg * (1 + d) * 2 ^ s * K * (wEnv s a b * wEnv s a c) := this
      _ ≤ _ := by
        have := mul_nonneg hP hab_bc
        have := mul_nonneg hP hab_ac
        nlinarith
  by_cases h2 : Torus.eucDist a b ≤ Torus.eucDist b c / 2
  · have h2' : Torus.eucDist b a ≤ Torus.eucDist b c / 2 := by
      rw [PairCorrAux.eucDist_symm' b a]; exact h2
    have hGb' : ‖periodicRieszGrad d s (a - b)‖ ≤
        Cg * (Torus.eucDist b a ^ (-s - 1) + 1) := by
      rw [PairCorrAux.eucDist_symm' b a]; exact hGb
    have := q84a_caseNear hd1 hs hCg0 hψ hab.symm hbc h2' (norm_nonneg _) hGb'
    rw [norm_sub_rev, PairCorrAux.wEnv_symm s b a] at this
    calc |inner ℝ (periodicRieszGrad d s (a - b)) (gradFst ψ a c - gradFst ψ b c)|
        ≤ _ := hinner
      _ ≤ Cg * (1 + d) * 2 ^ s * K * (wEnv s a b * wEnv s b c) := this
      _ ≤ _ := by
        have := mul_nonneg hP hab_bc
        have := mul_nonneg hP hab_ac
        nlinarith
  -- far case
  have h1 := not_le.mp h1
  have h2 := not_le.mp h2
  have hrab_pos : 0 < rTrunc a b := PairCorrAux.rTrunc_pos hab
  have hrab1 : rTrunc a b ≤ 1 := PairCorrAux.rTrunc_le_one a b
  have hrac : rTrunc a c ≤ 2 * rTrunc a b := q84a_min_le hDpos.le (by linarith)
  have hrbc : rTrunc b c ≤ 2 * rTrunc a b := q84a_min_le hDpos.le (by linarith)
  have hGb2 : ‖periodicRieszGrad d s (a - b)‖ ≤ 2 * Cg * rTrunc a b ^ (-s - 1) :=
    q84a_Gb_bound hCg0 hs hCg hab
  -- bounds on the gradients of psi
  have hgrad : ∀ {u v : Torus d}, u ≠ v → rTrunc u v ≤ 2 * rTrunc a b →
      ‖gradFst ψ u v‖ ≤ 4 * K * rTrunc a b * wEnv s u v := by
    intro u v huv hr
    have hrp := PairCorrAux.rTrunc_pos huv
    have hr1 := PairCorrAux.rTrunc_le_one u v
    have hq := q84a_one_add_le hrp hr1 hs1
    have hwu0 : 0 ≤ wEnv s u v := zero_le_one.trans (PairCorrAux.one_le_wEnv s u v)
    have hpow : 0 ≤ rTrunc u v ^ (-s) := Real.rpow_nonneg hrp.le _
    have hw : rTrunc u v * rTrunc u v ^ (-s) ≤ rTrunc u v * wEnv s u v :=
      mul_le_mul_of_nonneg_left (by unfold wEnv; linarith) hrp.le
    have hw2 : rTrunc u v * wEnv s u v ≤ 2 * rTrunc a b * wEnv s u v :=
      mul_le_mul_of_nonneg_right hr hwu0
    calc ‖gradFst ψ u v‖ ≤ K * (1 + rTrunc u v ^ (1 - s)) := q84a_grad_norm hψ huv
      _ ≤ K * (2 * (rTrunc u v * rTrunc u v ^ (-s))) := mul_le_mul_of_nonneg_left hq hK
      _ ≤ K * (2 * (2 * rTrunc a b * wEnv s u v)) :=
          mul_le_mul_of_nonneg_left (by linarith) hK
      _ = 4 * K * rTrunc a b * wEnv s u v := by ring
  have hA := hgrad hac hrac
  have hB := hgrad hbc hrbc
  have hΔ : ‖gradFst ψ a c - gradFst ψ b c‖ ≤
      4 * K * rTrunc a b * (wEnv s a c + wEnv s b c) := by
    refine (norm_sub_le _ _).trans ?_
    linarith
  have hprod : ‖periodicRieszGrad d s (a - b)‖ * ‖gradFst ψ a c - gradFst ψ b c‖ ≤
      (2 * Cg * rTrunc a b ^ (-s - 1)) * (4 * K * rTrunc a b * (wEnv s a c + wEnv s b c)) :=
    mul_le_mul hGb2 hΔ (norm_nonneg _) (by positivity)
  have hreq : (2 * Cg * rTrunc a b ^ (-s - 1)) *
      (4 * K * rTrunc a b * (wEnv s a c + wEnv s b c)) =
      8 * Cg * K * rTrunc a b ^ (-s) * (wEnv s a c + wEnv s b c) := by
    rw [← q84a_rpow_mul hrab_pos s]; ring
  have hrw : rTrunc a b ^ (-s) ≤ wEnv s a b := by
    unfold wEnv; linarith
  have hsum0 : 0 ≤ wEnv s a c + wEnv s b c := by linarith
  have hfinal : 8 * Cg * K * rTrunc a b ^ (-s) * (wEnv s a c + wEnv s b c) ≤
      8 * Cg * K * wEnv s a b * (wEnv s a c + wEnv s b c) := by
    have h8 : 0 ≤ 8 * Cg * K := by positivity
    have := mul_le_mul_of_nonneg_left hrw h8
    have := mul_le_mul_of_nonneg_right this hsum0
    linarith
  have hlast : 8 * Cg * K * wEnv s a b * (wEnv s a c + wEnv s b c) ≤
      8 * Cg * (1 + d) * 2 ^ s * K * (wEnv s a b * wEnv s a c + wEnv s a b * wEnv s b c) := by
    have h8 : 0 ≤ 8 * Cg * K * (wEnv s a b * wEnv s a c + wEnv s a b * wEnv s b c) := by
      positivity
    have := mul_le_mul_of_nonneg_left hcoef h8
    nlinarith
  calc |inner ℝ (periodicRieszGrad d s (a - b)) (gradFst ψ a c - gradFst ψ b c)|
      ≤ _ := hinner
    _ ≤ _ := hprod
    _ = _ := hreq
    _ ≤ _ := hfinal
    _ ≤ _ := hlast

/-! ### Algebra of the triple term -/

theorem q84a_Tsum_eq {ρ : Torus d → ℝ} {ψ : Torus d → Torus d → ℝ} (hsd : s < d)
    (hψ : IsSymmPair ψ) (x y z : Torus d) :
    Tpsi d s ρ ψ x y z + Tpsi d s ρ ψ x z y + Tpsi d s ρ ψ y z x =
      -(inner ℝ (periodicRieszGrad d s (x - z)) (gradFst ψ x y - gradFst ψ z y))
      - inner ℝ (periodicRieszGrad d s (y - z)) (gradFst ψ y x - gradFst ψ z x)
      - inner ℝ (periodicRieszGrad d s (x - y)) (gradFst ψ x z - gradFst ψ y z)
      + (inner ℝ (forceField d s ρ x) (gradFst ψ x y) + inner ℝ (forceField d s ρ y) (gradFst ψ y x)
        + inner ℝ (forceField d s ρ x) (gradFst ψ x z) + inner ℝ (forceField d s ρ z) (gradFst ψ z x)
        + inner ℝ (forceField d s ρ y) (gradFst ψ y z) + inner ℝ (forceField d s ρ z) (gradFst ψ z y)) := by
  have hneg : ∀ a b : Torus d, periodicRieszGrad d s (a - b) = -periodicRieszGrad d s (b - a) := by
    intro a b
    have e : a - b = -(b - a) := by abel
    rw [e, HRS.KernelGrad.periodicRieszGrad_neg_of_lt hsd]
  unfold Tpsi centeredForce
  simp only [q84a_gradSnd_eq hψ, hneg z y, hneg z x, hneg y x]
  simp only [inner_sub_left, inner_sub_right, inner_neg_left]
  ring

end HRS.Q84a
