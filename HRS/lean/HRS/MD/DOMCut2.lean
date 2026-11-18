/-
# HRS.MD.DOMCut2 — packet DOM-CUT (part 2): the configuration cut-off `χ_ε = ∏_{i<j} th(sT(x_i - x_j)/ε)`

`chi ε X`, the shell predicate `Near ε X`, `chi = 1` away from the shell, `chi = 0` close to a collision, the
covering-space smoothness, and the gradient/Laplacian bounds in each particle by powers of the master weight.
-/
import HRS.MD.DOMCut
import HRS.MD.DOMEnv

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.MD.DOMProof

open HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

/-- The pair cut-off `χ_ε(X) = ∏_{i<j} th(sT(x_i - x_j)/ε)`. -/
def chi (ε : ℝ) (X : Config d N) : ℝ := ∏ p ∈ pairsN N, th (ε⁻¹ * sT (X p.1 - X p.2))

/-- Some pair is in the shell or closer: `sT(x_a - x_b) ≤ 2ε`. -/
def Near (ε : ℝ) (X : Config d N) : Prop := ∃ a b : Fin N, a ≠ b ∧ sT (X a - X b) ≤ 2 * ε

theorem domp_mem_pairsN {p : Fin N × Fin N} (hp : p ∈ pairsN N) : p.1 < p.2 := by
  simpa [pairsN] using hp

theorem domp_sT_ordPair (X : Config d N) (a b : Fin N) :
    sT (X (ordPair a b).1 - X (ordPair a b).2) = sT (X a - X b) := by
  unfold ordPair
  split_ifs
  · rfl
  · rw [← neg_sub, domp_sT_neg]

theorem domp_chi_nonneg (ε : ℝ) (X : Config d N) : 0 ≤ chi ε X :=
  Finset.prod_nonneg fun p _ => domp_th_nonneg _

theorem domp_chi_le_one (ε : ℝ) (X : Config d N) : chi ε X ≤ 1 :=
  Finset.prod_le_one₀ (fun p _ => domp_th_nonneg _) fun p _ => domp_th_le_one _

theorem domp_chi_eq_zero {ε : ℝ} (hε : 0 < ε) {X : Config d N} {a b : Fin N} (hab : a ≠ b)
    (h : sT (X a - X b) ≤ ε) : chi ε X = 0 := by
  unfold chi
  refine Finset.prod_eq_zero (ordPair_mem hab) (domp_th_zero ?_)
  rw [domp_sT_ordPair, inv_mul_le_iff₀ hε]
  linarith

theorem domp_chi_eq_one {ε : ℝ} (hε : 0 < ε) {X : Config d N} (h : ¬ Near ε X) : chi ε X = 1 := by
  unfold chi
  refine Finset.prod_eq_one fun p hp => domp_th_one ?_
  have hlt : 2 * ε < sT (X p.1 - X p.2) := by
    by_contra hcon
    exact h ⟨p.1, p.2, (domp_mem_pairsN hp).ne, not_lt.1 hcon⟩
  rw [le_inv_mul_iff₀ hε]
  linarith

/-! ### Periodic lift -/

theorem domp_chi_lift (ε : ℝ) (Y : Fin N → Euc d) :
    chi ε (fun i => Torus.mk (Y i)) = ∏ p ∈ pairsN N, Th ε (Y p.1 - Y p.2) := by
  unfold chi Th
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← Q84a.q84a_mk_sub, domp_sT_mk]

theorem domp_contDiff_chi_lift (ε : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y : Fin N → Euc d => ∏ p ∈ pairsN N, Th ε (Y p.1 - Y p.2)) := by
  refine contDiff_prod fun p _ => (domp_Th_smooth ε).comp ?_
  exact (contDiff_apply ℝ (Euc d) p.1).sub (contDiff_apply ℝ (Euc d) p.2)

/-- `χ̃` vanishes near a configuration with a close pair. -/
theorem domp_chi_lift_eventually_zero {ε : ℝ} (hε : 0 < ε) {Y : Fin N → Euc d} {a b : Fin N}
    (hab : a ≠ b) (h : sE (Y a - Y b) < ε) :
    ∀ᶠ Z in 𝓝 Y, ∏ p ∈ pairsN N, Th ε (Z p.1 - Z p.2) = 0 := by
  have hc : Continuous (fun Z : Fin N → Euc d => sE (Z a - Z b)) :=
    domp_contDiff_sE.continuous.comp ((continuous_apply a).sub (continuous_apply b))
  filter_upwards [hc.continuousAt.eventually (gt_mem_nhds h)] with Z hZ
  have := domp_chi_eq_zero hε (X := fun i => Torus.mk (Z i)) hab (by
    rw [← Q84a.q84a_mk_sub, domp_sT_mk]; exact hZ.le)
  rwa [domp_chi_lift] at this

/-! ### Geometry of the shell -/

theorem domp_one_sub_cos_ge {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    8 * t ^ 2 ≤ 1 - Real.cos (2 * Real.pi * t) := by
  have hπ := Real.pi_pos
  have hs : 2 * t ≤ Real.sin (Real.pi * t) := by
    have := Real.mul_le_sin (x := Real.pi * t) (by positivity) (by nlinarith)
    have e : 2 / Real.pi * (Real.pi * t) = 2 * t := by field_simp
    linarith
  have hc : Real.cos (2 * Real.pi * t) = 1 - 2 * Real.sin (Real.pi * t) ^ 2 := by
    have := Real.cos_two_mul (Real.pi * t)
    have h2 := Real.sin_sq_add_cos_sq (Real.pi * t)
    rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring, this]
    nlinarith
  rw [hc]
  nlinarith [mul_self_le_mul_self (by positivity : 0 ≤ 2 * t) hs]

theorem domp_sT_lower (x y : Torus d) : 8 * Torus.eucDist x y ^ 2 ≤ sT (x - y) := by
  unfold sT Torus.eucDist
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hn : ‖(x - y) k‖ ≤ 1 / 2 := by
    have := AddCircle.norm_le_half_period (x := (x - y) k) (p := (1 : ℝ)) one_ne_zero
    simpa using this
  have := domp_one_sub_cos_ge (norm_nonneg ((x - y) k)) hn
  simpa using this

theorem domp_inv_rTrunc_le_w (hs1 : 1 ≤ s) {x y : Torus d} (hxy : x ≠ y) :
    (rTrunc x y)⁻¹ ≤ wEnv s x y := by
  have hr := PairCorrAux.rTrunc_pos hxy
  have hr1 := PairCorrAux.rTrunc_le_one x y
  have := Real.rpow_le_rpow_of_exponent_ge hr hr1 (show -s ≤ -1 by linarith)
  rw [Real.rpow_neg_one] at this
  unfold wEnv
  linarith

/-- On the shell, `1/sT ≤ w²/8`. -/
theorem domp_inv_sT_le (hs1 : 1 ≤ s) {x y : Torus d} (hxy : x ≠ y) :
    (sT (x - y))⁻¹ ≤ wEnv s x y ^ 2 / 8 := by
  have hr := PairCorrAux.rTrunc_pos hxy
  have hrle : rTrunc x y ≤ Torus.eucDist x y := min_le_right _ _
  have h1 : 8 * rTrunc x y ^ 2 ≤ sT (x - y) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hrle 2) (by norm_num)).trans (domp_sT_lower x y)
  have h2 := domp_inv_rTrunc_le_w hs1 hxy
  have hw : (rTrunc x y)⁻¹ ^ 2 ≤ wEnv s x y ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hr.le) h2 2
  calc (sT (x - y))⁻¹ ≤ (8 * rTrunc x y ^ 2)⁻¹ := inv_anti₀ (by positivity) h1
    _ = (rTrunc x y)⁻¹ ^ 2 / 8 := by field_simp
    _ ≤ wEnv s x y ^ 2 / 8 := by linarith

/-! ### One pair as a function of the displacement of particle `i` -/

theorem domp_sT_add_mk (x y : Torus d) (u : Euc d) :
    sT (x + Torus.mk u - y) = sE (Torus.rep x - Torus.rep y + u) := by
  rw [← domp_sT_mk]
  congr 1
  rw [Q84a.q84a_mk_add, Q84a.q84a_mk_sub, Torus.mk_rep, Torus.mk_rep]
  abel

theorem domp_sT_rep (x y : Torus d) : sT (x - y) = sE (Torus.rep x - Torus.rep y) := by
  rw [← domp_sT_mk, Q84a.q84a_mk_sub, Torus.mk_rep, Torus.mk_rep]

theorem domp_pair_cases (ε : ℝ) (X : Config d N) (i : Fin N) {p : Fin N × Fin N}
    (hp : p ∈ pairsN N) :
    (∀ u : Euc d, th (ε⁻¹ * sT (Function.update X i (X i + Torus.mk u) p.1 -
        Function.update X i (X i + Torus.mk u) p.2)) = th (ε⁻¹ * sT (X p.1 - X p.2))) ∨
    ∃ a : Euc d, sE a = sT (X p.1 - X p.2) ∧ ∀ u : Euc d,
      th (ε⁻¹ * sT (Function.update X i (X i + Torus.mk u) p.1 -
        Function.update X i (X i + Torus.mk u) p.2)) = Th ε (a + u) := by
  have hlt := domp_mem_pairsN hp
  by_cases h1 : p.1 = i
  · right
    have h2 : p.2 ≠ i := fun h => absurd (h1.trans h.symm) hlt.ne
    refine ⟨Torus.rep (X i) - Torus.rep (X p.2), ?_, fun u => ?_⟩
    · rw [← domp_sT_rep, h1]
    · rw [Function.update_of_ne h2, h1, Function.update_self, domp_sT_add_mk]
      rfl
  · by_cases h2 : p.2 = i
    · right
      refine ⟨Torus.rep (X i) - Torus.rep (X p.1), ?_, fun u => ?_⟩
      · rw [← domp_sT_rep, h2, ← neg_sub, domp_sT_neg]
      · rw [Function.update_of_ne h1, h2, Function.update_self, ← neg_sub, domp_sT_neg,
          domp_sT_add_mk]
        rfl
    · left
      intro u
      rw [Function.update_of_ne h1, Function.update_of_ne h2]

/-- Bounds for one pair factor. -/
theorem domp_pair_bound (hs1 : 1 ≤ s) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (ε : ℝ), 0 < ε → ∀ (X : Config d N), X ∉ collisionSet d N →
      ∀ (i : Fin N) (p : Fin N × Fin N), p ∈ pairsN N →
      let G : Euc d → ℝ := fun u => th (ε⁻¹ * sT (Function.update X i (X i + Torus.mk u) p.1 -
        Function.update X i (X i + Torus.mk u) p.2))
      ContDiffAt ℝ 2 G 0 ∧ 0 ≤ G 0 ∧ G 0 ≤ 1 ∧
      ‖gradient G 0‖ ≤ (if sT (X p.1 - X p.2) ≤ 2 * ε then C₁ * wEnv s (X p.1) (X p.2) else 0) ∧
      |Laplacian.laplacian G 0| ≤
        (if sT (X p.1 - X p.2) ≤ 2 * ε then C₂ * wEnv s (X p.1) (X p.2) ^ 2 else 0) := by
  obtain ⟨M₁, M₂, hM₁, hM₂, hM⟩ := domp_Th_bounds (d := d)
  refine ⟨M₁ + 1, M₂, by positivity, hM₂, fun ε hε X hX i p hp => ?_⟩
  intro G
  have hlt := domp_mem_pairsN hp
  have hne : X p.1 ≠ X p.2 := fun h => hX ⟨p.1, p.2, hlt.ne, h⟩
  have hw0 : 0 ≤ wEnv s (X p.1) (X p.2) := zero_le_one.trans (PairCorrAux.one_le_wEnv s _ _)
  have hα0 : 0 ≤ (if sT (X p.1 - X p.2) ≤ 2 * ε then (M₁ + 1) * wEnv s (X p.1) (X p.2) else 0) := by
    split_ifs
    · positivity
    · exact le_rfl
  have hγ0 : 0 ≤ (if sT (X p.1 - X p.2) ≤ 2 * ε then M₂ * wEnv s (X p.1) (X p.2) ^ 2 else 0) := by
    split_ifs
    · positivity
    · exact le_rfl
  have hG0 : 0 ≤ G 0 ∧ G 0 ≤ 1 := ⟨domp_th_nonneg _, domp_th_le_one _⟩
  rcases domp_pair_cases ε X i hp with hc | ⟨a, hsa, hTh⟩
  · have hG : G = fun _ => th (ε⁻¹ * sT (X p.1 - X p.2)) := funext hc
    rw [hG]
    refine ⟨contDiffAt_const, domp_th_nonneg _, domp_th_le_one _, ?_, ?_⟩
    · rw [gradient_fun_const]; simpa using hα0
    · rw [show Laplacian.laplacian (fun _ : Euc d => th (ε⁻¹ * sT (X p.1 - X p.2))) 0 = 0 from
        congrFun (InnerProductSpace.laplacian_const (E := Euc d)
          (c := th (ε⁻¹ * sT (X p.1 - X p.2)))) 0]
      simpa using hγ0
  · have hG : G = fun u => Th ε (a + u) := funext hTh
    have hcd : ContDiffAt ℝ 2 G 0 := by
      rw [hG]
      exact (((domp_Th_smooth ε).comp (contDiff_const.add contDiff_id)).of_le
        (by norm_cast)).contDiffAt
    refine ⟨hcd, hG0.1, hG0.2, ?_, ?_⟩
    · rw [hG, domp_gradient_comp_add]
      by_cases hsh : sT (X p.1 - X p.2) ≤ 2 * ε
      · rw [if_pos hsh]
        have hσ : 0 < sE a := by rw [hsa]; exact domp_sT_pos (sub_ne_zero.2 hne)
        have hb := ((hM ε a hε).2 hσ (by rw [hsa]; exact hsh)).1
        have hinv := domp_inv_sT_le hs1 hne
        rw [hsa] at hb
        have hσ' : 0 < sT (X p.1 - X p.2) := by rw [← hsa]; exact hσ
        have h1 : ‖gradient (Th ε) a‖ ^ 2 ≤ M₁ * (sT (X p.1 - X p.2))⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ hσ']; exact hb
        have h2 : ‖gradient (Th ε) a‖ ^ 2 ≤ ((M₁ + 1) * wEnv s (X p.1) (X p.2)) ^ 2 := by
          calc ‖gradient (Th ε) a‖ ^ 2 ≤ M₁ * (sT (X p.1 - X p.2))⁻¹ := h1
            _ ≤ M₁ * (wEnv s (X p.1) (X p.2) ^ 2 / 8) := mul_le_mul_of_nonneg_left hinv hM₁
            _ ≤ ((M₁ + 1) * wEnv s (X p.1) (X p.2)) ^ 2 := by
                have hw2 : 0 ≤ wEnv s (X p.1) (X p.2) ^ 2 := sq_nonneg _
                nlinarith [mul_nonneg hM₁ hw2, mul_nonneg (mul_nonneg hM₁ hM₁) hw2]
        exact le_of_sq_le_sq h2 (by positivity)
      · rw [if_neg hsh]
        have hfar : 2 * ε < sE a := by rw [hsa]; exact not_le.1 hsh
        rw [((hM ε a hε).1 hfar).1]; simp
    · rw [hG, domp_lap_comp_add]
      by_cases hsh : sT (X p.1 - X p.2) ≤ 2 * ε
      · rw [if_pos hsh]
        have hσ : 0 < sE a := by rw [hsa]; exact domp_sT_pos (sub_ne_zero.2 hne)
        have hb := ((hM ε a hε).2 hσ (by rw [hsa]; exact hsh)).2
        have hinv := domp_inv_sT_le hs1 hne
        rw [hsa] at hb
        have hσ' : 0 < sT (X p.1 - X p.2) := by rw [← hsa]; exact hσ
        have h1 : |Laplacian.laplacian (Th ε) a| ≤ M₂ * (sT (X p.1 - X p.2))⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ hσ']; exact hb
        calc |Laplacian.laplacian (Th ε) a| ≤ M₂ * (sT (X p.1 - X p.2))⁻¹ := h1
          _ ≤ M₂ * (wEnv s (X p.1) (X p.2) ^ 2 / 8) := mul_le_mul_of_nonneg_left hinv hM₂
          _ ≤ M₂ * wEnv s (X p.1) (X p.2) ^ 2 := by
              have := mul_nonneg hM₂ (sq_nonneg (wEnv s (X p.1) (X p.2)))
              nlinarith
      · rw [if_neg hsh]
        have hfar : 2 * ε < sE a := by rw [hsa]; exact not_le.1 hsh
        rw [((hM ε a hε).1 hfar).2]; simp

theorem domp_card_pairsN_le : ((pairsN N).card : ℝ) ≤ (N : ℝ) * N := by
  have : (pairsN N).card ≤ N * N := by
    calc (pairsN N).card ≤ (Finset.univ : Finset (Fin N × Fin N)).card := Finset.card_filter_le _ _
      _ = N * N := by simp
  exact_mod_cast this

/-- The gradient and Laplacian of `χ_ε` in the `i`-th particle. -/
theorem domp_chi_deriv (hs1 : 1 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ∀ (X : Config d N), X ∉ collisionSet d N → ∀ i : Fin N,
      ContDiffAt ℝ 2 (fun u : Euc d => chi ε (Function.update X i (X i + Torus.mk u))) 0 ∧
      ‖configGrad (chi ε) X i‖ ≤ C * Pw s X ∧ |configLap (chi ε) X i| ≤ C * Pw s X ^ 2 ∧
      (¬ Near ε X → configGrad (chi ε) X i = 0 ∧ configLap (chi ε) X i = 0) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hB⟩ := domp_pair_bound (d := d) (N := N) hs1
  have hN0 : (0 : ℝ) ≤ (N : ℝ) * N := by positivity
  refine ⟨(N * N) * C₁ + (N * N) * C₂ + 2 * ((N * N) * C₁) ^ 2, by positivity, fun ε hε X hX i => ?_⟩
  have hP1 := domp_one_le_Pw (s := s) X
  have hP0 : 0 ≤ Pw s X := by linarith
  set α : Fin N × Fin N → ℝ := fun p =>
    if sT (X p.1 - X p.2) ≤ 2 * ε then C₁ * wEnv s (X p.1) (X p.2) else 0 with hα
  set γ : Fin N × Fin N → ℝ := fun p =>
    if sT (X p.1 - X p.2) ≤ 2 * ε then C₂ * wEnv s (X p.1) (X p.2) ^ 2 else 0 with hγ
  set G : Fin N × Fin N → Euc d → ℝ := fun p u =>
    th (ε⁻¹ * sT (Function.update X i (X i + Torus.mk u) p.1 -
      Function.update X i (X i + Torus.mk u) p.2)) with hG
  have hpb : ∀ p ∈ pairsN N, ContDiffAt ℝ 2 (G p) 0 ∧ 0 ≤ G p 0 ∧ G p 0 ≤ 1 ∧
      ‖gradient (G p) 0‖ ≤ α p ∧ |Laplacian.laplacian (G p) 0| ≤ γ p :=
    fun p hp => hB ε hε X hX i p hp
  obtain ⟨⟨hP0', hP1'⟩, hcd, hgr, hlap⟩ := domp_prod_deriv_bound (pairsN N) G 0
    (fun p hp => (hpb p hp).1) (fun p hp => ⟨(hpb p hp).2.1, (hpb p hp).2.2.1⟩) α γ
    (fun p hp => (hpb p hp).2.2.2.1) (fun p hp => (hpb p hp).2.2.2.2)
  have hfun : (fun z => ∏ p ∈ pairsN N, G p z) =
      fun u : Euc d => chi ε (Function.update X i (X i + Torus.mk u)) := rfl
  rw [hfun] at hcd hgr hlap
  have hcg : configGrad (chi ε) X i = gradient (fun u : Euc d => chi ε (Function.update X i (X i + Torus.mk u))) 0 := rfl
  have hcl : configLap (chi ε) X i = Laplacian.laplacian (fun u : Euc d => chi ε (Function.update X i (X i + Torus.mk u))) 0 := rfl
  rw [← hcg] at hgr
  rw [← hcl] at hlap
  have hwP : ∀ p ∈ pairsN N, wEnv s (X p.1) (X p.2) ≤ Pw s X := fun p hp =>
    domp_w_le_Pw X (domp_mem_pairsN hp).ne
  have hαle : ∀ p ∈ pairsN N, α p ≤ C₁ * Pw s X := by
    intro p hp
    simp only [hα]
    split_ifs
    · exact mul_le_mul_of_nonneg_left (hwP p hp) hC₁
    · positivity
  have hγle : ∀ p ∈ pairsN N, γ p ≤ C₂ * Pw s X ^ 2 := by
    intro p hp
    simp only [hγ]
    split_ifs
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans
        (PairCorrAux.one_le_wEnv s _ _)) (hwP p hp) 2) hC₂
    · positivity
  have hsα : ∑ p ∈ pairsN N, α p ≤ (N * N) * C₁ * Pw s X := by
    calc ∑ p ∈ pairsN N, α p ≤ ∑ _p ∈ pairsN N, C₁ * Pw s X := Finset.sum_le_sum hαle
      _ = (pairsN N).card * (C₁ * Pw s X) := by simp
      _ ≤ (N * N) * (C₁ * Pw s X) := mul_le_mul_of_nonneg_right domp_card_pairsN_le (by positivity)
      _ = _ := by ring
  have hsγ : ∑ p ∈ pairsN N, γ p ≤ (N * N) * C₂ * Pw s X ^ 2 := by
    calc ∑ p ∈ pairsN N, γ p ≤ ∑ _p ∈ pairsN N, C₂ * Pw s X ^ 2 := Finset.sum_le_sum hγle
      _ = (pairsN N).card * (C₂ * Pw s X ^ 2) := by simp
      _ ≤ (N * N) * (C₂ * Pw s X ^ 2) := mul_le_mul_of_nonneg_right domp_card_pairsN_le (by positivity)
      _ = _ := by ring
  have hsα0 : 0 ≤ ∑ p ∈ pairsN N, α p := Finset.sum_nonneg fun p hp => (norm_nonneg _).trans (hpb p hp).2.2.2.1
  refine ⟨hcd, ?_, ?_, fun hnear => ?_⟩
  · rw [hcg]
    refine hgr.trans (hsα.trans ?_)
    have : 0 ≤ (N * N : ℝ) * C₁ * Pw s X := by positivity
    nlinarith [mul_nonneg (mul_nonneg hN0 hC₂) hP0, mul_nonneg (sq_nonneg ((N * N : ℝ) * C₁)) hP0,
      mul_nonneg (mul_nonneg hN0 hC₁) hP0]
  · rw [hcl]
    refine hlap.trans ?_
    have h1 : 2 * (∑ p ∈ pairsN N, α p) ^ 2 ≤ 2 * ((N * N) * C₁ * Pw s X) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsα0 hsα 2) (by norm_num)
    have hP2 : 1 ≤ Pw s X ^ 2 := one_le_pow₀ hP1
    have h2 : 0 ≤ (N * N : ℝ) * C₁ := mul_nonneg hN0 hC₁
    calc ∑ p ∈ pairsN N, γ p + 2 * (∑ p ∈ pairsN N, α p) ^ 2
        ≤ (N * N) * C₂ * Pw s X ^ 2 + 2 * ((N * N) * C₁ * Pw s X) ^ 2 := add_le_add hsγ h1
      _ = ((N * N) * C₂ + 2 * ((N * N) * C₁) ^ 2) * Pw s X ^ 2 := by ring
      _ ≤ ((N * N) * C₁ + (N * N) * C₂ + 2 * ((N * N) * C₁) ^ 2) * Pw s X ^ 2 := by
          gcongr
          linarith [mul_nonneg hN0 hC₁]
  · have hα0 : ∀ p ∈ pairsN N, α p = 0 := by
      intro p hp
      simp only [hα]
      rw [if_neg]
      intro hle
      exact hnear ⟨p.1, p.2, (domp_mem_pairsN hp).ne, hle⟩
    have hγ0 : ∀ p ∈ pairsN N, γ p = 0 := by
      intro p hp
      simp only [hγ]
      rw [if_neg]
      intro hle
      exact hnear ⟨p.1, p.2, (domp_mem_pairsN hp).ne, hle⟩
    rw [Finset.sum_eq_zero hα0] at hgr
    rw [Finset.sum_eq_zero hα0, Finset.sum_eq_zero hγ0] at hlap
    refine ⟨?_, ?_⟩
    · exact norm_le_zero_iff.1 (by simpa using hgr)
    · exact abs_nonpos_iff.1 (by simpa using hlap)

end HRS.MD.DOMProof

end
