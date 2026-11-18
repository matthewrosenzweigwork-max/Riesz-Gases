import HRS.Equilibrium.Parametrix.PX4aAuxL

/-!
# Packet PX4a auxiliaries M: full derivative bounds away from the diagonal; the far source

`conormal_full_away`: a conormal kernel has full derivative bounds `‖D^k lift2 F‖ ≤ K B` on
`{eucDist ≥ δ}` (no decay condition; the constant depends on `δ`).  `fsrc_smooth`: the far source
`Fsrc F = (1 - perCut_{1/32}) · leftCh F` is `C^M` with bounded derivatives `≤ K B`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma eucDist_chart_eq (X z : Euc d) (n : Lattice d) (hz : ‖z‖ < 1 / 8) :
    Torus.eucDist (Torus.mk (X + (1 / 2 : ℝ) • z + (Lattice.toEuc n))) (Torus.mk (X - (1 / 2 : ℝ) • z)) =
      ‖z‖ := by
  have h1 : Torus.mk (X + (1 / 2 : ℝ) • z + (Lattice.toEuc n)) =
      Torus.mk (X - (1 / 2 : ℝ) • z) + Torus.mk z := by
    rw [mk_add_eq, mk_toEuc_eq, add_zero, ← mk_add_eq]
    congr 1
    module
  rw [h1, eucDist_comm, LocalDivAux.eucDist_shift]
  have hb : ∀ i, |z i| ≤ 1 / 2 := fun i => by
    have := PiLp.norm_apply_le z i
    simp only [Real.norm_eq_abs] at this
    linarith
  exact LocalDivAux.eucDist_mk_zero' hb

lemma exists_weight_bound (σ : ℝ) (b M : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, δ ≤ r → r ≤ 1 → ∀ c : ℕ, c ≤ M →
      r ^ (-(σ + (c : ℝ))) * (1 + |Real.log r|) ^ b ≤ C := by
  set C : ℝ := ∑ c ∈ Finset.range (M + 1), (δ ^ (-(σ + (c : ℝ))) + 1) * lw δ ^ b with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun c _ => by
    have := lw_pos δ
    positivity
  refine ⟨C, hC0, fun r hδr hr1 c hc => ?_⟩
  have hr0 : 0 < r := lt_of_lt_of_le hδ hδr
  have h1 : r ^ (-(σ + (c : ℝ))) ≤ δ ^ (-(σ + (c : ℝ))) + 1 := by
    rcases le_or_gt 0 (-(σ + (c : ℝ))) with he | he
    · have : r ^ (-(σ + (c : ℝ))) ≤ 1 := Real.rpow_le_one hr0.le hr1 he
      have : 0 ≤ δ ^ (-(σ + (c : ℝ))) := Real.rpow_nonneg hδ.le _
      linarith
    · have : r ^ (-(σ + (c : ℝ))) ≤ δ ^ (-(σ + (c : ℝ))) :=
        Real.rpow_le_rpow_of_nonpos hδ hδr he.le
      linarith
  have h2 : (1 + |Real.log r|) ^ b ≤ lw δ ^ b :=
    pow_le_pow_left₀ (lw_pos _).le (lw_anti hδ hδr hr1) b
  have h3 : (δ ^ (-(σ + (c : ℝ))) + 1) * lw δ ^ b ≤ C :=
    Finset.single_le_sum (f := fun c : ℕ => (δ ^ (-(σ + (c : ℝ))) + 1) * lw δ ^ b)
      (fun c _ => by have := lw_pos δ; positivity) (Finset.mem_range.mpr (by omega))
  calc r ^ (-(σ + (c : ℝ))) * (1 + |Real.log r|) ^ b
      ≤ (δ ^ (-(σ + (c : ℝ))) + 1) * lw δ ^ b :=
        mul_le_mul h1 h2 (by positivity) (by have := Real.rpow_nonneg hδ.le (-(σ + (c : ℝ))); linarith)
    _ ≤ C := h3

theorem conormal_full_away {σ : ℝ} {b : ℕ} (M : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ {B : ℝ} {F : Torus d → Torus d → ℝ}, 0 ≤ B → Conormal σ b M B F →
      ∀ p ∈ offDiag d, δ ≤ Torus.eucDist (Torus.mk p.1) (Torus.mk p.2) →
        ∀ k ≤ M, ‖iteratedFDeriv ℝ k (lift2 F) p‖ ≤ K0 * B := by
  obtain ⟨C, hC0, hC⟩ := exists_weight_bound σ b M hδ
  refine ⟨max (4 ^ M * (1 + C)) 1, le_max_of_le_right zero_le_one, ?_⟩
  intro B F hB hF p hp hδp k hk
  by_cases hdist : Torus.eucDist (Torus.mk p.1) (Torus.mk p.2) < r0
  · obtain ⟨X, z, n, hz, hzr, hpe⟩ := near_rep hp hdist
    have hzr' : ‖z‖ < 1 / 8 := by unfold r0 at hzr; exact hzr
    have hq : (X, z) ∈ Uc d := mem_Uc hz hzr
    have hzd : δ ≤ ‖z‖ := by
      have := eucDist_chart_eq X z n hzr'
      rw [hpe] at hδp
      simp only [chartT_apply, Prod.fst_add, Prod.snd_add, add_zero] at hδp
      rw [this] at hδp
      exact hδp
    set r := ‖z‖ with hr
    have hr0 : 0 < r := norm_pos_iff.mpr hz
    have hr1 : r ≤ 1 := by linarith
    have hGd : ∀ nn ≤ M, ContDiffOn ℝ (nn : WithTop ℕ∞) (toChart F) (Uc d) := fun nn hn =>
      (toChart_contDiffOn hF.smooth).of_le (by exact_mod_cast hn)
    have hnear : ∀ a c, a + c = k → ‖mixedDeriv a c (toChart F) X z‖ ≤ B * (1 + C) := by
      intro a c hac
      refine (hF.near a c (by omega) X z hz hzr).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hB
      have := hC r hzd hr1 c (by omega)
      linarith
    have hTB : ∀ a c, a + c = k → TB (toChart F) (X, z) a c (B * (1 + C)) := fun a c hac =>
      tb_of_norm_le isOpen_Uc (hGd (a + c) (by omega)) hq (hnear a c hac)
    have hfull := full_of_tb k (toChart F) (B * (1 + C)) (by positivity)
      ((hGd k hk).contDiffAt (isOpen_Uc.mem_nhds hq)) hTB
    have hnorm : ‖iteratedFDeriv ℝ k (toChart F) (X, z)‖ ≤ 2 ^ k * (B * (1 + C)) := by
      refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun w => ?_
      have := hfull w
      rw [Real.norm_eq_abs]
      linarith
    have hconv := norm_iteratedFDeriv_chart_le (lift2 F) k (X, z)
    rw [← toChart_eq] at hconv
    rw [hpe, iteratedFDeriv_lift2_periodic]
    have hk4 : (4 : ℝ) ^ k ≤ 4 ^ M := pow_le_pow_right₀ (by norm_num) hk
    have h2k : (2 : ℝ) ^ k * 2 ^ k = 4 ^ k := by rw [← mul_pow]; norm_num
    calc ‖iteratedFDeriv ℝ k (lift2 F) (chartT d (X, z))‖
        ≤ 2 ^ k * ‖iteratedFDeriv ℝ k (toChart F) (X, z)‖ := hconv
      _ ≤ 2 ^ k * (2 ^ k * (B * (1 + C))) := mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = 4 ^ k * (B * (1 + C)) := by rw [← mul_assoc, h2k]
      _ ≤ 4 ^ M * (B * (1 + C)) := mul_le_mul_of_nonneg_right hk4 (by positivity)
      _ = (4 ^ M * (1 + C)) * B := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hB
  · push_neg at hdist
    have := hF.far k hk p hp hdist
    calc _ ≤ B := this
      _ = 1 * B := (one_mul B).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hB

/-- The linear map `(Y, w) ↦ (Y + w, Y)` (so that `leftCh F = lift2 F ∘ leftL`). -/
def leftL (d : ℕ) : Euc d × Euc d →L[ℝ] Euc d × Euc d :=
  ((ContinuousLinearMap.fst ℝ (Euc d) (Euc d)) + (ContinuousLinearMap.snd ℝ (Euc d) (Euc d))).prod
    (ContinuousLinearMap.fst ℝ (Euc d) (Euc d))

lemma leftL_apply (p : Euc d × Euc d) : leftL d p = (p.1 + p.2, p.1) := rfl

lemma norm_leftL_le : ‖leftL d‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun p => ?_
  rw [leftL_apply, Prod.norm_def]
  have h1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
  have h2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
  refine max_le ?_ ?_
  · show ‖p.1 + p.2‖ ≤ 2 * ‖p‖
    calc ‖p.1 + p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  · show ‖p.1‖ ≤ 2 * ‖p‖
    have := norm_nonneg p
    linarith

lemma leftCh_eq_comp (F : Torus d → Torus d → ℝ) : leftCh F = lift2 F ∘ leftL d := rfl

lemma eucDist_left (Y w : Euc d) :
    Torus.eucDist (Torus.mk (Y + w)) (Torus.mk Y) = ‖Torus.centeredRep (Torus.mk w)‖ := by
  rw [mk_add_eq, eucDist_comm, LocalDivAux.eucDist_shift]
  have hb : ∀ i, |Torus.centeredRep (Torus.mk w) i| ≤ 1 / 2 := fun i => px3a_abs_cR_le _ i
  rw [← LocalDivAux.eucDist_mk_zero' hb, px3a_mk_cR]

lemma isOpen_snd_mk_ne : IsOpen {p : Euc d × Euc d | Torus.mk p.2 ≠ 0} :=
  isOpen_mk_ne_zero'.preimage continuous_snd

set_option maxHeartbeats 1600000 in
theorem fsrc_smooth {σ : ℝ} {b : ℕ} (M : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {B : ℝ} {F : Torus d → Torus d → ℝ}, 0 ≤ B → Conormal σ b M B F →
      ContDiff ℝ (M : WithTop ℕ∞) (Fsrc F) ∧
      ∀ j ≤ M, ∀ p : Euc d × Euc d, ‖iteratedFDeriv ℝ j (Fsrc F) p‖ ≤ K * B := by
  obtain ⟨K0, hK0, hK⟩ := conormal_full_away (d := d) (σ := σ) (b := b) M (δ := 1 / 64) (by norm_num)
  have hηc : ∀ n : ℕ∞, ContDiff ℝ n (fun w : Euc d => 1 - perCut d (1 / 32) w) := fun n =>
    contDiff_const.sub (perCut_contDiff (by norm_num) (by norm_num) n)
  have hηb : ∀ n : ℕ, ∃ Mn : ℝ, 0 ≤ Mn ∧ ∀ y : Euc d,
      ‖iteratedFDeriv ℝ n (fun w : Euc d => 1 - perCut d (1 / 32) w) y‖ ≤ Mn := by
    intro n
    have : (fun w : Euc d => 1 - perCut d (1 / 32) w) =
        Torus.lift (fun x : Torus d => 1 - px3a_zeta d (1 / 32) (Torus.centeredRep x)) := rfl
    rw [this]
    exact bdd_iteratedFDeriv_lift _ n (by rw [← this]; exact_mod_cast hηc (n : ℕ∞))
  choose Mn hMn0 hMn using hηb
  set Mη : ℝ := ∑ n ∈ Finset.range (M + 1), Mn n with hMη
  have hMη0 : 0 ≤ Mη := Finset.sum_nonneg fun n _ => hMn0 n
  have hMηle : ∀ n ≤ M, Mn n ≤ Mη := fun n hn =>
    Finset.single_le_sum (f := Mn) (fun i _ => hMn0 i) (Finset.mem_range.mpr (by omega))
  refine ⟨2 ^ M * (Mη * (K0 * 2 ^ M)), by positivity, fun {B} {F} hB hF => ?_⟩
  have hUo := isOpen_snd_mk_ne (d := d)
  -- smoothness of the left chart on `U`
  have hleft : ContDiffOn ℝ (M : WithTop ℕ∞) (leftCh F) {p : Euc d × Euc d | Torus.mk p.2 ≠ 0} := by
    rw [leftCh_eq_comp]
    refine hF.smooth.comp (leftL d).contDiff.contDiffOn (fun p hp => ?_)
    show Torus.mk (leftL d p).1 ≠ Torus.mk (leftL d p).2
    rw [leftL_apply]
    simp only [mk_add_eq]
    intro h
    exact hp (by simpa using h)
  have hηs : ContDiff ℝ (M : WithTop ℕ∞) (fun p : Euc d × Euc d => 1 - perCut d (1 / 32) p.2) :=
    (hηc (M : ℕ∞)).comp contDiff_snd
  -- the near-lattice alternative
  have hzero : ∀ p : Euc d × Euc d, ∀ n : Euc d, IsLat n → ‖p.2 - n‖ < 1 / 64 →
      Fsrc F =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
    intro p n hn hpn
    filter_upwards [(isOpen_lt (continuous_norm.comp (continuous_snd.sub continuous_const))
      continuous_const).mem_nhds (show ‖p.2 - n‖ < (1 / 64 : ℝ) from hpn)] with p' hp'
    have hp'' : ‖p'.2 - n‖ < 1 / 64 := hp'
    have hs : ∀ i, |(p'.2 - n) i| < 1 / 2 := fun i => lt_of_le_of_lt (by
      have := PiLp.norm_apply_le (p'.2 - n) i
      simpa [Real.norm_eq_abs] using this) (by linarith)
    have : perCut d (1 / 32) p'.2 = 1 := by
      rw [perCut_eq_of_small _ p'.2 n hn hs]
      exact px3a_zeta_eq_one (by norm_num) (by linarith)
    show (1 - perCut d (1 / 32) p'.2) * leftCh F p' = 0
    rw [this]; ring
  have hfar : ∀ p : Euc d × Euc d, (∀ n : Euc d, IsLat n → 1 / 64 ≤ ‖p.2 - n‖) →
      p ∈ {p : Euc d × Euc d | Torus.mk p.2 ≠ 0} := by
    intro p hp hm
    have := hp p.2 (mk_eq_zero_imp hm) 
    simp at this
    linarith
  refine ⟨?_, fun j hj p => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hnear : ∃ n : Euc d, IsLat n ∧ ‖p.2 - n‖ < 1 / 64
    · obtain ⟨n, hn, hpn⟩ := hnear
      exact contDiffAt_const.congr_of_eventuallyEq (hzero p n hn hpn)
    · push_neg at hnear
      have hpU := hfar p hnear
      exact (hηs.contDiffAt.mul (hleft.contDiffAt (hUo.mem_nhds hpU)))
  · by_cases hnear : ∃ n : Euc d, IsLat n ∧ ‖p.2 - n‖ < 1 / 64
    · obtain ⟨n, hn, hpn⟩ := hnear
      rw [((hzero p n hn hpn).iteratedFDeriv ℝ j).eq_of_nhds]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp [iteratedFDeriv_zero_eq_comp]; positivity
      · rw [iteratedFDeriv_const_of_ne (by omega : j ≠ 0)]
        simp; positivity
    · push_neg at hnear
      have hpU := hfar p hnear
      have hmul := norm_iteratedFDerivWithin_mul_le (n := j) (N := (M : WithTop ℕ∞))
        (f := fun p : Euc d × Euc d => 1 - perCut d (1 / 32) p.2) (g := leftCh F)
        hηs.contDiffOn hleft hUo.uniqueDiffOn hpU (by exact_mod_cast hj)
      have hFeq : Fsrc F = fun p => (1 - perCut d (1 / 32) p.2) * leftCh F p := rfl
      rw [hFeq]
      have e0 : iteratedFDeriv ℝ j (fun p => (1 - perCut d (1 / 32) p.2) * leftCh F p) p =
          iteratedFDerivWithin ℝ j (fun p => (1 - perCut d (1 / 32) p.2) * leftCh F p)
            {p : Euc d × Euc d | Torus.mk p.2 ≠ 0} p := by
        rw [iteratedFDerivWithin_of_isOpen j hUo hpU]
      rw [e0]
      refine hmul.trans ?_
      have hL1 : ∀ i, iteratedFDerivWithin ℝ i (fun p : Euc d × Euc d => 1 - perCut d (1 / 32) p.2)
          {p : Euc d × Euc d | Torus.mk p.2 ≠ 0} p =
          iteratedFDeriv ℝ i (fun p : Euc d × Euc d => 1 - perCut d (1 / 32) p.2) p := fun i =>
        iteratedFDerivWithin_of_isOpen i hUo hpU
      have hL2 : ∀ i, iteratedFDerivWithin ℝ i (leftCh F) {p : Euc d × Euc d | Torus.mk p.2 ≠ 0} p =
          iteratedFDeriv ℝ i (leftCh F) p := fun i => iteratedFDerivWithin_of_isOpen i hUo hpU
      simp only [hL1, hL2]
      -- bounds on the two factors
      have hA : ∀ i ≤ M, ‖iteratedFDeriv ℝ i (fun p : Euc d × Euc d => 1 - perCut d (1 / 32) p.2) p‖ ≤ Mη := by
        intro i hi
        have := norm_iteratedFDeriv_comp_clm_le (ContinuousLinearMap.snd ℝ (Euc d) (Euc d))
          (ContinuousLinearMap.norm_snd_le ℝ (Euc d) (Euc d)) (hηc (M : ℕ∞)) (i := i)
          (by exact_mod_cast hi) p
        exact this.trans ((hMn i p.2).trans (hMηle i hi))
      have hmem : leftL d p ∈ offDiag d := by
        show Torus.mk (leftL d p).1 ≠ Torus.mk (leftL d p).2
        rw [leftL_apply]
        simp only [mk_add_eq]
        intro h
        exact hpU (by simpa using h)
      have hdist : 1 / 64 ≤ Torus.eucDist (Torus.mk (leftL d p).1) (Torus.mk (leftL d p).2) := by
        rw [leftL_apply]
        simp only
        rw [eucDist_left]
        obtain ⟨n0, hn0, hc⟩ := cR_exists_lat p.2
        rw [hc]
        exact hnear n0 hn0
      have hB : ∀ l ≤ M, ‖iteratedFDeriv ℝ l (leftCh F) p‖ ≤ K0 * B * 2 ^ M := by
        intro l hl
        rw [leftCh_eq_comp, iteratedFDeriv_comp_clm_of_open_n isOpen_offDiag
          (hF.smooth) (leftL d) hmem (by exact_mod_cast hl)]
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        have h1 := hK hB hF _ hmem hdist l hl
        have h2 : ∏ _i : Fin l, ‖leftL d‖ ≤ 2 ^ M := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          calc ‖leftL d‖ ^ l ≤ 2 ^ l := pow_le_pow_left₀ (norm_nonneg _) norm_leftL_le l
            _ ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hl
        exact mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) (mul_nonneg hK0 hB)
      have hterm : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun p : Euc d × Euc d => 1 - perCut d (1 / 32) p.2) p‖ *
            ‖iteratedFDeriv ℝ (j - i) (leftCh F) p‖ ≤ (j.choose i : ℝ) * (Mη * (K0 * B * 2 ^ M)) := by
        intro i hi
        have hij : i ≤ j := by have := Finset.mem_range.mp hi; omega
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        exact mul_le_mul (hA i (by omega)) (hB (j - i) (by omega)) (norm_nonneg _) hMη0
      calc _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (Mη * (K0 * B * 2 ^ M)) :=
            Finset.sum_le_sum hterm
        _ = 2 ^ j * (Mη * (K0 * B * 2 ^ M)) := by
            rw [← Finset.sum_mul]
            have : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = 2 ^ j := by
              exact_mod_cast Nat.sum_range_choose j
            rw [this]
        _ ≤ 2 ^ M * (Mη * (K0 * B * 2 ^ M)) := by
            refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) ?_
            positivity
        _ = _ := by ring

end HRS.Parx

end
