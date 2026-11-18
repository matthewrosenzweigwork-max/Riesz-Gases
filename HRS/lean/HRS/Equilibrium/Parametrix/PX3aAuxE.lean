import HRS.Equilibrium.Parametrix.PX3aAuxD

/-!
# Packet PX3a auxiliaries E: scaled cutoffs and the near/far splitting of the kernel
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma contDiff_mul_of_tsupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → ℝ}
    {U : Set E} (hU : IsOpen U) {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (hg : ContDiffOn ℝ n g U)
    (hs : tsupport f ⊆ U) : ContDiff ℝ n (fun x => f x * g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hf.contDiffAt.mul (hg.contDiffAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport f := fun h => hx (hs h)
    have : (fun y => f y * g y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx'] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq this

/-- Fixed radial cutoff: `1` on `‖u‖ ≤ 1/2`, supported in `‖u‖ < 1`. -/
def px3a_bump1 (d : ℕ) : ContDiffBump (0 : Euc d) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The scaled cutoff: `1` on `‖u‖ ≤ s/2`, `0` on `‖u‖ ≥ s`. -/
def px3a_zeta (d : ℕ) (s : ℝ) (u : Euc d) : ℝ := px3a_bump1 d (s⁻¹ • u)

lemma px3a_zeta_eq_one {s : ℝ} (hs : 0 < s) {u : Euc d} (hu : ‖u‖ ≤ s / 2) : px3a_zeta d s u = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hs.le]
  show s⁻¹ * ‖u‖ ≤ 1 / 2
  rw [inv_mul_le_iff₀ hs]; linarith

lemma px3a_zeta_eq_zero {s : ℝ} (hs : 0 < s) {u : Euc d} (hu : s ≤ ‖u‖) : px3a_zeta d s u = 0 := by
  apply ContDiffBump.zero_of_le_dist
  rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hs.le]
  show 1 ≤ s⁻¹ * ‖u‖
  rw [le_inv_mul_iff₀ hs]; linarith

lemma px3a_zeta_contDiff (s : ℝ) (n : ℕ∞) : ContDiff ℝ n (px3a_zeta d s) :=
  (px3a_bump1 d).contDiff.comp (contDiff_const_smul _)

lemma px3a_zeta_nonneg (s : ℝ) (u : Euc d) : 0 ≤ px3a_zeta d s u := ContDiffBump.nonneg _

lemma px3a_zeta_le_one (s : ℝ) (u : Euc d) : px3a_zeta d s u ≤ 1 := ContDiffBump.le_one _

lemma px3a_zeta_deriv_bound (n : ℕ) : ∃ S : ℝ, 0 ≤ S ∧ ∀ s : ℝ, 0 < s → ∀ i ≤ n, ∀ u : Euc d,
    ‖iteratedFDeriv ℝ i (px3a_zeta d s) u‖ ≤ S * (s⁻¹) ^ i := by
  obtain ⟨S, hS0, hS⟩ := (px3a_bump1 d).hasCompactSupport.exists_bound_iteratedFDeriv
    ((px3a_bump1 d).contDiff (n := (⊤ : ℕ∞))) n
  refine ⟨S, hS0, fun s hs i hi u => ?_⟩
  set L : Euc d →L[ℝ] Euc d := s⁻¹ • ContinuousLinearMap.id ℝ (Euc d) with hL
  have hz : px3a_zeta d s = (px3a_bump1 d) ∘ L := by funext u; simp [px3a_zeta, hL]
  have e := L.iteratedFDeriv_comp_right (f := (px3a_bump1 d : Euc d → ℝ))
    ((px3a_bump1 d).contDiff (n := (⊤ : ℕ∞))) u (i := i) (by exact_mod_cast le_top)
  rw [hz, e]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hLn : ‖L‖ ≤ s⁻¹ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    simp [hL, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
  have h1 : ∏ _j : Fin i, ‖L‖ ≤ (s⁻¹) ^ i := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_left₀ (norm_nonneg _) hLn _
  exact mul_le_mul (hS i hi _) h1 (Finset.prod_nonneg fun _ _ => norm_nonneg _) hS0

/-- Far part of the kernel: `(1 - ζ_ρ) ζ_1 (E - κ)`. -/
def Lf (d : ℕ) (κ ρ : ℝ) (y : Euc d) : ℝ :=
  (1 - px3a_zeta d ρ y) * px3a_zeta d 1 y * (Efund d y - κ)

/-- Near part of the kernel: `ζ_ρ (E - κ)`. -/
def Ln (d : ℕ) (κ ρ : ℝ) (y : Euc d) : ℝ := px3a_zeta d ρ y * (Efund d y - κ)

/-- A globally smooth kernel agreeing with `E - κ` away from the origin. -/
def Lamhat (d : ℕ) (κ ρ : ℝ) (y : Euc d) : ℝ := (1 - px3a_zeta d (ρ / 4) y) * (Efund d y - κ)

lemma Lf_eq {ρ : ℝ} (hρ : 0 < ρ) (κ : ℝ) (y : Euc d) :
    Lf d κ ρ y = ((1 - px3a_zeta d ρ y) * px3a_zeta d 1 y) * Lamhat d κ ρ y := by
  unfold Lf Lamhat
  rcases le_or_gt ‖y‖ (ρ / 2) with h | h
  · rw [px3a_zeta_eq_one hρ h]; ring
  · rw [px3a_zeta_eq_zero (by linarith : ρ / 4 > 0) (by linarith)]; ring

lemma tsupport_one_sub_zeta_subset {ρ : ℝ} (hρ : 0 < ρ) :
    tsupport (fun y : Euc d => 1 - px3a_zeta d (ρ / 4) y) ⊆ {0}ᶜ := by
  have : tsupport (fun y : Euc d => 1 - px3a_zeta d (ρ / 4) y) ⊆ {y : Euc d | ρ / 8 ≤ ‖y‖} := by
    refine closure_minimal (fun y hy => ?_) (isClosed_le continuous_const continuous_norm)
    rw [mem_setOf_eq]
    by_contra h
    have h' : ‖y‖ < ρ / 8 := not_le.mp h
    apply hy
    simp [px3a_zeta_eq_one (by linarith : ρ / 4 > 0) (by linarith : ‖y‖ ≤ ρ / 4 / 2)]
  intro y hy h0
  have := this hy
  simp only [mem_setOf_eq] at this
  rw [mem_singleton_iff] at h0
  subst h0
  simp at this
  linarith

lemma Lamhat_contDiff {ρ : ℝ} (hρ : 0 < ρ) (κ : ℝ) (n : ℕ∞) : ContDiff ℝ n (Lamhat d κ ρ) := by
  have h1 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun y : Euc d => Efund d y - κ) {0}ᶜ :=
    (contDiffOn_Efund _).sub contDiffOn_const
  have h2 := contDiff_mul_of_tsupport isOpen_compl_singleton
    ((contDiff_const.sub (px3a_zeta_contDiff (d := d) (ρ / 4) n))) h1 (tsupport_one_sub_zeta_subset hρ)
  exact h2

lemma Lf_contDiff {ρ : ℝ} (hρ : 0 < ρ) (κ : ℝ) (n : ℕ∞) : ContDiff ℝ n (Lf d κ ρ) := by
  have : Lf d κ ρ = fun y => ((1 - px3a_zeta d ρ y) * px3a_zeta d 1 y) * Lamhat d κ ρ y := by
    funext y; exact Lf_eq hρ κ y
  rw [this]
  exact ((contDiff_const.sub (px3a_zeta_contDiff ρ n)).mul (px3a_zeta_contDiff 1 n)).mul
    (Lamhat_contDiff hρ κ n)

lemma Lf_hasCompactSupport (ρ κ : ℝ) : HasCompactSupport (Lf d κ ρ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) 1) (fun y hy => ?_)
  have : 1 ≤ ‖y‖ := by simpa using (by simpa using hy : 1 < ‖y‖).le
  simp [Lf, px3a_zeta_eq_zero one_pos this]

lemma norm_iteratedFDeriv_one_sub {f : Euc d → ℝ} (hf : ContDiff ℝ ∞' f) {i : ℕ} (hi : 1 ≤ i) (x : Euc d) :
    ‖iteratedFDeriv ℝ i (fun y => 1 - f y) x‖ = ‖iteratedFDeriv ℝ i f x‖ := by
  have e : (fun y => 1 - f y) = (fun _ => (1 : ℝ)) + (fun y => -f y) := by
    funext y; simp [sub_eq_add_neg]
  rw [e, iteratedFDeriv_add_apply contDiffAt_const (hf.neg.contDiffAt.of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_const_of_ne (by omega : i ≠ 0)]
  have : iteratedFDeriv ℝ i (fun y => -f y) x = -iteratedFDeriv ℝ i f x := iteratedFDeriv_neg_apply
  rw [this]
  simp

lemma iteratedFDeriv_zeta_eq_zero_of_gt {ρ : ℝ} (hρ : 0 < ρ) {i : ℕ} (hi : 1 ≤ i) {y : Euc d}
    (hy : ρ < ‖y‖) : iteratedFDeriv ℝ i (px3a_zeta d ρ) y = 0 := by
  have : px3a_zeta d ρ =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with u hu
    exact px3a_zeta_eq_zero hρ hu.le
  rw [(this.iteratedFDeriv ℝ i).eq_of_nhds, iteratedFDeriv_const_of_ne (by omega : i ≠ 0)]
  rfl

lemma norm_iteratedFDeriv_Lamhat_le (hd : 2 ≤ d) {ρ : ℝ} (hρ : 0 < ρ) (κ : ℝ) {k : ℕ} (hk : 1 ≤ k)
    {M : ℝ} (hM : ∀ y : Euc d, y ≠ 0 → ‖iteratedFDeriv ℝ k (Efund d) y‖ ≤ M * ‖y‖ ^ ((2 : ℝ) - d - k))
    {y : Euc d} (hy : ρ / 4 < ‖y‖) :
    ‖iteratedFDeriv ℝ k (Lamhat d κ ρ) y‖ ≤ M * ‖y‖ ^ ((2 : ℝ) - d - k) := by
  have hy0 : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy; linarith
  have hev : Lamhat d κ ρ =ᶠ[𝓝 y] fun u => Efund d u - κ := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with u hu
    simp [Lamhat, px3a_zeta_eq_zero (by linarith : ρ / 4 > 0) hu.le]
  rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
  have e : (fun u : Euc d => Efund d u - κ) = Efund d + (fun _ => -κ) := by
    funext u; simp [sub_eq_add_neg]
  rw [e, iteratedFDeriv_add_apply ((contDiffAt_Efund _ hy0)) contDiffAt_const,
    iteratedFDeriv_const_of_ne (by omega : k ≠ 0)]
  simpa using hM y hy0

set_option maxHeartbeats 1600000 in
lemma norm_iteratedFDeriv_Lf_le (hd : 2 ≤ d) (j : ℕ) (hj : 1 ≤ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ ρ B : ℝ), 0 < ρ → 0 ≤ B →
      (∀ y : Euc d, ρ / 2 ≤ ‖y‖ → ‖y‖ ≤ ρ → |Efund d y - κ| ≤ B * ρ ^ ((2 : ℝ) - d)) →
      ∀ y : Euc d, ρ / 2 ≤ ‖y‖ → ‖y‖ < 1 / 2 →
        ‖iteratedFDeriv ℝ j (Lf d κ ρ) y‖ ≤ C * (1 + B) * ‖y‖ ^ ((2 : ℝ) - d - j) := by
  obtain ⟨S, hS0, hS⟩ := px3a_zeta_deriv_bound (d := d) j
  have hM : ∀ k, ∃ M : ℝ, 0 ≤ M ∧ (1 ≤ k → ∀ y : Euc d, y ≠ 0 →
      ‖iteratedFDeriv ℝ k (Efund d) y‖ ≤ M * ‖y‖ ^ ((2 : ℝ) - d - k)) := by
    intro k
    by_cases hk : 1 ≤ k
    · obtain ⟨M, hM0, hM⟩ := norm_iteratedFDeriv_Efund_le hd hk
      exact ⟨M, hM0, fun _ => hM⟩
    · exact ⟨0, le_rfl, fun h => absurd h hk⟩
  choose M hM0 hMb using hM
  set Mm : ℝ := ∑ k ∈ Finset.range (j + 1), M k with hMm
  have hMm0 : 0 ≤ Mm := Finset.sum_nonneg fun k _ => hM0 k
  have hMle : ∀ k ≤ j, M k ≤ Mm := fun k hk =>
    Finset.single_le_sum (f := M) (fun i _ => hM0 i) (Finset.mem_range.mpr (by omega))
  set C0 : ℝ := Mm + S * (1 + Mm) * 2 ^ (d + j) + S with hC0
  have hC00 : 0 ≤ C0 := by positivity
  refine ⟨2 ^ j * C0, by positivity, fun κ ρ B hρ hB hκ y hy1 hy2 => ?_⟩
  have hy0 : 0 < ‖y‖ := lt_of_lt_of_le (by positivity) hy1
  set e : ℝ := (2 : ℝ) - d - j with he
  have hen : e < 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    rw [he]; linarith
  have hLf : Lf d κ ρ = fun y => ((1 - px3a_zeta d ρ y) * px3a_zeta d 1 y) * Lamhat d κ ρ y := by
    funext y; exact Lf_eq hρ κ y
  have hf1 : ContDiff ℝ ∞' (fun y : Euc d => (1 - px3a_zeta d ρ y) * px3a_zeta d 1 y) :=
    (contDiff_const.sub (px3a_zeta_contDiff ρ _)).mul (px3a_zeta_contDiff 1 _)
  have hL : ContDiff ℝ ∞' (Lamhat d κ ρ) := Lamhat_contDiff hρ κ _
  rw [hLf]
  refine (norm_iteratedFDeriv_mul_le (N := ∞') hf1 hL y (by exact_mod_cast le_top)).trans ?_
  -- local form of the cutoff factor
  have hf1ev : (fun y : Euc d => (1 - px3a_zeta d ρ y) * px3a_zeta d 1 y) =ᶠ[𝓝 y]
      fun y => 1 - px3a_zeta d ρ y := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hy2] with u hu
    rw [px3a_zeta_eq_one one_pos (by have h' : ‖u‖ < 1 / 2 := hu; linarith : ‖u‖ ≤ 1 / 2), mul_one]
  have hD : ∀ i, iteratedFDeriv ℝ i (fun y : Euc d => (1 - px3a_zeta d ρ y) * px3a_zeta d 1 y) y =
      iteratedFDeriv ℝ i (fun y => 1 - px3a_zeta d ρ y) y := fun i =>
    (hf1ev.iteratedFDeriv ℝ i).eq_of_nhds
  have hterm : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i (fun y : Euc d => (1 - px3a_zeta d ρ y) * px3a_zeta d 1 y) y‖ *
        ‖iteratedFDeriv ℝ (j - i) (Lamhat d κ ρ) y‖ ≤ (j.choose i : ℝ) * (C0 * (1 + B) * ‖y‖ ^ e) := by
    intro i hi
    have hij : i ≤ j := by have := Finset.mem_range.mp hi; omega
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    rw [hD]
    have hyr : 0 ≤ ‖y‖ ^ e := by positivity
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · -- the term without derivative on the cutoff
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, norm_iteratedFDeriv_zero,
        Nat.sub_zero, LinearIsometryEquiv.norm_map]
      have h1 : ‖(1 : ℝ) - px3a_zeta d ρ y‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [px3a_zeta_le_one ρ y])]
        linarith [px3a_zeta_nonneg ρ y]
      have h2 := norm_iteratedFDeriv_Lamhat_le hd hρ κ hj (hMb j hj) (by linarith : ρ / 4 < ‖y‖)
      calc ‖(1 : ℝ) - px3a_zeta d ρ y‖ * ‖iteratedFDeriv ℝ j (Lamhat d κ ρ) y‖
          ≤ 1 * (M j * ‖y‖ ^ e) := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ ≤ C0 * (1 + B) * ‖y‖ ^ e := by
            have : M j ≤ C0 := by
              have := hMle j le_rfl
              have : 0 ≤ S * (1 + Mm) * 2 ^ (d + j) := by positivity
              linarith
            have : C0 ≤ C0 * (1 + B) := by nlinarith
            nlinarith
    · have hnorm : ‖iteratedFDeriv ℝ i (fun y => 1 - px3a_zeta d ρ y) y‖ =
          ‖iteratedFDeriv ℝ i (px3a_zeta d ρ) y‖ :=
        norm_iteratedFDeriv_one_sub (px3a_zeta_contDiff ρ _) hipos y
      rw [hnorm]
      by_cases hyρ : ρ < ‖y‖
      · rw [iteratedFDeriv_zeta_eq_zero_of_gt hρ hipos hyρ, norm_zero, zero_mul]
        positivity
      · have hyρ' : ‖y‖ ≤ ρ := not_lt.mp hyρ
        have hS1 : ‖iteratedFDeriv ℝ i (px3a_zeta d ρ) y‖ ≤ S * (ρ⁻¹) ^ i := hS ρ hρ i hij y
        have hρe : ρ ^ e ≤ ‖y‖ ^ e := Real.rpow_le_rpow_of_nonpos hy0 hyρ' hen.le
        have hρi : (ρ⁻¹) ^ i = ρ ^ (-(i : ℝ)) := by
          rw [Real.rpow_neg hρ.le, Real.rpow_natCast, inv_pow]
        rcases lt_or_eq_of_le hij with hlt | heq
        · -- `i < j`
          have hk : 1 ≤ j - i := by omega
          have h2 := norm_iteratedFDeriv_Lamhat_le hd hρ κ hk (hMb (j - i) hk) (by linarith : ρ / 4 < ‖y‖)
          set a : ℝ := (2 : ℝ) - d - ((j - i : ℕ) : ℝ) with ha
          have hae : a - i = e := by
            rw [ha, he]; push_cast [Nat.cast_sub hij]; ring
          have han : a < 0 := by
            have : (2 : ℝ) ≤ d := by exact_mod_cast hd
            have : (1 : ℝ) ≤ ((j - i : ℕ) : ℝ) := by exact_mod_cast hk
            rw [ha]; linarith
          have h3 : ‖y‖ ^ a ≤ (ρ / 2) ^ a :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hy1 han.le
          have h4 : (ρ / 2) ^ a = ρ ^ a * 2 ^ (-a) := by
            rw [Real.div_rpow hρ.le (by norm_num), Real.rpow_neg (by norm_num)]; ring
          have h5 : (2 : ℝ) ^ (-a) ≤ 2 ^ (d + j) := by
            rw [← Real.rpow_natCast]
            refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
            rw [ha]; push_cast [Nat.cast_sub hij]; nlinarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
          have h6 : ρ ^ (-(i : ℝ)) * ρ ^ a = ρ ^ e := by
            rw [← Real.rpow_add hρ]; congr 1; linarith
          have hMk : M (j - i) ≤ Mm := hMle _ (by omega)
          have hMk0 := hM0 (j - i)
          have h2p : (0 : ℝ) < 2 ^ (-a) := by positivity
          calc ‖iteratedFDeriv ℝ i (px3a_zeta d ρ) y‖ * ‖iteratedFDeriv ℝ (j - i) (Lamhat d κ ρ) y‖
              ≤ (S * ρ ^ (-(i : ℝ))) * (M (j - i) * ‖y‖ ^ a) :=
                mul_le_mul (by rw [← hρi]; exact hS1) h2 (norm_nonneg _) (by positivity)
            _ ≤ (S * ρ ^ (-(i : ℝ))) * (M (j - i) * (ρ ^ a * 2 ^ (-a))) := by
                gcongr
                rw [← h4]; exact h3
            _ = S * M (j - i) * 2 ^ (-a) * (ρ ^ (-(i : ℝ)) * ρ ^ a) := by ring
            _ = S * M (j - i) * 2 ^ (-a) * ρ ^ e := by rw [h6]
            _ ≤ S * Mm * 2 ^ (d + j) * ‖y‖ ^ e := by
                gcongr
            _ ≤ C0 * (1 + B) * ‖y‖ ^ e := by
                have h7 : S * Mm * 2 ^ (d + j) ≤ C0 := by
                  rw [hC0]
                  have : S * Mm * 2 ^ (d + j) ≤ S * (1 + Mm) * 2 ^ (d + j) := by gcongr; linarith
                  have : 0 ≤ Mm := hMm0
                  linarith
                have : C0 ≤ C0 * (1 + B) := by nlinarith
                nlinarith
        · -- `i = j`
          subst heq
          have hLam : ‖iteratedFDeriv ℝ (i - i) (Lamhat d κ ρ) y‖ = |Efund d y - κ| := by
            rw [Nat.sub_self]
            simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, LinearIsometryEquiv.norm_map]
            rw [Real.norm_eq_abs]
            simp [Lamhat, px3a_zeta_eq_zero (by linarith : ρ / 4 > 0) (by linarith : ρ / 4 ≤ ‖y‖)]
          rw [hLam]
          have h8 := hκ y hy1 hyρ'
          have h6 : ρ ^ (-(i : ℝ)) * ρ ^ ((2 : ℝ) - d) = ρ ^ e := by
            rw [← Real.rpow_add hρ]; congr 1; rw [he]; ring
          calc ‖iteratedFDeriv ℝ i (px3a_zeta d ρ) y‖ * |Efund d y - κ|
              ≤ (S * ρ ^ (-(i : ℝ))) * (B * ρ ^ ((2 : ℝ) - d)) :=
                mul_le_mul (by rw [← hρi]; exact hS1) h8 (abs_nonneg _) (by positivity)
            _ = S * B * ρ ^ e := by rw [← h6]; ring
            _ ≤ S * B * ‖y‖ ^ e := by gcongr
            _ ≤ C0 * (1 + B) * ‖y‖ ^ e := by
                have h7 : S ≤ C0 := by
                  have h9 : 0 ≤ Mm + S * (1 + Mm) * 2 ^ (d + i) := by positivity
                  rw [hC0]; linarith
                have : S * B ≤ C0 * (1 + B) := by nlinarith
                nlinarith
  calc _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (C0 * (1 + B) * ‖y‖ ^ e) :=
        Finset.sum_le_sum hterm
    _ = 2 ^ j * C0 * (1 + B) * ‖y‖ ^ e := by
        rw [← Finset.sum_mul]
        have : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = 2 ^ j := by
          exact_mod_cast Nat.sum_range_choose j
        rw [this]; ring

end HRS.Parx
