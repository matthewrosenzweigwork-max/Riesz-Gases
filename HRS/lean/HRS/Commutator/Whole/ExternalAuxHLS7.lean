import HRS.Commutator.Whole.ExternalAuxHLS6

/-!
# Integrals and sums of the dyadic pieces (packet X-HLS, part 7)
-/

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal FourierTransform ContDiff

noncomputable section

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

/-- Schwartz functions: smooth with rapidly decaying derivatives. -/
lemma cmxHLS_schwartz_dec (g : SchwartzMap (Euc d) ℂ) :
    ContDiff ℝ ∞ (⇑g) ∧ ∀ n N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Euc d,
      (1 + ‖ξ‖) ^ N * ‖iteratedFDeriv ℝ n (⇑g) ξ‖ ≤ C := by
  refine ⟨g.smooth ⊤, fun n N => ?_⟩
  refine ⟨2 ^ N * (Finset.Iic (N, n)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g,
    mul_nonneg (by positivity) (apply_nonneg _ _), fun ξ => ?_⟩
  exact SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, n)) (k := N) (n := n)
    le_rfl le_rfl g ξ

lemma cmxHLS_pow_rpow {b : ℝ} (hb : 0 ≤ b) (n : ℕ) (e : ℝ) : (b ^ n) ^ e = (b ^ e) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hb, mul_comm, Real.rpow_mul hb, Real.rpow_natCast]

/-- The dyadic geometric weights. -/
def cmxHLS_t (e : ℝ) (m : ℕ) (j : ℤ) : ℝ := ((2 : ℝ) ^ j) ^ e * ((1 + (2 : ℝ) ^ j) ^ m)⁻¹

lemma cmxHLS_t_summable {e : ℝ} (he : 0 < e) {m : ℕ} (hm : e < m) :
    Summable (cmxHLS_t e m) := by
  refine Summable.of_nat_of_neg ?_ ?_
  · -- j = n ≥ 0
    have hg : Summable (fun n : ℕ => ((2 : ℝ) ^ (e - m)) ^ n) :=
      summable_geometric_of_lt_one (by positivity) (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
        (by linarith))
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hg
    · unfold cmxHLS_t; positivity
    · unfold cmxHLS_t
      simp only [zpow_natCast]
      have h1 : ((2 : ℝ) ^ n) ^ m ≤ (1 + (2 : ℝ) ^ n) ^ m :=
        pow_le_pow_left₀ (by positivity) (by linarith) m
      have h2 : ((1 + (2 : ℝ) ^ n) ^ m)⁻¹ ≤ (((2 : ℝ) ^ n) ^ m)⁻¹ :=
        inv_anti₀ (by positivity) h1
      calc ((2 : ℝ) ^ n) ^ e * ((1 + (2 : ℝ) ^ n) ^ m)⁻¹
          ≤ ((2 : ℝ) ^ n) ^ e * (((2 : ℝ) ^ n) ^ m)⁻¹ := by gcongr
        _ = ((2 : ℝ) ^ (e - m)) ^ n := by
            rw [cmxHLS_pow_rpow (by norm_num), Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
              Real.rpow_natCast, div_pow, div_eq_mul_inv]
            congr 2
            rw [← pow_mul, ← pow_mul, mul_comm]
  · -- j = -n
    have hg : Summable (fun n : ℕ => ((2 : ℝ) ^ (-e)) ^ n) :=
      summable_geometric_of_lt_one (by positivity) (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
        (by linarith))
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hg
    · unfold cmxHLS_t; positivity
    · unfold cmxHLS_t
      simp only [zpow_neg, zpow_natCast]
      have h1 : 1 ≤ (1 + ((2 : ℝ) ^ n)⁻¹) ^ m := one_le_pow₀ (by
        have : (0 : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹ := by positivity
        linarith)
      calc (((2 : ℝ) ^ n)⁻¹) ^ e * ((1 + ((2 : ℝ) ^ n)⁻¹) ^ m)⁻¹
          ≤ (((2 : ℝ) ^ n)⁻¹) ^ e * 1 := by
            gcongr
            exact inv_le_one_of_one_le₀ h1
        _ = ((2 : ℝ) ^ (-e)) ^ n := by
            rw [mul_one, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity),
              cmxHLS_pow_rpow (by norm_num)]


lemma cmxHLS_int_scaled {c : ℝ} (hc : 0 < c) {r : ℝ} (hr : (d : ℝ) < r) :
    Integrable (fun x : Euc d => (1 + c * ‖x‖) ^ (-r)) ∧
      ∫ x : Euc d, (1 + c * ‖x‖) ^ (-r) = (c ^ d)⁻¹ * ∫ y : Euc d, (1 + ‖y‖) ^ (-r) := by
  have hI : Integrable (fun y : Euc d => (1 + ‖y‖) ^ (-r)) :=
    integrable_one_add_norm (by rwa [finrank_euclideanSpace_fin])
  have hfun : (fun x : Euc d => (1 + c * ‖x‖) ^ (-r)) =
      fun x : Euc d => (fun y : Euc d => (1 + ‖y‖) ^ (-r)) (c • x) := by
    funext x
    simp only [norm_smul, Real.norm_of_nonneg hc.le]
  rw [hfun]
  refine ⟨hI.comp_smul hc.ne', ?_⟩
  rw [Measure.integral_comp_smul volume (fun y : Euc d => (1 + ‖y‖) ^ (-r)) c,
    finrank_euclideanSpace_fin, abs_of_pos (by positivity), smul_eq_mul]

lemma cmxHLS_sym_contDiff {f : Euc d → ℂ} (hf : ContDiff ℝ ∞ f) (s : ℝ) (j : ℤ) :
    ContDiff ℝ ∞ (cmxHLS_sym s f j) := by
  have hc : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hh : ContDiff ℝ ∞ (fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ s *
      cmxMY_rho (((2 : ℝ) ^ j)⁻¹ • ξ)) := by
    refine cmxMY_contDiff_of_away_real (E := ℝ) (r := (2 : ℝ) ^ j / 2) (by positivity)
      (fun ξ hξ => ?_) (fun ξ hξ => ?_)
    · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
      have h1 : ContDiffAt ℝ ∞ (fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ s) ξ :=
        ContDiffAt.rpow_const_of_ne (contDiffAt_const.mul (contDiffAt_norm ℝ hξ)) (by positivity)
      exact h1.mul ((cmxMY_rho_contDiff.comp (contDiff_const_smul _)).contDiffAt)
    · rw [cmxMY_rho_eq_zero_of_le, mul_zero]
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hc.le, inv_mul_le_iff₀ hc]
      linarith
  unfold cmxHLS_sym
  exact (Complex.ofRealCLM.contDiff.comp hh).mul hf

lemma cmxHLS_sym_support (s : ℝ) (f : Euc d → ℂ) (j : ℤ) (ξ : Euc d)
    (hξ : (2 : ℝ) ^ (j + 1) ≤ ‖ξ‖) : cmxHLS_sym s f j ξ = 0 := by
  have hc : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  unfold cmxHLS_sym
  rw [cmxMY_rho_eq_zero_of_ge, mul_zero]
  · simp
  · rw [norm_smul, norm_inv, Real.norm_of_nonneg hc.le, le_inv_mul_iff₀ hc]
    rw [zpow_add_one₀ (by norm_num)] at hξ
    linarith

lemma cmxHLS_sym_integrable {f : Euc d → ℂ} (hf : ContDiff ℝ ∞ f) (s : ℝ) (j : ℤ) :
    Integrable (cmxHLS_sym s f j) := by
  refine (cmxHLS_sym_contDiff hf s j).continuous.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Euc d)
    ((2 : ℝ) ^ (j + 1))) ?_
  intro ξ hξ
  by_contra h
  have h' : (2 : ℝ) ^ (j + 1) < ‖ξ‖ := by simpa using h
  exact hξ (cmxHLS_sym_support s f j ξ h'.le)

lemma cmxHLS_piece_continuous {f : Euc d → ℂ} (hf : ContDiff ℝ ∞ f) (s : ℝ) (j : ℤ) :
    Continuous (cmxHLS_piece s f j) := by
  have hI := cmxHLS_sym_integrable hf s j
  have hc : Continuous (𝓕 (cmxHLS_sym s f j)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hI
  have : cmxHLS_piece s f j = fun x => 𝓕 (cmxHLS_sym s f j) (-x) := by
    funext x; exact Real.fourierInv_eq_fourier_neg _ _
  rw [this]
  exact hc.comp continuous_neg


/-- Weighted `L¹` bound for the dyadic pieces. -/
theorem cmxHLS_piece_L1 (F : SchwartzMap (Euc d) ℂ) (s : ℝ) (N N' : ℕ) (hN : d + 1 < N)
    (hN' : 1 ≤ N') :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j : ℤ,
      Integrable (fun x : Euc d => (1 + ‖x‖) * ‖cmxHLS_piece s (⇑F) j x‖) ∧
      ∫ x : Euc d, (1 + ‖x‖) * ‖cmxHLS_piece s (⇑F) j x‖ ≤ M * cmxHLS_t (s - 1) (N' - 1) j := by
  obtain ⟨hf, hdec⟩ := cmxHLS_schwartz_dec F
  obtain ⟨M₀, hM₀, hM⟩ := cmxHLS_piece_bound hf hdec s N N'
  set r : ℝ := (N : ℝ) - 1 with hr
  have hrd : (d : ℝ) < r := by
    have : (d : ℝ) + 1 < N := by exact_mod_cast hN
    linarith
  set I : ℝ := ∫ y : Euc d, (1 + ‖y‖) ^ (-r) with hI
  have hI0 : 0 ≤ I := integral_nonneg fun y => by positivity
  refine ⟨M₀ * I, mul_nonneg hM₀ hI0, fun j => ?_⟩
  set c : ℝ := (2 : ℝ) ^ j with hc
  have hc0 : 0 < c := zpow_pos (by norm_num) j
  obtain ⟨hgi, hgint⟩ := cmxHLS_int_scaled hc0 hrd
  set K : ℝ := M₀ * c ^ s * c ^ d * ((1 + c) ^ N')⁻¹ * (1 + c⁻¹) with hK
  have hpt : ∀ x : Euc d, (1 + ‖x‖) * ‖cmxHLS_piece s (⇑F) j x‖ ≤ K * (1 + c * ‖x‖) ^ (-r) := by
    intro x
    have h1 := hM j x
    have hcx : 0 ≤ c * ‖x‖ := by positivity
    have hu : 1 ≤ 1 + c * ‖x‖ := by linarith
    have hu0 : 0 < 1 + c * ‖x‖ := by linarith
    have hr' : r = ((N - 1 : ℕ) : ℝ) := by
      rw [hr, Nat.cast_sub (by omega : 1 ≤ N)]; simp
    have e1 : (1 + c * ‖x‖) ^ (-r) = ((1 + c * ‖x‖) ^ (N - 1))⁻¹ := by
      rw [hr', Real.rpow_neg hu0.le, Real.rpow_natCast]
    rw [e1]
    -- ‖P‖ ≤ M₀ c^s c^d ((1+c)^N')⁻¹ ((1+c‖x‖)^N)⁻¹
    have hP : ‖cmxHLS_piece s (⇑F) j x‖ ≤
        M₀ * (c ^ s * c ^ d) * ((1 + c) ^ N')⁻¹ * ((1 + c * ‖x‖) ^ N)⁻¹ := by
      have hA : 0 < (1 + c) ^ N' := by positivity
      have hB : 0 < (1 + c * ‖x‖) ^ N := by positivity
      have hq : M₀ * (c ^ s * c ^ d) * ((1 + c) ^ N')⁻¹ * ((1 + c * ‖x‖) ^ N)⁻¹ =
          M₀ * (c ^ s * c ^ d) / ((1 + c) ^ N' * (1 + c * ‖x‖) ^ N) := by field_simp
      rw [hq, le_div_iff₀ (by positivity)]
      calc ‖cmxHLS_piece s (⇑F) j x‖ * ((1 + c) ^ N' * (1 + c * ‖x‖) ^ N)
          = (1 + c) ^ N' * ((1 + c * ‖x‖) ^ N * ‖cmxHLS_piece s (⇑F) j x‖) := by ring
        _ ≤ M₀ * (c ^ s * c ^ d) := h1
    have hw : 1 + ‖x‖ ≤ (1 + c⁻¹) * (1 + c * ‖x‖) := by
      have hci : 0 ≤ c⁻¹ := by positivity
      have h2 : c⁻¹ * (c * ‖x‖) = ‖x‖ := by field_simp
      nlinarith [norm_nonneg x]
    have hN1 : (1 + c * ‖x‖) ^ N = (1 + c * ‖x‖) * (1 + c * ‖x‖) ^ (N - 1) := by
      rw [← pow_succ']; congr 1; omega
    calc (1 + ‖x‖) * ‖cmxHLS_piece s (⇑F) j x‖
        ≤ ((1 + c⁻¹) * (1 + c * ‖x‖)) * (M₀ * (c ^ s * c ^ d) * ((1 + c) ^ N')⁻¹ *
            ((1 + c * ‖x‖) ^ N)⁻¹) := by
          gcongr
      _ = K * ((1 + c * ‖x‖) ^ (N - 1))⁻¹ := by
          rw [hN1, hK, mul_inv]
          field_simp
  have hmeas : AEStronglyMeasurable (fun x : Euc d => (1 + ‖x‖) * ‖cmxHLS_piece s (⇑F) j x‖) volume :=
    (((continuous_const.add continuous_norm).mul
      (cmxHLS_piece_continuous hf s j).norm)).aestronglyMeasurable
  have hint : Integrable (fun x : Euc d => K * (1 + c * ‖x‖) ^ (-r)) := hgi.const_mul K
  have hK0 : 0 ≤ K := by positivity
  refine ⟨hint.mono' hmeas (Eventually.of_forall fun x => ?_), ?_⟩
  · rw [Real.norm_of_nonneg (by positivity)]; exact hpt x
  · calc ∫ x : Euc d, (1 + ‖x‖) * ‖cmxHLS_piece s (⇑F) j x‖
        ≤ ∫ x : Euc d, K * (1 + c * ‖x‖) ^ (-r) :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) hint
            (Eventually.of_forall hpt)
      _ = K * ((c ^ d)⁻¹ * I) := by rw [integral_const_mul, hgint]
      _ = M₀ * I * cmxHLS_t (s - 1) (N' - 1) j := by
          unfold cmxHLS_t
          rw [hK, ← hc, Real.rpow_sub_one hc0.ne']
          obtain ⟨m, hm⟩ : ∃ m, N' = m + 1 := ⟨N' - 1, by omega⟩
          subst hm
          simp only [Nat.add_sub_cancel, pow_succ]
          have hc1 : (0 : ℝ) < 1 + c := by linarith
          have hcd : c ^ d ≠ 0 := by positivity
          have hm1 : (1 + c) ^ m ≠ 0 := by positivity
          field_simp
          ring


/-- The pointwise bound for the dyadic pieces in division form. -/
lemma cmxHLS_piece_pt {f : Euc d → ℂ} (hf : ContDiff ℝ ∞ f)
    (hdec : ∀ n N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ, (1 + ‖ξ‖) ^ N * ‖iteratedFDeriv ℝ n f ξ‖ ≤ C)
    (s : ℝ) (N N' : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (j : ℤ) (x : Euc d),
      ‖cmxHLS_piece s f j x‖ ≤ M * (((2 : ℝ) ^ j) ^ s * ((2 : ℝ) ^ j) ^ d) *
        ((1 + (2 : ℝ) ^ j) ^ N')⁻¹ * ((1 + (2 : ℝ) ^ j * ‖x‖) ^ N)⁻¹ := by
  obtain ⟨M, hM0, hM⟩ := cmxHLS_piece_bound hf hdec s N N'
  refine ⟨M, hM0, fun j x => ?_⟩
  have hc0 : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hq : M * (((2 : ℝ) ^ j) ^ s * ((2 : ℝ) ^ j) ^ d) * ((1 + (2 : ℝ) ^ j) ^ N')⁻¹ *
      ((1 + (2 : ℝ) ^ j * ‖x‖) ^ N)⁻¹ =
      M * (((2 : ℝ) ^ j) ^ s * ((2 : ℝ) ^ j) ^ d) /
        ((1 + (2 : ℝ) ^ j) ^ N' * (1 + (2 : ℝ) ^ j * ‖x‖) ^ N) := by field_simp
  have hA : 0 < (1 + (2 : ℝ) ^ j) ^ N' := by positivity
  have hB : 0 < (1 + (2 : ℝ) ^ j * ‖x‖) ^ N := by positivity
  rw [hq, le_div_iff₀ (by positivity)]
  calc ‖cmxHLS_piece s f j x‖ * ((1 + (2 : ℝ) ^ j) ^ N' * (1 + (2 : ℝ) ^ j * ‖x‖) ^ N)
      = (1 + (2 : ℝ) ^ j) ^ N' * ((1 + (2 : ℝ) ^ j * ‖x‖) ^ N * ‖cmxHLS_piece s f j x‖) := by ring
    _ ≤ M * (((2 : ℝ) ^ j) ^ s * ((2 : ℝ) ^ j) ^ d) := hM j x

lemma cmxHLS_alg_Lr {M₀ I c s : ℝ} {d : ℕ} {r : ℝ} (hM₀ : 0 ≤ M₀) (hI : 0 ≤ I) (hc : 0 < c)
    (hr : 0 < r) (B : ℝ) (hB : 0 < B) :
    (M₀ * (c ^ s * c ^ d) * B⁻¹) ^ r * ((c ^ d)⁻¹ * I) =
      ((M₀ * I ^ (1 / r)) * (c ^ (s + d - d / r) * B⁻¹)) ^ r := by
  have h1 : c ^ d = c ^ (d : ℝ) := (Real.rpow_natCast c d).symm
  have e1 : (c ^ s * c ^ (d : ℝ)) ^ r = c ^ ((s + d) * r) := by
    rw [← Real.rpow_add hc, ← Real.rpow_mul hc.le]
  have e2 : (c ^ (s + d - d / r)) ^ r = c ^ ((s + d) * r) / c ^ (d : ℝ) := by
    rw [← Real.rpow_mul hc.le, ← Real.rpow_sub hc]
    congr 1
    field_simp
  have e3 : (I ^ (1 / r)) ^ r = I := by
    rw [← Real.rpow_mul hI, one_div_mul_cancel hr.ne', Real.rpow_one]
  have hcd : c ^ (d : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  have L : (M₀ * (c ^ s * c ^ (d : ℝ)) * B⁻¹) ^ r = M₀ ^ r * c ^ ((s + d) * r) * (B⁻¹) ^ r := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity), e1]
  have R : ((M₀ * I ^ (1 / r)) * (c ^ (s + d - d / r) * B⁻¹)) ^ r =
      M₀ ^ r * I * (c ^ ((s + d) * r) / c ^ (d : ℝ)) * (B⁻¹) ^ r := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity), e3, e2]
    ring
  rw [h1, L, R]
  field_simp

/-- `L^r` bound for the dyadic pieces. -/
theorem cmxHLS_piece_Lr (F : SchwartzMap (Euc d) ℂ) (s : ℝ) (N N' : ℕ) (hN : d + 1 < N)
    {r : ℝ} (hr : 1 ≤ r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j : ℤ,
      ∫⁻ x : Euc d, ‖cmxHLS_piece s (⇑F) j x‖ₑ ^ r ≤
        ENNReal.ofReal ((M * cmxHLS_t (s + d - d / r) N' j) ^ r) := by
  obtain ⟨hf, hdec⟩ := cmxHLS_schwartz_dec F
  obtain ⟨M₀, hM₀, hM⟩ := cmxHLS_piece_pt hf hdec s N N'
  have hr0 : 0 < r := by linarith
  have hNr : (d : ℝ) < N * r := by
    have : (d : ℝ) + 1 < N := by exact_mod_cast hN
    nlinarith
  set I : ℝ := ∫ y : Euc d, (1 + ‖y‖) ^ (-((N : ℝ) * r)) with hI
  have hI0 : 0 ≤ I := integral_nonneg fun y => by positivity
  refine ⟨M₀ * I ^ (1 / r), mul_nonneg hM₀ (Real.rpow_nonneg hI0 _), fun j => ?_⟩
  set c : ℝ := (2 : ℝ) ^ j with hc
  have hc0 : 0 < c := zpow_pos (by norm_num) j
  obtain ⟨hgi, hgint⟩ := cmxHLS_int_scaled hc0 hNr
  set Kg : ℝ := M₀ * (c ^ s * c ^ d) * ((1 + c) ^ N')⁻¹ with hKg
  have hKg0 : 0 ≤ Kg := by positivity
  have hpt : ∀ x : Euc d, ‖cmxHLS_piece s (⇑F) j x‖ ^ r ≤ Kg ^ r * (1 + c * ‖x‖) ^ (-((N : ℝ) * r)) := by
    intro x
    have h1 := hM j x
    have hu0 : 0 < 1 + c * ‖x‖ := by have : 0 ≤ c * ‖x‖ := by positivity
                                     linarith
    have h2 : ‖cmxHLS_piece s (⇑F) j x‖ ≤ Kg * (1 + c * ‖x‖) ^ (-(N : ℝ)) := by
      rw [Real.rpow_neg hu0.le, Real.rpow_natCast]
      exact h1
    calc ‖cmxHLS_piece s (⇑F) j x‖ ^ r ≤ (Kg * (1 + c * ‖x‖) ^ (-(N : ℝ))) ^ r :=
          Real.rpow_le_rpow (norm_nonneg _) h2 hr0.le
      _ = Kg ^ r * (1 + c * ‖x‖) ^ (-((N : ℝ) * r)) := by
          rw [Real.mul_rpow hKg0 (by positivity), ← Real.rpow_mul hu0.le]
          congr 2; ring
  have hpos : ∀ x : Euc d, 0 ≤ Kg ^ r * (1 + c * ‖x‖) ^ (-((N : ℝ) * r)) := fun x => by positivity
  calc ∫⁻ x : Euc d, ‖cmxHLS_piece s (⇑F) j x‖ₑ ^ r
      = ∫⁻ x : Euc d, ENNReal.ofReal (‖cmxHLS_piece s (⇑F) j x‖ ^ r) :=
        lintegral_congr fun x => by
          rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le]
    _ ≤ ∫⁻ x : Euc d, ENNReal.ofReal (Kg ^ r * (1 + c * ‖x‖) ^ (-((N : ℝ) * r))) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpt x)
    _ = ENNReal.ofReal (∫ x : Euc d, Kg ^ r * (1 + c * ‖x‖) ^ (-((N : ℝ) * r))) :=
        (ofReal_integral_eq_lintegral_ofReal (hgi.const_mul _)
          (Eventually.of_forall hpos)).symm
    _ = ENNReal.ofReal (Kg ^ r * ((c ^ d)⁻¹ * I)) := by rw [integral_const_mul, hgint]
    _ = ENNReal.ofReal ((M₀ * I ^ (1 / r) * cmxHLS_t (s + d - d / r) N' j) ^ r) := by
        unfold cmxHLS_t
        rw [← hc, hKg, cmxHLS_alg_Lr hM₀ hI0 hc0 hr0 _ (by positivity)]

end HRS.Commutator.Whole
