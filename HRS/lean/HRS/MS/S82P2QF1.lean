import HRS.MS.S82P2Sum3
import HRS.MS.CritForceMom5

/-!
# S8.2 (S82P2): facts about a weighted pair corrector `Q` (UNCOMPILED DRAFT)
Pointwise envelope `|Q x z| ≤ 2 A pw (1 + r^{1-s})`, the `L²(mu)` row bound
`∫ Q(x,z)² dmu(z) ≤ CQ A² jb(x)^{4M}`, and the Gaussian moment bound `∫ jb^k dmu`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

/-- elementary: `1 + r^{2-s} + [d=4]|log r| ≤ 2 (1 + r^{1-s})` for `0 < r ≤ 1`. -/
lemma s82p2_value_env {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    1 + r ^ (2 - criticalS d) + (if d = 4 then |Real.log r| else 0) ≤
      2 * (1 + r ^ (1 - criticalS d)) := by
  have h1 : r ^ (2 - criticalS d) ≤ r ^ (1 - criticalS d) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have h0 : 0 ≤ r ^ (1 - criticalS d) := Real.rpow_nonneg hr.le _
  by_cases h4 : d = 4
  · subst h4
    rw [if_pos rfl]
    have hs : criticalS 4 = 2 := by unfold criticalS; norm_num
    rw [hs] at h1 h0 ⊢
    have hlog : |Real.log r| ≤ r ^ (1 - (2 : ℝ)) := by
      have e : r ^ (1 - (2 : ℝ)) = r⁻¹ := by
        rw [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
      rw [e]
      have := Real.log_le_sub_one_of_pos (inv_pos.2 hr)
      rw [Real.log_inv] at this
      rw [abs_of_nonpos (Real.log_nonpos hr.le hr1)]
      linarith
    linarith
  · rw [if_neg h4]
    linarith

lemma s82p2_jb_rpow_nonneg {d : ℕ} (M : ℝ) (x : Euc d) : 0 ≤ jbracket x ^ M :=
  Real.rpow_nonneg (HRS.MS.S82N.s82n_jb_pos x).le _

/-- the pointwise envelope for a corrector. -/
lemma s82p2_Q_env {d : ℕ} (hd : 2 ≤ d) {a beta : ℝ} {rho : Euc d → ℝ} {M A : ℝ} (hA : 0 ≤ A)
    {f : Euc d → ℝ} {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q)
    (x z : Euc d) (hxz : x ≠ z) :
    |Q x z| ≤ A * (jbracket x ^ M * jbracket z ^ M) *
      (2 * (1 + smallRadius x z ^ (1 - criticalS d))) := by
  have h := hQ.value x z hxz
  have hr : 0 < smallRadius x z :=
    lt_min one_pos (norm_pos_iff.2 (sub_ne_zero.2 hxz))
  have hr1 : smallRadius x z ≤ 1 := min_le_left _ _
  have hApw : 0 ≤ A * (jbracket x ^ M * jbracket z ^ M) :=
    mul_nonneg hA (mul_nonneg (s82p2_jb_rpow_nonneg M x) (s82p2_jb_rpow_nonneg M z))
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_left (s82p2_value_env hd hr hr1) hApw

lemma s82p2_jb_rpow_sq {d : ℕ} (M : ℝ) (x : Euc d) :
    (jbracket x ^ M) ^ 2 = jbracket x ^ (2 * M) := by
  have hx := HRS.MS.S82N.s82n_jb_pos x
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  congr 1
  push_cast
  ring

/-- Generic weighted `L²(mu)` row bound from a pointwise envelope. -/
lemma s82p2_row_env {d : ℕ} (hd : 2 ≤ d) (M : ℝ) (hM : 0 ≤ M) (G c : ℝ) (hG : 0 < G)
    (hc : 0 < c) (rho : Euc d → ℝ)
    (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper G c rho) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ (B : ℝ), 0 ≤ B → ∀ (x : Euc d) (u : Euc d → ℝ),
      (∀ z, z ≠ x → |u z| ≤ B * (jbracket x ^ M * jbracket z ^ M) *
        (1 + smallRadius x z ^ (1 - criticalS d))) →
      ∫⁻ z, ENNReal.ofReal (u z ^ 2) ∂HRS.Whole.withDensityReal rho ≤
        ENNReal.ofReal (B ^ 2 * K0 * jbracket x ^ (4 * M)) := by
  have key := fun x : Euc d => HRS.MS.S82N.s82n_E1 hd (2 * M) G c 1 (by linarith) hG.le hc
    one_pos le_rfl rho hρ hρG x
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ, ∀ x : Euc d, ∫⁻ y, ENNReal.ofReal (jbracket y ^ (2 * M) *
      (1 + HRS.MS.S82N.s82n_smallRadius x y ^ (1 - HRS.MS.S82N.s82n_critS d)) ^ 2)
        ∂(HRS.Whole.withDensityReal rho) ≤ ENNReal.ofReal (jbracket x ^ (2 * M) * K0) :=
    ⟨_, fun x => key x⟩
  refine ⟨max K0 0, le_max_right _ _, fun B hB x u hu => ?_⟩
  have hae : ∀ᵐ z ∂HRS.Whole.withDensityReal rho, z ≠ x := by
    have := s82p2_mu_singleton hd rho x
    rw [ae_iff]
    simpa using this
  have hjx : 0 < jbracket x := HRS.MS.S82N.s82n_jb_pos x
  calc ∫⁻ z, ENNReal.ofReal (u z ^ 2) ∂HRS.Whole.withDensityReal rho
      ≤ ∫⁻ z, ENNReal.ofReal (B ^ 2 * jbracket x ^ (2 * M)) *
          ENNReal.ofReal (jbracket z ^ (2 * M) *
            (1 + HRS.MS.S82N.s82n_smallRadius x z ^ (1 - HRS.MS.S82N.s82n_critS d)) ^ 2)
          ∂HRS.Whole.withDensityReal rho := by
        refine lintegral_mono_ae (hae.mono fun z hz => ?_)
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have h1 := hu z hz
        have h2 : u z ^ 2 ≤ (B * (jbracket x ^ M * jbracket z ^ M) *
            (1 + smallRadius x z ^ (1 - criticalS d))) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        refine h2.trans (le_of_eq ?_)
        have e1 := s82p2_jb_rpow_sq M x
        have e2 := s82p2_jb_rpow_sq M z
        show (B * (jbracket x ^ M * jbracket z ^ M) *
            (1 + smallRadius x z ^ (1 - criticalS d))) ^ 2 =
          B ^ 2 * jbracket x ^ (2 * M) * (jbracket z ^ (2 * M) *
            (1 + smallRadius x z ^ (1 - criticalS d)) ^ 2)
        rw [← e1, ← e2]
        ring
    _ = ENNReal.ofReal (B ^ 2 * jbracket x ^ (2 * M)) *
          ∫⁻ z, ENNReal.ofReal (jbracket z ^ (2 * M) *
            (1 + HRS.MS.S82N.s82n_smallRadius x z ^ (1 - HRS.MS.S82N.s82n_critS d)) ^ 2)
          ∂HRS.Whole.withDensityReal rho :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (B ^ 2 * jbracket x ^ (2 * M)) *
          ENNReal.ofReal (jbracket x ^ (2 * M) * max K0 0) := by
        gcongr
        refine (hK0 x).trans (ENNReal.ofReal_le_ofReal ?_)
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) (s82p2_jb_rpow_nonneg _ x)
    _ = ENNReal.ofReal (B ^ 2 * max K0 0 * jbracket x ^ (4 * M)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have : jbracket x ^ (4 * M) = jbracket x ^ (2 * M) * jbracket x ^ (2 * M) := by
          rw [← Real.rpow_add hjx]; ring_nf
        rw [this]; ring

/-- `L²(mu)` row bound for the corrector, constant independent of the corrector. -/
lemma s82p2_Q_sq_row {d : ℕ} (hd : 2 ≤ d) (M : ℝ) (hM : 0 ≤ M) (G c : ℝ) (hG : 0 < G)
    (hc : 0 < c) (rho : Euc d → ℝ)
    (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper G c rho) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ (a beta A : ℝ), 0 ≤ A → ∀ (f : Euc d → ℝ) (Q : Euc d → Euc d → ℝ),
      PairCorrector a beta rho M A f Q → ∀ x : Euc d,
      ∫⁻ z, ENNReal.ofReal (Q x z ^ 2) ∂HRS.Whole.withDensityReal rho ≤
        ENNReal.ofReal (4 * A ^ 2 * K0 * jbracket x ^ (4 * M)) := by
  obtain ⟨K0, hK0, hrow⟩ := s82p2_row_env hd M hM G c hG hc rho hρ hρG
  refine ⟨K0, hK0, fun a beta A hA f Q hQ x => ?_⟩
  have h := hrow (2 * A) (by linarith) x (fun z => Q x z) (fun z hz => by
    have h1 := s82p2_Q_env hd hA hQ x z (Ne.symm hz)
    calc |Q x z| ≤ A * (jbracket x ^ M * jbracket z ^ M) *
          (2 * (1 + smallRadius x z ^ (1 - criticalS d))) := h1
      _ = 2 * A * (jbracket x ^ M * jbracket z ^ M) *
          (1 + smallRadius x z ^ (1 - criticalS d)) := by ring)
  calc _ ≤ ENNReal.ofReal ((2 * A) ^ 2 * K0 * jbracket x ^ (4 * M)) := h
    _ = ENNReal.ofReal (4 * A ^ 2 * K0 * jbracket x ^ (4 * M)) := by congr 1; ring

/-- Gaussian moment of the weight against the thermal measure. -/
lemma s82p2_jb_moment {d : ℕ} (hd : 2 ≤ d) (k : ℝ) (hk : 0 ≤ k) (G c : ℝ) (hG : 0 < G)
    (hc : 0 < c) (rho : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho) :
    ∫⁻ z, ENNReal.ofReal (jbracket z ^ k) ∂HRS.Whole.withDensityReal rho ≤
      ENNReal.ofReal (HRS.MS.S82N.s82n_Mom d k G c) := by
  have hjb : Measurable (fun x : Euc d => jbracket x) := by unfold jbracket; fun_prop
  have hfm : Measurable (fun x : Euc d => ENNReal.ofReal (rho x)) :=
    ENNReal.measurable_ofReal.comp hρ.measurable
  have hgm : Measurable (fun z : Euc d => ENNReal.ofReal (jbracket z ^ k)) :=
    ENNReal.measurable_ofReal.comp (hjb.pow_const k)
  unfold HRS.Whole.withDensityReal
  rw [lintegral_withDensity_eq_lintegral_mul _ hfm hgm]
  · refine le_trans ?_ (HRS.MS.S82N.s82n_mom_bound (by omega) k G c hk hG.le hc)
    refine lintegral_mono fun z => ?_
    simp only [Pi.mul_apply, Function.comp]
    rw [← ENNReal.ofReal_mul (hρ.nonneg z)]
    apply ENNReal.ofReal_le_ofReal
    have h1 := hρG.2 z
    have h2 : 0 ≤ jbracket z ^ k := s82p2_jb_rpow_nonneg k z
    calc rho z * jbracket z ^ k ≤ (G * Real.exp (-c * ‖z‖ ^ 2)) * jbracket z ^ k :=
        mul_le_mul_of_nonneg_right h1 h2
      _ = _ := rfl

end HRS.MS.S82P2
