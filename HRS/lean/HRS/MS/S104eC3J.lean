import HRS.MS.S104eC3I

/-!
# S104E route C, packet C3, file J: the mild equation for the limit, existence and uniqueness
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Interval

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.R2WinOrbNL

variable {d : ℕ} {j : ℕ} {η H : ℝ} {P A : ℝ → (Euc d → ℝ) → Euc d → ℝ}

/-- Choice of the exponential weight with `θ(λ) ≤ 1/2`. -/
theorem s104c3_exists_lam (hyp : VolHyp d j η H P A) (hη0 : 0 < η) (hη1 : η < 1) (hH : 0 < H) :
    ∃ lam : ℝ, 0 ≤ lam ∧ s104c3_theta hyp lam ≤ 1 / 2 := by
  have ha : 0 ≤ hyp.CP * hyp.CA := mul_nonneg (by linarith [hyp.CP1]) hyp.CA0
  obtain ⟨lam, hlam, hint⟩ := s104c3_k_small hη1 hη0 hH (θ := 1 / (2 * (hyp.CP * hyp.CA + 1)))
    (by positivity)
  refine ⟨lam, hlam, ?_⟩
  unfold s104c3_theta
  calc hyp.CP * hyp.CA * ∫ h in (0 : ℝ)..H, s104c3_k η h * Real.exp (-lam * h)
      ≤ hyp.CP * hyp.CA * (1 / (2 * (hyp.CP * hyp.CA + 1))) := mul_le_mul_of_nonneg_left hint ha
    _ ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith

/-- The limit satisfies the mild equation. -/
theorem s104c3_mild (hyp : VolHyp d j η H P A) (hη0 : 0 < η) (hη1 : η < 1) {t : ℝ}
    (ht : t ∈ Icc 0 H) {lam : ℝ} (hlam : 0 ≤ lam) (hθ : s104c3_theta hyp lam ≤ 1 / 2) {B : ℝ}
    {ψ : Euc d → ℝ} (hψ : HolB j η B ψ) (hψv : VanB (j + 1) ψ) {w : ℝ → Euc d → ℝ}
    (hb : ∀ r ∈ Icc 0 t, HolB j η (2 * hyp.CP * B * Real.exp (lam * (t - r))) (w r))
    (hd : ∀ r ∈ Icc 0 t, ∀ n : ℕ, HolB j η (hyp.CP * B * (1 / 2) ^ n * Real.exp (lam * (t - r)))
      (fun x => w r x - s104c3_seq P A t ψ n r x))
    (hTC : s104c3_TC t (j + 1) w)
    (hL : ∀ r ∈ Icc 0 t, ∀ x, Tendsto (fun n => s104c3_seq P A t ψ n r x) atTop (𝓝 (w r x))) :
    ∀ r ∈ Icc 0 t, ∀ x, w r x = P (t - r) ψ x + s104c3_Phi P A t w r x := by
  intro r hr x
  have hCP : 0 < hyp.CP := by linarith [hyp.CP1]
  have hB : 0 ≤ B := s104c3_HolB_nonneg hψ
  have props := s104c3_seq_props hyp hη0 hη1 ht hlam hθ hψ hψv
  set S := s104c3_seq P A t ψ with hS
  have hE0 : ∀ r : ℝ, 0 < Real.exp (lam * (t - r)) := fun r => Real.exp_pos _
  have h0 : 0 ≤ hyp.CP * B := mul_nonneg hCP.le hB
  have hwcd : ∀ v ∈ Icc 0 t, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (w v) := fun v hv => (hb v hv).1.1
  have hwc := s104c3_jets_cont_of_TC hTC hwcd
  have hw' : ∀ v ∈ Icc 0 t, HolB j η ((2 * (hyp.CP * B)) * Real.exp (lam * (t - v))) (w v) := fun v hv =>
    (hb v hv).mono_B (le_of_eq (by ring)) hη0.le
  have key : ∀ n : ℕ, |w r x - (P (t - r) ψ x + s104c3_Phi P A t w r x)| ≤
      hyp.CP * B * Real.exp (lam * (t - r)) * (1 / 2) ^ n := by
    intro n
    have hSn : ∀ v ∈ Icc 0 t, HolB j η ((2 * (hyp.CP * B)) * Real.exp (lam * (t - v))) (S n v) := by
      intro v hv
      refine ((props n).1 v hv).mono_B ?_ hη0.le
      have : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
      nlinarith [mul_nonneg h0 this, hE0 v, mul_nonneg (mul_nonneg h0 this) (hE0 v).le]
    have hScd : ∀ v ∈ Icc 0 t, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (S n v) :=
      fun v hv => ((props n).1 v hv).1.1
    have hSc := s104c3_jets_cont_of_TC (props n).2.1 hScd
    -- the difference family
    have hdn : ∀ v ∈ Icc 0 t, HolB j η ((hyp.CP * B * (1 / 2) ^ n) * Real.exp (lam * (t - v)))
        (fun y => w v y - S n v y) := fun v hv => hd v hv n
    have hdcd : ∀ v ∈ Icc 0 t, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (fun y => w v y - S n v y) :=
      fun v hv => (hdn v hv).1.1
    have hTCd : s104c3_TC t (j + 1) (fun v y => w v y - S n v y) := by
      have e : (fun v y => w v y - S n v y) = fun v y => -1 * S n v y + w v y := by
        funext v y; ring
      rw [e]
      exact s104c3_TC_lin (-1) hScd hwcd (props n).2.1 hTC
    have hdc := s104c3_jets_cont_of_TC hTCd hdcd
    have hΦ := (s104c3_duhamel hyp hη0 hη1 ht hlam hdn hdc r hr).2.2.2
    have hΦ0 : ‖s104c3_Phi P A t (fun v y => w v y - S n v y) r x‖ ≤
        s104c3_theta hyp lam * (hyp.CP * B * (1 / 2) ^ n) * Real.exp (lam * (t - r)) := by
      have := hΦ.1.2 0 (Nat.zero_le _) x
      rwa [norm_iteratedFDeriv_zero] at this
    have hsub := s104c3_phi_sub hyp hη0 hη1 ht hlam hSn hw' hSc hwc hr x
    rw [hsub] at hΦ0
    have h1 := (hd r hr (n + 1)).1.2 0 (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero] at h1
    have e : S (n + 1) r x = P (t - r) ψ x + s104c3_Phi P A t (S n) r x := rfl
    rw [e] at h1
    have hpos : 0 ≤ hyp.CP * B * (1 / 2) ^ n * Real.exp (lam * (t - r)) := by positivity
    have hθ' : s104c3_theta hyp lam * (hyp.CP * B * (1 / 2) ^ n) * Real.exp (lam * (t - r)) ≤
        1 / 2 * (hyp.CP * B * (1 / 2) ^ n) * Real.exp (lam * (t - r)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hθ (by positivity)) (hE0 r).le
    have htri : |w r x - (P (t - r) ψ x + s104c3_Phi P A t w r x)| ≤
        |w r x - (P (t - r) ψ x + s104c3_Phi P A t (S n) r x)| +
        |s104c3_Phi P A t w r x - s104c3_Phi P A t (S n) r x| := by
      have : w r x - (P (t - r) ψ x + s104c3_Phi P A t w r x) =
          (w r x - (P (t - r) ψ x + s104c3_Phi P A t (S n) r x)) -
          (s104c3_Phi P A t w r x - s104c3_Phi P A t (S n) r x) := by ring
      rw [this]; exact abs_sub _ _
    rw [Real.norm_eq_abs] at hΦ0
    rw [Real.norm_eq_abs] at h1
    have : hyp.CP * B * (1 / 2) ^ (n + 1) * Real.exp (lam * (t - r)) =
        1 / 2 * (hyp.CP * B * (1 / 2) ^ n * Real.exp (lam * (t - r))) := by ring
    nlinarith
  have hlim : Tendsto (fun n : ℕ => hyp.CP * B * Real.exp (lam * (t - r)) * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (hyp.CP * B * Real.exp (lam * (t - r)))
  have := ge_of_tendsto' hlim key
  have h2 : |w r x - (P (t - r) ψ x + s104c3_Phi P A t w r x)| = 0 :=
    le_antisymm this (abs_nonneg _)
  have := abs_eq_zero.1 h2
  linarith

/-- Existence (Picard iteration with exponential weight). -/
theorem c3_volterra_exists (j : ℕ) (η H : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hH : 0 < H)
    (P A : ℝ → (Euc d → ℝ) → Euc d → ℝ) (hyp : VolHyp d j η H P A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ), t ∈ Icc 0 H → ∀ (B : ℝ) (ψ : Euc d → ℝ), HolB j η B ψ →
      VanB (j + 1) ψ →
      ∃ w : ℝ → Euc d → ℝ, (∀ r ∈ Icc 0 t, HolB j η (C * B) (w r)) ∧ w t = ψ ∧
        (∀ i ≤ j + 1, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (w p.1) p.2)
          (Icc 0 t ×ˢ univ)) ∧
        (∀ r ∈ Icc 0 t, ∀ x, w r x = P (t - r) ψ x + ∫ v in r..t, P (v - r) (A v (w v)) x) ∧
        (∀ r ∈ Icc 0 t, VanB (j + 1) (w r)) ∧
        (∀ i ≤ j + 1, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Icc 0 t, ∀ r' ∈ Icc 0 t, |r - r'| < δ →
          ∀ x : Euc d, ‖iteratedFDeriv ℝ i (w r) x - iteratedFDeriv ℝ i (w r') x‖ ≤ ε) := by
  obtain ⟨lam, hlam, hθ⟩ := s104c3_exists_lam hyp hη0 hη1 hH
  have hCP : 0 < hyp.CP := by linarith [hyp.CP1]
  refine ⟨2 * hyp.CP * Real.exp (lam * H), by positivity, fun t ht B ψ hψ hψv => ?_⟩
  obtain ⟨w, hb, hd, hTC, hwv, hL⟩ := s104c3_limit hyp hη0 hη1 ht hlam hθ hψ hψv
  have hB : 0 ≤ B := s104c3_HolB_nonneg hψ
  have hbC : ∀ r ∈ Icc 0 t, HolB j η (2 * hyp.CP * Real.exp (lam * H) * B) (w r) := by
    intro r hr
    refine (hb r hr).mono_B ?_ hη0.le
    have hex : Real.exp (lam * (t - r)) ≤ Real.exp (lam * H) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [hr.1, ht.2]) hlam)
    have : 0 ≤ 2 * hyp.CP * B := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hex this]
  have hmild := s104c3_mild hyp hη0 hη1 ht hlam hθ hψ hψv hb hd hTC hL
  have hwcd : ∀ v ∈ Icc 0 t, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (w v) := fun v hv => (hb v hv).1.1
  refine ⟨w, hbC, ?_, s104c3_jets_cont_of_TC hTC hwcd, ?_, hwv, hTC⟩
  · funext x
    have := hmild t ⟨ht.1, le_rfl⟩ x
    rw [this]
    simp [s104c3_Phi, sub_self, hyp.P_zero]
  · intro r hr x
    exact hmild r hr x


/-- Uniqueness among families with `HolB`-bounded values and continuous jets. -/
theorem c3_volterra_unique (j : ℕ) (η H : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hH : 0 < H)
    (P A : ℝ → (Euc d → ℝ) → Euc d → ℝ) (hyp : VolHyp d j η H P A) {t : ℝ} (ht : t ∈ Icc 0 H)
    {ψ : Euc d → ℝ} {w w' : ℝ → Euc d → ℝ} {B B' : ℝ}
    (hw : ∀ r ∈ Icc 0 t, HolB j η B (w r)) (hw' : ∀ r ∈ Icc 0 t, HolB j η B' (w' r))
    (hwc : ∀ i ≤ j + 1, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (w p.1) p.2)
      (Icc 0 t ×ˢ univ))
    (hwc' : ∀ i ≤ j + 1, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (w' p.1) p.2)
      (Icc 0 t ×ˢ univ))
    (hm : ∀ r ∈ Icc 0 t, ∀ x, w r x = P (t - r) ψ x + ∫ v in r..t, P (v - r) (A v (w v)) x)
    (hm' : ∀ r ∈ Icc 0 t, ∀ x, w' r x = P (t - r) ψ x + ∫ v in r..t, P (v - r) (A v (w' v)) x) :
    ∀ r ∈ Icc 0 t, w r = w' r := by
  obtain ⟨lam, hlam, hθ⟩ := s104c3_exists_lam hyp hη0 hη1 hH
  have hB : 0 ≤ B := by
    have := s104c3_HolB_nonneg (hw t ⟨ht.1, le_rfl⟩); exact this
  have hB' : 0 ≤ B' := s104c3_HolB_nonneg (hw' t ⟨ht.1, le_rfl⟩)
  have hE1 : ∀ r ∈ Icc 0 t, 1 ≤ Real.exp (lam * (t - r)) := fun r hr =>
    Real.one_le_exp (mul_nonneg hlam (by linarith [hr.2]))
  have hE0 : ∀ r : ℝ, 0 < Real.exp (lam * (t - r)) := fun r => Real.exp_pos _
  have hwE : ∀ v ∈ Icc 0 t, HolB j η (B * Real.exp (lam * (t - v))) (w v) := fun v hv =>
    (hw v hv).mono_B (by nlinarith [hE1 v hv]) hη0.le
  have hwE' : ∀ v ∈ Icc 0 t, HolB j η (B' * Real.exp (lam * (t - v))) (w' v) := fun v hv =>
    (hw' v hv).mono_B (by nlinarith [hE1 v hv]) hη0.le
  have hwcd : ∀ v ∈ Icc 0 t, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (w v) := fun v hv => (hw v hv).1.1
  have hwcd' : ∀ v ∈ Icc 0 t, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (w' v) := fun v hv => (hw' v hv).1.1
  -- the difference family
  have hu : ∀ v ∈ Icc 0 t, HolB j η ((B + B') * Real.exp (lam * (t - v))) (fun y => w' v y - w v y) :=
    fun v hv => (s104c3_HolB_sub (hw v hv) (hw' v hv)).mono_B (by nlinarith [hE1 v hv]) hη0.le
  have huc : ∀ i ≤ j + 1, ContinuousOn
      (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (fun y => w' p.1 y - w p.1 y) p.2) (Icc 0 t ×ˢ univ) := by
    have h := s104c3_jets_lin (-1) hwcd hwcd' hwc hwc'
    intro i hi
    refine (h i hi).congr fun p hp => ?_
    have e : (fun y => w' p.1 y - w p.1 y) = fun y => -1 * w p.1 y + w' p.1 y := by funext y; ring
    rw [e]
  have key : ∀ r ∈ Icc 0 t, (fun y => w' r y - w r y) = s104c3_Phi P A t (fun v y => w' v y - w v y) r := by
    intro r hr
    funext x
    rw [s104c3_phi_sub hyp hη0 hη1 ht hlam hwE hwE' hwc hwc' hr x]
    have h1 := hm r hr x
    have h2 := hm' r hr x
    simp only [s104c3_Phi]
    linarith
  have hn : ∀ n : ℕ, ∀ r ∈ Icc 0 t,
      HolB j η ((B + B') * (1 / 2) ^ n * Real.exp (lam * (t - r))) (fun y => w' r y - w r y) := by
    intro n
    induction n with
    | zero => intro r hr; simpa using hu r hr
    | succ n ih =>
      intro r hr
      have hh := s104c3_halve hyp hη0 hη1 ht hlam hθ (N := (B + B') * (1 / 2) ^ n)
        (by positivity) (u := fun v y => w' v y - w v y) ih huc r hr
      rw [key r hr]
      refine hh.mono_B (le_of_eq ?_) hη0.le
      ring
  intro r hr
  funext x
  have hb : ∀ n : ℕ, |w' r x - w r x| ≤ (B + B') * Real.exp (lam * (t - r)) * (1 / 2) ^ n := by
    intro n
    have := (hn n r hr).1.2 0 (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    refine this.trans (le_of_eq ?_)
    ring
  have hlim : Tendsto (fun n : ℕ => (B + B') * Real.exp (lam * (t - r)) * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul ((B + B') * Real.exp (lam * (t - r)))
  have h0 := ge_of_tendsto' hlim hb
  have := abs_eq_zero.1 (le_antisymm h0 (abs_nonneg _))
  linarith

end HRS.MS.S104e.C
