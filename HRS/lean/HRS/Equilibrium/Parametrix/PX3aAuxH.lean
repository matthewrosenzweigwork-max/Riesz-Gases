import HRS.Equilibrium.Parametrix.PX3aAuxG

/-!
# Packet PX3a auxiliaries H: the near/far splitting of the Newton potential
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma Ln_measurable (κ ρ : ℝ) : Measurable (Ln d κ ρ) :=
  ((px3a_zeta_contDiff (d := d) ρ 0).continuous.measurable).mul (measurable_Efund.sub measurable_const)

lemma Lf_measurable {ρ : ℝ} (hρ : 0 < ρ) (κ : ℝ) : Measurable (Lf d κ ρ) :=
  (Lf_contDiff hρ κ 0).continuous.measurable

lemma Ln_integrable (hd : 2 ≤ d) {ρ : ℝ} (hρ : 0 < ρ) (κ : ℝ) : Integrable (Ln d κ ρ) := by
  have hsupp : Function.support (Ln d κ ρ) ⊆ Metric.ball (0 : Euc d) ρ := by
    intro y hy
    rw [Metric.mem_ball, dist_zero_right]
    by_contra hh
    exact hy (by simp [Ln, px3a_zeta_eq_zero hρ (not_lt.mp hh)])
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  have hE : IntegrableOn (Efund d) (Metric.ball (0 : Euc d) ρ) :=
    (locallyIntegrable_Efund hd).integrableOn_isCompact (isCompact_closedBall _ _) |>.mono_set
      Metric.ball_subset_closedBall
  have hb : IntegrableOn (fun y => ‖Efund d y‖ + |κ|) (Metric.ball (0 : Euc d) ρ) :=
    hE.norm.add (integrableOn_const measure_ball_lt_top.ne)
  refine hb.mono' ((Ln_measurable κ ρ).aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
  have h0 := px3a_zeta_nonneg (d := d) ρ y
  have h1 := px3a_zeta_le_one (d := d) ρ y
  simp only [Ln, norm_mul, Real.norm_of_nonneg h0]
  calc px3a_zeta d ρ y * ‖Efund d y - κ‖ ≤ 1 * ‖Efund d y - κ‖ := by gcongr
    _ ≤ ‖Efund d y‖ + |κ| := by
        rw [one_mul]
        exact (norm_sub_le _ _).trans (by simp)

lemma Lf_bdd {ρ : ℝ} (hρ : 0 < ρ) (κ : ℝ) : ∃ C : ℝ, ∀ y, ‖Lf d κ ρ y‖ ≤ C := by
  exact (Lf_contDiff hρ κ 0).continuous.bounded_above_of_compact_support (Lf_hasCompactSupport ρ κ)

lemma newtonPot_split (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) {b m : ℕ} {A : ℝ} (hA : 0 ≤ A)
    {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g) {r : ℝ} (hr : 0 < r) (hr1 : r < 1 / 8)
    {z0 : Euc d} (hz0 : ‖z0‖ = r) {p : Euc d × Euc d} (hp : ‖p.2 - z0‖ < r / 16) (κ : ℝ) :
    Integrable (fun u => Ln d κ (r / 8) u * g (p.1, p.2 - u)) ∧
    Integrable (fun w => Lf d κ (r / 8) (p.2 - w) * g (p.1, w)) ∧
    newtonPot d g p = κ * (∫ w, g (p.1, w)) + (∫ u, Ln d κ (r / 8) u * g (p.1, p.2 - u)) +
      ∫ w, Lf d κ (r / 8) (p.2 - w) * g (p.1, w) := by
  have hρ : 0 < r / 8 := by positivity
  have hd1 : 1 ≤ d := by omega
  have hgi := h.slice_integrable hd1 hσ p.1
  have hp2 : ‖p.2‖ < 1 / 4 := by
    have := norm_sub_norm_le p.2 z0
    linarith
  -- far piece
  obtain ⟨C, hC⟩ := Lf_bdd hρ κ
  have hLfi : Integrable (fun w => Lf d κ (r / 8) (p.2 - w) * g (p.1, w)) :=
    hgi.bdd_mul ((Lf_measurable hρ κ).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun w => hC _)
  -- near piece
  obtain ⟨M, hM0, hM⟩ := h.full_bound hA (k := 0) (Nat.zero_le m) (ρ0 := r / 2) (by positivity)
  have hnear_bd : ∀ u : Euc d, ‖u‖ < r / 8 → |g (p.1, p.2 - u)| ≤ M := by
    intro u hu
    have h1 : r / 2 ≤ ‖p.2 - u‖ := by
      have : ‖p.2‖ ≥ ‖z0‖ - ‖p.2 - z0‖ := by
        have := norm_sub_norm_le z0 p.2
        rw [norm_sub_rev] at this; linarith
      have h2 := norm_sub_norm_le p.2 u
      linarith
    have := hM (p.1, p.2 - u) h1
    simpa [norm_iteratedFDeriv_zero] using this
  have hgaes : AEStronglyMeasurable (fun u => g (p.1, p.2 - u)) (volume : Measure (Euc d)) :=
    (h.slice_aesm hd1 p.1).comp_measurePreserving (Measure.measurePreserving_sub_left volume p.2)
  have hLni : Integrable (fun u => Ln d κ (r / 8) u * g (p.1, p.2 - u)) := by
    refine ((Ln_integrable hd hρ κ).norm.mul_const M).mono'
      ((Ln_measurable κ (r / 8)).aestronglyMeasurable.mul hgaes) (Eventually.of_forall fun u => ?_)
    by_cases hu : ‖u‖ < r / 8
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (by simpa using hnear_bd u hu) (norm_nonneg _)
    · simp [Ln, px3a_zeta_eq_zero hρ (not_lt.mp hu)]
  have hLnw : Integrable (fun w => Ln d κ (r / 8) (p.2 - w) * g (p.1, w)) := by
    have := hLni.comp_sub_left p.2
    refine this.congr (Eventually.of_forall fun w => ?_)
    simp
  have hpt : ∀ w : Euc d, Efund d (p.2 - w) * g (p.1, w) =
      κ * g (p.1, w) + Ln d κ (r / 8) (p.2 - w) * g (p.1, w) + Lf d κ (r / 8) (p.2 - w) * g (p.1, w) := by
    intro w
    by_cases hw : 1 / 16 < ‖w‖
    · simp [h.supp p.1 w hw]
    · have hw' : ‖w‖ ≤ 1 / 16 := not_lt.mp hw
      have h1 : px3a_zeta d 1 (p.2 - w) = 1 :=
        px3a_zeta_eq_one one_pos (by have := norm_sub_le p.2 w; linarith)
      simp only [Ln, Lf, h1]
      ring
  refine ⟨hLni, hLfi, ?_⟩
  unfold newtonPot
  have hsw : ∫ w, Ln d κ (r / 8) (p.2 - w) * g (p.1, w) =
      ∫ u, Ln d κ (r / 8) u * g (p.1, p.2 - u) := by
    have := integral_sub_left_eq_self (fun u => Ln d κ (r / 8) u * g (p.1, p.2 - u)) volume p.2
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp
  have i1 : ∫ w, (κ * g (p.1, w) + Ln d κ (r / 8) (p.2 - w) * g (p.1, w) +
      Lf d κ (r / 8) (p.2 - w) * g (p.1, w)) =
      (∫ w, (κ * g (p.1, w) + Ln d κ (r / 8) (p.2 - w) * g (p.1, w))) +
        ∫ w, Lf d κ (r / 8) (p.2 - w) * g (p.1, w) :=
    integral_add ((hgi.const_mul κ).add hLnw) hLfi
  have i2 : ∫ w, (κ * g (p.1, w) + Ln d κ (r / 8) (p.2 - w) * g (p.1, w)) =
      (∫ w, κ * g (p.1, w)) + ∫ w, Ln d κ (r / 8) (p.2 - w) * g (p.1, w) :=
    integral_add (hgi.const_mul κ) hLnw
  rw [integral_congr_ae (Eventually.of_forall hpt), i1, i2, integral_const_mul, hsw]

lemma isOpen_near (z0 : Euc d) (R : ℝ) : IsOpen {p : Euc d × Euc d | ‖p.2 - z0‖ < R} :=
  isOpen_lt (continuous_norm.comp (continuous_snd.sub continuous_const)) continuous_const

/-- Smoothness and derivative formulas for the Newton potential modulo the constant `κ ∫ g`. -/
theorem newtonPot_FL (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) {b m : ℕ} {A : ℝ} (hA : 0 ≤ A)
    {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g) {r : ℝ} (hr : 0 < r) (hr1 : r < 1 / 8)
    {z0 : Euc d} (hz0 : ‖z0‖ = r) (κ : ℝ) :
    ContDiffOn ℝ (m : WithTop ℕ∞) (fun p => newtonPot d g p - κ * ∫ w, g (p.1, w))
      {p : Euc d × Euc d | ‖p.2 - z0‖ < r / 16} ∧
    (∀ k ≤ m, ∀ p : Euc d × Euc d, ‖p.2 - z0‖ < r / 16 →
      iteratedFDeriv ℝ k (fun p' => newtonPot d g p' - κ * ∫ w, g (p'.1, w)) p =
        (∫ u, Ln d κ (r / 8) u • iteratedFDeriv ℝ k g (p.1, p.2 - u)) +
        ∫ w, iteratedFDeriv ℝ k (fun q : Euc d × Euc d => Lf d κ (r / 8) (q.2 - w) * g (q.1, w)) p) ∧
    (∀ k ≤ m, ∀ p : Euc d × Euc d, ‖p.2 - z0‖ < r / 16 →
      Integrable (fun u => Ln d κ (r / 8) u • iteratedFDeriv ℝ k g (p.1, p.2 - u)) ∧
      Integrable (fun w => iteratedFDeriv ℝ k
        (fun q : Euc d × Euc d => Lf d κ (r / 8) (q.2 - w) * g (q.1, w)) p)) := by
  have hρ : 0 < r / 8 := by positivity
  have hd1 : 1 ≤ d := by omega
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  set U' : Set (Euc d × Euc d) := {p | ‖p.2 - z0‖ < r / 16} with hU'
  have hU'o : IsOpen U' := isOpen_near z0 _
  -- near piece
  have hnear := near_param (g := g) (V := {p : Euc d × Euc d | p.2 ≠ 0}) isOpen_ne_snd h.smooth
    (Ln_measurable κ (r / 8)) (Ln_integrable hd hρ κ) hU'o
    (fun p hp u hu => by
      have hu' : ‖u‖ < r / 8 := by
        by_contra hh
        exact hu (by simp [Ln, px3a_zeta_eq_zero hρ (not_lt.mp hh)])
      show p.2 - u ≠ 0
      intro h0
      have h1 : ‖p.2 - z0‖ < r / 16 := hp
      have h2 : ‖z0‖ ≤ ‖p.2 - z0‖ + ‖p.2‖ := by
        have := norm_sub_le p.2 (p.2 - z0); rw [sub_sub_cancel] at this; linarith
      have h3 : ‖p.2‖ = ‖u‖ := by rw [sub_eq_zero.mp h0]
      linarith)
    (fun k hk => by
      obtain ⟨M, hM0, hM⟩ := h.full_bound hA hk (ρ0 := r / 2) (by positivity)
      refine ⟨M, fun p hp u hu => hM _ ?_⟩
      have hu' : ‖u‖ < r / 8 := by
        by_contra hh
        exact hu (by simp [Ln, px3a_zeta_eq_zero hρ (not_lt.mp hh)])
      have h1 : ‖p.2 - z0‖ < r / 16 := hp
      have h2 : ‖z0‖ - ‖p.2‖ ≤ ‖p.2 - z0‖ := by
        have := norm_sub_norm_le z0 p.2; rw [norm_sub_rev] at this; exact this
      have h3 := norm_sub_norm_le p.2 u
      show r / 2 ≤ ‖p.2 - u‖
      linarith)
  -- far piece
  have hLf : ContDiff ℝ (m : WithTop ℕ∞) (Lf d κ (r / 8)) := by
    exact_mod_cast Lf_contDiff hρ κ (m : ℕ∞)
  have hfar := far_param hd1 h.smooth hLf
    (fun i hi => by
      obtain ⟨C, hC0, hC⟩ := (Lf_hasCompactSupport (d := d) (r / 8) κ).exists_bound_iteratedFDeriv
        (Lf_contDiff hρ κ (⊤ : ℕ∞)) m
      exact ⟨C, fun y => hC i hi y⟩)
    (fun j hj => by
      have hbi : Integrable (fun w : Euc d => (Metric.ball (0 : Euc d) (1 / 8)).indicator
          (fun w => A * (1 + ‖w‖ ^ (-σ) * (1 + |Real.log ‖w‖|) ^ b)) w) := by
        rw [integrable_indicator_iff measurableSet_ball]
        refine Integrable.const_mul ?_ A
        exact (integrableOn_const measure_ball_lt_top.ne).add (integrableOn_rpow_log hd1 hσ b (by norm_num))
      refine ⟨_, hbi, ?_⟩
      have hae : ∀ᵐ w : Euc d, w ≠ 0 := by
        have := (Set.countable_singleton (0 : Euc d)).ae_notMem (volume : Measure (Euc d))
        filter_upwards [this] with w hw using by simpa using hw
      filter_upwards [hae] with w hw0 X
      by_cases hw : ‖w‖ < 1 / 8
      · rw [Set.indicator_of_mem (by simpa using hw)]
        exact h.slice_bound hj X w hw0
      · rw [Set.indicator_of_notMem (by simpa using hw), h.slice_zero j (by linarith [not_lt.mp hw]) X]
        simp)
    hU'o
  obtain ⟨hn1, hn2, hn3⟩ := hnear
  obtain ⟨hf1, hf2, hf3⟩ := hfar
  have heq : ∀ p ∈ U', newtonPot d g p - κ * ∫ w, g (p.1, w) =
      (∫ u, Ln d κ (r / 8) u * g (p.1, p.2 - u)) + ∫ w, Lf d κ (r / 8) (p.2 - w) * g (p.1, w) := by
    intro p hp
    obtain ⟨-, -, hs⟩ := newtonPot_split hd hσ hA h hr hr1 hz0 hp κ
    rw [hs]; ring
  have hev : ∀ p ∈ U', (fun p' => newtonPot d g p' - κ * ∫ w, g (p'.1, w)) =ᶠ[𝓝 p]
      fun p' => (∫ u, Ln d κ (r / 8) u * g (p'.1, p'.2 - u)) +
        ∫ w, Lf d κ (r / 8) (p'.2 - w) * g (p'.1, w) := by
    intro p hp
    filter_upwards [hU'o.mem_nhds hp] with p' hp' using heq p' hp'
  refine ⟨(hn1.add hf1).congr heq, fun k hk p hp => ?_, fun k hk p hp => ⟨hn3 k hk p hp, hf3 k hk p hp⟩⟩
  rw [((hev p hp).iteratedFDeriv ℝ k).eq_of_nhds]
  show iteratedFDeriv ℝ k ((fun p' => ∫ u, Ln d κ (r / 8) u * g (p'.1, p'.2 - u)) +
    (fun p' => ∫ w, Lf d κ (r / 8) (p'.2 - w) * g (p'.1, w))) p = _
  rw [iteratedFDeriv_add_apply
    ((hn1.contDiffAt (hU'o.mem_nhds hp)).of_le (by exact_mod_cast hk))
    ((hf1.contDiffAt (hU'o.mem_nhds hp)).of_le (by exact_mod_cast hk)), hn2 k hk p hp, hf2 k hk p hp]

end HRS.Parx

end
