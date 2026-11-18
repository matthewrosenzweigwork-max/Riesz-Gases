import HRS.Equilibrium.Parametrix.PX4aAuxA

/-!
# Packet PX4a auxiliaries B: the potential `kPot` of a chart source; near/far splitting

The analogue of `newtonPot_split` and `newtonPot_FL` (PX3a, files H) for a local kernel `k`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The potential of a chart source with the kernel `k`: `∫ k(z - w) g(X, w) dw`. -/
def kPot (d : ℕ) (k : Euc d → ℝ) (g : Euc d × Euc d → ℝ) (p : Euc d × Euc d) : ℝ :=
  ∫ w, k (p.2 - w) * g (p.1, w)

section Split

variable {s : ℝ} {k : Euc d → ℝ}

lemma kPot_split (hd : 1 ≤ d) (hk : LocKer d s k) {σ : ℝ} (hσ : σ < d) {b m : ℕ} {A : ℝ}
    (hA : 0 ≤ A) {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g) {r : ℝ} (hr : 0 < r)
    (hr1 : r < 1 / 8) {z0 : Euc d} (hz0 : ‖z0‖ = r) {p : Euc d × Euc d}
    (hp : ‖p.2 - z0‖ < r / 16) :
    Integrable (fun u => kN k (r / 8) u * g (p.1, p.2 - u)) ∧
    Integrable (fun w => kF k (r / 8) (p.2 - w) * g (p.1, w)) ∧
    kPot d k g p = (∫ u, kN k (r / 8) u * g (p.1, p.2 - u)) +
      ∫ w, kF k (r / 8) (p.2 - w) * g (p.1, w) := by
  have hρ : 0 < r / 8 := by positivity
  have hgi := h.slice_integrable hd hσ p.1
  have hp2 : ‖p.2‖ < 1 / 4 := by
    have := norm_sub_norm_le p.2 z0
    linarith
  obtain ⟨C, hC⟩ := hk.kF_bdd hρ
  have hLfi : Integrable (fun w => kF k (r / 8) (p.2 - w) * g (p.1, w)) :=
    hgi.bdd_mul ((hk.kF_measurable hρ).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun w => hC _)
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
    (h.slice_aesm hd p.1).comp_measurePreserving (Measure.measurePreserving_sub_left volume p.2)
  have hLni : Integrable (fun u => kN k (r / 8) u * g (p.1, p.2 - u)) := by
    refine ((hk.kN_integrable hd hρ (by linarith)).norm.mul_const M).mono'
      ((hk.kN_measurable (r / 8)).aestronglyMeasurable.mul hgaes) (Eventually.of_forall fun u => ?_)
    by_cases hu : ‖u‖ < r / 8
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (by simpa using hnear_bd u hu) (norm_nonneg _)
    · simp [LocKer.kN_eq_zero hρ (not_lt.mp hu)]
  have hLnw : Integrable (fun w => kN k (r / 8) (p.2 - w) * g (p.1, w)) := by
    have := hLni.comp_sub_left p.2
    refine this.congr (Eventually.of_forall fun w => ?_)
    simp
  refine ⟨hLni, hLfi, ?_⟩
  unfold kPot
  have hsw : ∫ w, kN k (r / 8) (p.2 - w) * g (p.1, w) =
      ∫ u, kN k (r / 8) u * g (p.1, p.2 - u) := by
    have := integral_sub_left_eq_self (fun u => kN k (r / 8) u * g (p.1, p.2 - u)) volume p.2
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp
  have hpt : ∀ w : Euc d, k (p.2 - w) * g (p.1, w) =
      kN k (r / 8) (p.2 - w) * g (p.1, w) + kF k (r / 8) (p.2 - w) * g (p.1, w) := by
    intro w; rw [← add_mul, kN_add_kF]
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add hLnw hLfi, hsw]

lemma kPot_FL (hd : 1 ≤ d) (hk : LocKer d s k) {σ : ℝ} (hσ : σ < d) {b m : ℕ} {A : ℝ}
    (hA : 0 ≤ A) {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g) {r : ℝ} (hr : 0 < r)
    (hr1 : r < 1 / 8) {z0 : Euc d} (hz0 : ‖z0‖ = r) :
    ContDiffOn ℝ (m : WithTop ℕ∞) (kPot d k g) {p : Euc d × Euc d | ‖p.2 - z0‖ < r / 16} ∧
    (∀ j ≤ m, ∀ p : Euc d × Euc d, ‖p.2 - z0‖ < r / 16 →
      iteratedFDeriv ℝ j (kPot d k g) p =
        (∫ u, kN k (r / 8) u • iteratedFDeriv ℝ j g (p.1, p.2 - u)) +
        ∫ w, iteratedFDeriv ℝ j (fun q : Euc d × Euc d => kF k (r / 8) (q.2 - w) * g (q.1, w)) p) ∧
    (∀ j ≤ m, ∀ p : Euc d × Euc d, ‖p.2 - z0‖ < r / 16 →
      Integrable (fun u => kN k (r / 8) u • iteratedFDeriv ℝ j g (p.1, p.2 - u)) ∧
      Integrable (fun w => iteratedFDeriv ℝ j
        (fun q : Euc d × Euc d => kF k (r / 8) (q.2 - w) * g (q.1, w)) p)) := by
  have hρ : 0 < r / 8 := by positivity
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  set U' : Set (Euc d × Euc d) := {p | ‖p.2 - z0‖ < r / 16} with hU'
  have hU'o : IsOpen U' := isOpen_near z0 _
  -- near piece
  have hnear := near_param (g := g) (V := {p : Euc d × Euc d | p.2 ≠ 0}) isOpen_ne_snd h.smooth
    (hk.kN_measurable (r / 8)) (hk.kN_integrable hd hρ (by linarith)) hU'o
    (fun p hp u hu => by
      have hu' : ‖u‖ < r / 8 := by
        by_contra hh
        exact hu (LocKer.kN_eq_zero hρ (not_lt.mp hh))
      show p.2 - u ≠ 0
      intro h0
      have h1 : ‖p.2 - z0‖ < r / 16 := hp
      have h2 : ‖z0‖ ≤ ‖p.2 - z0‖ + ‖p.2‖ := by
        have := norm_sub_le p.2 (p.2 - z0); rw [sub_sub_cancel] at this; linarith
      have h3 : ‖p.2‖ = ‖u‖ := by rw [sub_eq_zero.mp h0]
      linarith)
    (fun j hj => by
      obtain ⟨M, hM0, hM⟩ := h.full_bound hA hj (ρ0 := r / 2) (by positivity)
      refine ⟨M, fun p hp u hu => hM _ ?_⟩
      have hu' : ‖u‖ < r / 8 := by
        by_contra hh
        exact hu (LocKer.kN_eq_zero hρ (not_lt.mp hh))
      have h1 : ‖p.2 - z0‖ < r / 16 := hp
      have h2 : ‖z0‖ - ‖p.2‖ ≤ ‖p.2 - z0‖ := by
        have := norm_sub_norm_le z0 p.2; rw [norm_sub_rev] at this; exact this
      have h3 := norm_sub_norm_le p.2 u
      show r / 2 ≤ ‖p.2 - u‖
      linarith)
  -- far piece
  have hLf : ContDiff ℝ (m : WithTop ℕ∞) (kF k (r / 8)) := by
    exact_mod_cast hk.kF_contDiff hρ (m : ℕ∞)
  have hfar := far_param hd h.smooth hLf
    (fun i hi => by
      obtain ⟨C, hC0, hC⟩ := (hk.kF_hasCompactSupport (r / 8)).exists_bound_iteratedFDeriv
        (hk.kF_contDiff hρ (⊤ : ℕ∞)) m
      exact ⟨C, fun y => hC i hi y⟩)
    (fun j hj => by
      have hbi : Integrable (fun w : Euc d => (Metric.ball (0 : Euc d) (1 / 8)).indicator
          (fun w => A * (1 + ‖w‖ ^ (-σ) * (1 + |Real.log ‖w‖|) ^ b)) w) := by
        rw [integrable_indicator_iff measurableSet_ball]
        refine Integrable.const_mul ?_ A
        exact (integrableOn_const measure_ball_lt_top.ne).add (integrableOn_rpow_log hd hσ b (by norm_num))
      refine ⟨_, hbi, ?_⟩
      have hae : ∀ᵐ w : Euc d, w ≠ 0 := ae_ne_zero_euc (d := d) hd
      filter_upwards [hae] with w hw0 X
      by_cases hw : ‖w‖ < 1 / 8
      · rw [Set.indicator_of_mem (by simpa using hw)]
        exact h.slice_bound hj X w hw0
      · rw [Set.indicator_of_notMem (by simpa using hw), h.slice_zero j (by linarith [not_lt.mp hw]) X]
        simp)
    hU'o
  obtain ⟨hn1, hn2, hn3⟩ := hnear
  obtain ⟨hf1, hf2, hf3⟩ := hfar
  have heq : ∀ p ∈ U', kPot d k g p =
      (∫ u, kN k (r / 8) u * g (p.1, p.2 - u)) + ∫ w, kF k (r / 8) (p.2 - w) * g (p.1, w) := by
    intro p hp
    obtain ⟨-, -, hs⟩ := kPot_split hd hk hσ hA h hr hr1 hz0 hp
    exact hs
  have hev : ∀ p ∈ U', kPot d k g =ᶠ[𝓝 p]
      fun p' => (∫ u, kN k (r / 8) u * g (p'.1, p'.2 - u)) +
        ∫ w, kF k (r / 8) (p'.2 - w) * g (p'.1, w) := by
    intro p hp
    filter_upwards [hU'o.mem_nhds hp] with p' hp' using heq p' hp'
  refine ⟨(hn1.add hf1).congr heq, fun j hj p hp => ?_, fun j hj p hp => ⟨hn3 j hj p hp, hf3 j hj p hp⟩⟩
  rw [((hev p hp).iteratedFDeriv ℝ j).eq_of_nhds]
  show iteratedFDeriv ℝ j ((fun p' => ∫ u, kN k (r / 8) u * g (p'.1, p'.2 - u)) +
    (fun p' => ∫ w, kF k (r / 8) (p'.2 - w) * g (p'.1, w))) p = _
  rw [iteratedFDeriv_add_apply
    ((hn1.contDiffAt (hU'o.mem_nhds hp)).of_le (by exact_mod_cast hj))
    ((hf1.contDiffAt (hU'o.mem_nhds hp)).of_le (by exact_mod_cast hj)), hn2 j hj p hp, hf2 j hj p hp]

end Split

end HRS.Parx

end
