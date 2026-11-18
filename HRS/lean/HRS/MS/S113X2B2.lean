import Mathlib

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Set intervalIntegral Filter Topology

namespace HRS.MS.S113X2B

/-! Chain-rule inequality for `w` with `w - ∫ g` antitone, by Riemann-sum discretization. -/

def s113b_cl (a b x : ℝ) : ℝ := max a (min b x)
def s113b_tau (s δ : ℝ) (k : ℕ) : ℝ := s + (k : ℝ) * δ
def s113b_rho (s δ σ : ℝ) : ℝ := s + (⌈(σ - s) / δ⌉₊ : ℝ) * δ

lemma s113b_cl_mem {a b : ℝ} (h : a ≤ b) (x : ℝ) : s113b_cl a b x ∈ Icc a b :=
  ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

lemma s113b_cl_id {a b x : ℝ} (hx : x ∈ Icc a b) : s113b_cl a b x = x := by
  unfold s113b_cl; rw [min_eq_right hx.2, max_eq_right hx.1]

lemma s113b_cl_cont (a b : ℝ) : Continuous (s113b_cl a b) := by
  unfold s113b_cl; fun_prop

lemma s113b_cl_mono (a b : ℝ) : Monotone (s113b_cl a b) :=
  fun _ _ h => max_le_max le_rfl (min_le_min le_rfl h)

lemma s113b_tau_succ (s δ : ℝ) (k : ℕ) : s113b_tau s δ (k + 1) = s113b_tau s δ k + δ := by
  unfold s113b_tau; push_cast; ring

lemma s113b_rho_cell {s δ σ : ℝ} (hδ : 0 < δ) (k : ℕ) (h1 : s113b_tau s δ k < σ)
    (h2 : σ ≤ s113b_tau s δ (k + 1)) : s113b_rho s δ σ = s113b_tau s δ (k + 1) := by
  have hc : ⌈(σ - s) / δ⌉₊ = k + 1 := by
    rw [Nat.ceil_eq_iff (Nat.succ_ne_zero k)]
    unfold s113b_tau at h1 h2
    constructor
    · rw [lt_div_iff₀ hδ]; push_cast; linarith
    · rw [div_le_iff₀ hδ]; push_cast at h2 ⊢; linarith
  unfold s113b_rho s113b_tau; rw [hc]

lemma s113b_rho_bd {s δ σ : ℝ} (hδ : 0 < δ) (hσ : s < σ) :
    σ ≤ s113b_rho s δ σ ∧ s113b_rho s δ σ < σ + δ := by
  have hx : (σ - s) / δ * δ = σ - s := div_mul_cancel₀ _ hδ.ne'
  have hx0 : 0 ≤ (σ - s) / δ := div_nonneg (by linarith) hδ.le
  unfold s113b_rho
  have h1 := mul_le_mul_of_nonneg_right (Nat.le_ceil ((σ - s) / δ)) hδ.le
  have h2 := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one hx0) hδ
  constructor <;> nlinarith

lemma s113b_rho_meas (s δ : ℝ) : Measurable (s113b_rho s δ) := by
  unfold s113b_rho
  exact measurable_const.add
    ((measurable_from_nat.comp (Nat.measurable_ceil.comp ((measurable_id.sub_const s).div_const δ))).mul_const δ)

/-- convexity-type inequality -/
lemma s113b_mono {B c d : ℝ} (hcd : Icc c d ⊆ Icc 0 B) {ψ ψ' : ℝ → ℝ}
    (hd : ∀ x ∈ Icc (0:ℝ) B, HasDerivWithinAt ψ (ψ' x) (Icc 0 B) x)
    (hnn : ∀ x ∈ Icc c d, 0 ≤ ψ' x) (hle : c ≤ d) : ψ c ≤ ψ d := by
  have hc : ContinuousOn ψ (Icc c d) := fun x hx => ((hd x (hcd hx)).continuousWithinAt).mono hcd
  exact monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc c d) hc
    (fun x hx => (hd x (hcd (interior_subset hx))).mono (interior_subset.trans hcd))
    (fun x hx => hnn x (interior_subset hx)) (left_mem_Icc.2 hle) (right_mem_Icc.2 hle) hle

lemma s113b_conv {B : ℝ} {f f2 : ℝ → ℝ}
    (hd : ∀ x ∈ Icc (0:ℝ) B, HasDerivWithinAt f (f2 x) (Icc 0 B) x)
    (hm : MonotoneOn f2 (Icc 0 B)) {a b : ℝ} (ha : a ∈ Icc (0:ℝ) B) (hb : b ∈ Icc (0:ℝ) B) :
    f b - f a ≤ f2 b * (b - a) := by
  have hlin : ∀ x ∈ Icc (0:ℝ) B, HasDerivWithinAt (fun y => f2 b * y) (f2 b) (Icc 0 B) x :=
    fun x _ => by simpa using (hasDerivWithinAt_id x (Icc 0 B)).const_mul (f2 b)
  rcases le_total a b with h | h
  · have := s113b_mono (B := B) (c := a) (d := b) (Icc_subset_Icc ha.1 hb.2)
      (ψ := fun x => f2 b * x - f x) (ψ' := fun x => f2 b - f2 x)
      (fun x hx => (hlin x hx).sub (hd x hx))
      (fun x hx => sub_nonneg.2 (hm ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩ hb hx.2)) h
    rw [mul_sub]; linarith
  · have := s113b_mono (B := B) (c := b) (d := a) (Icc_subset_Icc hb.1 ha.2)
      (ψ := fun x => f x - f2 b * x) (ψ' := fun x => f2 x - f2 b)
      (fun x hx => (hd x hx).sub (hlin x hx))
      (fun x hx => sub_nonneg.2 (hm hb ⟨hb.1.trans hx.1, hx.2.trans ha.2⟩ hx.1)) h
    rw [mul_sub]; linarith

lemma s113b_cell {s t B : ℝ} {w g : ℝ → ℝ} {F F1 F2 : ℝ → ℝ → ℝ}
    (hw : ∀ τ, w τ ∈ Icc (0:ℝ) B)
    (hineq : ∀ a b, s ≤ a → a ≤ b → b ≤ t → w b - w a ≤ ∫ τ in a..b, g τ)
    (hF1 : ∀ x ∈ Icc (0:ℝ) B, ∀ τ ∈ Icc s t, HasDerivAt (fun σ => F σ x) (F1 τ x) τ)
    (hF2 : ∀ τ ∈ Icc s t, ∀ x ∈ Icc (0:ℝ) B, HasDerivWithinAt (F τ) (F2 τ x) (Icc 0 B) x)
    (hF1c : Continuous (fun z : ℝ × ℝ => F1 z.1 z.2))
    (hF2nn : ∀ τ ∈ Icc s t, ∀ x ∈ Icc (0:ℝ) B, 0 ≤ F2 τ x)
    (hF2m : ∀ τ ∈ Icc s t, MonotoneOn (F2 τ) (Icc 0 B))
    {a b : ℝ} (ha : s ≤ a) (hab : a ≤ b) (hb : b ≤ t) :
    F b (w b) - F a (w a) ≤ (∫ σ in a..b, F1 σ (w b)) + F2 a (w b) * ∫ σ in a..b, g σ := by
  have hat : a ∈ Icc s t := ⟨ha, hab.trans hb⟩
  have hc : Continuous (fun σ => F1 σ (w b)) := hF1c.comp (continuous_id.prodMk continuous_const)
  have hFTC : ∫ σ in a..b, F1 σ (w b) = F b (w b) - F a (w b) := by
    apply integral_eq_sub_of_hasDerivAt (f := fun σ => F σ (w b))
    · intro x hx
      rw [uIcc_of_le hab] at hx
      exact hF1 _ (hw b) x ⟨ha.trans hx.1, hx.2.trans hb⟩
    · exact hc.intervalIntegrable _ _
  have hconv := s113b_conv (hF2 a hat) (hF2m a hat) (hw a) (hw b)
  have hmul := mul_le_mul_of_nonneg_left (hineq a b ha hab hb) (hF2nn a hat (w b) (hw b))
  rw [hFTC]; linarith

lemma s113b_aesm {s t : ℝ} {g H1 H2 : ℝ → ℝ} (hg : IntervalIntegrable g volume s t)
    (m1 : Measurable H1) (m2 : Measurable H2) :
    AEStronglyMeasurable (fun σ => H1 σ + H2 σ * g σ) (volume.restrict (uIoc s t)) :=
  m1.aestronglyMeasurable.add (m2.aestronglyMeasurable.mul (intervalIntegrable_iff.1 hg).aestronglyMeasurable)

lemma s113b_key {C1 C2 a b c : ℝ} (ha : |a| ≤ C1) (hb : |b| ≤ C2) :
    ‖a + b * c‖ ≤ C1 + C2 * ‖c‖ := by
  calc ‖a + b * c‖ ≤ ‖a‖ + ‖b * c‖ := norm_add_le _ _
    _ = |a| + |b| * ‖c‖ := by simp [norm_mul]
    _ ≤ C1 + C2 * ‖c‖ := add_le_add ha (mul_le_mul_of_nonneg_right hb (norm_nonneg c))

lemma s113b_intB2 {s t C1 C2 : ℝ} {g H1 H2 : ℝ → ℝ} (hg : IntervalIntegrable g volume s t)
    (m1 : Measurable H1) (m2 : Measurable H2) (b1 : ∀ σ, |H1 σ| ≤ C1) (b2 : ∀ σ, |H2 σ| ≤ C2) :
    IntervalIntegrable (fun σ => H1 σ + H2 σ * g σ) volume s t := by
  refine IntervalIntegrable.mono_fun' (f := fun σ => H1 σ + H2 σ * g σ) (g := fun σ => C1 + C2 * ‖g σ‖)
    (intervalIntegrable_const.add (hg.norm.const_mul C2)) (s113b_aesm hg m1 m2) ?_
  exact Filter.Eventually.of_forall (fun σ => s113b_key (b1 σ) (b2 σ))

lemma s113b_finite {s t B : ℝ} (hst : s ≤ t) {w g : ℝ → ℝ} {F P1 P2 : ℝ → ℝ → ℝ}
    (hw : ∀ τ, w τ ∈ Icc (0:ℝ) B) (hg : IntervalIntegrable g volume s t)
    (hineq : ∀ a b, s ≤ a → a ≤ b → b ≤ t → w b - w a ≤ ∫ τ in a..b, g τ)
    (hF1 : ∀ x ∈ Icc (0:ℝ) B, ∀ τ ∈ Icc s t, HasDerivAt (fun σ => F σ x) (P1 τ x) τ)
    (hF2 : ∀ τ ∈ Icc s t, ∀ x ∈ Icc (0:ℝ) B, HasDerivWithinAt (F τ) (P2 τ x) (Icc 0 B) x)
    (hP1c : Continuous (fun z : ℝ × ℝ => P1 z.1 z.2))
    (hF2nn : ∀ τ ∈ Icc s t, ∀ x ∈ Icc (0:ℝ) B, 0 ≤ P2 τ x)
    (hF2m : ∀ τ ∈ Icc s t, MonotoneOn (P2 τ) (Icc 0 B))
    {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hN : s113b_tau s δ (n + 1) = t)
    (hint : IntervalIntegrable (fun σ => P1 σ (w (s113b_rho s δ σ)) +
      P2 (s113b_rho s δ σ - δ) (w (s113b_rho s δ σ)) * g σ) volume s t) :
    F t (w t) - F s (w s) ≤ ∫ σ in s..t, (P1 σ (w (s113b_rho s δ σ)) +
      P2 (s113b_rho s δ σ - δ) (w (s113b_rho s δ σ)) * g σ) := by
  set f : ℝ → ℝ := fun σ => P1 σ (w (s113b_rho s δ σ)) +
      P2 (s113b_rho s δ σ - δ) (w (s113b_rho s δ σ)) * g σ with hf
  have hτ0 : s113b_tau s δ 0 = s := by simp [s113b_tau]
  have hτle : ∀ k, s113b_tau s δ k ≤ s113b_tau s δ (k + 1) := fun k => by
    rw [s113b_tau_succ]; linarith
  have hτmem : ∀ k, k ≤ n + 1 → s ≤ s113b_tau s δ k ∧ s113b_tau s δ k ≤ t := by
    intro k hk
    have h0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hkn : (k:ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_le.2 hk
    rw [← hN]
    unfold s113b_tau
    constructor <;> nlinarith
  have hcell : ∀ k, k ≤ n → (∫ σ in s113b_tau s δ k..s113b_tau s δ (k + 1), f σ) =
      (∫ σ in s113b_tau s δ k..s113b_tau s δ (k + 1), P1 σ (w (s113b_tau s δ (k + 1)))) +
        P2 (s113b_tau s δ k) (w (s113b_tau s δ (k + 1))) *
          ∫ σ in s113b_tau s δ k..s113b_tau s δ (k + 1), g σ := by
    intro k hk
    have hk1 := hτmem k (by omega)
    have hk2 := hτmem (k + 1) (by omega)
    have hgk : IntervalIntegrable g volume (s113b_tau s δ k) (s113b_tau s δ (k + 1)) :=
      hg.mono_set (by
        rw [uIcc_of_le (hτle k), uIcc_of_le hst]; exact Icc_subset_Icc hk1.1 hk2.2)
    have hc : Continuous (fun σ => P1 σ (w (s113b_tau s δ (k + 1)))) :=
      hP1c.comp (continuous_id.prodMk continuous_const)
    rw [intervalIntegral.integral_congr_ae (g := fun σ => P1 σ (w (s113b_tau s δ (k + 1))) +
      P2 (s113b_tau s δ k) (w (s113b_tau s δ (k + 1))) * g σ) ?_]
    · rw [intervalIntegral.integral_add (hc.intervalIntegrable _ _) (hgk.const_mul _),
        intervalIntegral.integral_const_mul]
    · refine Filter.Eventually.of_forall (fun σ hσ => ?_)
      rw [uIoc_of_le (hτle k)] at hσ
      have hρ := s113b_rho_cell hδ k hσ.1 hσ.2
      have h2 : s113b_tau s δ (k + 1) - δ = s113b_tau s δ k := by rw [s113b_tau_succ]; ring
      simp only [hf, hρ, h2]
  calc F t (w t) - F s (w s)
      = ∑ k ∈ Finset.range (n + 1), (F (s113b_tau s δ (k + 1)) (w (s113b_tau s δ (k + 1))) -
          F (s113b_tau s δ k) (w (s113b_tau s δ k))) := by
        rw [Finset.sum_range_sub (fun k => F (s113b_tau s δ k) (w (s113b_tau s δ k))), hN, hτ0]
    _ ≤ ∑ k ∈ Finset.range (n + 1), ∫ σ in s113b_tau s δ k..s113b_tau s δ (k + 1), f σ := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        rw [hcell k hk']
        exact s113b_cell hw hineq hF1 hF2 hP1c hF2nn hF2m (hτmem k (by omega)).1 (hτle k)
          (hτmem (k + 1) (by omega)).2
    _ = ∫ σ in s..t, f σ := by
        have := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume)
          (a := s113b_tau s δ) (n := n + 1) (fun k hk => hint.mono_set (by
            rw [uIcc_of_le (hτle k), uIcc_of_le hst]
            exact Icc_subset_Icc (hτmem k (by omega)).1 (hτmem (k + 1) (by omega)).2))
        rw [this, hτ0, hN]

lemma s113b_wext {s t : ℝ} (hst : s ≤ t) {w g : ℝ → ℝ} (hg : IntervalIntegrable g volume s t)
    (hineq : ∀ a b, s ≤ a → a ≤ b → b ≤ t → w b - w a ≤ ∫ τ in a..b, g τ) :
    Measurable (fun τ => w (s113b_cl s t τ)) ∧
      ∀ᵐ σ ∂(volume : Measure ℝ), ContinuousAt (fun τ => w (s113b_cl s t τ)) σ := by
  have hint : ∀ a b, s ≤ a → a ≤ b → b ≤ t → IntervalIntegrable g volume a b :=
    fun a b ha hab hb => hg.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le hst]; exact Icc_subset_Icc ha hb)
  have hAc : Continuous (fun τ => ∫ σ in s..s113b_cl s t τ, g σ) := by
    have h1 : ContinuousOn (fun x => ∫ σ in s..x, g σ) (uIcc s t) :=
      intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc
    exact h1.comp_continuous (s113b_cl_cont s t)
      (fun x => by rw [uIcc_of_le hst]; exact s113b_cl_mem hst x)
  have hm : Antitone (fun τ => w (s113b_cl s t τ) - ∫ σ in s..s113b_cl s t τ, g σ) := by
    intro x y hxy
    have hxy' := s113b_cl_mono s t hxy
    have hx := s113b_cl_mem hst x
    have hy := s113b_cl_mem hst y
    have h1 := hineq _ _ hx.1 hxy' hy.2
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hint s _ le_rfl hx.1 hx.2) (hint _ _ hx.1 hxy' hy.2)
    dsimp only
    linarith
  have hcount := hm.countable_not_continuousAt
  have hsub : {x | ¬ ContinuousAt (fun τ => w (s113b_cl s t τ)) x} ⊆
      {x | ¬ ContinuousAt (fun τ => w (s113b_cl s t τ) - ∫ σ in s..s113b_cl s t τ, g σ) x} := by
    intro x hx hxm
    apply hx
    have h3 := hxm.add hAc.continuousAt
    have e : (fun τ => w (s113b_cl s t τ)) = (fun τ => w (s113b_cl s t τ) -
        ∫ σ in s..s113b_cl s t τ, g σ) + fun τ => ∫ σ in s..s113b_cl s t τ, g σ := by
      funext τ; simp
    rw [e]; exact h3
  have hc2 := hcount.mono hsub
  exact ⟨measurable_of_countable_not_continuousAt hc2, by
    filter_upwards [hc2.ae_notMem volume] with x hx
    exact not_not.1 hx⟩

lemma s113b_core {s t B : ℝ} (hst : s < t) {w g : ℝ → ℝ} {F P1 P2 : ℝ → ℝ → ℝ} {C1 C2 : ℝ}
    (hw : ∀ τ, w τ ∈ Icc (0:ℝ) B) (hwm : Measurable w)
    (hwc : ∀ᵐ σ ∂(volume : Measure ℝ), ContinuousAt w σ)
    (hg : IntervalIntegrable g volume s t)
    (hineq : ∀ a b, s ≤ a → a ≤ b → b ≤ t → w b - w a ≤ ∫ τ in a..b, g τ)
    (hF1 : ∀ x ∈ Icc (0:ℝ) B, ∀ τ ∈ Icc s t, HasDerivAt (fun σ => F σ x) (P1 τ x) τ)
    (hF2 : ∀ τ ∈ Icc s t, ∀ x ∈ Icc (0:ℝ) B, HasDerivWithinAt (F τ) (P2 τ x) (Icc 0 B) x)
    (hP1c : Continuous (fun z : ℝ × ℝ => P1 z.1 z.2))
    (hP2c : Continuous (fun z : ℝ × ℝ => P2 z.1 z.2))
    (hC1 : ∀ σ x, |P1 σ x| ≤ C1) (hC2 : ∀ σ x, |P2 σ x| ≤ C2)
    (hF2nn : ∀ τ ∈ Icc s t, ∀ x ∈ Icc (0:ℝ) B, 0 ≤ P2 τ x)
    (hF2m : ∀ τ ∈ Icc s t, MonotoneOn (P2 τ) (Icc 0 B)) :
    F t (w t) - F s (w s) ≤ ∫ σ in s..t, (P1 σ (w σ) + P2 σ (w σ) * g σ) := by
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℕ → ℝ, ∀ n, δ n = (t - s) / ((n:ℝ) + 1) := ⟨_, fun _ => rfl⟩
  have hδpos : ∀ n, 0 < δ n := fun n => by
    rw [hδdef]; exact div_pos (sub_pos.2 hst) (by positivity)
  have hN : ∀ n : ℕ, s113b_tau s (δ n) (n + 1) = t := by
    intro n; unfold s113b_tau; rw [hδdef]; push_cast; field_simp; ring
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    have : δ = fun n : ℕ => (t - s) / ((n:ℝ) + 1) := funext hδdef
    rw [this]
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ → ℝ, ∀ n σ, f n σ = P1 σ (w (s113b_rho s (δ n) σ)) +
      P2 (s113b_rho s (δ n) σ - δ n) (w (s113b_rho s (δ n) σ)) * g σ := ⟨fun n σ => _, fun _ _ => rfl⟩
  have hm1 : ∀ n, Measurable (fun σ => P1 σ (w (s113b_rho s (δ n) σ))) := fun n =>
    hP1c.measurable.comp (measurable_id.prodMk (hwm.comp (s113b_rho_meas s (δ n))))
  have hm2 : ∀ n, Measurable (fun σ => P2 (s113b_rho s (δ n) σ - δ n) (w (s113b_rho s (δ n) σ))) :=
    fun n => hP2c.measurable.comp (((s113b_rho_meas s (δ n)).sub_const (δ n)).prodMk
      (hwm.comp (s113b_rho_meas s (δ n))))
  have hint : ∀ n, IntervalIntegrable (fun σ => f n σ) volume s t := fun n => by
    simp only [hf]
    exact s113b_intB2 hg (hm1 n) (hm2 n) (fun σ => hC1 _ _) (fun σ => hC2 _ _)
  have hfin : ∀ n, F t (w t) - F s (w s) ≤ ∫ σ in s..t, f n σ := fun n => by
    have := s113b_finite hst.le hw hg hineq hF1 hF2 hP1c hF2nn hF2m (hδpos n) (hN n)
      (by simpa only [hf] using hint n)
    simpa only [hf] using this
  have hlim : Tendsto (fun n => ∫ σ in s..t, f n σ) atTop
      (𝓝 (∫ σ in s..t, (P1 σ (w σ) + P2 σ (w σ) * g σ))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun σ => C1 + C2 * ‖g σ‖) ?_ ?_ ?_ ?_
    · refine Filter.Eventually.of_forall (fun n => ?_)
      have e : f n = fun σ => P1 σ (w (s113b_rho s (δ n) σ)) +
          P2 (s113b_rho s (δ n) σ - δ n) (w (s113b_rho s (δ n) σ)) * g σ := funext (hf n)
      rw [e]; exact s113b_aesm hg (hm1 n) (hm2 n)
    · refine Filter.Eventually.of_forall (fun n => Filter.Eventually.of_forall (fun σ _ => ?_))
      rw [hf]; exact s113b_key (hC1 _ _) (hC2 _ _)
    · exact intervalIntegrable_const.add (hg.norm.const_mul C2)
    · filter_upwards [hwc] with σ hσc hσI
      rw [uIoc_of_le hst.le] at hσI
      have hρt : Tendsto (fun n => s113b_rho s (δ n) σ) atTop (𝓝 σ) := by
        have hup : Tendsto (fun n => σ + δ n) atTop (𝓝 σ) := by
          simpa using (tendsto_const_nhds (x := σ)).add hδ0
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
          (fun n => (s113b_rho_bd (hδpos n) hσI.1).1) (fun n => (s113b_rho_bd (hδpos n) hσI.1).2.le)
      have hwρ : Tendsto (fun n => w (s113b_rho s (δ n) σ)) atTop (𝓝 (w σ)) := hσc.tendsto.comp hρt
      have h1 : Tendsto (fun n => P1 σ (w (s113b_rho s (δ n) σ))) atTop (𝓝 (P1 σ (w σ))) :=
        (hP1c.tendsto (σ, w σ)).comp (tendsto_const_nhds.prodMk_nhds hwρ)
      have h2 : Tendsto (fun n => P2 (s113b_rho s (δ n) σ - δ n) (w (s113b_rho s (δ n) σ))) atTop
          (𝓝 (P2 σ (w σ))) := by
        have h3 := hρt.sub hδ0
        rw [sub_zero] at h3
        exact (hP2c.tendsto (σ, w σ)).comp (h3.prodMk_nhds hwρ)
      simp only [hf]
      exact h1.add (h2.mul tendsto_const_nhds)
  exact ge_of_tendsto' hlim hfin

theorem s113b_chain_bv {s t B : ℝ} (hB : 0 ≤ B) (hst : s ≤ t) {w g : ℝ → ℝ}
    {F F1 F2 : ℝ → ℝ → ℝ}
    (hw : ∀ τ ∈ Icc s t, w τ ∈ Icc (0:ℝ) B)
    (hg : IntervalIntegrable g volume s t)
    (hineq : ∀ a b, s ≤ a → a ≤ b → b ≤ t → w b - w a ≤ ∫ τ in a..b, g τ)
    (hF1 : ∀ x ∈ Icc (0:ℝ) B, ∀ τ ∈ Icc s t, HasDerivAt (fun σ => F σ x) (F1 τ x) τ)
    (hF2 : ∀ τ ∈ Icc s t, ∀ x ∈ Icc (0:ℝ) B, HasDerivWithinAt (F τ) (F2 τ x) (Icc 0 B) x)
    (hF1c : ContinuousOn (fun z : ℝ × ℝ => F1 z.1 z.2) (Icc s t ×ˢ Icc 0 B))
    (hF2c : ContinuousOn (fun z : ℝ × ℝ => F2 z.1 z.2) (Icc s t ×ˢ Icc 0 B))
    (hF2nn : ∀ τ ∈ Icc s t, ∀ x ∈ Icc (0:ℝ) B, 0 ≤ F2 τ x)
    (hF2mono : ∀ τ ∈ Icc s t, MonotoneOn (F2 τ) (Icc 0 B)) :
    F t (w t) - F s (w s) ≤ ∫ τ in s..t, (F1 τ (w τ) + F2 τ (w τ) * g τ) := by
  rcases hst.eq_or_lt with rfl | hlt
  · simp
  obtain ⟨hwm, hwc⟩ := s113b_wext hst hg hineq
  have hcm : ∀ z : ℝ × ℝ, (s113b_cl s t z.1, s113b_cl 0 B z.2) ∈ Icc s t ×ˢ Icc 0 B :=
    fun z => ⟨s113b_cl_mem hst z.1, s113b_cl_mem hB z.2⟩
  have hcc : Continuous (fun z : ℝ × ℝ => (s113b_cl s t z.1, s113b_cl 0 B z.2)) :=
    ((s113b_cl_cont s t).comp continuous_fst).prodMk ((s113b_cl_cont 0 B).comp continuous_snd)
  obtain ⟨C1, hC1⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hF1c
  obtain ⟨C2, hC2⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hF2c
  have h := s113b_core hlt (w := fun τ => w (s113b_cl s t τ)) (F := F)
    (P1 := fun σ x => F1 (s113b_cl s t σ) (s113b_cl 0 B x))
    (P2 := fun σ x => F2 (s113b_cl s t σ) (s113b_cl 0 B x)) (C1 := C1) (C2 := C2)
    (fun τ => hw _ (s113b_cl_mem hst τ)) hwm hwc hg
    (by
      intro a b ha hab hb
      rw [s113b_cl_id ⟨ha, hab.trans hb⟩, s113b_cl_id ⟨ha.trans hab, hb⟩]
      exact hineq a b ha hab hb)
    (by
      intro x hx τ hτ
      rw [s113b_cl_id hτ, s113b_cl_id hx]
      exact hF1 x hx τ hτ)
    (by
      intro τ hτ x hx
      rw [s113b_cl_id hτ, s113b_cl_id hx]
      exact hF2 τ hτ x hx)
    (hF1c.comp_continuous hcc hcm) (hF2c.comp_continuous hcc hcm)
    (fun σ x => by rw [← Real.norm_eq_abs]; exact hC1 _ (hcm (σ, x)))
    (fun σ x => by rw [← Real.norm_eq_abs]; exact hC2 _ (hcm (σ, x)))
    (by
      intro τ hτ x hx
      rw [s113b_cl_id hτ, s113b_cl_id hx]
      exact hF2nn τ hτ x hx)
    (by
      intro τ hτ a ha b hb hab
      show F2 (s113b_cl s t τ) (s113b_cl 0 B a) ≤ F2 (s113b_cl s t τ) (s113b_cl 0 B b)
      rw [s113b_cl_id hτ, s113b_cl_id ha, s113b_cl_id hb]
      exact hF2mono τ hτ ha hb hab)
  rw [s113b_cl_id ⟨hst, le_rfl⟩, s113b_cl_id ⟨le_rfl, hst⟩] at h
  refine h.trans (le_of_eq (intervalIntegral.integral_congr (fun σ hσ => ?_)))
  rw [uIcc_of_le hst] at hσ
  rw [s113b_cl_id hσ, s113b_cl_id (hw σ hσ)]

end HRS.MS.S113X2B
