import HRS.MS.S104eC0
import HRS.MS.S104eC3A

/-!
# S104E route C, packet C3, file B: `Bd`/`HolB` algebra, the singular kernel, the structure `VolHyp`

Statement changes relative to `docs/handoff/wip/S104eCSkel.lean.wip` (see `HANDOFF_S104C3.md`): the continuity fields
`P_cont`/`A_cont` are replaced by jet-valued, family-valued versions (`P_cont` for jets `i ≤ j+1`; `P_jc`, `A_jc` for
continuous families), which are needed to make the pointwise time integrals non-junk (measurable integrands) and to
differentiate under them.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Interval

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.R2WinOrbNL

variable {d : ℕ}

/-! ## `HolB` algebra -/

theorem s104c3_Bd_zero_of {N : ℕ} {B : ℝ} {f : Euc d → ℝ} (h : Bd N B f) : Bd 0 B f :=
  Bd.mono_N (Nat.zero_le _) h

theorem s104c3_HolB_bd_j {j : ℕ} {η B : ℝ} {f : Euc d → ℝ} (h : HolB j η B f) : Bd j B f :=
  Bd.mono_N (Nat.le_succ j) h.1

theorem s104c3_HolB_nonneg {j : ℕ} {η B : ℝ} {f : Euc d → ℝ} (h : HolB j η B f) : 0 ≤ B :=
  h.1.nonneg

theorem s104c3_jets_lin_apply {N : ℕ} {f g : Euc d → ℝ} (c : ℝ) (hf : ContDiff ℝ (N : WithTop ℕ∞) f)
    (hg : ContDiff ℝ (N : WithTop ℕ∞) g) {i : ℕ} (hi : i ≤ N) (x : Euc d) :
    iteratedFDeriv ℝ i (fun y => c * f y + g y) x = c • iteratedFDeriv ℝ i f x + iteratedFDeriv ℝ i g x := by
  have e : (fun y => c * f y + g y) = c • f + g := by funext y; simp
  have hcf : ContDiff ℝ (N : WithTop ℕ∞) (c • f) := hf.const_smul c
  rw [e, iteratedFDeriv_add_apply (hcf.of_le (by exact_mod_cast hi)).contDiffAt
    (hg.of_le (by exact_mod_cast hi)).contDiffAt,
    iteratedFDeriv_const_smul_apply (hf.of_le (by exact_mod_cast hi)).contDiffAt]

theorem s104c3_HolB_lin {j : ℕ} {η B B' : ℝ} {f g : Euc d → ℝ} (c : ℝ) (hf : HolB j η B f)
    (hg : HolB j η B' g) : HolB j η (|c| * B + B') (fun x => c * f x + g x) := by
  refine ⟨(hf.1.smul c).add hg.1, fun x z => ?_⟩
  have hfc : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) f := hf.1.1
  have hgc : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) g := hg.1.1
  have e1 : ∀ y, iteratedFDeriv ℝ (j + 1) (fun x => c * f x + g x) y =
      c • iteratedFDeriv ℝ (j + 1) f y + iteratedFDeriv ℝ (j + 1) g y := fun y =>
    s104c3_jets_lin_apply c hfc hgc le_rfl y
  rw [e1, e1]
  have : c • iteratedFDeriv ℝ (j + 1) f (x + z) + iteratedFDeriv ℝ (j + 1) g (x + z) -
      (c • iteratedFDeriv ℝ (j + 1) f x + iteratedFDeriv ℝ (j + 1) g x) =
      c • (iteratedFDeriv ℝ (j + 1) f (x + z) - iteratedFDeriv ℝ (j + 1) f x) +
      (iteratedFDeriv ℝ (j + 1) g (x + z) - iteratedFDeriv ℝ (j + 1) g x) := by
    rw [smul_sub]; abel
  rw [this]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]
  have h1 := mul_le_mul_of_nonneg_left (hf.2 x z) (abs_nonneg c)
  have h2 := hg.2 x z
  have h3 : (|c| * B + B') * ‖z‖ ^ η = |c| * (B * ‖z‖ ^ η) + B' * ‖z‖ ^ η := by ring
  rw [h3]; linarith

theorem s104c3_HolB_sub {j : ℕ} {η B B' : ℝ} {f g : Euc d → ℝ} (hf : HolB j η B f)
    (hg : HolB j η B' g) : HolB j η (B + B') (fun x => g x - f x) := by
  have := s104c3_HolB_lin (-1) hf hg
  have e : (fun x => g x - f x) = fun x => -1 * f x + g x := by funext x; ring
  rw [e]; simpa using this

theorem s104c3_HolB_add {j : ℕ} {η B B' : ℝ} {f g : Euc d → ℝ} (hf : HolB j η B f)
    (hg : HolB j η B' g) : HolB j η (B + B') (fun x => g x + f x) := by
  have := s104c3_HolB_lin 1 hf hg
  have e : (fun x => g x + f x) = fun x => 1 * f x + g x := by funext x; ring
  rw [e]; simpa using this

/-- Pointwise limits of jets preserve `HolB`. -/
theorem s104c3_HolB_of_tendsto {j : ℕ} {η B : ℝ} {fK : ℕ → Euc d → ℝ} {f : Euc d → ℝ}
    (hf : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) f)
    (hl : ∀ m ≤ j + 1, ∀ x, Tendsto (fun K => iteratedFDeriv ℝ m (fK K) x) atTop
      (𝓝 (iteratedFDeriv ℝ m f x)))
    (hK : ∀ K, HolB j η B (fK K)) : HolB j η B f := by
  refine ⟨⟨hf, fun m hm x => ?_⟩, fun x z => ?_⟩
  · exact le_of_tendsto ((hl m hm x).norm) (Eventually.of_forall fun K => (hK K).1.2 m hm x)
  · have h1 := (hl (j + 1) le_rfl (x + z)).sub (hl (j + 1) le_rfl x)
    exact le_of_tendsto h1.norm (Eventually.of_forall fun K => (hK K).2 x z)

theorem s104c3_HolB_mono {j : ℕ} {η B B' : ℝ} {f : Euc d → ℝ} (h : HolB j η B f) (hB : B ≤ B')
    (hη : 0 ≤ η) : HolB j η B' f := h.mono_B hB hη

/-! ## The singular kernel -/

/-- `k(h) = 1 + h^{-(1+η)/2}`. -/
def s104c3_k (η h : ℝ) : ℝ := 1 + h ^ (-((1 + η) / 2))

theorem s104c3_k_nonneg (η : ℝ) {h : ℝ} (hh : 0 ≤ h) : 0 ≤ s104c3_k η h := by
  unfold s104c3_k
  have := Real.rpow_nonneg hh (-((1 + η) / 2))
  linarith

theorem s104c3_k_int {η : ℝ} (hη1 : η < 1) (hη0 : 0 < η) (a b : ℝ) :
    IntervalIntegrable (fun h => s104c3_k η h) volume a b := by
  unfold s104c3_k
  refine (intervalIntegrable_const (c := (1 : ℝ))).add ?_
  exact intervalIntegral.intervalIntegrable_rpow' (by linarith)

theorem s104c3_k_int_shift {η : ℝ} (hη1 : η < 1) (hη0 : 0 < η) (r a b : ℝ) :
    IntervalIntegrable (fun v => s104c3_k η (v - r)) volume a b := by
  have := (s104c3_k_int hη1 hη0 (a - r) (b - r)).comp_sub_right r
  simpa using this

/-- The weighted kernel integral can be made small. -/
theorem s104c3_k_small {η : ℝ} (hη1 : η < 1) (hη0 : 0 < η) {H : ℝ} (hH : 0 < H) {θ : ℝ} (hθ : 0 < θ) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∫ h in (0 : ℝ)..H, s104c3_k η h * Real.exp (-lam * h) ≤ θ := by
  have hu : Ι (0 : ℝ) H = Ioc 0 H := Set.uIoc_of_le hH.le
  have hlim : Tendsto (fun lam : ℝ => ∫ h in (0 : ℝ)..H, s104c3_k η h * Real.exp (-lam * h)) atTop
      (𝓝 (∫ h in (0 : ℝ)..H, (fun _ : ℝ => (0 : ℝ)) h)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun h => s104c3_k η h) ?_ ?_ (s104c3_k_int hη1 hη0 0 H) ?_
    · refine Eventually.of_forall fun lam => ?_
      have : IntervalIntegrable (fun h => s104c3_k η h * Real.exp (-lam * h)) volume 0 H := by
        refine (s104c3_k_int hη1 hη0 0 H).mul_continuousOn ?_
        exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
      rw [hu]; exact this.1.aestronglyMeasurable
    · refine (eventually_ge_atTop (0 : ℝ)).mono fun lam hlam => ae_of_all _ fun x hx => ?_
      rw [hu] at hx
      have hk := s104c3_k_nonneg η hx.1.le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk (Real.exp_pos _).le)]
      exact mul_le_of_le_one_right hk (Real.exp_le_one_iff.2 (by nlinarith [hx.1]))
    · refine ae_of_all _ fun x hx => ?_
      rw [hu] at hx
      have h1 : Tendsto (fun lam : ℝ => lam * x) atTop atTop := tendsto_id.atTop_mul_const hx.1
      have h2 : Tendsto (fun lam : ℝ => Real.exp (-lam * x)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (by
          have := tendsto_neg_atTop_atBot.comp h1
          refine this.congr fun lam => ?_
          simp [neg_mul])
      simpa using h2.const_mul (s104c3_k η x)
  simp only [intervalIntegral.integral_zero] at hlim
  obtain ⟨lam, h1, h2⟩ := ((hlim.eventually (gt_mem_nhds hθ)).and (eventually_ge_atTop 0)).exists
  exact ⟨lam, h2, h1.le⟩

end HRS.MS.S104e.C
