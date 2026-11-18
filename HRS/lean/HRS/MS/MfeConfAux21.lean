import HRS.MS.MfeConfAux20

/-!
# S.B.1, packet F3 (part 2): uniform bounds for the modulated energy of admissible kernels

The class `Sb1KerU d s k` (measurable, `-κ log(1+|z|) ≤ k(z) ≤ g(z)` for `z ≠ 0`, where `κ = 1` for `s = 0` and `κ = 0` for
`s > 0`) contains the Riesz kernel `g = rieszKernel d s` and all the truncations `k_M` of `IsP4Kernel`.  For a probability
density `ρ ≤ C_ρ` with first moment `≤ M₁`, the bounds below depend only on `(d, s, C_ρ, M₁)` and not on `k`:

* `sb1_Om_conv`: `∫ ψ(y) Ω(x-y) dy` is finite and bounded, `|k| ≤ Ω` off `0`;
* `sb1_G_upper`, `sb1_G_lower`, `sb1_c_lower`: `G(x) = ∫ρ(y)k(x-y)dy ≤ -κ log(1+|x|) + C`, `G ≥ -κ(log(1+|x|)+M₁)`;
* `sb1_E_le`: `exp(-βN F_N^k(X,ρ)) ≤ C_w` for all configurations `X` (this is where the cancellation between the pair
  repulsion and the background `e^{βG}` is used for `s = 0`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- exponent of the local majorant -/
def sb1sig (s : ℝ) : ℝ := if s = 0 then 1 / 2 else s

/-- `κ = 1` for the logarithmic kernel, `0` otherwise -/
def sb1kap (s : ℝ) : ℝ := if s = 0 then 1 else 0

theorem sb1sig_nonneg {s : ℝ} (hs0 : 0 ≤ s) : 0 ≤ sb1sig s := by
  unfold sb1sig; split_ifs <;> linarith

theorem sb1sig_lt (hd : 1 ≤ d) {s : ℝ} (hsd : s < d) : sb1sig s < d := by
  unfold sb1sig
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  split_ifs <;> linarith

theorem sb1kap_nonneg (s : ℝ) : 0 ≤ sb1kap s := by unfold sb1kap; split_ifs <;> norm_num

/-- the truncated local singularity `1_{|z|<1} |z|^{-σ}` -/
def sb1phi (d : ℕ) (σ : ℝ) (z : Euc d) : ℝ :=
  Set.indicator (Metric.ball (0 : Euc d) 1) (fun z => ‖z‖ ^ (-σ)) z

def sb1Isig (d : ℕ) (σ : ℝ) : ℝ := ∫ z, sb1phi d σ z

theorem sb1phi_nonneg (σ : ℝ) (z : Euc d) : 0 ≤ sb1phi d σ z := by
  unfold sb1phi
  exact Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg z) _) z

theorem sb1phi_meas (σ : ℝ) : Measurable (sb1phi d σ) :=
  (measurable_norm.pow_const _).indicator Metric.isOpen_ball.measurableSet

theorem sb1phi_integrable (hd : 1 ≤ d) {σ : ℝ} (hσ : σ < d) : Integrable (sb1phi d σ) := by
  have hdim : 1 ≤ Module.finrank ℝ (Euc d) := by simpa using hd
  have h1 : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-σ)) (Metric.ball 0 1) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) hdim (C := 1) (α := σ) (r := 1)
      (by simpa using hσ) ?_ ?_
    · refine ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet fun z _ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _), one_mul]
    · exact (measurable_norm.pow_const _).aestronglyMeasurable
  exact (integrable_indicator_iff Metric.isOpen_ball.measurableSet).2 h1

theorem sb1Isig_nonneg (σ : ℝ) : 0 ≤ sb1Isig d σ := integral_nonneg fun z => sb1phi_nonneg σ z

/-- `∫ ψ(y) |x-y|^{-σ} dy ≤ C_ψ I_σ + ∫ ψ`. -/
theorem sb1_conv_loc (hd : 1 ≤ d) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσd : σ < d) {ψ : Euc d → ℝ}
    (hψ0 : ∀ y, 0 ≤ ψ y) (hψm : Measurable ψ) (hψi : Integrable ψ) {Cψ : ℝ} (hψb : ∀ y, ψ y ≤ Cψ)
    (x : Euc d) :
    Integrable (fun y => ψ y * ‖x - y‖ ^ (-σ)) ∧
      ∫ y, ψ y * ‖x - y‖ ^ (-σ) ≤ Cψ * sb1Isig d σ + ∫ y, ψ y := by
  have hφ := sb1phi_integrable hd hσd
  have hφx : Integrable (fun y => sb1phi d σ (x - y)) := hφ.comp_sub_left x
  have hbd : Integrable (fun y => Cψ * sb1phi d σ (x - y) + ψ y) := (hφx.const_mul Cψ).add hψi
  have hmeas : Measurable (fun y => ψ y * ‖x - y‖ ^ (-σ)) :=
    hψm.mul ((measurable_norm.comp (measurable_const.sub measurable_id)).pow_const _)
  have hle : ∀ y, ψ y * ‖x - y‖ ^ (-σ) ≤ Cψ * sb1phi d σ (x - y) + ψ y := by
    intro y
    have hr : 0 ≤ ‖x - y‖ ^ (-σ) := Real.rpow_nonneg (norm_nonneg _) _
    by_cases h : ‖x - y‖ < 1
    · have : sb1phi d σ (x - y) = ‖x - y‖ ^ (-σ) := by
        unfold sb1phi
        rw [Set.indicator_of_mem (by simpa using h)]
      rw [this]
      nlinarith [hψ0 y, hψb y]
    · have h1 : ‖x - y‖ ^ (-σ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (not_lt.1 h) (by linarith)
      have : sb1phi d σ (x - y) = 0 := by
        unfold sb1phi
        rw [Set.indicator_of_notMem (by simpa using h)]
      rw [this]
      nlinarith [hψ0 y]
  have hint : Integrable (fun y => ψ y * ‖x - y‖ ^ (-σ)) :=
    hbd.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hψ0 y) (Real.rpow_nonneg (norm_nonneg _) _))]
      exact hle y)
  refine ⟨hint, ?_⟩
  calc ∫ y, ψ y * ‖x - y‖ ^ (-σ) ≤ ∫ y, (Cψ * sb1phi d σ (x - y) + ψ y) := integral_mono hint hbd hle
    _ = Cψ * sb1Isig d σ + ∫ y, ψ y := by
        rw [integral_add (hφx.const_mul _) hψi, integral_const_mul,
          integral_sub_left_eq_self (sb1phi d σ) volume x]
        rfl

/-! ### Admissible kernels -/

/-- the majorant `Ω(z) = log(1+|z|) + 2|z|^{-σ}` -/
def sb1Om (s : ℝ) (z : Euc d) : ℝ := Real.log (1 + ‖z‖) + 2 * ‖z‖ ^ (-(sb1sig s))

/-- admissible kernels: measurable, `-κ log(1+|z|) ≤ k z ≤ g z` for `z ≠ 0`. -/
structure Sb1KerU (d : ℕ) (s : ℝ) (k : Euc d → ℝ) : Prop where
  meas : Measurable k
  lower : ∀ z, -(sb1kap s * Real.log (1 + ‖z‖)) ≤ k z
  upper : ∀ z, z ≠ 0 → k z ≤ Whole.rieszKernel d s z

theorem sb1_neg_log_le {a : ℝ} (ha : 0 < a) : -Real.log a ≤ 2 * a ^ (-(1 / 2 : ℝ)) := by
  have ht : 0 < a ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos ha _
  have h1 := Real.one_sub_inv_le_log_of_pos ht
  rw [Real.log_rpow ha] at h1
  have e : a ^ (-(1 / 2 : ℝ)) = (a ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg ha.le _
  rw [e]
  have : 0 < (a ^ (1 / 2 : ℝ))⁻¹ := inv_pos.2 ht
  linarith

theorem sb1_k_abs_le {s : ℝ} (hs0 : 0 ≤ s) {k : Euc d → ℝ} (hk : Sb1KerU d s k) {z : Euc d} (hz : z ≠ 0) :
    |k z| ≤ sb1Om s z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hlog : 0 ≤ Real.log (1 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
  have hr : 0 ≤ ‖z‖ ^ (-(sb1sig s)) := Real.rpow_nonneg hn.le _
  have hl := hk.lower z
  have hu := hk.upper z hz
  unfold sb1Om
  by_cases h0 : s = 0
  · subst h0
    simp only [sb1kap, sb1sig, ite_true] at hl hr ⊢
    have h2 : k z ≤ 2 * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
      refine hu.trans ?_
      unfold Whole.rieszKernel
      simp only [ite_true]
      exact sb1_neg_log_le hn
    rw [abs_le]
    constructor <;> nlinarith
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h0)
    simp only [sb1kap, sb1sig, h0, ite_false] at hl hr ⊢
    have h2 : k z ≤ ‖z‖ ^ (-s) := by
      refine hu.trans (le_of_eq ?_)
      unfold Whole.rieszKernel
      simp [h0]
    rw [abs_le]
    constructor <;> nlinarith

/-- the Riesz kernel is admissible -/
theorem sb1KerU_riesz (d : ℕ) (s : ℝ) (hs0 : 0 ≤ s) : Sb1KerU d s (Whole.rieszKernel d s) where
  meas := sb1_measurable_rieszKernel s
  lower := fun z => by
    by_cases h0 : s = 0
    · subst h0
      simp only [sb1kap, ite_true, one_mul]
      unfold Whole.rieszKernel
      simp only [ite_true]
      by_cases hz : z = 0
      · subst hz; simp
      · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
        have := Real.log_le_log hn (by linarith : ‖z‖ ≤ 1 + ‖z‖)
        linarith
    · simp only [sb1kap, h0, ite_false, zero_mul, neg_zero]
      unfold Whole.rieszKernel
      simp only [h0, ite_false]
      exact Real.rpow_nonneg (norm_nonneg z) _
  upper := fun z _ => le_rfl

/-- the truncations of `IsP4Kernel` are admissible -/
theorem sb1KerU_of_p4 {s r₀ : ℝ} (hs0 : 0 ≤ s) {k : Euc d → ℝ} (hk : MP.SelfSimP4.IsP4Kernel d s r₀ k) :
    Sb1KerU d s k where
  meas := hk.smooth.continuous.measurable
  lower := fun z => by
    by_cases h0 : s = 0
    · simp only [sb1kap, h0, ite_true, one_mul]
      exact hk.lower z
    · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h0)
      simp only [sb1kap, h0, ite_false, zero_mul, neg_zero]
      exact hk.nonneg hspos z
  upper := fun z hz => hk.le_riesz z hz

end HRS.MS.MfeConf
