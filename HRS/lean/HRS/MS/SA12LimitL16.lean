import HRS.MS.SA12LimitL16A
import HRS.MS.SA12DualL2
import HRS.MS.UniqM1

/-!
# S.A.12 L16: lower semicontinuity of the local, global and weighted Sobolev norms
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MS.UniqM1

variable {d : ℕ}

theorem sa12x_sobE_lt {r : ℝ} {f : Euc d → ℝ} {a : ℝ≥0∞} (ha : a ≠ ⊤) (h : sobolevNormE r f < a) :
    HRS.PDE.ToolboxRd.MemSobolev r f ∧ HRS.PDE.ToolboxRd.sobolevNormSq r f ≤ a.toReal ^ 2 := by
  unfold sobolevNormE at h
  by_cases hm : HRS.PDE.ToolboxRd.MemSobolev r f
  · rw [if_pos hm] at h
    refine ⟨hm, ?_⟩
    have hS : 0 ≤ HRS.PDE.ToolboxRd.sobolevNormSq r f :=
      integral_nonneg fun ξ => mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)
    have := (ENNReal.ofReal_lt_iff_lt_toReal (Real.sqrt_nonneg _) ha).1 h
    calc HRS.PDE.ToolboxRd.sobolevNormSq r f = Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq r f) ^ 2 :=
          (Real.sq_sqrt hS).symm
      _ ≤ a.toReal ^ 2 := by gcongr
  · rw [if_neg hm] at h
    exact absurd h (not_lt.2 le_top)

theorem sa12x_sobE_of_le {r : ℝ} {f : Euc d → ℝ} {b : ℝ} (hb0 : 0 ≤ b)
    (hm : HRS.PDE.ToolboxRd.MemSobolev r f) (hb : HRS.PDE.ToolboxRd.sobolevNormSq r f ≤ b ^ 2) :
    sobolevNormE r f ≤ ENNReal.ofReal b := by
  unfold sobolevNormE
  rw [if_pos hm]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_iff.2 ⟨hb0, hb⟩)

/-- Weak convergence against `C_c^∞` tests extends to all `L²` tests for `L²`-bounded sequences. -/
theorem sa12x_conv_L2 {wn : ℕ → Euc d → ℝ} {w : Euc d → ℝ}
    (hwn : ∀ n, MemLp (wn n) 2 volume) (hw : MemLp w 2 volume) {A : ℝ}
    (hA : ∀ n, (eLpNorm (wn n) 2 volume).toReal ≤ A)
    (hconv : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      Tendsto (fun n => ∫ x, wn n x * ψ x) atTop (𝓝 (∫ x, w x * ψ x))) :
    ∀ ψ : Euc d → ℝ, MemLp ψ 2 volume →
      Tendsto (fun n => ∫ x, wn n x * ψ x) atTop (𝓝 (∫ x, w x * ψ x)) := by
  intro ψ hψ
  set W : ℝ := (eLpNorm w 2 volume).toReal with hW
  set K : ℝ := max A 0 + W + 1 with hK
  have hKpos : 0 < K := by
    have : 0 ≤ W := ENNReal.toReal_nonneg
    have : 0 ≤ max A 0 := le_max_right _ _
    linarith
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := ε / (4 * K) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨g, hg1, hg2, hg3⟩ := hψ.exist_eLpNorm_sub_le (p := 2) (by simp) (by norm_num) hδpos
  have hgm : MemLp g 2 volume := hg2.continuous.memLp_of_hasCompactSupport hg1
  have hdg : (eLpNorm (ψ - g) 2 volume).toReal ≤ δ := ENNReal.toReal_le_of_le_ofReal hδpos.le hg3
  have hdg' : (eLpNorm (g - ψ) 2 volume).toReal ≤ δ := by
    rw [eLpNorm_sub_comm]; exact hdg
  have hψg : MemLp (fun x => ψ x - g x) 2 volume := hψ.sub hgm
  have hgψ : MemLp (fun x => g x - ψ x) 2 volume := hgm.sub hψ
  filter_upwards [Metric.tendsto_nhds.1 (hconv g ⟨hg2, hg1⟩) (ε / 2) (half_pos hε)] with n hn
  have i1 : Integrable (fun x => wn n x * (ψ x - g x)) volume := (hwn n).integrable_mul hψg
  have i2 : Integrable (fun x => wn n x * g x) volume := (hwn n).integrable_mul hgm
  have i3 : Integrable (fun x => w x * (g x - ψ x)) volume := hw.integrable_mul hgψ
  have i4 : Integrable (fun x => w x * g x) volume := hw.integrable_mul hgm
  have k1 : ∫ x, wn n x * ψ x = (∫ x, wn n x * (ψ x - g x)) + ∫ x, wn n x * g x := by
    rw [← integral_add i1 i2]; congr 1; funext x; ring
  have k2 : ∫ x, w x * ψ x = (∫ x, w x * g x) - ∫ x, w x * (g x - ψ x) := by
    rw [← integral_sub i4 i3]; congr 1; funext x; ring
  have b1 := sa12x_cs (hwn n) hψg
  have b3 := sa12x_cs hw hgψ
  have hψg' : eLpNorm (fun x => ψ x - g x) 2 volume = eLpNorm (ψ - g) 2 volume := rfl
  have hgψ' : eLpNorm (fun x => g x - ψ x) 2 volume = eLpNorm (g - ψ) 2 volume := rfl
  rw [hψg'] at b1
  rw [hgψ'] at b3
  have hAn := hA n
  have hb1 : |∫ x, wn n x * (ψ x - g x)| ≤ K * δ := by
    refine b1.trans ?_
    have : (eLpNorm (wn n) 2 volume).toReal ≤ K := by
      have : 0 ≤ W := ENNReal.toReal_nonneg
      calc _ ≤ A := hAn
        _ ≤ max A 0 := le_max_left _ _
        _ ≤ K := by linarith
    exact mul_le_mul this hdg ENNReal.toReal_nonneg hKpos.le
  have hb3 : |∫ x, w x * (g x - ψ x)| ≤ K * δ := by
    refine b3.trans ?_
    have : W ≤ K := by
      have : 0 ≤ max A 0 := le_max_right _ _
      linarith
    exact mul_le_mul this hdg' ENNReal.toReal_nonneg hKpos.le
  have hKδ : K * δ = ε / 4 := by rw [hδ]; field_simp
  rw [Real.dist_eq] at hn ⊢
  rw [k1, k2]
  rw [abs_lt] at hn ⊢
  have b1' := abs_le.1 hb1
  have b3' := abs_le.1 hb3
  constructor <;> linarith [hn.1, hn.2, b1'.1, b1'.2, b3'.1, b3'.2]

/-- Weak lower semicontinuity of the `H^r` norm (`r ≥ 0`) for sequences converging against `C_c^∞` tests. -/
theorem sa12x_sl {r : ℝ} (hr : 0 ≤ r) {wn : ℕ → Euc d → ℝ} {w : Euc d → ℝ}
    (hw : MemLp w 2 volume)
    (hconv : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      Tendsto (fun n => ∫ x, wn n x * ψ x) atTop (𝓝 (∫ x, w x * ψ x))) :
    sobolevNormE r w ≤ liminf (fun n => sobolevNormE r (wn n)) atTop := by
  refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
  by_cases hat : a = ⊤
  · rw [hat]; exact le_top
  have hfreq : ∃ᶠ n in atTop, sobolevNormE r (wn n) < a :=
    Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) ha
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hfreq
  have hS : ∀ k, HRS.PDE.ToolboxRd.MemSobolev r (wn (φ k)) ∧
      HRS.PDE.ToolboxRd.sobolevNormSq r (wn (φ k)) ≤ a.toReal ^ 2 :=
    fun k => sa12x_sobE_lt hat (hφP k)
  have hL2 : ∀ k, (eLpNorm (wn (φ k)) 2 volume).toReal ≤ a.toReal := by
    intro k
    have h1 : sobolevNormE 0 (wn (φ k)) ≤ sobolevNormE r (wn (φ k)) := sobolevNormE_zero_le hr _
    rw [sobolevNormE_zero_eq (hS k).1.1] at h1
    exact ENNReal.toReal_mono hat (h1.trans (hφP k).le)
  have hconv' := sa12x_conv_L2 (fun k => (hS k).1.1) hw hL2
    (fun ψ hψ => (hconv ψ hψ).comp hφ.tendsto_atTop)
  obtain ⟨hM, hN⟩ := sa12x_weak_lsc r (fun k => (hS k).1.1) hw hconv' (b := a.toReal)
    (Filter.Eventually.of_forall hS).frequently
  calc sobolevNormE r w ≤ ENNReal.ofReal a.toReal := sa12x_sobE_of_le ENNReal.toReal_nonneg hM hN
    _ = a := ENNReal.ofReal_toReal hat

theorem sa12x_aesm_of_loc {u : Euc d → ℝ}
    (huloc : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (Metric.ball 0 R))) :
    AEStronglyMeasurable u volume := by
  have h1 : ∀ n : ℕ, AEStronglyMeasurable u (volume.restrict (Metric.ball (0 : Euc d) ((n : ℝ) + 1))) :=
    fun n => (huloc _ (by positivity)).aestronglyMeasurable
  have hunion : (⋃ n : ℕ, Metric.ball (0 : Euc d) ((n : ℝ) + 1)) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
    exact Set.mem_iUnion.2 ⟨n, by rw [Metric.mem_ball, dist_zero_right]; linarith⟩
  have := aestronglyMeasurable_iUnion_iff.2 h1
  rwa [hunion, Measure.restrict_univ] at this

theorem sa12x_loc_ball {u : Euc d → ℝ}
    (huloc : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (Metric.ball 0 R))) (z : Euc d) {r : ℝ}
    (hr : 0 < r) : MemLp u 2 (volume.restrict (Metric.ball z r)) :=
  (huloc (‖z‖ + r) (by positivity)).mono_measure
    (Measure.restrict_mono (Metric.ball_subset_ball' (by rw [dist_zero_right]; linarith)) le_rfl)

theorem sa12x_cut_of_loc {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (z : Euc d) {u : Euc d → ℝ}
    (hu : AEStronglyMeasurable u volume) (hloc : MemLp u 2 (volume.restrict (Metric.ball z 2))) :
    MemLp (fun x => χ (x - z) * u x) 2 volume := by
  have hχc : Continuous fun x : Euc d => χ (x - z) :=
    hχ.1.continuous.comp (continuous_id.sub continuous_const)
  have hm : AEStronglyMeasurable (fun x => χ (x - z) * u x) volume := hχc.aestronglyMeasurable.mul hu
  have hle : eLpNorm (fun x => χ (x - z) * u x) 2 volume ≤
      eLpNorm ((Metric.ball z 2).indicator u) 2 volume := by
    refine eLpNorm_mono hm fun x => ?_
    by_cases hx : x ∈ Metric.ball z 2
    · rw [Set.indicator_of_mem hx, norm_mul, Real.norm_of_nonneg (hχ.2.2.2.1 _).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχ.2.2.2.1 _).2
    · rw [Set.indicator_of_notMem hx]
      have : χ (x - z) = 0 := by
        by_contra hne
        have h1 : x - z ∈ tsupport χ := subset_tsupport _ (Function.mem_support.2 hne)
        have := hχ.2.2.1 h1
        rw [Metric.mem_ball, dist_zero_right] at this
        exact hx (by rw [Metric.mem_ball, dist_eq_norm]; exact this)
      simp [this]
  rw [memLp_iff]
  refine hle.trans_lt ?_
  rw [eLpNorm_indicator_eq_eLpNorm_restrict Metric.isOpen_ball.measurableSet]
  exact hloc.eLpNorm_lt_top

theorem sa12x_lintegral_ball_le {f : Euc d → ℝ≥0∞} (hf : AEMeasurable f volume) {M : ℝ≥0∞}
    (h : ∀ k : ℕ, ∫⁻ x in Metric.ball (0 : Euc d) ((k : ℝ) + 1), f x ≤ M) : ∫⁻ x, f x ≤ M := by
  have hmono : Monotone fun (k : ℕ) ξ => (Metric.ball (0 : Euc d) ((k : ℝ) + 1)).indicator f ξ := by
    intro j k hjk ξ
    exact Set.indicator_le_indicator_of_subset (Metric.ball_subset_ball (by
      have : (j : ℝ) ≤ k := by exact_mod_cast hjk
      linarith)) (fun _ => zero_le) ξ
  have hsup : f = fun ξ => ⨆ k : ℕ, (Metric.ball (0 : Euc d) ((k : ℝ) + 1)).indicator f ξ := by
    funext ξ
    apply le_antisymm
    · obtain ⟨k, hk'⟩ := exists_nat_ge ‖ξ‖
      refine le_trans ?_ (le_iSup _ k)
      rw [Set.indicator_of_mem (by rw [Metric.mem_ball, dist_zero_right]; linarith)]
    · exact iSup_le fun k => Set.indicator_le_self' (fun _ _ => zero_le) ξ
  rw [hsup, lintegral_iSup' (fun k => hf.indicator Metric.isOpen_ball.measurableSet)
    (Filter.Eventually.of_forall fun ξ => fun j k hjk => hmono hjk ξ)]
  refine iSup_le fun k => ?_
  rw [lintegral_indicator Metric.isOpen_ball.measurableSet]
  exact h k

theorem sa12x_sq_le_sq {a b : ℝ≥0∞} (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  have e : ∀ x : ℝ≥0∞, (x ^ 2) ^ (1 / 2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  calc a = (a ^ 2) ^ (1 / 2 : ℝ) := (e a).symm
    _ ≤ (b ^ 2) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = b := e b

/-- A locally `L²` function paired boundedly against all `C_c^∞` tests lies in `L²`. -/
theorem sa12x_global_L2 {u : Euc d → ℝ}
    (huloc : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (Metric.ball 0 R)))
    {A : ℝ} (hA : 0 ≤ A)
    (hpair : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      |∫ x, u x * ψ x| ≤ A * (eLpNorm ψ 2 volume).toReal) :
    MemLp u 2 volume ∧ eLpNorm u 2 volume ≤ ENNReal.ofReal A := by
  have hu := sa12x_aesm_of_loc huloc
  have hint : ∀ k : ℕ, ∫⁻ x in Metric.ball (0 : Euc d) ((k : ℝ) + 1), ‖u x‖ₑ ^ 2 ≤
      ENNReal.ofReal A ^ 2 := by
    intro k
    let ρ : ContDiffBump (0 : Euc d) := ⟨(k : ℝ) + 1, (k : ℝ) + 2, by positivity, by linarith⟩
    have hρc : Continuous (ρ : Euc d → ℝ) := ρ.continuous
    have hρs : ∀ x, ρ x ≠ 0 → x ∈ Metric.ball (0 : Euc d) ((k : ℝ) + 2) := by
      intro x hx
      have := ρ.support_eq
      rw [← this] at *
      simpa [ρ] using Function.mem_support.2 hx
    have hmem : MemLp (fun x => ρ x * u x) 2 volume := by
      have hloc : MemLp u 2 (volume.restrict (Metric.ball (0 : Euc d) ((k : ℝ) + 2))) :=
        huloc _ (by positivity)
      have hm : AEStronglyMeasurable (fun x => ρ x * u x) volume := hρc.aestronglyMeasurable.mul hu
      have hle : eLpNorm (fun x => ρ x * u x) 2 volume ≤
          eLpNorm ((Metric.ball (0 : Euc d) ((k : ℝ) + 2)).indicator u) 2 volume := by
        refine eLpNorm_mono hm fun x => ?_
        by_cases hx : x ∈ Metric.ball (0 : Euc d) ((k : ℝ) + 2)
        · rw [Set.indicator_of_mem hx, norm_mul, Real.norm_of_nonneg ρ.nonneg]
          exact mul_le_of_le_one_left (norm_nonneg _) ρ.le_one
        · rw [Set.indicator_of_notMem hx]
          have : ρ x = 0 := by by_contra hne; exact hx (hρs x hne)
          simp [this]
      rw [memLp_iff]
      refine hle.trans_lt ?_
      rw [eLpNorm_indicator_eq_eLpNorm_restrict Metric.isOpen_ball.measurableSet]
      exact hloc.eLpNorm_lt_top
    have hdual := sa12x_dual hmem hA fun ψ hψ => by
      have hψ' : IsCcInfty (fun x => ρ x * ψ x) := ⟨ρ.contDiff.mul hψ.1, hψ.2.mul_left⟩
      have e1 : (fun x => (ρ x * u x) * ψ x) = fun x => u x * (ρ x * ψ x) := funext fun x => by ring
      rw [e1]
      refine (hpair _ hψ').trans (mul_le_mul_of_nonneg_left ?_ hA)
      have hψm : MemLp ψ 2 volume := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2
      refine ENNReal.toReal_mono hψm.eLpNorm_ne_top (eLpNorm_mono (hρc.aestronglyMeasurable.mul
        hψm.aestronglyMeasurable) fun x => ?_)
      rw [norm_mul, Real.norm_of_nonneg ρ.nonneg]
      exact mul_le_of_le_one_left (norm_nonneg _) ρ.le_one
    have hsq : eLpNorm (fun x => ρ x * u x) 2 volume ^ 2 ≤ ENNReal.ofReal A ^ 2 :=
      pow_le_pow_left' hdual 2
    rw [sq_eLpNorm_two hmem.aestronglyMeasurable] at hsq
    refine le_trans ?_ hsq
    calc ∫⁻ x in Metric.ball (0 : Euc d) ((k : ℝ) + 1), ‖u x‖ₑ ^ 2
        = ∫⁻ x in Metric.ball (0 : Euc d) ((k : ℝ) + 1), ‖ρ x * u x‖ₑ ^ 2 := by
          refine setLIntegral_congr_fun Metric.isOpen_ball.measurableSet fun x hx => ?_
          rw [ρ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx), one_mul]
      _ ≤ _ := setLIntegral_le_lintegral _ _
  have hall := sa12x_lintegral_ball_le (f := fun x => ‖u x‖ₑ ^ 2) (hu.enorm.pow_const 2) hint
  have hu2 : eLpNorm u 2 volume ≤ ENNReal.ofReal A := by
    refine sa12x_sq_le_sq ?_
    rw [sq_eLpNorm_two hu]; exact hall
  exact ⟨hu2.trans_lt ENNReal.ofReal_lt_top, hu2⟩

theorem sa12x_sobE_le {r : ℝ} {f : Euc d → ℝ} {b : ℝ} (hb0 : 0 ≤ b)
    (h : sobolevNormE r f ≤ ENNReal.ofReal b) :
    HRS.PDE.ToolboxRd.MemSobolev r f ∧ HRS.PDE.ToolboxRd.sobolevNormSq r f ≤ b ^ 2 := by
  unfold sobolevNormE at h
  by_cases hm : HRS.PDE.ToolboxRd.MemSobolev r f
  · rw [if_pos hm] at h
    refine ⟨hm, ?_⟩
    have hS : 0 ≤ HRS.PDE.ToolboxRd.sobolevNormSq r f :=
      integral_nonneg fun ξ => mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)
    have := (ENNReal.ofReal_le_ofReal_iff hb0).1 h
    calc HRS.PDE.ToolboxRd.sobolevNormSq r f = Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq r f) ^ 2 :=
          (Real.sq_sqrt hS).symm
      _ ≤ b ^ 2 := by gcongr
  · rw [if_neg hm] at h
    exact absurd h (not_le.2 ENNReal.ofReal_lt_top)

-- BEGIN SA12.L16
theorem local_norm_lower_semicontinuity (hd : 1 ≤ d) (m : ℕ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (B : ℝ)
    (un : ℕ → Euc d → ℝ) (u : Euc d → ℝ)
    (huloc : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (Metric.ball 0 R)))
    (hconv : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      Tendsto (fun n => ∫ x, un n x * ψ x) atTop (𝓝 (∫ x, u x * ψ x)))
    (hB : ∀ n, ulocNormE m χ (un n) ≤ ENNReal.ofReal B) :
    ulocNormE m χ u ≤ ENNReal.ofReal B ∧
      (∀ B' : ℝ, (∀ n, sobolevNormE (m : ℝ) (un n) ≤ ENNReal.ofReal B') →
        sobolevNormE (m : ℝ) u ≤ ENNReal.ofReal B') ∧
      varpiNormE m χ u ≤ liminf (fun n => varpiNormE m χ (un n)) atTop := by
  have hu := sa12x_aesm_of_loc huloc
  have hsl : ∀ c : Euc d, sobolevNormE (m : ℝ) (fun x => χ (x - c) * u x) ≤
      liminf (fun n => sobolevNormE (m : ℝ) (fun x => χ (x - c) * un n x)) atTop := by
    intro c
    refine sa12x_sl (Nat.cast_nonneg m) (sa12x_cut_of_loc hχ c hu (sa12x_loc_ball huloc c two_pos))
      fun ψ hψ => ?_
    have hψ' : IsCcInfty (fun x => χ (x - c) * ψ x) :=
      ⟨(hχ.1.comp (contDiff_id.sub contDiff_const)).mul hψ.1, hψ.2.mul_left⟩
    have h1 := hconv _ hψ'
    have e : ∀ (f : Euc d → ℝ) (x : Euc d), χ (x - c) * f x * ψ x = f x * (χ (x - c) * ψ x) :=
      fun f x => by ring
    simp_rw [e]
    exact h1
  refine ⟨?_, ?_, ?_⟩
  · refine iSup_le fun z => (hsl z).trans ?_
    refine liminf_le_of_frequently_le' (Filter.Eventually.of_forall fun n => ?_).frequently
    exact (le_iSup (fun z : Euc d => sobolevNormE (m : ℝ) fun x => χ (x - z) * un n x) z).trans (hB n)
  · intro B' hB'
    set b : ℝ := max B' 0 with hb
    have hb0 : 0 ≤ b := le_max_right _ _
    have hbB : ENNReal.ofReal B' ≤ ENNReal.ofReal b := ENNReal.ofReal_le_ofReal (le_max_left _ _)
    have hun : ∀ n, MemLp (un n) 2 volume := fun n =>
      (sa12x_sobE_le hb0 ((hB' n).trans hbB)).1.1
    have hL2 : ∀ n, (eLpNorm (un n) 2 volume).toReal ≤ b := by
      intro n
      have h1 : sobolevNormE 0 (un n) ≤ sobolevNormE (m : ℝ) (un n) := sobolevNormE_zero_le (Nat.cast_nonneg m) _
      rw [sobolevNormE_zero_eq (hun n)] at h1
      exact ENNReal.toReal_le_of_le_ofReal hb0 (h1.trans ((hB' n).trans hbB))
    have hpair : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → |∫ x, u x * ψ x| ≤ b * (eLpNorm ψ 2 volume).toReal := by
      intro ψ hψ
      have hψm : MemLp ψ 2 volume := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2
      refine le_of_tendsto' (hconv ψ hψ).abs fun n => ?_
      exact (sa12x_cs (hun n) hψm).trans (mul_le_mul_of_nonneg_right (hL2 n) ENNReal.toReal_nonneg)
    obtain ⟨hu2, -⟩ := sa12x_global_L2 huloc hb0 hpair
    refine (sa12x_sl (Nat.cast_nonneg m) hu2 hconv).trans ?_
    exact liminf_le_of_frequently_le' (Filter.Eventually.of_forall hB').frequently
  · set wz : (Fin d → ℤ) → ℝ≥0∞ := fun z => ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) with hwz
    set N : (Fin d → ℤ) → ℕ → ℝ≥0∞ := fun z n =>
      sobolevNormE (m : ℝ) (fun x => χ (x - cellPt d z) * un n x) with hN
    set Nu : (Fin d → ℤ) → ℝ≥0∞ := fun z =>
      sobolevNormE (m : ℝ) (fun x => χ (x - cellPt d z) * u x) with hNu
    have hterm : ∀ z, wz z * Nu z ^ 2 ≤ liminf (fun n => wz z * N z n ^ 2) atTop := by
      intro z
      have hg : Monotone (fun x : ℝ≥0∞ => wz z * x ^ 2) := fun a b hab => by simp only []; gcongr
      have hcont : Continuous (fun x : ℝ≥0∞ => wz z * x ^ 2) :=
        (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp (ENNReal.continuous_pow 2)
      have h1 := hg.map_liminf_of_continuousAt (F := atTop) (N z) hcont.continuousAt
      calc wz z * Nu z ^ 2 ≤ wz z * (liminf (N z) atTop) ^ 2 := hg (hsl (cellPt d z))
        _ = liminf ((fun x : ℝ≥0∞ => wz z * x ^ 2) ∘ N z) atTop := h1
        _ = liminf (fun n => wz z * N z n ^ 2) atTop := rfl
    have hsum : ∑' z, wz z * Nu z ^ 2 ≤ liminf (fun n => ∑' z, wz z * N z n ^ 2) atTop := by
      calc ∑' z, wz z * Nu z ^ 2 ≤ ∑' z, liminf (fun n => wz z * N z n ^ 2) atTop :=
            ENNReal.tsum_le_tsum hterm
        _ = ∫⁻ z, liminf (fun n => wz z * N z n ^ 2) atTop ∂Measure.count := (lintegral_count _).symm
        _ ≤ liminf (fun n => ∫⁻ z, wz z * N z n ^ 2 ∂Measure.count) atTop :=
            lintegral_liminf_le (fun n => measurable_of_countable _)
        _ = liminf (fun n => ∑' z, wz z * N z n ^ 2) atTop := by
            simp_rw [lintegral_count]
    show (∑' z, wz z * Nu z ^ 2) ^ (1 / 2 : ℝ) ≤
      liminf (fun n => (∑' z, wz z * N z n ^ 2) ^ (1 / 2 : ℝ)) atTop
    have hg1 : Monotone (fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ)) := fun a b h =>
      ENNReal.rpow_le_rpow h (by norm_num)
    have hc1 : Continuous (fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ)) := ENNReal.continuous_rpow_const
    have h2 := hg1.map_liminf_of_continuousAt (F := atTop) (fun n => ∑' z, wz z * N z n ^ 2) hc1.continuousAt
    exact (hg1 hsum).trans (le_of_eq h2)
-- END SA12.L16

end HRS.MH.AdjointRd.Phase2SA12Limit
