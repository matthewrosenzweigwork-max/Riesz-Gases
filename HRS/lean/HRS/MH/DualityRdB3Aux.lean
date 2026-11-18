import HRS.MH.DualityRdB2

/-!
# DualityRd packet B3 (auxiliary): ingredients of the time-dependent weak form on `ℝ^d`

Integrability of densities against bounded or linearly growing continuous functions, the clamped test
function `Φ(u,x) = f_{clamp u}(x)` (jointly continuous on `ℝ × ℝ^d`), the fundamental theorem of calculus in time
for `f`, Fubini on `ℝ^d × [a,b]`, the increment identity `⟨ρ_b, f_b⟩ - ⟨ρ_a, f_a⟩ = ∫_a^b ⟨ρ_b, ∂_u f_u⟩ du +
∫_a^b mfGen(f_a, ρ_r) dr`, and the telescoping lemma.  Helper names carry the prefix `db3_`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.DualityRd

open HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-! ### Integrability against densities -/

theorem db3_int_bdd {ρ ψ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) (hψ : Continuous ψ) {C : ℝ}
    (hC : ∀ x, |ψ x| ≤ C) : Integrable (fun x => ρ x * ψ x) := by
  refine ((db1_prob_integrable hρ).const_mul C).mono'
    (hρ.measurable.mul hψ.measurable).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg x)]
  calc ρ x * |ψ x| ≤ ρ x * C := mul_le_mul_of_nonneg_left (hC x) (hρ.nonneg x)
    _ = C * ρ x := mul_comm _ _

theorem db3_int_one_add {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ)
    (hρ2 : Integrable (fun x => ρ x * ‖x‖ ^ 2)) : Integrable (fun x => ρ x * (1 + ‖x‖)) := by
  have hb : Integrable (fun x => 2 * ρ x + ρ x * ‖x‖ ^ 2) :=
    ((db1_prob_integrable hρ).const_mul 2).add hρ2
  refine hb.mono' (hρ.measurable.mul (by fun_prop : Measurable fun x : Euc d => 1 + ‖x‖)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ.nonneg x) (by positivity))]
  have h1 : 1 + ‖x‖ ≤ 2 + ‖x‖ ^ 2 := by nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1)]
  nlinarith [mul_le_mul_of_nonneg_left h1 (hρ.nonneg x)]

theorem db3_int_lin {ρ ψ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ)
    (hρ2 : Integrable (fun x => ρ x * ‖x‖ ^ 2)) (hψ : Continuous ψ) {B : ℝ}
    (hB : ∀ x, |ψ x| ≤ B * (1 + ‖x‖)) : Integrable (fun x => ρ x * ψ x) := by
  have hB' : ∀ x, |ψ x| ≤ |B| * (1 + ‖x‖) := fun x =>
    (hB x).trans (mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity))
  have hb : Integrable (fun x => |B| * (ρ x * (1 + ‖x‖))) :=
    (db3_int_one_add hρ hρ2).const_mul |B|
  refine hb.mono' (hρ.measurable.mul hψ.measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg x)]
  calc ρ x * |ψ x| ≤ ρ x * (|B| * (1 + ‖x‖)) := mul_le_mul_of_nonneg_left (hB' x) (hρ.nonneg x)
    _ = |B| * (ρ x * (1 + ‖x‖)) := by ring

theorem db3_pair_add {ρ' : Euc d → ℝ} {ψ χ : Euc d → ℝ}
    (hψ : Integrable (fun x => ρ' x * ψ x)) (hχ : Integrable (fun x => ρ' x * χ x))
    (hρ' : Whole.IsProbDensity ρ') :
    Whole.pair (Whole.withDensityReal ρ') (fun x => ψ x + χ x)
      = Whole.pair (Whole.withDensityReal ρ') ψ + Whole.pair (Whole.withDensityReal ρ') χ := by
  rw [Q09A.pair_withDensityReal hρ', Q09A.pair_withDensityReal hρ', Q09A.pair_withDensityReal hρ']
  rw [← integral_add hψ hχ]
  congr 1
  funext x
  ring

/-! ### The clamped test function -/

theorem db3_clamp_mem {t : ℝ} (ht : 0 ≤ t) (u : ℝ) : max 0 (min u t) ∈ Set.Icc (0 : ℝ) t :=
  ⟨le_max_left _ _, max_le ht (min_le_right _ _)⟩

theorem db3_clamp_eq {t u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) t) : max 0 (min u t) = u := by
  rw [min_eq_left hu.2, max_eq_right hu.1]

theorem db3_Phi_cont {t : ℝ} (ht : 0 ≤ t) {ft : ℝ → Euc d → ℝ}
    (hft : Continuous fun q : Set.Icc (0 : ℝ) t × Euc d => ft q.1.1 q.2) :
    Continuous (fun q : ℝ × Euc d => ft (max 0 (min q.1 t)) q.2) := by
  have hc1 : Continuous (fun q : ℝ × Euc d => max 0 (min q.1 t)) :=
    continuous_const.max (continuous_fst.min continuous_const)
  have hc : Continuous (fun q : ℝ × Euc d =>
      ((⟨max 0 (min q.1 t), db3_clamp_mem ht q.1⟩ : Set.Icc (0 : ℝ) t), q.2)) :=
    (Continuous.subtype_mk hc1 (fun q => db3_clamp_mem ht q.1)).prodMk continuous_snd
  exact hft.comp hc

/-! ### Time regularity of `f` -/

theorem db3_slice_on {φ : ℝ → Euc d → ℝ} {t : ℝ}
    (hφc : ContinuousOn (Function.uncurry φ) (Set.Icc (0 : ℝ) t ×ˢ Set.univ)) (x : Euc d) :
    ContinuousOn (fun u => φ u x) (Set.Icc (0 : ℝ) t) :=
  hφc.comp (continuousOn_id.prodMk continuousOn_const) (fun u hu => ⟨hu, Set.mem_univ _⟩)

theorem db3_f_joint {t : ℝ} {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) :
    ContinuousOn (Function.uncurry f) (Set.Icc (0 : ℝ) t ×ˢ Set.univ) := by
  have h0 := hf.cont_c2 0 (by norm_num)
  have hG : Continuous fun q : Set.Icc (0 : ℝ) t × Euc d => f q.1.1 q.2 := by
    have h1 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Euc d) ℝ
      (fun i => i.elim0)).continuous.comp h0
    refine h1.congr fun q => ?_
    simp [iteratedFDeriv_zero_apply]
  exact db2_contOn_subtype hG

/-- Fundamental theorem of calculus in time, for each fixed `x`. -/
theorem db3_ftc {t : ℝ} {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbt : b ≤ t) (x : Euc d) : ∫ u in a..b, ft u x = f b x - f a x := by
  have hfc : ContinuousOn (fun u => f u x) (Set.Icc a b) :=
    (db3_slice_on (φ := f) (db3_f_joint hf) x).mono (Set.Icc_subset_Icc ha hbt)
  have hftc : ContinuousOn (fun u => ft u x) (Set.Icc a b) :=
    (db3_slice_on (φ := ft) (db2_contOn_subtype hf.cont_time_deriv) x).mono (Set.Icc_subset_Icc ha hbt)
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hfc (fun u hu => ?_)
    (hftc.intervalIntegrable_of_Icc hab)
  exact hf.time_deriv x u ⟨lt_of_le_of_lt ha hu.1, hu.2.trans_le hbt⟩

/-! ### Fubini on `ℝ^d × [a,b]` -/

theorem db3_fubini {ρ' : Euc d → ℝ} (hρ' : Whole.IsProbDensity ρ')
    (hρ2 : Integrable (fun x => ρ' x * ‖x‖ ^ 2)) {t : ℝ} (ht : 0 ≤ t) {ft : ℝ → Euc d → ℝ}
    (hft : Continuous fun q : Set.Icc (0 : ℝ) t × Euc d => ft q.1.1 q.2) {B : ℝ}
    (hB : ∀ u ∈ Set.Icc (0 : ℝ) t, ∀ x, |ft u x| ≤ B * (1 + ‖x‖)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbt : b ≤ t) :
    ∫ x, ρ' x * (∫ u in a..b, ft u x) = ∫ u in a..b, Whole.pair (Whole.withDensityReal ρ') (ft u) := by
  set Φ : ℝ → Euc d → ℝ := fun u x => ft (max 0 (min u t)) x with hΦdef
  have hΦc : Continuous (fun q : ℝ × Euc d => Φ q.1 q.2) := db3_Phi_cont ht hft
  have hΦB : ∀ u : ℝ, ∀ x, |Φ u x| ≤ |B| * (1 + ‖x‖) := fun u x => by
    have := hB _ (db3_clamp_mem ht u) x
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity))
  have hFi : Integrable (fun z : Euc d × ℝ => ρ' z.1 * Φ z.2 z.1)
      ((volume : Measure (Euc d)).prod (volume.restrict (Set.Ioc a b))) := by
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
    have hg : Integrable (fun x : Euc d => |B| * (ρ' x * (1 + ‖x‖))) :=
      (db3_int_one_add hρ' hρ2).const_mul |B|
    have hprod := hg.mul_prod (integrable_const (1 : ℝ) (μ := volume.restrict (Set.Ioc a b)))
    refine hprod.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact ((hρ'.measurable.comp measurable_fst).mul
        (hΦc.measurable.comp (measurable_snd.prodMk measurable_fst))).aestronglyMeasurable
    · show ‖ρ' z.1 * Φ z.2 z.1‖ ≤ (|B| * (ρ' z.1 * (1 + ‖z.1‖))) * 1
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hρ'.nonneg z.1)]
      calc ρ' z.1 * |Φ z.2 z.1| ≤ ρ' z.1 * (|B| * (1 + ‖z.1‖)) :=
            mul_le_mul_of_nonneg_left (hΦB _ _) (hρ'.nonneg _)
        _ = (|B| * (ρ' z.1 * (1 + ‖z.1‖))) * 1 := by ring
  have hswap := integral_integral_swap (μ := volume) (ν := volume.restrict (Set.Ioc a b))
    (f := fun x u => ρ' x * Φ u x) hFi
  have e1 : ∀ x : Euc d, ∫ u in a..b, ft u x = ∫ u, Φ u x ∂(volume.restrict (Set.Ioc a b)) := by
    intro x
    rw [intervalIntegral.integral_of_le hab]
    refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
    have hu' : u ∈ Set.Icc (0 : ℝ) t := ⟨ha.trans (le_of_lt hu.1), hu.2.trans hbt⟩
    show ft u x = ft (max 0 (min u t)) x
    rw [db3_clamp_eq hu']
  calc ∫ x, ρ' x * (∫ u in a..b, ft u x)
      = ∫ x, ∫ u, ρ' x * Φ u x ∂(volume.restrict (Set.Ioc a b)) := by
        congr 1
        funext x
        rw [e1 x, integral_const_mul]
    _ = ∫ u, ∫ x, ρ' x * Φ u x ∂volume ∂(volume.restrict (Set.Ioc a b)) := hswap
    _ = ∫ u in a..b, Whole.pair (Whole.withDensityReal ρ') (ft u) := by
        rw [intervalIntegral.integral_of_le hab]
        refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
        have hu' : u ∈ Set.Icc (0 : ℝ) t := ⟨ha.trans (le_of_lt hu.1), hu.2.trans hbt⟩
        show ∫ x, ρ' x * Φ u x = Whole.pair (Whole.withDensityReal ρ') (ft u)
        rw [Q09A.pair_withDensityReal hρ' (ft u)]
        congr 1
        funext x
        show ρ' x * ft (max 0 (min u t)) x = ρ' x * ft u x
        rw [db3_clamp_eq hu']

/-! ### Telescoping -/

theorem db3_telescope {H : ℝ → ℝ} {t s ε : ℝ} (hs : 0 < s)
    (hloc : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ t → b - a ≤ s → |H b - H a| ≤ ε * (b - a)) :
    ∀ n : ℕ, ∀ b : ℝ, 0 ≤ b → b ≤ t → b ≤ n * s → |H b - H 0| ≤ ε * b := by
  intro n
  induction n with
  | zero =>
    intro b hb0 _ hb
    have hb' : b = 0 := by
      have : b ≤ 0 := by simpa using hb
      linarith
    rw [hb']
    simp
  | succ n ih =>
    intro b hb0 hbt hb
    by_cases hle : b ≤ n * s
    · exact ih b hb0 hbt hle
    · push_neg at hle
      have hn0 : (0 : ℝ) ≤ n * s := by positivity
      have h1 := hloc (n * s) b hn0 hle.le hbt (by push_cast at hb; linarith)
      have h2 := ih (n * s) hn0 (by linarith) le_rfl
      calc |H b - H 0| = |(H b - H (n * s)) + (H (n * s) - H 0)| := by ring_nf
        _ ≤ |H b - H (n * s)| + |H (n * s) - H 0| := abs_add_le _ _
        _ ≤ ε * (b - n * s) + ε * (n * s) := add_le_add h1 h2
        _ = ε * b := by ring

end HRS.MH.DualityRd
