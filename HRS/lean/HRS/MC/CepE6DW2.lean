import HRS.MC.CepE6DW1

/-!
# Packet CEPE6D, part 3b: the weak-limit lemma W (existence of `Λ`, total variation)
-/

open Set Filter Topology
open scoped RealInnerProductSpace ContDiff

noncomputable section

namespace HRS.MC.CepE6D

variable {N : ℕ}

/-- Restriction of a function continuous on `[0,T]` to an element of `C([0,T]; ℝ^N)`. -/
def ofFun {T : ℝ} (f : ℝ → Ch6D N) (hf : ContinuousOn f (Icc 0 T)) : C(Icc (0 : ℝ) T, Ch6D N) :=
  ⟨(Icc 0 T).restrict f, hf.restrict⟩

/-- Extension of `f ∈ C([0,T]; ℝ^N)` to `ℝ` (constant outside). -/
def extFun {T : ℝ} (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, Ch6D N)) : ℝ → Ch6D N := Set.IccExtend hT f

theorem extFun_continuous {T : ℝ} (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, Ch6D N)) :
    Continuous (extFun hT f) := Continuous.Icc_extend' f.continuous

theorem extFun_apply {T : ℝ} (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, Ch6D N)) {s : ℝ} (hs : s ∈ Icc 0 T) :
    extFun hT f s = f ⟨s, hs⟩ := by
  simp [extFun, Set.IccExtend_of_mem hT f hs]

theorem norm_extFun_le {T : ℝ} (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, Ch6D N)) {s : ℝ} (hs : s ∈ Icc 0 T) :
    ‖extFun hT f s‖ ≤ ‖f‖ := by
  rw [extFun_apply hT f hs]; exact f.norm_coe_le_norm _

theorem extFun_ofFun {T : ℝ} (hT : 0 ≤ T) (f : ℝ → Ch6D N) (hf : ContinuousOn f (Icc 0 T)) {s : ℝ}
    (hs : s ∈ Icc 0 T) : extFun hT (ofFun f hf) s = f s := by
  rw [extFun_apply hT _ hs]; rfl

theorem extFun_add {T : ℝ} (hT : 0 ≤ T) (f g : C(Icc (0 : ℝ) T, Ch6D N)) (s : ℝ) :
    extFun hT (f + g) s = extFun hT f s + extFun hT g s := by
  simp [extFun, Set.IccExtend]

theorem extFun_smul {T : ℝ} (hT : 0 ≤ T) (c : ℝ) (f : C(Icc (0 : ℝ) T, Ch6D N)) (s : ℝ) :
    extFun hT (c • f) s = c • extFun hT f s := by
  simp [extFun, Set.IccExtend]

theorem Lfun_add {T : ℝ} (hT : 0 ≤ T) {b f g : ℝ → Ch6D N} (hb : ContinuousOn b (Icc 0 T))
    (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T)) :
    Lfun T b (fun s => f s + g s) = Lfun T b f + Lfun T b g := by
  unfold Lfun
  rw [← intervalIntegral.integral_add (integrable_inner hT hf hb) (integrable_inner hT hg hb)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp [inner_add_left]

theorem Lfun_smul {T : ℝ} (c : ℝ) (b f : ℝ → Ch6D N) :
    Lfun T b (fun s => c • f s) = c * Lfun T b f := by
  unfold Lfun
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp [inner_smul_left]

theorem Lfun_congr {T : ℝ} (hT : 0 ≤ T) {b f g : ℝ → Ch6D N} (h : ∀ s ∈ Icc 0 T, f s = g s) :
    Lfun T b f = Lfun T b g := by
  unfold Lfun
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le hT] at hs
  simp only [h s hs]

theorem integral_norm_nonneg {T : ℝ} (hT : 0 ≤ T) (b : ℝ → Ch6D N) : 0 ≤ ∫ s in (0 : ℝ)..T, ‖b s‖ :=
  intervalIntegral.integral_nonneg hT fun _ _ => norm_nonneg _

/-- The limit of `∫_0^T ⟨f, b_n⟩ ds` (junk when it does not exist). -/
def LimL (T : ℝ) (b : ℕ → ℝ → Ch6D N) (f : ℝ → Ch6D N) : ℝ := limUnder atTop (fun n => Lfun T (b n) f)

section Main

variable {T : ℝ} {b : ℕ → ℝ → Ch6D N} {A : ℝ → Ch6D N} {K : ℝ}

theorem cauchy_Lfun (hT : 0 ≤ T) (hb : ∀ n, Continuous (b n))
    (hA : TendstoUniformlyOn (fun n => prim (b n)) A atTop (Icc 0 T))
    (hK : ∀ᶠ n in atTop, ∫ s in (0 : ℝ)..T, ‖b n s‖ ≤ K) {f : ℝ → Ch6D N}
    (hf : ContinuousOn f (Icc 0 T)) : CauchySeq (fun n => Lfun T (b n) f) := by
  obtain ⟨n0, hn0⟩ := hK.exists
  have hK0 : 0 ≤ K := (integral_norm_nonneg hT (b n0)).trans hn0
  rw [Metric.cauchySeq_iff']
  intro ε hε
  set η : ℝ := ε / (4 * (K + 1)) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨g, hg, hfg⟩ := exists_smooth_approx hf hηpos
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast le_top)
  have hconv := tendsto_Lfun_C1 hT hb hA hg1
  have hηK : η * K ≤ ε / 4 := by
    rw [hη, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- key estimate
  have hdiff : ∀ n, ∫ s in (0 : ℝ)..T, ‖b n s‖ ≤ K → |Lfun T (b n) f - Lfun T (b n) g| ≤ ε / 4 := by
    intro n hn
    rw [← Lfun_sub hT (hb n).continuousOn hf hg1.continuous.continuousOn]
    refine (abs_Lfun_le hT (hb n).continuousOn (M := η) fun s hs => hfg s hs).trans ?_
    calc η * ∫ s in (0 : ℝ)..T, ‖b n s‖ ≤ η * K := mul_le_mul_of_nonneg_left hn hηpos.le
      _ ≤ ε / 4 := hηK
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hK.and (Metric.tendsto_nhds.1 hconv (ε / 4) (by positivity)))
  refine ⟨N0, fun n hn => ?_⟩
  obtain ⟨hKn, hcn⟩ := hN0 n hn
  obtain ⟨hKN, hcN⟩ := hN0 N0 le_rfl
  have h1 := hdiff n hKn
  have h2 := hdiff N0 hKN
  rw [Real.dist_eq] at hcn hcN ⊢
  have e : Lfun T (b n) f - Lfun T (b N0) f =
      (Lfun T (b n) f - Lfun T (b n) g) + (Lfun T (b n) g - (⟪g T, A T⟫ - ∫ s in (0 : ℝ)..T, ⟪deriv g s, A s⟫)) -
      (Lfun T (b N0) g - (⟪g T, A T⟫ - ∫ s in (0 : ℝ)..T, ⟪deriv g s, A s⟫)) -
      (Lfun T (b N0) f - Lfun T (b N0) g) := by ring
  rw [e]
  obtain ⟨a1, a2⟩ := abs_le.1 h1
  obtain ⟨b1, b2⟩ := abs_lt.1 hcn
  obtain ⟨c1, c2⟩ := abs_lt.1 hcN
  obtain ⟨d1, d2⟩ := abs_le.1 h2
  rw [abs_lt]
  constructor <;> linarith


theorem tendsto_LimL (hT : 0 ≤ T) (hb : ∀ n, Continuous (b n))
    (hA : TendstoUniformlyOn (fun n => prim (b n)) A atTop (Icc 0 T))
    (hK : ∀ᶠ n in atTop, ∫ s in (0 : ℝ)..T, ‖b n s‖ ≤ K) {f : ℝ → Ch6D N}
    (hf : ContinuousOn f (Icc 0 T)) : Tendsto (fun n => Lfun T (b n) f) atTop (𝓝 (LimL T b f)) := by
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete (cauchy_Lfun hT hb hA hK hf)
  rw [LimL, hl.limUnder_eq]; exact hl

theorem LimL_congr (hT : 0 ≤ T) {f g : ℝ → Ch6D N} (h : ∀ s ∈ Icc 0 T, f s = g s) :
    LimL T b f = LimL T b g := by
  unfold LimL
  have : (fun n => Lfun T (b n) f) = fun n => Lfun T (b n) g := funext fun n => Lfun_congr hT h
  rw [this]

theorem abs_LimL_le (hT : 0 ≤ T) (hb : ∀ n, Continuous (b n))
    (hA : TendstoUniformlyOn (fun n => prim (b n)) A atTop (Icc 0 T))
    (hK : ∀ᶠ n in atTop, ∫ s in (0 : ℝ)..T, ‖b n s‖ ≤ K) {f : ℝ → Ch6D N}
    (hf : ContinuousOn f (Icc 0 T)) {M : ℝ} (hM : ∀ s ∈ Icc 0 T, ‖f s‖ ≤ M) :
    |LimL T b f| ≤ M * K := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  refine le_of_tendsto ((tendsto_LimL hT hb hA hK hf).abs) ?_
  filter_upwards [hK] with n hn
  exact (abs_Lfun_le hT (hb n).continuousOn hM).trans (mul_le_mul_of_nonneg_left hn hM0)

/-- Total variation bound for the limit path. -/
theorem sum_norm_prim_le {c : ℝ → Ch6D N} (hc : Continuous c) {u : ℕ → ℝ} (hu : Monotone u) (n : ℕ) :
    ∑ i ∈ Finset.range n, ‖prim c (u (i + 1)) - prim c (u i)‖ ≤ ∫ s in (u 0)..(u n), ‖c s‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hint : ∀ x y : ℝ, IntervalIntegrable c MeasureTheory.volume x y := fun x y =>
      hc.intervalIntegrable x y
    have hint' : ∀ x y : ℝ, IntervalIntegrable (fun s => ‖c s‖) MeasureTheory.volume x y := fun x y =>
      hc.norm.intervalIntegrable x y
    have h1 : prim c (u (n + 1)) - prim c (u n) = ∫ s in (u n)..(u (n + 1)), c s := by
      unfold prim
      rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 (u n)) (hint (u n) (u (n + 1)))]
      abel
    have h2 : ‖∫ s in (u n)..(u (n + 1)), c s‖ ≤ ∫ s in (u n)..(u (n + 1)), ‖c s‖ :=
      intervalIntegral.norm_integral_le_integral_norm (hu (Nat.le_succ n))
    rw [h1, ← intervalIntegral.integral_add_adjacent_intervals (hint' (u 0) (u n)) (hint' (u n) (u (n + 1)))]
    linarith

theorem eVariation_le (hT : 0 ≤ T) (hb : ∀ n, Continuous (b n))
    (hA : TendstoUniformlyOn (fun n => prim (b n)) A atTop (Icc 0 T))
    (hK : ∀ᶠ n in atTop, ∫ s in (0 : ℝ)..T, ‖b n s‖ ≤ K) :
    eVariationOn A (Icc 0 T) ≤ ENNReal.ofReal K := by
  unfold eVariationOn
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, hmem⟩ := p
  simp only
  have hnorm : ∑ i ∈ Finset.range n, ‖A (u (i + 1)) - A (u i)‖ ≤ K := by
    have hlim : Tendsto (fun m => ∑ i ∈ Finset.range n, ‖prim (b m) (u (i + 1)) - prim (b m) (u i)‖)
        atTop (𝓝 (∑ i ∈ Finset.range n, ‖A (u (i + 1)) - A (u i)‖)) := by
      refine tendsto_finsetSum _ fun i _ => ?_
      exact ((hA.tendsto_at (hmem (i + 1))).sub (hA.tendsto_at (hmem i))).norm
    refine le_of_tendsto hlim ?_
    filter_upwards [hK] with m hm
    refine (sum_norm_prim_le (hb m) hu n).trans (le_trans ?_ hm)
    exact intervalIntegral.integral_mono_interval (hmem 0).1 (hu (Nat.zero_le n)) (hmem n).2
      (Filter.Eventually.of_forall fun s => norm_nonneg _)
      ((hb m).norm.intervalIntegrable _ _)
  have : ∑ i ∈ Finset.range n, edist (A (u (i + 1))) (A (u i)) =
      ENNReal.ofReal (∑ i ∈ Finset.range n, ‖A (u (i + 1)) - A (u i)‖) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => norm_nonneg _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [edist_dist, dist_eq_norm]
  rw [this]
  exact ENNReal.ofReal_le_ofReal hnorm

end Main

end HRS.MC.CepE6D
