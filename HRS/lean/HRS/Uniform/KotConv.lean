import HRS.Uniform.KotMaximal

/-!
# Lemma 3.17, dissipative alternative: refinement and comparison of Riemann-type convolutions (packet KOTELENEZ)

Tagged Riemann sums `rsTag`, the comparison identity `rsTag - rsProc = rsProc ∘ stepT` (so that the difference of two Riemann
sums on the same partition is itself a discrete convolution of a martingale transform, to which the maximal inequality
applies), and the refinement identity expressing the Riemann sum of a coarse partition as a tagged sum on a refinement.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS
namespace Uniform
namespace Kot

section Refine

variable {Ω : Type*} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem clampI_trans {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (τ : ℝ) :
    clampI a c τ = if τ ≤ b then clampI a b τ else clampI b c τ := by
  unfold clampI
  split_ifs with h
  · rw [min_eq_left h, min_eq_left (h.trans hbc)]
  · rw [not_le] at h
    have h1 : b ≤ min τ c := le_min h.le hbc
    rw [max_eq_right (hab.trans h1), max_eq_right h1]

variable {V : ℝ → ℝ → H →L[ℝ] H} {N : ℝ → Ω → H} {s : ℕ → ℝ}

/-- Telescoping of clamped increments over a block of cells. -/
theorem sum_cells_clamp (hs : Monotone s) {a b : ℕ} (hab : a ≤ b) (τ : ℝ) (ω : Ω) :
    ∑ l ∈ Finset.Ico a b, (N (clampI (s l) (s (l + 1)) τ) ω - N (s l) ω) =
      N (clampI (s a) (s b) τ) ω - N (s a) ω := by
  induction b, hab using Nat.le_induction with
  | base =>
    simp [clampI, min_le_right]
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih, clampI_trans (hs hab) (hs (Nat.le_succ b)) τ]
    by_cases hτ : τ ≤ s b
    · simp only [hτ, if_true]
      rw [clampI_of_le_left hτ]
      abel
    · simp only [hτ, if_false]
      rw [clampI_of_right_le (hs hab) (not_le.1 hτ).le]
      abel

/-- Tagged Riemann-type convolution: the tags `g l ≤ s l` replace the left endpoints in the evolution factor. -/
def rsTag (V : ℝ → ℝ → H →L[ℝ] H) (N : ℝ → Ω → H) (s : ℕ → ℝ) (m : ℕ) (g : ℕ → ℝ) (τ : ℝ) (ω : Ω) : H :=
  ∑ l ∈ Finset.range m, V τ (min (g l) τ) (N (clampI (s l) (s (l + 1)) τ) ω - N (s l) ω)

theorem rsProc_eq_rsTag (V : ℝ → ℝ → H →L[ℝ] H) (N : ℝ → Ω → H) (s : ℕ → ℝ) (m : ℕ) (τ : ℝ) (ω : Ω) :
    rsProc V N s m τ ω = rsTag V N s m s τ ω := rfl

/-- The increment of a step transform over one cell is the operator applied to the increment of `N`. -/
theorem stepT_cell_incr {K' : Type} [NormedAddCommGroup K'] [InnerProductSpace ℝ K'] [CompleteSpace K']
    (hs : Monotone s) {m : ℕ} (B : ℕ → H →L[ℝ] K') {l : ℕ} (hl : l < m) (τ : ℝ) (ω : Ω) :
    stepT N s m B (clampI (s l) (s (l + 1)) τ) ω - stepT N s m B (s l) ω =
      B l (N (clampI (s l) (s (l + 1)) τ) ω - N (s l) ω) := by
  unfold stepT
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single l]
  · have h1 : clampI (s l) (s (l + 1)) (clampI (s l) (s (l + 1)) τ) = clampI (s l) (s (l + 1)) τ :=
      clampI_of_mem (clampI_mem (hs (Nat.le_succ l)) τ).1 (clampI_mem (hs (Nat.le_succ l)) τ).2
    have h2 : clampI (s l) (s (l + 1)) (s l) = s l := clampI_of_le_left le_rfl
    rw [h1, h2]
    simp
  · intro l' hl' hne
    have hc := clampI_mem (hs (Nat.le_succ l)) τ
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 : s (l' + 1) ≤ s l := hs h
      rw [clampI_of_right_le (hs (Nat.le_succ l')) (h1.trans hc.1),
        clampI_of_right_le (hs (Nat.le_succ l')) h1]
      simp
    · have h1 : s (l + 1) ≤ s l' := hs h
      rw [clampI_of_le_left (hc.2.trans h1), clampI_of_le_left ((hs (Nat.le_succ l)).trans h1)]
      simp
  · intro h; exact absurd (Finset.mem_range.2 hl) h

/-- Comparison identity: the difference of the tagged and untagged Riemann sums on the same partition is a
discrete convolution of the step transform with `B_l = V(s_l, g_l) - 1`. -/
theorem rsTag_sub {K T : ℝ} (hV : EvolBound V K T) (hs : Monotone s) (h0 : 0 ≤ s 0) {m : ℕ}
    (hsm : s m ≤ T) {g : ℕ → ℝ} (hg0 : ∀ l < m, 0 ≤ g l) (hgs : ∀ l < m, g l ≤ s l) {τ : ℝ}
    (hτT : τ ≤ T) (ω : Ω) :
    rsTag V N s m g τ ω - rsProc V N s m τ ω =
      rsProc V (stepT N s m (fun l => V (s l) (g l) - 1)) s m τ ω := by
  have hnn : ∀ l, 0 ≤ s l := fun l => h0.trans (hs (Nat.zero_le l))
  unfold rsTag rsProc
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlm : l < m := Finset.mem_range.1 hl
  rw [stepT_cell_incr hs _ hlm]
  by_cases hτ : τ ≤ s l
  · rw [clampI_of_le_left hτ]
    simp
  · rw [not_le] at hτ
    rw [min_eq_left (hgs l hlm |>.trans hτ.le), min_eq_left hτ.le]
    have hc := hV.comp (g l) (s l) τ (hg0 l hlm) (hgs l hlm) hτ.le hτT
    set d := N (clampI (s l) (s (l + 1)) τ) ω - N (s l) ω with hd
    have h1 : V τ (s l) (V (s l) (g l) d) = V τ (g l) d := by
      have := congrArg (fun F : H →L[ℝ] H => F d) hc
      simpa using this
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    conv_rhs => rw [(V τ (s l)).map_sub, h1]

/-- Index of the coarse cell containing the fine cell `l`. -/
def chunk (φ : ℕ → ℕ) (n l : ℕ) : ℕ := Nat.findGreatest (fun i => φ i ≤ l) n

theorem chunk_succ_of_lt {φ : ℕ → ℕ} {n l : ℕ} (h : l < φ (n + 1)) : chunk φ (n + 1) l = chunk φ n l := by
  unfold chunk
  rw [Nat.findGreatest_succ, if_neg (not_le.2 h)]

theorem chunk_eq_of_mem {φ : ℕ → ℕ} {n l : ℕ} (h1 : φ n ≤ l) (h2 : l < φ (n + 1)) : chunk φ (n + 1) l = n := by
  rw [chunk_succ_of_lt h2]
  exact Nat.findGreatest_eq h1

theorem sum_chunks {G : Type*} [AddCommMonoid G] (φ : ℕ → ℕ) (hφ : Monotone φ) (hφ0 : φ 0 = 0)
    (F : ℕ → ℕ → G) (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ l ∈ Finset.Ico (φ i) (φ (i + 1)), F i l =
      ∑ l ∈ Finset.range (φ n), F (chunk φ n l) l := by
  induction n with
  | zero => simp [hφ0]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, ← Finset.sum_range_add_sum_Ico _ (hφ (Nat.le_succ n))]
    congr 1
    · refine Finset.sum_congr rfl fun l hl => ?_
      have : l < φ (n + 1) := (Finset.mem_range.1 hl).trans_le (hφ (Nat.le_succ n))
      rw [chunk_succ_of_lt this]
    · refine Finset.sum_congr rfl fun l hl => ?_
      have hl' := Finset.mem_Ico.1 hl
      rw [chunk_eq_of_mem hl'.1 hl'.2]

/-- **Refinement identity.** The Riemann-type convolution on a coarse partition is the tagged one on a refinement. -/
theorem rsProc_refine (hs : Monotone s) {r : ℕ → ℝ} {n m : ℕ} (φ : ℕ → ℕ) (hφ : Monotone φ)
    (hφ0 : φ 0 = 0) (hφn : φ n = m) (hrs : ∀ i ≤ n, r i = s (φ i)) (τ : ℝ) (ω : Ω) :
    rsProc V N r n τ ω = rsTag V N s m (fun l => r (chunk φ n l)) τ ω := by
  unfold rsProc rsTag
  have h1 : ∀ i ∈ Finset.range n, V τ (min (r i) τ) (N (clampI (r i) (r (i + 1)) τ) ω - N (r i) ω) =
      ∑ l ∈ Finset.Ico (φ i) (φ (i + 1)), V τ (min (r i) τ)
        (N (clampI (s l) (s (l + 1)) τ) ω - N (s l) ω) := by
    intro i hi
    have hin : i < n := Finset.mem_range.1 hi
    rw [← map_sum, sum_cells_clamp hs (hφ (Nat.le_succ i)), hrs i hin.le, hrs (i + 1) hin]
  rw [Finset.sum_congr rfl h1, sum_chunks φ hφ hφ0 (fun i l => V τ (min (r i) τ)
    (N (clampI (s l) (s (l + 1)) τ) ω - N (s l) ω)) n, hφn]

/-- Admissible data: a partition of mesh `≤ δ` with tags in `[s_l - δ, s_l]`. -/
structure Adm (T δ : ℝ) (s : ℕ → ℝ) (m : ℕ) (g : ℕ → ℝ) : Prop where
  delta_nonneg : 0 ≤ δ
  mono : Monotone s
  nonneg : 0 ≤ s 0
  top : s m ≤ T
  mesh : ∀ l < m, s (l + 1) - s l ≤ δ
  tag0 : ∀ l < m, 0 ≤ g l
  tag_le : ∀ l < m, g l ≤ s l
  tag_ge : ∀ l < m, s l - δ ≤ g l

theorem tendsto_Phi {K T : ℝ} (hV : EvolBound V K T)
    (hcont : ∀ x : H, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 x)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})
    {ℓ : ℕ → H} (hs : Summable fun j => ‖ℓ j‖ ^ 2) {r : ℝ} (hr : r ∈ Icc 0 T) {a b : ℕ → ℝ}
    (ha : Tendsto a atTop (𝓝 r)) (hb : Tendsto b atTop (𝓝 r))
    (hab : ∀ k, 0 ≤ b k ∧ b k ≤ a k ∧ a k ≤ T) :
    Tendsto (fun k => ∑' j, ‖(V (a k) (b k) - 1) (ℓ j)‖ ^ 2) atTop (𝓝 0) := by
  set cV := Real.exp (|K| * T / 2) + 1 with hcV
  have hcV0 : 0 ≤ cV := by positivity
  have hbound : ∀ k j, ‖‖(V (a k) (b k) - 1) (ℓ j)‖ ^ 2‖ ≤ cV ^ 2 * ‖ℓ j‖ ^ 2 := by
    intro k j
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 : ‖V (a k) (b k)‖ ≤ Real.exp (|K| * T / 2) :=
      (hV.norm_le (b k) (a k) (hab k).1 (hab k).2.1 (hab k).2.2).trans
        (exp_le_of_le (sub_nonneg.2 (hab k).2.1) (by linarith [(hab k).1, (hab k).2.2]))
    have h2 : ‖(V (a k) (b k) - 1) (ℓ j)‖ ≤ cV * ‖ℓ j‖ := by
      calc ‖(V (a k) (b k) - 1) (ℓ j)‖ ≤ ‖V (a k) (b k) - 1‖ * ‖ℓ j‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ cV * ‖ℓ j‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          calc ‖V (a k) (b k) - 1‖ ≤ ‖V (a k) (b k)‖ + ‖(1 : H →L[ℝ] H)‖ := norm_sub_le _ _
            _ ≤ Real.exp (|K| * T / 2) + 1 := by
              gcongr
              exact ContinuousLinearMap.norm_id_le
    calc ‖(V (a k) (b k) - 1) (ℓ j)‖ ^ 2 ≤ (cV * ‖ℓ j‖) ^ 2 := by gcongr
      _ = cV ^ 2 * ‖ℓ j‖ ^ 2 := by ring
  have hlim : ∀ j, Tendsto (fun k => ‖(V (a k) (b k) - 1) (ℓ j)‖ ^ 2) atTop (𝓝 0) := by
    intro j
    have hcw := hcont (ℓ j) (r, r) ⟨hr.1, le_rfl, hr.2⟩
    have hmem : Tendsto (fun k => (a k, b k)) atTop
        (𝓝[{p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}] (r, r)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨ha.prodMk_nhds hb, Eventually.of_forall hab⟩
    have h1 := hcw.tendsto.comp hmem
    simp only [hV.self r hr.1 hr.2, ContinuousLinearMap.one_apply] at h1
    have h2 : Tendsto (fun k => (V (a k) (b k) - 1) (ℓ j)) atTop (𝓝 0) := by
      have := h1.sub_const (ℓ j)
      simpa [Function.comp_def] using this
    have h3 := (continuous_norm.tendsto 0).comp h2
    simpa using h3.pow 2
  have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (bound := fun j => cV ^ 2 * ‖ℓ j‖ ^ 2)
    (hs.mul_left _) hlim (Eventually.of_forall hbound)
  simpa using this

theorem tendsto_tn_step {K T : ℝ} (hV : EvolBound V K T)
    (hcont : ∀ x : H, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 x)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})
    {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) {r : ℝ}
    (hr : r ∈ Icc 0 T) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)) (ω : Ω) (hSg : Sg r ω = C)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (s : ℕ → ℕ → ℝ) (m : ℕ → ℕ) (g : ℕ → ℕ → ℝ)
    (hadm : ∀ k, Adm T (δ k) (s k) (m k) (g k)) :
    Tendsto (fun k => traceNormForm
      (stepSg Sg (s k) (m k) (fun l => V (s k l) (g k l) - 1) r ω)) atTop (𝓝 0) := by
  classical
  obtain ⟨ℓ, hs, hℓ⟩ := hC.exists_decomp'
  -- the evaluation points
  let pt : ℕ → ℝ × ℝ := fun k =>
    if h : ∃ l < m k, r ∈ Ioc (s k l) (s k (l + 1)) then (s k (Classical.choose h), g k (Classical.choose h))
    else (r, r)
  have hpt : ∀ k, 0 ≤ (pt k).2 ∧ (pt k).2 ≤ (pt k).1 ∧ (pt k).1 ≤ T ∧ |(pt k).1 - r| ≤ δ k ∧
      |(pt k).2 - r| ≤ 2 * δ k ∧
      traceNormForm (stepSg Sg (s k) (m k) (fun l => V (s k l) (g k l) - 1) r ω) ≤
        ∑' j, ‖(V (pt k).1 (pt k).2 - 1) (ℓ j)‖ ^ 2 := by
    intro k
    have hA := hadm k
    by_cases h : ∃ l < m k, r ∈ Ioc (s k l) (s k (l + 1))
    · have hl := Classical.choose_spec h
      set l := Classical.choose h with hldef
      have hptk : pt k = (s k l, g k l) := by simp only [pt, dif_pos h]; rfl
      rw [hptk]
      simp only
      have h1 := hA.tag0 l hl.1
      have h2 := hA.tag_le l hl.1
      have h3 := hA.tag_ge l hl.1
      have h4 := hA.mesh l hl.1
      have h5 : s k l ≤ s k (m k) := hA.mono hl.1.le
      refine ⟨h1, h2, h5.trans hA.top, ?_, ?_, ?_⟩
      · rw [abs_le]; constructor <;> linarith [hl.2.1, hl.2.2]
      · rw [abs_le]; constructor <;> linarith [hl.2.1, hl.2.2]
      · rw [stepSg_of_mem hA.mono hl.1 hl.2, hSg]
        refine (traceNormForm_formComp_le_decomp _ hs hℓ).trans ?_
        refine le_of_eq (tsum_congr fun j => ?_)
        simp [ContinuousLinearMap.adjoint_adjoint]
    · have hptk : pt k = (r, r) := by simp only [pt, dif_neg h]
      rw [hptk]
      push_neg at h
      refine ⟨hr.1, le_rfl, hr.2, by simp [(hadm k).delta_nonneg], by simp [(hadm k).delta_nonneg], ?_⟩
      rw [stepSg_of_not_mem h, traceNormForm_zero]
      exact tsum_nonneg fun j => sq_nonneg _
  have hamono : Tendsto (fun k => (pt k).1) atTop (𝓝 r) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hδ)
    rw [Real.norm_eq_abs]; exact (hpt k).2.2.2.1
  have hbmono : Tendsto (fun k => (pt k).2) atTop (𝓝 r) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
      (by simpa using hδ.const_mul 2))
    rw [Real.norm_eq_abs]; exact (hpt k).2.2.2.2.1
  have hPhi := tendsto_Phi hV hcont hs hr hamono hbmono (fun k => ⟨(hpt k).1, (hpt k).2.1, (hpt k).2.2.1⟩)
  exact squeeze_zero (fun k => traceNormForm_nonneg _) (fun k => (hpt k).2.2.2.2.2) hPhi

theorem chunk_spec {φ : ℕ → ℕ} (hφ0 : φ 0 = 0) {n l : ℕ} (hl : l < φ n) :
    φ (chunk φ n l) ≤ l ∧ l < φ (chunk φ n l + 1) ∧ chunk φ n l < n := by
  have h0 : (fun i => φ i ≤ l) 0 := by simp [hφ0]
  have hspec : φ (chunk φ n l) ≤ l := Nat.findGreatest_spec (P := fun i => φ i ≤ l) (Nat.zero_le n) h0
  have hle : chunk φ n l ≤ n := Nat.findGreatest_le n
  have hlt : chunk φ n l < n := by
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · rw [h] at hspec; omega
  refine ⟨hspec, ?_, hlt⟩
  have := Nat.findGreatest_is_greatest (P := fun i => φ i ≤ l) (Nat.lt_succ_self (chunk φ n l)) hlt
  exact not_le.1 this

/-- A refinement with tags `r (chunk l)` is admissible. -/
theorem adm_of_refine {T δ : ℝ} {r s : ℕ → ℝ} {n m : ℕ} (hs : Monotone s) (φ : ℕ → ℕ)
    (hφ : Monotone φ) (hφ0 : φ 0 = 0) (hφn : φ n = m) (hrs : ∀ i ≤ n, r i = s (φ i))
    (h0 : 0 ≤ s 0) (hsm : s m ≤ T) (hδ : 0 ≤ δ) (hmr : ∀ i < n, r (i + 1) - r i ≤ δ)
    (hms : ∀ l < m, s (l + 1) - s l ≤ δ) :
    Adm T δ s m (fun l => r (chunk φ n l)) := by
  refine ⟨hδ, hs, h0, hsm, hms, ?_, ?_, ?_⟩
  · intro l hl
    have hc := chunk_spec hφ0 (hφn ▸ hl : l < φ n)
    rw [hrs _ hc.2.2.le]
    exact h0.trans (hs (Nat.zero_le _))
  · intro l hl
    have hc := chunk_spec hφ0 (hφn ▸ hl : l < φ n)
    rw [hrs _ hc.2.2.le]
    exact hs hc.1
  · intro l hl
    have hc := chunk_spec hφ0 (hφn ▸ hl : l < φ n)
    rw [hrs _ hc.2.2.le]
    have h1 : s l ≤ s (φ (chunk φ n l + 1)) := hs hc.2.1.le
    have h2 := hmr (chunk φ n l) hc.2.2
    rw [hrs _ hc.2.2.le, hrs _ (Nat.succ_le_of_lt hc.2.2)] at h2
    linarith

theorem mesh_of_refine {δ : ℝ} {r s : ℕ → ℝ} {n m : ℕ} (hs : Monotone s) (φ : ℕ → ℕ)
    (hφ0 : φ 0 = 0) (hφn : φ n = m) (hrs : ∀ i ≤ n, r i = s (φ i))
    (hmr : ∀ i < n, r (i + 1) - r i ≤ δ) : ∀ l < m, s (l + 1) - s l ≤ δ := by
  intro l hl
  have hc := chunk_spec hφ0 (hφn ▸ hl : l < φ n)
  have h1 : s (l + 1) ≤ s (φ (chunk φ n l + 1)) := hs (Nat.succ_le_of_lt hc.2.1)
  have h2 : s (φ (chunk φ n l)) ≤ s l := hs hc.1
  have h3 := hmr (chunk φ n l) hc.2.2
  rw [hrs _ hc.2.2.le, hrs _ (Nat.succ_le_of_lt hc.2.2)] at h3
  linarith

/-- Given a fine partition `s` containing the points of a coarse one `r`, the index map `φ`. -/
theorem exists_phi {r s : ℕ → ℝ} {n m : ℕ} (hs : Monotone s) (hr : Monotone r)
    (hstrict : ∀ l l', l ≤ m → l' ≤ m → s l ≤ s l' → l ≤ l')
    (hmem : ∀ i ≤ n, ∃ l ≤ m, s l = r i) (h0 : r 0 = s 0) (hn : r n = s m) :
    ∃ φ : ℕ → ℕ, Monotone φ ∧ φ 0 = 0 ∧ φ n = m ∧ ∀ i ≤ n, r i = s (φ i) := by
  classical
  let φ : ℕ → ℕ := fun i => if h : i ≤ n then Classical.choose (hmem i h) else m
  have hφm : ∀ i, φ i ≤ m := by
    intro i
    by_cases h : i ≤ n
    · simp only [φ, dif_pos h]; exact (Classical.choose_spec (hmem i h)).1
    · simp only [φ, dif_neg h]; exact le_rfl
  have hφs : ∀ i ≤ n, s (φ i) = r i := by
    intro i hi
    simp only [φ, dif_pos hi]; exact (Classical.choose_spec (hmem i hi)).2
  have hmono : Monotone φ := by
    intro i i' hii'
    by_cases h' : i' ≤ n
    · have h1 := hφs i (hii'.trans h')
      have h2 := hφs i' h'
      refine hstrict _ _ (hφm i) (hφm i') ?_
      rw [h1, h2]; exact hr hii'
    · simp only [φ, dif_neg h']; exact hφm i
  have hφ0 : φ 0 = 0 := by
    have h1 := hφs 0 (Nat.zero_le n)
    have := hstrict (φ 0) 0 (hφm 0) (Nat.zero_le m) (by rw [h1, h0])
    omega
  have hφn : φ n = m := by
    have h1 := hφs n le_rfl
    have := hstrict m (φ n) le_rfl (hφm n) (by rw [h1, hn])
    exact le_antisymm (hφm n) this
  exact ⟨φ, hmono, hφ0, hφn, fun i hi => (hφs i hi).symm⟩

/-- Common refinement of two partitions with the same endpoints. -/
theorem exists_merge {r r' : ℕ → ℝ} {n n' : ℕ} (hr : Monotone r) (hr' : Monotone r') {a t : ℝ}
    (hr0 : r 0 = a) (hr'0 : r' 0 = a) (hrn : r n = t) (hr'n : r' n' = t) :
    ∃ (s : ℕ → ℝ) (m : ℕ) (φ φ' : ℕ → ℕ), Monotone s ∧ s 0 = a ∧ s m = t ∧
      (Monotone φ ∧ φ 0 = 0 ∧ φ n = m ∧ ∀ i ≤ n, r i = s (φ i)) ∧
      (Monotone φ' ∧ φ' 0 = 0 ∧ φ' n' = m ∧ ∀ i ≤ n', r' i = s (φ' i)) := by
  classical
  set S : Finset ℝ := (Finset.range (n + 1)).image r ∪ (Finset.range (n' + 1)).image r' with hS
  have haS : a ∈ S := by
    simp only [hS, Finset.mem_union, Finset.mem_image, Finset.mem_range]
    exact Or.inl ⟨0, by omega, hr0⟩
  have htS : t ∈ S := by
    simp only [hS, Finset.mem_union, Finset.mem_image, Finset.mem_range]
    exact Or.inl ⟨n, by omega, hrn⟩
  have hSne : S.Nonempty := ⟨a, haS⟩
  have hge : ∀ x ∈ S, a ≤ x := by
    intro x hx
    simp only [hS, Finset.mem_union, Finset.mem_image, Finset.mem_range] at hx
    rcases hx with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · rw [← hr0]; exact hr (Nat.zero_le i)
    · rw [← hr'0]; exact hr' (Nat.zero_le i)
  have hle : ∀ x ∈ S, x ≤ t := by
    intro x hx
    simp only [hS, Finset.mem_union, Finset.mem_image, Finset.mem_range] at hx
    rcases hx with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · rw [← hrn]; exact hr (by omega)
    · rw [← hr'n]; exact hr' (by omega)
  have hk : 0 < S.card := Finset.card_pos.2 hSne
  set m := S.card - 1 with hm
  have hkm : S.card = m + 1 := by omega
  set emb := S.orderEmbOfFin rfl with hemb
  have hlt : ∀ l : ℕ, min l m < S.card := fun l =>
    lt_of_le_of_lt (min_le_right l m) (by omega)
  let s : ℕ → ℝ := fun l => emb ⟨min l m, hlt l⟩
  have hsmono : Monotone s := fun l l' h => emb.monotone (Fin.mk_le_mk.2 (min_le_min h le_rfl))
  have hsval : ∀ l (hl : l ≤ m), s l = emb ⟨l, lt_of_le_of_lt hl (by omega)⟩ := by
    intro l hl; simp only [s, min_eq_left hl]
  have hstrict : ∀ l l', l ≤ m → l' ≤ m → s l ≤ s l' → l ≤ l' := by
    intro l l' hl hl' h
    rw [hsval l hl, hsval l' hl'] at h
    exact Fin.mk_le_mk.1 (emb.le_iff_le.1 h)
  have hmemS : ∀ x ∈ S, ∃ l ≤ m, s l = x := by
    intro x hx
    have : x ∈ Set.range emb := by rw [hemb, Finset.range_orderEmbOfFin]; exact hx
    obtain ⟨j, rfl⟩ := this
    refine ⟨j.val, by omega, ?_⟩
    rw [hsval _ (by omega)]
  have hs0 : s 0 = a := by
    rw [hsval 0 (Nat.zero_le m)]
    have h1 := Finset.orderEmbOfFin_zero (s := S) rfl hk
    have h2 : S.min' hSne = a := le_antisymm (Finset.min'_le S a haS) (Finset.le_min' S hSne a hge)
    rw [← h2]
    exact h1
  have hsm : s m = t := by
    rw [hsval m le_rfl]
    have h1 := Finset.orderEmbOfFin_last (s := S) rfl hk
    have h2 : S.max' hSne = t := le_antisymm (Finset.max'_le S hSne t hle) (Finset.le_max' S t htS)
    rw [← h2]
    exact h1
  have hmem1 : ∀ i ≤ n, ∃ l ≤ m, s l = r i := fun i hi => hmemS (r i) (by
    simp only [hS, Finset.mem_union, Finset.mem_image, Finset.mem_range]
    exact Or.inl ⟨i, by omega, rfl⟩)
  have hmem2 : ∀ i ≤ n', ∃ l ≤ m, s l = r' i := fun i hi => hmemS (r' i) (by
    simp only [hS, Finset.mem_union, Finset.mem_image, Finset.mem_range]
    exact Or.inr ⟨i, by omega, rfl⟩)
  obtain ⟨φ, h1, h2, h3, h4⟩ := exists_phi hsmono hr hstrict hmem1 (by rw [hr0, hs0]) (by rw [hrn, hsm])
  obtain ⟨φ', h1', h2', h3', h4'⟩ := exists_phi hsmono hr' hstrict hmem2 (by rw [hr'0, hs0])
    (by rw [hr'n, hsm])
  exact ⟨s, m, φ, φ', hsmono, hs0, hsm, ⟨h1, h2, h3, h4⟩, ⟨h1', h2', h3', h4'⟩⟩

/-- Dyadic partition of `[0,T]` with `2^m` cells. -/
def dy (T : ℝ) (m : ℕ) (l : ℕ) : ℝ := T * ((min l (2 ^ m) : ℕ) : ℝ) / 2 ^ m

theorem dy_mono {T : ℝ} (hT : 0 ≤ T) (m : ℕ) : Monotone (dy T m) := by
  intro l l' h
  unfold dy
  have : ((min l (2 ^ m) : ℕ) : ℝ) ≤ ((min l' (2 ^ m) : ℕ) : ℝ) := by exact_mod_cast min_le_min h le_rfl
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  rw [div_le_div_iff_of_pos_right h2]
  exact mul_le_mul_of_nonneg_left this hT

theorem dy_zero (T : ℝ) (m : ℕ) : dy T m 0 = 0 := by simp [dy]

theorem dy_top (T : ℝ) (m : ℕ) : dy T m (2 ^ m) = T := by
  unfold dy
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  simp only [min_self]
  push_cast
  field_simp

theorem dy_nonneg {T : ℝ} (hT : 0 ≤ T) (m l : ℕ) : 0 ≤ dy T m l := by
  unfold dy; positivity

theorem dy_le {T : ℝ} (hT : 0 ≤ T) (m l : ℕ) : dy T m l ≤ T := by
  unfold dy
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  have : ((min l (2 ^ m) : ℕ) : ℝ) ≤ 2 ^ m := by exact_mod_cast min_le_right l (2 ^ m)
  rw [div_le_iff₀ h2]
  exact mul_le_mul_of_nonneg_left this hT

theorem dy_step {T : ℝ} (hT : 0 ≤ T) (m l : ℕ) : dy T m (l + 1) - dy T m l ≤ T / 2 ^ m := by
  unfold dy
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  rw [← sub_div, div_le_div_iff_of_pos_right h2, ← mul_sub]
  have : ((min (l + 1) (2 ^ m) : ℕ) : ℝ) - ((min l (2 ^ m) : ℕ) : ℝ) ≤ 1 := by
    have h1 : min (l + 1) (2 ^ m) ≤ min l (2 ^ m) + 1 := by omega
    have : ((min (l + 1) (2 ^ m) : ℕ) : ℝ) ≤ ((min l (2 ^ m) : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    linarith
  nlinarith

theorem dy_refine (T : ℝ) (m d i : ℕ) : dy T m i = dy T (m + d) (2 ^ d * i) := by
  unfold dy
  have h1 : min (2 ^ d * i) (2 ^ (m + d)) = 2 ^ d * min i (2 ^ m) := by
    rw [pow_add, mul_comm (2 ^ m) (2 ^ d), ← Nat.mul_min_mul_left]
  rw [h1]
  push_cast
  rw [pow_add]
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  have h3 : (0 : ℝ) < 2 ^ d := by positivity
  field_simp

/-- Truncating a partition at the evaluation time does not change the Riemann-type convolution there. -/
theorem rsProc_trunc (hs : Monotone s) (n : ℕ) (t : ℝ) (ω : Ω) :
    rsProc V N s n t ω = rsProc V N (fun l => min (s l) t) n t ω := by
  unfold rsProc
  refine Finset.sum_congr rfl fun l _ => ?_
  have hl : s l ≤ s (l + 1) := hs (Nat.le_succ l)
  by_cases h1 : t ≤ s l
  · rw [clampI_of_le_left h1]
    have e1 : min (s l) t = t := min_eq_right h1
    have e2 : min (s (l + 1)) t = t := min_eq_right (h1.trans hl)
    simp only [e1, e2]
    rw [clampI_of_le_left le_rfl]
    simp
  · rw [not_le] at h1
    by_cases h2 : t ≤ s (l + 1)
    · rw [clampI_of_mem h1.le h2]
      have e1 : min (s l) t = s l := min_eq_left h1.le
      have e2 : min (s (l + 1)) t = t := min_eq_right h2
      simp only [e1, e2, min_self]
      rw [clampI_of_mem h1.le le_rfl]
    · rw [not_le] at h2
      rw [clampI_of_right_le hl h2.le]
      have e1 : min (s l) t = s l := min_eq_left h1.le
      have e2 : min (s (l + 1)) t = s (l + 1) := min_eq_left h2.le
      simp only [e1, e2, min_self]
      rw [clampI_of_right_le hl h2.le]

end Refine

section Psi

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {V : ℝ → ℝ → H →L[ℝ] H} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)} {T K : ℝ}

theorem norm_B_le {V : ℝ → ℝ → H →L[ℝ] H} (hV : EvolBound V K T) {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a)
    (haT : a ≤ T) : ‖V a b - 1‖ ≤ Real.exp (|K| * T / 2) + 1 := by
  calc ‖V a b - 1‖ ≤ ‖V a b‖ + ‖(1 : H →L[ℝ] H)‖ := norm_sub_le _ _
    _ ≤ Real.exp (|K| * T / 2) + 1 := by
      gcongr
      · exact (hV.norm_le b a hb hba haT).trans (exp_le_of_le (sub_nonneg.2 hba) (by linarith))
      · exact ContinuousLinearMap.norm_id_le

theorem psi_tendsto (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) (hV : EvolBound V K T)
    (hcont : ∀ x : H, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 x)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (s : ℕ → ℕ → ℝ) (m : ℕ → ℕ) (g : ℕ → ℕ → ℝ)
    (hadm : ∀ k, Adm T (δ k) (s k) (m k) (g k)) :
    Tendsto (fun k => ∫⁻ ω, (∫⁻ r in Icc 0 T, ENNReal.ofReal (traceNormForm
      (stepSg Sg (s k) (m k) (fun l => V (s k l) (g k l) - 1) r ω))) ∂P) atTop (𝓝 0) := by
  set cV := Real.exp (|K| * T / 2) + 1 with hcV
  have hBk : ∀ k, ∀ l < m k, ‖V (s k l) (g k l) - 1‖ ≤ cV := by
    intro k l hl
    have hA := hadm k
    exact norm_B_le hV (hA.tag0 l hl) (hA.tag_le l hl) ((hA.mono hl.le).trans hA.top)
  set F : ℕ → ℝ × Ω → ℝ≥0∞ := fun k p => ENNReal.ofReal (traceNormForm
      (stepSg Sg (s k) (m k) (fun l => V (s k l) (g k l) - 1) p.1 p.2)) with hF
  have hFm : ∀ k, Measurable (F k) := fun k =>
    (measurable_traceNormForm_stepSg hM (s k) (m k) (fun l => V (s k l) (g k l) - 1)).ennreal_ofReal
  set Bd : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (cV ^ 2) *
    ∫⁻ r in Icc 0 T, ENNReal.ofReal (traceNormForm (Sg r ω)) with hBd
  -- the dominating function is integrable
  have hBdfin : ∫⁻ ω, Bd ω ∂P ≠ ⊤ := by
    rw [hBd, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    have h1 : ∀ᵐ ω ∂P, ∫⁻ r in Icc 0 T, ENNReal.ofReal (traceNormForm (Sg r ω)) =
        ENNReal.ofReal (∫ r in Icc 0 T, traceNormForm (Sg r ω)) := by
      filter_upwards [hM.sigma_pathint] with ω hω
      rw [ofReal_integral_eq_lintegral_ofReal hω (Eventually.of_forall fun _ => traceNormForm_nonneg _)]
    rw [lintegral_congr_ae h1]
    exact hM.sigma_int.lintegral_lt_top.ne
  -- inner convergence
  have hinner : ∀ᵐ ω ∂P, Tendsto (fun k => ∫⁻ r in Icc 0 T, F k (r, ω)) atTop (𝓝 0) := by
    have hbd : ∀ k, ∀ᵐ ω ∂P, ∀ σ ∈ Icc 0 T, traceNormForm (stepSg Sg (s k) (m k)
        (fun l => V (s k l) (g k l) - 1) σ ω) ≤ cV ^ 2 * traceNormForm (Sg σ ω) := fun k => by
      filter_upwards [pathint_stepSg hM (hadm k).mono (fun l => V (s k l) (g k l) - 1) (cA := cV)
        (fun l hl => hBk k l hl)] with ω hω using hω.2
    filter_upwards [ae_all_iff.2 hbd, hM.sigma_traceClass, hM.sigma_pathint] with ω hbω htc hpath
    have key := tendsto_lintegral_of_dominated_convergence (μ := volume.restrict (Icc 0 T))
      (F := fun k r => F k (r, ω)) (f := fun _ => (0 : ℝ≥0∞))
      (fun r => ENNReal.ofReal (cV ^ 2) * ENNReal.ofReal (traceNormForm (Sg r ω)))
      (fun k => (hFm k).comp (measurable_id.prodMk measurable_const))
      (fun k => by
        refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
        simp only [hF]
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (hbω k r hr))
      (by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpath.lintegral_lt_top.ne)
      (by
        refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
        have := tendsto_tn_step hV hcont (htc r hr) hr Sg ω rfl δ hδ s m g hadm
        have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp this
        simpa [hF, Function.comp_def] using h2)
    simpa using key
  -- outer convergence
  have hG : ∀ k, Measurable (fun ω => ∫⁻ r in Icc 0 T, F k (r, ω)) := fun k =>
    Measurable.lintegral_prod_right' (f := fun p : Ω × ℝ => F k (p.2, p.1)) (ν := volume.restrict (Icc 0 T))
      ((hFm k).comp measurable_swap)
  have hGb : ∀ k, ∀ᵐ ω ∂P, ∫⁻ r in Icc 0 T, F k (r, ω) ≤ Bd ω := fun k => by
    filter_upwards [lintegral_stepSg_le hM (hadm k).mono (fun l => V (s k l) (g k l) - 1) (cA := cV)
      (fun l hl => hBk k l hl)] with ω hω using hω
  have := tendsto_lintegral_of_dominated_convergence (μ := P) (F := fun k ω => ∫⁻ r in Icc 0 T, F k (r, ω))
    (f := fun _ => (0 : ℝ≥0∞)) Bd hG hGb hBdfin hinner
  simpa using this

theorem psi_small (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) (hV : EvolBound V K T)
    (hcont : ∀ x : H, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 x)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (s : ℕ → ℝ) (m : ℕ) (g : ℕ → ℝ), Adm T δ s m g →
      ∫⁻ ω, (∫⁻ r in Icc 0 T, ENNReal.ofReal (traceNormForm
        (stepSg Sg s m (fun l => V (s l) (g l) - 1) r ω))) ∂P ≤ ε := by
  by_contra hcon
  push_neg at hcon
  have hk : ∀ k : ℕ, ∃ (s : ℕ → ℝ) (m : ℕ) (g : ℕ → ℝ), Adm T (1 / ((k : ℝ) + 1)) s m g ∧
      ε < ∫⁻ ω, (∫⁻ r in Icc 0 T, ENNReal.ofReal (traceNormForm
        (stepSg Sg s m (fun l => V (s l) (g l) - 1) r ω))) ∂P := fun k =>
    hcon (1 / ((k : ℝ) + 1)) (by positivity)
  choose s m g hadm hlt using hk
  have hδ : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h := psi_tendsto hM hV hcont (fun k : ℕ => 1 / ((k : ℝ) + 1)) hδ s m g hadm
  have h2 : ∀ᶠ k in atTop, (∫⁻ ω, (∫⁻ r in Icc 0 T, ENNReal.ofReal (traceNormForm
        (stepSg Sg (s k) (m k) (fun l => V (s k l) (g k l) - 1) r ω))) ∂P) < ε :=
    h.eventually (gt_mem_nhds hε)
  obtain ⟨k, hk⟩ := h2.exists
  exact absurd (hlt k) (not_lt.2 hk.le)

theorem rsTag_L2 (hcomp : IsCompleteFiltration P ℱ) (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    (hV : EvolBound V K T) {δ : ℝ} {s : ℕ → ℝ} {m : ℕ} {g : ℕ → ℝ} (hadm : Adm T δ s m g) :
    ∫⁻ ω, (⨆ τ ∈ Icc 0 T, ‖rsTag V M s m g τ ω - rsProc V M s m τ ω‖ₑ) ^ (2 : ℝ) ∂P ≤
      ENNReal.ofReal (CD 2 K T) * ∫⁻ ω, (∫⁻ r in Icc 0 T, ENNReal.ofReal (traceNormForm
        (stepSg Sg s m (fun l => V (s l) (g l) - 1) r ω))) ∂P := by
  have hB : ∀ l < m, ‖V (s l) (g l) - 1‖ ≤ Real.exp (|K| * T / 2) + 1 := fun l hl =>
    norm_B_le hV (hadm.tag0 l hl) (hadm.tag_le l hl) ((hadm.mono hl.le).trans hadm.top)
  have hN := isHMC_stepT hcomp hM hadm.mono hadm.nonneg hadm.top (fun l => V (s l) (g l) - 1) hB
  have hmax := maximal_rs hcomp hN hV hadm.mono hadm.nonneg hadm.top (p := 2) (by norm_num)
  have hT : 0 ≤ T := hadm.nonneg.trans ((hadm.mono (Nat.zero_le m)).trans hadm.top)
  have heq : ∀ ω, (⨆ τ ∈ Icc 0 T, ‖rsTag V M s m g τ ω - rsProc V M s m τ ω‖ₑ) =
      ⨆ τ ∈ Icc 0 T, ‖rsProc V (stepT M s m (fun l => V (s l) (g l) - 1)) s m τ ω‖ₑ := by
    intro ω
    refine iSup_congr fun τ => iSup_congr fun hτ => ?_
    rw [rsTag_sub hV hadm.mono hadm.nonneg hadm.top hadm.tag0 hadm.tag_le hτ.2 ω]
  simp_rw [heq]
  have h22 : (2 : ℝ) / 2 = 1 := by norm_num
  simp only [h22, ENNReal.rpow_one] at hmax
  exact hmax

theorem aestronglyMeasurable_rsTag (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) {s : ℕ → ℝ}
    (hs : Monotone s) (h0 : 0 ≤ s 0) {m : ℕ} (hsm : s m ≤ T) (g : ℕ → ℝ) (τ : ℝ) :
    AEStronglyMeasurable (rsTag V M s m g τ) P := by
  have : rsTag V M s m g τ = fun ω => ∑ l ∈ Finset.range m,
      V τ (min (g l) τ) (M (clampI (s l) (s (l + 1)) τ) ω - M (s l) ω) := rfl
  rw [this]
  refine Finset.aestronglyMeasurable_fun_sum _ fun l hl => ?_
  have hc := cell_mem hs h0 hsm (Finset.mem_range.1 hl)
  have h1 := clampI_mem hc.2.1 τ
  have h2 := (hM.sq_int _ ⟨hc.1.trans h1.1, h1.2.trans hc.2.2⟩ : MemLp (M (clampI (s l) (s (l + 1)) τ)) 2 P)
  have h3 := (hM.sq_int _ ⟨hc.1, hc.2.1.trans hc.2.2⟩ : MemLp (M (s l)) 2 P)
  exact (V τ (min (g l) τ)).continuous.comp_aestronglyMeasurable
    (h2.aestronglyMeasurable.sub h3.aestronglyMeasurable)

theorem enorm_sub_rpow_two_le {a b : H} :
    ‖a - b‖ₑ ^ (2 : ℝ) ≤ 2 * (‖a‖ₑ ^ (2 : ℝ) + ‖b‖ₑ ^ (2 : ℝ)) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow ‖a‖ₑ ‖b‖ₑ (p := 2) (by norm_num)
  have h2 : (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 := by norm_num
  rw [h2] at h
  calc ‖a - b‖ₑ ^ (2 : ℝ) ≤ (‖a‖ₑ + ‖b‖ₑ) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow (by simpa using enorm_sub_le (a := a) (b := b)) (by norm_num)
    _ ≤ _ := h

theorem L2_compare (hcomp : IsCompleteFiltration P ℱ)
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) (hV : EvolBound V K T)
    (hcont : ∀ x : H, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 x)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}) (hT : 0 ≤ T) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc 0 T, ∀ (r : ℕ → ℝ) (n : ℕ), Monotone r → r 0 = 0 → r n = t →
      (∀ i < n, r (i + 1) - r i ≤ δ) → ∀ m : ℕ, T / 2 ^ m ≤ δ →
        ∫⁻ ω, ‖rsProc V M r n t ω - rsProc V M (dy T m) (2 ^ m) t ω‖ₑ ^ (2 : ℝ) ∂P ≤
          ENNReal.ofReal (4 * CD 2 K T) * ε := by
  obtain ⟨δ, hδ, hsmall⟩ := psi_small hM hV hcont hε
  refine ⟨δ, hδ, fun t ht r n hr hr0 hrn hmr m hm => ?_⟩
  set D : ℕ → ℝ := fun l => min (dy T m l) t with hD
  have hDmono : Monotone D := fun l l' h => min_le_min (dy_mono hT m h) le_rfl
  have hD0 : D 0 = 0 := by simp [hD, dy_zero, ht.1]
  have hDn : D (2 ^ m) = t := by simp [hD, dy_top, ht.2]
  have hDmesh : ∀ i < 2 ^ m, D (i + 1) - D i ≤ δ := by
    intro i _
    have h1 := dy_step hT m i
    have h2 := dy_mono hT m (Nat.le_succ i)
    simp only [hD]
    have : min (dy T m (i + 1)) t - min (dy T m i) t ≤ dy T m (i + 1) - dy T m i := by
      rcases le_total (dy T m (i + 1)) t with h | h
      · rw [min_eq_left h, min_eq_left (h2.trans h)]
      · rw [min_eq_right h]
        have := min_le_left (dy T m i) t
        have h3 := min_le_right (dy T m i) t
        rcases le_total (dy T m i) t with h4 | h4
        · rw [min_eq_left h4]; linarith
        · rw [min_eq_right h4]; linarith
    linarith
  have htr : ∀ ω, rsProc V M (dy T m) (2 ^ m) t ω = rsProc V M D (2 ^ m) t ω := fun ω =>
    rsProc_trunc (dy_mono hT m) (2 ^ m) t ω
  simp_rw [htr]
  obtain ⟨s, mm, φ, φ', hsmono, hs0, hsm, ⟨hφ1, hφ2, hφ3, hφ4⟩, ⟨hφ1', hφ2', hφ3', hφ4'⟩⟩ :=
    exists_merge hr hDmono hr0 hD0 hrn hDn
  have hms : ∀ l < mm, s (l + 1) - s l ≤ δ := mesh_of_refine hsmono φ hφ2 hφ3 hφ4 hmr
  have hAdm : Adm T δ s mm (fun l => r (chunk φ n l)) :=
    adm_of_refine hsmono φ hφ1 hφ2 hφ3 hφ4 (by rw [hs0]) (by rw [hsm]; exact ht.2) hδ.le hmr hms
  have hAdm' : Adm T δ s mm (fun l => D (chunk φ' (2 ^ m) l)) :=
    adm_of_refine hsmono φ' hφ1' hφ2' hφ3' hφ4' (by rw [hs0]) (by rw [hsm]; exact ht.2) hδ.le hDmesh hms
  have e1 := rsProc_refine (V := V) (N := M) hsmono φ hφ1 hφ2 hφ3 hφ4 t
  have e2 := rsProc_refine (V := V) (N := M) hsmono φ' hφ1' hφ2' hφ3' hφ4' t
  have hsM : AEStronglyMeasurable (rsProc V M s mm t) P :=
    aestronglyMeasurable_rsTag hM hsmono (by rw [hs0]) (by rw [hsm]; exact ht.2) s t
  have hma : AEMeasurable (fun ω => ‖rsTag V M s mm (fun l => r (chunk φ n l)) t ω - rsProc V M s mm t ω‖ₑ ^ (2 : ℝ)) P :=
    (((aestronglyMeasurable_rsTag hM hsmono (by rw [hs0]) (by rw [hsm]; exact ht.2) _ t).sub hsM).aemeasurable.enorm).pow_const _
  have hbound1 := hsmall s mm _ hAdm
  have hbound2 := hsmall s mm _ hAdm'
  have hL1 := rsTag_L2 hcomp hM hV hAdm (Sg := Sg)
  have hL2 := rsTag_L2 hcomp hM hV hAdm' (Sg := Sg)
  have hup : ∀ (g : ℕ → ℝ), ∫⁻ ω, ‖rsTag V M s mm g t ω - rsProc V M s mm t ω‖ₑ ^ (2 : ℝ) ∂P ≤
      ∫⁻ ω, (⨆ τ ∈ Icc 0 T, ‖rsTag V M s mm g τ ω - rsProc V M s mm τ ω‖ₑ) ^ (2 : ℝ) ∂P := fun g =>
    lintegral_mono fun ω => ENNReal.rpow_le_rpow
      (le_iSup₂ (f := fun τ (_ : τ ∈ Icc 0 T) => ‖rsTag V M s mm g τ ω - rsProc V M s mm τ ω‖ₑ) t ht)
      (by norm_num)
  have hA := (hup _).trans (hL1.trans (mul_le_mul' le_rfl hbound1))
  have hB := (hup _).trans (hL2.trans (mul_le_mul' le_rfl hbound2))
  calc ∫⁻ ω, ‖rsProc V M r n t ω - rsProc V M D (2 ^ m) t ω‖ₑ ^ (2 : ℝ) ∂P
      = ∫⁻ ω, ‖(rsTag V M s mm (fun l => r (chunk φ n l)) t ω - rsProc V M s mm t ω) -
          (rsTag V M s mm (fun l => D (chunk φ' (2 ^ m) l)) t ω - rsProc V M s mm t ω)‖ₑ ^ (2 : ℝ) ∂P := by
        refine lintegral_congr fun ω => ?_
        rw [e1, e2]
        congr 2
        abel
    _ ≤ ∫⁻ ω, 2 * (‖rsTag V M s mm (fun l => r (chunk φ n l)) t ω - rsProc V M s mm t ω‖ₑ ^ (2 : ℝ) +
          ‖rsTag V M s mm (fun l => D (chunk φ' (2 ^ m) l)) t ω - rsProc V M s mm t ω‖ₑ ^ (2 : ℝ)) ∂P :=
        lintegral_mono fun ω => enorm_sub_rpow_two_le
    _ = 2 * (∫⁻ ω, ‖rsTag V M s mm (fun l => r (chunk φ n l)) t ω - rsProc V M s mm t ω‖ₑ ^ (2 : ℝ) ∂P +
          ∫⁻ ω, ‖rsTag V M s mm (fun l => D (chunk φ' (2 ^ m) l)) t ω - rsProc V M s mm t ω‖ₑ ^ (2 : ℝ) ∂P) := by
        rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left' hma]
    _ ≤ 2 * (ENNReal.ofReal (CD 2 K T) * ε + ENNReal.ofReal (CD 2 K T) * ε) := by gcongr
    _ = ENNReal.ofReal (4 * CD 2 K T) * ε := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        have : (ENNReal.ofReal 4) = 4 := by norm_num
        rw [this]
        ring

theorem continuousOn_clm_apply_of_strong {S : Set ℝ} {A : ℝ → H →L[ℝ] H} {y : ℝ → H} {c : ℝ}
    (hA : ∀ x, ContinuousOn (fun τ => A τ x) S) (hb : ∀ τ ∈ S, ‖A τ‖ ≤ c)
    (hy : ContinuousOn y S) : ContinuousOn (fun τ => A τ (y τ)) S := by
  intro τ₀ hτ₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun τ => ‖y τ - y τ₀‖) (𝓝[S] τ₀) (𝓝 0) := by
    have := (hy τ₀ hτ₀).tendsto.sub_const (y τ₀)
    simpa using this.norm
  have h2 : Tendsto (fun τ => ‖A τ (y τ₀) - A τ₀ (y τ₀)‖) (𝓝[S] τ₀) (𝓝 0) := by
    have := ((hA (y τ₀)) τ₀ hτ₀).tendsto.sub_const (A τ₀ (y τ₀))
    simpa using this.norm
  have h3 : Tendsto (fun τ => c * ‖y τ - y τ₀‖ + ‖A τ (y τ₀) - A τ₀ (y τ₀)‖) (𝓝[S] τ₀) (𝓝 0) := by
    have := (h1.const_mul c).add h2
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun τ => norm_nonneg _) ?_ h3
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have e : A τ (y τ) - A τ₀ (y τ₀) = A τ (y τ - y τ₀) + (A τ (y τ₀) - A τ₀ (y τ₀)) := by
    rw [map_sub]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  gcongr
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hb τ hτ) (norm_nonneg _))

theorem continuousOn_rsProc {K T : ℝ} (hV : EvolBound V K T)
    (hcont : ∀ x : H, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 x)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}) {s : ℕ → ℝ} (hs : Monotone s) (h0 : 0 ≤ s 0) {n : ℕ}
    (hsn : s n ≤ T) {ω : Ω} (hω : ContinuousOn (fun τ => M τ ω) (Icc 0 T)) :
    ContinuousOn (fun τ => rsProc V M s n τ ω) (Icc 0 T) := by
  unfold rsProc
  refine continuousOn_finset_sum _ fun l hl => ?_
  have hc := cell_mem hs h0 hsn (Finset.mem_range.1 hl)
  refine continuousOn_clm_apply_of_strong (S := Icc 0 T) (A := fun τ => V τ (min (s l) τ))
    (c := Real.exp (|K| * T / 2)) ?_ ?_ ?_
  · intro x
    have h1 : ContinuousOn (fun τ : ℝ => (τ, min (s l) τ)) (Icc 0 T) :=
      (continuous_id.prodMk (continuous_const.min continuous_id)).continuousOn
    refine (hcont x).comp h1 fun τ hτ => ⟨?_, min_le_right _ _, hτ.2⟩
    exact le_min hc.1 hτ.1
  · intro τ hτ
    refine (hV.norm_le (min (s l) τ) τ (le_min hc.1 hτ.1) (min_le_right _ _) hτ.2).trans
      (exp_le_of_le (sub_nonneg.2 (min_le_right _ _)) (by linarith [hτ.2, le_min hc.1 hτ.1]))
  · refine ContinuousOn.sub ?_ continuousOn_const
    refine hω.comp (continuous_clampI _ _).continuousOn fun τ _ => ?_
    have := clampI_mem hc.2.1 τ
    exact ⟨hc.1.trans this.1, this.2.trans hc.2.2⟩

theorem exists_dyadic_small {T δ : ℝ} (hδ : 0 < δ) : ∃ m₀ : ℕ, ∀ m ≥ m₀, T / 2 ^ m ≤ δ := by
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (T / δ)
  refine ⟨m₀, fun m hm => ?_⟩
  have h2 : (m₀ : ℝ) ≤ 2 ^ m := by
    have : m₀ ≤ 2 ^ m := (hm.trans (Nat.lt_two_pow_self).le)
    exact_mod_cast this
  have h3 : (0 : ℝ) < 2 ^ m := by positivity
  rw [div_le_iff₀ h3]
  have := (div_lt_iff₀ hδ).1 hm₀
  nlinarith

theorem dyadic_cauchy (hcomp : IsCompleteFiltration P ℱ)
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) (hV : EvolBound V K T)
    (hcont : ∀ x : H, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 x)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}) (hT : 0 ≤ T) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ d : ℕ,
      ∫⁻ ω, (⨆ τ ∈ Icc 0 T, ‖rsProc V M (dy T m) (2 ^ m) τ ω -
        rsProc V M (dy T (m + d)) (2 ^ (m + d)) τ ω‖ₑ) ^ (2 : ℝ) ∂P ≤
          ENNReal.ofReal (CD 2 K T) * ε := by
  obtain ⟨δ, hδ, hsmall⟩ := psi_small hM hV hcont hε
  obtain ⟨m₀, hm₀⟩ := exists_dyadic_small (T := T) hδ
  refine ⟨m₀, fun m hm d => ?_⟩
  have hmδ : T / 2 ^ m ≤ δ := hm₀ m hm
  have hφ : Monotone (fun i : ℕ => 2 ^ d * i) := fun i i' h => Nat.mul_le_mul_left _ h
  have hmesh_r : ∀ i < 2 ^ m, dy T m (i + 1) - dy T m i ≤ δ := fun i _ => (dy_step hT m i).trans hmδ
  have hmesh_s : ∀ l < 2 ^ (m + d), dy T (m + d) (l + 1) - dy T (m + d) l ≤ δ := by
    intro l _
    refine (dy_step hT (m + d) l).trans (le_trans ?_ hmδ)
    rw [pow_add]
    have h1 : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
    have h2 : (0 : ℝ) < 2 ^ m := by positivity
    rw [div_le_div_iff₀ (by positivity) h2]
    nlinarith [mul_nonneg (mul_nonneg hT h2.le) (sub_nonneg.2 h1)]
  have hAdm : Adm T δ (dy T (m + d)) (2 ^ (m + d)) (fun l => dy T m (chunk (fun i => 2 ^ d * i) (2 ^ m) l)) :=
    adm_of_refine (dy_mono hT (m + d)) (fun i => 2 ^ d * i) hφ (by simp)
      (by rw [pow_add, mul_comm]) (fun i _ => dy_refine T m d i)
      (by rw [dy_zero]) (by rw [dy_top]) hδ.le hmesh_r hmesh_s
  have heq : ∀ τ ω, rsProc V M (dy T m) (2 ^ m) τ ω =
      rsTag V M (dy T (m + d)) (2 ^ (m + d)) (fun l => dy T m (chunk (fun i => 2 ^ d * i) (2 ^ m) l)) τ ω :=
    fun τ ω => rsProc_refine (dy_mono hT (m + d)) (fun i => 2 ^ d * i) hφ (by simp)
      (by rw [pow_add, mul_comm]) (fun i _ => dy_refine T m d i) τ ω
  simp_rw [heq]
  exact (rsTag_L2 hcomp hM hV hAdm (Sg := Sg)).trans (mul_le_mul' le_rfl (hsmall _ _ _ hAdm))

end Psi


section Analysis

theorem geom_eq (k₀ n : ℕ) : (1 / 2 : ℝ) ^ (k₀ + n) = 2 * (1 / 2 : ℝ) ^ k₀ / 2 / 2 ^ n := by
  rw [pow_add]
  have h : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp
  rw [← mul_pow]; norm_num

variable {H : Type} [NormedAddCommGroup H] [CompleteSpace H]

/-- A sequence of continuous functions with eventually geometrically summable increments converges uniformly. -/
theorem uniform_limit_of_geometric {S : Set ℝ} {F : ℕ → ℝ → H} (hc : ∀ k, ContinuousOn (F k) S)
    (hb : ∀ᶠ k in atTop, ∀ τ ∈ S, ‖F (k + 1) τ - F k τ‖ ≤ (1 / 2 : ℝ) ^ k) :
    ∃ f : ℝ → H, ContinuousOn f S ∧ ∀ τ ∈ S, Tendsto (fun k => F k τ) atTop (𝓝 (f τ)) := by
  classical
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hb
  set C : ℝ := 2 * (1 / 2 : ℝ) ^ k₀ with hC
  have hcauchy : ∀ τ ∈ S, CauchySeq (fun n => F (k₀ + n) τ) := by
    intro τ hτ
    refine cauchySeq_of_le_geometric_two (C := C) (fun n => ?_)
    rw [dist_comm, dist_eq_norm]
    have := hk₀ (k₀ + n) (Nat.le_add_right _ _) τ hτ
    refine this.trans (le_of_eq ?_)
    rw [hC, geom_eq]
  let f : ℝ → H := fun τ => if h : τ ∈ S then Classical.choose (cauchySeq_tendsto_of_complete (hcauchy τ h)) else 0
  have hf : ∀ τ ∈ S, Tendsto (fun n => F (k₀ + n) τ) atTop (𝓝 (f τ)) := by
    intro τ hτ
    simp only [f, dif_pos hτ]
    exact Classical.choose_spec (cauchySeq_tendsto_of_complete (hcauchy τ hτ))
  have hfull : ∀ τ ∈ S, Tendsto (fun k => F k τ) atTop (𝓝 (f τ)) := by
    intro τ hτ
    exact (tendsto_add_atTop_iff_nat k₀).1 (by simpa [add_comm] using hf τ hτ)
  refine ⟨f, ?_, hfull⟩
  have hunif : TendstoUniformlyOn (fun n => F (k₀ + n)) f atTop S := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (C + 1) by
      have : 0 ≤ C := by positivity
      positivity) (by norm_num : (1 / 2 : ℝ) < 1)
    filter_upwards [eventually_ge_atTop N] with n hn τ hτ
    have hd : dist (F (k₀ + n) τ) (f τ) ≤ C / 2 ^ n := by
      refine dist_le_of_le_geometric_two_of_tendsto (C := C) (f := fun n => F (k₀ + n) τ) (fun n => ?_)
        (hf τ hτ) n
      rw [dist_comm, dist_eq_norm]
      have := hk₀ (k₀ + n) (Nat.le_add_right _ _) τ hτ
      refine this.trans (le_of_eq ?_)
      rw [hC, geom_eq]
    rw [dist_comm]
    refine lt_of_le_of_lt hd ?_
    have h2 : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    have h3 : C / 2 ^ n = C * (1 / 2) ^ n := by rw [one_div, inv_pow]; ring
    rw [h3]
    have hC0 : 0 ≤ C := by positivity
    calc C * (1 / 2 : ℝ) ^ n ≤ C * (1 / 2 : ℝ) ^ N := mul_le_mul_of_nonneg_left h2 hC0
      _ ≤ (C + 1) * (1 / 2 : ℝ) ^ N := by nlinarith [pow_pos (show (0:ℝ) < 1/2 by norm_num) N]
      _ < (C + 1) * (ε / (C + 1)) := by
          exact mul_lt_mul_of_pos_left hN (by positivity)
      _ = ε := by field_simp
  exact hunif.continuousOn (Eventually.of_forall fun n => hc (k₀ + n)).frequently

end Analysis

section FinPart

variable {Ω : Type*} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {V : ℝ → ℝ → H →L[ℝ] H} {M : ℝ → Ω → H}

/-- Extension of a `Fin (n+1)`-indexed partition to `ℕ` (constant beyond `n`). -/
def extP {n : ℕ} (r : Fin (n + 1) → ℝ) : ℕ → ℝ := fun l => r ⟨min l n, Nat.lt_succ_of_le (min_le_right l n)⟩

theorem extP_mono {n : ℕ} {r : Fin (n + 1) → ℝ} (hr : Monotone r) : Monotone (extP r) := fun l l' h =>
  hr (Fin.mk_le_mk.2 (min_le_min h le_rfl))

theorem extP_val {n : ℕ} (r : Fin (n + 1) → ℝ) {l : ℕ} (hl : l ≤ n) :
    extP r l = r ⟨l, Nat.lt_succ_of_le hl⟩ := by
  simp only [extP, min_eq_left hl]

theorem sum_riemann_eq {n : ℕ} {r : Fin (n + 1) → ℝ} (hr : Monotone r) {t : ℝ}
    (hrn : r (Fin.last n) = t) (ω : Ω) :
    ∑ i : Fin n, V t (r i.castSucc) (M (r i.succ) ω - M (r i.castSucc) ω) =
      rsProc V M (extP r) n t ω := by
  unfold rsProc
  rw [← Fin.sum_univ_eq_sum_range (fun l => V t (min (extP r l) t)
    (M (clampI (extP r l) (extP r (l + 1)) t) ω - M (extP r l) ω)) n]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : extP r i.val = r i.castSucc := by
    rw [extP_val r (Nat.le_of_lt i.2)]; rfl
  have h2 : extP r (i.val + 1) = r i.succ := by
    rw [extP_val r (Nat.succ_le_of_lt i.2)]; rfl
  have h3 : r i.succ ≤ t := hrn ▸ hr (Fin.le_last _)
  have h4 : r i.castSucc ≤ r i.succ := hr (Fin.castSucc_le_succ i)
  rw [h1, h2, clampI_of_right_le h4 h3, min_eq_left (h4.trans h3)]

end FinPart

section Psi2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {V : ℝ → ℝ → H →L[ℝ] H} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)} {T K : ℝ}

theorem exists_dyadic_limit (hcomp : IsCompleteFiltration P ℱ)
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) (hV : EvolBound V K T)
    (hcont : ∀ x : H, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 x)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}) (hT : 0 ≤ T) :
    ∃ (m : ℕ → ℕ) (Z : ℝ → Ω → H), StrictMono m ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun τ => Z τ ω) (Icc 0 T)) ∧
      (∀ᵐ ω ∂P, ∀ τ ∈ Icc 0 T,
        Tendsto (fun k => rsProc V M (dy T (m k)) (2 ^ m k) τ ω) atTop (𝓝 (Z τ ω))) := by
  classical
  set CDv := CD 2 K T with hCDv
  have hCD0 : 0 ≤ CDv := CD_nonneg _ _ _
  have hεpos : ∀ k : ℕ, 0 < ENNReal.ofReal ((1 / 8 : ℝ) ^ k / (CDv + 1)) := fun k =>
    ENNReal.ofReal_pos.2 (by positivity)
  choose m₀ hm₀ using fun k : ℕ => dyadic_cauchy hcomp hM hV hcont hT (Sg := Sg) (hεpos k)
  let mk : ℕ → ℕ := fun k => (Finset.range (k + 1)).sup m₀ + k
  have hmk_ge : ∀ k, m₀ k ≤ mk k := fun k =>
    (Finset.le_sup (f := m₀) (Finset.self_mem_range_succ k)).trans (Nat.le_add_right _ _)
  have hmk_strict : StrictMono mk := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    have : (Finset.range (k + 1)).sup m₀ ≤ (Finset.range (k + 1 + 1)).sup m₀ :=
      Finset.sup_mono (Finset.range_mono (Nat.le_succ _))
    simp only [mk]; omega
  let Y : ℕ → ℝ → Ω → H := fun k τ ω => rsProc V M (dy T (mk k)) (2 ^ mk k) τ ω
  have hD : ∀ k, ∫⁻ ω, (⨆ τ ∈ Icc 0 T, ‖Y k τ ω - Y (k + 1) τ ω‖ₑ) ^ (2 : ℝ) ∂P ≤
      ENNReal.ofReal ((1 / 8 : ℝ) ^ k) := by
    intro k
    obtain ⟨d, hd⟩ : ∃ d, mk (k + 1) = mk k + d :=
      ⟨mk (k + 1) - mk k, (Nat.add_sub_cancel' (hmk_strict (Nat.lt_succ_self k)).le).symm⟩
    have h1 := hm₀ k (mk k) (hmk_ge k) d
    simp only [Y]
    rw [hd]
    refine h1.trans ?_
    rw [← ENNReal.ofReal_mul hCD0]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : CDv / (CDv + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    calc CDv * ((1 / 8 : ℝ) ^ k / (CDv + 1)) = (1 / 8 : ℝ) ^ k * (CDv / (CDv + 1)) := by ring
      _ ≤ (1 / 8 : ℝ) ^ k * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := mul_one _
  have hYmeas : ∀ k τ, AEStronglyMeasurable (Y k τ) P := fun k τ =>
    aestronglyMeasurable_rsTag hM (dy_mono hT _) (by rw [dy_zero]) (by rw [dy_top]) _ τ
  set D' : ℕ → Ω → ℝ≥0∞ := fun k ω => ⨆ q ∈ ratSet T, ‖Y k q ω - Y (k + 1) q ω‖ₑ with hD'
  have hD'm : ∀ k, AEMeasurable (D' k) P := fun k =>
    aemeasurable_sup_rat (X := fun q ω => Y k q ω - Y (k + 1) q ω) fun q _ =>
      ((hYmeas k q).sub (hYmeas (k + 1) q)).aemeasurable
  have hD'le : ∀ k ω, D' k ω ≤ ⨆ τ ∈ Icc 0 T, ‖Y k τ ω - Y (k + 1) τ ω‖ₑ := fun k ω =>
    iSup₂_le fun q hq => le_iSup₂ (f := fun τ (_ : τ ∈ Icc 0 T) => ‖Y k τ ω - Y (k + 1) τ ω‖ₑ) q hq.1
  have hcontY : ∀ᵐ ω ∂P, ∀ k, ContinuousOn (fun τ => Y k τ ω) (Icc 0 T) := by
    filter_upwards [hM.cont] with ω hω k
    exact continuousOn_rsProc hV hcont (dy_mono hT _) (by rw [dy_zero]) (by rw [dy_top]) hω
  have hDleD' : ∀ᵐ ω ∂P, ∀ k, (⨆ τ ∈ Icc 0 T, ‖Y k τ ω - Y (k + 1) τ ω‖ₑ) ≤ D' k ω := by
    filter_upwards [hcontY] with ω hω k
    exact iSup_Icc_le_iSup_ratSet (f := fun τ => Y k τ ω - Y (k + 1) τ ω) hT ((hω k).sub (hω (k + 1)))
  -- Markov + Borel–Cantelli
  set A : ℕ → Set Ω := fun k => {ω | ENNReal.ofReal ((1 / 4 : ℝ) ^ k) ≤ D' k ω ^ (2 : ℝ)} with hA
  have hAk : ∀ k, P (A k) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    intro k
    have h1 := mul_meas_ge_le_lintegral₀ ((hD'm k).pow_const (2 : ℝ)) (ENNReal.ofReal ((1 / 4 : ℝ) ^ k))
    have h2 : ∫⁻ ω, D' k ω ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal ((1 / 8 : ℝ) ^ k) :=
      (lintegral_mono fun ω => ENNReal.rpow_le_rpow (hD'le k ω) (by norm_num)).trans (hD k)
    have h3 := h1.trans h2
    have hne : ENNReal.ofReal ((1 / 4 : ℝ) ^ k) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have h4 : P (A k) ≤ ENNReal.ofReal ((1 / 8 : ℝ) ^ k) / ENNReal.ofReal ((1 / 4 : ℝ) ^ k) := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
      exact h3
    refine h4.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_div_of_pos (by positivity), ← div_pow]
    norm_num
  have hsum : ∑' k, P (A k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hAk)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  have hbc := ae_eventually_notMem hsum
  have hgood : ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ τ ∈ Icc 0 T, ‖Y (k + 1) τ ω - Y k τ ω‖ ≤ (1 / 2 : ℝ) ^ k := by
    filter_upwards [hbc, hDleD'] with ω h1 h2
    filter_upwards [h1] with k hk τ hτ
    simp only [hA, Set.mem_setOf_eq, not_le] at hk
    have h3 : (⨆ τ ∈ Icc 0 T, ‖Y k τ ω - Y (k + 1) τ ω‖ₑ) ^ (2 : ℝ) < ENNReal.ofReal ((1 / 4 : ℝ) ^ k) :=
      lt_of_le_of_lt (ENNReal.rpow_le_rpow (h2 k) (by norm_num)) hk
    have h4 : ENNReal.ofReal ((1 / 4 : ℝ) ^ k) = ENNReal.ofReal ((1 / 2 : ℝ) ^ k) ^ (2 : ℝ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two,
        ← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [h4] at h3
    have h5 := (ENNReal.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) < 2)).1 h3
    have h6 : ‖Y k τ ω - Y (k + 1) τ ω‖ₑ < ENNReal.ofReal ((1 / 2 : ℝ) ^ k) :=
      lt_of_le_of_lt (le_iSup₂ (f := fun τ (_ : τ ∈ Icc 0 T) => ‖Y k τ ω - Y (k + 1) τ ω‖ₑ) τ hτ) h5
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_lt_ofReal_iff (by positivity)] at h6
    rw [norm_sub_rev]
    exact h6.le
  set Z : ℝ → Ω → H := fun τ ω => limUnder atTop (fun k => Y k τ ω) with hZ
  have hlim : ∀ᵐ ω ∂P, ∃ f : ℝ → H, ContinuousOn f (Icc 0 T) ∧
      ∀ τ ∈ Icc 0 T, Tendsto (fun k => Y k τ ω) atTop (𝓝 (f τ)) := by
    filter_upwards [hgood, hcontY] with ω h1 h2
    exact uniform_limit_of_geometric (F := fun k τ => Y k τ ω) h2 h1
  refine ⟨mk, Z, hmk_strict, ?_, ?_⟩
  · filter_upwards [hlim] with ω ⟨f, hf, hfl⟩
    refine hf.congr fun τ hτ => ?_
    exact (hfl τ hτ).limUnder_eq
  · filter_upwards [hlim] with ω ⟨f, hf, hfl⟩ τ hτ
    have := hfl τ hτ
    rw [← this.limUnder_eq] at this
    exact this

theorem hconv_Z (hcomp : IsCompleteFiltration P ℱ)
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) (hV : EvolBound V K T)
    (hcont : ∀ x : H, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 x)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}) (hT : 0 ≤ T) {m : ℕ → ℕ} (hm : StrictMono m)
    {Z : ℝ → Ω → H}
    (hlim : ∀ᵐ ω ∂P, ∀ τ ∈ Icc 0 T,
      Tendsto (fun k => rsProc V M (dy T (m k)) (2 ^ m k) τ ω) atTop (𝓝 (Z τ ω)))
    {t : ℝ} (ht : t ∈ Icc 0 T) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (r : Fin (n + 1) → ℝ), r 0 = 0 → r (Fin.last n) = t → Monotone r →
      (∀ i : Fin n, r i.succ - r i.castSucc < δ) →
      ∫⁻ ω, ‖Z t ω - ∑ i : Fin n, V t (r i.castSucc) (M (r i.succ) ω - M (r i.castSucc) ω)‖ₑ ^ 2 ∂P <
        ENNReal.ofReal ε := by
  set CDv := CD 2 K T with hCDv
  have hCD0 : 0 ≤ CDv := CD_nonneg _ _ _
  have hε'' : 0 < ENNReal.ofReal (ε / (8 * (CDv + 1))) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨δ, hδ, hL⟩ := L2_compare hcomp hM hV hcont hT (Sg := Sg) hε''
  refine ⟨δ, hδ, fun n r hr0 hrn hmono hmesh => ?_⟩
  set ext := extP r with hext
  have hext_mono : Monotone ext := extP_mono hmono
  have hext0 : ext 0 = 0 := by rw [hext, extP_val r (Nat.zero_le n)]; exact hr0
  have hextn : ext n = t := by rw [hext, extP_val r le_rfl]; exact hrn
  have hextmesh : ∀ i < n, ext (i + 1) - ext i ≤ δ := by
    intro i hi
    have := hmesh ⟨i, hi⟩
    rw [hext, extP_val r (Nat.succ_le_of_lt hi), extP_val r hi.le]
    exact this.le
  obtain ⟨k₀, hk₀⟩ := exists_dyadic_small (T := T) hδ
  have hmk : ∀ k, k ≤ m k := fun k => hm.id_le k
  have hev : ∀ k ≥ k₀, ∫⁻ ω, ‖rsProc V M ext n t ω - rsProc V M (dy T (m k)) (2 ^ m k) t ω‖ₑ ^ (2 : ℝ) ∂P ≤
      ENNReal.ofReal (4 * CDv) * ENNReal.ofReal (ε / (8 * (CDv + 1))) := fun k hk =>
    hL t ht ext n hext_mono hext0 hextn hextmesh (m k) (hk₀ (m k) (hk.trans (hmk k)))
  -- Fatou
  set f : ℕ → Ω → ℝ≥0∞ := fun k ω => ‖rsProc V M ext n t ω - rsProc V M (dy T (m k)) (2 ^ m k) t ω‖ₑ ^ (2 : ℝ)
    with hf
  have hSM : AEStronglyMeasurable (rsProc V M ext n t) P :=
    aestronglyMeasurable_rsTag hM hext_mono (by rw [hext0]) (by rw [hextn]; exact ht.2) ext t
  have hfm : ∀ k, AEMeasurable (f k) P := fun k =>
    ((hSM.sub (aestronglyMeasurable_rsTag hM (dy_mono hT _) (by rw [dy_zero]) (by rw [dy_top]) _ t)).aemeasurable.enorm).pow_const _
  have hlimf : ∀ᵐ ω ∂P, Tendsto (fun k => f k ω) atTop
      (𝓝 (‖rsProc V M ext n t ω - Z t ω‖ₑ ^ (2 : ℝ))) := by
    filter_upwards [hlim] with ω hω
    have h1 := hω t ht
    have h2 : Tendsto (fun k => rsProc V M ext n t ω - rsProc V M (dy T (m k)) (2 ^ m k) t ω) atTop
        (𝓝 (rsProc V M ext n t ω - Z t ω)) := tendsto_const_nhds.sub h1
    exact (ENNReal.continuous_rpow_const.tendsto _).comp ((continuous_enorm.tendsto _).comp h2)
  have hfat := lintegral_liminf_le' (u := (atTop : Filter ℕ)) hfm
  have hint : ∫⁻ ω, ‖rsProc V M ext n t ω - Z t ω‖ₑ ^ (2 : ℝ) ∂P ≤
      ENNReal.ofReal (4 * CDv) * ENNReal.ofReal (ε / (8 * (CDv + 1))) := by
    calc ∫⁻ ω, ‖rsProc V M ext n t ω - Z t ω‖ₑ ^ (2 : ℝ) ∂P
        = ∫⁻ ω, Filter.liminf (fun k => f k ω) atTop ∂P :=
          lintegral_congr_ae (hlimf.mono fun ω hω => hω.liminf_eq.symm)
      _ ≤ Filter.liminf (fun k => ∫⁻ ω, f k ω ∂P) atTop := hfat
      _ ≤ _ := by
          have hfreq : ∃ᶠ k in atTop, ∫⁻ ω, f k ω ∂P ≤
              ENNReal.ofReal (4 * CDv) * ENNReal.ofReal (ε / (8 * (CDv + 1))) :=
            (eventually_atTop.2 ⟨k₀, hev⟩).frequently
          exact Filter.liminf_le_of_frequently_le' hfreq
  have hfin : ENNReal.ofReal (4 * CDv) * ENNReal.ofReal (ε / (8 * (CDv + 1))) < ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [ENNReal.ofReal_lt_ofReal_iff hε]
    have h1 : 4 * CDv * (ε / (8 * (CDv + 1))) = ε / 2 * (CDv / (CDv + 1)) := by
      field_simp; ring
    rw [h1]
    have h2 : CDv / (CDv + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    nlinarith [div_nonneg hCD0 (by linarith : (0:ℝ) ≤ CDv + 1)]
  refine lt_of_le_of_lt ?_ hfin
  refine le_trans (le_of_eq ?_) hint
  refine lintegral_congr fun ω => ?_
  rw [sum_riemann_eq hmono hrn, enorm_sub_rev, ENNReal.rpow_two]

theorem sup_Z_bound (hcomp : IsCompleteFiltration P ℱ)
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) (hV : EvolBound V K T) (hT : 0 ≤ T)
    {m : ℕ → ℕ} {Z : ℝ → Ω → H}
    (hZc : ∀ᵐ ω ∂P, ContinuousOn (fun τ => Z τ ω) (Icc 0 T))
    (hlim : ∀ᵐ ω ∂P, ∀ τ ∈ Icc 0 T,
      Tendsto (fun k => rsProc V M (dy T (m k)) (2 ^ m k) τ ω) atTop (𝓝 (Z τ ω)))
    {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ ω, (⨆ τ ∈ Icc 0 T, ‖Z τ ω‖ₑ) ^ p ∂P ≤
      ENNReal.ofReal (CD p K T) *
        ∫⁻ ω, (∫⁻ r in Icc 0 T, ENNReal.ofReal (traceNormForm (Sg r ω))) ^ (p / 2) ∂P := by
  have hp0 : 0 < p := by linarith
  set Y : ℕ → ℝ → Ω → H := fun k τ ω => rsProc V M (dy T (m k)) (2 ^ m k) τ ω with hY
  have hYmeas : ∀ k τ, AEStronglyMeasurable (Y k τ) P := fun k τ =>
    aestronglyMeasurable_rsTag hM (dy_mono hT _) (by rw [dy_zero]) (by rw [dy_top]) _ τ
  set S : ℕ → Ω → ℝ≥0∞ := fun k ω => ⨆ q ∈ ratSet T, ‖Y k q ω‖ₑ with hS
  have hSm : ∀ k, AEMeasurable (fun ω => S k ω ^ p) P := fun k =>
    (aemeasurable_sup_rat (X := fun q ω => Y k q ω) fun q _ => (hYmeas k q).aemeasurable).pow_const p
  have hSle : ∀ k ω, S k ω ≤ ⨆ τ ∈ Icc 0 T, ‖Y k τ ω‖ₑ := fun k ω =>
    iSup₂_le fun q hq => le_iSup₂ (f := fun τ (_ : τ ∈ Icc 0 T) => ‖Y k τ ω‖ₑ) q hq.1
  have hbd : ∀ k, ∫⁻ ω, S k ω ^ p ∂P ≤ ENNReal.ofReal (CD p K T) *
      ∫⁻ ω, (∫⁻ r in Icc 0 T, ENNReal.ofReal (traceNormForm (Sg r ω))) ^ (p / 2) ∂P := fun k =>
    (lintegral_mono fun ω => ENNReal.rpow_le_rpow (hSle k ω) hp0.le).trans
      (maximal_rs hcomp hM hV (dy_mono hT _) (by rw [dy_zero]) (by rw [dy_top]) hp)
  -- pointwise comparison
  have hpt : ∀ᵐ ω ∂P, (⨆ τ ∈ Icc 0 T, ‖Z τ ω‖ₑ) ^ p ≤ Filter.liminf (fun k => S k ω ^ p) atTop := by
    filter_upwards [hZc, hlim] with ω hc hl
    have h1 : (⨆ τ ∈ Icc 0 T, ‖Z τ ω‖ₑ) ≤ ⨆ q ∈ ratSet T, ‖Z q ω‖ₑ :=
      iSup_Icc_le_iSup_ratSet (f := fun τ => Z τ ω) hT hc
    have h2 : (⨆ q ∈ ratSet T, ‖Z q ω‖ₑ) ≤ Filter.liminf (fun k => S k ω) atTop := by
      refine iSup₂_le fun q hq => ?_
      have h3 : Tendsto (fun k => ‖Y k q ω‖ₑ) atTop (𝓝 ‖Z q ω‖ₑ) :=
        (continuous_enorm.tendsto _).comp (hl q hq.1)
      rw [← h3.liminf_eq]
      refine Filter.liminf_le_liminf (Eventually.of_forall fun k => ?_)
      exact le_iSup₂ (f := fun q (_ : q ∈ ratSet T) => ‖Y k q ω‖ₑ) q hq
    calc (⨆ τ ∈ Icc 0 T, ‖Z τ ω‖ₑ) ^ p ≤ (Filter.liminf (fun k => S k ω) atTop) ^ p :=
          ENNReal.rpow_le_rpow (h1.trans h2) hp0.le
      _ = Filter.liminf (fun k => S k ω ^ p) atTop := by
          have := Monotone.map_liminf_of_continuousAt (F := (atTop : Filter ℕ))
            (f := fun x : ℝ≥0∞ => x ^ p) (fun a b hab => ENNReal.rpow_le_rpow hab hp0.le)
            (fun k => S k ω) (ENNReal.continuous_rpow_const.continuousAt)
          exact this
  calc ∫⁻ ω, (⨆ τ ∈ Icc 0 T, ‖Z τ ω‖ₑ) ^ p ∂P ≤ ∫⁻ ω, Filter.liminf (fun k => S k ω ^ p) atTop ∂P :=
        lintegral_mono_ae hpt
    _ ≤ Filter.liminf (fun k => ∫⁻ ω, S k ω ^ p ∂P) atTop := lintegral_liminf_le' (u := (atTop : Filter ℕ)) hSm
    _ ≤ _ := Filter.liminf_le_of_frequently_le' (Eventually.of_forall hbd).frequently

end Psi2


end Kot
end Uniform
end HRS
