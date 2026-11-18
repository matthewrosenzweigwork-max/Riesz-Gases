import HRS.Uniform.Comp28Aux3

/-!
# COMP-28, part 4: the weighted CLT core on a window

`vpathW` (the initial path of a plain evolution), `core_limit_w`, and `clt_core_w`:
for `Φ` in the `C_b²` unit ball of the window path space,
`|∫Φ(res(V(·,0)X₀ + Z)) - ∫Φ(res(V(·,0)X₀ + Z̄))| ≤ ½ K² E∫ w_a² ‖Σ - Cb‖_{𝔖₁}`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Comp28

open HRS HRS.Uniform HRS.Uniform.Q45 HRS.LindebergAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The initial path `t ↦ V(t,0)x` of a strongly continuous plain evolution, as an element of `C([0,T];H)`. -/
def vpathW (V : ℝ → ℝ → H →L[ℝ] H) {T : ℝ}
    (hc : ∀ y : H, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 y) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})
    (x : H) : PathSp T H :=
  (⟨fun t => V (t : ℝ) 0 x, by
    have := (hc x).comp_continuous
      (show Continuous (fun t : Set.Icc (0 : ℝ) T => ((t : ℝ), (0 : ℝ))) by fun_prop)
      (fun t => ⟨le_rfl, t.2.1, t.2.2⟩)
    exact this⟩ : C(Set.Icc (0 : ℝ) T, H))

lemma pcm_vpathW (V : ℝ → ℝ → H →L[ℝ] H) {T : ℝ}
    (hc : ∀ y : H, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 y) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})
    (x : H) (t : Set.Icc (0 : ℝ) T) : pcm (vpathW V hc x) t = V (t : ℝ) 0 x := rfl

lemma continuousOn_V_zero (V : ℝ → ℝ → H →L[ℝ] H) {T : ℝ}
    (hc : ∀ y : H, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 y) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})
    (x : H) : ContinuousOn (fun t : ℝ => V t 0 x) (Set.Icc 0 T) :=
  (hc x).comp (continuousOn_id.prodMk continuousOn_const) (fun t ht => ⟨le_rfl, ht.1, ht.2⟩)

section Core

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

lemma pcm_vpathW_add_window (V : ℝ → ℝ → H →L[ℝ] H) {T : ℝ}
    (hc : ∀ y : H, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 y) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})
    (x : H) (Z : ℝ → Ω → H) {ω : Ω} (hω : ContinuousOn (fun t => Z t ω) (Set.Icc 0 T))
    (t : Set.Icc (0 : ℝ) T) :
    pcm (vpathW V hc x + windowPath 0 T Z ω) t = V (t : ℝ) 0 x + Z (t : ℝ) ω := by
  rw [pcm_add, pcm_vpathW, pcm_windowPath Z hω]

/-- The finite-dimensional approximants converge in expectation. -/
theorem core_limit_w {T : ℝ} (hT : 0 < T) (V : ℝ → ℝ → H →L[ℝ] H)
    (hc : ∀ y : H, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 y) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})
    {d : ℕ → ℕ} {b : ∀ n, Fin (d n) → H} (hb : ∀ n, Orthonormal ℝ (b n))
    (hspat : ∀ (y : PathSp T H) (ε : ℝ), 0 < ε → ∃ n0 : ℕ, ∀ n ≥ n0, ∀ t : Set.Icc (0 : ℝ) T,
      ‖pcm y t - ∑ a, inner ℝ (b n a) (pcm y t) • b n a‖ ≤ ε)
    {ℱ : Filtration ℝ mΩ} (X₀ : Ω → H) (hX : Measurable[ℱ 0] X₀) (Z : ℝ → Ω → H)
    (hZm : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (Z t))
    (hZc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T))
    {Φ : PathSp T H → ℝ} (hΦ : Φ ∈ CbUnitBall (PathSp T H) 2) :
    Tendsto (fun n : ℕ => ∫ ω, Φ (hatPath T (n + 1) (fun i =>
        projB (b n) (V (unifPart T (n + 1) i) 0 (X₀ ω) + Z (unifPart T (n + 1) i) ω))) ∂P)
      atTop (𝓝 (∫ ω, Φ (vpathW V hc (X₀ ω) + windowPath 0 T Z ω) ∂P)) := by
  obtain ⟨hΦc, hΦb, -, -⟩ := cbUnit_bounds hΦ
  have hX' : Measurable X₀ := hX.mono (ℱ.le 0) le_rfl
  have hmeasB : ∀ n : ℕ, Measurable fun ω => hatPath T (n + 1) (fun i =>
      projB (b n) (V (unifPart T (n + 1) i) 0 (X₀ ω) + Z (unifPart T (n + 1) i) ω)) := by
    intro n
    have : Measurable fun ω => (fun i : Fin (n + 1 + 1) =>
        projB (b n) (V (unifPart T (n + 1) i) 0 (X₀ ω) + Z (unifPart T (n + 1) i) ω)) :=
      measurable_pi_iff.2 fun i =>
        (continuous_projB (b n)).measurable.comp
          (((V _ 0).continuous.measurable.comp hX').add
            (hZm _ ⟨unifPart_nonneg hT.le _ _, gridT_le hT (Nat.le_add_left 1 n) i⟩))
    exact (continuous_hatPath hT (Nat.le_add_left 1 n)).measurable.comp this
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun n =>
    (hΦc.continuous.measurable.comp (hmeasB n)).aestronglyMeasurable) (integrable_const _)
    (fun n => ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hΦb _) ?_
  filter_upwards [hZc] with ω hω
  set Y : PathSp T H := vpathW V hc (X₀ ω) + windowPath 0 T Z ω with hY
  have hsamp : ∀ (n : ℕ) (i : Fin (n + 1 + 1)), samplePath hT.le (n + 1) Y i =
      V (unifPart T (n + 1) i) 0 (X₀ ω) + Z (unifPart T (n + 1) i) ω := by
    intro n i
    unfold samplePath
    have hi : (i : ℝ) * T / ((n + 1 : ℕ) : ℝ) ∈ Set.Icc 0 T :=
      ⟨by positivity, gridT_le hT (Nat.le_add_left 1 n) i⟩
    have := pcm_vpathW_add_window V hc (X₀ ω) Z hω ⟨_, hi⟩
    rw [Set.projIcc_of_mem hT.le hi]
    simpa [unifPart] using this
  have hconv : Tendsto (fun n : ℕ => hatPath T (n + 1) (fun i =>
      projB (b n) (V (unifPart T (n + 1) i) 0 (X₀ ω) + Z (unifPart T (n + 1) i) ω))) atTop
      (𝓝 Y) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨n0, hn0⟩ := lambda_approx hT hb hspat Y (show 0 < ε / 2 by positivity)
    refine ⟨n0, fun n hn => ?_⟩
    rw [dist_eq_norm]
    have := hn0 n hn
    have e : (fun i : Fin (n + 1 + 1) => projB (b n) (samplePath hT.le (n + 1) Y i)) =
        fun i : Fin (n + 1 + 1) => projB (b n) (V (unifPart T (n + 1) i) 0 (X₀ ω) +
          Z (unifPart T (n + 1) i) ω) := by
      funext i; rw [hsamp]
    rw [e] at this
    linarith
  exact (hΦc.continuous.tendsto Y).comp hconv

/-- **The weighted CLT core on a window.** -/
theorem clt_core_w {a T K c : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (hT' : 0 < a + T) (hK : 0 ≤ K)
    (hc : 0 ≤ c) {V : ℝ → ℝ → H →L[ℝ] H}
    (hcont : ∀ y : H, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 y)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ a + T})
    (hV : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ a + T → ‖V t r‖ ≤ K * Real.exp (-c * (t - r)))
    {ℱ : Filtration ℝ mΩ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ (a + T) M Sg)
    {G : ℝ → Ω → H} {Cb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)} (hCb : IsDetCovDensity (a + T) Cb)
    (hG : IsHilbertMartingaleWithCovariation P ℱ (a + T) G (fun r _ => Cb r))
    (X₀ : Ω → H) (hX : Measurable[ℱ 0] X₀) (Z Zb : ℝ → Ω → H)
    (hZ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), IsStochConv P V (ContinuousLinearMap.id ℝ H) M 0 t (Z t))
    (hZb : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), IsStochConv P V (ContinuousLinearMap.id ℝ H) G 0 t (Zb t))
    (hZm : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), Measurable (Z t))
    (hZbm : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), Measurable (Zb t))
    (hZc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T)))
    (hZbc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 (a + T)))
    {Φ : PathSp T H → ℝ} (hΦ : Φ ∈ CbUnitBall (PathSp T H) 2) :
    |∫ ω, Φ (resWin a T ha hT (vpathW V hcont (X₀ ω) + windowPath 0 (a + T) Z ω)) ∂P -
      ∫ ω, Φ (resWin a T ha hT (vpathW V hcont (X₀ ω) + windowPath 0 (a + T) Zb ω)) ∂P| ≤
      (1 / 2) * K ^ 2 * covDiscW P (a + T) (fun σ => wt c a σ ^ 2) Sg Cb := by
  set S := plainData V with hS
  obtain ⟨d, b, hb, hspat⟩ := exists_spatial_approx H
  have hΦ' : (Φ ∘ resWin a T ha hT) ∈ CbUnitBall (PathSp (a + T) H) 2 :=
    cbUnitBall_comp_clm _ (norm_resWin_le ha hT) hΦ
  have hlimZ := core_limit_w P hT' V hcont hb (fun y ε hε => hspat (a + T) y ε hε) X₀ hX Z hZm hZc hΦ'
  have hlimZb := core_limit_w P hT' V hcont hb (fun y ε hε => hspat (a + T) y ε hε) X₀ hX Zb hZbm hZbc hΦ'
  set Δ : ℝ := covDiscW P (a + T) (fun σ => wt c a σ ^ 2) Sg Cb with hΔ
  have hΔ0 : 0 ≤ Δ := integral_nonneg fun ω =>
    setIntegral_nonneg measurableSet_Icc fun σ _ => mul_nonneg (sq_nonneg _) (traceNormForm_nonneg _)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hε5 : 0 < ε / 5 := by positivity
  -- the factor `(K e^{cT'/g})²` tends to `K²`
  have hfac : Tendsto (fun n : ℕ => (1 / 2) * (K * Real.exp (c * ((a + T) / ((n + 1 : ℕ) : ℝ)))) ^ 2 * Δ)
      atTop (𝓝 ((1 / 2) * (K * Real.exp (c * 0)) ^ 2 * Δ)) := by
    have h0 : Tendsto (fun n : ℕ => (a + T) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (a + T)).comp (tendsto_add_atTop_nat 1)
    have hcont' : Continuous fun x : ℝ => (1 / 2) * (K * Real.exp (c * x)) ^ 2 * Δ := by fun_prop
    exact (hcont'.tendsto 0).comp h0
  have hfac' : ∀ᶠ n : ℕ in atTop,
      (1 / 2) * (K * Real.exp (c * ((a + T) / ((n + 1 : ℕ) : ℝ)))) ^ 2 * Δ <
        (1 / 2) * (K * Real.exp (c * 0)) ^ 2 * Δ + ε / 5 :=
    hfac.eventually (gt_mem_nhds (by linarith))
  obtain ⟨n3, hn3⟩ := Filter.eventually_atTop.1 hfac'
  have e1 := (Metric.tendsto_atTop.1 hlimZ) (ε / 5) hε5
  have e2 := (Metric.tendsto_atTop.1 hlimZb) (ε / 5) hε5
  obtain ⟨n1, hn1⟩ := e1
  obtain ⟨n2, hn2⟩ := e2
  set n := max (max n1 n2) n3 with hn
  have h1 := hn1 n ((le_max_left _ _).trans (le_max_left _ _))
  have h2 := hn2 n ((le_max_right _ _).trans (le_max_left _ _))
  have h3 := hn3 n (le_max_right _ _)
  rw [Real.dist_eq] at h1 h2
  set g := n + 1 with hg
  have hg1 : 1 ≤ g := Nat.le_add_left 1 n
  have hη : 0 < ε / 5 / ((g : ℝ) + 1) := by positivity
  obtain ⟨κ1, hκ1⟩ := core_close P hT' hg1 (b n) (hb n) S hM X₀ hX Z hZ hZm hΦ' hη
  obtain ⟨κ2, hκ2⟩ := core_close P hT' hg1 (b n) (hb n) S hG X₀ hX Zb hZb hZbm hΦ' hη
  set κ := max (max κ1 κ2) 1 with hκ
  have c1 := hκ1 κ ((le_max_left _ _).trans (le_max_left _ _)) (le_max_right _ _)
  have c2 := hκ2 κ ((le_max_right _ _).trans (le_max_left _ _)) (le_max_right _ _)
  have hgrid := path_grid_comparison_w ha hT hT' hK hc hV P hg1 (le_max_right _ _ : 1 ≤ κ) (hb n) hM hCb hG
    X₀ hX hΦ
  have hcalc : (g + 1 : ℝ) * (ε / 5 / ((g : ℝ) + 1)) = ε / 5 := by field_simp
  rw [hcalc] at c1 c2
  have hgrid' : (1 / 2) * (K * Real.exp (c * ((a + T) / (g : ℝ)))) ^ 2 * Δ <
      (1 / 2) * K ^ 2 * Δ + ε / 5 := by
    have h3' := h3
    simp only [mul_zero, Real.exp_zero, mul_one] at h3'
    exact h3'
  set a1 := ∫ ω, Φ (resWin a T ha hT (vpathW V hcont (X₀ ω) + windowPath 0 (a + T) Z ω)) ∂P
  set a2 := ∫ ω, Φ (resWin a T ha hT (vpathW V hcont (X₀ ω) + windowPath 0 (a + T) Zb ω)) ∂P
  set b1 := ∫ ω, Φ (resWin a T ha hT (hatPath (a + T) g (fun i => projB (b n)
      (V (unifPart (a + T) g i) 0 (X₀ ω) + Z (unifPart (a + T) g i) ω)))) ∂P
  set b2 := ∫ ω, Φ (resWin a T ha hT (hatPath (a + T) g (fun i => projB (b n)
      (V (unifPart (a + T) g i) 0 (X₀ ω) + Zb (unifPart (a + T) g i) ω)))) ∂P
  set m1 := ∫ ω, Φ (resWin a T ha hT (hatPath (a + T) g (fun i => projB (b n)
      (V (unifPart (a + T) g i) 0 (X₀ ω) + rsum S (a + T) g κ M i ω)))) ∂P
  set m2 := ∫ ω, Φ (resWin a T ha hT (hatPath (a + T) g (fun i => projB (b n)
      (V (unifPart (a + T) g i) 0 (X₀ ω) + rsum S (a + T) g κ G i ω)))) ∂P
  rw [abs_lt] at h1 h2
  rw [abs_le] at c1 c2 hgrid ⊢
  have h1' : -(ε / 5) < b1 - a1 ∧ b1 - a1 < ε / 5 := h1
  have h2' : -(ε / 5) < b2 - a2 ∧ b2 - a2 < ε / 5 := h2
  have c1' : -(ε / 5) ≤ b1 - m1 ∧ b1 - m1 ≤ ε / 5 := c1
  have c2' : -(ε / 5) ≤ b2 - m2 ∧ b2 - m2 ≤ ε / 5 := c2
  have hg' : -((1 / 2) * (K * Real.exp (c * ((a + T) / (g : ℝ)))) ^ 2 * Δ) ≤ m1 - m2 ∧
      m1 - m2 ≤ (1 / 2) * (K * Real.exp (c * ((a + T) / (g : ℝ)))) ^ 2 * Δ := hgrid
  constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2, c1'.1, c1'.2, c2'.1, c2'.2, hg'.1, hg'.2]

end Core

end HRS.Uniform.Comp28
