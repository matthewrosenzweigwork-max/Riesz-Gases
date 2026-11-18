import HRS.Uniform.Comp28Aux2

/-!
# COMP-28, part 3: the window-restricted, weighted grid comparison

`norm_resWin_hatPath_le` (the restriction of a polygon to the window only sees the nodes within one mesh of the window),
`pathMap_block_bound_w` (the blockwise bound `K e^{cT'/g} w_a(r_k)`), `path_grid_comparison_w`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Comp28

open HRS HRS.Uniform HRS.Uniform.Q45 HRS.LindebergAux

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The restriction of a polygon to the window `[a,a+T]` has norm at most `B` if the node values `v i` with
`iT'/g > a - T'/g` (the only ones the window sees) are bounded by `B`. -/
lemma norm_resWin_hatPath_le {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (hT' : 0 < a + T) {g : ℕ} (hg : 1 ≤ g)
    (v : Fin (g + 1) → H) {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ i : Fin (g + 1), a - (a + T) / g < HRS.unifPart (a + T) g i → ‖v i‖ ≤ B) :
    ‖resWin a T ha hT (hatPath (a + T) g v)‖ ≤ B := by
  refine norm_pcm_le _ hB fun s => ?_
  rw [pcm_resWin, hatPath_apply]
  set t : ℝ := a + (s : ℝ) with ht
  have hs0 : a ≤ t := by rw [ht]; linarith [s.2.1]
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  calc ‖∑ i : Fin (g + 1), hatFn (a + T) g i t • v i‖
      ≤ ∑ i : Fin (g + 1), ‖hatFn (a + T) g i t • v i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin (g + 1), hatFn (a + T) g i t * B := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_of_nonneg (hatFn_nonneg _ _ _ _)]
        by_cases h0 : hatFn (a + T) g i t = 0
        · rw [h0]; simp
        · refine mul_le_mul_of_nonneg_left (hv i ?_) (hatFn_nonneg _ _ _ _)
          have hsupp := hatFn_support hT' hg i h0
          rw [abs_lt] at hsupp
          have : a - (a + T) / g < (i : ℝ) * (a + T) / g := by linarith [hsupp.1]
          simpa [unifPart] using this
    _ = B := by
        rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun i => hatFn (a + T) g i t) (g + 1),
          hatFn_sum hT' hg ⟨by linarith [s.2.1], by linarith [s.2.2]⟩, one_mul]

/-- The weighted blockwise bound of the window-restricted synthesis map. -/
lemma pathMap_block_bound_w {a T K c : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (hT' : 0 < a + T) (hK : 0 ≤ K)
    (hc : 0 ≤ c) {V : ℝ → ℝ → H →L[ℝ] H}
    (hV : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ a + T → ‖V t r‖ ≤ K * Real.exp (-c * (t - r)))
    {g κ : ℕ} (hg : 1 ≤ g) (hκ : 1 ≤ κ) {d : ℕ} {b : Fin d → H} (hb : Orthonormal ℝ b) (k : ℕ) (x : H) :
    ‖resWin a T ha hT (pathMap hT' hg hb
        (WithLp.toLp 2 fun j => inner ℝ (gridα (plainData V) (a + T) g κ d b j k) x))‖ ≤
      (K * Real.exp (c * ((a + T) / g)) * wt c a (Q45.rr (g * κ) (a + T) k)) * ‖x‖ := by
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hBnn : 0 ≤ (K * Real.exp (c * ((a + T) / g)) * wt c a (Q45.rr (g * κ) (a + T) k)) * ‖x‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg hK (Real.exp_pos _).le) (wt_pos _ _ _).le) (norm_nonneg _)
  rw [pathMap_apply]
  refine norm_resWin_hatPath_le ha hT hT' hg _ hBnn fun i hi => ?_
  rw [synthVec_block]
  split_ifs with h
  · refine (norm_projB_le hb _).trans ?_
    have hk0 : 0 ≤ Q45.rr (g * κ) (a + T) k := unifPart_nonneg hT'.le _ _
    have hrt : Q45.rr (g * κ) (a + T) k ≤ HRS.unifPart (a + T) g i := rr_le_gridT hT' hg hκ i h.le
    have hti : HRS.unifPart (a + T) g i ≤ a + T := gridT_le hT' hg i
    have hb1 := hV _ _ hk0 hrt hti
    have hb2 : ‖V (HRS.unifPart (a + T) g i) (Q45.rr (g * κ) (a + T) k) x‖ ≤
        K * Real.exp (-c * (HRS.unifPart (a + T) g i - Q45.rr (g * κ) (a + T) k)) * ‖x‖ :=
      ((V _ _).le_opNorm x).trans (mul_le_mul_of_nonneg_right hb1 (norm_nonneg _))
    refine hb2.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hexp : Real.exp (-c * (HRS.unifPart (a + T) g i - Q45.rr (g * κ) (a + T) k)) ≤
        Real.exp (c * ((a + T) / g)) * wt c a (Q45.rr (g * κ) (a + T) k) := by
      unfold wt
      rw [← Real.exp_add, Real.exp_le_exp]
      have hh : 0 ≤ (a + T) / (g : ℝ) := div_nonneg hT'.le hg'.le
      have hmax : max (a - Q45.rr (g * κ) (a + T) k) 0 ≤
          HRS.unifPart (a + T) g i - Q45.rr (g * κ) (a + T) k + (a + T) / g := by
        refine max_le ?_ (by linarith)
        linarith
      nlinarith [mul_le_mul_of_nonneg_left hmax hc]
    calc K * Real.exp (-c * (HRS.unifPart (a + T) g i - Q45.rr (g * κ) (a + T) k))
        ≤ K * (Real.exp (c * ((a + T) / g)) * wt c a (Q45.rr (g * κ) (a + T) k)) :=
          mul_le_mul_of_nonneg_left hexp hK
      _ = _ := by ring
  · simpa using hBnn

/-- The left endpoint of the block containing `σ` is at most `σ`. -/
lemma rr_blk_le {Nb : ℕ} (hNb : 1 ≤ Nb) {T : ℝ} (hT : 0 < T) {σ : ℝ} (hσ : 0 ≤ σ) :
    Q45.rr Nb T (blk Nb T σ) ≤ σ := by
  have hN : (0 : ℝ) < Nb := by exact_mod_cast hNb
  have h1 : ((blk Nb T σ : ℕ) : ℝ) ≤ σ * Nb / T := by
    have h2 : (blk Nb T σ : ℕ) ≤ ⌊σ * Nb / T⌋₊ := min_le_left _ _
    have h3 : (⌊σ * Nb / T⌋₊ : ℝ) ≤ σ * Nb / T := Nat.floor_le (by positivity)
    exact (Nat.cast_le.2 h2).trans h3
  unfold Q45.rr unifPart
  rw [div_le_iff₀ hN]
  rw [le_div_iff₀ hT] at h1
  linarith

/-- **Grid comparison, window and weights.**  For a test function `Φ` on the window path space, the grid-interpolated,
spatially projected Riemann-sum paths of two Hilbert martingales differ by at most
`½ K² e^{2cT'/g} E∫ w_a² ‖Σ - Cb‖_{𝔖₁}`. -/
theorem path_grid_comparison_w {a T K c : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (hT' : 0 < a + T) (hK : 0 ≤ K)
    (hc : 0 ≤ c) {V : ℝ → ℝ → H →L[ℝ] H}
    (hV : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ a + T → ‖V t r‖ ≤ K * Real.exp (-c * (t - r)))
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {g κ : ℕ} (hg : 1 ≤ g) (hκ : 1 ≤ κ) {d : ℕ} {b : Fin d → H} (hb : Orthonormal ℝ b)
    {ℱ : Filtration ℝ mΩ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ (a + T) M Sg)
    {G : ℝ → Ω → H} {Cb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)} (hCb : IsDetCovDensity (a + T) Cb)
    (hG : IsHilbertMartingaleWithCovariation P ℱ (a + T) G (fun r _ => Cb r))
    (X₀ : Ω → H) (hX : Measurable[ℱ 0] X₀) {Φ : PathSp T H → ℝ} (hΦ : Φ ∈ CbUnitBall (PathSp T H) 2) :
    |∫ ω, Φ (resWin a T ha hT (hatPath (a + T) g (fun i => projB b (V (HRS.unifPart (a + T) g i) 0 (X₀ ω) +
        rsum (plainData V) (a + T) g κ M i ω)))) ∂P -
      ∫ ω, Φ (resWin a T ha hT (hatPath (a + T) g (fun i => projB b (V (HRS.unifPart (a + T) g i) 0 (X₀ ω) +
        rsum (plainData V) (a + T) g κ G i ω)))) ∂P| ≤
      (1 / 2) * (K * Real.exp (c * ((a + T) / g))) ^ 2 *
        covDiscW P (a + T) (fun σ => wt c a σ ^ 2) Sg Cb := by
  set S := plainData V with hS
  have hNb : 1 ≤ g * κ := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hξ : StronglyMeasurable[ℱ 0] (fun ω => initCoord (T := a + T) (g := g) b S (X₀ ω)) := by
    have hX' : StronglyMeasurable[ℱ 0] X₀ := hX.stronglyMeasurable
    refine stronglyMeasurable_of_coord fun j => ?_
    have hcont : Continuous fun x : H => inner ℝ (b (finProdFinEquiv.symm j).2)
        (S.VE (HRS.unifPart (a + T) g (finProdFinEquiv.symm j).1) 0 (S.j x)) :=
      continuous_const.inner ((S.VE _ 0).continuous.comp S.j.continuous)
    exact hcont.comp_stronglyMeasurable hX'
  set Kf : ℕ → ℝ := fun k => K * Real.exp (c * ((a + T) / g)) * wt c a (Q45.rr (g * κ) (a + T) k) with hKf
  have hKf0 : ∀ k, 0 ≤ Kf k := fun k =>
    mul_nonneg (mul_nonneg hK (Real.exp_pos _).le) (wt_pos _ _ _).le
  set L : (ℝ^((g + 1) * d)) →L[ℝ] PathSp T H :=
    (resWin a T ha hT).comp (pathMap hT' hg hb) with hL
  have hLn : ‖L‖ ≤ 1 := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc ‖(resWin a T ha hT : PathSp (a + T) H →L[ℝ] PathSp T H)‖ * ‖pathMap hT' hg hb‖ ≤ 1 * 1 :=
          mul_le_mul (norm_resWin_le ha hT) (norm_pathMap_le hT' hg hb) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have key := finite_comparison_w P hT' hNb (gridα S (a + T) g κ d b) L hLn Kf hKf0
    (fun k _ x => by
      rw [hL, ContinuousLinearMap.comp_apply]
      exact pathMap_block_bound_w ha hT hT' hK hc hV hg hκ hb k x)
    hM hCb hG (fun ω => initCoord (T := a + T) (g := g) b S (X₀ ω)) hξ hΦ
  simp only [hL, ContinuousLinearMap.comp_apply, pathMap_zeta hT' hg hκ hb S] at key
  -- compare the blockwise weight with the continuous one
  set B : ℝ := (K * Real.exp (c * ((a + T) / g))) ^ 2 with hB
  have hB0 : 0 ≤ B := sq_nonneg _
  have hϖm : Measurable fun σ : ℝ => Kf (blk (g * κ) (a + T) σ) ^ 2 :=
    ((measurable_from_top (f := fun k : ℕ => Kf k ^ 2)).comp (measurable_blk (g * κ) (a + T)))
  have hKmax : ∀ σ : ℝ, Kf (blk (g * κ) (a + T) σ) ^ 2 ≤ B := by
    intro σ
    have h1 : Kf (blk (g * κ) (a + T) σ) ≤ K * Real.exp (c * ((a + T) / g)) := by
      have := wt_le_one hc a (Q45.rr (g * κ) (a + T) (blk (g * κ) (a + T) σ))
      calc Kf _ = K * Real.exp (c * ((a + T) / g)) * wt c a _ := rfl
        _ ≤ K * Real.exp (c * ((a + T) / g)) * 1 :=
            mul_le_mul_of_nonneg_left this (mul_nonneg hK (Real.exp_pos _).le)
        _ = _ := mul_one _
    rw [hB]
    exact pow_le_pow_left₀ (hKf0 _) h1 2
  have hw1 := wdisc_integrable P hM hCb hϖm (fun σ => sq_nonneg _) hKmax
  have hwm : Measurable fun σ : ℝ => wt c a σ ^ 2 := ((wt_continuous c a).pow 2).measurable
  have hw2 := wdisc_integrable P hM hCb hwm (fun σ => sq_nonneg _) (B := 1)
    (fun σ => pow_le_one₀ (wt_pos _ _ _).le (wt_le_one hc a σ))
  have hpath1 := wdisc_pathint P hM hCb hϖm (fun σ => sq_nonneg _) hKmax
  have hpath2 := wdisc_pathint P hM hCb hwm (fun σ => sq_nonneg _) (B := 1)
    (fun σ => pow_le_one₀ (wt_pos _ _ _).le (wt_le_one hc a σ))
  have hle : ∫ ω, (∫ σ in Set.Icc (0 : ℝ) (a + T),
        Kf (blk (g * κ) (a + T) σ) ^ 2 * traceNormForm (Sg σ ω - Cb σ)) ∂P ≤
      B * covDiscW P (a + T) (fun σ => wt c a σ ^ 2) Sg Cb := by
    unfold covDiscW
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun ω =>
      setIntegral_nonneg measurableSet_Icc fun σ _ =>
        mul_nonneg (sq_nonneg _) (traceNormForm_nonneg _)) (hw2.const_mul B) ?_
    filter_upwards [hpath1, hpath2] with ω h1 h2
    rw [← integral_const_mul]
    refine setIntegral_mono_on h1 (h2.const_mul B) measurableSet_Icc fun σ hσ => ?_
    have hrr := rr_blk_le hNb hT' hσ.1
    have hwm' : wt c a (Q45.rr (g * κ) (a + T) (blk (g * κ) (a + T) σ)) ≤ wt c a σ := wt_mono hc a hrr
    have : Kf (blk (g * κ) (a + T) σ) ^ 2 ≤ B * wt c a σ ^ 2 := by
      have e : Kf (blk (g * κ) (a + T) σ) ^ 2 =
          B * wt c a (Q45.rr (g * κ) (a + T) (blk (g * κ) (a + T) σ)) ^ 2 := by
        simp only [hKf, hB]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (wt_pos _ _ _).le hwm' 2) hB0
    calc Kf (blk (g * κ) (a + T) σ) ^ 2 * traceNormForm (Sg σ ω - Cb σ)
        ≤ (B * wt c a σ ^ 2) * traceNormForm (Sg σ ω - Cb σ) :=
          mul_le_mul_of_nonneg_right this (traceNormForm_nonneg _)
      _ = B * (wt c a σ ^ 2 * traceNormForm (Sg σ ω - Cb σ)) := by ring
  calc _ ≤ _ := key
    _ ≤ (1 / 2) * (B * covDiscW P (a + T) (fun σ => wt c a σ ^ 2) Sg Cb) := by gcongr
    _ = _ := by rw [hB]; ring

end HRS.Uniform.Comp28
