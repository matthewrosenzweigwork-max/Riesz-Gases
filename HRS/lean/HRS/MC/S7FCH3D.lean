import HRS.MC.S7FCH3A
import HRS.MC.S7FCH3C

/-!
# S7FCH3D: from coordinate moments to the `L^q(Ω; L²_t E_r)` norm (H3, part D)

Sorry-free, no regime-specific input:

* `S7FCH3_core_moment`: if every Fourier coordinate of a jointly measurable `Y` satisfies the `L^{2m}(Ω)` bound
  `∫⁻ |Ŷ_k(t)|^{2m} ≤ σ_k^m Dm_k` for a.e. `t ∈ [0,T]`, then `∫⁻ (∫⁻_{[0,T]} ‖Y t‖² dt)^m` is bounded by
  `T^m A^{m-1} ∑_k a_k Dm_k`;
* `S7FCH3_norm_moment`: for `Y = B - G` with `B`, `G` jointly measurable, `B` a.s. in `L²_t`, this bound makes `G` a.s.
  `L²_t` and bounds `E ‖toL2 B - toL2 G‖^q`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCH3

open HRS HRS.Sec7 HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.S7FCW9

variable {d : ℕ}

theorem S7FCH3_coord_eq (r : ℝ) (F : NegSobolev d r) (k : NonzeroLattice d) :
    Lattice.jp k.1 ^ (-r) * NegSobolev.fourierCoeff F k = NegSobolev.coord F k := by
  unfold NegSobolev.fourierCoeff
  rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1), neg_add_cancel, Real.rpow_zero, one_mul]

theorem S7FCH3_hasSum_norm_sq (r : ℝ) (F : NegSobolev d r) :
    HasSum (fun k : NonzeroLattice d => S7FCH3_wt d r k *
      (NegSobolev.fourierCoeff F k ^ 2 / S7FCH3_sg d k)) (‖F‖ ^ 2) := by
  obtain ⟨hs, he⟩ := NegSobolev.coord_sq F
  rw [he]
  convert hs.hasSum using 1
  funext k
  unfold S7FCH3_wt S7FCH3_sg
  rw [S7FCH3_weight_eq r _ (Torus.jp_pos k.1), S7FCH3_coord_eq]

theorem S7FCH3_core_moment (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) {Ω' : Type} [MeasurableSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P'] (T : ℝ) (hT : 0 < T) (Y : ℝ → Ω' → NegSobolev d r)
    (hYm : Measurable (Function.uncurry Y)) (m : ℝ) (hm : 1 ≤ m) (Dm : NonzeroLattice d → ℝ)
    (hDm0 : ∀ k, 0 ≤ Dm k) (hDs : Summable fun k => S7FCH3_wt d r k * Dm k)
    (hmom : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ k : NonzeroLattice d,
      ∫⁻ ω, ENNReal.ofReal (|NegSobolev.fourierCoeff (Y t ω) k| ^ (2 * m)) ∂P' ≤
        ENNReal.ofReal (S7FCH3_sg d k ^ m * Dm k)) :
    ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal (‖Y t ω‖ ^ 2)) ^ m ∂P' ≤
      ENNReal.ofReal (T ^ m * ((∑' k, S7FCH3_wt d r k + 1) ^ (m - 1) * ∑' k, S7FCH3_wt d r k * Dm k)) := by
  have hasum : Summable (S7FCH3_wt d r : NonzeroLattice d → ℝ) := by
    have := S7FCW9_summable_jp (d := d) (2 * r - ((d : ℝ) + 3)) (by rw [hr]; push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
    exact this.congr fun k => rfl
  set A : ℝ := ∑' k, S7FCH3_wt d r k + 1 with hA
  have hA0 : 0 < A := by
    have : 0 ≤ ∑' k, S7FCH3_wt d r k := tsum_nonneg fun k => (S7FCH3_wt_pos r k).le
    linarith
  have hN : Measurable (Function.uncurry fun t ω => ‖Y t ω‖ ^ 2) :=
    (continuous_norm.measurable.comp hYm).pow_const 2
  refine S7FCH3_time_jensen P' T hT.le (fun t ω => ‖Y t ω‖ ^ 2) hN (fun t ω => sq_nonneg _) m
    (A ^ (m - 1) * ∑' k, S7FCH3_wt d r k * Dm k) hm ?_
  filter_upwards [hmom] with t ht
  have hfm : ∀ k : NonzeroLattice d, Measurable (fun ω => NegSobolev.fourierCoeff (Y t ω) k) := fun k =>
    (HRS.FieldSingAux.measurable_fourierCoeff k).comp (hYm.comp (measurable_const.prodMk measurable_id))
  exact S7FCH3_lint_jensen_tsum P' (S7FCH3_wt d r) (S7FCH3_sg d) Dm
    (fun k ω => NegSobolev.fourierCoeff (Y t ω) k) (fun ω => ‖Y t ω‖ ^ 2) A m hfm
    (fun k => (S7FCH3_wt_pos r k).le) (fun k => S7FCH3_sg_pos k) hDm0 hasum (by linarith) hA0 hm hDs ht
    (fun ω => S7FCH3_hasSum_norm_sq r (Y t ω))

theorem S7FCH3_norm_moment {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (r T : ℝ) (B G : ℝ → Ω' → NegSobolev d r) (hBm : Measurable (Function.uncurry B))
    (hGm : Measurable (Function.uncurry G))
    (hBL2 : ∀ᵐ ω ∂P', MemLp (fun t => B t ω) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (m W : ℝ) (hm : 1 ≤ m)
    (hW : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal (‖B t ω - G t ω‖ ^ 2)) ^ m ∂P' ≤
      ENNReal.ofReal W)
    (q : ℝ) (hq : 1 ≤ q) (hqm : q ≤ 2 * m) (δ : ℝ) (hδ : 0 < δ) (hWδ : W ≤ δ ^ (2 * m / q)) :
    (∀ᵐ ω ∂P', MemLp (fun t => G t ω) 2 (volume.restrict (Set.Icc (0 : ℝ) T))) ∧
    Integrable (fun ω => ‖toL2 r T (fun t => B t ω) - toL2 r T (fun t => G t ω)‖ ^ q) P' ∧
    ∫ ω, ‖toL2 r T (fun t => B t ω) - toL2 r T (fun t => G t ω)‖ ^ q ∂P' ≤ δ := by
  have hm0 : 0 < m := by linarith
  have hq0 : 0 < q := by linarith
  set μT : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμT
  haveI : IsFiniteMeasure μT := Real.isFiniteMeasure_restrict_Icc 0 T
  set Y : ℝ → Ω' → NegSobolev d r := fun t ω => B t ω - G t ω with hY
  have hYm : Measurable (Function.uncurry Y) := hBm.sub hGm
  set n : Ω' → ℝ≥0∞ := fun ω => ∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal (‖Y t ω‖ ^ 2) with hn
  have hnm : Measurable n := by
    have : Measurable (fun p : Ω' × ℝ => ENNReal.ofReal (‖Y p.2 p.1‖ ^ 2)) :=
      ENNReal.measurable_ofReal.comp ((continuous_norm.measurable.comp (hYm.comp measurable_swap)).pow_const 2)
    exact this.lintegral_prod_right'
  have hfin : ∫⁻ ω, (n ω) ^ m ∂P' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hW
  have hae_lt : ∀ᵐ ω ∂P', (n ω) ^ m < ⊤ := ae_lt_top (hnm.pow_const m) hfin
  have hae_n : ∀ᵐ ω ∂P', n ω < ⊤ := by
    filter_upwards [hae_lt] with ω hω
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h, ENNReal.top_rpow_of_pos hm0] at hω
    exact absurd hω (lt_irrefl _)
  have hgood : ∀ᵐ ω ∂P', n ω < ⊤ ∧ MemLp (fun t => B t ω) 2 μT := hae_n.and hBL2
  have hGL2 : ∀ᵐ ω ∂P', MemLp (fun t => G t ω) 2 μT ∧ MemLp (fun t => Y t ω) 2 μT := by
    filter_upwards [hgood] with ω hω
    obtain ⟨hn1, hB⟩ := hω
    have hYmeas : Measurable (fun t => Y t ω) := hYm.comp (measurable_id.prodMk measurable_const)
    have hYL : MemLp (fun t => Y t ω) 2 μT := by
      rw [memLp_two_iff_integrable_sq_norm hYmeas.aestronglyMeasurable]
      refine ⟨(hYmeas.norm.pow_const 2).aestronglyMeasurable, ?_⟩
      exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun t => sq_nonneg _)).2 hn1
    refine ⟨?_, hYL⟩
    have := hB.sub hYL
    refine this.ae_eq (Eventually.of_forall fun t => ?_)
    simp [hY]
  set Xm : Ω' → ℝ := fun ω => Real.sqrt (n ω).toReal with hXm
  have hXmm : Measurable Xm := (hnm.ennreal_toReal).sqrt
  have hXe : ∀ᵐ ω ∂P', ‖toL2 r T (fun t => B t ω) - toL2 r T (fun t => G t ω)‖ = Xm ω := by
    filter_upwards [hgood, hGL2] with ω hω hω2
    obtain ⟨hn1, hB⟩ := hω
    obtain ⟨hG, hYL⟩ := hω2
    have h1 : ‖toL2 r T (fun t => B t ω) - toL2 r T (fun t => G t ω)‖ ^ 2 = (n ω).toReal := by
      have hBG : MemLp (fun t => B t ω - G t ω) 2 μT := hB.sub hG
      rw [S7FCH3_toL2_sub r T hB hG, S7FCH3_toL2_norm_sq r T hBG]
      have hmeas : AEStronglyMeasurable (fun t => ‖B t ω - G t ω‖ ^ 2) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
        ((continuous_norm.measurable.comp (hYm.comp (measurable_id.prodMk measurable_const))).pow_const 2).aestronglyMeasurable
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun t => sq_nonneg _) hmeas]
    rw [hXm]
    simp only
    rw [← h1, Real.sqrt_sq (norm_nonneg _)]
  have hXq : ∀ᵐ ω ∂P', ENNReal.ofReal (Xm ω ^ (2 * m)) = (n ω) ^ m := by
    filter_upwards [hae_n] with ω hω
    have hx : 0 ≤ Xm ω := Real.sqrt_nonneg _
    have e : Xm ω ^ (2 * m) = ((n ω).toReal) ^ m := by
      rw [hXm]; simp only
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ENNReal.toReal_nonneg]
      congr 1
      ring
    rw [e, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hm0.le, ENNReal.ofReal_toReal hω.ne]
  -- Hölder with the exponent `2m/q`
  set f : Ω' → ℝ≥0∞ := fun ω => ENNReal.ofReal (Xm ω ^ q) with hf
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp (hXmm.pow_const q)
  have hm' : 1 ≤ 2 * m / q := by
    rw [le_div_iff₀ hq0]; linarith
  have hH := S7FCH3_lint_holder_time P' f hfm.aemeasurable (2 * m / q) hm'
  rw [measure_univ, ENNReal.one_rpow, one_mul] at hH
  have hfpow : ∀ᵐ ω ∂P', f ω ^ (2 * m / q) = (n ω) ^ m := by
    filter_upwards [hXq] with ω hω
    have hx : 0 ≤ Xm ω := Real.sqrt_nonneg _
    rw [hf]; simp only
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hx q)
      (by positivity), ← Real.rpow_mul hx, mul_div_cancel₀ _ hq0.ne']
    exact hω
  have hint : ∫⁻ ω, f ω ^ (2 * m / q) ∂P' ≤ ENNReal.ofReal W := by
    rw [lintegral_congr_ae hfpow]; exact hW
  have hδm : ENNReal.ofReal W ≤ ENNReal.ofReal δ ^ (2 * m / q) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hδ.le (by positivity)]
    exact ENNReal.ofReal_le_ofReal hWδ
  have hle : ∫⁻ ω, f ω ∂P' ≤ ENNReal.ofReal δ := by
    have h1 : (∫⁻ ω, f ω ∂P') ^ (2 * m / q) ≤ ENNReal.ofReal δ ^ (2 * m / q) :=
      hH.trans (hint.trans hδm)
    exact (ENNReal.rpow_le_rpow_iff (by positivity)).1 h1
  have hint_Xm : Integrable (fun ω => Xm ω ^ q) P' := by
    refine ⟨(hXmm.pow_const q).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => Real.rpow_nonneg (Real.sqrt_nonneg _) _)]
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  refine ⟨hGL2.mono fun ω h => h.1, ?_, ?_⟩
  · refine hint_Xm.congr ?_
    filter_upwards [hXe] with ω hω
    rw [hω]
  · calc ∫ ω, ‖toL2 r T (fun t => B t ω) - toL2 r T (fun t => G t ω)‖ ^ q ∂P'
        = ∫ ω, Xm ω ^ q ∂P' := by
          refine integral_congr_ae ?_
          filter_upwards [hXe] with ω hω
          rw [hω]
      _ ≤ δ := by
          rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => Real.rpow_nonneg (Real.sqrt_nonneg _) _)
            (hXmm.pow_const q).aestronglyMeasurable]
          exact ENNReal.toReal_le_of_le_ofReal hδ.le hle

end HRS.MC.Sec7.S7FCH3

end
