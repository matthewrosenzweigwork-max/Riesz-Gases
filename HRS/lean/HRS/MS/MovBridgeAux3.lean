import HRS.MS.MovBridgeAux2
import HRS.MS.MovOscAux5
import HRS.MS.ThCorrSAux2
import HRS.Prob.Gaussian
import HRS.Prob.Metrics

/-!
# MOVA3B1, part 3: `Σ → H` Stein interpolation (`mo_interp_osc_H`)

Namespace `HRS.MS.MovOsc`.  Proves `mo_interp_osc_H_stmt d` (statement of `MovInterpAux3`,
unchanged).  Proof (three lines on the Fourier side): for `f = ∑ c_α h_α`, the partner
`K = 1_{‖ξ‖ ≤ R} W^σ conj(\hat{T f})` is bounded and compactly supported, the family
`F(z) = ∫ W^{(z-θ)δ} \hat{T f_z} K` (`f_z` the rotated finite Hermite combination) is entire and
bounded on the strip (`MovBridgeAux2`), `|F(j + it)| ≤ M_j ‖f‖_{Σ^ρ} ‖Q_R‖₂` on the boundary lines by
Cauchy-Schwarz and the complexified endpoint bounds (`mova3b1_endpoint_sob`), and `F(θ) = ‖Q_R‖₂²`.
The three-lines theorem gives `‖Q_R‖₂² ≤ M_0^{1-θ} M_1^θ ‖f‖_{Σ^ρ} ‖Q_R‖₂`; `R → ∞` is monotone
convergence (`mova3b1_monotone_limit`), which also yields `MemSobolev` (no density needed).

The second half (section `B1`) proves the bridge `B1`: `mo_bridge1` (`‖a f‖_{H^s} ≤ C M ‖f‖_{Σ^s}` for
`0 ≤ s ≤ N`, `a ∈ C^N` with `|a| ≤ M`, `|∂_j^i a| ≤ M` for `i ≤ N`, `f` in the Hermite span) and
`mo_bridge1_cb` (same with `M = cbNorm N a` for `MemCb N a`).  Statement adjustments relative to the
sketch of `docs/MOV_PLAN.md`: `θ` is a function `a` (to avoid the clash with the interpolation
parameter); the hypothesis `N ≥ s + 1` is weakened to `N ≥ s` (an integer `N ≥ ⌈s⌉` suffices); the
statement is for `f` in the Hermite span (`mo_Hspan d`), which is where `mo_interp_osc_H` applies.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff
open HRS.Whole HRS.MS.MovInterp HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

namespace HRS.MS.MovOsc

variable {d : ℕ}

section Boundary

variable {T : (Euc d → ℝ) → (Euc d → ℝ)}

/-- Boundary bound on the line `Re z = j`. -/
lemma mova3b1_boundary
    (hlin : ∀ f ∈ mo_Hspan d, ∀ g ∈ mo_Hspan d, ∀ a : ℝ, T (a • f + g) = a • T f + T g)
    (hL2 : ∀ f ∈ mo_Hspan d, MemLp (T f) 2 (volume : Measure (Euc d)))
    {r0 r1 s0 s1 θ R j M r s : ℝ} (hM : 0 ≤ M) (hs : s = s0 + j * (s1 - s0))
    (hr : r = r0 + j * (r1 - r0))
    (hend : ∀ f ∈ mo_Hspan d, HRS.PDE.ToolboxRd.MemSobolev s (T f) ∧
      Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s (T f)) ≤ M * oscNorm r f)
    (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) {z : ℂ} (hz : z.re = j) :
    ‖mova3b1_F S c (fun α => fourierL2 (T (hermiteFunD α)))
        (mova3b1_K ((1 - θ) * s0 + θ * s1) R (fourierL2 (T (mova3_comb S c))))
        θ r0 r1 ((s1 - s0) / 2) z‖ ≤
      M * Real.sqrt (∑ α ∈ S, oscEigenvalue d α ^ ((1 - θ) * r0 + θ * r1) * c α ^ 2) *
        Real.sqrt (∫ ξ, mova3b1_Q ((1 - θ) * s0 + θ * s1) R
          (fourierL2 (T (mova3_comb S c))) ξ ^ 2) := by
  set σ := (1 - θ) * s0 + θ * s1 with hσ
  set Ψ := fourierL2 (T (mova3_comb S c)) with hΨdef
  set Θ : MultiIndex d → Euc d → ℂ := fun α => fourierL2 (T (hermiteFunD α)) with hΘdef
  have hΨ : MemLp Ψ 2 volume := memLp_fourierL2 (hL2 _ (mova3_comb_mem S c))
  have hΘ : ∀ α, MemLp (Θ α) 2 volume := fun α =>
    memLp_fourierL2 (hL2 _ (mova3_hermite_mem α))
  set K := mova3b1_K σ R Ψ with hKdef
  have hK : MemLp K 2 volume := mova3b1_K_memLp σ R hΨ
  have hKs := mova3b1_K_supp σ R Ψ
  set u : MultiIndex d → ℂ := fun α => mova3_ua (oscEigenvalue d) c θ r0 r1 z α with hu
  set Φ : Euc d → ℂ := fun ξ => ∑ α ∈ S, u α * Θ α ξ with hΦ
  obtain ⟨hIΦ, hleΦ⟩ := mova3b1_endpoint_sob hlin hL2 hend S u
  have hsum : ∑ α ∈ S, oscEigenvalue d α ^ r * ‖u α‖ ^ 2 =
      ∑ α ∈ S, oscEigenvalue d α ^ ((1 - θ) * r0 + θ * r1) * c α ^ 2 := by
    refine Finset.sum_congr rfl fun α _ => ?_
    have := mova3_hu (fun α => oscEv_pos α) c θ r0 r1 z α
    rw [hz] at this
    rw [hr]; exact this
  have hΦm : AEStronglyMeasurable Φ volume := by
    have : Φ = ∑ α ∈ S, fun ξ => u α * Θ α ξ := by funext ξ; simp [hΦ]
    rw [this]
    exact Finset.aestronglyMeasurable_sum S fun α _ =>
      aestronglyMeasurable_const.mul (hΘ α).aestronglyMeasurable
  set δ : ℝ := (s1 - s0) / 2 with hδ
  have hPQ : ∀ ξ, ‖((mova3b1_W ξ : ℝ) : ℂ) ^ ((z - (θ : ℂ)) * (δ : ℂ)) * (Φ ξ * K ξ)‖ =
      (mova3b1_W ξ ^ (s / 2) * ‖Φ ξ‖) * mova3b1_Q σ R Ψ ξ := by
    intro ξ
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (mova3b1_W_pos ξ), hKdef,
      mova3b1_K_norm]
    have hre : ((z - (θ : ℂ)) * (δ : ℂ)).re = (j - θ) * δ := by
      simp [Complex.mul_re, hz]
    rw [hre]
    unfold mova3b1_Q
    by_cases hξ : ξ ∈ Metric.closedBall (0 : Euc d) R
    · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ]
      have hpos := mova3b1_W_pos ξ
      have he : mova3b1_W ξ ^ ((j - θ) * δ) * mova3b1_W ξ ^ σ =
          mova3b1_W ξ ^ (s / 2) * mova3b1_W ξ ^ (σ / 2) := by
        rw [← Real.rpow_add hpos, ← Real.rpow_add hpos]
        congr 1
        rw [hs, hσ, hδ]; ring
      calc mova3b1_W ξ ^ ((j - θ) * δ) * (‖Φ ξ‖ * (mova3b1_W ξ ^ σ * ‖Ψ ξ‖))
          = (mova3b1_W ξ ^ ((j - θ) * δ) * mova3b1_W ξ ^ σ) * (‖Φ ξ‖ * ‖Ψ ξ‖) := by ring
        _ = (mova3b1_W ξ ^ (s / 2) * mova3b1_W ξ ^ (σ / 2)) * (‖Φ ξ‖ * ‖Ψ ξ‖) := by rw [he]
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ]; simp
  have hP2 : Integrable (fun ξ => (mova3b1_W ξ ^ (s / 2) * ‖Φ ξ‖) ^ 2) volume := by
    refine hIΦ.congr (Eventually.of_forall fun ξ => ?_)
    show mova3b1_W ξ ^ s * ‖Φ ξ‖ ^ 2 = (mova3b1_W ξ ^ (s / 2) * ‖Φ ξ‖) ^ 2
    rw [mul_pow, mova3_rpow_half_sq (mova3b1_W_pos ξ)]
  have hPm : AEStronglyMeasurable (fun ξ => mova3b1_W ξ ^ (s / 2) * ‖Φ ξ‖) volume :=
    (mova3b1_W_rpow_cont (s / 2)).aestronglyMeasurable.mul hΦm.norm
  have hCS := mova3b1_CS (P := fun ξ => mova3b1_W ξ ^ (s / 2) * ‖Φ ξ‖)
    (Q := mova3b1_Q σ R Ψ)
    (fun ξ => mul_nonneg (Real.rpow_nonneg (mova3b1_W_pos ξ).le _) (norm_nonneg _))
    (mova3b1_Q_nonneg σ R Ψ) hPm (mova3b1_Q_meas σ R hΨ) hP2 (mova3b1_Q_sq_integrable σ R hΨ)
  have hP2le : ∫ ξ, (mova3b1_W ξ ^ (s / 2) * ‖Φ ξ‖) ^ 2 ≤
      M ^ 2 * ∑ α ∈ S, oscEigenvalue d α ^ ((1 - θ) * r0 + θ * r1) * c α ^ 2 := by
    have : ∫ ξ, (mova3b1_W ξ ^ (s / 2) * ‖Φ ξ‖) ^ 2 =
        ∫ ξ, mova3b1_W ξ ^ s * ‖Φ ξ‖ ^ 2 := by
      refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      show (mova3b1_W ξ ^ (s / 2) * ‖Φ ξ‖) ^ 2 = mova3b1_W ξ ^ s * ‖Φ ξ‖ ^ 2
      rw [mul_pow, mova3_rpow_half_sq (mova3b1_W_pos ξ)]
    rw [this, ← hsum]; exact hleΦ
  have hF := mova3b1_F_eq_integral (S := S) (c := c) hΘ hK hKs θ r0 r1 δ z
  calc ‖mova3b1_F S c Θ K θ r0 r1 δ z‖
      = ‖∫ ξ, ((mova3b1_W ξ : ℝ) : ℂ) ^ ((z - (θ : ℂ)) * (δ : ℂ)) * (Φ ξ * K ξ)‖ := by rw [hF]
    _ ≤ ∫ ξ, ‖((mova3b1_W ξ : ℝ) : ℂ) ^ ((z - (θ : ℂ)) * (δ : ℂ)) * (Φ ξ * K ξ)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ ξ, (mova3b1_W ξ ^ (s / 2) * ‖Φ ξ‖) * mova3b1_Q σ R Ψ ξ :=
        integral_congr_ae (Eventually.of_forall hPQ)
    _ ≤ Real.sqrt (∫ ξ, (mova3b1_W ξ ^ (s / 2) * ‖Φ ξ‖) ^ 2) *
          Real.sqrt (∫ ξ, mova3b1_Q σ R Ψ ξ ^ 2) := hCS
    _ ≤ M * Real.sqrt (∑ α ∈ S, oscEigenvalue d α ^ ((1 - θ) * r0 + θ * r1) * c α ^ 2) *
          Real.sqrt (∫ ξ, mova3b1_Q σ R Ψ ξ ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        calc Real.sqrt (∫ ξ, (mova3b1_W ξ ^ (s / 2) * ‖Φ ξ‖) ^ 2)
            ≤ Real.sqrt (M ^ 2 * ∑ α ∈ S, oscEigenvalue d α ^ ((1 - θ) * r0 + θ * r1) *
                c α ^ 2) := Real.sqrt_le_sqrt hP2le
          _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hM]

end Boundary

/-! ### The value at `z = θ` -/

section AtTheta

variable {T : (Euc d → ℝ) → (Euc d → ℝ)}

lemma mova3b1_F_theta
    (hlin : ∀ f ∈ mo_Hspan d, ∀ g ∈ mo_Hspan d, ∀ a : ℝ, T (a • f + g) = a • T f + T g)
    (hL2 : ∀ f ∈ mo_Hspan d, MemLp (T f) 2 (volume : Measure (Euc d)))
    (θ r0 r1 s0 s1 R : ℝ) (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) :
    mova3b1_F S c (fun α => fourierL2 (T (hermiteFunD α)))
        (mova3b1_K ((1 - θ) * s0 + θ * s1) R (fourierL2 (T (mova3_comb S c))))
        θ r0 r1 ((s1 - s0) / 2) (θ : ℂ) =
      ((∫ ξ, mova3b1_Q ((1 - θ) * s0 + θ * s1) R (fourierL2 (T (mova3_comb S c))) ξ ^ 2 : ℝ) : ℂ) := by
  set σ := (1 - θ) * s0 + θ * s1 with hσ
  set Ψ := fourierL2 (T (mova3_comb S c)) with hΨdef
  have hΨ : MemLp Ψ 2 volume := memLp_fourierL2 (hL2 _ (mova3_comb_mem S c))
  have hΘ : ∀ α, MemLp (fourierL2 (T (hermiteFunD α))) 2 volume := fun α =>
    memLp_fourierL2 (hL2 _ (mova3_hermite_mem α))
  rw [mova3b1_F_eq_integral hΘ (mova3b1_K_memLp σ R hΨ) (mova3b1_K_supp σ R Ψ)]
  rw [← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [mova3b1_fourier_T_comb hlin hL2 S c] with ξ hξ
  have hua : ∀ α, mova3_ua (oscEigenvalue d) c θ r0 r1 (θ : ℂ) α = (c α : ℂ) := by
    intro α; simp [mova3_ua]
  simp only [hua, sub_self, zero_mul, Complex.cpow_zero, one_mul]
  rw [← hξ, ← hΨdef]
  unfold mova3b1_K
  by_cases hξb : ξ ∈ Metric.closedBall (0 : Euc d) R
  · rw [Set.indicator_of_mem hξb, mova3b1_Q_sq, Set.indicator_of_mem hξb]
    have h1 : Ψ ξ * conj (Ψ ξ) = ((‖Ψ ξ‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    calc Ψ ξ * (((mova3b1_W ξ ^ σ : ℝ) : ℂ) * conj (Ψ ξ))
        = ((mova3b1_W ξ ^ σ : ℝ) : ℂ) * (Ψ ξ * conj (Ψ ξ)) := by ring
      _ = _ := by rw [h1]; push_cast; ring
  · rw [Set.indicator_of_notMem hξb, mova3b1_Q_sq, Set.indicator_of_notMem hξb]; simp

end AtTheta

/-! ### Monotone convergence -/

lemma mova3b1_monotone_limit {g : Euc d → ℝ} (hg0 : ∀ ξ, 0 ≤ g ξ)
    (hgm : AEStronglyMeasurable g volume) {C : ℝ} (hC : 0 ≤ C)
    (hI : ∀ n : ℕ, Integrable ((Metric.closedBall (0 : Euc d) n).indicator g) volume)
    (h : ∀ n : ℕ, ∫ ξ, (Metric.closedBall (0 : Euc d) n).indicator g ξ ≤ C) :
    Integrable g volume ∧ ∫ ξ, g ξ ≤ C := by
  have hind0 : ∀ (n : ℕ) ξ, 0 ≤ (Metric.closedBall (0 : Euc d) n).indicator g ξ := fun n ξ =>
    Set.indicator_nonneg (fun ξ _ => hg0 ξ) ξ
  have hlin : ∫⁻ ξ, ENNReal.ofReal (g ξ) ≤ ENNReal.ofReal C := by
    have hT := lintegral_tendsto_of_tendsto_of_monotone (μ := (volume : Measure (Euc d)))
      (f := fun (n : ℕ) ξ => ENNReal.ofReal ((Metric.closedBall (0 : Euc d) n).indicator g ξ))
      (F := fun ξ => ENNReal.ofReal (g ξ))
      (fun n => (hI n).aemeasurable.ennreal_ofReal)
      (Eventually.of_forall fun ξ n m hnm => ENNReal.ofReal_le_ofReal
        (Set.indicator_le_indicator_of_subset (Metric.closedBall_subset_closedBall
          (by exact_mod_cast hnm)) (fun ξ => hg0 ξ) ξ))
      (Eventually.of_forall fun ξ => by
        obtain ⟨N, hN⟩ := exists_nat_ge ‖ξ‖
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N] with n hn
        rw [Set.indicator_of_mem]
        simp only [Metric.mem_closedBall, dist_zero_right]
        exact hN.trans (by exact_mod_cast hn))
    refine le_of_tendsto' hT fun n => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hI n) (Eventually.of_forall (hind0 n))]
    exact ENNReal.ofReal_le_ofReal (h n)
  have hfin : Integrable g volume :=
    ⟨hgm, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hg0)).2
      (lt_of_le_of_lt hlin ENNReal.ofReal_lt_top)⟩
  refine ⟨hfin, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg0) hgm]
  exact ENNReal.toReal_le_of_le_ofReal hC hlin

/-! ### The three-lines step -/

section Main

variable {T : (Euc d → ℝ) → (Euc d → ℝ)}

lemma mova3b1_three_lines
    (hlin : ∀ f ∈ mo_Hspan d, ∀ g ∈ mo_Hspan d, ∀ a : ℝ, T (a • f + g) = a • T f + T g)
    (hL2 : ∀ f ∈ mo_Hspan d, MemLp (T f) 2 (volume : Measure (Euc d)))
    {r0 r1 s0 s1 M0 M1 θ : ℝ} (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h0 : ∀ f ∈ mo_Hspan d, HRS.PDE.ToolboxRd.MemSobolev s0 (T f) ∧
      Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s0 (T f)) ≤ M0 * oscNorm r0 f)
    (h1 : ∀ f ∈ mo_Hspan d, HRS.PDE.ToolboxRd.MemSobolev s1 (T f) ∧
      Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s1 (T f)) ≤ M1 * oscNorm r1 f)
    (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) (R : ℝ) :
    ∫ ξ, mova3b1_Q ((1 - θ) * s0 + θ * s1) R (fourierL2 (T (mova3_comb S c))) ξ ^ 2 ≤
      M0 ^ (1 - θ) * M1 ^ θ *
        Real.sqrt (∑ α ∈ S, oscEigenvalue d α ^ ((1 - θ) * r0 + θ * r1) * c α ^ 2) *
        Real.sqrt (∫ ξ, mova3b1_Q ((1 - θ) * s0 + θ * s1) R
          (fourierL2 (T (mova3_comb S c))) ξ ^ 2) := by
  set σ := (1 - θ) * s0 + θ * s1 with hσ
  set Ψ := fourierL2 (T (mova3_comb S c)) with hΨdef
  have hΨ : MemLp Ψ 2 volume := memLp_fourierL2 (hL2 _ (mova3_comb_mem S c))
  have hΘ : ∀ α, MemLp (fourierL2 (T (hermiteFunD α))) 2 volume := fun α =>
    memLp_fourierL2 (hL2 _ (mova3_hermite_mem α))
  have hK : MemLp (mova3b1_K σ R Ψ) 2 volume := mova3b1_K_memLp σ R hΨ
  have hKs := mova3b1_K_supp σ R Ψ
  set X := Real.sqrt (∑ α ∈ S, oscEigenvalue d α ^ ((1 - θ) * r0 + θ * r1) * c α ^ 2) with hX
  set N := ∫ ξ, mova3b1_Q σ R Ψ ξ ^ 2 with hN
  set Y := Real.sqrt N with hY
  have hXn : 0 ≤ X := Real.sqrt_nonneg _
  have hYn : 0 ≤ Y := Real.sqrt_nonneg _
  have hN0 : 0 ≤ N := integral_nonneg fun ξ => sq_nonneg _
  set F := mova3b1_F S c (fun α => fourierL2 (T (hermiteFunD α))) (mova3b1_K σ R Ψ) θ r0 r1
    ((s1 - s0) / 2) with hF
  have hdiff : Differentiable ℂ F := mova3b1_F_differentiable hΘ hK hKs θ r0 r1 _
  obtain ⟨C, hC⟩ := mova3b1_F_bdd (S := S) (c := c) hΘ hK hKs hθ0 hθ1 r0 r1 ((s1 - s0) / 2)
  have hB : BddAbove ((norm ∘ F) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hC z hz.1 hz.2
  have ha : ∀ z ∈ Complex.re ⁻¹' {(0 : ℝ)}, ‖F z‖ ≤ M0 * (X * Y) := by
    intro z hz
    have hz0 : z.re = 0 := hz
    have := mova3b1_boundary hlin hL2 (r0 := r0) (r1 := r1) (s0 := s0) (s1 := s1) (θ := θ) (R := R) (j := 0) hM0 (s := s0) (r := r0)
      (by ring) (by ring) h0 S c hz0
    exact this.trans (le_of_eq (mul_assoc _ _ _))
  have hb : ∀ z ∈ Complex.re ⁻¹' {(1 : ℝ)}, ‖F z‖ ≤ M1 * (X * Y) := by
    intro z hz
    have hz1 : z.re = 1 := hz
    have := mova3b1_boundary hlin hL2 (r0 := r0) (r1 := r1) (s0 := s0) (s1 := s1) (θ := θ) (R := R) (j := 1) hM1 (s := s1) (r := r1)
      (by ring) (by ring) h1 S c hz1
    exact this.trans (le_of_eq (mul_assoc _ _ _))
  have hzmem : (θ : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp only [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage,
      Complex.ofReal_re, Set.mem_Icc]
    exact ⟨hθ0, hθ1⟩
  have key := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := F) (z := (θ : ℂ)) (a := M0 * (X * Y)) (b := M1 * (X * Y)) (l := 0) (u := 1)
    zero_lt_one hzmem hdiff.diffContOnCl hB ha hb
  have hFθ : F (θ : ℂ) = ((N : ℝ) : ℂ) := mova3b1_F_theta hlin hL2 θ r0 r1 s0 s1 R S c
  rw [hFθ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN0] at key
  simp only [Complex.ofReal_re, sub_zero, div_one] at key
  refine key.trans (le_of_eq ?_)
  have hXY : 0 ≤ X * Y := mul_nonneg hXn hYn
  rw [Real.mul_rpow hM0 hXY, Real.mul_rpow hM1 hXY]
  have : (X * Y) ^ (1 - θ) * (X * Y) ^ θ = X * Y := by
    rw [← Real.rpow_add' hXY (by linarith : (1 - θ) + θ ≠ 0)]
    simp
  calc M0 ^ (1 - θ) * (X * Y) ^ (1 - θ) * (M1 ^ θ * (X * Y) ^ θ)
      = M0 ^ (1 - θ) * M1 ^ θ * ((X * Y) ^ (1 - θ) * (X * Y) ^ θ) := by ring
    _ = _ := by rw [this]; ring

end Main

/-! ### The theorem -/

/-- **`Σ → H` Stein interpolation** (statement `mo_interp_osc_H_stmt` of `MovInterpAux3`). -/
theorem mo_interp_osc_H (d : ℕ) : mo_interp_osc_H_stmt d := by
  intro T hlin hL2 r0 r1 s0 s1 M0 M1 hM0 hM1 h0 h1 θ hθ f hf
  obtain ⟨S, c, rfl⟩ := mova3_exists_comb hf
  set σ := (1 - θ) * s0 + θ * s1 with hσ
  set ρ := (1 - θ) * r0 + θ * r1 with hρ
  set Ψ := fourierL2 (T (mova3_comb S c)) with hΨdef
  have hΨ : MemLp Ψ 2 volume := memLp_fourierL2 (hL2 _ hf)
  set B := M0 ^ (1 - θ) * M1 ^ θ with hB
  have hBn : 0 ≤ B := mul_nonneg (Real.rpow_nonneg hM0 _) (Real.rpow_nonneg hM1 _)
  set X := Real.sqrt (∑ α ∈ S, oscEigenvalue d α ^ ρ * c α ^ 2) with hX
  have hXn : 0 ≤ X := Real.sqrt_nonneg _
  set g : Euc d → ℝ := fun ξ => mova3b1_W ξ ^ σ * ‖Ψ ξ‖ ^ 2 with hg
  have hg0 : ∀ ξ, 0 ≤ g ξ := fun ξ =>
    mul_nonneg (Real.rpow_nonneg (mova3b1_W_pos ξ).le _) (sq_nonneg _)
  have hgm : AEStronglyMeasurable g volume :=
    (mova3b1_W_rpow_cont σ).aestronglyMeasurable.mul (hΨ.aestronglyMeasurable.norm.pow 2)
  have hind : ∀ (n : ℕ) ξ, mova3b1_Q σ n Ψ ξ ^ 2 =
      (Metric.closedBall (0 : Euc d) n).indicator g ξ := fun n ξ => mova3b1_Q_sq σ n Ψ ξ
  have hbound : ∀ n : ℕ, ∫ ξ, mova3b1_Q σ n Ψ ξ ^ 2 ≤ (B * X) ^ 2 := by
    intro n
    have hl := mova3b1_three_lines hlin hL2 hM0 hM1 hθ.1 hθ.2 h0 h1 S c (n : ℝ)
    set N := ∫ ξ, mova3b1_Q σ n Ψ ξ ^ 2 with hN
    have hN0 : 0 ≤ N := integral_nonneg fun ξ => sq_nonneg _
    have hy : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0
    have hyn : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    have hle : Real.sqrt N ≤ B * X := by
      by_contra hlt
      rw [not_le] at hlt
      have hpos : 0 < Real.sqrt N := lt_of_le_of_lt (mul_nonneg hBn hXn) hlt
      nlinarith [hl, hy]
    calc N = Real.sqrt N ^ 2 := hy.symm
      _ ≤ (B * X) ^ 2 := pow_le_pow_left₀ hyn hle 2
  have hlim := mova3b1_monotone_limit hg0 hgm (C := (B * X) ^ 2) (sq_nonneg _)
    (fun n => (mova3b1_Q_sq_integrable σ n hΨ).congr
      (Eventually.of_forall fun ξ => hind n ξ))
    (fun n => by
      have := hbound n
      rwa [show (∫ ξ, mova3b1_Q σ n Ψ ξ ^ 2) =
        ∫ ξ, (Metric.closedBall (0 : Euc d) n).indicator g ξ from
          integral_congr_ae (Eventually.of_forall fun ξ => hind n ξ)] at this)
  refine ⟨⟨hL2 _ hf, hlim.1⟩, ?_⟩
  rw [mova3_oscNorm_comb]
  have : HRS.PDE.ToolboxRd.sobolevNormSq σ (T (mova3_comb S c)) = ∫ ξ, g ξ := rfl
  rw [this]
  calc Real.sqrt (∫ ξ, g ξ) ≤ Real.sqrt ((B * X) ^ 2) := Real.sqrt_le_sqrt hlim.2
    _ = B * X := Real.sqrt_sq (mul_nonneg hBn hXn)


/-! ## The bridge `B1`: `Σ^s → H^s` for multiplication by a `C_b^N` function

Real `s` by interpolation (`mo_interp_osc_H`) between the integer endpoints `⌊s⌋, ⌊s⌋+1`, which are
proved by the Leibniz rule for `∂_j^n (a f)`, the Fourier transform of `∂_j^n` of a `C^n` function with
`L²` derivatives (`tcs_fourier_partial`), and the `L²` bounds `‖∂_j^m f‖₂ ≲ ‖f‖_{Σ^m}` on the Hermite
span (`mo_partial_ext`). -/

section B1

open Finset

/-! ### Hermite span: derivative closure -/

/-- The coordinate derivative `∂_j u`. -/
def mova3b1_Dj (j : Fin d) (u : Euc d → ℝ) : Euc d → ℝ :=
  fun x => fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))

lemma mova3b1_Dj_hermite (α : MultiIndex d) (j : Fin d) :
    mova3b1_Dj j (hermiteFunD α) = fun x =>
      Real.sqrt ((α j : ℝ) / 2) * hermiteFunD (mova1_dn j α) x -
        Real.sqrt (((α j : ℝ) + 1) / 2) * hermiteFunD (mova1_up j α) x := by
  funext x
  have hd : DifferentiableAt ℝ (hermiteFunD α) x :=
    ((contDiff_hermiteFunD α).differentiable (by simp)) x
  unfold mova3b1_Dj
  rw [← hd.lineDeriv_eq_fderiv, ((hermiteFunD_line_data α j).1 x).lineDeriv, mova1_dQ_hD]

lemma mova3b1_hspan_contDiff {f : Euc d → ℝ} (hf : f ∈ mo_Hspan d) : ContDiff ℝ ∞ f := by
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨α, rfl⟩ := hx; exact contDiff_hermiteFunD α
  | zero => exact contDiff_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

lemma mova3b1_hspan_memOsc (r : ℝ) {f : Euc d → ℝ} (hf : f ∈ mo_Hspan d) : MemOsc r f := by
  obtain ⟨S, c, rfl⟩ := mova3_exists_comb hf
  exact mo_hsum_memOsc r S c

lemma mova3b1_Dj_mem (j : Fin d) {f : Euc d → ℝ} (hf : f ∈ mo_Hspan d) :
    mova3b1_Dj j f ∈ mo_Hspan d := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, rfl⟩ := hx
    rw [mova3b1_Dj_hermite]
    have h1 := (mo_Hspan d).smul_mem (Real.sqrt ((α j : ℝ) / 2)) (mova3_hermite_mem (mova1_dn j α))
    have h2 := (mo_Hspan d).smul_mem (Real.sqrt (((α j : ℝ) + 1) / 2))
      (mova3_hermite_mem (mova1_up j α))
    convert (mo_Hspan d).sub_mem h1 h2 using 1
  | zero =>
    have : mova3b1_Dj j (0 : Euc d → ℝ) = 0 := by funext x; simp [mova3b1_Dj]
    rw [this]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    have : mova3b1_Dj j (x + y) = mova3b1_Dj j x + mova3b1_Dj j y := by
      funext z
      have h1 := ((mova3b1_hspan_contDiff hx).differentiable (by simp)) z
      have h2 := ((mova3b1_hspan_contDiff hy).differentiable (by simp)) z
      simp only [mova3b1_Dj, Pi.add_apply]
      rw [fderiv_add h1 h2]
      rfl
    rw [this]; exact Submodule.add_mem _ ihx ihy
  | smul a x hx ihx =>
    have : mova3b1_Dj j (a • x) = a • mova3b1_Dj j x := by
      funext z
      have h1 := ((mova3b1_hspan_contDiff hx).differentiable (by simp)) z
      simp only [mova3b1_Dj, Pi.smul_apply]
      rw [fderiv_const_smul h1 a]
      rfl
    rw [this]; exact Submodule.smul_mem _ _ ihx

lemma mova3b1_Dj_iter_mem (j : Fin d) (m : ℕ) {f : Euc d → ℝ} (hf : f ∈ mo_Hspan d) :
    (mova3b1_Dj j)^[m] f ∈ mo_Hspan d := by
  induction m generalizing f with
  | zero => simpa using hf
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    exact ih (mova3b1_Dj_mem j hf)

/-- `‖∂_j^m f‖_{Σ^r} ≤ C ‖f‖_{Σ^{r+m}}` on the Hermite span. -/
lemma mova3b1_Dj_iter_osc (m : ℕ) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin d) (f : Euc d → ℝ), f ∈ mo_Hspan d →
      MemOsc r ((mova3b1_Dj j)^[m] f) ∧
        oscNorm r ((mova3b1_Dj j)^[m] f) ≤ C * oscNorm (r + m) f := by
  induction m generalizing r with
  | zero =>
    refine ⟨1, zero_le_one, fun j f hf => ⟨?_, ?_⟩⟩
    · simpa using mova3b1_hspan_memOsc r hf
    · simp
  | succ m ih =>
    obtain ⟨C1, hC1, h1⟩ := ih r
    obtain ⟨C2, hC2, h2⟩ := mo_partial_ext (d := d) (r + m)
    refine ⟨C1 * C2, mul_nonneg hC1 hC2, fun j f hf => ?_⟩
    have hg := mova3b1_Dj_mem j hf
    obtain ⟨hm1, hb1⟩ := h1 j _ hg
    have hf1 : MemOsc (r + m + 1) f := mova3b1_hspan_memOsc _ hf
    obtain ⟨hm2, hb2⟩ := h2 j f hf1 ((mova3b1_hspan_contDiff hf).differentiable (by simp))
      (mova3_hspan_memLp hg)
    rw [Function.iterate_succ_apply]
    refine ⟨hm1, ?_⟩
    have e : r + ((m + 1 : ℕ) : ℝ) = r + m + 1 := by push_cast; ring
    rw [e]
    calc oscNorm r ((mova3b1_Dj j)^[m] (mova3b1_Dj j f))
        ≤ C1 * oscNorm (r + m) (mova3b1_Dj j f) := hb1
      _ ≤ C1 * (C2 * oscNorm (r + m + 1) f) := mul_le_mul_of_nonneg_left hb2 hC1
      _ = _ := by ring

lemma mova3b1_Dj_contDiff (j : Fin d) {k : ℕ} {u : Euc d → ℝ} (hu : ContDiff ℝ (k + 1 : ℕ) u) :
    ContDiff ℝ (k : ℕ) (mova3b1_Dj j u) := by
  unfold mova3b1_Dj
  exact (hu.fderiv_right (m := k) (by norm_cast)).clm_apply contDiff_const

lemma mova3b1_Dj_iter_contDiff (j : Fin d) : ∀ (m : ℕ) {k : ℕ} {u : Euc d → ℝ},
    ContDiff ℝ (k + m : ℕ) u → ContDiff ℝ (k : ℕ) ((mova3b1_Dj j)^[m] u) := by
  intro m
  induction m with
  | zero => intro k u hu; simpa using hu
  | succ m ih =>
    intro k u hu
    rw [Function.iterate_succ_apply']
    have h1 : ContDiff ℝ ((k + 1 : ℕ) + m : ℕ) u := by
      have : (k + 1 + m : ℕ) = k + (m + 1) := by omega
      rw [this]; exact hu
    exact mova3b1_Dj_contDiff j (ih h1)

lemma mova3b1_Dj_mul (j : Fin d) {u v : Euc d → ℝ} {x : Euc d} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) :
    mova3b1_Dj j (fun y => u y * v y) x = mova3b1_Dj j u x * v x + u x * mova3b1_Dj j v x := by
  unfold mova3b1_Dj
  rw [fderiv_fun_mul hu hv]
  simp
  ring

lemma mova3b1_Dj_const_mul (j : Fin d) (c : ℝ) {u : Euc d → ℝ} {x : Euc d}
    (hu : DifferentiableAt ℝ u x) :
    mova3b1_Dj j (fun y => c * u y) x = c * mova3b1_Dj j u x := by
  unfold mova3b1_Dj
  rw [fderiv_const_mul hu]
  simp

lemma mova3b1_Dj_sum (j : Fin d) {ι : Type*} (s : Finset ι) {g : ι → Euc d → ℝ} {x : Euc d}
    (hg : ∀ i ∈ s, DifferentiableAt ℝ (g i) x) :
    mova3b1_Dj j (fun y => ∑ i ∈ s, g i y) x = ∑ i ∈ s, mova3b1_Dj j (g i) x := by
  unfold mova3b1_Dj
  rw [fderiv_fun_sum hg]
  simp

/-- Leibniz rule for `∂_j^k (a f)`. -/
lemma mova3b1_leibniz (j : Fin d) : ∀ (k : ℕ) (a f : Euc d → ℝ), ContDiff ℝ (k : ℕ) a →
    ContDiff ℝ (k : ℕ) f → (mova3b1_Dj j)^[k] (fun x => a x * f x) = fun x =>
      ∑ ij ∈ antidiagonal k, (k.choose ij.1 : ℝ) *
        ((mova3b1_Dj j)^[ij.1] a x * (mova3b1_Dj j)^[ij.2] f x) := by
  intro k
  induction k with
  | zero => intro a f _ _; funext x; simp
  | succ k ih =>
    intro a f ha hf
    rw [Function.iterate_succ_apply', ih a f (ha.of_le (by norm_cast; omega))
      (hf.of_le (by norm_cast; omega))]
    funext x
    have hdiff : ∀ (g : Euc d → ℝ), ContDiff ℝ (k + 1 : ℕ) g → ∀ i ≤ k,
        DifferentiableAt ℝ ((mova3b1_Dj j)^[i] g) x := by
      intro g hg i hi
      have : ContDiff ℝ ((1 : ℕ) + i : ℕ) g := hg.of_le (by norm_cast; omega)
      exact ((mova3b1_Dj_iter_contDiff j i this).differentiable (by simp)) x
    have hs : ∀ ij ∈ antidiagonal k, DifferentiableAt ℝ
        (fun y => (k.choose ij.1 : ℝ) * ((mova3b1_Dj j)^[ij.1] a y * (mova3b1_Dj j)^[ij.2] f y)) x := by
      intro ij hij
      have h1 := mem_antidiagonal.1 hij
      exact (((hdiff a ha ij.1 (by omega)).mul (hdiff f hf ij.2 (by omega))).const_mul _)
    rw [mova3b1_Dj_sum j _ hs]
    have hterm : ∀ ij ∈ antidiagonal k,
        mova3b1_Dj j (fun y => (k.choose ij.1 : ℝ) *
          ((mova3b1_Dj j)^[ij.1] a y * (mova3b1_Dj j)^[ij.2] f y)) x =
        (k.choose ij.2 : ℝ) * ((mova3b1_Dj j)^[ij.1 + 1] a x * (mova3b1_Dj j)^[ij.2] f x) +
        (k.choose ij.1 : ℝ) * ((mova3b1_Dj j)^[ij.1] a x * (mova3b1_Dj j)^[ij.2 + 1] f x) := by
      intro ij hij
      have h1 := mem_antidiagonal.1 hij
      have hA := hdiff a ha ij.1 (by omega)
      have hB := hdiff f hf ij.2 (by omega)
      have hAB : DifferentiableAt ℝ
          (fun y => (mova3b1_Dj j)^[ij.1] a y * (mova3b1_Dj j)^[ij.2] f y) x := hA.mul hB
      rw [mova3b1_Dj_const_mul j _ hAB, mova3b1_Dj_mul j hA hB,
        Nat.choose_symm_of_eq_add h1.symm]
      simp only [Function.iterate_succ_apply']
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    have := Finset.sum_antidiagonal_choose_succ_mul
      (fun i m => (mova3b1_Dj j)^[i] a x * (mova3b1_Dj j)^[m] f x) k
    rw [add_comm]
    exact this.symm

lemma mova3b1_fourier_Dj_iter (n : ℕ) (j : Fin d) {u : Euc d → ℝ} (hu : ContDiff ℝ (n : ℕ) u)
    (hL : ∀ m ≤ n, MemLp ((mova3b1_Dj j)^[m] u) 2 volume) :
    ∀ m ≤ n, ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      ‖fourierL2 ((mova3b1_Dj j)^[m] u) ξ‖ = (2 * Real.pi * |ξ j|) ^ m * ‖fourierL2 u ξ‖ := by
  intro m
  induction m with
  | zero => intro _; exact Eventually.of_forall fun ξ => by simp
  | succ m ih =>
    intro hm
    have h1 : ContDiff ℝ ((1 : ℕ) + m : ℕ) u := hu.of_le (by norm_cast; omega)
    have hc := mova3b1_Dj_iter_contDiff j m h1
    have hp := HRS.MS.TcS.tcs_fourier_partial j (by exact_mod_cast hc) (hL m (by omega))
      (by
        have := hL (m + 1) hm
        rwa [Function.iterate_succ_apply'] at this)
    filter_upwards [ih (by omega), hp] with ξ h2 h3
    rw [Function.iterate_succ_apply']
    show ‖fourierL2 (fun x => fderiv ℝ ((mova3b1_Dj j)^[m] u) x
      (EuclideanSpace.single j (1 : ℝ))) ξ‖ = _
    rw [h3, norm_mul, h2]
    have : ‖(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ))‖ = 2 * Real.pi * |ξ j| := by
      simp [abs_of_pos Real.pi_pos]
    rw [this]; ring


/-- `H^n` bound by `‖u‖₂` and `‖∂_j^n u‖₂` for `C^n` functions with `L²` derivatives. -/
theorem mova3b1_sobolev_bound (n : ℕ) {u : Euc d → ℝ} (hu : ContDiff ℝ (n : ℕ) u)
    (hL : ∀ (j : Fin d), ∀ m ≤ n, MemLp ((mova3b1_Dj j)^[m] u) 2 volume)
    (hmu : MemLp u 2 volume) :
    HRS.PDE.ToolboxRd.MemSobolev (n : ℝ) u ∧ HRS.PDE.ToolboxRd.sobolevNormSq (n : ℝ) u ≤
      ((d : ℝ) + 1) ^ n * ((∫ x, u x ^ 2) + ∑ j : Fin d, ∫ x, ((mova3b1_Dj j)^[n] u x) ^ 2) := by
  set B : ℝ := ((d : ℝ) + 1) ^ n with hB
  have hB0 : 0 ≤ B := by positivity
  have hmG : ∀ j : Fin d, MemLp ((mova3b1_Dj j)^[n] u) 2 volume := fun j => hL j n le_rfl
  have hF := aestronglyMeasurable_fourierL2 hmu
  have hae : ∀ᵐ ξ : Euc d ∂volume, ∀ j : Fin d, ‖fourierL2 ((mova3b1_Dj j)^[n] u) ξ‖ =
      (2 * Real.pi * |ξ j|) ^ n * ‖fourierL2 u ξ‖ :=
    (ae_all_iff).2 fun j => mova3b1_fourier_Dj_iter n j hu (hL j) n le_rfl
  set bd : Euc d → ℝ := fun ξ => B * (‖fourierL2 u ξ‖ ^ 2 +
    ∑ j : Fin d, ‖fourierL2 ((mova3b1_Dj j)^[n] u) ξ‖ ^ 2) with hbd
  have hbdi : Integrable bd :=
    ((integrable_norm_sq_fourierL2 hmu).add
      (integrable_finsetSum _ fun j _ => integrable_norm_sq_fourierL2 (hmG j))).const_mul _
  have hle : ∀ᵐ ξ : Euc d ∂volume, wt ξ ^ (n : ℝ) * ‖fourierL2 u ξ‖ ^ 2 ≤ bd ξ := by
    filter_upwards [hae] with ξ hξ
    rw [Real.rpow_natCast]
    have h1 := mova1_wt_pow_le (d := d) n ξ
    have h2 : 0 ≤ ‖fourierL2 u ξ‖ ^ 2 := sq_nonneg _
    have h3 : ∀ j : Fin d, ‖fourierL2 ((mova3b1_Dj j)^[n] u) ξ‖ ^ 2 =
        ((2 * Real.pi * ξ j) ^ 2) ^ n * ‖fourierL2 u ξ‖ ^ 2 := by
      intro j
      rw [hξ j]
      have e : (2 * Real.pi * |ξ j|) ^ 2 = (2 * Real.pi * ξ j) ^ 2 := by
        rw [mul_pow, sq_abs, ← mul_pow]
      have key : ∀ A N : ℝ, (A ^ n * N) ^ 2 = (A ^ 2) ^ n * N ^ 2 := fun A N => by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm n 2]
      rw [key, e]
    simp only [hbd, h3]
    calc wt ξ ^ n * ‖fourierL2 u ξ‖ ^ 2
        ≤ (B * (1 + ∑ j, ((2 * Real.pi * ξ j) ^ 2) ^ n)) * ‖fourierL2 u ξ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = B * (‖fourierL2 u ξ‖ ^ 2 + ∑ j, ((2 * Real.pi * ξ j) ^ 2) ^ n * ‖fourierL2 u ξ‖ ^ 2) := by
          rw [← Finset.sum_mul]; ring
  have hint : Integrable (fun ξ : Euc d => wt ξ ^ (n : ℝ) * ‖fourierL2 u ξ‖ ^ 2) := by
    refine Integrable.mono' hbdi (aesm_wt_mul hF (n : ℝ)) ?_
    filter_upwards [hle] with ξ hξ
    have h0 : 0 ≤ wt ξ ^ (n : ℝ) * ‖fourierL2 u ξ‖ ^ 2 := by
      have := wt_pos (d := d) ξ
      positivity
    rw [Real.norm_of_nonneg h0]
    exact hξ
  refine ⟨⟨hmu, hint⟩, ?_⟩
  rw [sobolevNormSq_eq]
  calc ∫ ξ, wt ξ ^ (n : ℝ) * ‖fourierL2 u ξ‖ ^ 2 ≤ ∫ ξ, bd ξ := integral_mono_ae hint hbdi hle
    _ = B * ((∫ x, u x ^ 2) + ∑ j : Fin d, ∫ x, ((mova3b1_Dj j)^[n] u x) ^ 2) := by
        simp only [hbd]
        rw [integral_const_mul, integral_add (integrable_norm_sq_fourierL2 hmu)
          (integrable_finsetSum _ fun j _ => integrable_norm_sq_fourierL2 (hmG j)),
          integral_finsetSum _ fun j _ => integrable_norm_sq_fourierL2 (hmG j),
          integral_norm_sq_fourierL2 hmu]
        congr 2
        exact Finset.sum_congr rfl fun j _ => integral_norm_sq_fourierL2 (hmG j)

/-- Hypothesis form of `C_b^N`: `‖(∂_j)^i θ‖_∞ ≤ M` for `i ≤ N`. -/
def mova3b1_DirBdd (N : ℕ) (a : Euc d → ℝ) (M : ℝ) : Prop :=
  ∀ (j : Fin d) (i : ℕ), i ≤ N → ∀ x, |(mova3b1_Dj j)^[i] a x| ≤ M

lemma mova3b1_Dj_a_bound (n : ℕ) {a : Euc d → ℝ} {M : ℝ} (ha : ContDiff ℝ (n : ℕ) a)
    (hM : mova3b1_DirBdd n a M) {f : Euc d → ℝ} (hf : f ∈ mo_Hspan d) (j : Fin d) (m : ℕ)
    (hm : m ≤ n) {K : ℝ} (hK : ∀ i ≤ n, ∫ x, ((mova3b1_Dj j)^[i] f x) ^ 2 ≤ K ^ 2) :
    MemLp ((mova3b1_Dj j)^[m] (fun x => a x * f x)) 2 volume ∧
      ∫ x, ((mova3b1_Dj j)^[m] (fun x => a x * f x) x) ^ 2 ≤
        (((m : ℝ) + 1) * (2 ^ m * M) * K) ^ 2 := by
  have hfs : ContDiff ℝ (n : ℕ) f := (mova3b1_hspan_contDiff hf).of_le (by exact_mod_cast le_top)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM j 0 (Nat.zero_le _) 0)
  have hleib := mova3b1_leibniz j m a f (ha.of_le (by exact_mod_cast hm))
    (hfs.of_le (by exact_mod_cast hm))
  -- pieces
  have hB : ∀ i, MemLp ((mova3b1_Dj j)^[i] f) 2 volume := fun i =>
    mova3_hspan_memLp (mova3b1_Dj_iter_mem j i hf)
  have hBc : ∀ i, Continuous ((mova3b1_Dj j)^[i] f) := fun i =>
    (mova3b1_hspan_contDiff (mova3b1_Dj_iter_mem j i hf)).continuous
  have hAc : ∀ i ≤ m, Continuous ((mova3b1_Dj j)^[i] a) := fun i hi => by
    have : ContDiff ℝ ((0 : ℕ) + i : ℕ) a := ha.of_le (by norm_cast; omega)
    exact (mova3b1_Dj_iter_contDiff j i this).continuous
  have hAb : ∀ i ≤ m, ∀ x, |(mova3b1_Dj j)^[i] a x| ≤ M := fun i hi x => hM j i (by omega) x
  set z : ℕ × ℕ → Euc d → ℝ := fun ij x => (m.choose ij.1 : ℝ) *
    ((mova3b1_Dj j)^[ij.1] a x * (mova3b1_Dj j)^[ij.2] f x) with hz
  have hch : ∀ ij ∈ antidiagonal m, (m.choose ij.1 : ℝ) ≤ 2 ^ m := fun ij _ => by
    exact_mod_cast Nat.choose_le_two_pow m ij.1
  have hzb : ∀ ij ∈ antidiagonal m, ∀ x, |z ij x| ≤ 2 ^ m * M * |(mova3b1_Dj j)^[ij.2] f x| := by
    intro ij hij x
    have hi : ij.1 ≤ m := by have := mem_antidiagonal.1 hij; omega
    simp only [hz, abs_mul, Nat.abs_cast]
    have h1 := hch ij hij
    have h2 := hAb ij.1 hi x
    have h3 := abs_nonneg ((mova3b1_Dj j)^[ij.2] f x)
    have h4 := abs_nonneg ((mova3b1_Dj j)^[ij.1] a x)
    calc (m.choose ij.1 : ℝ) * (|(mova3b1_Dj j)^[ij.1] a x| * |(mova3b1_Dj j)^[ij.2] f x|)
        ≤ 2 ^ m * (M * |(mova3b1_Dj j)^[ij.2] f x|) := by
          apply mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 h3) (by positivity) (by positivity)
      _ = _ := by ring
  have hzm : ∀ ij ∈ antidiagonal m, MemLp (z ij) 2 volume := by
    intro ij hij
    have hi : ij.1 ≤ m := by have := mem_antidiagonal.1 hij; omega
    refine ((hB ij.2).norm.const_mul (2 ^ m * M)).of_le ?_ (Eventually.of_forall fun x => ?_)
    · exact (((hAc ij.1 hi).mul (hBc ij.2)).aestronglyMeasurable.const_mul _)
    · have := hzb ij hij x
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ m * M)]
      simpa [Real.norm_eq_abs, abs_abs] using this
  have hfun : (mova3b1_Dj j)^[m] (fun x => a x * f x) = fun x => ∑ ij ∈ antidiagonal m, z ij x := hleib
  have hL2 : MemLp ((mova3b1_Dj j)^[m] (fun x => a x * f x)) 2 volume := by
    rw [hfun]; exact memLp_finsetSum _ hzm
  refine ⟨hL2, ?_⟩
  set Bf : ℕ × ℕ → Euc d → ℝ := fun ij x => (mova3b1_Dj j)^[ij.2] f x with hBf
  have hcard : (antidiagonal m).card = m + 1 := Finset.Nat.card_antidiagonal m
  have hsq : ∀ x, ((mova3b1_Dj j)^[m] (fun x => a x * f x) x) ^ 2 ≤
      ((m : ℝ) + 1) * ∑ ij ∈ antidiagonal m, (2 ^ m * M) ^ 2 * (Bf ij x) ^ 2 := by
    intro x
    rw [hfun]
    show (∑ ij ∈ antidiagonal m, z ij x) ^ 2 ≤ _
    have h1 : |∑ ij ∈ antidiagonal m, z ij x| ≤ ∑ ij ∈ antidiagonal m, 2 ^ m * M * |Bf ij x| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ij hij => hzb ij hij x)
    calc (∑ ij ∈ antidiagonal m, z ij x) ^ 2 = |∑ ij ∈ antidiagonal m, z ij x| ^ 2 :=
          (sq_abs _).symm
      _ ≤ (∑ ij ∈ antidiagonal m, 2 ^ m * M * |Bf ij x|) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ ≤ (antidiagonal m).card * ∑ ij ∈ antidiagonal m, (2 ^ m * M * |Bf ij x|) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ = _ := by
          rw [hcard]
          push_cast
          congr 1
          refine Finset.sum_congr rfl fun ij _ => ?_
          rw [mul_pow, sq_abs]
  have hI1 : Integrable (fun x => ((m : ℝ) + 1) * ∑ ij ∈ antidiagonal m,
      (2 ^ m * M) ^ 2 * (Bf ij x) ^ 2) volume :=
    (integrable_finsetSum _ fun ij _ => (hB ij.2).integrable_sq.const_mul _).const_mul _
  calc ∫ x, ((mova3b1_Dj j)^[m] (fun x => a x * f x) x) ^ 2
      ≤ ∫ x, ((m : ℝ) + 1) * ∑ ij ∈ antidiagonal m, (2 ^ m * M) ^ 2 * (Bf ij x) ^ 2 :=
        integral_mono hL2.integrable_sq hI1 hsq
    _ = ((m : ℝ) + 1) * ∑ ij ∈ antidiagonal m, (2 ^ m * M) ^ 2 * ∫ x, (Bf ij x) ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ fun ij _ =>
          (hB ij.2).integrable_sq.const_mul _]
        congr 1
        exact Finset.sum_congr rfl fun ij _ => integral_const_mul _ _
    _ ≤ ((m : ℝ) + 1) * ∑ ij ∈ antidiagonal m, (2 ^ m * M) ^ 2 * K ^ 2 := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun ij hij => ?_) (by positivity)
        have hi : ij.2 ≤ m := by have := mem_antidiagonal.1 hij; omega
        exact mul_le_mul_of_nonneg_left (hK ij.2 (by omega)) (by positivity)
    _ = (((m : ℝ) + 1) * (2 ^ m * M) * K) ^ 2 := by
        rw [Finset.sum_const, hcard]
        simp only [nsmul_eq_mul]
        push_cast
        ring


/-- **Integer endpoint of the bridge `B1`.**  `‖a f‖_{H^n} ≤ C M ‖f‖_{Σ^n}` for `f` in the Hermite
span, `a ∈ C^n` with `|a| ≤ M` and `|∂_j^i a| ≤ M` (`i ≤ n`, all `j`); `C` depends on `d, n` only. -/
theorem mova3b1_int_endpoint (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : Euc d → ℝ) (M : ℝ),
    (∀ x, |a x| ≤ M) → ContDiff ℝ (n : ℕ) a → mova3b1_DirBdd n a M → ∀ f ∈ mo_Hspan d,
      HRS.PDE.ToolboxRd.MemSobolev (n : ℝ) (fun x => a x * f x) ∧
        Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (n : ℝ) (fun x => a x * f x)) ≤
          C * M * oscNorm (n : ℝ) f := by
  choose Cm hCm0 hCm using fun m : ℕ => mova3b1_Dj_iter_osc (d := d) m 0
  set K : ℝ := 1 + ∑ m ∈ range (n + 1), Cm m with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ ∑ m ∈ range (n + 1), Cm m := sum_nonneg fun m _ => hCm0 m
    linarith
  have hKm : ∀ m ≤ n, Cm m ≤ K := fun m hm => by
    have := Finset.single_le_sum (f := Cm) (fun i _ => hCm0 i) (Finset.mem_range.2 (by omega : m < n + 1))
    linarith
  refine ⟨Real.sqrt (((d : ℝ) + 1) ^ (n + 1)) * (n + 1) * 2 ^ n * K, by positivity,
    fun a M hab ha hM f hf => ?_⟩
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hab 0)
  set u : Euc d → ℝ := fun x => a x * f x with hu
  set osc : ℝ := oscNorm (n : ℝ) f with hosc
  set Kf : ℝ := K * osc with hKf
  have hosc0 : 0 ≤ osc := Real.sqrt_nonneg _
  have hKf0 : 0 ≤ Kf := mul_nonneg (by linarith) hosc0
  have hfm : MemOsc (n : ℝ) f := mova3b1_hspan_memOsc _ hf
  have hfL2 := mova3_hspan_memLp hf
  have hKb : ∀ (j : Fin d), ∀ i ≤ n, ∫ x, ((mova3b1_Dj j)^[i] f x) ^ 2 ≤ Kf ^ 2 := by
    intro j i hi
    have hg := mova3_hspan_memLp (mova3b1_Dj_iter_mem j i hf)
    have h0 := oscNorm_zero _ hg
    have h1 := (hCm i j f hf).2
    have h2 : oscNorm ((0 : ℝ) + i) f ≤ osc := by
      have := (mo_mono (r := (0 : ℝ) + i) (r' := (n : ℝ)) (by simp; exact_mod_cast hi) hfm).2
      exact this
    have h3 : oscNorm 0 ((mova3b1_Dj j)^[i] f) ≤ Kf := by
      calc oscNorm 0 ((mova3b1_Dj j)^[i] f) ≤ Cm i * oscNorm ((0 : ℝ) + i) f := h1
        _ ≤ Cm i * osc := mul_le_mul_of_nonneg_left h2 (hCm0 i)
        _ ≤ K * osc := mul_le_mul_of_nonneg_right (hKm i hi) hosc0
    have h4 : 0 ≤ ∫ x, ((mova3b1_Dj j)^[i] f x) ^ 2 := integral_nonneg fun x => sq_nonneg _
    calc ∫ x, ((mova3b1_Dj j)^[i] f x) ^ 2 = oscNorm 0 ((mova3b1_Dj j)^[i] f) ^ 2 := by
          rw [h0, Real.sq_sqrt h4]
      _ ≤ Kf ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h3 2
  have hB := fun j m (hm : m ≤ n) => mova3b1_Dj_a_bound n ha hM hf j m hm (hKb j)
  -- the `L²` norm of `u` itself
  have hac : Continuous a := ha.continuous
  have hfc : Continuous f := (mova3b1_hspan_contDiff hf).continuous
  have hmu : MemLp u 2 volume := by
    refine (hfL2.norm.const_mul M).of_le ((hac.mul hfc).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    simp only [hu, Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg hM0]
    exact mul_le_mul_of_nonneg_right (hab x) (abs_nonneg _)
  have hfint : ∫ x, f x ^ 2 ≤ osc ^ 2 := by
    have h0 := oscNorm_zero f hfL2
    have h1 : oscNorm 0 f ≤ osc := (mo_mono (r := 0) (r' := (n : ℝ))
      (Nat.cast_nonneg n) hfm).2
    have h4 : 0 ≤ ∫ x, f x ^ 2 := integral_nonneg fun x => sq_nonneg _
    calc ∫ x, f x ^ 2 = oscNorm 0 f ^ 2 := by rw [h0, Real.sq_sqrt h4]
      _ ≤ osc ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  have hu2 : ∫ x, u x ^ 2 ≤ (M * osc) ^ 2 := by
    calc ∫ x, u x ^ 2 ≤ ∫ x, M ^ 2 * f x ^ 2 := by
          refine integral_mono hmu.integrable_sq (hfL2.integrable_sq.const_mul _)
            fun x => ?_
          simp only [hu]
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right
            (by rw [← sq_abs (a x)]; exact pow_le_pow_left₀ (abs_nonneg _) (hab x) 2) (sq_nonneg _)
      _ = M ^ 2 * ∫ x, f x ^ 2 := integral_const_mul _ _
      _ ≤ M ^ 2 * osc ^ 2 := mul_le_mul_of_nonneg_left hfint (sq_nonneg _)
      _ = (M * osc) ^ 2 := by ring
  have hL : ∀ j : Fin d, ∀ m ≤ n, MemLp ((mova3b1_Dj j)^[m] u) 2 volume := fun j m hm =>
    (hB j m hm).1
  have hfs : ContDiff ℝ (n : ℕ) f :=
    (mova3b1_hspan_contDiff hf).of_le (by exact_mod_cast le_top)
  obtain ⟨hmem, hsob⟩ := mova3b1_sobolev_bound n (ha.mul hfs) hL hmu
  refine ⟨hmem, ?_⟩
  set P : ℝ := ((n : ℝ) + 1) * 2 ^ n * M * Kf with hP
  have hP0 : 0 ≤ P := by positivity
  have hDn : ∀ j : Fin d, ∫ x, ((mova3b1_Dj j)^[n] u x) ^ 2 ≤ P ^ 2 := fun j => by
    have := (hB j n le_rfl).2
    rw [hP]
    calc _ ≤ _ := this
      _ = _ := by ring
  have hMo : (M * osc) ^ 2 ≤ P ^ 2 := by
    refine pow_le_pow_left₀ (mul_nonneg hM0 hosc0) ?_ 2
    rw [hP, hKf]
    have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) * 2 ^ n * K := by
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
        _ ≤ _ := by gcongr
    calc M * osc = 1 * (M * osc) := by ring
      _ ≤ (((n : ℝ) + 1) * 2 ^ n * K) * (M * osc) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg hM0 hosc0)
      _ = _ := by ring
  have hsum : ∑ j : Fin d, ∫ x, ((mova3b1_Dj j)^[n] u x) ^ 2 ≤ (d : ℝ) * P ^ 2 := by
    calc _ ≤ ∑ _j : Fin d, P ^ 2 := sum_le_sum fun j _ => hDn j
      _ = _ := by simp
  have hsq : HRS.PDE.ToolboxRd.sobolevNormSq (n : ℝ) u ≤
      (Real.sqrt (((d : ℝ) + 1) ^ (n + 1)) * P) ^ 2 := by
    calc _ ≤ ((d : ℝ) + 1) ^ n * ((∫ x, u x ^ 2) + ∑ j : Fin d, ∫ x, ((mova3b1_Dj j)^[n] u x) ^ 2) :=
          hsob
      _ ≤ ((d : ℝ) + 1) ^ n * (P ^ 2 + (d : ℝ) * P ^ 2) := by
          gcongr
          linarith
      _ = (Real.sqrt (((d : ℝ) + 1) ^ (n + 1)) * P) ^ 2 := by
          have e : (Real.sqrt (((d : ℝ) + 1) ^ (n + 1)) * P) ^ 2 = ((d : ℝ) + 1) ^ (n + 1) * P ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (by positivity)]
          rw [e]
          ring
  calc Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (n : ℝ) u)
      ≤ Real.sqrt ((Real.sqrt (((d : ℝ) + 1) ^ (n + 1)) * P) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (((d : ℝ) + 1) ^ (n + 1)) * P := Real.sqrt_sq (by positivity)
    _ = _ := by rw [hP, hKf]; ring

lemma mova3b1_Dj_iter_apply (j : Fin d) : ∀ (i : ℕ) {u : Euc d → ℝ}, ContDiff ℝ (i : ℕ) u →
    ∀ x, (mova3b1_Dj j)^[i] u x =
      iteratedFDeriv ℝ i u x (fun _ => (EuclideanSpace.single j (1 : ℝ) : Euc d)) := by
  intro i
  induction i with
  | zero => intro u hu x; simp
  | succ i ih =>
    intro u hu x
    rw [Function.iterate_succ_apply, ih (mova3b1_Dj_contDiff j hu) x]
    have h1 := ContinuousLinearMap.iteratedFDeriv_comp_left
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ) : Euc d))
      (f := fderiv ℝ u) (x := x) (n := i) (i := i)
      ((hu.fderiv_right (m := i) (by norm_cast)).contDiffAt) le_rfl
    have h2 : (mova3b1_Dj j u) = (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single j (1 : ℝ) : Euc d)) ∘ fderiv ℝ u := by
      funext y; rfl
    rw [h2, h1]
    have h3 := iteratedFDeriv_succ_apply_right (𝕜 := ℝ) (f := u) (x := x) (n := i)
      (fun _ => (EuclideanSpace.single j (1 : ℝ) : Euc d))
    rw [h3]
    rfl

lemma mova3b1_DirBdd_mono {N N' : ℕ} (h : N ≤ N') {a : Euc d → ℝ} {M : ℝ}
    (hM : mova3b1_DirBdd N' a M) : mova3b1_DirBdd N a M :=
  fun j i hi x => hM j i (hi.trans h) x

/-- **The bridge `B1`** (`Σ^s → H^s` for multiplication by a `C_b^N` function), real `s`.
For `0 ≤ s ≤ N`, `N` an integer, there is `C = C(d, s, N)` such that for every `C^N` function `a` with
`|a| ≤ M` and `|∂_j^i a| ≤ M` (`i ≤ N`, all coordinates `j`), and every `f` in the Hermite span,
`a f ∈ H^s` and `‖a f‖_{H^s} ≤ C M ‖f‖_{Σ^s}`. -/
theorem mo_bridge1 (s : ℝ) (hs : 0 ≤ s) (N : ℕ) (hN : s ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : Euc d → ℝ) (M : ℝ), (∀ x, |a x| ≤ M) → ContDiff ℝ (N : ℕ) a →
      mova3b1_DirBdd N a M → ∀ f ∈ mo_Hspan d,
        HRS.PDE.ToolboxRd.MemSobolev s (fun x => a x * f x) ∧
          Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s (fun x => a x * f x)) ≤
            C * M * oscNorm s f := by
  set n0 : ℕ := ⌊s⌋₊ with hn0
  have hn0s : (n0 : ℝ) ≤ s := Nat.floor_le hs
  by_cases hint : (n0 : ℝ) = s
  · obtain ⟨C0, hC0, h0⟩ := mova3b1_int_endpoint (d := d) n0
    refine ⟨C0, hC0, fun a M hab ha hM f hf => ?_⟩
    have hn0N : n0 ≤ N := by exact_mod_cast hint.le.trans hN
    rw [← hint]
    exact h0 a M hab (ha.of_le (by exact_mod_cast hn0N)) (mova3b1_DirBdd_mono hn0N hM) f hf
  · have hlt : (n0 : ℝ) < s := lt_of_le_of_ne hn0s hint
    have hn1N : n0 + 1 ≤ N := by
      have : (n0 : ℝ) < N := hlt.trans_le hN
      exact_mod_cast this
    have hs1 : s < (n0 : ℝ) + 1 := Nat.lt_floor_add_one s
    set θ : ℝ := s - n0 with hθ
    have hθ0 : 0 ≤ θ := by linarith
    have hθ1 : θ ≤ 1 := by linarith
    obtain ⟨C0, hC0, h0⟩ := mova3b1_int_endpoint (d := d) n0
    obtain ⟨C1, hC1, h1⟩ := mova3b1_int_endpoint (d := d) (n0 + 1)
    refine ⟨C0 ^ (1 - θ) * C1 ^ θ, mul_nonneg (Real.rpow_nonneg hC0 _) (Real.rpow_nonneg hC1 _),
      fun a M hab ha hM f hf => ?_⟩
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hab 0)
    have hn0N : n0 ≤ N := by omega
    have e0 := h0 a M hab (ha.of_le (by exact_mod_cast hn0N)) (mova3b1_DirBdd_mono hn0N hM)
    have e1 := h1 a M hab (ha.of_le (by exact_mod_cast hn1N)) (mova3b1_DirBdd_mono hn1N hM)
    have hT := mo_interp_osc_H d (T := fun f x => a x * f x)
      (fun f _ g _ c => by funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring)
      (fun f hf => by
        have hfL2 := mova3_hspan_memLp hf
        have hM0' : 0 ≤ M := hM0
        refine (hfL2.norm.const_mul M).of_le
          ((ha.continuous.mul (mova3b1_hspan_contDiff hf).continuous).aestronglyMeasurable)
          (Eventually.of_forall fun x => ?_)
        simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg hM0']
        exact mul_le_mul_of_nonneg_right (hab x) (abs_nonneg _))
      (r0 := (n0 : ℝ)) (r1 := ((n0 + 1 : ℕ) : ℝ)) (s0 := (n0 : ℝ)) (s1 := ((n0 + 1 : ℕ) : ℝ))
      (M0 := C0 * M) (M1 := C1 * M) (mul_nonneg hC0 hM0) (mul_nonneg hC1 hM0)
      (fun f hf => by
        have := e0 f hf
        exact ⟨this.1, by simpa [mul_assoc] using this.2⟩)
      (fun f hf => by
        have := e1 f hf
        exact ⟨this.1, by simpa [mul_assoc] using this.2⟩)
      (θ := θ) ⟨hθ0, hθ1⟩ f hf
    have hσ : (1 - θ) * (n0 : ℝ) + θ * ((n0 + 1 : ℕ) : ℝ) = s := by
      rw [hθ]; push_cast; ring
    rw [hσ] at hT
    refine ⟨hT.1, hT.2.trans (le_of_eq ?_)⟩
    rw [Real.mul_rpow hC0 hM0, Real.mul_rpow hC1 hM0]
    have : M ^ (1 - θ) * M ^ θ = M := by
      rw [← Real.rpow_add' hM0 (by linarith : (1 - θ) + θ ≠ 0)]; simp
    calc C0 ^ (1 - θ) * M ^ (1 - θ) * (C1 ^ θ * M ^ θ) * oscNorm s f
        = C0 ^ (1 - θ) * C1 ^ θ * (M ^ (1 - θ) * M ^ θ) * oscNorm s f := by ring
      _ = _ := by rw [this]

/-- `C_b^N` in the repository's form (`MemCb`, `cbNorm`) gives the hypotheses of `mo_bridge1`
with `M = cbNorm N a`. -/
lemma mova3b1_of_memCb {N : ℕ} {a : Euc d → ℝ} (ha : HRS.MemCb N a) :
    (∀ x, |a x| ≤ HRS.cbNorm N a) ∧ mova3b1_DirBdd N a (HRS.cbNorm N a) := by
  have hterm : ∀ i ≤ N, ∀ x, ‖iteratedFDeriv ℝ i a x‖ ≤ HRS.cbNorm N a := by
    intro i hi x
    unfold HRS.cbNorm
    have h1 : ‖iteratedFDeriv ℝ i a x‖ ≤ ⨆ z : Euc d, ‖iteratedFDeriv ℝ i a z‖ :=
      le_ciSup (ha.2 i hi) x
    have h2 : (⨆ z : Euc d, ‖iteratedFDeriv ℝ i a z‖) ≤
        ∑ k ∈ Finset.range (N + 1), ⨆ z : Euc d, ‖iteratedFDeriv ℝ k a z‖ :=
      Finset.single_le_sum (f := fun k => ⨆ z : Euc d, ‖iteratedFDeriv ℝ k a z‖)
        (fun k _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (by omega))
    exact h1.trans h2
  refine ⟨fun x => ?_, fun j i hi x => ?_⟩
  · have := hterm 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this
  · rw [mova3b1_Dj_iter_apply j i (ha.1.of_le (by exact_mod_cast hi)) x]
    refine (Real.norm_eq_abs _ ▸ ((iteratedFDeriv ℝ i a x).le_opNorm _).trans ?_).trans (hterm i hi x)
    simp

end B1

/-- **`B1` in the repository's `C_b^N` form** (`HRS.MemCb`, `HRS.cbNorm`): for `0 ≤ s ≤ N` there is
`C = C(d, s, N)` with `‖a f‖_{H^s} ≤ C ‖a‖_{C_b^N} ‖f‖_{Σ^s}` for all `a` with `MemCb N a` and all `f` in
the Hermite span. -/
theorem mo_bridge1_cb (s : ℝ) (hs : 0 ≤ s) (N : ℕ) (hN : s ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : Euc d → ℝ), HRS.MemCb N a → ∀ f ∈ mo_Hspan d,
      HRS.PDE.ToolboxRd.MemSobolev s (fun x => a x * f x) ∧
        Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s (fun x => a x * f x)) ≤
          C * HRS.cbNorm N a * oscNorm s f := by
  obtain ⟨C, hC, h⟩ := mo_bridge1 (d := d) s hs N hN
  refine ⟨C, hC, fun a ha f hf => ?_⟩
  obtain ⟨h1, h2⟩ := mova3b1_of_memCb ha
  exact h a _ h1 ha.1 h2 f hf

end HRS.MS.MovOsc
