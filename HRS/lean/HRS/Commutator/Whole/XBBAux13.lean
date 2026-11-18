import HRS.Commutator.Whole.XBBAux12

/-!
# Packet XBB, part 13: the Kato–Ponce estimate for `∂_a v_c` (assembly)

`xbb_core`: `‖∂_a v_c · Γ‖_{Ḣ^β} ≲ (‖∇v‖_∞ + ‖|∇|^α v‖_{L^p}) ‖Γ‖_{Ḣ^β}`, by the decomposition
`K_{j₀+k} ⋆ W = K_{j₀} ⋆ W + (K_{j₀+k} - K_{j₀}) ⋆ W` (T1 + T2) and Fatou as `k → ∞`.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section
namespace HRS.Commutator.Whole.XBB
open HRS.Commutator.Whole HRS.Commutator.Whole.XLI HRS.Commutator.Whole.XNRS
variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- **The Kato–Ponce estimate** for `W = ∂_a v_c` against a Fourier-localised Schwartz `Γ`. -/
lemma xbb_core (hd : 3 ≤ d) {β η p α : ℝ} (hβ : 0 < β) (hη : 0 ≤ η) (hp : 1 < p)
    (hrel : 1 / p - η / d = β / d) (hα : α = β + η + 1) (hβd : 2 * β < d) (a : Fin d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (c : Fin d) {v : 𝔼 → 𝔼}, XTVF v → ∀ {L F : ℝ}, 0 ≤ L → 0 ≤ F →
      XLip v L → ∀ {w : 𝔼 → 𝔼}, (∀ i, HRS.Whole.IsFracDerivRep α (fun x => v x i) (fun x => w x i)) →
      eLpNorm (fun x => ‖w x‖) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal F →
      ∀ (Γ GΓ : 𝓢(𝔼, ℂ)), XComp β Γ GΓ → ∀ ε : ℝ, 0 < ε → (∀ ξ : 𝔼, ‖ξ‖ < ε → 𝓕 (⇑Γ) ξ = 0) →
        xbbN β (fun x => ((xw v a c x : ℝ) : ℂ) * Γ x) ≤
          C * (ENNReal.ofReal F + ENNReal.ofReal L) * xbbN β ⇑Γ := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C1, hC1, h1⟩ := xbb_T1 hd1 hβ
  obtain ⟨C2, hC2, h2⟩ := xbb_T2 hd hβ hη hp hrel hα hβd a
  obtain ⟨A, hA, hAK⟩ := xbbK_lintegral_le d
  refine ⟨C1 + C2, ENNReal.add_ne_top.2 ⟨hC1, hC2⟩, ?_⟩
  intro c v hv L F hL hF hLip w hrep hw Γ GΓ hG ε hε hΓ
  -- the exponent `j₀`
  obtain ⟨j₀, hj₀, -⟩ := _root_.exists_mem_Ico_zpow hε (one_lt_two : (1 : ℝ) < 2)
  have hΓ' : ∀ ξ : 𝔼, ‖ξ‖ < (2 : ℝ) ^ j₀ → 𝓕 (⇑Γ) ξ = 0 := fun ξ hξ => hΓ ξ (hξ.trans_le hj₀)
  -- a measurable representative of `w`
  obtain ⟨w', hw'm, hrep', hw'⟩ := SAMP1.exists_meas_rep hrep hw
  set wc : 𝔼 → ℝ := fun x => w' x c with hwc
  have hwcm : Measurable wc := (EuclideanSpace.proj c : 𝔼 →L[ℝ] ℝ).continuous.measurable.comp hw'm
  have hwp : eLpNorm (fun z => ((wc z : ℝ) : ℂ)) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal F := by
    refine le_trans (eLpNorm_mono (g := fun x => ‖w' x‖)
      (Complex.measurable_ofReal.comp hwcm).aestronglyMeasurable (fun z => ?_)) hw'
    simp only [hwc, Complex.norm_real, norm_norm]
    exact (PiLp.norm_apply_le (w' z) c)
  have hb : ∀ z, |xw v a c z| ≤ L := fun z => xw_le hv hL hLip a c z
  -- the function `W`
  set W : 𝔼 → ℂ := fun z => ((xw v a c z : ℝ) : ℂ) with hW
  have hWs : ContDiff ℝ ∞ W := Complex.ofRealCLM.contDiff.comp (xtg_xw hv a c).1
  have hWb : ∀ z, ‖W z‖ ≤ L := fun z => by
    simp only [hW, Complex.norm_real, Real.norm_eq_abs]; exact hb z
  have hWm : Measurable W := hWs.continuous.measurable
  have hAr : ENNReal.ofReal A.toReal = A := ENNReal.ofReal_toReal hA
  have hcvb : ∀ (j : ℤ) x, ‖cv ⇑(xbbK j) W x‖ ≤ A.toReal * L := fun j x =>
    xbb_norm_cv_le (xbbK j).continuous.measurable hL ENNReal.toReal_nonneg
      (by rw [hAr]; exact hAK j) hWb x
  have hcvc : ∀ j : ℤ, Continuous (cv ⇑(xbbK j) W) := fun j =>
    BddAbove.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℂ ℂ)
      ⟨L, by rintro _ ⟨y, rfl⟩; exact hWb y⟩ (xbbK j).integrable hWs.continuous
  have hint : ∀ (j : ℤ), Integrable (fun x => cv ⇑(xbbK j) W x * Γ x) := fun j =>
    Γ.integrable.bdd_mul (c := A.toReal * L) (hcvc j).aestronglyMeasurable
      (Eventually.of_forall fun x => hcvb j x)
  set N := xbbN β ⇑Γ with hN
  set F' := ENNReal.ofReal F
  set L' := ENNReal.ofReal L
  have hbound : ∀ k : ℕ, xbbN β (fun x => cv ⇑(xbbK (j₀ + (k : ℤ))) W x * Γ x) ≤
      (C1 + C2) * (F' + L') * N := by
    intro k
    set j : ℤ := j₀ + (k : ℤ) with hj
    have hjj : j₀ ≤ j := by omega
    have hsplit : ∀ x, cv ⇑(xbbK j) W x = cv ⇑(xbbK j₀) W x +
        cv ⇑(xbbK j - xbbK j₀ : 𝓢(𝔼, ℂ)) W x := by
      intro x
      have := xbb_cv_sub (xbbK j).integrable (xbbK j₀).integrable hWm.aestronglyMeasurable hWb x
      have e : (⇑(xbbK j - xbbK j₀ : 𝓢(𝔼, ℂ)) : 𝔼 → ℂ) = fun y => xbbK j y - xbbK j₀ y := rfl
      rw [e, this]; ring
    have hB : Integrable (fun x => cv ⇑(xbbK j - xbbK j₀ : 𝓢(𝔼, ℂ)) W x * Γ x) := by
      have e : (fun x => cv ⇑(xbbK j - xbbK j₀ : 𝓢(𝔼, ℂ)) W x * Γ x) =
          fun x => cv ⇑(xbbK j) W x * Γ x - cv ⇑(xbbK j₀) W x * Γ x := by
        funext x; rw [hsplit x]; ring
      rw [e]; exact (hint j).sub (hint j₀)
    have e2 : (fun x => cv ⇑(xbbK j) W x * Γ x) = fun x =>
        (cv ⇑(xbbK j₀) W x * Γ x) + (cv ⇑(xbbK j - xbbK j₀ : 𝓢(𝔼, ℂ)) W x * Γ x) := by
      funext x; rw [hsplit x]; ring
    rw [e2]
    refine (xbbN_add_le β (hint j₀) hB).trans ?_
    have hT1 := h1 W hWs hL hWb j₀ Γ hΓ'
    have hT2 := h2 c hv hL hF hb hwcm hwp (hrep' c) j₀ j hjj Γ GΓ hG hΓ'
    calc _ ≤ C1 * L' * N + C2 * (F' + L') * N := add_le_add hT1 hT2
      _ ≤ C1 * (F' + L') * N + C2 * (F' + L') * N := by gcongr; exact le_add_self
      _ = _ := by ring
  have hlim : ∀ ξ : 𝔼, Tendsto (fun k : ℕ => 𝓕 (fun x => cv ⇑(xbbK (j₀ + (k : ℤ))) W x * Γ x) ξ) atTop
      (𝓝 (𝓕 (fun x => W x * Γ x) ξ)) := fun ξ =>
    xbb_fourier_tendsto (M := A.toReal * L) (fun k => (hcvc (j₀ + (k : ℤ))).aestronglyMeasurable)
      (fun k x => hcvb _ x) (fun x => xbb_approx hWs.continuous hWb j₀ x) ξ
  exact xbbN_fatou β (fun k => hint _) hlim hbound tendsto_const_nhds

end HRS.Commutator.Whole.XBB
