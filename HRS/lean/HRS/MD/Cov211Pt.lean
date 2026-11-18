import HRS.MD.Cov211Fam

/-!
# Packet COV211, pointwise comparison `ofReal (gfam) ≤ ofReal (wfam) * Tfam` and interval averages
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MD.Cov211

open HRS

variable {d : ℕ} {s β : ℝ} {k : Lattice d} {ρ : ℝ → Torus d → ℝ}

theorem ofReal_div_le_aux {x K δ : ℝ} {T : ℝ≥0∞} (hK : 0 < K) (hδ : 0 < δ)
    (h : ENNReal.ofReal x ≤ ENNReal.ofReal K * T) :
    ENNReal.ofReal (max 0 x / (K * δ)) ≤ ENNReal.ofReal δ⁻¹ * T := by
  have hmax : ENNReal.ofReal (max 0 x) = ENNReal.ofReal x := by
    rcases le_total 0 x with h0 | h0
    · rw [max_eq_right h0]
    · rw [max_eq_left h0, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h0]
  have h1 : ENNReal.ofReal (max 0 x / (K * δ)) =
      ENNReal.ofReal δ⁻¹ * (ENNReal.ofReal K⁻¹ * ENNReal.ofReal (max 0 x)) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hK.le), ← ENNReal.ofReal_mul (inv_nonneg.2 hδ.le)]
    congr 1
    field_simp
  rw [h1, hmax]
  gcongr
  calc ENNReal.ofReal K⁻¹ * ENNReal.ofReal x ≤ ENNReal.ofReal K⁻¹ * (ENNReal.ofReal K * T) := by
        gcongr
    _ = T := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hK.le), inv_mul_cancel₀ hK.ne',
          ENNReal.ofReal_one, one_mul]

section Laws

variable (H : Hyp d s β k ρ)
include H

theorem rateLaw_tail {N : ℕ} (hN : 2 ≤ N) (θ D : ℝ)
    (htail : ∀ x : ℝ, 0 ≤ x → rateGibbs d s k β θ N {X | x < |rateY d s k β N θ X|} +
      gaussianReal 0 (covC d s β k ρ θ).toNNReal {z | x < |z|} ≤
        ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D)))) (x : ℝ) (hx : 0 ≤ x) :
    rateLaw d s k β N θ {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D))) := by
  unfold rateLaw
  rw [Measure.map_apply (rateY_measurable k β θ N)
    (measurableSet_lt measurable_const measurable_abs : MeasurableSet {z : ℝ | x < |z|})]
  exact le_trans le_self_add (htail x hx)

theorem rateGaussian_tail {N : ℕ} (hN : 2 ≤ N) (θ D : ℝ)
    (htail : ∀ x : ℝ, 0 ≤ x → rateGibbs d s k β θ N {X | x < |rateY d s k β N θ X|} +
      gaussianReal 0 (covC d s β k ρ θ).toNNReal {z | x < |z|} ≤
        ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D)))) (x : ℝ) (hx : 0 ≤ x) :
    rateGaussian d s k β (ρ θ) {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D))) :=
  le_trans le_add_self (htail x hx)

end Laws

/-- Pointwise comparison. -/
theorem hmin (H : Hyp d s β k ρ) (ε D D' : ℝ) (hD2 : 2 ≤ D) (hD' : 1 ≤ D')
    (htail : ∀ x : ℝ, 0 ≤ x → ∀ N : ℕ, 2 ≤ N → ∀ θ ∈ Icc 0 ε,
      rateGibbs d s k β θ N {X | x < |rateY d s k β N θ X|} +
        gaussianReal 0 (covC d s β k ρ θ).toNNReal {z | x < |z|} ≤
        ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D))))
    (hCN : ∀ N : ℕ, 2 ≤ N → ∀ θ ∈ Icc 0 ε, rateVarN d s k β N θ ≤ D')
    (i N : ℕ) (hN : 2 ≤ N) (θ : ℝ) (hθ : θ ∈ Icc 0 ε) :
    ENNReal.ofReal (gfam d s k β ρ D D' i N θ) ≤
      ENNReal.ofReal (wfam d s i N) * Tfam d s k β ρ i N θ := by
  have hD : 0 < D := by linarith
  have hD'0 : 0 < D' := by linarith
  have hN0 : 0 < N := by omega
  have hN1 : 1 ≤ N := hN0
  haveI hP : IsProbabilityMeasure (rateLaw d s k β N θ) :=
    rateLaw_isProb H.hd H.hs1.le H.hsd H.hβ k hN0 θ
  haveI hQ : IsProbabilityMeasure (rateGaussian d s k β (ρ θ)) := rateGaussian_isProb _ _ _ _ _
  have htP := rateLaw_tail H hN θ D (fun x hx => htail x hx N hN θ hθ)
  have htQ := rateGaussian_tail H hN θ D (fun x hx => htail x hx N hN θ hθ)
  have hCnn : 0 ≤ covC d s β k ρ θ := C_nonneg H.hd H.hs1.le H.hsd β H.hβ k ρ H.hρ θ
  have hC1 : covC d s β k ρ θ ≤ 1 := C_le_one H.hd H.hs1.le H.hsd β H.hβ k H.hk ρ H.hρ θ
  have hmP : ∫ z, z ^ 2 ∂(rateLaw d s k β N θ) = rateVarN d s k β N θ := integral_sq_rateLaw k β N θ
  have hmQ : ∫ z, z ^ 2 ∂(rateGaussian d s k β (ρ θ)) = covC d s β k ρ θ :=
    integral_sq_rateGaussian d s k β (ρ θ) hCnn
  have hiP := integrable_sq_of_tail _ D hD htP
  have hiQ := integrable_sq_of_tail _ D hD htQ
  have hδ : 0 < deltaN d s N := deltaN_pos H.hs1 hN0
  have hlogge := exp_one_mul_log_ge N hN1
  unfold gfam
  rw [if_pos hN]
  rcases i with _ | _ | j
  · -- W2
    have h2 := w2_lower _ _ hiP hiQ D' hD'0 (by rw [hmP]; exact hCN N hN θ hθ)
      (by rw [hmQ]; linarith)
    rw [hmP, hmQ] at h2
    have hKpos : 0 < Kfam D D' 0 := by unfold Kfam; positivity
    have := ofReal_div_le_aux (x := |rateVarN d s k β N θ - covC d s β k ρ θ| - taufam D 0 N)
      (K := Kfam D D' 0) (δ := deltaN d s N) hKpos hδ (by
        simp only [taufam, sub_zero, Kfam]; exact h2)
    simpa [wfam, Tfam] using this
  · -- W1
    have hLsq1 := Lsq_ge D (by linarith) N hN1
    set L := Real.sqrt (Lsq D N) with hL
    have hL1 : 1 ≤ L := by rw [hL]; exact Real.one_le_sqrt.2 hLsq1
    have hL2 : L ^ 2 = Lsq D N := Real.sq_sqrt (by linarith)
    have hlog0 : 0 ≤ Real.log (Real.exp 1 * N) := by linarith
    have hLfac : L = Real.sqrt (32 * D) * Real.sqrt (Real.log (Real.exp 1 * N)) := by
      rw [hL]; unfold Lsq; rw [Real.sqrt_mul (by positivity)]
    have hw := M1c_spec _ _ D hD htP htQ L hL1
    rw [hmP, hmQ, hL2] at hw
    have hK : ENNReal.ofReal (M1c * L) = ENNReal.ofReal (Kfam D D' 1) *
        ENNReal.ofReal (Real.sqrt (Real.log (Real.exp 1 * N))) := by
      rw [hLfac, ← ENNReal.ofReal_mul (by unfold Kfam; have := M1c_pos; positivity)]
      congr 1
      unfold Kfam; ring
    have hKpos : 0 < Kfam D D' 1 := by unfold Kfam; have := M1c_pos; positivity
    have h := ofReal_div_le_aux (x := |rateVarN d s k β N θ - covC d s β k ρ θ| - taufam D 1 N)
      (K := Kfam D D' 1) (δ := deltaN d s N)
      (T := ENNReal.ofReal (Real.sqrt (Real.log (Real.exp 1 * N))) *
        wassersteinE 1 (rateLaw d s k β N θ) (rateGaussian d s k β (ρ θ))) hKpos hδ (by
        rw [← mul_assoc, ← hK]
        exact hw)
    refine h.trans (le_of_eq ?_)
    simp only [wfam, Tfam]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hδ.le), inv_mul_eq_div]
  · -- d_j, j + 2
    have hLsq1 := Lsq_ge D (by linarith) N hN1
    set L := Real.sqrt (Lsq D N) with hL
    have hL1 : 1 ≤ L := by rw [hL]; exact Real.one_le_sqrt.2 hLsq1
    have hL2 : L ^ 2 = Lsq D N := Real.sq_sqrt (by linarith)
    have hlog0 : 0 ≤ Real.log (Real.exp 1 * N) := by linarith
    have hw := Mjc_spec (j + 2) _ _ D hD htP htQ L hL1
    rw [hmP, hmQ, hL2] at hw
    have hK : ENNReal.ofReal (Mjc (j + 2) * Lsq D N) = ENNReal.ofReal (Kfam D D' (j + 2)) *
        ENNReal.ofReal (Real.log (Real.exp 1 * N)) := by
      rw [← ENNReal.ofReal_mul (by unfold Kfam; have := Mjc_pos (j + 2); positivity)]
      congr 1
      unfold Kfam Lsq; ring
    have hKpos : 0 < Kfam D D' (j + 2) := by unfold Kfam; have := Mjc_pos (j + 2); positivity
    have h := ofReal_div_le_aux (x := |rateVarN d s k β N θ - covC d s β k ρ θ| - taufam D (j + 2) N)
      (K := Kfam D D' (j + 2)) (δ := deltaN d s N)
      (T := ENNReal.ofReal (Real.log (Real.exp 1 * N)) *
        ENNReal.ofReal (smoothDist (j + 2) (rateLaw d s k β N θ) (rateGaussian d s k β (ρ θ))))
      hKpos hδ (by
        rw [← mul_assoc, ← hK]
        exact hw)
    refine h.trans (le_of_eq ?_)
    simp only [wfam, Tfam]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hδ.le), inv_mul_eq_div]

/-- Interval averages of the minorants are eventually bounded below. -/
theorem avg_lower (H : Hyp d s β k ρ) (ε D D' c₀ : ℝ) (hD : 0 < D) (hc₀ : 0 < c₀)
    (hB : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ ε → c₀ * (b - a) ≤
      supercriticalBias d s β (ρ b) (Torus.cosMode k) -
        supercriticalBias d s β (ρ a) (Torus.cosMode k))
    (i : ℕ) (hK : 0 < Kfam D D' i) (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < ε) :
    ∀ᶠ N : ℕ in atTop, (c₀ / (2 * Kfam D D' i)) * (b - a) ≤
      ∫ θ in a..b, gfam d s k β ρ D D' i N θ := by
  set K := Kfam D D' i with hKdef
  have hba : 0 < b - a := by linarith
  have hlim : Tendsto (fun N : ℕ => (1 / K) * ((deltaN d s N)⁻¹ * (∫ θ in a..b,
      (rateVarN d s k β N θ - covC d s β k ρ θ)) - (b - a) * (taufam D i N / deltaN d s N)))
      atTop (𝓝 ((1 / K) * ((supercriticalBias d s β (ρ b) (Torus.cosMode k) -
        supercriticalBias d s β (ρ a) (Torus.cosMode k)) - (b - a) * 0))) :=
    ((avg_tendsto H.hd H.hs1 H.hsd β H.hβ k H.hk ρ H.hρ a b).sub
      ((taufam_div_tendsto H.hs1 D hD i).const_mul (b - a))).const_mul (1 / K)
  have hgt : (c₀ / (2 * K)) * (b - a) < (1 / K) * ((supercriticalBias d s β (ρ b) (Torus.cosMode k) -
        supercriticalBias d s β (ρ a) (Torus.cosMode k)) - (b - a) * 0) := by
    have h1 := hB a b ha.le hab.le hb.le
    rw [mul_zero, sub_zero]
    have : (c₀ / (2 * K)) * (b - a) < (1 / K) * (c₀ * (b - a)) := by
      rw [show (c₀ / (2 * K)) * (b - a) = (1 / K) * (c₀ * (b - a) / 2) by field_simp]
      gcongr
      have : 0 < c₀ * (b - a) := by positivity
      linarith
    exact this.trans_le (by gcongr)
  filter_upwards [hlim.eventually_const_lt hgt, eventually_ge_atTop 2] with N hN hN2
  refine hN.le.trans ?_
  have hδ : 0 < deltaN d s N := deltaN_pos H.hs1 (by omega)
  have hcont1 : Continuous (fun θ => rateVarN d s k β N θ - covC d s β k ρ θ) :=
    (rateVarN_continuous H.hd H.hs1.le H.hsd β H.hβ k H.hk hN2).sub
      (C_continuous H.hd H.hs1.le H.hsd β H.hβ k H.hk ρ H.hρ)
  set τ := taufam D i N with hτ
  have hg0 : Continuous (fun θ => (rateVarN d s k β N θ - covC d s β k ρ θ - τ) /
      (K * deltaN d s N)) := (hcont1.sub continuous_const).div_const _
  have hmono : ∫ θ in a..b, (rateVarN d s k β N θ - covC d s β k ρ θ - τ) / (K * deltaN d s N) ≤
      ∫ θ in a..b, gfam d s k β ρ D D' i N θ := by
    refine intervalIntegral.integral_mono_on hab.le (hg0.intervalIntegrable _ _)
      ((gfam_continuous H D D' i N).intervalIntegrable _ _) fun θ _ => ?_
    unfold gfam
    rw [if_pos hN2]
    refine div_le_div_of_nonneg_right ?_ (mul_pos hK hδ).le
    exact le_trans (by linarith [le_abs_self (rateVarN d s k β N θ - covC d s β k ρ θ)])
      (le_max_right _ _)
  refine le_trans (le_of_eq ?_) hmono
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (hcont1.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const, smul_eq_mul]
  field_simp

end HRS.MD.Cov211
