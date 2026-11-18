import HRS.MD.Cov211Bias
import HRS.MD.Cov211Lower
import HRS.MD.Cov211Scheme

/-!
# Packet COV211, the family of continuous minorants

Index `i = 0` is `W_2`, `i = 1` is `W_1`, `i = j + 2` is `d_{j+2}`.  For each `i` we have a scaling
`wfam i N`, a distance `Tfam i N θ ∈ ℝ≥0∞` and a continuous nonnegative minorant `gfam i N θ` with
`ofReal (gfam i N θ) ≤ ofReal (wfam i N) * Tfam i N θ` (`θ ∈ [0,ε]`, `N ≥ 2`), built from
`|C_N - C|` minus a tail `taufam i N` (`= 0` for `W_2`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MD.Cov211

open HRS

/-- Standing hypotheses of Proposition 2.11. -/
structure Hyp (d : ℕ) (s β : ℝ) (k : Lattice d) (ρ : ℝ → Torus d → ℝ) : Prop where
  hd : 2 ≤ d
  hs1 : (d : ℝ) / 2 < s
  hsd : s < d
  hβ : 0 < β
  hk : k ≠ 0
  hρ : ∀ θ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β (ρ θ)

/-- `L_N²`, the squared truncation level, `32 D log (eN)`. -/
def Lsq (D : ℝ) (N : ℕ) : ℝ := 32 * D * Real.log (Real.exp 1 * N)

/-- The tail `40 D e^{-L_N²/(8D)}`. -/
def tau (D : ℝ) (N : ℕ) : ℝ := 40 * D * Real.exp (-(Lsq D N) / (8 * D))

/-- Universal constant of `w1_lower`. -/
def M1c : ℝ := Classical.choose w1_lower

theorem M1c_pos : 0 < M1c := (Classical.choose_spec w1_lower).1

theorem M1c_spec : ∀ (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (D : ℝ),
    0 < D →
    (∀ x : ℝ, 0 ≤ x → P {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D)))) →
    (∀ x : ℝ, 0 ≤ x → Q {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D)))) →
    ∀ L : ℝ, 1 ≤ L →
    ENNReal.ofReal (|∫ z, z ^ 2 ∂P - ∫ z, z ^ 2 ∂Q| - 40 * D * Real.exp (-L ^ 2 / (8 * D))) ≤
      ENNReal.ofReal (M1c * L) * wassersteinE 1 P Q :=
  (Classical.choose_spec w1_lower).2

/-- Constant of `dj_lower j`. -/
def Mjc (j : ℕ) : ℝ := Classical.choose (dj_lower j)

theorem Mjc_pos (j : ℕ) : 0 < Mjc j := (Classical.choose_spec (dj_lower j)).1

theorem Mjc_spec (j : ℕ) : ∀ (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (D : ℝ), 0 < D →
    (∀ x : ℝ, 0 ≤ x → P {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D)))) →
    (∀ x : ℝ, 0 ≤ x → Q {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D)))) →
    ∀ L : ℝ, 1 ≤ L →
    ENNReal.ofReal (|∫ z, z ^ 2 ∂P - ∫ z, z ^ 2 ∂Q| - 40 * D * Real.exp (-L ^ 2 / (8 * D))) ≤
      ENNReal.ofReal (Mjc j * L ^ 2) * ENNReal.ofReal (smoothDist j P Q) :=
  (Classical.choose_spec (dj_lower j)).2

/-- The constants `K_i`. -/
def Kfam (D D' : ℝ) : ℕ → ℝ
  | 0 => 2 * Real.sqrt D'
  | 1 => M1c * Real.sqrt (32 * D)
  | (j + 2) => 32 * D * Mjc (j + 2)

/-- The tails. -/
def taufam (D : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | (_ + 1), N => tau D N

/-- The scalings. -/
def wfam (d : ℕ) (s : ℝ) : ℕ → ℕ → ℝ
  | 0, N => (deltaN d s N)⁻¹
  | 1, N => Real.sqrt (Real.log (Real.exp 1 * N)) / deltaN d s N
  | (_ + 2), N => Real.log (Real.exp 1 * N) / deltaN d s N

/-- The distances. -/
def Tfam (d : ℕ) (s : ℝ) (k : Lattice d) (β : ℝ) (ρ : ℝ → Torus d → ℝ) : ℕ → ℕ → ℝ → ℝ≥0∞
  | 0, N, θ => wassersteinE 2 (rateLaw d s k β N θ) (rateGaussian d s k β (ρ θ))
  | 1, N, θ => wassersteinE 1 (rateLaw d s k β N θ) (rateGaussian d s k β (ρ θ))
  | (j + 2), N, θ => ENNReal.ofReal
      (smoothDist (j + 2) (rateLaw d s k β N θ) (rateGaussian d s k β (ρ θ)))

/-- The continuous minorants. -/
def gfam (d : ℕ) (s : ℝ) (k : Lattice d) (β : ℝ) (ρ : ℝ → Torus d → ℝ) (D D' : ℝ) (i N : ℕ)
    (θ : ℝ) : ℝ :=
  if 2 ≤ N then
    max 0 (|rateVarN d s k β N θ - covC d s β k ρ θ| - taufam D i N) /
      (Kfam D D' i * deltaN d s N)
  else 0

theorem gfam_nonneg (d : ℕ) (s : ℝ) (k : Lattice d) (β : ℝ) (ρ : ℝ → Torus d → ℝ) (D D' : ℝ)
    (hK : ∀ i, 0 ≤ Kfam D D' i) (hδ : ∀ N, 0 ≤ deltaN d s N) (i N : ℕ) (θ : ℝ) :
    0 ≤ gfam d s k β ρ D D' i N θ := by
  unfold gfam
  split_ifs
  · exact div_nonneg (le_max_left _ _) (mul_nonneg (hK i) (hδ N))
  · exact le_rfl

variable {d : ℕ} {s β : ℝ} {k : Lattice d} {ρ : ℝ → Torus d → ℝ}

theorem gfam_continuous (H : Hyp d s β k ρ) (D D' : ℝ) (i N : ℕ) :
    Continuous (gfam d s k β ρ D D' i N) := by
  unfold gfam
  split_ifs with hN
  · have h1 : Continuous (fun θ => rateVarN d s k β N θ - covC d s β k ρ θ) :=
      (rateVarN_continuous H.hd H.hs1.le H.hsd β H.hβ k H.hk hN).sub
        (C_continuous H.hd H.hs1.le H.hsd β H.hβ k H.hk ρ H.hρ)
    exact (continuous_const.max (h1.abs.sub continuous_const)).div_const _
  · exact continuous_const

/-! ### Elementary facts -/

theorem exp_one_mul_log_ge (N : ℕ) (hN : 1 ≤ N) : 1 ≤ Real.log (Real.exp 1 * N) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Real.log_mul (Real.exp_pos 1).ne' (by linarith), Real.log_exp]
  have := Real.log_nonneg hN'
  linarith

theorem Lsq_ge (D : ℝ) (hD : 1 ≤ D) (N : ℕ) (hN : 1 ≤ N) : 1 ≤ Lsq D N := by
  unfold Lsq
  have := exp_one_mul_log_ge N hN
  nlinarith

theorem tau_nonneg (D : ℝ) (hD : 0 ≤ D) (N : ℕ) : 0 ≤ tau D N := by
  unfold tau; positivity

theorem tau_le (D : ℝ) (hD : 0 < D) (N : ℕ) (hN : 1 ≤ N) :
    tau D N ≤ 40 * D * ((N : ℝ) ^ 4)⁻¹ := by
  unfold tau Lsq
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hy : 0 < Real.exp 1 * N := by positivity
  have h0 : -(32 * D * Real.log (Real.exp 1 * N)) / (8 * D) = -(4 * Real.log (Real.exp 1 * N)) := by
    field_simp; ring
  have h1 : Real.exp (-(4 * Real.log (Real.exp 1 * N))) = ((Real.exp 1 * N) ^ 4)⁻¹ := by
    rw [Real.exp_neg]
    congr 1
    rw [show (4 : ℝ) * Real.log (Real.exp 1 * N) = ((4 : ℕ) : ℝ) * Real.log (Real.exp 1 * N) by norm_num,
      Real.exp_nat_mul, Real.exp_log hy]
  rw [h0, h1]
  have h2 : ((Real.exp 1 * N) ^ 4)⁻¹ ≤ ((N : ℝ) ^ 4)⁻¹ := by
    apply inv_anti₀ (by positivity)
    apply pow_le_pow_left₀ hN'.le
    have : (1 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    nlinarith
  gcongr

theorem delta_inv_le (hs1 : (d : ℝ) / 2 < s) (N : ℕ) (hN : 1 ≤ N) : (deltaN d s N)⁻¹ ≤ N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hspos : 0 < s := lt_of_le_of_lt (by positivity) hs1
  have h1 : (N : ℝ) ^ (-1 : ℝ) ≤ deltaN d s N := by
    rw [deltaN_eq hs1]
    apply Real.rpow_le_rpow_of_exponent_le hN'
    have : (d : ℝ) / s ≤ 2 := by rw [div_le_iff₀ hspos]; linarith
    linarith
  rw [Real.rpow_neg_one] at h1
  have h2 : 0 < deltaN d s N := deltaN_pos hs1 (by omega)
  calc (deltaN d s N)⁻¹ ≤ ((N : ℝ)⁻¹)⁻¹ := inv_anti₀ (by positivity) h1
    _ = N := inv_inv _

theorem taufam_div_tendsto (hs1 : (d : ℝ) / 2 < s) (D : ℝ) (hD : 0 < D) (i : ℕ) :
    Tendsto (fun N : ℕ => taufam D i N / deltaN d s N) atTop (𝓝 0) := by
  cases i with
  | zero => simp [taufam]
  | succ i =>
    have hlim : Tendsto (fun N : ℕ => 40 * D * ((N : ℝ) ^ 3)⁻¹) atTop (𝓝 0) := by
      have h := (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp
        tendsto_natCast_atTop_atTop)).const_mul (40 * D)
      simpa using h
    refine squeeze_zero' (Filter.Eventually.of_forall fun N => ?_) ?_ hlim
    · unfold taufam
      exact div_nonneg (tau_nonneg D hD.le N) (by
        rcases Nat.eq_zero_or_pos N with h | h
        · subst h; rw [deltaN_eq hs1]; exact Real.rpow_nonneg (by simp) _
        · exact (deltaN_pos hs1 h).le)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have hδ : 0 < deltaN d s N := deltaN_pos hs1 (by omega)
      unfold taufam
      rw [div_eq_mul_inv]
      calc tau D N * (deltaN d s N)⁻¹ ≤ (40 * D * ((N : ℝ) ^ 4)⁻¹) * N :=
            mul_le_mul (tau_le D hD N hN) (delta_inv_le hs1 N hN) (by positivity) (by positivity)
        _ = 40 * D * ((N : ℝ) ^ 3)⁻¹ := by field_simp

end HRS.MD.Cov211
