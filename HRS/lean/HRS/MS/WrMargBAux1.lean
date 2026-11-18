import HRS.MS.WrRefMargAux3
import HRS.MS.WrInsAux2

/-!
# HRS.MS.WrMargBAux1 -- full-law marginal: exact cavity equation and its ingredients (WR-13d, part 1)

Packet WR-13d (T10 of `docs/WR_B_PLAN.md`: `euc-cavity-equation`, `euc-unsimplified`), namespace `HRS.MS.Wr`,
helper prefix `wr13d_`.  Whole space `ℝ^d`, `2 ≤ d`, `0 < s < d`, `μ = ρ dx`, `ρ ≤ M`, `β ≥ 0`, `n ≥ 1`,
`N = n + 1`, `λ = β/N`, `π_N = (Q_N)^{(1)}`, `ν_n = (P_n^0)^{(1)}` (`Bias.cavityMarginal`).

* `wr13d_theta`: the density `dπ_N/dμ = e^{β g*μ} Φ_x / Z` of `wr13a_firstMarginal_eq_density`; it is
  measurable, strictly positive, bounded by `e^{2 β M_g}`, and integrates to `1`;
* `wr13d_log_theta` (the unsimplified cavity equation `euc-unsimplified`, exact and pointwise):
  `log θ(x) = β (g*μ)(x) + D_N(x) - λ n (g*ν_n)(x) - log Z`, with `D_N = Bias.insertionDefect`;
* `wr13d_cavMarg_le`: `ν_n ≤ C μ`;
* `wr13d_event_bound`: `|π_N(A) - ν_n(A)| ≤ C √(δ_N/N)` for every measurable `A` (from `wr13c2_cavity_tv`).

No hypothesis is added to the torus-style statements; all statements are unconditional in the displayed
parameters (`β ≥ 0` for the density facts, `β ∈ [βm, βp]` with `βm > 0` for the event bound).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

open HRS.Whole (rieszKernel EucConfig potentialBound)

variable {d : ℕ} {s : ℝ}

/-! ### 1. The density of `π_N` -/

/-- The normalising integral `Z = ∫ e^{β g*μ} Φ dμ`. -/
def wr13d_Z (d : ℕ) (s : ℝ) (n : ℕ) (β : ℝ) (μ : Measure (Euc d)) : ℝ :=
  ∫ y, Real.exp (β * HRS.Whole.convMeasure (rieszKernel d s) μ y) *
    HRS.Whole.poleNormalizer d s (n + 1) β μ y 1 ∂μ

/-- The density `θ = dπ_N/dμ = e^{β g*μ} Φ / Z` (`wr13a_firstMarginal_eq_density`). -/
def wr13d_theta (d : ℕ) (s : ℝ) (n : ℕ) (β : ℝ) (μ : Measure (Euc d)) (x : Euc d) : ℝ :=
  Real.exp (β * HRS.Whole.convMeasure (rieszKernel d s) μ x) *
    HRS.Whole.poleNormalizer d s (n + 1) β μ x 1 / wr13d_Z d s n β μ

section Density

variable {ρ : Euc d → ℝ} {M β : ℝ} {n : ℕ}

theorem wr13d_firstMarginal_eq (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d)
    (hρ : HRS.Whole.IsProbDensity ρ) (hM : ∀ x, ρ x ≤ M) (hβ : 0 ≤ β) (n : ℕ) :
    HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) (n + 1) β
        (HRS.Whole.withDensityReal ρ)) =
      (HRS.Whole.withDensityReal ρ).withDensity
        (fun x => ENNReal.ofReal (wr13d_theta d s n β (HRS.Whole.withDensityReal ρ) x)) :=
  wr13a_firstMarginal_eq_density hd hs0 hsd hρ hM hβ n

theorem wr13d_Z_pos (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d)
    (hρ : HRS.Whole.IsProbDensity ρ) (hM : ∀ x, ρ x ≤ M) (hβ : 0 ≤ β) (n : ℕ) :
    0 < wr13d_Z d s n β (HRS.Whole.withDensityReal ρ) := by
  have := wr13a_isProb_density hρ
  exact (wr13a_firstMarginal_eq hs0 (fun z => (wr13a_potential_bound (by omega) hs0 hsd hρ hM z).1)
    (wr13a_conv_le_density (by omega) hs0 hsd hρ hM)
    (wr13a_potentialBound_nonneg (by omega) hs0 hsd hρ hM) hβ n).1

theorem wr13d_Phi_pos (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d)
    (hρ : HRS.Whole.IsProbDensity ρ) (hM : ∀ x, ρ x ≤ M) (hβ : 0 ≤ β) (hn : 1 ≤ n) (x : Euc d) :
    0 < HRS.Whole.poleNormalizer d s (n + 1) β (HRS.Whole.withDensityReal ρ) x 1 :=
  (wr13a_cavityWellDefined_density hd hs0 hsd hρ hM hβ (n + 1) (by omega) x
    ⟨zero_le_one, le_rfl⟩).pole_pos

theorem wr13d_theta_pos (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d)
    (hρ : HRS.Whole.IsProbDensity ρ) (hM : ∀ x, ρ x ≤ M) (hβ : 0 ≤ β) (hn : 1 ≤ n) (x : Euc d) :
    0 < wr13d_theta d s n β (HRS.Whole.withDensityReal ρ) x :=
  div_pos (mul_pos (Real.exp_pos _) (wr13d_Phi_pos hd hs0 hsd hρ hM hβ hn x))
    (wr13d_Z_pos hd hs0 hsd hρ hM hβ n)

theorem wr13d_theta_meas (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d)
    (hρ : HRS.Whole.IsProbDensity ρ) (hM : ∀ x, ρ x ≤ M) (hβ : 0 ≤ β) (n : ℕ) :
    Measurable (wr13d_theta d s n β (HRS.Whole.withDensityReal ρ)) := by
  have := wr13a_isProb_density hρ
  exact ((Real.measurable_exp.comp ((wr13a_conv_meas hs0 (HRS.Whole.withDensityReal ρ)).const_mul β)).mul
    (wr13a_Phi_meas hs0 (wr13a_conv_le_density (by omega) hs0 hsd hρ hM) hβ n)).div_const _

/-- `θ ≤ exp (2 β M_g)` pointwise. -/
theorem wr13d_theta_le (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d)
    (hρ : HRS.Whole.IsProbDensity ρ) (hM : ∀ x, ρ x ≤ M) (hβ : 0 ≤ β) (n : ℕ) (x : Euc d) :
    wr13d_theta d s n β (HRS.Whole.withDensityReal ρ) x ≤ Real.exp (2 * β * potentialBound d s M) := by
  have := wr13a_isProb_density hρ
  have hint : ∀ z, Integrable (fun y => rieszKernel d s (z - y)) (HRS.Whole.withDensityReal ρ) :=
    fun z => (wr13a_potential_bound (by omega) hs0 hsd hρ hM z).1
  have hconv := wr13a_conv_le_density (by omega) hs0 hsd hρ hM
  have hMg0 := wr13a_potentialBound_nonneg (by omega) hs0 hsd hρ hM
  obtain ⟨-, hfun, -⟩ := wr13a_firstMarginal_eq hs0 hint hconv hMg0 hβ n
  have h1 : ENNReal.ofReal (wr13d_theta d s n β (HRS.Whole.withDensityReal ρ) x) ≤
      ENNReal.ofReal (Real.exp (2 * β * potentialBound d s M)) := by
    have := hfun x
    unfold wr13d_theta wr13d_Z
    rw [← this]
    exact wr13a_phi_le hs0 hint hconv hMg0 hβ n x
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).1 h1

theorem wr13d_firstMarginal_isProb (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d)
    (hρ : HRS.Whole.IsProbDensity ρ) (hM : ∀ x, ρ x ≤ M) (hβ : 0 ≤ β) (hn : 1 ≤ n) :
    IsProbabilityMeasure (HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) (n + 1) β
      (HRS.Whole.withDensityReal ρ))) := by
  have := wr13a_isProb_density hρ
  have := wr13c2_Q_isProb hs0 (wr13a_conv_le_density (by omega) hs0 hsd hρ hM) hβ
    (by omega : 1 ≤ n + 1)
  unfold HRS.Whole.firstMarginal
  rw [dif_pos (by omega : 0 < n + 1)]
  infer_instance

theorem wr13d_theta_integral (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d)
    (hρ : HRS.Whole.IsProbDensity ρ) (hM : ∀ x, ρ x ≤ M) (hβ : 0 ≤ β) (hn : 1 ≤ n) :
    ∫ x, wr13d_theta d s n β (HRS.Whole.withDensityReal ρ) x ∂(HRS.Whole.withDensityReal ρ) = 1 := by
  have := wr13a_isProb_density hρ
  have := wr13d_firstMarginal_isProb hd hs0 hsd hρ hM hβ hn
  have hm := wr13d_theta_meas hd hs0 hsd hρ hM hβ n
  have hint : Integrable (wr13d_theta d s n β (HRS.Whole.withDensityReal ρ))
      (HRS.Whole.withDensityReal ρ) :=
    Integrable.of_bound hm.aestronglyMeasurable (Real.exp (2 * β * potentialBound d s M))
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (wr13d_theta_pos hd hs0 hsd hρ hM hβ hn x)]
        exact wr13d_theta_le hd hs0 hsd hρ hM hβ n x)
  have h1 : ∫⁻ x, ENNReal.ofReal (wr13d_theta d s n β (HRS.Whole.withDensityReal ρ) x)
      ∂(HRS.Whole.withDensityReal ρ) = 1 := by
    have := measure_univ (μ := HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s)
      (n + 1) β (HRS.Whole.withDensityReal ρ)))
    rw [wr13d_firstMarginal_eq hd hs0 hsd hρ hM hβ n, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] at this
    exact this
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => (wr13d_theta_pos hd hs0 hsd hρ hM hβ hn x).le)] at h1
  exact (ENNReal.ofReal_eq_one.1 h1)

end Density

/-! ### 2. The exact cavity equation (`euc-unsimplified`) -/

section Cavity

variable {ρ : Euc d → ℝ} {M β : ℝ} {n : ℕ}

theorem wr13d_cavMarg_isProb (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d)
    (hρ : HRS.Whole.IsProbDensity ρ) (hM : ∀ x, ρ x ≤ M) (hβ : 0 ≤ β) (hn : 1 ≤ n) :
    IsProbabilityMeasure (HRS.Whole.cavityMarginal d s (n + 1) β (HRS.Whole.withDensityReal ρ)) := by
  have := wr13a_isProb_density hρ
  have := wr13a_cavityLaw_isProb hs0 (wr13a_conv_le_density (by omega) hs0 hsd hρ hM) hβ (n + 1)
  unfold HRS.Whole.cavityMarginal HRS.Whole.firstMarginal
  rw [dif_pos (by omega : 0 < n + 1 - 1)]
  infer_instance

/-- `∫ X_x dP_n^0 = -λ n (g*ν_n)(x)`. -/
theorem wr13d_integral_X (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d)
    (hρ : HRS.Whole.IsProbDensity ρ) (hM : ∀ x, ρ x ≤ M) (hβ : 0 ≤ β) (hn : 1 ≤ n) (x : Euc d) :
    ∫ Y, wr13c2_X d s (n + 1) β x Y ∂(HRS.Whole.cavityLaw d s (n + 1) β (HRS.Whole.withDensityReal ρ)) =
      -(β / ((n + 1 : ℕ) : ℝ)) * n *
        ∫ y, rieszKernel d s (x - y) ∂(HRS.Whole.cavityMarginal d s (n + 1) β (HRS.Whole.withDensityReal ρ)) := by
  have := wr13a_isProb_density hρ
  have hconv := wr13a_conv_le_density (by omega) hs0 hsd hρ hM
  have hpos : 0 < n + 1 - 1 := by omega
  set P0 := HRS.Whole.cavityLaw d s (n + 1) β (HRS.Whole.withDensityReal ρ) with hP0
  have hcoord : ∀ j : Fin (n + 1 - 1), ∫ Y : EucConfig d (n + 1 - 1), rieszKernel d s (x - Y j) ∂P0 =
      ∫ y, rieszKernel d s (x - y) ∂(HRS.Whole.cavityMarginal d s (n + 1) β (HRS.Whole.withDensityReal ρ)) := by
    intro j
    have e : P0.map (fun Y : EucConfig d (n + 1 - 1) => Y j) =
        HRS.Whole.cavityMarginal d s (n + 1) β (HRS.Whole.withDensityReal ρ) := by
      unfold HRS.Whole.cavityMarginal HRS.Whole.firstMarginal
      rw [dif_pos hpos]
      exact (wr13c2_cavityLaw_exchangeable hs0 hconv hβ (n + 1)).marginal_eq j ⟨0, hpos⟩
    rw [← e, integral_map (measurable_pi_apply j).aemeasurable
      (((wr13a_g_meas hs0).comp (measurable_const.sub measurable_id)).aestronglyMeasurable)]
  unfold wr13c2_X
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => wr13c2_integrable_coord hd hs0 hsd hρ hM hβ
    (by omega : 2 ≤ n + 1) x j)]
  rw [Finset.sum_congr rfl (fun j _ => hcoord j)]
  simp [Finset.sum_const, Finset.card_fin]
  ring

/-- **Unsimplified cavity equation** (`euc-unsimplified`), exact and pointwise:
`log θ(x) = β (g*μ)(x) + D_N(x) - λ n (g*ν_n)(x) - log Z`. -/
theorem wr13d_log_theta (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d)
    (hρ : HRS.Whole.IsProbDensity ρ) (hM : ∀ x, ρ x ≤ M) (hβ : 0 ≤ β) (hn : 1 ≤ n) (x : Euc d) :
    Real.log (wr13d_theta d s n β (HRS.Whole.withDensityReal ρ) x) =
      β * HRS.Whole.convMeasure (rieszKernel d s) (HRS.Whole.withDensityReal ρ) x +
        (HRS.Whole.insertionDefect d s (n + 1) β (HRS.Whole.withDensityReal ρ) x +
          -(β / ((n + 1 : ℕ) : ℝ)) * n *
            ∫ y, rieszKernel d s (x - y) ∂(HRS.Whole.cavityMarginal d s (n + 1) β
              (HRS.Whole.withDensityReal ρ))) -
        Real.log (wr13d_Z d s n β (HRS.Whole.withDensityReal ρ)) := by
  have hΦ := wr13d_Phi_pos hd hs0 hsd hρ hM hβ hn x
  have hZ := wr13d_Z_pos hd hs0 hsd hρ hM hβ n
  have h1 : Real.log (wr13d_theta d s n β (HRS.Whole.withDensityReal ρ) x) =
      β * HRS.Whole.convMeasure (rieszKernel d s) (HRS.Whole.withDensityReal ρ) x +
        Real.log (HRS.Whole.poleNormalizer d s (n + 1) β (HRS.Whole.withDensityReal ρ) x 1) -
          Real.log (wr13d_Z d s n β (HRS.Whole.withDensityReal ρ)) := by
    unfold wr13d_theta
    rw [Real.log_div (mul_pos (Real.exp_pos _) hΦ).ne' hZ.ne', Real.log_mul (Real.exp_pos _).ne' hΦ.ne',
      Real.log_exp]
  rw [h1]
  obtain ⟨-, hdef⟩ := wr13c2_insertionDefect_eq hd hs0 hsd hρ hM hβ (by omega : 2 ≤ n + 1) x
  have hP : Real.log (HRS.Whole.poleNormalizer d s (n + 1) β (HRS.Whole.withDensityReal ρ) x 1) =
      cgf (wr13c2_X d s (n + 1) β x) (HRS.Whole.cavityLaw d s (n + 1) β (HRS.Whole.withDensityReal ρ)) 1 := by
    have := congrFun (wr13c2_insertionPressure_eq (s := s) (n + 1) β (HRS.Whole.withDensityReal ρ) x) 1
    exact this
  rw [hP]
  have hX := wr13d_integral_X hd hs0 hsd hρ hM hβ hn x
  rw [hX] at hdef
  linarith

/-- The cavity marginal has a bounded density with respect to `μ` (the one-coordinate pole bound at `t = 0`). -/
theorem wr13d_cavMarg_le (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (βp M : ℝ) (hβp : 0 ≤ βp) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, 0 ≤ β → β ≤ βp → ∀ N : ℕ, 2 ≤ N →
        HRS.Whole.cavityMarginal d s N β (HRS.Whole.withDensityReal ρ) ≤
          ENNReal.ofReal C • HRS.Whole.withDensityReal ρ := by
  obtain ⟨C, hC1, hb⟩ := wr13a_pole_bundle hd hs0 hsd hβp M
  refine ⟨C, hC1, fun ρ hρ hM β hβ hββp N hN => ?_⟩
  have := wr13a_isProb_density hρ
  have hconv := wr13a_conv_le_density (by omega) hs0 hsd hρ hM
  obtain ⟨-, -, hpole⟩ := hb ρ hρ hM β hβ hββp N hN
  have h1 := (hpole 0 0 ⟨le_rfl, zero_le_one⟩).2.1
  rw [wr13c2_poleLaw_zero hs0 hconv hβ N 0] at h1
  unfold HRS.Whole.cavityMarginal
  refine h1.trans (le_of_eq ?_)
  rw [← withDensity_const]
  congr 1
  funext y
  simp

end Cavity

/-! ### 3. Event form of the cavity total variation -/

section Event

/-- Event-wise form of `wr13c2_cavity_tv`: for every measurable `A`,
`|π_N(A) - ν_n(A)| ≤ K √(δ_N/N)`. -/
theorem wr13d_event_bound (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {βm : ℝ} (hβm : 0 < βm)
    (βp M : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ n : ℕ, 1 ≤ n → ∀ A : Set (Euc d), MeasurableSet A →
        |(HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) (n + 1) β
            (HRS.Whole.withDensityReal ρ))).real A -
          (HRS.Whole.cavityMarginal d s (n + 1) β (HRS.Whole.withDensityReal ρ)).real A| ≤
          K * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
  obtain ⟨K, hK0, hK⟩ := wr13c2_cavity_tv hd hs0 hsd hβm βp M
  refine ⟨K, hK0, fun ρ hρ hM β hβ1 hββp n hn A hA => ?_⟩
  have hβ0 : 0 ≤ β := (hβm.trans_le hβ1).le
  have := wr13d_firstMarginal_isProb hd hs0 hsd hρ hM hβ0 hn
  have := wr13d_cavMarg_isProb hd hs0 hsd hρ hM hβ0 hn
  have h1 := HRS.External.Entropy.abs_le_tvDist
    (HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) (n + 1) β
      (HRS.Whole.withDensityReal ρ)))
    (HRS.Whole.cavityMarginal d s (n + 1) β (HRS.Whole.withDensityReal ρ)) hA
  exact h1.trans (hK ρ hρ hM β hβ1 hββp (n + 1) (by omega))

end Event

end HRS.MS.Wr
