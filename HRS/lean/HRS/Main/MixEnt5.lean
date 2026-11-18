import HRS.Main.MixEnt4

/-!
# MIXENT 5: the entropy scale `B_N ≤ C N δ_N` for the mixture preparation, in the form used by
`mixture_full_bounds` (assembly of M2, M3, M4)

TeX L6952-6962 (proof of Proposition 5.9 / Example 2.6: "for the product mixture the entropy
computation gives `B_N ≤ C N δ_N`").  The hypotheses are exactly those of `mixture_full_bounds`:
`b` smooth with `μ°(b) = 0`, `N ≥ 2`, `4 a₀² (⨆ x, |b x|)² ≤ N`.
-/

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- A smooth function is bounded by its supremum `⨆ x, |b x|` (a genuine sup: `b` is continuous on the
compact torus). -/
theorem mx_abs_le_iSup {b : Torus d → ℝ} (hb : Torus.IsSmooth b) (x : Torus d) :
    |b x| ≤ ⨆ y, |b y| := by
  have hbc : Continuous b := therm_continuous_of_smooth hb
  obtain ⟨B₀, hB₀⟩ := isCompact_univ.exists_bound_of_continuousOn hbc.continuousOn
  refine le_ciSup (f := fun y => |b y|) ⟨|B₀|, ?_⟩ x
  rintro _ ⟨y, rfl⟩
  have := hB₀ y (Set.mem_univ y)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_abs_self _)

/-- The hypothesis `4 a₀² (⨆|b|)² ≤ N` of `mixture_full_bounds` gives `|a₀ b| ≤ √N/2`. -/
theorem mx_hB_of_sup {b : Torus d → ℝ} (hb : Torus.IsSmooth b) {a₀ : ℝ} {N : ℕ}
    (h : 4 * a₀ ^ 2 * (⨆ x, |b x|) ^ 2 ≤ (N : ℝ)) (x : Torus d) :
    |a₀ * b x| ≤ Real.sqrt N / 2 := by
  have h1 : |b x| ≤ ⨆ y, |b y| := mx_abs_le_iSup hb x
  have h2 : |a₀| * |b x| ≤ |a₀| * ⨆ y, |b y| :=
    mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  rw [abs_mul]
  have h3 : (2 * (|a₀| * ⨆ y, |b y|)) ^ 2 ≤ N := by
    have : (2 * (|a₀| * ⨆ y, |b y|)) ^ 2 = 4 * a₀ ^ 2 * (⨆ y, |b y|) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]; ring
    linarith
  have h4 : 2 * (|a₀| * ⨆ y, |b y|) ≤ Real.sqrt N := Real.le_sqrt_of_sq_le h3
  linarith

/-- **M4 + M3 packaged** (the entropy input of `mixture_full_bounds`; TeX L6952-6962):
there is `C > 0` (chosen after `S, b, a₀`, before `N`) such that for every `N ≥ 2` with
`4 a₀² (⨆|b|)² ≤ N`, the mixture preparation has finite relative entropy against `Q_N^0` and
`B_N ≤ C N δ_N`. -/
theorem mx_B_mixture (S : PreparedData d) (b : Torus d → ℝ) (hb : Torus.IsSmooth b)
    (hb0 : pair S.μ0 b = 0) (a₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → 4 * a₀ ^ 2 * (⨆ x, |b x|) ^ 2 ≤ (N : ℝ) →
      relEntropy (mixturePrep S.μ0 b a₀ N) (S.refMeasure N 0) < ⊤ ∧
      S.B N (mixturePrep S.μ0 b a₀ N) ≤ C * ((N : ℝ) * deltaN d S.s N) := by
  have hbc : Continuous b := therm_continuous_of_smooth hb
  have hbm : Measurable b := hbc.measurable
  obtain ⟨C₁, hC₁0, hC₁⟩ := mx_B_le S
  set Jbb := mxJ (periodicRiesz d S.s) S.μ0 b b with hJbb
  set J11 := mxJ (periodicRiesz d S.s) S.μ0 (fun _ => 1) (fun _ => 1) with hJ11
  set E : ℝ := -(1 / 2) * J11 + (1 / 2) * a₀ ^ 2 * |Jbb| with hE
  set Mb : ℝ := ⨆ x, |b x| with hMb
  set K : ℝ := 2 + a₀ ^ 2 * ∫ x, b x ^ 2 ∂S.μ0 + S.β * |E| + C₁ with hK
  have hK0 : 0 < K := by
    have h1 : 0 ≤ a₀ ^ 2 * ∫ x, b x ^ 2 ∂S.μ0 :=
      mul_nonneg (sq_nonneg _) (integral_nonneg fun x => sq_nonneg _)
    have h2 : 0 ≤ S.β * |E| := mul_nonneg S.hβ.le (abs_nonneg _)
    rw [hK]; linarith
  refine ⟨K, hK0, fun N hN hsup => ?_⟩
  have hB := mx_hB_of_sup hb hsup
  have hbM : ∀ x, |b x| ≤ Mb := mx_abs_le_iSup hb
  obtain ⟨hint, hval⟩ := mx_energy_mix S hbm hbM hb0 a₀ (by omega : 1 ≤ N) hB
  have hle : ∫ X, mxW S N X ∂(mixturePrep S.μ0 b a₀ N) ≤ E := by
    rw [hval, hE]
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hc0 : 0 ≤ ((N : ℝ) - 1) / (2 * N) := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
      positivity
    have hc1 : ((N : ℝ) - 1) / (2 * N) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have : ((N : ℝ) - 1) / (2 * N) * Jbb ≤ (1 / 2) * |Jbb| := by
      calc ((N : ℝ) - 1) / (2 * N) * Jbb ≤ ((N : ℝ) - 1) / (2 * N) * |Jbb| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hc0
        _ ≤ (1 / 2) * |Jbb| := mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)
    nlinarith [sq_nonneg a₀]
  exact hC₁ b hbm Mb hbM hb0 a₀ N hN hB E hint hle

end Main

end HRS
