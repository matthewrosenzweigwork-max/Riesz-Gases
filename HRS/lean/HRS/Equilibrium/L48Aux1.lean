/-
# HRS.Equilibrium.L48Aux1 — Proposition 4.8 (`M:R:prop:conditional-expectation`), part 1

Conditional density of the `i`-th pole coordinate given the others (TeX `R:eq:conditional-density`).

## TeX inequality chain for Proposition 4.8 (source lines 4354-4386), and the Lean lemma of each step

Notation: `n = N-1`, `λ = β/N`, `P = critPole x t`, `a₀(y) = e^{-tλ g₊(x-y)}`, `f₁ = g₊(x-·) a₀`,
`B = ∫ a₀ dμ`, `F = ∫ f₁ dμ`, `v_Y = cavityField i Y`, `Z_Y = ∫ a₀ e^{-v_Y} dμ`,
`N_Y = ∫ f₁ e^{-v_Y} dμ`, `T₁ = N_Y / Z_Y`.

1. `T₁ = E_P[g₊(x - y_i) | y_j, j ≠ i]` a.e. (exact conditional density):
   `l48_condExp_eq` (via `l48_core`, the disintegration along coordinate `i`;
   `l48_poleExp_update_eq` is the `y_i`-dependence of the exponent).
2. Deterministic bounds: `Z_Y ≥ e^{-3βCg}`, `0 ≤ N_Y ≤ Cg e^{βCg}` (`Z_bounds`,
   `l48_Z_bounds`, `l48_Nn_bounds`), hence `0 ≤ T₁ ≤ C` (`l48_T_bound`): `E[T₁²] ≤ C`
   (third assertion), integrability (first assertion, `l48_integrable`).
3. Exact quotient identity (TeX `R:eq:quotient-identity`), in the form
   `B N_Y - F Z_Y = ∫ ψ v_Y dμ - ∫ ψ H(v_Y) dμ`, `ψ = F a₀ - B f₁`, `∫ ψ dμ = 0`,
   `H(v) = e^{-v} - 1 + v ≥ 0`: `l48_quotient` (`L48Aux4`), with `l48_BF_bounds`.
4. Taylor remainders `∫ f H(v_Y) dμ` in `L²(P)`: `integrated_taylor_remainder_proof`
   (Lemma 4.7), `‖·‖₂² ≤ C N^{-9/8}` (used in `l48_T_L2`, `L48Aux5`).
5. Linear term `∫ ψ v_Y dμ = λ ∑_{j≠i} Φ(y_j) - β μ(Φ)`, `Φ(z) = ∫ ψ(y) g₊(y-z) dμ(y)`
   (`l48_ell_ae`, `l48_int_psi_h`, `L48Aux3`); pole variance estimate (`l48_var_S`, from
   `pole_variance_clause`), `Φ ∈ L²(μ)` (`l48_psi_K`, from `critical_integrals` clause 6),
   pole first marginal against `L²(μ)` tests, `|E_P Φ(y_j) - μ(Φ)| ≤ C ‖Φ‖₂ δ_N`
   (`l48_mean_shift`, `L48Aux2`); total `l48_linear` (`L48Aux3`).
6. Assembly (`l48_T_L2` and `conditional_singular_observation_proof`, `L48Aux5`): clause 1 is
   `l48_integrable`, clause 2 is `l48_T_L2`, clause 3 is `l48_evariance_le`, clause 4 is `l48_T_bound`.
   (The proof only needs `t ∈ [0,1]`; the hypothesis `t > 0` of the statement is not used.)
-/
import HRS.Equilibrium.CavityPsi

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace L48

variable {d : ℕ} {s c : ℝ}

open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp

/-! ### Index bookkeeping and the exponent of the pole law as a function of coordinate `i` -/

theorem l48_split_erase {n : ℕ} (i : Fin n) (f : Fin n → ℝ) :
    ∑ a, f a = f i + ∑ a ∈ Finset.univ.erase i, f a :=
  (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm

theorem l48_sum_erase {m : ℕ} (i : Fin (m + 1)) (f : Fin (m + 1) → ℝ) :
    ∑ j ∈ Finset.univ.erase i, f j = ∑ j' : Fin m, f (i.succAbove j') := by
  have h := Fin.sum_univ_succAbove f i
  have h2 := Finset.add_sum_erase (Finset.univ : Finset (Fin (m + 1))) f (Finset.mem_univ i)
  linarith

/-- The exponent of the pole law, with coordinate `i` replaced by `y`: the `y`-dependent part is
`-tλ G(x-y) - (λ ∑_{j≠i} G(y - Y_j) - β (G*μ)(y))`, the rest does not depend on `y`. -/
theorem l48_poleExp_update_eq {G : Torus d → ℝ} (hG : ∀ z, G (-z) = G z) (μ : Measure (Torus d))
    {n : ℕ} (lam β t : ℝ) (x : Torus d) (i : Fin n) (Y : Config d n) (y : Torus d) :
    poleExp G μ n lam β t x (Function.update Y i y) =
      (-(t * lam) * G (x - y) -
          (lam * ∑ j ∈ Finset.univ.erase i, G (y - Y j) - β * convMeasure G μ y)) +
        (-(lam / 2) * (G 0 - n * G 0 +
            ∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase i, G (Y a - Y b)) +
          β * ∑ a ∈ Finset.univ.erase i, convMeasure G μ (Y a) -
            (t * lam) * ∑ a ∈ Finset.univ.erase i, G (x - Y a)) := by
  set Y' : Config d n := Function.update Y i y with hY'
  have h1 : ∀ a ∈ Finset.univ.erase i, Y' a = Y a := fun a ha =>
    Function.update_of_ne (Finset.ne_of_mem_erase ha) _ _
  have h2 : Y' i = y := Function.update_self _ _ _
  have hsw : ∀ a ∈ Finset.univ.erase i, G (Y a - y) = G (y - Y a) := fun a _ => by
    rw [← hG, neg_sub]
  have e1a : ∑ b, G (Y' i - Y' b) = G 0 + ∑ b ∈ Finset.univ.erase i, G (y - Y b) := by
    rw [l48_split_erase i (fun b => G (Y' i - Y' b))]
    simp only [h2, sub_self]
    congr 1
    exact Finset.sum_congr rfl fun b hb => by rw [h1 b hb]
  have e1b : ∀ a ∈ Finset.univ.erase i, ∑ b, G (Y' a - Y' b) =
      G (y - Y a) + ∑ b ∈ Finset.univ.erase i, G (Y a - Y b) := by
    intro a ha
    rw [l48_split_erase i (fun b => G (Y' a - Y' b))]
    simp only [h2, h1 a ha]
    rw [hsw a ha]
    congr 1
    exact Finset.sum_congr rfl fun b hb => by rw [h1 b hb]
  have e1 : ∑ a, ∑ b, G (Y' a - Y' b) = G 0 + 2 * ∑ b ∈ Finset.univ.erase i, G (y - Y b) +
      ∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase i, G (Y a - Y b) := by
    rw [l48_split_erase i (fun a => ∑ b, G (Y' a - Y' b)), e1a,
      Finset.sum_congr rfl e1b, Finset.sum_add_distrib]
    ring
  have e2 : ∑ a, convMeasure G μ (Y' a) =
      convMeasure G μ y + ∑ a ∈ Finset.univ.erase i, convMeasure G μ (Y a) := by
    rw [l48_split_erase i (fun a => convMeasure G μ (Y' a)), h2]
    congr 1
    exact Finset.sum_congr rfl fun b hb => by rw [h1 b hb]
  have e3 : ∑ a, G (x - Y' a) =
      G (x - y) + ∑ a ∈ Finset.univ.erase i, G (x - Y a) := by
    rw [l48_split_erase i (fun a => G (x - Y' a)), h2]
    congr 1
    exact Finset.sum_congr rfl fun b hb => by rw [h1 b hb]
  unfold poleExp
  rw [PoleCavityAux.pairSum_eq hG, e1, e2, e3]
  ring

theorem l48_poleExp_update_diff {G : Torus d → ℝ} (hG : ∀ z, G (-z) = G z) (μ : Measure (Torus d))
    {n : ℕ} (lam β t : ℝ) (x : Torus d) (i : Fin n) (Y : Config d n) (y y0 : Torus d) :
    poleExp G μ n lam β t x (Function.update Y i y) =
      poleExp G μ n lam β t x (Function.update Y i y0) +
        ((-(t * lam) * G (x - y) -
            (lam * ∑ j ∈ Finset.univ.erase i, G (y - Y j) - β * convMeasure G μ y)) -
          (-(t * lam) * G (x - y0) -
            (lam * ∑ j ∈ Finset.univ.erase i, G (y0 - Y j) - β * convMeasure G μ y0))) := by
  rw [l48_poleExp_update_eq hG μ lam β t x i Y y, l48_poleExp_update_eq hG μ lam β t x i Y y0]
  ring

/-! ### Integration over the product measure along coordinate `i` -/

theorem l48_lintegral_pi_insertNth {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    {n : ℕ} (i : Fin (n + 1)) (F : (Fin (n + 1) → E) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ X, F X ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
      ∫⁻ y, ∫⁻ r, F (Fin.insertNth i y r) ∂(Measure.pi fun _ : Fin n => μ) ∂μ := by
  have e := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i).symm
  have h1 := e.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) F
  rw [← h1]
  have hm : Measurable fun p : E × (Fin n → E) =>
      F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) i).symm p) :=
    hF.comp (MeasurableEquiv.measurable _)
  rw [lintegral_prod _ hm.aemeasurable]
  rfl

/-! ### The conditional numerator, denominator and `T₁` -/

/-- Exponent of the conditional density of coordinate `i` (TeX `R:eq:conditional-density`):
`a_Y(y) = -tλ g₊(x-y) - v_Y(y)`. -/
def l48_A (d : ℕ) (s c β : ℝ) (ρ : Torus d → ℝ) (N : ℕ) (x : Torus d) (t : ℝ) {n : ℕ} (i : Fin n)
    (Y : Config d n) (y : Torus d) : ℝ :=
  -(t * (β / N)) * gPlus d s c (x - y) - cavityField d s c β ρ N i Y y

/-- The conditional normaliser `Z_Y`. -/
def l48_Z (d : ℕ) (s c β : ℝ) (ρ : Torus d → ℝ) (N : ℕ) (x : Torus d) (t : ℝ) {n : ℕ} (i : Fin n)
    (Y : Config d n) : ℝ :=
  ∫ y, Real.exp (l48_A d s c β ρ N x t i Y y) ∂(withDensityReal ρ)

/-- The conditional numerator `N_Y`. -/
def l48_Nn (d : ℕ) (s c β : ℝ) (ρ : Torus d → ℝ) (N : ℕ) (x : Torus d) (t : ℝ) {n : ℕ} (i : Fin n)
    (Y : Config d n) : ℝ :=
  ∫ y, gPlus d s c (x - y) * Real.exp (l48_A d s c β ρ N x t i Y y) ∂(withDensityReal ρ)

/-- `T₁ = N_Y / Z_Y`, the conditional expectation of `g₊(x - y_i)` given the other coordinates. -/
def l48_T (d : ℕ) (s c β : ℝ) (ρ : Torus d → ℝ) (N : ℕ) (x : Torus d) (t : ℝ) {n : ℕ} (i : Fin n)
    (Y : Config d n) : ℝ :=
  l48_Nn d s c β ρ N x t i Y / l48_Z d s c β ρ N x t i Y

/-- The cavity field of the other particles `r` (indexed by `Fin m`). -/
def l48_k (d : ℕ) (s c β : ℝ) (ρ : Torus d → ℝ) (N : ℕ) {m : ℕ} (r : Fin m → Torus d)
    (y : Torus d) : ℝ :=
  (β / N) * ∑ j, gPlus d s c (y - r j) - β * convMeasure (gPlus d s c) (withDensityReal ρ) y

theorem l48_field_eq {m : ℕ} (N : ℕ) (β : ℝ) (ρ : Torus d → ℝ) (i : Fin (m + 1)) (Y : Config d (m + 1))
    (y : Torus d) :
    cavityField d s c β ρ N i Y y = l48_k d s c β ρ N (Fin.removeNth i Y) y := by
  unfold cavityField l48_k
  rw [l48_sum_erase i (fun j => gPlus d s c (y - Y j))]
  rfl

/-- `Z` as a function of the other particles `r`. -/
def l48_Zr (d : ℕ) (s c β : ℝ) (ρ : Torus d → ℝ) (N : ℕ) (x : Torus d) (t : ℝ) {m : ℕ}
    (r : Fin m → Torus d) : ℝ :=
  ∫ y, Real.exp (-(t * (β / N)) * gPlus d s c (x - y) - l48_k d s c β ρ N r y)
    ∂(withDensityReal ρ)

/-- `N` as a function of the other particles `r`. -/
def l48_Nr (d : ℕ) (s c β : ℝ) (ρ : Torus d → ℝ) (N : ℕ) (x : Torus d) (t : ℝ) {m : ℕ}
    (r : Fin m → Torus d) : ℝ :=
  ∫ y, gPlus d s c (x - y) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y) - l48_k d s c β ρ N r y)
    ∂(withDensityReal ρ)

theorem l48_Z_eq {m : ℕ} (N : ℕ) (β : ℝ) (ρ : Torus d → ℝ) (x : Torus d) (t : ℝ) (i : Fin (m + 1))
    (Y : Config d (m + 1)) :
    l48_Z d s c β ρ N x t i Y = l48_Zr d s c β ρ N x t (Fin.removeNth i Y) := by
  unfold l48_Z l48_Zr l48_A
  simp only [l48_field_eq (s := s) (c := c) N β ρ i Y]

theorem l48_Nn_eq {m : ℕ} (N : ℕ) (β : ℝ) (ρ : Torus d → ℝ) (x : Torus d) (t : ℝ) (i : Fin (m + 1))
    (Y : Config d (m + 1)) :
    l48_Nn d s c β ρ N x t i Y = l48_Nr d s c β ρ N x t (Fin.removeNth i Y) := by
  unfold l48_Nn l48_Nr l48_A
  simp only [l48_field_eq (s := s) (c := c) N β ρ i Y]

/-- `T₁` as a function of the other particles. -/
def l48_Tr (d : ℕ) (s c β : ℝ) (ρ : Torus d → ℝ) (N : ℕ) (x : Torus d) (t : ℝ) {m : ℕ}
    (r : Fin m → Torus d) : ℝ :=
  l48_Nr d s c β ρ N x t r / l48_Zr d s c β ρ N x t r

theorem l48_T_eq {m : ℕ} (N : ℕ) (β : ℝ) (ρ : Torus d → ℝ) (x : Torus d) (t : ℝ) (i : Fin (m + 1))
    (Y : Config d (m + 1)) :
    l48_T d s c β ρ N x t i Y = l48_Tr d s c β ρ N x t (Fin.removeNth i Y) := by
  unfold l48_T l48_Tr
  rw [l48_Nn_eq, l48_Z_eq]

section Bounds

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)

include hd hcrit hβ hρ hc

/-- Deterministic bounds on `Z_Y` and `N_Y` (TeX: `0 < c ≤ Z_Y ≤ C`). -/
theorem l48_bounds {Cg : ℝ} (hCg : ∀ y, 0 ≤ convMeasure (gPlus d s c) (withDensityReal ρ) y ∧
      convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ Cg)
    {N : ℕ} (hN : 2 ≤ N) (x : Torus d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : Fin (N - 1))
    (Y : Config d (N - 1)) :
    Real.exp (-(3 * (β * Cg))) ≤ l48_Z d s c β ρ N x t i Y ∧
      l48_Z d s c β ρ N x t i Y ≤ Real.exp (β * Cg) ∧
      0 ≤ l48_Nn d s c β ρ N x t i Y ∧
      l48_Nn d s c β ρ N x t i Y ≤ Real.exp (β * Cg) * Cg := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  obtain ⟨hup, hai, -, -, hlow, hhigh⟩ :=
    Z_bounds hd hcrit hβ hρ hc hCg hN x ht Y i (l48_A d s c β ρ N x t i Y) (fun y' => rfl)
  refine ⟨hlow, hhigh, ?_, ?_⟩
  · exact integral_nonneg fun y => mul_nonneg (show 0 ≤ gPlus d s c (x - y) from hc _) (Real.exp_pos _).le
  · have hGi := gPlus_int hd hcrit hβ hρ hc hs0 hsd x
    have hamm : Measurable (l48_A d s c β ρ N x t i Y) := by
      have : l48_A d s c β ρ N x t i Y = fun y' => -(t * (β / N)) * gPlus d s c (x - y') -
          cavityField d s c β ρ N i Y y' := rfl
      rw [this]
      exact ((hgm.comp (measurable_const.sub measurable_id)).const_mul _).sub
        (measurable_field_slice hd hcrit hβ hρ hc N i Y)
    have hexi : Integrable (fun y => gPlus d s c (x - y) * Real.exp (l48_A d s c β ρ N x t i Y y))
        (withDensityReal ρ) := by
      refine Integrable.mono' (hGi.mul_const (Real.exp (β * Cg)))
        ((hgm.comp (measurable_const.sub measurable_id)).mul
          (Real.measurable_exp.comp hamm)).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
      have hG0 : 0 ≤ gPlus d s c (x - y) := hc _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hG0 (Real.exp_pos _).le)]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hup y)) hG0
    calc l48_Nn d s c β ρ N x t i Y
        ≤ ∫ y, gPlus d s c (x - y) * Real.exp (β * Cg) ∂(withDensityReal ρ) :=
          integral_mono hexi (hGi.mul_const _) fun y =>
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hup y)) (show 0 ≤ gPlus d s c (x - y) from hc _)
      _ = Real.exp (β * Cg) * convMeasure (gPlus d s c) (withDensityReal ρ) x := by
          rw [integral_mul_const]; unfold convMeasure; ring
      _ ≤ Real.exp (β * Cg) * Cg :=
          mul_le_mul_of_nonneg_left (hCg x).2 (Real.exp_pos _).le

theorem l48_T_bound {Cg : ℝ} (hCg : ∀ y, 0 ≤ convMeasure (gPlus d s c) (withDensityReal ρ) y ∧
      convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ Cg)
    {N : ℕ} (hN : 2 ≤ N) (x : Torus d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : Fin (N - 1))
    (Y : Config d (N - 1)) :
    0 ≤ l48_T d s c β ρ N x t i Y ∧
      l48_T d s c β ρ N x t i Y ≤ Real.exp (β * Cg) * Cg * Real.exp (3 * (β * Cg)) := by
  obtain ⟨h1, h2, h3, h4⟩ := l48_bounds hd hcrit hβ hρ hc hCg hN x ht i Y
  have hZ : 0 < l48_Z d s c β ρ N x t i Y := lt_of_lt_of_le (Real.exp_pos _) h1
  refine ⟨div_nonneg h3 hZ.le, ?_⟩
  unfold l48_T
  rw [div_le_iff₀ hZ]
  have hCg0 : 0 ≤ Cg := (hCg 0).1.trans (hCg 0).2
  calc l48_Nn d s c β ρ N x t i Y ≤ Real.exp (β * Cg) * Cg := h4
    _ = Real.exp (β * Cg) * Cg * Real.exp (3 * (β * Cg)) * Real.exp (-(3 * (β * Cg))) := by
        rw [mul_assoc _ (Real.exp (3 * (β * Cg))) , ← Real.exp_add]; simp
    _ ≤ Real.exp (β * Cg) * Cg * Real.exp (3 * (β * Cg)) * l48_Z d s c β ρ N x t i Y :=
        mul_le_mul_of_nonneg_left h1 (by positivity)

end Bounds

section Core

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)

include hd hcrit hβ hρ hc

theorem l48_meas_kx {m : ℕ} (N : ℕ) (x : Torus d) :
    Measurable fun r : Fin m → Torus d => l48_k d s c β ρ N r x := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  unfold l48_k
  exact ((Finset.measurable_sum _ fun j _ => hgm.comp (measurable_const.sub
      (measurable_pi_apply j))).const_mul _).sub measurable_const

theorem l48_meas_A0_joint {m : ℕ} (N : ℕ) (x : Torus d) (t : ℝ) :
    Measurable fun q : Torus d × (Fin m → Torus d) =>
      -(t * (β / N)) * gPlus d s c (x - q.1) - l48_k d s c β ρ N q.2 q.1 := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  unfold l48_k
  exact ((hgm.comp (measurable_const.sub measurable_fst)).const_mul _).sub
    (((Finset.measurable_sum _ fun j _ => hgm.comp (measurable_fst.sub
      ((measurable_pi_apply j).comp measurable_snd))).const_mul _).sub
      (((measurable_convMeasure hgm _).comp measurable_fst).const_mul β))

theorem l48_meas_A0_slice {m : ℕ} (N : ℕ) (x : Torus d) (t : ℝ) (r : Fin m → Torus d) :
    Measurable fun y : Torus d =>
      -(t * (β / N)) * gPlus d s c (x - y) - l48_k d s c β ρ N r y := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  unfold l48_k
  exact ((hgm.comp (measurable_const.sub measurable_id)).const_mul _).sub
    (((Finset.measurable_sum _ fun j _ => hgm.comp (measurable_id.sub
      measurable_const)).const_mul _).sub
      ((measurable_convMeasure hgm _).const_mul β))

theorem l48_A0_le {Cg : ℝ} (hCg : ∀ y, 0 ≤ convMeasure (gPlus d s c) (withDensityReal ρ) y ∧
      convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ Cg)
    {m : ℕ} (x : Torus d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (r : Fin m → Torus d) (y : Torus d) :
    -(t * (β / ((m + 2 : ℕ) : ℝ))) * gPlus d s c (x - y) - l48_k d s c β ρ (m + 2) r y ≤ β * Cg := by
  have hN0 : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  have hlam : 0 ≤ β / ((m + 2 : ℕ) : ℝ) := by positivity
  have h1 : 0 ≤ (t * (β / ((m + 2 : ℕ) : ℝ))) * gPlus d s c (x - y) :=
    mul_nonneg (mul_nonneg ht.1 hlam) (hc _)
  have h2 : 0 ≤ (β / ((m + 2 : ℕ) : ℝ)) * ∑ j, gPlus d s c (y - r j) :=
    mul_nonneg hlam (Finset.sum_nonneg fun j _ => hc _)
  have h3 : β * convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ β * Cg :=
    mul_le_mul_of_nonneg_left (hCg y).2 hβ.le
  unfold l48_k
  nlinarith

/-- Bounds for `Z` and `N` as functions of the other particles. -/
theorem l48_r_bounds {Cg : ℝ} (hCg : ∀ y, 0 ≤ convMeasure (gPlus d s c) (withDensityReal ρ) y ∧
      convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ Cg)
    {m : ℕ} (x : Torus d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (r : Fin m → Torus d) :
    Real.exp (-(3 * (β * Cg))) ≤ l48_Zr d s c β ρ (m + 2) x t r ∧
      l48_Zr d s c β ρ (m + 2) x t r ≤ Real.exp (β * Cg) ∧
      0 ≤ l48_Nr d s c β ρ (m + 2) x t r ∧
      l48_Nr d s c β ρ (m + 2) x t r ≤ Real.exp (β * Cg) * Cg := by
  have i0 : Fin (m + 1) := ⟨0, by omega⟩
  have hb := l48_bounds hd hcrit hβ hρ hc hCg (N := m + 2) (by omega) x ht i0
    (Fin.insertNth i0 x r)
  have e1 : l48_Zr d s c β ρ (m + 2) x t r =
      l48_Z d s c β ρ (m + 2) x t i0 (Fin.insertNth i0 x r) := by
    rw [l48_Z_eq]; simp
  have e2 : l48_Nr d s c β ρ (m + 2) x t r =
      l48_Nn d s c β ρ (m + 2) x t i0 (Fin.insertNth i0 x r) := by
    rw [l48_Nn_eq]; simp
  rw [e1, e2]
  exact hb

end Core

/-- Part of the pole exponent depending only on the other particles `r` (reference point `x`). -/
def l48_E (d : ℕ) (s c β : ℝ) (ρ : Torus d → ℝ) (N : ℕ) (x : Torus d) (t : ℝ) {m : ℕ}
    (i : Fin (m + 1)) (r : Fin m → Torus d) : ℝ :=
  poleExp (gPlus d s c) (withDensityReal ρ) (m + 1) (β / N) β t x (Fin.insertNth i x r) -
    (-(t * (β / N)) * gPlus d s c (x - x) - l48_k d s c β ρ N r x)

section Core2

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)

include hd hcrit hβ hρ hc

theorem l48_poleExp_insertNth {m : ℕ} (N : ℕ) (x : Torus d) (t : ℝ) (i : Fin (m + 1))
    (y : Torus d) (r : Fin m → Torus d) :
    poleExp (gPlus d s c) (withDensityReal ρ) (m + 1) (β / N) β t x (Fin.insertNth i y r) =
      l48_E d s c β ρ N x t i r +
        (-(t * (β / N)) * gPlus d s c (x - y) - l48_k d s c β ρ N r y) := by
  have hGe : ∀ z, gPlus d s c (-z) = gPlus d s c z := gPlus_even hd hcrit hβ hρ hc
  have h := l48_poleExp_update_diff hGe (withDensityReal ρ) (β / N) β t x i (Fin.insertNth i x r) y x
  rw [Fin.update_insertNth, Fin.update_insertNth] at h
  have hs : ∀ y' : Torus d, ∑ j ∈ Finset.univ.erase i, gPlus d s c (y' - (Fin.insertNth i x r : Fin (m + 1) → Torus d) j) =
      ∑ j', gPlus d s c (y' - r j') := by
    intro y'
    rw [l48_sum_erase i (fun j => gPlus d s c (y' - (Fin.insertNth i x r : Fin (m + 1) → Torus d) j))]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Fin.insertNth_apply_succAbove]
  rw [hs, hs] at h
  rw [h]
  unfold l48_E l48_k
  ring

theorem l48_core_aux {m : ℕ} (N : ℕ) (x : Torus d) (t : ℝ) (i : Fin (m + 1))
    (u : Torus d → ℝ≥0∞) (hu : Measurable u) (v : (Fin m → Torus d) → ℝ≥0∞) (hv : Measurable v) :
    ∫⁻ Y, ENNReal.ofReal (Real.exp (poleExp (gPlus d s c) (withDensityReal ρ) (m + 1) (β / N) β t x Y)) *
        (v (Fin.removeNth i Y) * u (Y i)) ∂(Measure.pi fun _ : Fin (m + 1) => withDensityReal ρ) =
      ∫⁻ r, (ENNReal.ofReal (Real.exp (l48_E d s c β ρ N x t i r)) * v r) *
        ∫⁻ y, ENNReal.ofReal (Real.exp (-(t * (β / N)) * gPlus d s c (x - y) -
          l48_k d s c β ρ N r y)) * u y ∂(withDensityReal ρ)
        ∂(Measure.pi fun _ : Fin m => withDensityReal ρ) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  have hWm : Measurable (poleExp (gPlus d s c) (withDensityReal ρ) (m + 1) (β / N) β t x) :=
    measurable_poleExp hgm (withDensityReal ρ) _ _ β t x
  have hrem : Measurable fun Y : Config d (m + 1) => Fin.removeNth i Y :=
    measurable_pi_iff.2 fun j => measurable_pi_apply _
  have hF : Measurable fun Y : Config d (m + 1) =>
      ENNReal.ofReal (Real.exp (poleExp (gPlus d s c) (withDensityReal ρ) (m + 1) (β / N) β t x Y)) *
        (v (Fin.removeNth i Y) * u (Y i)) :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hWm)).mul
      ((hv.comp hrem).mul (hu.comp (measurable_pi_apply i)))
  rw [l48_lintegral_pi_insertNth (withDensityReal ρ) i _ hF]
  simp only [Fin.removeNth_insertNth, Fin.insertNth_apply_same]
  simp_rw [l48_poleExp_insertNth hd hcrit hβ hρ hc N x t i]
  -- joint measurability
  have hins : Measurable fun p : Torus d × (Fin m → Torus d) => (Fin.insertNth i p.1 p.2 : Fin (m + 1) → Torus d) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Torus d) i).symm.measurable
  have hk : Measurable fun r : Fin m → Torus d => l48_k d s c β ρ N r x :=
    l48_meas_kx hd hcrit hβ hρ hc N x
  have hEm : Measurable fun r : Fin m → Torus d => l48_E d s c β ρ N x t i r := by
    unfold l48_E
    refine (hWm.comp (hins.comp (measurable_const.prodMk measurable_id))).sub ?_
    exact measurable_const.sub hk
  have hA0 : Measurable fun q : Torus d × (Fin m → Torus d) =>
      -(t * (β / N)) * gPlus d s c (x - q.1) - l48_k d s c β ρ N q.2 q.1 :=
    l48_meas_A0_joint hd hcrit hβ hρ hc N x t
  have hjoint : Measurable fun q : Torus d × (Fin m → Torus d) =>
      ENNReal.ofReal (Real.exp (l48_E d s c β ρ N x t i q.2 +
        (-(t * (β / N)) * gPlus d s c (x - q.1) - l48_k d s c β ρ N q.2 q.1))) *
        (v q.2 * u q.1) := by
    refine (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)).mul
      ((hv.comp measurable_snd).mul (hu.comp measurable_fst))
    exact (hEm.comp measurable_snd).add hA0
  rw [lintegral_lintegral_swap hjoint.aemeasurable]
  refine lintegral_congr fun r => ?_
  have hyr : Measurable fun y : Torus d => ENNReal.ofReal (Real.exp (-(t * (β / N)) * gPlus d s c (x - y) -
      l48_k d s c β ρ N r y)) * u y :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (l48_meas_A0_slice hd hcrit hβ hρ hc N x t r))).mul hu
  rw [← lintegral_const_mul _ hyr]
  refine lintegral_congr fun y => ?_
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  ring

theorem l48_meas_A0_rj {m : ℕ} (N : ℕ) (x : Torus d) (t : ℝ) :
    Measurable fun q : (Fin m → Torus d) × Torus d =>
      -(t * (β / N)) * gPlus d s c (x - q.2) - l48_k d s c β ρ N q.1 q.2 := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  unfold l48_k
  exact ((hgm.comp (measurable_const.sub measurable_snd)).const_mul _).sub
    (((Finset.measurable_sum _ fun j _ => hgm.comp (measurable_snd.sub
      ((measurable_pi_apply j).comp measurable_fst))).const_mul _).sub
      (((measurable_convMeasure hgm _).comp measurable_snd).const_mul β))

theorem l48_meas_Zr {m : ℕ} (N : ℕ) (x : Torus d) (t : ℝ) :
    Measurable (fun r : Fin m → Torus d => l48_Zr d s c β ρ N x t r) := by
  have hμ := isProbabilityMeasure_mu hρ
  unfold l48_Zr
  have h : StronglyMeasurable fun q : (Fin m → Torus d) × Torus d =>
      Real.exp (-(t * (β / N)) * gPlus d s c (x - q.2) - l48_k d s c β ρ N q.1 q.2) :=
    (Real.measurable_exp.comp (l48_meas_A0_rj hd hcrit hβ hρ hc N x t)).stronglyMeasurable
  exact (h.integral_prod_right' (ν := withDensityReal ρ)).measurable

theorem l48_meas_Nr {m : ℕ} (N : ℕ) (x : Torus d) (t : ℝ) :
    Measurable (fun r : Fin m → Torus d => l48_Nr d s c β ρ N x t r) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  unfold l48_Nr
  have h : StronglyMeasurable fun q : (Fin m → Torus d) × Torus d =>
      gPlus d s c (x - q.2) * Real.exp (-(t * (β / N)) * gPlus d s c (x - q.2) -
        l48_k d s c β ρ N q.1 q.2) :=
    ((hgm.comp (measurable_const.sub measurable_snd)).mul
      (Real.measurable_exp.comp (l48_meas_A0_rj hd hcrit hβ hρ hc N x t))).stronglyMeasurable
  exact (h.integral_prod_right' (ν := withDensityReal ρ)).measurable

/-- Disintegration along coordinate `i`: for every function `χ` of the other particles,
`E[χ g₊(x - y_i)] = E[χ T₁]` under the pole law. -/
theorem l48_core {m : ℕ} (x : Torus d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : Fin (m + 1))
    (P : Measure (Config d (m + 1))) (hPdef : P = critPole d s c β ρ (m + 2) x t)
    (χ : (Fin m → Torus d) → ℝ≥0∞) (hχ : Measurable χ) :
    ∫⁻ Y, χ (Fin.removeNth i Y) * ENNReal.ofReal (gPlus d s c (x - Y i)) ∂P =
      ∫⁻ Y, χ (Fin.removeNth i Y) * ENNReal.ofReal (l48_T d s c β ρ (m + 2) x t i Y) ∂P := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Cg, hCg0, hCg⟩ := conv_gPlus hd hs0 hsd hρ hc
  have hgm := measurable_gPlus hd hs0 hsd c
  have hN : 2 ≤ m + 2 := by omega
  have hP : P =
      tiltMeasure (Measure.pi fun _ : Fin (m + 1) => withDensityReal ρ)
        (poleExp (gPlus d s c) (withDensityReal ρ) (m + 1) (β / ((m + 2 : ℕ) : ℝ)) β t x) := by
    rw [hPdef]
    exact critPole_single hd hs0 hsd β hβ hρ hc hN x ht.1
  have hWm := measurable_poleExp hgm (withDensityReal ρ) (m + 1) (β / ((m + 2 : ℕ) : ℝ)) β t x
  have hrem : Measurable fun Y : Config d (m + 1) => Fin.removeNth i Y :=
    measurable_pi_iff.2 fun j => measurable_pi_apply _
  have hem : Measurable fun Y : Config d (m + 1) =>
      ENNReal.ofReal (Real.exp (poleExp (gPlus d s c) (withDensityReal ρ) (m + 1)
        (β / ((m + 2 : ℕ) : ℝ)) β t x Y)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hWm)
  set Tr : (Fin m → Torus d) → ℝ := fun r =>
    l48_Nr d s c β ρ (m + 2) x t r / l48_Zr d s c β ρ (m + 2) x t r with hTr
  have hTrm : Measurable Tr :=
    (l48_meas_Nr hd hcrit hβ hρ hc (m + 2) x t).div (l48_meas_Zr hd hcrit hβ hρ hc (m + 2) x t)
  have hT : ∀ Y : Config d (m + 1), l48_T d s c β ρ (m + 2) x t i Y = Tr (Fin.removeNth i Y) := by
    intro Y
    unfold l48_T
    rw [l48_Nn_eq, l48_Z_eq]
  simp_rw [hT]
  rw [hP]
  unfold tiltMeasure
  rw [lintegral_smul_measure, lintegral_smul_measure]
  congr 1
  have hF1 : Measurable fun Y : Config d (m + 1) =>
      χ (Fin.removeNth i Y) * ENNReal.ofReal (gPlus d s c (x - Y i)) :=
    (hχ.comp hrem).mul (ENNReal.measurable_ofReal.comp
      (hgm.comp (measurable_const.sub (measurable_pi_apply i))))
  have hF2 : Measurable fun Y : Config d (m + 1) =>
      χ (Fin.removeNth i Y) * ENNReal.ofReal (Tr (Fin.removeNth i Y)) :=
    (hχ.comp hrem).mul (ENNReal.measurable_ofReal.comp (hTrm.comp hrem))
  rw [lintegral_withDensity_eq_lintegral_mul _ hem hF1,
    lintegral_withDensity_eq_lintegral_mul _ hem hF2]
  simp only [Pi.mul_apply]
  have hu1 : Measurable fun y : Torus d => ENNReal.ofReal (gPlus d s c (x - y)) :=
    ENNReal.measurable_ofReal.comp (hgm.comp (measurable_const.sub measurable_id))
  have e1 := l48_core_aux hd hcrit hβ hρ hc (m := m) (m + 2) x t i
    (fun y => ENNReal.ofReal (gPlus d s c (x - y))) hu1 χ hχ
  have e2 := l48_core_aux hd hcrit hβ hρ hc (m := m) (m + 2) x t i
    (fun _ => 1) measurable_const (fun r => χ r * ENNReal.ofReal (Tr r))
    (hχ.mul (ENNReal.measurable_ofReal.comp hTrm))
  simp only [mul_assoc, mul_one] at e1 e2 ⊢
  rw [e1, e2]
  refine lintegral_congr fun r => ?_
  -- the inner integrals
  have hup := l48_A0_le hd hcrit hβ hρ hc hCg (m := m) x ht r
  have hslice := l48_meas_A0_slice hd hcrit hβ hρ hc (m + 2) x t r
  have hGi := gPlus_int hd hcrit hβ hρ hc hs0 hsd x
  have hZi : Integrable (fun y => Real.exp (-(t * (β / ((m + 2 : ℕ) : ℝ))) * gPlus d s c (x - y) -
      l48_k d s c β ρ (m + 2) r y)) (withDensityReal ρ) := by
    refine Integrable.mono' (integrable_const (Real.exp (β * Cg)))
      (Real.measurable_exp.comp hslice).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (hup y)
  have hNi : Integrable (fun y => gPlus d s c (x - y) *
      Real.exp (-(t * (β / ((m + 2 : ℕ) : ℝ))) * gPlus d s c (x - y) - l48_k d s c β ρ (m + 2) r y))
      (withDensityReal ρ) := by
    refine Integrable.mono' (hGi.mul_const (Real.exp (β * Cg)))
      ((hgm.comp (measurable_const.sub measurable_id)).mul
        (Real.measurable_exp.comp hslice)).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    have hG0 : 0 ≤ gPlus d s c (x - y) := hc _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hG0 (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hup y)) hG0
  have hZ : ∫⁻ y, ENNReal.ofReal (Real.exp (-(t * (β / ((m + 2 : ℕ) : ℝ))) * gPlus d s c (x - y) -
      l48_k d s c β ρ (m + 2) r y)) ∂(withDensityReal ρ) =
      ENNReal.ofReal (l48_Zr d s c β ρ (m + 2) x t r) := by
    unfold l48_Zr
    rw [ofReal_integral_eq_lintegral_ofReal hZi (Eventually.of_forall fun y => (Real.exp_pos _).le)]
  have hN' : ∫⁻ y, ENNReal.ofReal (Real.exp (-(t * (β / ((m + 2 : ℕ) : ℝ))) * gPlus d s c (x - y) -
      l48_k d s c β ρ (m + 2) r y)) * ENNReal.ofReal (gPlus d s c (x - y)) ∂(withDensityReal ρ) =
      ENNReal.ofReal (l48_Nr d s c β ρ (m + 2) x t r) := by
    unfold l48_Nr
    rw [ofReal_integral_eq_lintegral_ofReal hNi
      (Eventually.of_forall fun y => mul_nonneg (show 0 ≤ gPlus d s c (x - y) from hc _) (Real.exp_pos _).le)]
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_mul (show 0 ≤ gPlus d s c (x - y) from hc _), mul_comm]
  have hb := l48_r_bounds hd hcrit hβ hρ hc hCg (m := m) x ht r
  have hZpos : 0 < l48_Zr d s c β ρ (m + 2) x t r := lt_of_lt_of_le (Real.exp_pos _) hb.1
  rw [hZ, hN']
  have : ENNReal.ofReal (Tr r) * ENNReal.ofReal (l48_Zr d s c β ρ (m + 2) x t r) =
      ENNReal.ofReal (l48_Nr d s c β ρ (m + 2) x t r) := by
    rw [← ENNReal.ofReal_mul (div_nonneg hb.2.2.1 hZpos.le)]
    congr 1
    show l48_Nr d s c β ρ (m + 2) x t r / l48_Zr d s c β ρ (m + 2) x t r *
      l48_Zr d s c β ρ (m + 2) x t r = l48_Nr d s c β ρ (m + 2) x t r
    field_simp
  rw [← this]

theorem l48_meas_Tr {m : ℕ} (N : ℕ) (x : Torus d) (t : ℝ) :
    Measurable (fun r : Fin m → Torus d => l48_Tr d s c β ρ N x t r) :=
  (l48_meas_Nr hd hcrit hβ hρ hc N x t).div (l48_meas_Zr hd hcrit hβ hρ hc N x t)

theorem l48_integrable {N : ℕ} (hN : 2 ≤ N) (x : Torus d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin (N - 1)) :
    Integrable (fun Y : Config d (N - 1) => gPlus d s c (x - Y i)) (critPole d s c β ρ N x t) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  obtain ⟨M1, hM1, hM⟩ := pole_marg_le hd hs0 hsd hβ hρ
  have hmap := (hM N hN x t ht).2 i
  rw [← critPole_eq_poleLaw (c := c) hd hs0 hsd β hβ hρ hN x t] at hmap
  have hGi := gPlus_int hd hcrit hβ hρ hc hs0 hsd x
  have hmeas : Measurable fun Y : Config d (N - 1) => gPlus d s c (x - Y i) :=
    hgm.comp (measurable_const.sub (measurable_pi_apply i))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hnn : ∀ Y : Config d (N - 1), ‖gPlus d s c (x - Y i)‖ₑ = ENNReal.ofReal (gPlus d s c (x - Y i)) :=
    fun Y => by
      have hG0 : 0 ≤ gPlus d s c (x - Y i) := hc _
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hG0]
  unfold HasFiniteIntegral
  simp_rw [hnn]
  have hfin : ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) ∂(withDensityReal ρ) < ⊤ := by
    have := hGi.hasFiniteIntegral
    unfold HasFiniteIntegral at this
    refine lt_of_le_of_lt (le_of_eq ?_) this
    refine lintegral_congr fun y => ?_
    have hG0 : 0 ≤ gPlus d s c (x - y) := hc _
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hG0]
  calc ∫⁻ Y, ENNReal.ofReal (gPlus d s c (x - Y i)) ∂(critPole d s c β ρ N x t)
      = ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) ∂((critPole d s c β ρ N x t).map
          (fun Y : Config d (N - 1) => Y i)) :=
        (lintegral_map (ENNReal.measurable_ofReal.comp (hgm.comp (measurable_const.sub measurable_id)))
          (measurable_pi_apply i)).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) ∂(ENNReal.ofReal M1 • withDensityReal ρ) :=
        lintegral_mono' hmap le_rfl
    _ = ENNReal.ofReal M1 * ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) ∂(withDensityReal ρ) :=
        lintegral_smul_measure _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

set_option maxHeartbeats 800000 in
theorem l48_condExp_eq_m {m : ℕ} (x : Torus d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin (m + 1)) (P : Measure (Config d (m + 1))) (hPdef : P = critPole d s c β ρ (m + 2) x t) :
    P[fun Y' : Config d (m + 1) => gPlus d s c (x - Y' i) | othersSigma i]
      =ᵐ[P] fun Y => l48_T d s c β ρ (m + 2) x t i Y := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Cg, hCg0, hCg⟩ := conv_gPlus hd hs0 hsd hρ hc
  have hgm := measurable_gPlus hd hs0 hsd c
  have hN : 2 ≤ m + 2 := by omega
  have hlam : 0 ≤ β / ((m + 2 : ℕ) : ℝ) := by positivity
  have hPprob : IsProbabilityMeasure P := by
    rw [hPdef, critPole_eq_poleLaw (c := c) hd hs0 hsd β hβ hρ hN x t]
    exact pole_isProb hd hs0 hsd β hρ (m + 2 - 1) (β / ((m + 2 : ℕ) : ℝ)) hlam x t ht.1
  have hf' : Integrable (fun Y : Config d (m + 1) => gPlus d s c (x - Y i)) P := by
    rw [hPdef]; exact l48_integrable hd hcrit hβ hρ hc hN x ht i
  have hbd' : ∀ Y : Config d (m + 1), 0 ≤ l48_T d s c β ρ (m + 2) x t i Y ∧
      l48_T d s c β ρ (m + 2) x t i Y ≤ Real.exp (β * Cg) * Cg * Real.exp (3 * (β * Cg)) :=
    fun Y => l48_T_bound hd hcrit hβ hρ hc hCg hN x ht i Y
  have hm : othersSigma (d := d) i ≤ MeasurableSpace.pi :=
    (measurable_pi_iff.2 fun j => measurable_pi_apply _ :
      Measurable (fun (Y : Config d (m + 1)) (j : {j // j ≠ i}) => Y j)).comap_le
  have hrem : Measurable fun Y : Config d (m + 1) => Fin.removeNth i Y :=
    measurable_pi_iff.2 fun j => measurable_pi_apply _
  have hTr := l48_meas_Tr hd hcrit hβ hρ hc (m := m) (m + 2) x t
  have hTeq : (fun Y : Config d (m + 1) => l48_T d s c β ρ (m + 2) x t i Y) =
      fun Y => l48_Tr d s c β ρ (m + 2) x t (Fin.removeNth i Y) :=
    funext fun Y => l48_T_eq (s := s) (c := c) (m := m) (m + 2) β ρ x t i Y
  have hTm : Measurable fun Y : Config d (m + 1) => l48_T d s c β ρ (m + 2) x t i Y := by
    rw [hTeq]
    exact hTr.comp hrem
  have hTi : Integrable (fun Y : Config d (m + 1) => l48_T d s c β ρ (m + 2) x t i Y) P :=
    Integrable.of_bound hTm.aestronglyMeasurable (Real.exp (β * Cg) * Cg * Real.exp (3 * (β * Cg)))
      (Eventually.of_forall fun Y => by
        obtain ⟨h1, h2⟩ := hbd' Y
        rw [Real.norm_eq_abs, abs_of_nonneg h1]; exact h2)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hf' (fun S _ _ => hTi.integrableOn) ?_ ?_).symm
  · -- the set-integral identity
    intro S hS hSfin
    obtain ⟨A', hA', rfl⟩ := (MeasurableSpace.measurableSet_comap).1 hS
    have hSm : MeasurableSet ((fun (Y : Config d (m + 1)) (j : {j // j ≠ i}) => Y j) ⁻¹' A') :=
      hm _ hS
    choose c' hc' using fun j : {j : Fin (m + 1) // j ≠ i} => Fin.exists_succAbove_eq j.2
    let Λ' : (Fin m → Torus d) → ({j : Fin (m + 1) // j ≠ i} → Torus d) := fun r j => r (c' j)
    have hΛ'm : Measurable Λ' := measurable_pi_iff.2 fun j => measurable_pi_apply _
    set A : Set (Fin m → Torus d) := Λ' ⁻¹' A' with hAdef
    have hAm : MeasurableSet A := hΛ'm hA'
    have hS_eq : ((fun (Y : Config d (m + 1)) (j : {j // j ≠ i}) => Y j) ⁻¹' A') =
        (fun Y : Config d (m + 1) => Fin.removeNth i Y) ⁻¹' A := by
      ext Y
      simp only [Set.mem_preimage, hAdef]
      have : (fun j : {j // j ≠ i} => Y j) = Λ' (Fin.removeNth i Y) := by
        funext j
        simp only [Λ', Fin.removeNth]
        rw [hc' j]
      rw [this]
    rw [hS_eq] at hSm ⊢
    set χ : (Fin m → Torus d) → ℝ≥0∞ := A.indicator (fun _ => 1) with hχdef
    have hχm : Measurable χ := measurable_const.indicator hAm
    have hconv : ∀ F : Config d (m + 1) → ℝ, Measurable F → (∀ Y, 0 ≤ F Y) →
        ∫ Y in (fun Y : Config d (m + 1) => Fin.removeNth i Y) ⁻¹' A, F Y ∂P =
          (∫⁻ Y, χ (Fin.removeNth i Y) * ENNReal.ofReal (F Y) ∂P).toReal := by
      intro F hF hF0
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hF0) hF.aestronglyMeasurable,
        ← lintegral_indicator hSm]
      congr 1
      refine lintegral_congr fun Y => ?_
      by_cases h : Fin.removeNth i Y ∈ A
      · have h' : Y ∈ (fun Y : Config d (m + 1) => Fin.removeNth i Y) ⁻¹' A := h
        rw [Set.indicator_of_mem h', hχdef, Set.indicator_of_mem h]; simp
      · have h' : Y ∉ (fun Y : Config d (m + 1) => Fin.removeNth i Y) ⁻¹' A := h
        rw [Set.indicator_of_notMem h', hχdef, Set.indicator_of_notMem h]; simp
    have hgm' : Measurable fun Y : Config d (m + 1) => gPlus d s c (x - Y i) :=
      hgm.comp (measurable_const.sub (measurable_pi_apply i))
    rw [hconv _ hTm (fun Y => (hbd' Y).1), hconv _ hgm' (fun Y => hc _)]
    congr 1
    exact (l48_core hd hcrit hβ hρ hc x ht i P hPdef χ hχm).symm
  · -- measurability with respect to the conditioning σ-algebra
    have hΛ : Measurable fun (w : {j : Fin (m + 1) // j ≠ i} → Torus d) =>
        (fun j' : Fin m => w ⟨i.succAbove j', Fin.succAbove_ne i j'⟩) :=
      measurable_pi_iff.2 fun j' => measurable_pi_apply _
    have hG : Measurable[othersSigma i] fun Y : Config d (m + 1) =>
        l48_Tr d s c β ρ (m + 2) x t (Fin.removeNth i Y) := by
      have h1 := (hTr.comp hΛ).comp
        (comap_measurable (m := MeasurableSpace.pi)
          (fun (Y : Config d (m + 1)) (j : {j // j ≠ i}) => Y j))
      exact h1
    rw [hTeq]
    exact hG.stronglyMeasurable.aestronglyMeasurable

/-- Step 1 of the chain: the conditional expectation of `g₊(x - y_i)` given the other coordinates
is `T₁ = N_Y / Z_Y` (TeX `R:eq:conditional-density`). -/
theorem l48_condExp_eq {N : ℕ} (hN : 2 ≤ N) (x : Torus d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin (N - 1)) :
    (critPole d s c β ρ N x t)[fun Y' : Config d (N - 1) => gPlus d s c (x - Y' i) | othersSigma i]
      =ᵐ[critPole d s c β ρ N x t] fun Y => l48_T d s c β ρ N x t i Y := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  exact l48_condExp_eq_m hd hcrit hβ hρ hc x ht i _ rfl

end Core2

end L48

end HRS

end
