import HRS.MD.Cov211Pt
import HRS.MD.Cov211Growth

/-!
# Packet COV211: Proposition 2.11 `covariance_obstruction` (relocated proof)

Plan (TeX `V:subsubsec:covariance-obstruction-proof`, L5344-5497); all bounds on the `θ`-integrals are
lower bounds through continuous minorants, so no measurability of `θ ↦ W_p` is used.

* `Cov211Metric`: `W_2`, `W_1`, `d_j` lower bounds by test functions on `ℝ`.
* `Cov211Trunc`, `Cov211Lower`: the truncated quadratic `FL L` and sub-Gaussian second-moment tails.
* `Cov211Base`, `Cov211Bias`: smoothness of `M, C`, `∫_a^b (C_N - C) = ΔM`, and the pointwise bias limit
  from `equilibrium_bias_expansion_proof`; `δ_N⁻¹ ∫_a^b (C_N - C) → B(b) - B(a)`.
* `Cov211Fam`, `Cov211Pt`: the family (`i = 0` is `W_2`, `1` is `W_1`, `j + 2` is `d_{j+2}`) of continuous
  minorants `gfam i N θ` with `ofReal (gfam) ≤ ofReal (wfam) * Tfam`, and their interval averages.
* `Cov211Scheme`: interval-averaged `liminf` and the dense `G_δ` set (Baire, via `response_category_freq`),
  `inter_dense` for the countable intersection over `i`.
* `Cov211Growth`: root-`N` failure at `s > 2d/3`.
* this file: assembly.  The tie to `HRS.Main.covariance_obstruction` is in `Cov211Tie`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MD.Cov211

open HRS

variable {d : ℕ} {s : ℝ}

theorem sqrt_mul_delta (hs1 : (d : ℝ) / 2 < s) {N : ℕ} (hN : 0 < N) :
    Real.sqrt N * deltaN d s N = (N : ℝ) ^ ((3 : ℝ) / 2 - d / s) := by
  rw [deltaN_eq hs1, Real.sqrt_eq_rpow, ← Real.rpow_add (by exact_mod_cast hN)]
  congr 1; ring

theorem growth_exponent (hs1 : (d : ℝ) / 2 < s) (h23 : 2 * (d : ℝ) / 3 < s) :
    0 < (3 : ℝ) / 2 - d / s := by
  have hspos : 0 < s := lt_of_le_of_lt (by positivity) hs1
  have : (d : ℝ) / s < 3 / 2 := by rw [div_lt_iff₀ hspos]; linarith
  linarith

theorem growth (hs1 : (d : ℝ) / 2 < s) (h23 : 2 * (d : ℝ) / 3 < s) (i : ℕ) :
    Tendsto (fun N : ℕ => Real.sqrt N / wfam d s i N) atTop atTop := by
  have ha := growth_exponent hs1 h23
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ ((3 : ℝ) / 2 - d / s)) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  rcases i with _ | _ | j
  · refine hpow.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [wfam, div_inv_eq_mul]
    exact (sqrt_mul_delta hs1 hN).symm
  · refine (tendsto_rpow_div_sqrt_log _ ha).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hδ := deltaN_pos hs1 (show 0 < N by omega)
    have hlog : 0 < Real.sqrt (Real.log (Real.exp 1 * N)) := Real.sqrt_pos.2 (by
      have := log_exp_mul_pos hN; linarith)
    simp only [wfam]
    rw [← sqrt_mul_delta hs1 (show 0 < N by omega)]
    field_simp
  · refine (tendsto_rpow_div_log _ ha).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hδ := deltaN_pos hs1 (show 0 < N by omega)
    have hlog : 0 < Real.log (Real.exp 1 * N) := by have := log_exp_mul_pos hN; linarith
    simp only [wfam]
    rw [← sqrt_mul_delta hs1 (show 0 < N by omega)]
    field_simp

theorem wfam_pos (hs1 : (d : ℝ) / 2 < s) (i N : ℕ) (hN : 2 ≤ N) : 0 < wfam d s i N := by
  have hδ := deltaN_pos hs1 (show 0 < N by omega)
  have hlog : 0 < Real.log (Real.exp 1 * N) := by have := log_exp_mul_pos (show 1 ≤ N by omega); linarith
  rcases i with _ | _ | j
  · simp only [wfam]; positivity
  · simp only [wfam]; have := Real.sqrt_pos.2 hlog; positivity
  · simp only [wfam]; positivity

theorem Kfam_pos (D D' : ℝ) (hD : 0 < D) (hD' : 0 < D') (i : ℕ) : 0 < Kfam D D' i := by
  rcases i with _ | _ | j
  · unfold Kfam; positivity
  · unfold Kfam; have := M1c_pos; positivity
  · unfold Kfam; have := Mjc_pos (j + 2); positivity

theorem deltaN_nonneg' (hs1 : (d : ℝ) / 2 < s) (N : ℕ) : 0 ≤ deltaN d s N := by
  rw [deltaN_eq hs1]; exact Real.rpow_nonneg (Nat.cast_nonneg N) _

theorem covariance_obstruction_proof (hd : 2 ≤ d) {s : ℝ} (hs1 : (d : ℝ) / 2 < s) (hsd : s < d)
    (β : ℝ) (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β (ρ θ)) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun θ => supercriticalBias d s β (ρ θ) (Torus.cosMode k)) ∧
      supercriticalBias d s β (ρ 0) (Torus.cosMode k) = 0 ∧
      (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ θ ∈ Set.Icc (0 : ℝ) ε,
        c₀ ≤ deriv (fun θ' => supercriticalBias d s β (ρ θ') (Torus.cosMode k)) θ) ∧
      (∃ c₁ : ℝ, 0 < c₁ ∧ ∃ cJ : ℕ → ℝ, (∀ j : ℕ, 2 ≤ j → 0 < cJ j) ∧
        ∀ a b : ℝ, 0 < a → a < b → b < ε →
        Tendsto (fun N : ℕ => (deltaN d s N)⁻¹ * ∫ θ in a..b,
            (rateVarN d s k β N θ - susceptibilityCov (periodicRiesz d s) (withDensityReal (ρ θ)) β
              (Torus.cosMode k) (Torus.cosMode k))) atTop
          (𝓝 (supercriticalBias d s β (ρ b) (Torus.cosMode k) -
            supercriticalBias d s β (ρ a) (Torus.cosMode k))) ∧
        0 < supercriticalBias d s β (ρ b) (Torus.cosMode k) -
          supercriticalBias d s β (ρ a) (Torus.cosMode k) ∧
        ENNReal.ofReal (c * (b - a)) ≤ liminf (fun N : ℕ =>
          ENNReal.ofReal (deltaN d s N)⁻¹ * ∫⁻ θ in Set.Icc a b,
            wassersteinE 2 (rateLaw d s k β N θ) (rateGaussian d s k β (ρ θ))) atTop ∧
        ENNReal.ofReal (c₁ * (b - a)) ≤ liminf (fun N : ℕ =>
          ENNReal.ofReal (Real.sqrt (Real.log (Real.exp 1 * N)) / deltaN d s N) *
            ∫⁻ θ in Set.Icc a b,
              wassersteinE 1 (rateLaw d s k β N θ) (rateGaussian d s k β (ρ θ))) atTop ∧
        (∀ j : ℕ, 2 ≤ j → ENNReal.ofReal (cJ j * (b - a)) ≤
          liminf (fun N : ℕ =>
            ENNReal.ofReal (Real.log (Real.exp 1 * N) / deltaN d s N) *
              ∫⁻ θ in Set.Icc a b, ENNReal.ofReal
                (smoothDist j (rateLaw d s k β N θ) (rateGaussian d s k β (ρ θ)))) atTop)) ∧
      ∃ ℛ : Set ℝ, IsGδ ℛ ∧ ℛ ⊆ Set.Ioo 0 ε ∧ Set.Ioo 0 ε ⊆ closure ℛ ∧
        ∀ θ ∈ ℛ,
          ENNReal.ofReal c ≤ limsup (fun N : ℕ => ENNReal.ofReal (deltaN d s N)⁻¹ *
            wassersteinE 2 (rateLaw d s k β N θ) (rateGaussian d s k β (ρ θ))) atTop ∧
          0 < limsup (fun N : ℕ =>
            ENNReal.ofReal (Real.sqrt (Real.log (Real.exp 1 * N)) / deltaN d s N) *
              wassersteinE 1 (rateLaw d s k β N θ) (rateGaussian d s k β (ρ θ))) atTop ∧
          (∀ j : ℕ, 2 ≤ j →
            0 < limsup (fun N : ℕ => ENNReal.ofReal (Real.log (Real.exp 1 * N) / deltaN d s N) *
              ENNReal.ofReal (smoothDist j (rateLaw d s k β N θ)
                (rateGaussian d s k β (ρ θ)))) atTop) ∧
          (2 * (d : ℝ) / 3 < s →
            limsup (fun N : ℕ => ENNReal.ofReal (Real.sqrt N) *
              wassersteinE 2 (rateLaw d s k β N θ) (rateGaussian d s k β (ρ θ))) atTop = ⊤ ∧
            limsup (fun N : ℕ => ENNReal.ofReal (Real.sqrt N) *
              wassersteinE 1 (rateLaw d s k β N θ) (rateGaussian d s k β (ρ θ))) atTop = ⊤ ∧
            ∀ j : ℕ, 2 ≤ j →
              limsup (fun N : ℕ => ENNReal.ofReal (Real.sqrt N) *
                ENNReal.ofReal (smoothDist j (rateLaw d s k β N θ)
                  (rateGaussian d s k β (ρ θ)))) atTop = ⊤) := by
  classical
  have H : Hyp d s β k ρ := ⟨hd, hs1, hsd, hβ, hk, hρ⟩
  have hs : (d : ℝ) / 2 ≤ s := hs1.le
  obtain ⟨-, -, -, hB4⟩ := TRR.thermal_response_rates_proof hd hs hsd β hβ k hk ρ hρ
  obtain ⟨hBcd, hB0, hBder, hP0⟩ := hB4 hs1
  obtain ⟨P0, hBder, hP0⟩ : ∃ P0 : ℝ, HasDerivAt (fun θ => supercriticalBias d s β (ρ θ)
      (Torus.cosMode k)) P0 0 ∧ 0 < P0 := ⟨_, hBder, hP0⟩
  have hcd : Continuous (deriv (fun θ => supercriticalBias d s β (ρ θ) (Torus.cosMode k))) :=
    hBcd.continuous_deriv (by simp)
  have hev : ∀ᶠ θ in 𝓝 (0 : ℝ), P0 / 2 < deriv (fun θ => supercriticalBias d s β (ρ θ)
      (Torus.cosMode k)) θ :=
    hcd.continuousAt.eventually (lt_mem_nhds (by rw [hBder.deriv]; linarith))
  obtain ⟨ε', hε'0, hε'⟩ := Metric.eventually_nhds_iff.1 hev
  set ε : ℝ := ε' / 2 with hεdef
  have hε : 0 < ε := by positivity
  have hder : ∀ θ ∈ Icc (0 : ℝ) ε, P0 / 2 < deriv (fun θ => supercriticalBias d s β (ρ θ)
      (Torus.cosMode k)) θ := by
    intro θ hθ
    refine hε' ?_
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hθ.1]
    linarith [hθ.2]
  have hBlow : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ ε → P0 / 2 * (b - a) ≤
      supercriticalBias d s β (ρ b) (Torus.cosMode k) -
        supercriticalBias d s β (ρ a) (Torus.cosMode k) := by
    intro a b ha hab hb
    refine (convex_Icc (0 : ℝ) ε).mul_sub_le_image_sub_of_le_deriv (f := fun θ =>
      supercriticalBias d s β (ρ θ) (Torus.cosMode k)) hBcd.continuous.continuousOn
      (hBcd.differentiable (by simp)).differentiableOn (C := P0 / 2) (fun x hx => ?_) a
      ⟨ha, hab.trans hb⟩ b ⟨ha.trans hab, hb⟩ hab
    rw [interior_Icc] at hx
    exact (hder x ⟨hx.1.le, hx.2.le⟩).le
  -- sub-Gaussian tail and variance bounds on [0, ε]
  obtain ⟨D, hD2, hDt⟩ := response_subGaussian_proof hd hs hsd β hβ k hk ρ hρ 0 ε
  obtain ⟨Cu, hCu⟩ := rateVarN_uniform_bound hd hs hsd β hβ k hk 0 ε
  set D' : ℝ := max Cu 1 with hD'def
  have hD' : 1 ≤ D' := le_max_right _ _
  have hCN : ∀ N : ℕ, 2 ≤ N → ∀ θ ∈ Icc (0 : ℝ) ε, rateVarN d s k β N θ ≤ D' :=
    fun N hN θ hθ => (hCu N hN θ hθ).trans (le_max_left _ _)
  have htail : ∀ x : ℝ, 0 ≤ x → ∀ N : ℕ, 2 ≤ N → ∀ θ ∈ Icc (0 : ℝ) ε,
      rateGibbs d s k β θ N {X | x < |rateY d s k β N θ X|} +
        gaussianReal 0 (covC d s β k ρ θ).toNNReal {z | x < |z|} ≤
        ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D))) :=
    fun x hx N hN θ hθ => hDt x hx N hN θ hθ
  have hDpos : 0 < D := by linarith
  have hD'pos : 0 < D' := by linarith
  set qf : ℕ → ℝ := fun i => P0 / 2 / (2 * Kfam D D' i) with hqf
  have hqfpos : ∀ i, 0 < qf i := fun i => by
    have := Kfam_pos D D' hDpos hD'pos i
    simp only [hqf]; positivity
  have hS : ∀ i : ℕ,
      (∀ a b : ℝ, 0 < a → a < b → b < ε → ENNReal.ofReal (qf i * (b - a)) ≤
        liminf (fun N : ℕ => ENNReal.ofReal (wfam d s i N) *
          ∫⁻ θ in Icc a b, Tfam d s k β ρ i N θ) atTop) ∧
      ∃ R : Set ℝ, R ⊆ Ioo 0 ε ∧ IsGδ R ∧ Ioo 0 ε ⊆ closure R ∧
        ∀ θ ∈ R, ∀ L : ℕ, ∃ N : ℕ, L ≤ N ∧ 2 ≤ N ∧ qf i / 2 < gfam d s k β ρ D D' i N θ :=
    fun i => scheme ε hε (gfam d s k β ρ D D' i) (Tfam d s k β ρ i) (wfam d s i)
      (gfam_continuous H D D' i)
      (gfam_nonneg d s k β ρ D D' (fun j => (Kfam_pos D D' hDpos hD'pos j).le)
        (deltaN_nonneg' hs1) i)
      (fun N hN θ hθ => hmin H ε D D' hD2 hD' htail hCN i N hN θ ⟨hθ.1.le, hθ.2.le⟩)
      (qf i) (hqfpos i)
      (fun c e hc hce he => avg_lower H ε D D' (P0 / 2) hDpos (by linarith) hBlow i
        (Kfam_pos D D' hDpos hD'pos i) c e hc hce he)
  choose R hR using fun i => (hS i).2
  have hint := inter_dense ε R (fun i => ⟨(hR i).1, (hR i).2.1, (hR i).2.2.1⟩)
  have key : ∀ θ ∈ ⋂ i, R i, ∀ i : ℕ, ∀ L : ℕ, ∃ N : ℕ, L ≤ N ∧ 2 ≤ N ∧
      ENNReal.ofReal (qf i / 2) ≤ ENNReal.ofReal (wfam d s i N) * Tfam d s k β ρ i N θ := by
    intro θ hθ i L
    have hθi := Set.mem_iInter.1 hθ i
    obtain ⟨N, h1, h2, h3⟩ := (hR i).2.2.2 θ hθi L
    have hθ' : θ ∈ Ioo 0 ε := (hR i).1 hθi
    exact ⟨N, h1, h2, (ENNReal.ofReal_le_ofReal h3.le).trans
      (hmin H ε D D' hD2 hD' htail hCN i N h2 θ ⟨hθ'.1.le, hθ'.2.le⟩)⟩
  have hfreq : ∀ θ ∈ ⋂ i, R i, ∀ i : ℕ, ∃ᶠ N : ℕ in atTop,
      ENNReal.ofReal (qf i / 2) ≤ ENNReal.ofReal (wfam d s i N) * Tfam d s k β ρ i N θ := by
    intro θ hθ i
    rw [Filter.frequently_atTop]
    intro L
    obtain ⟨N, h1, -, h3⟩ := key θ hθ i L
    exact ⟨N, h1, h3⟩
  refine ⟨ε, qf 0 / 2, hε, by have := hqfpos 0; positivity, hBcd, hB0,
    ⟨P0 / 2, by linarith, fun θ hθ => (hder θ hθ).le⟩,
    ⟨qf 1, hqfpos 1, fun j => qf j, fun j hj => hqfpos j, fun a b ha hab hb => ?_⟩,
    ⋂ i, R i, hint.2.1, hint.1, hint.2.2, fun θ hθ => ?_⟩
  · refine ⟨avg_tendsto hd hs1 hsd β hβ k hk ρ hρ a b, ?_, ?_, (hS 1).1 a b ha hab hb, ?_⟩
    · have := hBlow a b ha.le hab.le hb.le
      have h2 : 0 < P0 / 2 * (b - a) := by
        have : 0 < b - a := by linarith
        positivity
      linarith
    · refine le_trans (ENNReal.ofReal_le_ofReal ?_) ((hS 0).1 a b ha hab hb)
      have : 0 < b - a := by linarith
      have := hqfpos 0
      nlinarith
    · intro j hj
      obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le' hj
      exact (hS (j' + 2)).1 a b ha hab hb
  · have fr := hfreq θ hθ
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Filter.le_limsup_of_frequently_le (fr 0)
    · exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by have := hqfpos 1; positivity))
        (Filter.le_limsup_of_frequently_le (fr 1))
    · intro j hj
      obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le' hj
      exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by have := hqfpos (j' + 2); positivity))
        (Filter.le_limsup_of_frequently_le (fr (j' + 2)))
    · intro h23
      refine ⟨?_, ?_, ?_⟩
      · exact limsup_top_of_frequent (T := fun N => Tfam d s k β ρ 0 N θ) (w := wfam d s 0)
          (q := qf 0 / 2) (by have := hqfpos 0; positivity) (fun N hN => wfam_pos hs1 0 N hN)
          (fun L => key θ hθ 0 L) (growth hs1 h23 0)
      · exact limsup_top_of_frequent (T := fun N => Tfam d s k β ρ 1 N θ) (w := wfam d s 1)
          (q := qf 1 / 2) (by have := hqfpos 1; positivity) (fun N hN => wfam_pos hs1 1 N hN)
          (fun L => key θ hθ 1 L) (growth hs1 h23 1)
      · intro j hj
        obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le' hj
        exact limsup_top_of_frequent (T := fun N => Tfam d s k β ρ (j' + 2) N θ)
          (w := wfam d s (j' + 2)) (q := qf (j' + 2) / 2)
          (by have := hqfpos (j' + 2); positivity) (fun N hN => wfam_pos hs1 (j' + 2) N hN)
          (fun L => key θ hθ (j' + 2) L) (growth hs1 h23 (j' + 2))

end HRS.MD.Cov211
