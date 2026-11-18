/-
# HRS.Equilibrium.PinStep -- torus estimates and the pin step for Lemma 4.10 (EQ-01b)

Downstream of `PairCorrection` (the proof uses the pole-volume bounds `twopole_vol` etc. proved
there).  The abstract weighted Dobrushin comparison is `HRS.External.WeakPointwise`.
-/
import HRS.Equilibrium.PairCorrection
import HRS.External.WeakPointwise
import HRS.Equilibrium.ReferenceMarginal

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace PinAux

variable {d : ℕ} {s : ℝ}

/-- `ℓ^4 ≤ (1 + 4/s)^4 w` and `ℓ ≤ (1 + 4/s) w` (pointwise). -/
theorem ellEnv_le_wEnv {s : ℝ} (hs : 0 < s) (x y : Torus d) :
    ellEnv x y ≤ (1 + 4 / s) * wEnv s x y ∧ ellEnv x y ^ 4 ≤ (1 + 4 / s) ^ 4 * wEnv s x y := by
  have hr0 : 0 ≤ rTrunc x y := PairCorrAux.rTrunc_nonneg x y
  have hr1 : rTrunc x y ≤ 1 := PairCorrAux.rTrunc_le_one x y
  rcases hr0.eq_or_lt with h0 | hpos
  · have h : rTrunc x y = 0 := h0.symm
    have e1 : ellEnv x y = 1 := by unfold ellEnv; rw [h]; simp
    have e2 : wEnv s x y = 1 := by
      unfold wEnv; rw [h, Real.zero_rpow (by linarith : -s ≠ 0)]; norm_num
    rw [e1, e2]
    have h4 : (0 : ℝ) ≤ 4 / s := by positivity
    have : (1 : ℝ) ≤ 1 + 4 / s := by linarith
    constructor
    · linarith
    · simpa using one_le_pow₀ (n := 4) this
  · set r := rTrunc x y with hr
    have hε : 0 < s / 4 := by positivity
    have hlog : Real.log (1 / r) ≤ (1 / r) ^ (s / 4) / (s / 4) :=
      Real.log_le_rpow_div (by positivity) hε
    set u : ℝ := r ^ (-(s / 4)) with hu
    have hu1 : 1 ≤ u := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos hr1 (by linarith)
    have hone : (1 / r) ^ (s / 4) = u := by
      rw [hu, one_div, Real.inv_rpow hpos.le, Real.rpow_neg hpos.le]
    rw [hone] at hlog
    have hell : ellEnv x y ≤ (1 + 4 / s) * u := by
      unfold ellEnv
      rw [← hr]
      have : u / (s / 4) = 4 / s * u := by field_simp
      rw [this] at hlog
      nlinarith
    have hu4 : u ^ 4 = r ^ (-s) := by
      rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
      congr 1; push_cast; ring
    have hus : u ≤ r ^ (-s) := by
      rw [hu]
      exact Real.rpow_le_rpow_of_exponent_ge hpos hr1 (by linarith)
    have hw : wEnv s x y = 1 + r ^ (-s) := by unfold wEnv; rw [hr]
    have hell0 : 0 ≤ ellEnv x y := by
      unfold ellEnv; linarith [PairCorrAux.log_one_div_nonneg x y]
    have hc0 : 0 ≤ 1 + 4 / s := by positivity
    constructor
    · rw [hw]
      calc ellEnv x y ≤ (1 + 4 / s) * u := hell
        _ ≤ (1 + 4 / s) * (1 + r ^ (-s)) := by gcongr; linarith
    · rw [hw]
      calc ellEnv x y ^ 4 ≤ ((1 + 4 / s) * u) ^ 4 := pow_le_pow_left₀ hell0 hell 4
        _ = (1 + 4 / s) ^ 4 * r ^ (-s) := by rw [mul_pow, hu4]
        _ ≤ (1 + 4 / s) ^ 4 * (1 + r ^ (-s)) := by gcongr; linarith


theorem measurable_ellEnv (b : Torus d) : Measurable (fun x : Torus d => ellEnv x b) := by
  unfold ellEnv rTrunc
  have h : Measurable (fun x : Torus d => Torus.eucDist x b) := by
    have := PairCorrAux.measurable_eucDist' (d := d) b
    simpa [PairCorrAux.eucDist_symm'] using this
  exact measurable_const.add (Real.measurable_log.comp (measurable_const.div (measurable_const.min h)))

theorem ellEnv_nonneg (x y : Torus d) : 0 ≤ ellEnv x y := by
  unfold ellEnv; linarith [PairCorrAux.log_one_div_nonneg x y]

theorem wEnv_pos (s : ℝ) (x y : Torus d) : 0 ≤ wEnv s x y := by
  linarith [PairCorrAux.one_le_wEnv s x y]

/-- **Triple-convolution estimate**: `sup_{z,b} ∫ w(z,x) ℓ(x,b) dx < ∞` (Hölder with exponents
`4/3`, `4`, using `g_+ ∈ L^{4/3}` and `ℓ^4 ≲ w`). -/
theorem wEll_vol {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z b : Torus d,
      ∫⁻ x, ENNReal.ofReal (wEnv s z x * ellEnv x b) ≤ ENNReal.ofReal C := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  have : (volume : Measure (Torus d)).IsNegInvariant :=
    MeasureTheory.Measure.pi.isNegInvariant (fun _ : Fin d => (volume : Measure UnitAddCircle))
  obtain ⟨A, hA0, hAw⟩ := PairCorrAux.wEnv_le_gPlus hd hcrit c hc
  have hG := PoleCavityAux.A_finite hd hcrit c hc
  set G : ℝ≥0∞ := ∫⁻ z, ((ENNReal.ofReal (gPlus d s c z)) ^ (2 / 3 : ℝ)) ^ 2 with hGdef
  set C0 : ℝ := PairCorrAux.cdR d * ((1 / d + 1 / s) * 1 ^ s) + 2 with hC0
  have hC0n : 0 ≤ C0 := by
    have := PairCorrAux.cdR_nonneg d
    have : 0 ≤ (1 / (d : ℝ) + 1 / s) * 1 ^ s := by positivity
    positivity
  set cl : ℝ := 1 + 4 / s with hcl
  have hcl0 : 0 ≤ cl := by positivity
  set Cfin : ℝ := A * (cl * C0 + (G.toReal) ^ (3 / 4 : ℝ) * (cl ^ 4 * C0) ^ (1 / 4 : ℝ)) with hCfin
  refine ⟨Cfin, by positivity, fun z b => ?_⟩
  obtain ⟨hs0', hsd'⟩ := PoleCavityAux.hs_aux hd hcrit
  have hgm := PoleCavityAux.measurable_gPlus hd hs0' hsd' c
  have hlm := measurable_ellEnv (d := d) b
  -- pointwise
  have hpt : ∀ x : Torus d, ENNReal.ofReal (wEnv s z x * ellEnv x b)
      ≤ ENNReal.ofReal A * (ENNReal.ofReal (ellEnv x b)
          + ENNReal.ofReal (gPlus d s c (z - x)) * ENNReal.ofReal (ellEnv x b)) := by
    intro x
    have hl := ellEnv_nonneg x b
    have hg : 0 ≤ gPlus d s c (z - x) := hc _
    rw [← ENNReal.ofReal_mul hg, ← ENNReal.ofReal_add hl (mul_nonneg hg hl),
      ← ENNReal.ofReal_mul hA0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    calc wEnv s z x * ellEnv x b ≤ (A * (1 + gPlus d s c (z - x))) * ellEnv x b :=
          mul_le_mul_of_nonneg_right (hAw z x) hl
      _ = _ := by ring
  have hI1 : ∫⁻ x, ENNReal.ofReal (ellEnv x b) ≤ ENNReal.ofReal (cl * C0) := by
    calc ∫⁻ x, ENNReal.ofReal (ellEnv x b)
        ≤ ∫⁻ x, ENNReal.ofReal cl * ENNReal.ofReal (wEnv s b x) := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.ofReal_mul hcl0]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [PairCorrAux.wEnv_symm s b x]
          exact (ellEnv_le_wEnv hs0 x b).1
      _ = ENNReal.ofReal cl * ∫⁻ x, ENNReal.ofReal (wEnv s b x) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal cl * ENNReal.ofReal C0 := by
          gcongr; exact PairCorrAux.radial_B0 hd hcrit b
      _ = _ := (ENNReal.ofReal_mul hcl0).symm
  have hI4 : ∫⁻ x, (ENNReal.ofReal (ellEnv x b)) ^ (4 : ℝ) ≤ ENNReal.ofReal (cl ^ 4 * C0) := by
    calc ∫⁻ x, (ENNReal.ofReal (ellEnv x b)) ^ (4 : ℝ)
        ≤ ∫⁻ x, ENNReal.ofReal (cl ^ 4) * ENNReal.ofReal (wEnv s b x) := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_rpow_of_nonneg (ellEnv_nonneg x b)
            (by norm_num)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [PairCorrAux.wEnv_symm s b x]
          have := (ellEnv_le_wEnv hs0 x b).2
          simpa [Real.rpow_natCast] using this
      _ = ENNReal.ofReal (cl ^ 4) * ∫⁻ x, ENNReal.ofReal (wEnv s b x) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (cl ^ 4) * ENNReal.ofReal C0 := by
          gcongr; exact PairCorrAux.radial_B0 hd hcrit b
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  have hhold : (4 / 3 : ℝ).HolderConjugate 4 :=
    Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
  have hI2 : ∫⁻ x, ENNReal.ofReal (gPlus d s c (z - x)) * ENNReal.ofReal (ellEnv x b)
      ≤ ENNReal.ofReal ((G.toReal) ^ (3 / 4 : ℝ) * (cl ^ 4 * C0) ^ (1 / 4 : ℝ)) := by
    have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure (Torus d)) hhold
      (f := fun x => ENNReal.ofReal (gPlus d s c (z - x)))
      (g := fun x => ENNReal.ofReal (ellEnv x b))
      ((ENNReal.measurable_ofReal.comp (hgm.comp (measurable_const.sub measurable_id))).aemeasurable)
      ((ENNReal.measurable_ofReal.comp hlm).aemeasurable)
    refine hh.trans ?_
    have e1 : ∫⁻ x, (ENNReal.ofReal (gPlus d s c (z - x))) ^ (4 / 3 : ℝ) = G := by
      have : ∀ x, (ENNReal.ofReal (gPlus d s c (z - x))) ^ (4 / 3 : ℝ)
          = ((ENNReal.ofReal (gPlus d s c (z - x))) ^ (2 / 3 : ℝ)) ^ 2 := fun x => by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
      simp_rw [this]
      exact lintegral_sub_left_eq_self (fun y => ((ENNReal.ofReal (gPlus d s c y)) ^ (2 / 3 : ℝ)) ^ 2) z
    rw [e1]
    have hGt : G = ENNReal.ofReal G.toReal := (ENNReal.ofReal_toReal hG).symm
    have e2 : G ^ (1 / (4 / 3 : ℝ)) = (ENNReal.ofReal G.toReal) ^ (3 / 4 : ℝ) := by
      rw [← hGt]; norm_num
    calc G ^ (1 / (4 / 3 : ℝ)) * (∫⁻ x, (ENNReal.ofReal (ellEnv x b)) ^ (4 : ℝ)) ^ (1 / (4 : ℝ))
        ≤ (ENNReal.ofReal G.toReal) ^ (3 / 4 : ℝ) * (ENNReal.ofReal (cl ^ 4 * C0)) ^ (1 / 4 : ℝ) :=
          mul_le_mul' (le_of_eq e2) (ENNReal.rpow_le_rpow hI4 (by norm_num))
      _ = _ := by
          rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
            ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
            ← ENNReal.ofReal_mul (by positivity)]
  calc ∫⁻ x, ENNReal.ofReal (wEnv s z x * ellEnv x b)
      ≤ ∫⁻ x, ENNReal.ofReal A * (ENNReal.ofReal (ellEnv x b)
          + ENNReal.ofReal (gPlus d s c (z - x)) * ENNReal.ofReal (ellEnv x b)) := lintegral_mono hpt
    _ = ENNReal.ofReal A * ((∫⁻ x, ENNReal.ofReal (ellEnv x b))
          + ∫⁻ x, ENNReal.ofReal (gPlus d s c (z - x)) * ENNReal.ofReal (ellEnv x b)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left (f := fun x => ENNReal.ofReal (ellEnv x b))
            (ENNReal.measurable_ofReal.comp hlm)]
    _ ≤ ENNReal.ofReal A * (ENNReal.ofReal (cl * C0)
          + ENNReal.ofReal ((G.toReal) ^ (3 / 4 : ℝ) * (cl ^ 4 * C0) ^ (1 / 4 : ℝ))) := by
        gcongr
    _ = ENNReal.ofReal Cfin := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hA0.le]


/-- Constants of the pole-volume estimates (all in the volume measure on the torus). -/
structure EnvFacts (d : ℕ) (s : ℝ) (q : Torus d → ℝ) (γ₀ C0 C1 C2 cl Cw A' : ℝ) : Prop where
  C0_nn : 0 ≤ C0
  C1_nn : 0 ≤ C1
  C2_nn : 0 ≤ C2
  cl_nn : 0 ≤ cl
  Cw_nn : 0 ≤ Cw
  A'_nn : 0 ≤ A'
  int_w : ∀ z : Torus d, ∫⁻ x, ENNReal.ofReal (wEnv s z x) ≤ ENNReal.ofReal C0
  twopole : ∀ z b : Torus d, z ≠ b →
    ∫⁻ x, ENNReal.ofReal (wEnv s z x * wEnv s b x) ≤ ENNReal.ofReal (C1 * ellEnv z b)
  wEll : ∀ z b : Torus d, ∫⁻ x, ENNReal.ofReal (wEnv s z x * ellEnv x b) ≤ ENNReal.ofReal C2
  ell_le : ∀ x y : Torus d, ellEnv x y ≤ cl * wEnv s x y
  kern : ∀ z x : Torus d, q (z - x) + γ₀ ≤ Cw * wEnv s z x
  low : ∀ z x : Torus d, wEnv s z x ≤ A' * (1 + q (z - x))

theorem measurable_wEnv_left (s : ℝ) (b : Torus d) : Measurable (fun x : Torus d => wEnv s x b) := by
  have : (fun x : Torus d => wEnv s x b) = fun x => wEnv s b x := funext fun x => PairCorrAux.wEnv_symm s x b
  rw [this]; exact PairCorrAux.measurable_wEnv s b

section JLemmas

variable {s : ℝ} {q : Torus d → ℝ} {γ₀ C0 C1 C2 cl Cw A' : ℝ} {ρ : Torus d → ℝ} {Λ : ℝ}

theorem J_w (hE : EnvFacts d s q γ₀ C0 C1 C2 cl Cw A') (hΛ : ∀ x, ρ x ≤ Λ) (hΛ0 : 0 ≤ Λ) {m : ℕ}
    (b : Fin m → Torus d) (z : Torus d) (hz : ∀ k, z ≠ b k) :
    ∫⁻ x, ENNReal.ofReal ((1 + ∑ k, wEnv s x (b k)) * wEnv s z x) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (Λ * (C0 + ∑ k, C1 * ellEnv z (b k))) := by
  have hw1 := fun x => PairCorrAux.one_le_wEnv s z x
  have hw0 : ∀ x y : Torus d, 0 ≤ wEnv s x y := wEnv_pos s
  have hpt : ∀ x : Torus d, ENNReal.ofReal ((1 + ∑ k, wEnv s x (b k)) * wEnv s z x)
      = ENNReal.ofReal (wEnv s z x) + ∑ k, ENNReal.ofReal (wEnv s z x * wEnv s (b k) x) := by
    intro x
    have : (1 + ∑ k, wEnv s x (b k)) * wEnv s z x
        = wEnv s z x + ∑ k, wEnv s z x * wEnv s (b k) x := by
      rw [add_mul, one_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [PairCorrAux.wEnv_symm s x (b k)]; ring
    rw [this, ENNReal.ofReal_add (hw0 _ _) (Finset.sum_nonneg fun k _ => mul_nonneg (hw0 _ _) (hw0 _ _)),
      ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (hw0 _ _) (hw0 _ _))]
  calc ∫⁻ x, ENNReal.ofReal ((1 + ∑ k, wEnv s x (b k)) * wEnv s z x) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal Λ * ∫⁻ x, ENNReal.ofReal ((1 + ∑ k, wEnv s x (b k)) * wEnv s z x) :=
        PoleCavityAux.lintegral_mu_le_vol hΛ _
    _ = ENNReal.ofReal Λ * ((∫⁻ x, ENNReal.ofReal (wEnv s z x))
          + ∑ k, ∫⁻ x, ENNReal.ofReal (wEnv s z x * wEnv s (b k) x)) := by
        congr 1
        simp_rw [hpt]
        rw [lintegral_add_left (f := fun x => ENNReal.ofReal (wEnv s z x))
          (ENNReal.measurable_ofReal.comp (PairCorrAux.measurable_wEnv s z)),
          lintegral_finsetSum]
        intro k _
        exact ENNReal.measurable_ofReal.comp
          ((PairCorrAux.measurable_wEnv s z).mul (PairCorrAux.measurable_wEnv s (b k)))
    _ ≤ ENNReal.ofReal Λ * (ENNReal.ofReal C0 + ∑ k, ENNReal.ofReal (C1 * ellEnv z (b k))) := by
        gcongr with k _
        · exact hE.int_w z
        · exact hE.twopole z (b k) (hz k)
    _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg hE.C1_nn (ellEnv_nonneg _ _)),
          ← ENNReal.ofReal_add hE.C0_nn (Finset.sum_nonneg fun k _ => mul_nonneg hE.C1_nn (ellEnv_nonneg _ _)),
          ← ENNReal.ofReal_mul hΛ0]

theorem J_ell (hE : EnvFacts d s q γ₀ C0 C1 C2 cl Cw A') (hΛ : ∀ x, ρ x ≤ Λ) (hΛ0 : 0 ≤ Λ) {m : ℕ}
    (b : Fin m → Torus d) (z : Torus d) :
    ∫⁻ x, ENNReal.ofReal ((1 + ∑ k, ellEnv x (b k)) * wEnv s z x) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (Λ * (C0 + m * C2)) := by
  have hw0 : ∀ x y : Torus d, 0 ≤ wEnv s x y := wEnv_pos s
  have hpt : ∀ x : Torus d, ENNReal.ofReal ((1 + ∑ k, ellEnv x (b k)) * wEnv s z x)
      = ENNReal.ofReal (wEnv s z x) + ∑ k, ENNReal.ofReal (wEnv s z x * ellEnv x (b k)) := by
    intro x
    have : (1 + ∑ k, ellEnv x (b k)) * wEnv s z x
        = wEnv s z x + ∑ k, wEnv s z x * ellEnv x (b k) := by
      rw [add_mul, one_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this, ENNReal.ofReal_add (hw0 _ _) (Finset.sum_nonneg fun k _ => mul_nonneg (hw0 _ _) (ellEnv_nonneg _ _)),
      ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (hw0 _ _) (ellEnv_nonneg _ _))]
  calc ∫⁻ x, ENNReal.ofReal ((1 + ∑ k, ellEnv x (b k)) * wEnv s z x) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal Λ * ∫⁻ x, ENNReal.ofReal ((1 + ∑ k, ellEnv x (b k)) * wEnv s z x) :=
        PoleCavityAux.lintegral_mu_le_vol hΛ _
    _ = ENNReal.ofReal Λ * ((∫⁻ x, ENNReal.ofReal (wEnv s z x))
          + ∑ k, ∫⁻ x, ENNReal.ofReal (wEnv s z x * ellEnv x (b k))) := by
        congr 1
        simp_rw [hpt]
        rw [lintegral_add_left (f := fun x => ENNReal.ofReal (wEnv s z x))
          (ENNReal.measurable_ofReal.comp (PairCorrAux.measurable_wEnv s z)),
          lintegral_finsetSum]
        intro k _
        exact ENNReal.measurable_ofReal.comp
          ((PairCorrAux.measurable_wEnv s z).mul (measurable_ellEnv (b k)))
    _ ≤ ENNReal.ofReal Λ * (ENNReal.ofReal C0 + ∑ _k : Fin m, ENNReal.ofReal C2) := by
        gcongr with k _
        · exact hE.int_w z
        · exact hE.wEll z (b k)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_add hE.C0_nn (mul_nonneg (Nat.cast_nonneg _) hE.C2_nn),
          ← ENNReal.ofReal_mul hΛ0]

end JLemmas


section TstarBounds

open HRS.External

variable {s γ₀ C0 C1 C2 cl Cw A' : ℝ} {q : Torus d → ℝ} {ρ : Torus d → ℝ} {Λ : ℝ}

/-- The dependence kernel of the field ensembles is dominated by `Cω Cw w`. -/
theorem fieldOmega_le_w (hE : EnvFacts d s q γ₀ C0 C1 C2 cl Cw A') {μ : Measure (Torus d)}
    (V : WeakPotential μ) (hVq : ∀ x y, V.q x y = q (x - y)) (hVγ : V.γ = γ₀) {lam K1 : ℝ}
    (hlam : 0 ≤ lam) (hK1 : 0 ≤ K1) (z x : Torus d) :
    fieldOmega V lam K1 z x ≤ (K1 * (1 + K1) * lam * Cw) * wEnv s z x := by
  unfold fieldOmega
  rw [hVq, hVγ]
  have hC : 0 ≤ K1 * (1 + K1) * lam := by positivity
  calc K1 * (1 + K1) * lam * (q (z - x) + γ₀) ≤ K1 * (1 + K1) * lam * (Cw * wEnv s z x) :=
        mul_le_mul_of_nonneg_left (hE.kern z x) hC
    _ = _ := by ring

/-- `T* u (z)` for `u` dominated by a weight `ū`. -/
theorem Tstar_weight_bound (hE : EnvFacts d s q γ₀ C0 C1 C2 cl Cw A')
    (hρ : SmoothPosDensity ρ)
    (V : WeakPotential (withDensityReal ρ)) (hVq : ∀ x y, V.q x y = q (x - y)) (hVγ : V.γ = γ₀)
    {lam K1 : ℝ} (hlam : 0 ≤ lam) (hK1 : 0 ≤ K1) {n : ℕ} (hn : 1 ≤ n) {u : Torus d → ℝ}
    (hu : GoodF u) (ū : Torus d → ℝ) (hū : Measurable ū) (hū0 : ∀ x, 0 ≤ ū x)
    (hle : ∀ᵐ x ∂(withDensityReal ρ), u x ≤ ū x) (z : Torus d) {J1 J2 : ℝ}
    (hJ1 : 0 ≤ J1) (hJ2 : 0 ≤ J2)
    (h1 : ∫⁻ x, ENNReal.ofReal (ū x * wEnv s z x) ∂(withDensityReal ρ) ≤ ENNReal.ofReal J1)
    (h2 : ∫⁻ x, ENNReal.ofReal (ū x) ∂(withDensityReal ρ) ≤ ENNReal.ofReal J2) :
    Tstar (withDensityReal ρ) (fieldOmega V lam K1) n u z
      ≤ ((n : ℝ) - 1) * ((K1 * (1 + K1) * lam * Cw) * J1
          + (2 * (K1 * (1 + K1) * lam) * γ₀) * J2) := by
  have : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu hρ
  have hker := fieldOmega_ker (μ := withDensityReal ρ) V hlam hK1
  set Cω : ℝ := K1 * (1 + K1) * lam with hCω
  have hCω0 : 0 ≤ Cω := by positivity
  have hρc : 2 * Cω * V.γ = 2 * Cω * γ₀ := by rw [hVγ]
  have hCw0 := hE.Cw_nn
  refine Tstar_le_of_lintegral hker hn hu (fun x => ENNReal.ofReal (ū x))
    (by filter_upwards [hle] with x hx using ENNReal.ofReal_le_ofReal hx) z
    (T1 := Cω * Cw * J1) (T2 := (2 * Cω * γ₀) * J2) (by positivity) (by
      have := (hVγ ▸ V.γ_nonneg : 0 ≤ γ₀); positivity) ?_ ?_ |>.trans (le_of_eq (by ring))
  · calc ∫⁻ x, ENNReal.ofReal (ū x) * ENNReal.ofReal (fieldOmega V lam K1 z x) ∂(withDensityReal ρ)
        ≤ ∫⁻ x, ENNReal.ofReal (Cω * Cw) * ENNReal.ofReal (ū x * wEnv s z x) ∂(withDensityReal ρ) := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.ofReal_mul (hū0 x), ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          calc ū x * fieldOmega V lam K1 z x ≤ ū x * ((Cω * Cw) * wEnv s z x) :=
                mul_le_mul_of_nonneg_left (fieldOmega_le_w hE V hVq hVγ hlam hK1 z x) (hū0 x)
            _ = _ := by ring
      _ = ENNReal.ofReal (Cω * Cw) * ∫⁻ x, ENNReal.ofReal (ū x * wEnv s z x) ∂(withDensityReal ρ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Cω * Cw) * ENNReal.ofReal J1 := by gcongr
      _ = ENNReal.ofReal (Cω * Cw * J1) := (ENNReal.ofReal_mul (by positivity)).symm
  · have hcol : ∀ x, colS (withDensityReal ρ) (fieldOmega V lam K1) x ≤ 2 * Cω * γ₀ := fun x => by
      rw [← hρc]; exact hker.col_le x
    calc ∫⁻ x, ENNReal.ofReal (ū x) * ENNReal.ofReal (colS (withDensityReal ρ) (fieldOmega V lam K1) x) ∂(withDensityReal ρ)
        ≤ ∫⁻ x, ENNReal.ofReal (2 * Cω * γ₀) * ENNReal.ofReal (ū x) ∂(withDensityReal ρ) := by
          refine lintegral_mono fun x => ?_
          rw [mul_comm]
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hcol x)) le_rfl
      _ = ENNReal.ofReal (2 * Cω * γ₀) * ∫⁻ x, ENNReal.ofReal (ū x) ∂(withDensityReal ρ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (2 * Cω * γ₀) * ENNReal.ofReal J2 := by gcongr
      _ = _ := (ENNReal.ofReal_mul (by
          have := (hVγ ▸ V.γ_nonneg : 0 ≤ γ₀); positivity)).symm

end TstarBounds


section PinD

open HRS.External

variable {s γ₀ C0 C1 C2 cl Cw A' : ℝ} {q : Torus d → ℝ} {ρ : Torus d → ℝ} {Λ : ℝ}

/-- The pointwise pin bound `δ(z) = lam ∑_k q(z - b_k)`. -/
def pinDelta (q : Torus d → ℝ) (lam : ℝ) {m : ℕ} (b : Fin m → Torus d) (z : Torus d) : ℝ :=
  lam * ∑ k, q (z - b k)

/-- The truncated majorant `D = min{K₁, K₁ δ + K₁² ∫ δ}` of the density difference. -/
def pinD (μ : Measure (Torus d)) (q : Torus d → ℝ) (lam K1 : ℝ) {m : ℕ} (b : Fin m → Torus d) :
    Torus d → ℝ :=
  fun z => min K1 (K1 * pinDelta q lam b z + K1 * K1 * ∫ w, pinDelta q lam b w ∂μ)

theorem measurable_pinDelta (hqm : Measurable q) (lam : ℝ) {m : ℕ} (b : Fin m → Torus d) :
    Measurable (pinDelta q lam b) := by
  unfold pinDelta
  exact measurable_const.mul (Finset.measurable_sum _ fun k _ => hqm.comp (measurable_id.sub_const _))

theorem integrable_pinDelta {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (V : WeakPotential μ)
    (hVq : ∀ x y, V.q x y = q (x - y)) (lam : ℝ) {m : ℕ} (b : Fin m → Torus d) :
    Integrable (pinDelta q lam b) μ := by
  unfold pinDelta
  refine Integrable.const_mul (integrable_finsetSum _ fun k _ => ?_) _
  have := integrable_q_left V (b k)
  simpa [hVq] using this

theorem integral_pinDelta_le {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (V : WeakPotential μ)
    (hVq : ∀ x y, V.q x y = q (x - y)) (hVγ : V.γ = γ₀) {lam : ℝ} (hlam : 0 ≤ lam) {m : ℕ}
    (b : Fin m → Torus d) : ∫ z, pinDelta q lam b z ∂μ ≤ lam * m * γ₀ := by
  unfold pinDelta
  rw [integral_const_mul]
  have h1 : ∫ z, ∑ k, q (z - b k) ∂μ = ∑ k, ∫ z, q (z - b k) ∂μ := by
    refine integral_finsetSum _ fun k _ => ?_
    have := integrable_q_left V (b k)
    simpa [hVq] using this
  rw [h1]
  have h2 : ∀ k, ∫ z, q (z - b k) ∂μ ≤ γ₀ := fun k => by
    have := integral_q_left_le V (b k)
    simpa [hVq, hVγ] using this
  calc lam * ∑ k, ∫ z, q (z - b k) ∂μ ≤ lam * ∑ _k : Fin m, γ₀ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => h2 k) hlam
    _ = lam * m * γ₀ := by simp [mul_assoc]

theorem pinDelta_nonneg (hq0 : ∀ z, 0 ≤ q z) {lam : ℝ} (hlam : 0 ≤ lam) {m : ℕ}
    (b : Fin m → Torus d) (z : Torus d) : 0 ≤ pinDelta q lam b z :=
  mul_nonneg hlam (Finset.sum_nonneg fun k _ => hq0 _)

theorem pinDelta_le (hE : EnvFacts d s q γ₀ C0 C1 C2 cl Cw A') (hγ₀ : 0 ≤ γ₀) {lam : ℝ}
    (hlam : 0 ≤ lam) {m : ℕ} (b : Fin m → Torus d) (z : Torus d) :
    pinDelta q lam b z ≤ lam * Cw * ∑ k, wEnv s z (b k) := by
  unfold pinDelta
  have : ∑ k, q (z - b k) ≤ Cw * ∑ k, wEnv s z (b k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => by linarith [hE.kern z (b k)]
  calc lam * ∑ k, q (z - b k) ≤ lam * (Cw * ∑ k, wEnv s z (b k)) :=
        mul_le_mul_of_nonneg_left this hlam
    _ = _ := by ring

theorem pinD_goodF {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (V : WeakPotential μ)
    (hVq : ∀ x y, V.q x y = q (x - y)) (hqm : Measurable q) (hq0 : ∀ z, 0 ≤ q z) {lam K1 : ℝ}
    (hlam : 0 ≤ lam) (hK1 : 0 ≤ K1) {m : ℕ} (b : Fin m → Torus d) :
    GoodF (fun z => pinD μ q lam K1 b z + ∫ w, pinD μ q lam K1 b w ∂μ) := by
  have hδm := measurable_pinDelta hqm lam b
  have hI0 : 0 ≤ ∫ w, pinDelta q lam b w ∂μ := integral_nonneg fun w => pinDelta_nonneg hq0 hlam b w
  have hD0 : ∀ z, 0 ≤ pinD μ q lam K1 b z := fun z => by
    unfold pinD
    exact le_min hK1 (by have := pinDelta_nonneg hq0 hlam b z; positivity)
  have hDm : Measurable (pinD μ q lam K1 b) := by
    unfold pinD
    exact measurable_const.min ((measurable_const.mul hδm).add measurable_const)
  have hDb : ∀ z, pinD μ q lam K1 b z ≤ K1 := fun z => min_le_left _ _
  have hI : 0 ≤ ∫ w, pinD μ q lam K1 b w ∂μ := integral_nonneg hD0
  exact ⟨hDm.add measurable_const, fun z => add_nonneg (hD0 z) hI,
    K1 + ∫ w, pinD μ q lam K1 b w ∂μ, fun z => add_le_add (hDb z) le_rfl⟩

/-- Pointwise bound of `v₀ = D + ∫ D` by a multiple of `1 + ∑ w`. -/
theorem v0_le (hE : EnvFacts d s q γ₀ C0 C1 C2 cl Cw A') (hγ₀ : 0 ≤ γ₀) (hqm : Measurable q)
    (hq0 : ∀ z, 0 ≤ q z) {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (V : WeakPotential μ)
    (hVq : ∀ x y, V.q x y = q (x - y)) (hVγ : V.γ = γ₀) {lam K1 Kb : ℝ} (hlam : 0 ≤ lam)
    (hK1 : 0 < K1) (hKK : K1 ≤ Kb) {m a : ℕ} (hm : m ≤ a) (b : Fin m → Torus d) (z : Torus d) :
    pinD μ q lam K1 b z + ∫ w, pinD μ q lam K1 b w ∂μ
      ≤ lam * (Kb * Cw + (Kb + 2 * Kb ^ 2) * a * γ₀) * (1 + ∑ k, wEnv s z (b k)) := by
  have hδm := measurable_pinDelta hqm lam b
  have hδi := integrable_pinDelta V hVq lam b
  have hδ0 := pinDelta_nonneg hq0 hlam b
  set I : ℝ := ∫ w, pinDelta q lam b w ∂μ with hI
  have hI0 : 0 ≤ I := integral_nonneg hδ0
  have hIle : I ≤ lam * m * γ₀ := integral_pinDelta_le V hVq hVγ hlam b
  have hK0 : 0 ≤ Kb := hK1.le.trans hKK
  have hDle : ∀ z, pinD μ q lam K1 b z ≤ K1 * pinDelta q lam b z + K1 * K1 * I := fun z => min_le_right _ _
  have hD0 : ∀ z, 0 ≤ pinD μ q lam K1 b z := fun z => by
    unfold pinD
    exact le_min hK1.le (by have := hδ0 z; positivity)
  have hDm : Measurable (pinD μ q lam K1 b) := by
    unfold pinD
    exact measurable_const.min ((measurable_const.mul hδm).add measurable_const)
  have hDi : Integrable (pinD μ q lam K1 b) μ :=
    Integrable.of_bound hDm.aestronglyMeasurable K1 (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (hD0 z)]; exact min_le_left _ _)
  have hint : ∫ w, pinD μ q lam K1 b w ∂μ ≤ K1 * I + K1 * K1 * I := by
    calc ∫ w, pinD μ q lam K1 b w ∂μ ≤ ∫ w, (K1 * pinDelta q lam b w + K1 * K1 * I) ∂μ :=
          integral_mono hDi ((hδi.const_mul K1).add (integrable_const _)) hDle
      _ = K1 * I + K1 * K1 * I := by
          rw [integral_add (hδi.const_mul _) (integrable_const _), integral_const_mul]
          simp [hI]
  set S : ℝ := ∑ k, wEnv s z (b k) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => wEnv_pos s _ _
  have h1 : K1 * pinDelta q lam b z ≤ Kb * (lam * Cw * S) :=
    mul_le_mul hKK (pinDelta_le hE hγ₀ hlam b z) (hδ0 z) hK0
  have hm' : (m : ℝ) ≤ a := by exact_mod_cast hm
  have h2 : (K1 + 2 * K1 ^ 2) * I ≤ (Kb + 2 * Kb ^ 2) * (lam * a * γ₀) := by
    refine mul_le_mul (by nlinarith [hK1.le]) ?_ hI0 (by positivity)
    calc I ≤ lam * m * γ₀ := hIle
      _ ≤ lam * a * γ₀ := by gcongr
  have hCw0 := hE.Cw_nn
  have hz : pinD μ q lam K1 b z + ∫ w, pinD μ q lam K1 b w ∂μ
      ≤ K1 * pinDelta q lam b z + (K1 + 2 * K1 ^ 2) * I := by
    have := hDle z
    nlinarith [hint]
  have hr : lam * Kb * Cw * S + (Kb + 2 * Kb ^ 2) * (lam * a * γ₀)
      ≤ lam * (Kb * Cw + (Kb + 2 * Kb ^ 2) * a * γ₀) * (1 + S) := by
    have h3 : 0 ≤ lam * ((Kb + 2 * Kb ^ 2) * a * γ₀) * S := by positivity
    have h4 : 0 ≤ lam * Kb * Cw := by positivity
    nlinarith [h3, h4]
  calc _ ≤ K1 * pinDelta q lam b z + (K1 + 2 * K1 ^ 2) * I := hz
    _ ≤ Kb * (lam * Cw * S) + (Kb + 2 * Kb ^ 2) * (lam * a * γ₀) := add_le_add h1 h2
    _ = lam * Kb * Cw * S + (Kb + 2 * Kb ^ 2) * (lam * a * γ₀) := by ring
    _ ≤ _ := hr

end PinD


section Leaf

variable {s γ₀ C0 C1 C2 cl Cw A' : ℝ} {q : Torus d → ℝ} {ρ : Torus d → ℝ} {Λ : ℝ}

theorem J_one (hE : EnvFacts d s q γ₀ C0 C1 C2 cl Cw A') (hρ : SmoothPosDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) (hΛ0 : 0 ≤ Λ) {m : ℕ} (b : Fin m → Torus d) :
    ∫⁻ x, ENNReal.ofReal (1 + ∑ k, wEnv s x (b k)) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (1 + Λ * m * C0) := by
  have : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu hρ
  have hw0 : ∀ x y : Torus d, 0 ≤ wEnv s x y := wEnv_pos s
  have hpt : ∀ x : Torus d, ENNReal.ofReal (1 + ∑ k, wEnv s x (b k))
      = 1 + ∑ k, ENNReal.ofReal (wEnv s x (b k)) := by
    intro x
    rw [ENNReal.ofReal_add zero_le_one (Finset.sum_nonneg fun k _ => hw0 _ _), ENNReal.ofReal_one,
      ENNReal.ofReal_sum_of_nonneg (fun k _ => hw0 _ _)]
  calc ∫⁻ x, ENNReal.ofReal (1 + ∑ k, wEnv s x (b k)) ∂(withDensityReal ρ)
      = (∫⁻ x, (1 : ℝ≥0∞) ∂(withDensityReal ρ))
          + ∑ k, ∫⁻ x, ENNReal.ofReal (wEnv s x (b k)) ∂(withDensityReal ρ) := by
        simp_rw [hpt]
        rw [lintegral_add_left (f := fun _ => (1 : ℝ≥0∞)) measurable_const, lintegral_finsetSum]
        intro k _
        exact ENNReal.measurable_ofReal.comp (measurable_wEnv_left s (b k))
    _ ≤ 1 + ∑ _k : Fin m, ENNReal.ofReal (Λ * C0) := by
        gcongr with k _
        · simp
        · calc ∫⁻ x, ENNReal.ofReal (wEnv s x (b k)) ∂(withDensityReal ρ)
              ≤ ENNReal.ofReal Λ * ∫⁻ x, ENNReal.ofReal (wEnv s x (b k)) :=
                PoleCavityAux.lintegral_mu_le_vol hΛ _
            _ = ENNReal.ofReal Λ * ∫⁻ x, ENNReal.ofReal (wEnv s (b k) x) := by
                simp_rw [PairCorrAux.wEnv_symm s _ (b k)]
            _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal C0 := by gcongr; exact hE.int_w (b k)
            _ = _ := (ENNReal.ofReal_mul hΛ0).symm
    _ = ENNReal.ofReal (1 + Λ * m * C0) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg hΛ0 hE.C0_nn))]
        congr 1; ring

theorem J_one_ell (hE : EnvFacts d s q γ₀ C0 C1 C2 cl Cw A') (hρ : SmoothPosDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) (hΛ0 : 0 ≤ Λ) {m : ℕ} (b : Fin m → Torus d) :
    ∫⁻ x, ENNReal.ofReal (1 + ∑ k, ellEnv x (b k)) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (1 + Λ * m * (cl * C0)) := by
  have : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu hρ
  have hpt : ∀ x : Torus d, ENNReal.ofReal (1 + ∑ k, ellEnv x (b k))
      = 1 + ∑ k, ENNReal.ofReal (ellEnv x (b k)) := by
    intro x
    rw [ENNReal.ofReal_add zero_le_one (Finset.sum_nonneg fun k _ => ellEnv_nonneg _ _), ENNReal.ofReal_one,
      ENNReal.ofReal_sum_of_nonneg (fun k _ => ellEnv_nonneg _ _)]
  calc ∫⁻ x, ENNReal.ofReal (1 + ∑ k, ellEnv x (b k)) ∂(withDensityReal ρ)
      = (∫⁻ x, (1 : ℝ≥0∞) ∂(withDensityReal ρ))
          + ∑ k, ∫⁻ x, ENNReal.ofReal (ellEnv x (b k)) ∂(withDensityReal ρ) := by
        simp_rw [hpt]
        rw [lintegral_add_left (f := fun _ => (1 : ℝ≥0∞)) measurable_const, lintegral_finsetSum]
        intro k _
        exact ENNReal.measurable_ofReal.comp (measurable_ellEnv (b k))
    _ ≤ 1 + ∑ _k : Fin m, ENNReal.ofReal (Λ * (cl * C0)) := by
        gcongr with k _
        · simp
        · calc ∫⁻ x, ENNReal.ofReal (ellEnv x (b k)) ∂(withDensityReal ρ)
              ≤ ENNReal.ofReal Λ * ∫⁻ x, ENNReal.ofReal (ellEnv x (b k)) :=
                PoleCavityAux.lintegral_mu_le_vol hΛ _
            _ ≤ ENNReal.ofReal Λ * ∫⁻ x, ENNReal.ofReal cl * ENNReal.ofReal (wEnv s (b k) x) := by
                gcongr with x
                rw [← ENNReal.ofReal_mul hE.cl_nn]
                refine ENNReal.ofReal_le_ofReal ?_
                rw [PairCorrAux.wEnv_symm s (b k) x]
                exact hE.ell_le x (b k)
            _ = ENNReal.ofReal Λ * (ENNReal.ofReal cl * ∫⁻ x, ENNReal.ofReal (wEnv s (b k) x)) := by
                rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            _ ≤ ENNReal.ofReal Λ * (ENNReal.ofReal cl * ENNReal.ofReal C0) := by
                gcongr; exact hE.int_w (b k)
            _ = _ := by
                rw [← ENNReal.ofReal_mul hE.cl_nn, ← ENNReal.ofReal_mul hΛ0]
    _ = ENNReal.ofReal (1 + Λ * m * (cl * C0)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg hΛ0 (mul_nonneg hE.cl_nn hE.C0_nn)))]
        congr 1; ring

end Leaf


section Steps

open HRS.External

variable {s γ₀ C0 C1 C2 cl Cw A' : ℝ} {q : Torus d → ℝ} {ρ : Torus d → ℝ} {Λ : ℝ}

theorem u0_step (hE : EnvFacts d s q γ₀ C0 C1 C2 cl Cw A') (hρ : SmoothPosDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) (hΛ0 : 0 ≤ Λ) (hq0 : ∀ z, 0 ≤ q z) (hqm : Measurable q) (hγ₀ : 0 ≤ γ₀)
    (Kb β : ℝ) (hKb : 0 ≤ Kb) (hβ : 0 ≤ β) (a : ℕ) :
    ∃ P0 P1 : ℝ, 0 ≤ P0 ∧ 0 ≤ P1 ∧ ∀ (V : WeakPotential (withDensityReal ρ))
      (hVq : ∀ x y, V.q x y = q (x - y)) (hVγ : V.γ = γ₀)
      (lam K1 : ℝ) (n m : ℕ) [NeZero n] (b : Fin m → Torus d),
      0 ≤ lam → 0 < K1 → K1 ≤ Kb → m ≤ a → (n : ℝ) * lam ≤ β →
      ∀ z : Torus d, (∀ k, z ≠ b k) →
        Tstar (withDensityReal ρ) (fieldOmega V lam K1) n
          (fun z => pinD (withDensityReal ρ) q lam K1 b z
            + ∫ w, pinD (withDensityReal ρ) q lam K1 b w ∂(withDensityReal ρ)) z
          ≤ lam * (P0 + P1 * ∑ k, ellEnv z (b k)) := by
  have : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu hρ
  set c1 : ℝ := Kb * Cw + (Kb + 2 * Kb ^ 2) * a * γ₀ with hc1
  have hc10 : 0 ≤ c1 := by have := hE.Cw_nn; positivity
  set Kf : ℝ := Kb * (1 + Kb) with hKf
  have hKf0 : 0 ≤ Kf := by positivity
  refine ⟨β * Kf * c1 * (Cw * Λ * C0 + 2 * γ₀ * (1 + a * Λ * C0)),
    β * Kf * c1 * Cw * Λ * C1, by have := hE.Cw_nn; have := hE.C0_nn; positivity,
    by have := hE.Cw_nn; have := hE.C1_nn; positivity, ?_⟩
  intro V hVq hVγ lam K1 n m _ b hlam hK1 hKK hm hnl z hz
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hgood := pinD_goodF (μ := withDensityReal ρ) V hVq hqm hq0 hlam hK1.le b
  set ū : Torus d → ℝ := fun x => lam * c1 * (1 + ∑ k, wEnv s x (b k)) with hū
  have hū0 : ∀ x, 0 ≤ ū x := fun x => by
    have : 0 ≤ ∑ k, wEnv s x (b k) := Finset.sum_nonneg fun k _ => wEnv_pos s _ _
    simp only [hū]; positivity
  have hūm : Measurable ū := by
    simp only [hū]
    refine measurable_const.mul (measurable_const.add (Finset.measurable_sum _ fun k _ => ?_))
    exact measurable_wEnv_left s (b k)
  have hle : ∀ᵐ x ∂(withDensityReal ρ),
      (pinD (withDensityReal ρ) q lam K1 b x + ∫ w, pinD (withDensityReal ρ) q lam K1 b w ∂(withDensityReal ρ)) ≤ ū x :=
    Filter.Eventually.of_forall fun x => v0_le hE hγ₀ hqm hq0 V hVq hVγ hlam hK1 hKK hm b x
  have hJ1 : ∫⁻ x, ENNReal.ofReal (ū x * wEnv s z x) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (lam * c1 * (Λ * (C0 + ∑ k, C1 * ellEnv z (b k)))) := by
    calc ∫⁻ x, ENNReal.ofReal (ū x * wEnv s z x) ∂(withDensityReal ρ)
        = ∫⁻ x, ENNReal.ofReal (lam * c1) * ENNReal.ofReal ((1 + ∑ k, wEnv s x (b k)) * wEnv s z x)
            ∂(withDensityReal ρ) := by
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; simp only [hū]; ring
      _ = ENNReal.ofReal (lam * c1) * ∫⁻ x, ENNReal.ofReal ((1 + ∑ k, wEnv s x (b k)) * wEnv s z x)
            ∂(withDensityReal ρ) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (lam * c1) * ENNReal.ofReal (Λ * (C0 + ∑ k, C1 * ellEnv z (b k))) := by
          gcongr; exact J_w hE hΛ hΛ0 b z hz
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
  have hJ2 : ∫⁻ x, ENNReal.ofReal (ū x) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (lam * c1 * (1 + a * Λ * C0)) := by
    have hm' : (m : ℝ) ≤ a := by exact_mod_cast hm
    calc ∫⁻ x, ENNReal.ofReal (ū x) ∂(withDensityReal ρ)
        = ∫⁻ x, ENNReal.ofReal (lam * c1) * ENNReal.ofReal (1 + ∑ k, wEnv s x (b k))
            ∂(withDensityReal ρ) := by
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (lam * c1) * ∫⁻ x, ENNReal.ofReal (1 + ∑ k, wEnv s x (b k))
            ∂(withDensityReal ρ) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (lam * c1) * ENNReal.ofReal (1 + Λ * m * C0) := by
          gcongr; exact J_one hE hρ hΛ hΛ0 b
      _ ≤ ENNReal.ofReal (lam * c1) * ENNReal.ofReal (1 + a * Λ * C0) := by
          refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
          have := hE.C0_nn
          nlinarith [mul_nonneg hΛ0 this, mul_le_mul_of_nonneg_right hm' (mul_nonneg hΛ0 this)]
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
  have hmain := Tstar_weight_bound hE hρ V hVq hVγ hlam hK1.le hn hgood ū hūm hū0 hle z
    (J1 := lam * c1 * (Λ * (C0 + ∑ k, C1 * ellEnv z (b k))))
    (J2 := lam * c1 * (1 + a * Λ * C0)) (by
      have := hE.C0_nn; have := hE.C1_nn
      have : 0 ≤ ∑ k, C1 * ellEnv z (b k) := Finset.sum_nonneg fun k _ => mul_nonneg hE.C1_nn (ellEnv_nonneg _ _)
      positivity) (by have := hE.C0_nn; positivity) hJ1 hJ2
  refine hmain.trans ?_
  -- arithmetic
  set Sℓ : ℝ := ∑ k, ellEnv z (b k) with hSℓ
  have hSℓ0 : 0 ≤ Sℓ := Finset.sum_nonneg fun k _ => ellEnv_nonneg _ _
  have hsum : ∑ k, C1 * ellEnv z (b k) = C1 * Sℓ := by rw [hSℓ, Finset.mul_sum]
  rw [hsum]
  set X : ℝ := ((n : ℝ) - 1) * (K1 * (1 + K1) * lam) with hX
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hX0 : 0 ≤ X := by positivity
  have hXle : X ≤ β * Kf := by
    have h1 : K1 * (1 + K1) ≤ Kf := by
      rw [hKf]; exact mul_le_mul hKK (by linarith) (by linarith) hKb
    calc X = ((n : ℝ) - 1) * lam * (K1 * (1 + K1)) := by rw [hX]; ring
      _ ≤ (n * lam) * (K1 * (1 + K1)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          nlinarith
      _ ≤ β * Kf := mul_le_mul hnl h1 (by positivity) hβ
  have hCw0 := hE.Cw_nn
  have hC00 := hE.C0_nn
  have hC10 := hE.C1_nn
  calc ((n : ℝ) - 1) * ((K1 * (1 + K1) * lam * Cw) * (lam * c1 * (Λ * (C0 + C1 * Sℓ)))
        + (2 * (K1 * (1 + K1) * lam) * γ₀) * (lam * c1 * (1 + a * Λ * C0)))
      = X * (lam * c1 * (Cw * Λ * (C0 + C1 * Sℓ) + 2 * γ₀ * (1 + a * Λ * C0))) := by
        rw [hX]; ring
    _ ≤ (β * Kf) * (lam * c1 * (Cw * Λ * (C0 + C1 * Sℓ) + 2 * γ₀ * (1 + a * Λ * C0))) :=
        mul_le_mul_of_nonneg_right hXle (by positivity)
    _ = lam * (β * Kf * c1 * (Cw * Λ * C0 + 2 * γ₀ * (1 + a * Λ * C0)) + β * Kf * c1 * Cw * Λ * C1 * Sℓ) := by
        ring

end Steps


section Steps2

open HRS.External

variable {s γ₀ C0 C1 C2 cl Cw A' : ℝ} {q : Torus d → ℝ} {ρ : Torus d → ℝ} {Λ : ℝ}

theorem u1_step (hE : EnvFacts d s q γ₀ C0 C1 C2 cl Cw A') (hρ : SmoothPosDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) (hΛ0 : 0 ≤ Λ) (hγ₀ : 0 ≤ γ₀)
    (Kb β : ℝ) (hKb : 0 ≤ Kb) (hβ : 0 ≤ β) (a : ℕ) (P3 : ℝ) (hP3 : 0 ≤ P3) :
    ∃ P4 : ℝ, 0 ≤ P4 ∧ ∀ (V : WeakPotential (withDensityReal ρ))
      (hVq : ∀ x y, V.q x y = q (x - y)) (hVγ : V.γ = γ₀)
      (lam K1 : ℝ) (n m : ℕ) [NeZero n] (b : Fin m → Torus d),
      0 ≤ lam → 0 < K1 → K1 ≤ Kb → m ≤ a → (n : ℝ) * lam ≤ β →
      ∀ u : Torus d → ℝ, GoodF u →
        (∀ᵐ x ∂(withDensityReal ρ), u x ≤ lam * P3 * (1 + ∑ k, ellEnv x (b k))) →
        ∀ z : Torus d, Tstar (withDensityReal ρ) (fieldOmega V lam K1) n u z ≤ lam * P4 := by
  have : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu hρ
  set Kf : ℝ := Kb * (1 + Kb) with hKf
  have hKf0 : 0 ≤ Kf := by positivity
  have hCw0 := hE.Cw_nn
  have hC00 := hE.C0_nn
  have hC20 := hE.C2_nn
  have hcl0 := hE.cl_nn
  refine ⟨β * Kf * P3 * (Cw * Λ * (C0 + a * C2) + 2 * γ₀ * (1 + a * Λ * (cl * C0))),
    by positivity, ?_⟩
  intro V hVq hVγ lam K1 n m _ b hlam hK1 hKK hm hnl u hu hule z
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hm' : (m : ℝ) ≤ a := by exact_mod_cast hm
  set ū : Torus d → ℝ := fun x => lam * P3 * (1 + ∑ k, ellEnv x (b k)) with hū
  have hSℓ : ∀ x, 0 ≤ ∑ k, ellEnv x (b k) := fun x => Finset.sum_nonneg fun k _ => ellEnv_nonneg _ _
  have hū0 : ∀ x, 0 ≤ ū x := fun x => by
    have := hSℓ x
    simp only [hū]; positivity
  have hūm : Measurable ū := by
    simp only [hū]
    refine measurable_const.mul (measurable_const.add (Finset.measurable_sum _ fun k _ => ?_))
    exact measurable_ellEnv (b k)
  have hJ1 : ∫⁻ x, ENNReal.ofReal (ū x * wEnv s z x) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (lam * P3 * (Λ * (C0 + a * C2))) := by
    calc ∫⁻ x, ENNReal.ofReal (ū x * wEnv s z x) ∂(withDensityReal ρ)
        = ∫⁻ x, ENNReal.ofReal (lam * P3) * ENNReal.ofReal ((1 + ∑ k, ellEnv x (b k)) * wEnv s z x)
            ∂(withDensityReal ρ) := by
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; simp only [hū]; ring
      _ = ENNReal.ofReal (lam * P3) * ∫⁻ x, ENNReal.ofReal ((1 + ∑ k, ellEnv x (b k)) * wEnv s z x)
            ∂(withDensityReal ρ) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (lam * P3) * ENNReal.ofReal (Λ * (C0 + m * C2)) := by
          gcongr; exact J_ell hE hΛ hΛ0 b z
      _ ≤ ENNReal.ofReal (lam * P3) * ENNReal.ofReal (Λ * (C0 + a * C2)) := by
          refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
          exact mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_right hm' hC20]) hΛ0
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
  have hJ2 : ∫⁻ x, ENNReal.ofReal (ū x) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (lam * P3 * (1 + a * Λ * (cl * C0))) := by
    calc ∫⁻ x, ENNReal.ofReal (ū x) ∂(withDensityReal ρ)
        = ∫⁻ x, ENNReal.ofReal (lam * P3) * ENNReal.ofReal (1 + ∑ k, ellEnv x (b k))
            ∂(withDensityReal ρ) := by
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (lam * P3) * ∫⁻ x, ENNReal.ofReal (1 + ∑ k, ellEnv x (b k))
            ∂(withDensityReal ρ) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (lam * P3) * ENNReal.ofReal (1 + Λ * m * (cl * C0)) := by
          gcongr; exact J_one_ell hE hρ hΛ hΛ0 b
      _ ≤ ENNReal.ofReal (lam * P3) * ENNReal.ofReal (1 + a * Λ * (cl * C0)) := by
          refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
          have h0 : 0 ≤ Λ * (cl * C0) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hm' h0]
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
  have hmain := Tstar_weight_bound hE hρ V hVq hVγ hlam hK1.le hn hu ū hūm hū0 hule z
    (J1 := lam * P3 * (Λ * (C0 + a * C2))) (J2 := lam * P3 * (1 + a * Λ * (cl * C0)))
    (by positivity) (by positivity) hJ1 hJ2
  refine hmain.trans ?_
  set X : ℝ := ((n : ℝ) - 1) * (K1 * (1 + K1) * lam) with hX
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hX0 : 0 ≤ X := by positivity
  have hXle : X ≤ β * Kf := by
    have h1 : K1 * (1 + K1) ≤ Kf := by
      rw [hKf]; exact mul_le_mul hKK (by linarith) (by linarith) hKb
    calc X = ((n : ℝ) - 1) * lam * (K1 * (1 + K1)) := by rw [hX]; ring
      _ ≤ (n * lam) * (K1 * (1 + K1)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          nlinarith
      _ ≤ β * Kf := mul_le_mul hnl h1 (by positivity) hβ
  calc ((n : ℝ) - 1) * ((K1 * (1 + K1) * lam * Cw) * (lam * P3 * (Λ * (C0 + a * C2)))
        + (2 * (K1 * (1 + K1) * lam) * γ₀) * (lam * P3 * (1 + a * Λ * (cl * C0))))
      = X * (lam * P3 * (Cw * Λ * (C0 + a * C2) + 2 * γ₀ * (1 + a * Λ * (cl * C0)))) := by
        rw [hX]; ring
    _ ≤ (β * Kf) * (lam * P3 * (Cw * Λ * (C0 + a * C2) + 2 * γ₀ * (1 + a * Λ * (cl * C0)))) :=
        mul_le_mul_of_nonneg_right hXle (by positivity)
    _ = _ := by ring

end Steps2


section Assembly

open HRS.External

variable {s γ₀ C0 C1 C2 cl Cw A' : ℝ} {q : Torus d → ℝ} {ρ : Torus d → ℝ} {Λ : ℝ}

theorem ae_not_mem_pins (hd : 1 ≤ d) (ρ : Torus d → ℝ) {m : ℕ} (b : Fin m → Torus d) :
    ∀ᵐ z ∂(withDensityReal ρ), ∀ k, z ≠ b k := by
  rw [ae_all_iff]
  intro k
  rw [ae_iff]
  have : {a : Torus d | ¬ a ≠ b k} = {b k} := by ext x; simp
  rw [this]
  exact withDensity_absolutelyContinuous _ _ (volume_singleton_torus hd (b k))

theorem final_arith {lam c1 P0 P1 P4 A' cl Sq a : ℝ} (hlam : 0 ≤ lam) (hc1 : 0 ≤ c1) (hP0 : 0 ≤ P0)
    (hP1 : 0 ≤ P1) (hP4 : 0 ≤ P4) (hA : 0 ≤ A') (hcl : 0 ≤ cl) (hSq : 0 ≤ Sq) (ha : 0 ≤ a) :
    lam * (c1 + c1 * A' * (a + Sq)) + lam * ((P0 + P1) + (P0 + P1) * cl * A' * (a + Sq))
        + 2 * (lam * P4)
      ≤ (c1 + (P0 + P1) + 2 * P4 + (c1 * A' + (P0 + P1) * cl * A') * (a + 1)) * lam * (1 + Sq) := by
  have hX : 0 ≤ c1 * A' + (P0 + P1) * cl * A' := by positivity
  have hdiff : (c1 + (P0 + P1) + 2 * P4 + (c1 * A' + (P0 + P1) * cl * A') * (a + 1)) * lam * (1 + Sq)
      - (lam * (c1 + c1 * A' * (a + Sq)) + lam * ((P0 + P1) + (P0 + P1) * cl * A' * (a + Sq))
          + 2 * (lam * P4)) = lam * ((c1 * A' + (P0 + P1) * cl * A')
          + (c1 + (P0 + P1) + 2 * P4 + (c1 * A' + (P0 + P1) * cl * A') * a) * Sq) := by ring
  have hpos : 0 ≤ lam * ((c1 * A' + (P0 + P1) * cl * A')
          + (c1 + (P0 + P1) + 2 * P4 + (c1 * A' + (P0 + P1) * cl * A') * a) * Sq) := by positivity
  linarith

theorem tstar_bounds (hd : 1 ≤ d) (hE : EnvFacts d s q γ₀ C0 C1 C2 cl Cw A') (hρ : SmoothPosDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) (hΛ0 : 0 ≤ Λ) (hq0 : ∀ z, 0 ≤ q z) (hqm : Measurable q) (hγ₀ : 0 ≤ γ₀)
    (Kb β : ℝ) (hKb : 0 ≤ Kb) (hβ : 0 ≤ β) (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : WeakPotential (withDensityReal ρ))
      (hVq : ∀ x y, V.q x y = q (x - y)) (hVγ : V.γ = γ₀)
      (lam K1 : ℝ) (n m : ℕ) [NeZero n] (b : Fin m → Torus d),
      0 ≤ lam → 0 < K1 → K1 ≤ Kb → m ≤ a → (n : ℝ) * lam ≤ β →
      ∃ B2 : ℝ,
        (∀ z, Tstar (withDensityReal ρ) (fieldOmega V lam K1) n
          (Tstar (withDensityReal ρ) (fieldOmega V lam K1) n
            (fun z => pinD (withDensityReal ρ) q lam K1 b z
              + ∫ w, pinD (withDensityReal ρ) q lam K1 b w ∂(withDensityReal ρ))) z ≤ B2) ∧
        (∀ᵐ z ∂(withDensityReal ρ),
          (pinD (withDensityReal ρ) q lam K1 b z
              + ∫ w, pinD (withDensityReal ρ) q lam K1 b w ∂(withDensityReal ρ))
            + Tstar (withDensityReal ρ) (fieldOmega V lam K1) n
                (fun z => pinD (withDensityReal ρ) q lam K1 b z
                  + ∫ w, pinD (withDensityReal ρ) q lam K1 b w ∂(withDensityReal ρ)) z
            + 2 * B2 ≤ C * lam * (1 + ∑ k, q (z - b k))) := by
  have : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu hρ
  obtain ⟨P0, P1, hP0, hP1, hu0⟩ := u0_step hE hρ hΛ hΛ0 hq0 hqm hγ₀ Kb β hKb hβ a
  obtain ⟨P4, hP4, hu1⟩ := u1_step hE hρ hΛ hΛ0 hγ₀ Kb β hKb hβ a (P0 + P1)
    (add_nonneg hP0 hP1)
  set c1 : ℝ := Kb * Cw + (Kb + 2 * Kb ^ 2) * a * γ₀ with hc1
  have hCw0 := hE.Cw_nn
  have hA0 := hE.A'_nn
  have hcl0 := hE.cl_nn
  have hc10 : 0 ≤ c1 := by positivity
  have hX0 : 0 ≤ c1 * A' + (P0 + P1) * cl * A' := by positivity
  refine ⟨c1 + (P0 + P1) + 2 * P4 + (c1 * A' + (P0 + P1) * cl * A') * (a + 1), by positivity, ?_⟩
  intro V hVq hVγ lam K1 n m _ b hlam hK1 hKK hm hnl
  have hker := fieldOmega_ker (μ := withDensityReal ρ) V hlam hK1.le
  have hgood := pinD_goodF (μ := withDensityReal ρ) V hVq hqm hq0 hlam hK1.le b
  have hu1good := hgood.Tstar (n := n) hker
  refine ⟨lam * P4, fun z => ?_, ?_⟩
  · refine hu1 V hVq hVγ lam K1 n m b hlam hK1 hKK hm hnl _ hu1good ?_ z
    filter_upwards [ae_not_mem_pins hd ρ b] with x hx
    refine (hu0 V hVq hVγ lam K1 n m b hlam hK1 hKK hm hnl x hx).trans ?_
    have hS : 0 ≤ ∑ k, ellEnv x (b k) := Finset.sum_nonneg fun k _ => ellEnv_nonneg _ _
    nlinarith [mul_nonneg hlam hP0, mul_nonneg hlam hP1, mul_nonneg (mul_nonneg hlam hP0) hS]
  · filter_upwards [ae_not_mem_pins hd ρ b] with z hz
    have h1 := v0_le hE hγ₀ hqm hq0 V hVq hVγ hlam hK1 hKK hm b z
    have h2 := hu0 V hVq hVγ lam K1 n m b hlam hK1 hKK hm hnl z hz
    set Sq : ℝ := ∑ k, q (z - b k) with hSq
    have hSq0 : 0 ≤ Sq := Finset.sum_nonneg fun k _ => hq0 _
    have hSw : ∑ k, wEnv s z (b k) ≤ A' * (m + Sq) := by
      calc ∑ k, wEnv s z (b k) ≤ ∑ k, A' * (1 + q (z - b k)) :=
            Finset.sum_le_sum fun k _ => hE.low z (b k)
        _ = A' * (m + Sq) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib]; simp [hSq]
    have hSl : ∑ k, ellEnv z (b k) ≤ cl * (A' * (m + Sq)) := by
      calc ∑ k, ellEnv z (b k) ≤ ∑ k, cl * wEnv s z (b k) :=
            Finset.sum_le_sum fun k _ => hE.ell_le z (b k)
        _ = cl * ∑ k, wEnv s z (b k) := by rw [Finset.mul_sum]
        _ ≤ cl * (A' * (m + Sq)) := mul_le_mul_of_nonneg_left hSw hcl0
    have hm' : (m : ℝ) ≤ a := by exact_mod_cast hm
    have hSl0 : 0 ≤ ∑ k, ellEnv z (b k) := Finset.sum_nonneg fun k _ => ellEnv_nonneg _ _
    have hSw0 : 0 ≤ ∑ k, wEnv s z (b k) := Finset.sum_nonneg fun k _ => wEnv_pos s _ _
    -- final arithmetic
    set Tz := Tstar (withDensityReal ρ) (fieldOmega V lam K1)  n
      (fun z => pinD (withDensityReal ρ) q lam K1 b z
        + ∫ w, pinD (withDensityReal ρ) q lam K1 b w ∂(withDensityReal ρ)) z with hTz
    have hA1 : lam * c1 * (1 + ∑ k, wEnv s z (b k)) ≤ lam * (c1 + c1 * A' * (a + Sq)) := by
      have : 1 + ∑ k, wEnv s z (b k) ≤ 1 + A' * (a + Sq) := by
        have : A' * (m + Sq) ≤ A' * (a + Sq) := mul_le_mul_of_nonneg_left (by linarith) hA0
        linarith
      calc lam * c1 * (1 + ∑ k, wEnv s z (b k)) ≤ lam * c1 * (1 + A' * (a + Sq)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have hA2 : lam * (P0 + P1 * ∑ k, ellEnv z (b k))
        ≤ lam * ((P0 + P1) + (P0 + P1) * cl * A' * (a + Sq)) := by
      have h3 : ∑ k, ellEnv z (b k) ≤ cl * (A' * (a + Sq)) := by
        refine hSl.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hA0) hcl0)
      have : P0 + P1 * ∑ k, ellEnv z (b k) ≤ (P0 + P1) + (P0 + P1) * cl * A' * (a + Sq) := by
        have h4 : P1 * ∑ k, ellEnv z (b k) ≤ P1 * (cl * (A' * (a + Sq))) :=
          mul_le_mul_of_nonneg_left h3 hP1
        have h5 : P1 * (cl * (A' * (a + Sq))) ≤ (P0 + P1) * cl * A' * (a + Sq) := by
          have : 0 ≤ P0 * (cl * A' * (a + Sq)) := by positivity
          nlinarith [this]
        nlinarith [h4, h5]
      exact mul_le_mul_of_nonneg_left this hlam
    have hfin := final_arith (a := (a : ℝ)) hlam hc10 hP0 hP1 hP4 hA0 hcl0 hSq0 (Nat.cast_nonneg a)
    calc _ ≤ lam * c1 * (1 + ∑ k, wEnv s z (b k)) + lam * (P0 + P1 * ∑ k, ellEnv z (b k)) + 2 * (lam * P4) := by
          linarith
      _ ≤ _ := by linarith

end Assembly


section Env

variable {s : ℝ}

theorem one_add_dist_le_wEnv (hs : 0 < s) (x y : Torus d) :
    1 + Torus.eucDist x y ^ (-s) ≤ wEnv s x y := by
  unfold wEnv rTrunc
  by_cases h : Torus.eucDist x y ≤ 1
  · rw [min_eq_right h]
  · push Not at h
    rw [min_eq_left h.le, Real.one_rpow]
    have : Torus.eucDist x y ^ (-s) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos h.le (by linarith)
    linarith

theorem exists_env {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (q : Torus d → ℝ)
    (hq0 : ∀ z, 0 ≤ q z) (Cq : ℝ)
    (hqenv : ∀ z, z ≠ 0 → q z ≤ Cq * (1 + Torus.eucDist z 0 ^ (-s)))
    (hdec : ∃ k : Torus d → ℝ, Torus.IsSmooth k ∧ ∃ c : ℝ, ∀ z, z ≠ 0 →
      periodicRiesz d s z = q z + k z + c) (γ₀ : ℝ) (hγ₀ : 0 ≤ γ₀) :
    ∃ C0 C1 C2 cl Cw A' : ℝ, EnvFacts d s q γ₀ C0 C1 C2 cl Cw A' := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  -- a lower bound making `periodicRiesz + c'` nonnegative
  obtain ⟨c', hc'⟩ := periodicRiesz_ge (d := d) (s := s) hd hs0.le hsd
  have hc'pos : ∀ z, 0 ≤ periodicRiesz d s z + c' := fun z => by linarith [hc' z]
  obtain ⟨C1, hC10, hC1⟩ := PairCorrAux.twopole_vol (d := d) hd hcrit
  obtain ⟨C2, hC20, hC2⟩ := wEll_vol hd hcrit c' hc'pos
  obtain ⟨A, hA0, hAw⟩ := PairCorrAux.wEnv_le_gPlus hd hcrit c' hc'pos
  obtain ⟨k, hk, c0, hkc⟩ := hdec
  have hkc' : Continuous k := PoleCavityAux.continuous_of_lift'
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift k) from hk).continuous
  obtain ⟨Bk, hBk⟩ := isCompact_univ.exists_bound_of_continuousOn (f := k) hkc'.continuousOn
  have hBk' : ∀ z, |k z| ≤ |Bk| := fun z => by
    have := hBk z trivial
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  set C0 : ℝ := PairCorrAux.cdR d * ((1 / d + 1 / s) * 1 ^ s) + 2 with hC0
  have hC0n : 0 ≤ C0 := by
    have := PairCorrAux.cdR_nonneg d
    have : 0 ≤ (1 / (d : ℝ) + 1 / s) * 1 ^ s := by positivity
    positivity
  set cl : ℝ := 1 + 4 / s with hcl
  set Cw : ℝ := max Cq 0 + q 0 + γ₀ with hCw
  have hq00 := hq0 0
  have hCw0 : 0 ≤ Cw := by have := le_max_right Cq 0; positivity
  set A' : ℝ := max 1 (A * (1 + |Bk| + |c0| + |c'|)) with hA'
  refine ⟨C0, C1, C2, cl, Cw, A', ?_⟩
  refine ⟨hC0n, hC10, hC20, by positivity, hCw0, (zero_le_one.trans (le_max_left _ _)),
    fun z => PairCorrAux.radial_B0 hd hcrit z, ?_, ?_, fun x y => (ellEnv_le_wEnv hs0 x y).1, ?_, ?_⟩
  · intro z b hzb
    exact hC1 z b hzb
  · intro z b
    exact hC2 z b
  · -- kernel envelope
    intro z x
    have hw1 := PairCorrAux.one_le_wEnv s z x
    by_cases hzx : z = x
    · subst hzx
      have h0 : z - z = 0 := sub_self z
      rw [h0]
      have : wEnv s z z = 1 := by
        unfold wEnv rTrunc
        rw [PairCorrAux.eucDist_self' z, min_eq_right zero_le_one] 
        simp [Real.zero_rpow (by linarith : -s ≠ 0)]
      rw [this]
      have := le_max_right Cq 0
      nlinarith [hq00, hγ₀, le_max_left Cq 0]
    · have hne : z - x ≠ 0 := sub_ne_zero.mpr hzx
      have h1 := hqenv (z - x) hne
      have h2 : 1 + Torus.eucDist (z - x) 0 ^ (-s) ≤ wEnv s z x := by
        rw [← PairCorrAux.eucDist_sub_zero]; exact one_add_dist_le_wEnv hs0 z x
      have h3 : Cq * (1 + Torus.eucDist (z - x) 0 ^ (-s)) ≤ max Cq 0 * wEnv s z x := by
        have h4 : 0 ≤ 1 + Torus.eucDist (z - x) 0 ^ (-s) := by
          have : 0 ≤ Torus.eucDist (z - x) 0 ^ (-s) := Real.rpow_nonneg (PairCorrAux.eucDist_nonneg' _ _) _
          linarith
        calc Cq * (1 + Torus.eucDist (z - x) 0 ^ (-s)) ≤ max Cq 0 * (1 + Torus.eucDist (z - x) 0 ^ (-s)) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) h4
          _ ≤ max Cq 0 * wEnv s z x := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      have h5 : γ₀ ≤ γ₀ * wEnv s z x := by nlinarith
      have h6 : q 0 * wEnv s z x ≥ 0 := by positivity
      calc q (z - x) + γ₀ ≤ max Cq 0 * wEnv s z x + γ₀ * wEnv s z x := by linarith
        _ ≤ Cw * wEnv s z x := by rw [hCw]; nlinarith
  · -- lower envelope
    intro z x
    by_cases hzx : z = x
    · subst hzx
      have : wEnv s z z = 1 := by
        unfold wEnv rTrunc
        rw [PairCorrAux.eucDist_self' z, min_eq_right zero_le_one]
        simp [Real.zero_rpow (by linarith : -s ≠ 0)]
      rw [this]
      have := le_max_left 1 (A * (1 + |Bk| + |c0| + |c'|))
      nlinarith [hq0 (z - z)]
    · have hne : z - x ≠ 0 := sub_ne_zero.mpr hzx
      have h1 := hAw z x
      have h2 : gPlus d s c' (z - x) ≤ q (z - x) + |Bk| + |c0| + |c'| := by
        unfold gPlus
        rw [hkc (z - x) hne]
        have := hBk' (z - x)
        have := le_abs_self (k (z - x))
        have := le_abs_self c0
        have := le_abs_self c'
        linarith
      have h3 : wEnv s z x ≤ A * (1 + (q (z - x) + |Bk| + |c0| + |c'|)) :=
        h1.trans (mul_le_mul_of_nonneg_left (by linarith) hA0.le)
      have hq := hq0 (z - x)
      have hB : 0 ≤ |Bk| + |c0| + |c'| := by positivity
      calc wEnv s z x ≤ A * (1 + (q (z - x) + |Bk| + |c0| + |c'|)) := h3
        _ ≤ (A * (1 + |Bk| + |c0| + |c'|)) * (1 + q (z - x)) := by nlinarith [mul_nonneg hA0.le hq, mul_nonneg hA0.le hB]
        _ ≤ A' * (1 + q (z - x)) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)

end Env


section PinStep

open HRS.External

/-- The smallness threshold `γ₀` of Lemma 4.10 (depends only on `β`). -/
def pinGamma (β : ℝ) : ℝ := 1 / (16 * Real.exp 10 * β)

theorem pinGamma_pos {β : ℝ} (hβ : 0 < β) : 0 < pinGamma β := by
  unfold pinGamma; positivity

theorem beta_mul_pinGamma {β : ℝ} (hβ : 0 < β) : β * pinGamma β = 1 / (16 * Real.exp 10) := by
  unfold pinGamma; field_simp

theorem pin_numeric {g K1 E5 : ℝ} (hE5 : 1 ≤ E5) (hg : g = 1 / (16 * (E5 * E5))) (hK : 0 ≤ K1)
    (hKE : K1 ≤ E5) : 4 * K1 * g < 1 ∧ 4 * (K1 * (1 + K1)) * g ≤ 1 / 2 := by
  have hE0 : 0 < E5 := by linarith
  have hg16 : 16 * (E5 * E5) * g = 1 := by rw [hg]; field_simp
  have hg0 : 0 < g := by rw [hg]; positivity
  have h1 : 4 * K1 * g ≤ 4 * E5 * g := by nlinarith
  have h2 : 4 * (K1 * (1 + K1)) * g ≤ 4 * (E5 * (1 + E5)) * g := by
    have : K1 * (1 + K1) ≤ E5 * (1 + E5) := mul_le_mul hKE (by linarith) (by linarith) hE0.le
    nlinarith
  have h3 : 4 * E5 * g * (4 * E5) = 1 := by nlinarith [hg16]
  have h4 : 4 * E5 * g ≤ 1 / 4 := by nlinarith [h3, hg0, hE0]
  constructor
  · linarith
  · have h5 : 4 * (E5 * (1 + E5)) * g = 4 * E5 * g + 4 * E5 * g * E5 := by ring
    have h6 : 4 * E5 * g * E5 = 1 / 4 := by nlinarith [h3]
    nlinarith [h2, h5, h6, h4]

theorem pinD_props {μ : Measure (Torus d)} {q : Torus d → ℝ} (hqm : Measurable q)
    (hq0 : ∀ z, 0 ≤ q z) {lam K1 : ℝ} (hlam : 0 ≤ lam) (hK1 : 0 ≤ K1) {m : ℕ} (b : Fin m → Torus d) :
    Measurable (pinD μ q lam K1 b) ∧ (∀ z, 0 ≤ pinD μ q lam K1 b z) ∧ ∀ z, pinD μ q lam K1 b z ≤ K1 := by
  have hδm := measurable_pinDelta hqm lam b
  refine ⟨?_, fun z => ?_, fun z => min_le_left _ _⟩
  · unfold pinD
    exact measurable_const.min ((measurable_const.mul hδm).add measurable_const)
  · unfold pinD
    exact le_min hK1 (add_nonneg (mul_nonneg hK1 (pinDelta_nonneg hq0 hlam b z))
      (mul_nonneg (mul_nonneg hK1 hK1) (integral_nonneg fun w => pinDelta_nonneg hq0 hlam b w)))

theorem pin_step_set {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (q : Torus d → ℝ) (hq0 : ∀ z, 0 ≤ q z)
    (hqm : Measurable q) (Cq : ℝ)
    (hqenv : ∀ z, z ≠ 0 → q z ≤ Cq * (1 + Torus.eucDist z 0 ^ (-s)))
    (hdec : ∃ k : Torus d → ℝ, Torus.IsSmooth k ∧ ∃ c : ℝ, ∀ z, z ≠ 0 →
      periodicRiesz d s z = q z + k z + c) (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (V : WeakPotential (withDensityReal ρ)) (_ : ∀ x y, V.q x y = q (x - y))
        (_ : V.γ = pinGamma β) (_ : V.M = β * pinGamma β + 1) (_ : V.M' = 1)
        (N n m : ℕ) [NeZero n], a + 1 ≤ N → n ≤ N → m ≤ a + 1 → ∀ (b : Fin m → Torus d)
        (ψ ψ' : Torus d → ℝ) (M₁ M₁' : ℝ), IsField (withDensityReal ρ) ψ V.M M₁ →
        IsField (withDensityReal ρ) ψ' V.M M₁' → M₁ ≤ 1 + β * pinGamma β →
        M₁' ≤ 1 + β * pinGamma β → (∀ z, |ψ' z - ψ z| ≤ pinDelta q (β / N) b z) →
        ∀ (i0 : Fin n) (A : Set (Torus d)), MeasurableSet A →
        |((fieldLaw V ψ' (β / N) n).map (fun x => x i0)).real A
          - ((fieldLaw V ψ (β / N) n).map (fun x => x i0)).real A|
          ≤ ∫ z in A, C * (β / N) * (1 + ∑ k, q (z - b k)) ∂(withDensityReal ρ) := by
  have : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu hρ
  set γ₀ := pinGamma β with hγ₀def
  have hγ₀ : 0 < γ₀ := pinGamma_pos hβ
  obtain ⟨C0, C1, C2, cl, Cw, A', hE⟩ := exists_env hd hcrit q hq0 Cq hqenv hdec γ₀ hγ₀.le
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  obtain ⟨C, hC0, hC⟩ := tstar_bounds (by omega) hE hρ hΛ hΛ0.le hq0 hqm hγ₀.le
    (Real.exp 5) β (Real.exp_pos 5).le hβ.le (a + 1)
  refine ⟨C, hC0, ?_⟩
  intro V hVq hVγ hVM hVM' N n m _ hNa hnN hma b ψ ψ' M₁ M₁' hψ hψ' hM₁ hM₁' hdiff i0 A hA
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hnl : (n : ℝ) * (β / N) ≤ β := by
    have : (n : ℝ) ≤ N := by exact_mod_cast hnN
    calc (n : ℝ) * (β / N) = (n / N) * β := by ring
      _ ≤ 1 * β := by
          refine mul_le_mul_of_nonneg_right ?_ hβ.le
          rw [div_le_one hNpos]; exact this
      _ = β := one_mul _
  set Λf : ℝ := 1 + 2 * β * γ₀ with hΛf
  have hg : β * γ₀ = 1 / (16 * Real.exp 10) := beta_mul_pinGamma hβ
  have hE5 : 1 ≤ Real.exp 5 := Real.one_le_exp (by norm_num)
  have hexp10 : Real.exp 10 = Real.exp 5 * Real.exp 5 := by rw [← Real.exp_add]; norm_num
  have hg1 : β * γ₀ ≤ 1 := by
    rw [hg]; rw [div_le_one (by positivity)]
    nlinarith [Real.exp_pos 10, Real.add_one_le_exp (10 : ℝ)]
  set K1 : ℝ := Real.exp (V.M + Λf) with hK1
  have hK1pos : 0 < K1 := Real.exp_pos _
  have hK1le : K1 ≤ Real.exp 5 := by
    rw [hK1]
    refine Real.exp_le_exp.2 ?_
    rw [hVM, hΛf]; nlinarith
  have hnum := pin_numeric (g := β * γ₀) hE5 (by rw [hg, hexp10]) hK1pos.le hK1le
  have hlg : (n : ℝ) * (β / N) * γ₀ ≤ β * γ₀ := mul_le_mul_of_nonneg_right hnl hγ₀.le
  have hΛ1 : M₁ + (β / N) * n * V.γ ≤ Λf := by
    rw [hVγ, hΛf]
    have : (β / N) * n * γ₀ = (n : ℝ) * (β / N) * γ₀ := by ring
    nlinarith
  have hΛ2 : M₁' + (β / N) * n * V.γ ≤ Λf := by
    rw [hVγ, hΛf]
    have : (β / N) * n * γ₀ = (n : ℝ) * (β / N) * γ₀ := by ring
    nlinarith
  have hr : (n : ℝ) * (4 * Real.exp (V.M + Λf) * (β / N) * V.γ) < 1 := by
    rw [hVγ, ← hK1]
    have : (n : ℝ) * (4 * K1 * (β / N) * γ₀) = 4 * K1 * ((n : ℝ) * (β / N) * γ₀) := by ring
    rw [this]
    calc 4 * K1 * ((n : ℝ) * (β / N) * γ₀) ≤ 4 * K1 * (β * γ₀) :=
          mul_le_mul_of_nonneg_left hlg (by positivity)
      _ < 1 := hnum.1
  have hε : ((n : ℝ) - 1) * (2 * (2 * (Real.exp (V.M + Λf) * (1 + Real.exp (V.M + Λf)) * (β / N))
      * V.γ)) ≤ 1 / 2 := by
    rw [hVγ, ← hK1]
    have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
      linarith
    have hn2 : ((n : ℝ) - 1) * (β / N) * γ₀ ≤ β * γ₀ := by
      refine le_trans (mul_le_mul_of_nonneg_right ?_ hγ₀.le) hlg
      nlinarith [div_nonneg hβ.le hNpos.le]
    have e : ((n : ℝ) - 1) * (2 * (2 * (K1 * (1 + K1) * (β / N)) * γ₀))
        = 4 * (K1 * (1 + K1)) * (((n : ℝ) - 1) * (β / N) * γ₀) := by ring
    rw [e]
    calc 4 * (K1 * (1 + K1)) * (((n : ℝ) - 1) * (β / N) * γ₀) ≤ 4 * (K1 * (1 + K1)) * (β * γ₀) :=
          mul_le_mul_of_nonneg_left hn2 (by positivity)
      _ ≤ 1 / 2 := hnum.2
  obtain ⟨B2, hB2, hΨ⟩ := hC V hVq hVγ (β / N) K1 n m b hlam hK1pos hK1le hma hnl
  obtain ⟨hDm, hD0, hDb⟩ := pinD_props (μ := withDensityReal ρ) hqm hq0 hlam hK1pos.le b
  have hδi := integrable_pinDelta V hVq (β / N) b
  have hI : ∫ w, |ψ' w - ψ w| ∂(withDensityReal ρ) ≤ ∫ w, pinDelta q (β / N) b w ∂(withDensityReal ρ) :=
    integral_mono (hψ'.integrable.sub hψ.integrable).abs hδi fun w => hdiff w
  have hD : ∀ z, min (Real.exp (V.M + Λf)) (Real.exp (V.M + Λf) * |ψ' z - ψ z|
        + Real.exp (V.M + Λf) * Real.exp (V.M + Λf) * ∫ w, |ψ' w - ψ w| ∂(withDensityReal ρ))
      ≤ pinD (withDensityReal ρ) q (β / N) K1 b z := by
    intro z
    rw [← hK1]
    unfold pinD
    exact min_le_min le_rfl (add_le_add (mul_le_mul_of_nonneg_left (hdiff z) hK1pos.le)
      (mul_le_mul_of_nonneg_left hI (by positivity)))
  have hΨi : Integrable (fun z => C * (β / N) * (1 + ∑ k, q (z - b k))) (withDensityReal ρ) := by
    refine Integrable.const_mul ((integrable_const _).add (integrable_finsetSum _ fun k _ => ?_)) _
    have := integrable_q_left V (b k)
    simpa [hVq] using this
  have hfin := field_marginal_set_bound (V := V) hψ hψ' hlam hΛ1 hΛ2 hr hε hDm hD0 hDb hD
    (B2 := B2) (by rw [← hK1]; exact hB2) hΨi (by rw [← hK1]; exact hΨ) i0 hA
  exact hfin

end PinStep


section DimStep

open HRS.External HRS.External.RefMarg

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem pinnedLaw_isEmpty (V : WeakPotential μ) (lam : ℝ) (n : ℕ) {B : Type*} [Fintype B] [IsEmpty B]
    (a : B → E) : pinnedLaw V lam n a = fieldLaw V V.φ lam n := by
  unfold pinnedLaw
  congr 1
  funext z
  simp [pinField]

/-- Density bound from a measure bound. -/
theorem ae_rnDeriv_le_of_le {ν : Measure E} [IsFiniteMeasure ν] (hν : ν ≪ μ) {K : ℝ} (hK : 0 ≤ K)
    (h : ν ≤ ENNReal.ofReal K • μ) : ∀ᵐ z ∂μ, (ν.rnDeriv μ z).toReal ≤ K := by
  have hm : Measurable (ν.rnDeriv μ) := Measure.measurable_rnDeriv _ _
  have h1 : ν.rnDeriv μ ≤ᵐ[μ] fun _ => ENNReal.ofReal K := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite hm fun A hA _ => ?_
    rw [Measure.setLIntegral_rnDeriv hν]
    calc ν A ≤ (ENNReal.ofReal K • μ) A := h A
      _ = ∫⁻ _ in A, ENNReal.ofReal K ∂μ := by
          rw [Measure.smul_apply, smul_eq_mul, setLIntegral_const, mul_comm]
  filter_upwards [h1] with z hz
  exact ENNReal.toReal_le_of_le_ofReal hK hz

/-- Marginal density bound for pinned laws with `n ≤ N` free coordinates and `|B|` pins. -/
theorem pinned_marginal_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hnN : n ≤ N) {B : Type*} [Fintype B] (a : B → E) (i : Fin n) :
    (pinnedLaw V (β / N) n a).map (fun y => y i)
      ≤ ENNReal.ofReal (Real.exp (V.M + V.M' + β * (1 + Fintype.card B) * V.γ)) • μ := by
  set N' : ℕ := N + Fintype.card B with hN'
  have hN'0 : 0 < N' := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hN'r : (0 : ℝ) < N' := by exact_mod_cast hN'0
  set β' : ℝ := β * N' / N with hβ'
  have hβ'0 : 0 ≤ β' := by positivity
  have hrat : β' / N' = β / N := by rw [hβ']; field_simp
  have h := marginal_le_smul (μ := μ) V hβ'0 hN'0 (by omega : n + Fintype.card B ≤ N') a i
  rw [hrat] at h
  refine h.trans (Measure.le_iff'.2 fun A => ?_)
  simp only [Measure.smul_apply, smul_eq_mul]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) le_rfl
  have hγ := V.γ_nonneg
  have : β' ≤ β * (1 + Fintype.card B) := by
    rw [hβ', hN', div_le_iff₀ hNr]
    push_cast
    have : (Fintype.card B : ℝ) ≤ (Fintype.card B) * N := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN0
      nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card B)]
    nlinarith
  nlinarith

end DimStep

end PinAux

end HRS
