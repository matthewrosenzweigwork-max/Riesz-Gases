/-
# HRS.Equilibrium.PairMomentsL2 -- the second level of the three-particle estimate, assembled (EQ-01b)
-/
import HRS.Equilibrium.PairMomentsT2

open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.PairMom

open HRS HRS.External HRS.Quad HRS.External.PoleVar

variable {d : ℕ} {s : ℝ}

theorem ellEnv_symm' (x y : Torus d) : ellEnv x y = ellEnv y x := by
  unfold ellEnv; rw [PairCorrAux.rTrunc_symm]

theorem measurable_ellEnv_right (x : Torus d) : Measurable (fun u : Torus d => ellEnv x u) := by
  have : (fun u : Torus d => ellEnv x u) = fun u => ellEnv u x := funext fun u => ellEnv_symm' x u
  rw [this]; exact PinAux.measurable_ellEnv x

theorem measurable_wEll {N : ℕ} (x : Torus d) :
    Measurable (fun u : Torus d => wEnv s x u * (logEN N + ellEnv x u)) := by
  exact (PairCorrAux.measurable_wEnv s x).mul (measurable_const.add (measurable_ellEnv_right x))


section L2Int

/-- The integrals against the one-pin pole weight needed at the second level. -/
theorem l2_integrals (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (Mmax M'max γmax Cq : ℝ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V → ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      (∀ y : Torus d, ∫⁻ z, ENNReal.ofReal (aFun s c (β / N) y z) ∂(withDensityReal ρ) ≤
          ENNReal.ofReal (C * logEN N)) ∧
      (∫⁻ u, ENNReal.ofReal (wEnv s x u ^ 2) * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
          pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u)) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal (C * logEN N)) ∧
      (∫⁻ u, ENNReal.ofReal (wEnv s x u * (logEN N + ellEnv x u)) * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
          pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u)) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal (C * logEN N)) ∧
      (∫⁻ u, ENNReal.ofReal (wEnv s x u ^ 2 * (logEN N + ellEnv x u) ^ 2) * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
          pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u)) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal (C * logEN N ^ 3)) ∧
      (∫⁻ u, Jfun s c (β / N) (withDensityReal ρ) x u * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
          pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u)) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal (C * logEN N ^ 2)) := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨C1, hC1⟩ := critical_envelope_integrals hd hcrit β hβ ρ hρ c hc 1 one_pos
  obtain ⟨C0, hC00, hC0⟩ := pole_w_integrals hd hcrit β hβ ρ hρ c hc Mmax M'max γmax Cq hCq
  obtain ⟨Cw, hCw, hCwF⟩ := lintegral_wEll_exp hd hcrit β hβ ρ hρ c hc
  obtain ⟨B, hB0, hB⟩ := lintegral_mu_w hd hcrit
  obtain ⟨Cl, hCl0, hCl⟩ := lintegral_mu_wEll hd hcrit
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  set E0 : ℝ := Real.exp (M'max + β * max γmax 0 + Mmax) with hE0
  have hE0p : 0 < E0 := Real.exp_pos _
  set Ep : ℝ := Real.exp (M'max + β * max γmax 0 + Mmax + β * Cq) with hEp
  have hEpp : 0 < Ep := Real.exp_pos _
  set B1 : ℝ := max C1 0 with hB1
  have hB10 : 0 ≤ B1 := le_max_right _ _
  set C : ℝ := B1 + C0 + E0 * Λ * (B + Cl) + Ep * Cw + E0 * B1 ^ 2 with hC
  have hC0' : 0 ≤ C := by positivity
  refine ⟨C, hC0', fun V hV N hN x => ?_⟩
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hLe := logEN_pos' (N := N) (by omega)
  have hL0 : 0 ≤ logEN N := by linarith
  have hlam0 : 0 ≤ β / N := by positivity
  have hlamβ : β / N ≤ β := by
    rw [div_le_iff₀ hNp]
    have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  have hI : ∀ y : Torus d, ∫⁻ z, ENNReal.ofReal (aFun s c (β / N) y z) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (B1 * logEN N) := by
    intro y
    have h := ((hC1 N hN).1 y).1
    simp only [one_mul] at h
    exact h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hL0))
  have hCL : B1 * logEN N ≤ C * logEN N := by
    refine mul_le_mul_of_nonneg_right ?_ hL0
    have : 0 ≤ C0 + E0 * Λ * (B + Cl) + Ep * Cw + E0 * B1 ^ 2 := by positivity
    linarith
  refine ⟨fun y => (hI y).trans (ENNReal.ofReal_le_ofReal hCL), ?_, ?_, ?_, ?_⟩
  · refine ((hC0 V hV N hN x).1).trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_right ?_ hL0
    have : 0 ≤ B1 + E0 * Λ * (B + Cl) + Ep * Cw + E0 * B1 ^ 2 := by positivity
    linarith
  · -- w (L + ℓ) against the pole weight
    have hmw1 : Measurable fun u : Torus d => ENNReal.ofReal (wEnv s x u) :=
      ENNReal.measurable_ofReal.comp (PairCorrAux.measurable_wEnv s x)
    have e1 : ∀ u : Torus d, ENNReal.ofReal (wEnv s x u * (logEN N + ellEnv x u)) =
        ENNReal.ofReal (logEN N) * ENNReal.ofReal (wEnv s x u) + ENNReal.ofReal (wEnv s x u * ellEnv x u) := by
      intro u
      have h1 := PairCorrAux.one_le_wEnv s x u
      have h2 := one_le_ellEnv x u
      rw [← ENNReal.ofReal_mul hL0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring
    calc _ ≤ ∫⁻ u, ENNReal.ofReal (wEnv s x u * (logEN N + ellEnv x u)) * ENNReal.ofReal E0 ∂(withDensityReal ρ) := by
          refine lintegral_mono fun u => mul_le_mul' le_rfl ?_
          exact poleW_le_const (V := V) hV hβ.le hlam0 (pinsWith (fun e : Empty => e.elim) x) u
      _ = (ENNReal.ofReal (logEN N) * ∫⁻ u, ENNReal.ofReal (wEnv s x u) ∂(withDensityReal ρ) +
            ∫⁻ u, ENNReal.ofReal (wEnv s x u * ellEnv x u) ∂(withDensityReal ρ)) * ENNReal.ofReal E0 := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
          congr 1
          simp_rw [e1]
          rw [lintegral_add_left (hmw1.const_mul _), lintegral_const_mul _ hmw1]
      _ ≤ (ENNReal.ofReal (logEN N) * ENNReal.ofReal (Λ * B) + ENNReal.ofReal (Λ * Cl)) * ENNReal.ofReal E0 := by
          gcongr
          · exact hB hΛ hΛ0.le x
          · exact hCl hΛ hΛ0.le x
      _ = ENNReal.ofReal ((logEN N * (Λ * B) + Λ * Cl) * E0) := by
          rw [← ENNReal.ofReal_mul hL0, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (logEN N * (Λ * B) + Λ * Cl) * E0 ≤ (E0 * Λ * (B + Cl)) * logEN N := by
            have : 0 ≤ Λ * Cl * E0 := by positivity
            nlinarith [mul_nonneg (mul_nonneg hE0p.le hΛ0.le) hCl0, mul_nonneg (mul_nonneg hE0p.le hΛ0.le) hB0]
          have h2 : 0 ≤ B1 + C0 + Ep * Cw + E0 * B1 ^ 2 := by positivity
          nlinarith
  · -- w² (L+ℓ)² against the pole weight
    rw [show (fun u : Torus d => ENNReal.ofReal (wEnv s x u ^ 2 * (logEN N + ellEnv x u) ^ 2) *
        ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
          pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u))) = _ from rfl]
    refine (lintegral_pole_le hV hβ.le hlam0 hlamβ hCq (x := x) (hatom) _).trans ?_
    have h := hCwF N hN x
    calc ENNReal.ofReal Ep * ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2 * (logEN N + ellEnv x y) ^ 2) *
          ENNReal.ofReal (Real.exp (-(β / N) * gPlus d s c (x - y))) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal Ep * ENNReal.ofReal (Cw * logEN N ^ 3) := by
          gcongr
          refine le_trans (le_of_eq ?_) h
          refine lintegral_congr fun y => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (Ep * (Cw * logEN N ^ 3)) := (ENNReal.ofReal_mul hEpp.le).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h3 : 0 ≤ logEN N ^ 3 := by positivity
          have h2 : 0 ≤ B1 + C0 + E0 * Λ * (B + Cl) + E0 * B1 ^ 2 := by positivity
          nlinarith [mul_nonneg h2 h3]
  · -- the J term
    have hJ := lintegral_Jfun_le (μ := withDensityReal ρ) hd hcrit c (β / N) x (mul_nonneg hB10 hL0) hI
    calc _ ≤ ∫⁻ u, Jfun s c (β / N) (withDensityReal ρ) x u * ENNReal.ofReal E0 ∂(withDensityReal ρ) := by
          refine lintegral_mono fun u => mul_le_mul' le_rfl ?_
          exact poleW_le_const (V := V) hV hβ.le hlam0 (pinsWith (fun e : Empty => e.elim) x) u
      _ = (∫⁻ u, Jfun s c (β / N) (withDensityReal ρ) x u ∂(withDensityReal ρ)) * ENNReal.ofReal E0 :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ (ENNReal.ofReal (B1 * logEN N) * ENNReal.ofReal (B1 * logEN N)) * ENNReal.ofReal E0 := by gcongr
      _ = ENNReal.ofReal ((B1 * logEN N) * (B1 * logEN N) * E0) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h3 : 0 ≤ logEN N ^ 2 := by positivity
          have h2 : 0 ≤ B1 + C0 + E0 * Λ * (B + Cl) + Ep * Cw := by positivity
          have : (B1 * logEN N) * (B1 * logEN N) * E0 = (E0 * B1 ^ 2) * logEN N ^ 2 := by ring
          rw [this]
          nlinarith [mul_nonneg h2 h3]

end L2Int

section L2Bound

theorem integrable_of_sq_lt_top {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]
    {F : α → ℝ} (hF : Measurable F) (h : ∫⁻ y, ‖F y‖ₑ ^ 2 ∂P < ⊤) : Integrable F P := by
  refine ⟨hF.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ y, ‖F y‖ₑ ∂P ≤ ∫⁻ y, (1 + ‖F y‖ₑ ^ 2) ∂P := by
        refine lintegral_mono fun y => ?_
        by_cases h1 : ‖F y‖ₑ ≤ 1
        · exact h1.trans le_self_add
        · push Not at h1
          exact (le_self_pow₀ h1.le (by norm_num)).trans le_add_self
    _ = 1 + ∫⁻ y, ‖F y‖ₑ ^ 2 ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, h⟩

theorem real_final (E2 C K A L N m : ℝ) (hE2 : 0 ≤ E2) (hC : 0 ≤ C) (hL1 : 1 ≤ L) (hLN : L ≤ N)
    (hm0 : 0 ≤ m) (hmN : m + 1 ≤ N) :
    8 * ((m + 1) * (6 * m * K ^ 2 * E2 * (2 * C ^ 2 + C) * L ^ 2 + A ^ 2 * C * L ^ 3)) +
        ((m + 1) * (A * (C * L))) ^ 2 ≤
      (8 * (6 * E2 * (2 * C ^ 2 + C) + C) + C ^ 2) * (K ^ 2 + A ^ 2) * N ^ 2 * L ^ 2 := by
  have hN0 : 0 ≤ N := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hmm : (m + 1) * m ≤ N ^ 2 := by nlinarith
  have hmL : (m + 1) * L ≤ N * N := by nlinarith
  have hm1 : (m + 1) ^ 2 ≤ N ^ 2 := by nlinarith
  have hc1 : 0 ≤ 6 * E2 * (2 * C ^ 2 + C) * K ^ 2 * L ^ 2 := by positivity
  have h1 : (m + 1) * (6 * m * K ^ 2 * E2 * (2 * C ^ 2 + C) * L ^ 2) ≤
      6 * E2 * (2 * C ^ 2 + C) * K ^ 2 * N ^ 2 * L ^ 2 := by
    have := mul_le_mul_of_nonneg_left hmm hc1
    nlinarith
  have hc2 : 0 ≤ A ^ 2 * C * L ^ 2 := by positivity
  have h2 : (m + 1) * (A ^ 2 * C * L ^ 3) ≤ A ^ 2 * C * N ^ 2 * L ^ 2 := by
    have := mul_le_mul_of_nonneg_left hmL hc2
    nlinarith
  have hc3 : 0 ≤ A ^ 2 * C ^ 2 * L ^ 2 := by positivity
  have h3 : ((m + 1) * (A * (C * L))) ^ 2 ≤ A ^ 2 * C ^ 2 * N ^ 2 * L ^ 2 := by
    have := mul_le_mul_of_nonneg_left hm1 hc3
    nlinarith
  have P1 : 0 ≤ (8 * C + C ^ 2) * K ^ 2 * N ^ 2 * L ^ 2 := by positivity
  have P2 : 0 ≤ 48 * E2 * (2 * C ^ 2 + C) * A ^ 2 * N ^ 2 * L ^ 2 := by positivity
  nlinarith [h1, h2, h3, P1, P2]

/-- The crude two-pole integral of `|g₃|`: `∫ |g₃(x,u,z)| e^{pole_{x,u}(z)} dμ ≤ |K| E₀ Λ (2B w + C_tp ℓ)`. -/
theorem g3_pole2_le (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) :
    ∃ B Ctp : ℝ, 0 ≤ B ∧ 0 ≤ Ctp ∧ ∀ {ρ : Torus d → ℝ} {Λ : ℝ}, (∀ x, ρ x ≤ Λ) → 0 ≤ Λ →
    ∀ (hρ : SmoothPosDensity ρ)
    {c Mmax M'max γmax Cq : ℝ} {V : WeakPotential (withDensityReal ρ)}
    (hV : PotBound (d := d) s c Mmax M'max γmax Cq V) {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (K : ℝ)
    {g3 : Torus d → Torus d → Torus d → ℝ}
    (hg3 : ∀ x y z, x ≠ y → x ≠ z → y ≠ z → |g3 x y z| ≤ K * tEnv s x y z) {x u : Torus d} (hxu : x ≠ u),
    ∫⁻ z, ‖g3 x u z‖ₑ * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / N) (pinsWith (pinsWith (fun e : Empty => e.elim) x) u) z)) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (|K| * Real.exp (M'max + β * max γmax 0 + Mmax)) *
        ENNReal.ofReal (Λ * (2 * B * wEnv s x u + Ctp * ellEnv x u)) := by
  obtain ⟨B, Ctp, hB0, hCt0, hT⟩ := lintegral_mu_tEnv (s := s) hd hcrit
  refine ⟨B, Ctp, hB0, hCt0, fun {ρ Λ} hΛ hΛ0 hρ {c Mmax M'max γmax Cq} {V} hV {β} hβ {N} K {g3} hg3 {x u} hxu => ?_⟩
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  set E0 : ℝ := Real.exp (M'max + β * max γmax 0 + Mmax) with hE0
  have hE0p : 0 < E0 := Real.exp_pos _
  have hlam0 : 0 ≤ β / N := by positivity
  have hmt : Measurable fun z : Torus d => ENNReal.ofReal (tEnv s x u z) := by
    have h1 := PairCorrAux.measurable_wEnv s x
    have h2 := PairCorrAux.measurable_wEnv s u
    refine ENNReal.measurable_ofReal.comp ?_
    unfold tEnv
    exact (measurable_const.mul h1).add (measurable_const.mul h2) |>.add (h1.mul h2)
  have hae : ∀ᵐ z ∂(withDensityReal ρ), z ≠ x ∧ z ≠ u :=
    (HRS.External.PoleVar.ae_ne_pt hatom x).and (HRS.External.PoleVar.ae_ne_pt hatom u)
  calc _ ≤ ∫⁻ z, ENNReal.ofReal (|K| * E0) * ENNReal.ofReal (tEnv s x u z) ∂(withDensityReal ρ) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with z hz
        have h1 : ‖g3 x u z‖ₑ ≤ ENNReal.ofReal (|K| * tEnv s x u z) := by
          rw [Real.enorm_eq_ofReal_abs]
          refine ENNReal.ofReal_le_ofReal ?_
          calc |g3 x u z| ≤ K * tEnv s x u z := hg3 x u z hxu (Ne.symm hz.1) (Ne.symm hz.2)
            _ ≤ |K| * tEnv s x u z := mul_le_mul_of_nonneg_right (le_abs_self K) (tEnv_nonneg s x u z)
        have h2 := poleW_le_const (V := V) hV hβ hlam0 (pinsWith (pinsWith (fun e : Empty => e.elim) x) u) z
        calc ‖g3 x u z‖ₑ * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
              pinField V (β / N) (pinsWith (pinsWith (fun e : Empty => e.elim) x) u) z))
            ≤ ENNReal.ofReal (|K| * tEnv s x u z) * ENNReal.ofReal E0 := mul_le_mul' h1 h2
          _ = _ := by
              rw [← ENNReal.ofReal_mul (by have := tEnv_nonneg s x u z; positivity),
                ← ENNReal.ofReal_mul (by positivity)]
              congr 1; ring
    _ = ENNReal.ofReal (|K| * E0) * ∫⁻ z, ENNReal.ofReal (tEnv s x u z) ∂(withDensityReal ρ) :=
        lintegral_const_mul _ hmt
    _ ≤ _ := by
        gcongr
        exact hT hΛ hΛ0 x u hxu

theorem g3_marg_integrable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {c Mmax M'max γmax Cq : ℝ} {V : WeakPotential (withDensityReal ρ)}
    (hV : PotBound (d := d) s c Mmax M'max γmax Cq V) {β : ℝ} (hβ : 0 ≤ β) {m N : ℕ} (hN0 : 0 < N)
    (hN : m + 2 ≤ N) (K : ℝ) {g3 : Torus d → Torus d → Torus d → ℝ}
    (hgm : Measurable (fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2))
    (hg3 : ∀ x y z, x ≠ y → x ≠ z → y ≠ z → |g3 x y z| ≤ K * tEnv s x y z) {x u : Torus d} (hxu : x ≠ u)
    (k : Fin m) :
    Integrable (g3 x u) ((pinnedLaw V (β / N) m
      (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)).map (fun Y => Y k)) := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨B, Ctp, hB0, hCt0, hT⟩ := g3_pole2_le (s := s) hd hcrit
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  have hcard : m + Fintype.card (Option (Option Empty)) ≤ N := by simp; omega
  have hgx : Measurable (g3 x u) :=
    Measurable.comp (g := fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) hgm
      (f := fun z : Torus d => (x, u, z)) (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  exact integrable_marg V hβ hN0 hcard _ k hgx
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (hT hΛ hΛ0.le hρ hV hβ K hg3 hxu)

/-- **The second-level estimate** (`Q:eq:inner-triple-variance`, `Q:eq:inner-triple-mean`): under the
one-pin ensemble `R^x`, `E |∑_{j≠k} g₃(x, y_j, y_k)|² ≲ (K² + A²) N² L²`, provided the
two-pin means are bounded by `A w(x,u)(L + ℓ(x,u))`. -/
theorem level2_bound (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (Mmax M'max γmax Cq : ℝ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V → ∀ m : ℕ, 1 ≤ m → weakKappa V β ≤ 1 / 2 →
      ∀ (K A : ℝ), 0 ≤ A → ∀ (g3 : Torus d → Torus d → Torus d → ℝ),
      Measurable (fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) →
      IsSymmTriple g3 →
      (∀ x y z, x ≠ y → x ≠ z → y ≠ z → |g3 x y z| ≤ K * tEnv s x y z) →
      (∀ x u : Torus d, x ≠ u →
        |∑ k : Fin m, ∫ z, g3 x u z ∂((pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) m
          (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)).map (fun Y => Y k))| ≤
          A * (wEnv s x u * (logEN (m + 2) + ellEnv x u))) →
      ∀ x : Torus d,
        ∫⁻ Y, ‖pairSumOrdered (g3 x) Y‖ₑ ^ 2
            ∂(pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) (m + 1) (pinsWith (fun e : Empty => e.elim) x)) ≤
          ENNReal.ofReal (C * (K ^ 2 + A ^ 2) * ((m + 2 : ℕ) : ℝ) ^ 2 * logEN (m + 2) ^ 2) := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨C, hC0, hCI⟩ := l2_integrals hd hcrit β hβ ρ hρ c hc Mmax M'max γmax Cq hCq
  set E2 : ℝ := Real.exp (M'max + β * max γmax 0 + Mmax + 2 * (β * Cq)) with hE2
  have hE2p : 0 < E2 := Real.exp_pos _
  refine ⟨8 * (6 * E2 * (2 * C ^ 2 + C) + C) + C ^ 2, by positivity, fun V hV m hm1 hκ K A hA g3 hgm hsym hg3 hMean x => ?_⟩
  set N : ℕ := m + 2 with hNdef
  have hN2 : 2 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  haveI : NeZero m := ⟨by omega⟩
  have hLe := logEN_pos' (N := N) (by omega)
  have hL0 : 0 ≤ logEN N := by linarith
  have hLN := logEN_le_N (N := N) (by omega)
  have hlam0 : 0 ≤ β / N := by positivity
  have hlamβ : β / N ≤ β := by
    rw [div_le_iff₀ hNp]
    have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  obtain ⟨hI, hw2, hwl, hw2l, hJ⟩ := hCI V hV N hN2 x
  set h : Torus d → Torus d → ℝ := fun y z => g3 x y z with hh
  have hhm : Measurable (Function.uncurry h) :=
    Measurable.comp (g := fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) hgm
      (f := fun p : Torus d × Torus d => (x, p.1, p.2)) (measurable_const.prodMk measurable_id)
  have hhsym : ∀ y z, h y z = h z y := fun y z => (hsym x y z).2
  have hμ' : IsProbabilityMeasure (pinnedLaw V (β / N) (m + 1) (pinsWith (fun e : Empty => e.elim) x)) :=
    isProb_pinnedLaw V hlam0 (m + 1) _
  have hcard : m + 1 + Fintype.card (Option Empty) ≤ N := by simp [hNdef]
  have hcardB : m + 1 + Fintype.card (Option Empty) ≤ N := hcard
  have hpm : Measurable (pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x)) :=
    (isField_pinField V hlam0 _).measurable
  have hPm : Measurable fun u : Torus d => ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
      pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.add hpm))
  have hw2m : Measurable fun u : Torus d => ENNReal.ofReal (wEnv s x u ^ 2) :=
    ENNReal.measurable_ofReal.comp ((PairCorrAux.measurable_wEnv s x).pow_const 2)
  set 𝒱 : Torus d → ℝ≥0∞ := fun u => ENNReal.ofReal (3 * K ^ 2 * E2) *
    (ENNReal.ofReal (wEnv s x u ^ 2) * ENNReal.ofReal (2 * (C * logEN N)) +
      Jfun s c (β / N) (withDensityReal ρ) x u) with h𝒱
  set 𝓜 : Torus d → ℝ := fun u => A * (wEnv s x u * (logEN N + ellEnv x u)) with h𝓜
  have h𝒱m : Measurable 𝒱 :=
    ((hw2m.mul_const _).add (measurable_Jfun hd hcrit c (β / N) x)).const_mul _
  have h𝓜m : Measurable 𝓜 := measurable_const.mul (measurable_wEll x)
  have h𝓜0 : ∀ u, 0 ≤ 𝓜 u := fun u =>
    mul_nonneg hA (mul_nonneg (by linarith [PairCorrAux.one_le_wEnv s x u]) (by linarith [one_le_ellEnv x u]))
  have hae : ∀ᵐ u ∂(withDensityReal ρ), u ≠ x := HRS.External.PoleVar.ae_ne_pt hatom x
  have hrowV : ∀ᵐ u ∂(withDensityReal ρ), ∫⁻ z, ‖h u z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
      pinField V (β / N) (pinsWith (pinsWith (fun e : Empty => e.elim) x) u) z)) ∂(withDensityReal ρ) ≤ 𝒱 u := by
    filter_upwards [hae] with u hu
    have hxu : x ≠ u := Ne.symm hu
    refine (var2_bound hd hcrit hV hβ.le hlam0 hlamβ hCq hatom hc K hg3 hxu).trans ?_
    refine mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl ?_) le_rfl)
    calc _ ≤ ENNReal.ofReal (C * logEN N) + ENNReal.ofReal (C * logEN N) := add_le_add (hI x) (hI u)
      _ = _ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have hrowM : ∀ᵐ u ∂(withDensityReal ρ), |∑ k : Fin m, ∫ z, h u z ∂((pinnedLaw V (β / N) m
      (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)).map (fun Y => Y k))| ≤ 𝓜 u := by
    filter_upwards [hae] with u hu
    exact hMean x u (Ne.symm hu)
  have hrow : ∀ i : Fin (m + 1), ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)‖ₑ ^ 2
      ∂(pinnedLaw V (β / N) (m + 1) (pinsWith (fun e : Empty => e.elim) x)) ≤
      ∫⁻ u, pinWeight V (β / N) (pinsWith (fun e : Empty => e.elim) x) m u *
        (ENNReal.ofReal (2 * m) * 𝒱 u + ENNReal.ofReal ((𝓜 u) ^ 2)) ∂(withDensityReal ρ) :=
    fun i => row_moment_pins_le V hβ.le (by omega) hcard _ hκ hhm i hrowV hrowM
  have hΨm : Measurable fun u => ENNReal.ofReal (2 * m) * 𝒱 u + ENNReal.ofReal ((𝓜 u) ^ 2) :=
    (h𝒱m.const_mul _).add (ENNReal.measurable_ofReal.comp (h𝓜m.pow_const 2))
  set Ξb : ℝ := 6 * m * K ^ 2 * E2 * (2 * C ^ 2 + C) * logEN N ^ 2 + A ^ 2 * C * logEN N ^ 3 with hΞb
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hXi : ∫⁻ u, pinWeight V (β / N) (pinsWith (fun e : Empty => e.elim) x) m u *
        (ENNReal.ofReal (2 * m) * 𝒱 u + ENNReal.ofReal ((𝓜 u) ^ 2)) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal Ξb := by
    refine (lintegral_pinWeight_le V hβ.le (by omega) hcard _ hΨm).trans ?_
    set P : Torus d → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
      pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u)) with hP
    have hpt : ∀ u : Torus d, (ENNReal.ofReal (2 * m) * 𝒱 u + ENNReal.ofReal ((𝓜 u) ^ 2)) * P u =
        ENNReal.ofReal (2 * m * (3 * K ^ 2 * E2) * (2 * (C * logEN N))) * (ENNReal.ofReal (wEnv s x u ^ 2) * P u) +
        ENNReal.ofReal (2 * m * (3 * K ^ 2 * E2)) * (Jfun s c (β / N) (withDensityReal ρ) x u * P u) +
        ENNReal.ofReal (A ^ 2) * (ENNReal.ofReal (wEnv s x u ^ 2 * (logEN N + ellEnv x u) ^ 2) * P u) := by
      intro u
      have e1 : ENNReal.ofReal (2 * m * (3 * K ^ 2 * E2) * (2 * (C * logEN N))) =
          ENNReal.ofReal (2 * m) * ENNReal.ofReal (3 * K ^ 2 * E2) * ENNReal.ofReal (2 * (C * logEN N)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      have e2 : ENNReal.ofReal (2 * m * (3 * K ^ 2 * E2)) =
          ENNReal.ofReal (2 * m) * ENNReal.ofReal (3 * K ^ 2 * E2) := by
        rw [ENNReal.ofReal_mul (by positivity)]
      have e3 : ENNReal.ofReal ((𝓜 u) ^ 2) = ENNReal.ofReal (A ^ 2) *
          ENNReal.ofReal (wEnv s x u ^ 2 * (logEN N + ellEnv x u) ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1; simp only [h𝓜]; ring
      rw [e1, e2, e3]
      simp only [h𝒱]
      ring
    refine le_trans (le_of_eq (lintegral_congr hpt)) ?_
    have hF1 : Measurable fun u : Torus d => ENNReal.ofReal (wEnv s x u ^ 2) * P u := hw2m.mul hPm
    have hF2 : Measurable fun u : Torus d => Jfun s c (β / N) (withDensityReal ρ) x u * P u :=
      (measurable_Jfun hd hcrit c (β / N) x).mul hPm
    have hF3 : Measurable fun u : Torus d => ENNReal.ofReal (wEnv s x u ^ 2 * (logEN N + ellEnv x u) ^ 2) * P u :=
      (ENNReal.measurable_ofReal.comp (((PairCorrAux.measurable_wEnv s x).pow_const 2).mul
        ((measurable_const.add (measurable_ellEnv_right x)).pow_const 2))).mul hPm
    have hF12 : Measurable fun u : Torus d =>
        ENNReal.ofReal (2 * m * (3 * K ^ 2 * E2) * (2 * (C * logEN N))) * (ENNReal.ofReal (wEnv s x u ^ 2) * P u) +
        ENNReal.ofReal (2 * m * (3 * K ^ 2 * E2)) * (Jfun s c (β / N) (withDensityReal ρ) x u * P u) :=
      (hF1.const_mul _).add (hF2.const_mul _)
    rw [lintegral_add_left hF12, lintegral_add_left (hF1.const_mul _),
      lintegral_const_mul _ hF1, lintegral_const_mul _ hF2, lintegral_const_mul _ hF3]
    calc _ ≤ ENNReal.ofReal (2 * m * (3 * K ^ 2 * E2) * (2 * (C * logEN N))) * ENNReal.ofReal (C * logEN N) +
          ENNReal.ofReal (2 * m * (3 * K ^ 2 * E2)) * ENNReal.ofReal (C * logEN N ^ 2) +
          ENNReal.ofReal (A ^ 2) * ENNReal.ofReal (C * logEN N ^ 3) := by
          gcongr
      _ = ENNReal.ofReal Ξb := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          simp only [hΞb]; ring
  have hrowI : ∀ i : Fin (m + 1), ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)‖ₑ ^ 2
      ∂(pinnedLaw V (β / N) (m + 1) (pinsWith (fun e : Empty => e.elim) x)) ≤ ENNReal.ofReal Ξb :=
    fun i => (hrow i).trans hXi
  have hint : ∀ i : Fin (m + 1), Integrable (fun Y : Fin (m + 1) → Torus d =>
      ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j))
      (pinnedLaw V (β / N) (m + 1) (pinsWith (fun e : Empty => e.elim) x)) := fun i =>
    integrable_of_sq_lt_top (measurable_rowSum hhm i) (lt_of_le_of_lt (hrowI i) ENNReal.ofReal_lt_top)
  set W : ℝ := A * (C * logEN N) with hWdef
  have hW0 : 0 ≤ W := by positivity
  have hmwl : Measurable fun u : Torus d => ENNReal.ofReal (wEnv s x u * (logEN N + ellEnv x u)) :=
    ENNReal.measurable_ofReal.comp (measurable_wEll x)
  have hW : ∫⁻ u, ENNReal.ofReal (𝓜 u) * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
      pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal W := by
    calc _ = ∫⁻ u, ENNReal.ofReal A * (ENNReal.ofReal (wEnv s x u * (logEN N + ellEnv x u)) *
          ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
            pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u))) ∂(withDensityReal ρ) := by
          refine lintegral_congr fun u => ?_
          simp only [h𝓜]
          rw [ENNReal.ofReal_mul hA, mul_assoc]
      _ = ENNReal.ofReal A * ∫⁻ u, ENNReal.ofReal (wEnv s x u * (logEN N + ellEnv x u)) *
          ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
            pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u)) ∂(withDensityReal ρ) :=
          lintegral_const_mul _ (hmwl.mul hPm)
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal (C * logEN N) := by gcongr
      _ = ENNReal.ofReal W := (ENNReal.ofReal_mul hA).symm
  have hfπ : ∀ᵐ u ∂(withDensityReal ρ), ∀ k : Fin m, Integrable (h u) ((pinnedLaw V (β / N) m
      (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)).map (fun Y => Y k)) := by
    filter_upwards [hae] with u hu k
    exact g3_marg_integrable hd hcrit hρ hV hβ.le (by omega) (by omega) K hgm hg3 (Ne.symm hu) k
  have hmean : ∀ i : Fin (m + 1), |∫ Y, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)
      ∂(pinnedLaw V (β / N) (m + 1) (pinsWith (fun e : Empty => e.elim) x))| ≤ W := fun i =>
    abs_integral_row_le V hβ.le (by omega) hcard _ hhm i (hint i) h𝓜m h𝓜0 hfπ hrowM hW0 hW
  have hmeanT : |∫ Y, pairSumOrdered h Y ∂(pinnedLaw V (β / N) (m + 1)
      (pinsWith (fun e : Empty => e.elim) x))| ≤ ((m : ℝ) + 1) * W := by
    have e : ∫ Y, pairSumOrdered h Y ∂(pinnedLaw V (β / N) (m + 1) (pinsWith (fun e : Empty => e.elim) x)) =
        ∑ i : Fin (m + 1), ∫ Y, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)
          ∂(pinnedLaw V (β / N) (m + 1) (pinsWith (fun e : Empty => e.elim) x)) := by
      unfold pairSumOrdered
      exact integral_finsetSum _ fun i _ => hint i
    rw [e]
    calc _ ≤ ∑ i : Fin (m + 1), |∫ Y, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)
          ∂(pinnedLaw V (β / N) (m + 1) (pinsWith (fun e : Empty => e.elim) x))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (m + 1), W := Finset.sum_le_sum fun i _ => hmean i
      _ = ((m : ℝ) + 1) * W := by simp
  have hvar := evariance_pairSum_le_pins V hβ.le (N := N) (n := m + 1) (by omega) hcard
    (pinsWith (fun e : Empty => e.elim) x) hκ hhm hhsym 1
  simp only [one_mul] at hvar
  have hsq := lintegral_sq_le_evariance_add (measurable_pairSumOrdered hhm) hmeanT
  have hsum : ∑ i : Fin (m + 1), ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)‖ₑ ^ 2
      ∂(pinnedLaw V (β / N) (m + 1) (pinsWith (fun e : Empty => e.elim) x)) ≤
      ENNReal.ofReal ((m : ℝ) + 1) * ENNReal.ofReal Ξb := by
    calc _ ≤ ∑ _i : Fin (m + 1), ENNReal.ofReal Ξb := Finset.sum_le_sum fun i _ => hrowI i
      _ = ENNReal.ofReal ((m : ℝ) + 1) * ENNReal.ofReal Ξb := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          congr 1
          rw [← ENNReal.ofReal_natCast]; push_cast; rfl
  have hL1 : 1 ≤ logEN N := hLe
  have hfin := real_final E2 C K A (logEN N) N m hE2p.le hC0 hL1 hLN hmR (by simp [hNdef])
  refine hsq.trans ?_
  refine le_trans (add_le_add (hvar.trans (mul_le_mul' le_rfl hsum)) le_rfl) ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := hfin
  simp only [hΞb, hWdef] at *
  nlinarith [this]

end L2Bound

end HRS.PairMom

end
