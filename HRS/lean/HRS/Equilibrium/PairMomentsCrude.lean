/-
# HRS.Equilibrium.PairMomentsCrude -- crude (no smallness) second moments under pinned ensembles (EQ-01b)
-/
import HRS.Equilibrium.PairMomentsM2

open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.PairMom

open HRS HRS.External HRS.Quad HRS.External.PoleVar

variable {d : ℕ} {s : ℝ}

section CrudePins

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {B : Type*} [Fintype B]

/-- Pair second moment under a pinned ensemble, via disintegration at `i`. -/
theorem pair_lintegral_le_pins (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + 1 + Fintype.card B ≤ N) (a : B → Torus d) (i j : Fin (n + 1)) (hij : i ≠ j)
    {h : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry h)) {𝒱 : Torus d → ℝ≥0∞}
    (h𝒱m : Measurable 𝒱)
    (hV : ∀ᵐ u ∂μ, ∫⁻ z, ‖h u z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / N) (pinsWith a u) z)) ∂μ ≤ 𝒱 u) :
    ∫⁻ Y, ‖h (Y i) (Y j)‖ₑ ^ 2 ∂(pinnedLaw V (β / N) (n + 1) a) ≤
      ∫⁻ u, 𝒱 u * ENNReal.ofReal (Real.exp (V.M' + β * V.γ + pinField V (β / N) a u)) ∂μ := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
  have hΦ : Measurable fun Y : Fin (n + 1) → Torus d => ‖h (Y i) (Y j)‖ₑ ^ 2 :=
    ((measurable_h_pair hm i j).enorm).pow_const 2
  rw [lintegral_pinned_succ V hlam a i hΦ]
  refine le_trans (lintegral_mono_ae ?_) (lintegral_pinWeight_le V hβ hN0 hN a h𝒱m)
  filter_upwards [hV] with x hx
  refine mul_le_mul' le_rfl ?_
  have e : ∀ y : Fin n → Torus d, ‖h (insertAt i x y i) (insertAt i x y j)‖ₑ ^ 2 = ‖h x (y k)‖ₑ ^ 2 := by
    intro y
    rw [insertAt_same, ← hk, insertAt_succAbove]
  simp_rw [e]
  have hcard : n + Fintype.card (Option B) ≤ N := by
    simp only [Fintype.card_option]; omega
  have hmeas : Measurable fun z => ‖h x z‖ₑ ^ 2 := ((measurable_h_x hm x).enorm).pow_const 2
  calc ∫⁻ y, ‖h x (y k)‖ₑ ^ 2 ∂(pinnedLaw V (β / N) n (pinsWith a x))
      = ∫⁻ z, ‖h x z‖ₑ ^ 2 ∂((pinnedLaw V (β / N) n (pinsWith a x)).map (fun Y => Y k)) := by
        rw [lintegral_map hmeas (measurable_pi_apply k)]
    _ ≤ _ := lintegral_marg_le V hβ hN0 hcard (pinsWith a x) k hmeas
    _ ≤ 𝒱 x := hx

/-- **Crude second moment of an ordered pair sum** under a pinned ensemble. -/
theorem lintegral_pairSum_sq_le_pins (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + 1 + Fintype.card B ≤ N) (a : B → Torus d)
    {h : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry h)) {𝒱 : Torus d → ℝ≥0∞}
    (h𝒱m : Measurable 𝒱)
    (hV : ∀ᵐ u ∂μ, ∫⁻ z, ‖h u z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / N) (pinsWith a u) z)) ∂μ ≤ 𝒱 u) {Ξ : ℝ≥0∞}
    (hΞ : ∫⁻ u, 𝒱 u * ENNReal.ofReal (Real.exp (V.M' + β * V.γ + pinField V (β / N) a u)) ∂μ ≤ Ξ) :
    ∫⁻ Y, ‖pairSumOrdered h Y‖ₑ ^ 2 ∂(pinnedLaw V (β / N) (n + 1) a) ≤
      ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ 4) * Ξ := by
  have hmeas : ∀ i j : Fin (n + 1), Measurable fun Y : Config d (n + 1) => ‖h (Y i) (Y j)‖ₑ ^ 2 :=
    fun i j => ((measurable_h_pair hm i j).enorm).pow_const 2
  have hpair : ∀ i j : Fin (n + 1), i ≠ j → ∫⁻ Y, ‖h (Y i) (Y j)‖ₑ ^ 2 ∂(pinnedLaw V (β / N) (n + 1) a) ≤ Ξ :=
    fun i j hij => (pair_lintegral_le_pins V hβ hN0 hN a i j hij hm h𝒱m hV).trans hΞ
  calc ∫⁻ Y, ‖pairSumOrdered h Y‖ₑ ^ 2 ∂(pinnedLaw V (β / N) (n + 1) a)
      ≤ ∫⁻ Y, ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ 2) *
          ∑ i, ∑ j ∈ Finset.univ.erase i, ‖h (Y i) (Y j)‖ₑ ^ 2 ∂(pinnedLaw V (β / N) (n + 1) a) :=
        lintegral_mono fun Y => enorm_sq_pairSum_le h Y
    _ = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
          ∫⁻ Y, ‖h (Y i) (Y j)‖ₑ ^ 2 ∂(pinnedLaw V (β / N) (n + 1) a) := by
        rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _
          fun j _ => hmeas i j)]
        congr 1
        rw [lintegral_finsetSum _ (fun i _ => Finset.measurable_sum _ fun j _ => hmeas i j)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_finsetSum _ (fun j _ => hmeas i j)]
    _ ≤ ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ 2) * ∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.erase i, Ξ := by
        gcongr with i _ j hj
        exact hpair i j (Finset.ne_of_mem_erase hj).symm
    _ ≤ ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ 2) * ∑ _i : Fin (n + 1), ∑ _j : Fin (n + 1), Ξ := by
        exact mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum_of_subset (Finset.erase_subset i Finset.univ))
    _ = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ 4) * Ξ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show (4 : ℕ) = 2 + 1 + 1 by norm_num]
        have : ((n + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (((n + 1 : ℕ) : ℝ)) := by
          rw [ENNReal.ofReal_natCast]
        rw [this, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 3

end CrudePins

section Level2Crude

/-- Crude second-level estimate (no smallness, no reference density input). -/
theorem level2_crude (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (Mmax M'max γmax Cq : ℝ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V → ∀ m : ℕ, 1 ≤ m →
      ∀ (K : ℝ) (g3 : Torus d → Torus d → Torus d → ℝ),
      Measurable (fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) →
      (∀ x y z, x ≠ y → x ≠ z → y ≠ z → |g3 x y z| ≤ K * tEnv s x y z) →
      ∀ x : Torus d,
        ∫⁻ Y, ‖pairSumOrdered (g3 x) Y‖ₑ ^ 2
            ∂(pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) (m + 1) (pinsWith (fun e : Empty => e.elim) x)) ≤
          ENNReal.ofReal (C * K ^ 2 * ((m + 2 : ℕ) : ℝ) ^ 4 * logEN (m + 2) ^ 2) := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨C, hC0, hCI⟩ := l2_integrals hd hcrit β hβ ρ hρ c hc Mmax M'max γmax Cq hCq
  set E2 : ℝ := Real.exp (M'max + β * max γmax 0 + Mmax + 2 * (β * Cq)) with hE2
  have hE2p : 0 < E2 := Real.exp_pos _
  refine ⟨3 * E2 * (2 * C ^ 2 + C), by positivity, fun V hV m hm1 K g3 hgm hg3 x => ?_⟩
  set N : ℕ := m + 2 with hNdef
  have hN2 : 2 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hLe := logEN_pos' (N := N) (by omega)
  have hL0 : 0 ≤ logEN N := by linarith
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
  have hcard : m + 1 + Fintype.card (Option Empty) ≤ N := by simp [hNdef]
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
  have h𝒱m : Measurable 𝒱 :=
    ((hw2m.mul_const _).add (measurable_Jfun hd hcrit c (β / N) x)).const_mul _
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
  set Ξb : ℝ := 3 * K ^ 2 * E2 * (2 * C ^ 2 + C) * logEN N ^ 2 with hΞb
  have hΞ : ∫⁻ u, 𝒱 u * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
      pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal Ξb := by
    set P : Torus d → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
      pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) u)) with hP
    have hpt : ∀ u : Torus d, 𝒱 u * P u =
        ENNReal.ofReal (3 * K ^ 2 * E2 * (2 * (C * logEN N))) * (ENNReal.ofReal (wEnv s x u ^ 2) * P u) +
        ENNReal.ofReal (3 * K ^ 2 * E2) * (Jfun s c (β / N) (withDensityReal ρ) x u * P u) := by
      intro u
      have e1 : ENNReal.ofReal (3 * K ^ 2 * E2 * (2 * (C * logEN N))) =
          ENNReal.ofReal (3 * K ^ 2 * E2) * ENNReal.ofReal (2 * (C * logEN N)) := by
        rw [ENNReal.ofReal_mul (by positivity)]
      rw [e1]
      simp only [h𝒱]
      ring
    refine le_trans (le_of_eq (lintegral_congr hpt)) ?_
    have hF1 : Measurable fun u : Torus d => ENNReal.ofReal (wEnv s x u ^ 2) * P u := hw2m.mul hPm
    have hF2 : Measurable fun u : Torus d => Jfun s c (β / N) (withDensityReal ρ) x u * P u :=
      (measurable_Jfun hd hcrit c (β / N) x).mul hPm
    rw [lintegral_add_left (hF1.const_mul _), lintegral_const_mul _ hF1, lintegral_const_mul _ hF2]
    calc _ ≤ ENNReal.ofReal (3 * K ^ 2 * E2 * (2 * (C * logEN N))) * ENNReal.ofReal (C * logEN N) +
          ENNReal.ofReal (3 * K ^ 2 * E2) * ENNReal.ofReal (C * logEN N ^ 2) := by
          gcongr
      _ = ENNReal.ofReal Ξb := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          simp only [hΞb]; ring
  have hmain := lintegral_pairSum_sq_le_pins V hβ.le (N := N) (n := m) (by omega) hcard
    (pinsWith (fun e : Empty => e.elim) x) hhm h𝒱m hrowV hΞ
  refine hmain.trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hm4 : (((m + 1 : ℕ) : ℝ)) ^ 4 ≤ (N : ℝ) ^ 4 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 4
    exact_mod_cast (by omega : m + 1 ≤ N)
  have h0 : 0 ≤ Ξb := by positivity
  calc ((m + 1 : ℕ) : ℝ) ^ 4 * Ξb ≤ (N : ℝ) ^ 4 * Ξb := mul_le_mul_of_nonneg_right hm4 h0
    _ = _ := by simp only [hΞb]; ring

end Level2Crude

end HRS.PairMom

end
