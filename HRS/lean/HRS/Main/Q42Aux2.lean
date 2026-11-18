import HRS.PDE.MeanFieldDefs
import HRS.Equilibrium.PreparationAux
import HRS.Equilibrium.PoleCavity
import HRS.Energy.Modulated
import HRS.Energy.StaticLimitGauss

/-!
# Packet Q42: inverse-Gibbs moment (helpers for `inverse_gibbs_moment_infinite`)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d : ℕ}

/-- Lower bound for a double sum over ordered pairs with a uniform lower bound `-B`. -/
theorem q42_double_lower {N : ℕ} {f : Fin N → Fin N → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hf : ∀ a b, -B ≤ f a b) {i j : Fin N} (hij : i ≠ j) :
    f i j + f j i + 2 * B - N * (N * B) ≤ ∑ a, ∑ b ∈ Finset.univ.erase a, f a b := by
  set h : Fin N → Fin N → ℝ := fun a b => f a b + B with hh
  have hnn : ∀ a b, 0 ≤ h a b := fun a b => by simp only [hh]; linarith [hf a b]
  have step1 : ∀ a, ∑ b ∈ Finset.univ.erase a, h a b - N * B ≤
      ∑ b ∈ Finset.univ.erase a, f a b := by
    intro a
    have hc : ∑ b ∈ Finset.univ.erase a, B ≤ ∑ _b : Fin N, B :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => hB0)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hc
    have e : ∑ b ∈ Finset.univ.erase a, h a b = ∑ b ∈ Finset.univ.erase a, f a b +
        ∑ b ∈ Finset.univ.erase a, B := by
      rw [← Finset.sum_add_distrib]
    have e2 : ∑ b ∈ Finset.univ.erase a, B = ((Finset.univ.erase a).card : ℝ) * B := by
      rw [Finset.sum_const, nsmul_eq_mul]
    linarith
  have step2 : ∑ b ∈ Finset.univ.erase i, h i b + ∑ b ∈ Finset.univ.erase j, h j b ≤
      ∑ a, ∑ b ∈ Finset.univ.erase a, h a b := by
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun a => ∑ b ∈ Finset.univ.erase a, h a b)
      (Finset.subset_univ {i, j}) (fun a _ _ => Finset.sum_nonneg (fun b _ => hnn a b))
    rw [Finset.sum_pair hij] at this
    exact this
  have step3 : h i j ≤ ∑ b ∈ Finset.univ.erase i, h i b :=
    Finset.single_le_sum (f := fun b => h i b) (fun b _ => hnn i b)
      (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩)
  have step4 : h j i ≤ ∑ b ∈ Finset.univ.erase j, h j b :=
    Finset.single_le_sum (f := fun b => h j b) (fun b _ => hnn j b)
      (Finset.mem_erase.2 ⟨hij, Finset.mem_univ i⟩)
  have step5 : ∑ a, (∑ b ∈ Finset.univ.erase a, h a b - N * B) ≤
      ∑ a, ∑ b ∈ Finset.univ.erase a, f a b :=
    Finset.sum_le_sum (fun a _ => step1 a)
  rw [Finset.sum_sub_distrib] at step5
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at step5
  simp only [hh] at step2 step3 step4
  linarith

/-- Lower bound on `N F_N` in terms of one pair, for an integrable... (uniform in `X`). -/
theorem q42_energy_lower (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ) {N : ℕ}
    (i j : Fin N) (hij : i ≠ j) :
    ∃ C : ℝ, ∀ X : Config d N,
      periodicRiesz d s (X i - X j) / N - C ≤
        N * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ) := by
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  obtain ⟨C1, hC1⟩ := convMeasure_bounded hd hs0 hsd ρ hρ Λ hΛ
  set μ := withDensityReal ρ with hμ
  set g := periodicRiesz d s with hg
  set T : ℝ := ∫ x, ∫ y, g (x - y) ∂μ ∂μ with hT
  set Bp : ℝ := max B 0 with hBp
  have hBp0 : 0 ≤ Bp := le_max_right _ _
  have hBp' : ∀ x, -Bp ≤ g x := fun x => (neg_le_neg (le_max_left _ _)).trans (hB x)
  refine ⟨N * C1 - (N / 2) * T - (2 * Bp - (N : ℝ) * (N * Bp)) / (2 * N), fun X => ?_⟩
  -- the energy identity
  have hF : (N : ℝ) * modulatedEnergyKernel g X μ =
      (1 / (2 * (N : ℝ))) * (∑ a, ∑ b ∈ Finset.univ.erase a, g (X a - X b)) -
        ∑ a, ∫ y, g (X a - y) ∂μ + (N / 2) * T := by
    unfold modulatedEnergyKernel modulatedEnergy
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      simp
    · have hN : (N : ℝ) ≠ 0 := by positivity
      field_simp
      ring
  have hS := q42_double_lower (f := fun a b => g (X a - X b)) hBp0
    (fun a b => hBp' _) hij
  have hsym : g (X j - X i) = g (X i - X j) := by
    rw [← neg_sub]
    exact periodicRiesz_neg _
  have hconv : ∑ a, ∫ y, g (X a - y) ∂μ ≤ N * C1 := by
    have : ∀ a, ∫ y, g (X a - y) ∂μ ≤ C1 := fun a =>
      (le_abs_self _).trans (hC1 (X a))
    calc ∑ a, ∫ y, g (X a - y) ∂μ ≤ ∑ _a : Fin N, C1 :=
          Finset.sum_le_sum (fun a _ => this a)
      _ = N * C1 := by simp
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.2
    exact_mod_cast this
  rw [hF]
  have hq : (1 / (2 * (N : ℝ))) * (2 * g (X i - X j) + 2 * Bp - (N : ℝ) * (N * Bp)) =
      g (X i - X j) / N + (2 * Bp - (N : ℝ) * (N * Bp)) / (2 * N) := by
    field_simp
    ring
  have hmul : (1 / (2 * (N : ℝ))) * (2 * g (X i - X j) + 2 * Bp - (N : ℝ) * (N * Bp)) ≤
      (1 / (2 * (N : ℝ))) * (∑ a, ∑ b ∈ Finset.univ.erase a, g (X a - X b)) :=
    mul_le_mul_of_nonneg_left (by linarith [hS, hsym]) (by positivity)
  linarith [hq, hmul, hconv]

/-- `∫⁻_𝕋 exp(κ g) = ∞` for `κ > 0` (the attractive pair singularity is not integrable). -/
theorem q42_torus_exp_top (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {κ : ℝ} (hκ : 0 < κ) :
    ∫⁻ z : Torus d, ENNReal.ofReal (Real.exp (κ * periodicRiesz d s z)) = ⊤ := by
  obtain ⟨r, δ, hδ, hr, hsing⟩ := periodicRiesz_local_singularity hd hs0 hsd
  have hrc : Continuous r := HRS.StaticLimitAux.continuous_of_smooth hr
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hrc.continuousOn
  set ε : ℝ := min δ (1 / 2) with hε
  have hε0 : 0 < ε := lt_min hδ (by norm_num)
  have hεδ : ε ≤ δ := min_le_left _ _
  have hε12 : ε ≤ 1 / 2 := min_le_right _ _
  have hd1 : 1 ≤ d := by omega
  have key := HRS.PreparationAux.lintegral_ball_exp_rpow_eq_top hd1 hs0 κ M ε hκ hε0
  have hle := HRS.PreparationAux.lintegral_ball_le_torus hd1 hε12
    (fun z => ENNReal.ofReal (Real.exp (κ * periodicRiesz d s z)))
    (fun w => ENNReal.ofReal (Real.exp (κ * (‖w‖ ^ (-s) - M))))
    (fun w hw hw0 => by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.2
      rw [hsing w (lt_of_lt_of_le hw hεδ) hw0]
      have h2 : -M ≤ r (Torus.mk w) := by
        have := hM (Torus.mk w) (Set.mem_univ _)
        rw [Real.norm_eq_abs] at this
        linarith [(abs_le.1 this).1]
      have h3 := mul_nonneg hκ.le (show (0 : ℝ) ≤ r (Torus.mk w) + M by linarith)
      nlinarith [h3])
  exact top_le_iff.1 (key ▸ hle)

/-- The pair integral against `P = μ^{⊗N}`, `μ = ρ dx` with `ρ ≥ c > 0`, is infinite. -/
theorem q42_pair_lintegral_top (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d)
    {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {c : ℝ} (hc : 0 < c) (hcρ : ∀ x, c ≤ ρ x)
    {N : ℕ} (i j : Fin N) (hij : i ≠ j) {κ : ℝ} (hκ : 0 < κ) :
    ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (κ * periodicRiesz d s (X i - X j)))
      ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) = ⊤ := by
  have hμp : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hG : Measurable (fun z : Torus d => ENNReal.ofReal (Real.exp (κ * periodicRiesz d s z))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (HRS.PoleCavityAux.measurable_periodicRiesz hd hs0.le hsd)))
  have hGp : Measurable (fun p : Torus d × Torus d =>
      ENNReal.ofReal (Real.exp (κ * periodicRiesz d s (p.1 - p.2)))) :=
    hG.comp (measurable_fst.sub measurable_snd)
  have hmeas_pair : Measurable (fun X : Config d N => (X i, X j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have e2 : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (κ * periodicRiesz d s (X i - X j)))
      ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) =
      ∫⁻ p : Torus d × Torus d, ENNReal.ofReal (Real.exp (κ * periodicRiesz d s (p.1 - p.2)))
        ∂((withDensityReal ρ).prod (withDensityReal ρ)) := by
    rw [← HRS.pi_map_pair (withDensityReal ρ) hij]
    exact (lintegral_map hGp hmeas_pair).symm
  rw [e2, lintegral_prod _ hGp.aemeasurable]
  have inner : ∀ x : Torus d, ∫⁻ y, ENNReal.ofReal (Real.exp (κ * periodicRiesz d s (x - y)))
      ∂(withDensityReal ρ) = ⊤ := by
    intro x
    have hmG : Measurable (fun y : Torus d => ENNReal.ofReal (Real.exp (κ * periodicRiesz d s (x - y)))) :=
      hG.comp (measurable_const.sub measurable_id)
    have hwd : ∫⁻ y, ENNReal.ofReal (Real.exp (κ * periodicRiesz d s (x - y)))
        ∂(withDensityReal ρ) = ∫⁻ y, ENNReal.ofReal (ρ y) *
          ENNReal.ofReal (Real.exp (κ * periodicRiesz d s (x - y))) := by
      unfold withDensityReal
      exact lintegral_withDensity_eq_lintegral_mul _ (ENNReal.measurable_ofReal.comp hρ.measurable) hmG
    have htop : ∫⁻ y, ENNReal.ofReal (Real.exp (κ * periodicRiesz d s (x - y))) = ⊤ :=
      (lintegral_sub_left_eq_self (fun z : Torus d => ENNReal.ofReal (Real.exp (κ * periodicRiesz d s z))) x).trans
        (q42_torus_exp_top hd hs0 hsd hκ)
    rw [hwd]
    refine top_le_iff.1 ?_
    calc (⊤ : ℝ≥0∞) = ENNReal.ofReal c * ∫⁻ y, ENNReal.ofReal (Real.exp (κ * periodicRiesz d s (x - y))) := by
          rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hc).ne']
      _ = ∫⁻ y, ENNReal.ofReal c * ENNReal.ofReal (Real.exp (κ * periodicRiesz d s (x - y))) :=
          (lintegral_const_mul _ hmG).symm
      _ ≤ ∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal (Real.exp (κ * periodicRiesz d s (x - y))) :=
          lintegral_mono fun y => by
            gcongr
            exact hcρ y
  simp_rw [inner]
  rw [lintegral_const, measure_univ, mul_one]

/-- Density bounds `0 < c ≤ ρ ≤ Λ` for a continuous positive density on the torus. -/
theorem q42_density_bounds {ρ : Torus d → ℝ} (hρc : Continuous ρ) (hpos : ∀ x, 0 < ρ x) :
    ∃ c : ℝ, 0 < c ∧ (∀ x, c ≤ ρ x) ∧ ∃ Λ : ℝ, ∀ x, ρ x ≤ Λ := by
  obtain ⟨x0, -, hx0⟩ := (isCompact_univ (X := Torus d)).exists_isMinOn Set.univ_nonempty
    hρc.continuousOn
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hρc.continuousOn
  refine ⟨ρ x0, hpos x0, fun x => hx0 (Set.mem_univ x), M, fun x => ?_⟩
  have := hM x (Set.mem_univ _)
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

/-- Real inequality for the pointwise lower bound of the Gibbs density power. -/
theorem q42_real_bound {Z ε β g F C : ℝ} {N : ℝ} (hZ : 0 < Z) (hε : 0 < ε) (hβ : 0 < β)
    (hN : 0 < N) (hC : g / N - C ≤ N * F) :
    Z ^ ε * Real.exp (-(ε * β * C)) * Real.exp (ε * β / N * g) ≤
      (Z * Real.exp (β * N * F)) ^ ε := by
  rw [Real.mul_rpow hZ.le (Real.exp_pos _).le, ← Real.exp_mul, mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hZ.le _)
  apply Real.exp_le_exp.2
  have h1 := mul_le_mul_of_nonneg_left hC (le_of_lt (mul_pos hε hβ))
  have e1 : ε * β / N * g = ε * β * (g / N) := by ring
  have e2 : ε * β * (g / N - C) = ε * β * (g / N) - ε * β * C := by ring
  have e3 : ε * β * (N * F) = β * N * F * ε := by ring
  linarith [h1, e1, e2, e3]

/-- Measurability of the modulated energy. -/
theorem q42_energy_measurable {N : ℕ} {g : Torus d → ℝ} (hg : Measurable g)
    (μ : Measure (Torus d)) [SFinite μ] :
    Measurable (fun X : Config d N => modulatedEnergyKernel g X μ) := by
  unfold modulatedEnergyKernel modulatedEnergy
  have h1 : Measurable (fun X : Config d N => ∑ i, ∑ j ∈ Finset.univ.erase i,
      g (X i - X j)) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      hg.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
  have h2 : Measurable (fun X : Config d N => ∑ i, ∫ y, g (X i - y) ∂μ) :=
    Finset.measurable_sum _ fun i _ => (PoleCavityAux.measurable_convMeasure hg μ).comp
      (measurable_pi_apply i)
  exact (((measurable_const.mul h1).sub (measurable_const.mul h2)).add measurable_const)


/-- The inverse-Gibbs moment `∫ (d(μ^{⊗N})/dℚ_{N,β})^{1+ε} dℚ = ∞`. -/
theorem q42_gibbs_moment (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (N : ℕ) (hN : 2 ≤ N) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ X, ((Measure.pi fun _ : Fin N => withDensityReal ρ).rnDeriv
        (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) X) ^ (1 + ε)
      ∂(modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) = ⊤ := by
  have hμp : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨cρ, hcρ0, hcρ, Λ, hΛ⟩ := q42_density_bounds (ρ := ρ)
    (HRS.StaticLimitAux.continuous_of_smooth hρ.smooth) hρ.pos
  have hgm : Measurable (periodicRiesz d s) :=
    HRS.PoleCavityAux.measurable_periodicRiesz hd hs0.le hsd
  have hF : Measurable (fun X : Config d N =>
      modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)) :=
    q42_energy_measurable hgm _
  set i0 : Fin N := ⟨0, by omega⟩ with hi0
  set i1 : Fin N := ⟨1, by omega⟩ with hi1
  have hij : i0 ≠ i1 := fun h => absurd (congrArg Fin.val h) (by simp [hi0, hi1])
  obtain ⟨C, hC⟩ := q42_energy_lower hd hs0.le hsd hρ.density Λ hΛ i0 i1 hij
  obtain ⟨Bg, hBg⟩ := periodicRiesz_ge (d := d) hd hs0.le hsd
  -- uniform upper bound on the exponent
  set M0 : ℝ := β * (Bg / N + C) with hM0
  have hbound : ∀ X : Config d N,
      -β * N * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ) ≤ M0 := by
    intro X
    have h1 : -Bg / N ≤ periodicRiesz d s (X i0 - X i1) / N :=
      div_le_div_of_nonneg_right (hBg _) hN0.le
    have h2 : -Bg / N - C ≤ N * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ) := by
      linarith [hC X]
    have h3 := mul_le_mul_of_nonneg_left h2 hβ.le
    linarith [h3, (by ring : -β * N * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ) =
      -(β * (N * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)))),
      (by ring : β * (-Bg / N - C) = -(β * (Bg / N + C)))]
  set P := Measure.pi fun _ : Fin N => withDensityReal ρ with hP
  haveI : IsProbabilityMeasure P := by rw [hP]; infer_instance
  have hint : Integrable (fun X : Config d N =>
      Real.exp (-β * N * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ))) P := by
    refine Integrable.mono' (integrable_const (Real.exp M0))
      (Real.measurable_exp.comp (measurable_const.mul hF)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.2 (hbound X)
  have hZ : 0 < ∫ X : Config d N,
      Real.exp (-β * N * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)) ∂P := by
    refine (integral_pos_iff_support_of_nonneg (fun X => (Real.exp_pos _).le) hint).2 ?_
    have hsupp : Function.support (fun X : Config d N =>
        Real.exp (-β * N * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ))) =
        Set.univ := Set.eq_univ_of_forall fun X => (Real.exp_pos _).ne'
    rw [hsupp, measure_univ]
    norm_num
  set Zr : ℝ := ∫ X : Config d N,
      Real.exp (-β * N * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)) ∂P
    with hZr
  have hK : (fun X : Config d N => ENNReal.ofReal (Real.exp
      (-β * N * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)))) =
      fun X => ENNReal.ofReal (Real.exp
      (-β * N * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ))) := rfl
  set W : Config d N → ℝ≥0∞ := fun X => ENNReal.ofReal (Real.exp
    (-β * N * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ))) with hW
  set cQ : ℝ≥0∞ := (ENNReal.ofReal Zr)⁻¹ with hcQ
  have hQdef : modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) = cQ • P.withDensity W :=
    rfl
  have hWm : Measurable W := ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp (measurable_const.mul hF))
  have hWne : ∀ X, W X ≠ 0 := fun X => (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hcne : cQ ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hQeq : modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) =
      P.withDensity (fun X => cQ * W X) := by
    rw [hQdef, ← withDensity_smul cQ hWm]
    rfl
  have hQprob : IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) :=
    modulatedGibbs_isProbabilityMeasure (periodicRiesz d s) β (withDensityReal ρ) hZ hint
  have hPQ : P ≪ modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) := by
    rw [hQeq]
    exact withDensity_absolutelyContinuous' (measurable_const.mul hWm).aemeasurable
      (Filter.Eventually.of_forall fun X => mul_ne_zero hcne (hWne X))
  have hrnQP : (P.withDensity (fun X => cQ * W X)).rnDeriv P =ᵐ[P] fun X => cQ * W X :=
    Measure.rnDeriv_withDensity P (measurable_const.mul hWm)
  have hrn2 : (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)).rnDeriv P =ᵐ[P]
      fun X => cQ * W X := by
    rw [hQeq]
    exact hrnQP
  have hinv := Measure.inv_rnDeriv hPQ
  have hrn : ∀ᵐ X ∂P, P.rnDeriv (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) X =
      (cQ * W X)⁻¹ := by
    filter_upwards [hinv, hrn2] with X h1 h2
    have h1' : (P.rnDeriv (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) X)⁻¹ =
        (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)).rnDeriv P X := h1
    calc P.rnDeriv (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) X
        = (P.rnDeriv (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) X)⁻¹⁻¹ :=
          (inv_inv _).symm
      _ = ((modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)).rnDeriv P X)⁻¹ := by
          rw [h1']
      _ = (cQ * W X)⁻¹ := by rw [h2]
  set Q := modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) with hQ
  have hrat : ∀ X : Config d N, (P.rnDeriv Q X) ^ (1 + ε) = P.rnDeriv Q X * (P.rnDeriv Q X) ^ ε := by
    intro X
    rw [ENNReal.rpow_add_of_nonneg (1 : ℝ) ε zero_le_one hε.le, ENNReal.rpow_one]
  have step1 : ∫⁻ X, (P.rnDeriv Q X) ^ (1 + ε) ∂Q = ∫⁻ X, P.rnDeriv Q X * (P.rnDeriv Q X) ^ ε ∂Q :=
    lintegral_congr fun X => hrat X
  have step2 : ∫⁻ X, P.rnDeriv Q X * (P.rnDeriv Q X) ^ ε ∂Q = ∫⁻ X, (P.rnDeriv Q X) ^ ε ∂P :=
    lintegral_rnDeriv_mul hPQ ((Measure.measurable_rnDeriv P Q).pow_const ε).aemeasurable
  have step3 : ∫⁻ X, (P.rnDeriv Q X) ^ ε ∂P = ∫⁻ X, (cQ * W X)⁻¹ ^ ε ∂P :=
    lintegral_congr_ae (hrn.mono fun X hX => by simp only [hX])
  set κ : ℝ := ε * β / N with hκ
  have hκpos : 0 < κ := div_pos (mul_pos hε hβ) hN0
  set K : ℝ := Zr ^ ε * Real.exp (-(ε * β * C)) with hKdef
  have hKpos : 0 < K := mul_pos (Real.rpow_pos_of_pos hZ _) (Real.exp_pos _)
  have hpt : ∀ X : Config d N, ENNReal.ofReal K *
      ENNReal.ofReal (Real.exp (κ * periodicRiesz d s (X i0 - X i1))) ≤ (cQ * W X)⁻¹ ^ ε := by
    intro X
    have hpos : 0 < Zr⁻¹ * Real.exp (-β * N * modulatedEnergyKernel (periodicRiesz d s) X
        (withDensityReal ρ)) := mul_pos (inv_pos.2 hZ) (Real.exp_pos _)
    have e1 : cQ * W X = ENNReal.ofReal (Zr⁻¹ * Real.exp (-β * N *
        modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ))) := by
      rw [hcQ, hW, ENNReal.ofReal_mul (inv_nonneg.2 hZ.le), ENNReal.ofReal_inv_of_pos hZ]
    have hE : (Real.exp (-β * N * modulatedEnergyKernel (periodicRiesz d s) X
        (withDensityReal ρ)))⁻¹ = Real.exp (β * N * modulatedEnergyKernel (periodicRiesz d s) X
        (withDensityReal ρ)) := by
      rw [← Real.exp_neg]
      congr 1
      ring
    have hinv : (cQ * W X)⁻¹ = ENNReal.ofReal (Zr * Real.exp (β * N *
        modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ))) := by
      rw [e1, ← ENNReal.ofReal_inv_of_pos hpos]
      congr 1
      rw [mul_inv, inv_inv, hE]
    rw [hinv, ENNReal.ofReal_rpow_of_nonneg (mul_pos hZ (Real.exp_pos _)).le hε.le,
      ← ENNReal.ofReal_mul hKpos.le]
    apply ENNReal.ofReal_le_ofReal
    exact q42_real_bound hZ hε hβ hN0 (hC X)
  have hGm : Measurable (fun X : Config d N =>
      ENNReal.ofReal (Real.exp (κ * periodicRiesz d s (X i0 - X i1)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
      (hgm.comp ((measurable_pi_apply i0).sub (measurable_pi_apply i1)))))
  have hpair := q42_pair_lintegral_top hd hs0 hsd hρ.density hcρ0 hcρ i0 i1 hij hκpos
  have hG_int : ∫⁻ X, ENNReal.ofReal K *
      ENNReal.ofReal (Real.exp (κ * periodicRiesz d s (X i0 - X i1))) ∂P = ⊤ := by
    rw [lintegral_const_mul _ hGm, hP, hpair, ENNReal.mul_top (ENNReal.ofReal_pos.2 hKpos).ne']
  have hlow : ∫⁻ X, ENNReal.ofReal K * ENNReal.ofReal (Real.exp (κ * periodicRiesz d s (X i0 - X i1)))
      ∂P ≤ ∫⁻ X, (cQ * W X)⁻¹ ^ ε ∂P := lintegral_mono (fun X => hpt X)
  rw [hG_int] at hlow
  rw [step1, step2, step3]
  exact top_unique hlow

end HRS
