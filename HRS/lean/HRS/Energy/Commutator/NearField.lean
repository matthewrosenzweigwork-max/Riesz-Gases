import HRS.Energy.Commutator.Basic

/-!
# Near-field (nearest-neighbour) control by the modulated energy (packet CM-NF)

Sources: `[HCRS]` Prop. 2.11, Cor. 2.13, Cor. 2.14 (= (2.50)-(2.51)); `[RS]` Prop. 2.3 (2.29), Cor. 2.4.
The statement used by the route `d-2 ≤ s < d` is `nearField_control`.

**Route (torus, heat truncation; reuses `periodic_coercivity`).**  Use the repository's heat
truncation `g = gT_ε + nearF_ε` (`CoercAux.periodicRiesz_decomp`, `gT_eq_integral`, `nearF_ge`,
`CoercAux.rieszEnergy_ge_aux`, `Q_eq_tsum`) with `ε = (c λ)²`:
* `energy_split_near`: *keep* the pair sum `(1/2N²)∑_{i≠j} nearF_ε(x_i-x_j)` that
  `rieszEnergy_ge_aux` discards (the identity `F_N = ½ Esq - gT(0)/2N + (1/2N²)∑_{i≠j} nearF
  - N⁻¹∑ nearF*μ(x_i) + ½∬ nearF μ μ` is exact; `Esq ≥ 0` by Fourier positivity
  `cT ≥ 0`, and `nearF*μ ∈ [-B', ΛB']`, `B' = nearB`, `CoercAux.nearF_conv_bounds`);
* `nearF_lower_pos/zero`: `nearF_ε(x) ≥ c |x|^{-s} - C ε^{(d-s)/2}` (`s > 0`),
  `≥ log(√ε/|x|) - C` (`s = 0`) for `|x| ≤ δ √ε`.  Proof: `1 + Ψ(x,u) ≥ (π/u)^{d/2} e^{-π²|x|²/u}`
  (one term of the positive Poisson series `KernelAux.theta_images`), then the Euclidean Mellin
  integral `A∫_0^ε u^{a-1}(π/u)^{d/2} e^{-π²|x|²/u} du` (incomplete Gamma function; `subA_zero_mul`
  for the exact coefficient `1/2` of the logarithm).  **Torus difference with `[HCRS]`**: there
  `f_η ≥ 0`; here `nearF ≥ -B'` only (the zero mode of `g` is removed), which costs the additive
  `(1+Λ) B' ≲ Λ λ^{d-s}`, exactly the allowed error.
* `nearField_control`: choose `ε` so that `4 r_i ≤ δ √ε` for all `i` (this is why the cap of
  `smearRadius` is `θ_* λ`, `θ_* = 1/8`), keep for each `i` one pair `(i, nn(i))`, and absorb
  `gT_ε(0)/(2N) ≲ aNΛ` (`CoercAux.gT_zero_le_pos/zero`, `diag_const`).

Estimated size 600-800 lines, difficulty medium (incomplete-Gamma lower bound).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Real

namespace HRS.Commutator

variable {d : ℕ} {s : ℝ}

/-! ### Auxiliary lemmas (Poisson lower bound and Mellin integrals) -/

namespace NearFieldAux



theorem tdist_sub_zero (x y : Torus d) : KernelGrad.tdist x y = KernelGrad.tdist (x - y) 0 := by
  simp [KernelGrad.tdist]

theorem exists_box (x : Torus d) : ∃ y : Fin d → ℝ, (∀ i, |y i| ≤ 1/2) ∧ KernelAux.boxPt y = x := by
  choose y hy1 hy2 using fun i => exists_rep (x i)
  exact ⟨y, hy1, funext fun i => (hy2 i).symm⟩

theorem sum_sq_eq_tdist {y : Fin d → ℝ} (hy : ∀ i, |y i| ≤ 1/2) :
    ∑ i, y i ^ 2 = KernelGrad.tdist (KernelAux.boxPt y) 0 ^ 2 := by
  rw [KernelGrad.tdist_zero_right, CoercAux.centeredRep_boxPt hy, EuclideanSpace.norm_sq_eq]
  simp [sq_abs]

theorem nearF_eq_integral (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε)
    {x : Torus d} (hx : x ≠ 0) :
    CoercAux.nearF d s ε x = KernelAux.subA d s *
      ∫ u in Ioc 0 ε, u ^ (((d:ℝ) - s) / 2 - 1) * psiFn x u := by
  have h := CoercAux.periodicRiesz_decomp hd hs0 hsd hε x hx
  unfold CoercAux.nearF
  rw [if_neg hx, h]
  ring

theorem theta_lower {y : Fin d → ℝ} {u : ℝ} (hu : 0 < u) :
    Real.sqrt (Real.pi / u) ^ d * Real.exp (-(Real.pi ^ 2 * ∑ i, y i ^ 2) / u) ≤ 1 + psiFn (KernelAux.boxPt y) u := by
  rw [← psi_eq _ hu, KernelAux.theta_images y hu]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  -- summability of the Poisson series over `ℤ^d`
  have hs : ∀ i : Fin d, Summable fun n : ℤ => |Real.exp (-(π^2 * ((n:ℝ) - y i)^2 / u))| := by
    intro i
    simp_rw [abs_of_pos (Real.exp_pos _)]
    have : Summable fun n : ℤ => Real.exp (-(π^2 / u) * ((n:ℝ) - y i)^2) :=
      KernelAux.summable_shift_gauss (by positivity) _
    refine this.congr fun n => ?_
    congr 1; ring
  have hsum : Summable fun m : Fin d → ℤ =>
      Real.exp (-(π^2 * ∑ i, (((m i : ℤ) : ℝ) - y i)^2 / u)) := by
    refine (KernelAux.pi_hasSum_real d (fun i n => Real.exp (-(π^2 * ((n:ℝ) - y i)^2 / u))) hs).summable.congr
      fun m => ?_
    rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.mul_sum, mul_div_assoc,
      Finset.sum_div]
  have h0 : Real.exp (-(Real.pi ^ 2 * ∑ i, y i ^ 2) / u) =
      Real.exp (-(Real.pi ^ 2 * ∑ i, ((((fun _ : Fin d => (0:ℤ)) i : ℤ) : ℝ) - y i) ^ 2 / u)) := by
    congr 1
    simp only [Int.cast_zero, zero_sub, neg_sq, ← Finset.sum_div, ← mul_div_assoc]
    ring_nf
  rw [h0]
  exact hsum.le_tsum (fun _ => 0) (fun m _ => (Real.exp_pos _).le)

theorem sqrtpi_pow_eq (d : ℕ) : Real.sqrt Real.pi ^ d = Real.pi ^ ((d : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
  congr 1; ring

theorem rpow_identity (d : ℕ) (s : ℝ) {u : ℝ} (hu : 0 < u) :
    u ^ (((d:ℝ) - s) / 2 - 1) * Real.sqrt (Real.pi / u) ^ d =
      Real.sqrt Real.pi ^ d * u ^ (-s / 2 - 1) := by
  have h1 : Real.sqrt (Real.pi / u) ^ d = (Real.pi / u) ^ ((d:ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; ring
  have h2 : (Real.pi / u) ^ ((d:ℝ) / 2) = Real.pi ^ ((d:ℝ) / 2) / u ^ ((d:ℝ) / 2) :=
    Real.div_rpow Real.pi_pos.le hu.le _
  have h4 : u ^ (((d:ℝ) - s) / 2 - 1) / u ^ ((d:ℝ) / 2) = u ^ (-s / 2 - 1) := by
    rw [← Real.rpow_sub hu]; congr 1; ring
  rw [h1, h2, sqrtpi_pow_eq, ← h4]
  ring

theorem nearF_ge_core (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε)
    {y : Fin d → ℝ} (hx : KernelAux.boxPt y ≠ 0) :
    KernelAux.subA d s * (∫ u in Ioc (Real.pi ^ 2 * ∑ i, y i ^ 2) ε,
        Real.sqrt Real.pi ^ d * u ^ (-s / 2 - 1) * Real.exp (-(Real.pi ^ 2 * ∑ i, y i ^ 2) / u))
      - CoercAux.nearB d s ε ≤ CoercAux.nearF d s ε (KernelAux.boxPt y) := by
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set c : ℝ := Real.pi ^ 2 * ∑ i, y i ^ 2 with hc_def
  have hc0 : 0 ≤ c := by
    rw [hc_def]; have : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    positivity
  have hA := CoercAux.subA_nonneg_one hd hs0 hsd
  set x := KernelAux.boxPt y with hx_def
  -- the rewritten integrand
  set Φ : ℝ → ℝ := fun u => Real.sqrt Real.pi ^ d * u ^ (-s / 2 - 1) * Real.exp (-c / u) with hΦ
  have hψi : IntegrableOn (fun u : ℝ => u ^ (a - 1) * psiFn x u) (Ioc 0 ε) :=
    (KernelAux.integrableOn_psi hsd x hx).mono_set (fun u hu => mem_Ioi.mpr hu.1)
  have hri : IntegrableOn (fun u : ℝ => u ^ (a - 1)) (Ioc 0 ε) := CoercAux.integrableOn_Ioc_rpow ha hε
  have hbound : ∀ u ∈ Ioc 0 ε, Φ u ≤ u ^ (a - 1) * (1 + psiFn x u) := by
    intro u hu
    have hu0 : 0 < u := hu.1
    have h1 := theta_lower (y := y) hu0
    have hr := rpow_identity d s hu0
    have hu1 : 0 ≤ u ^ (a - 1) := (Real.rpow_pos_of_pos hu0 _).le
    have e : Φ u = u ^ (a - 1) * (Real.sqrt (Real.pi / u) ^ d * Real.exp (-c / u)) := by
      rw [hΦ]; simp only; rw [← hr]; ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ hu1
    rw [hc_def]
    exact h1
  have hΦm : Measurable Φ := by
    rw [hΦ]; fun_prop
  have hΦnn : ∀ u, 0 < u → 0 ≤ Φ u := by
    intro u hu
    rw [hΦ]; simp only
    have := Real.rpow_pos_of_pos hu (-s / 2 - 1)
    have := Real.exp_pos (-c / u)
    positivity
  have hΦi : IntegrableOn Φ (Ioc 0 ε) := by
    refine Integrable.mono' ((hψi.add hri)) hΦm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hΦnn u hu.1)]
    have := hbound u hu
    simp only [Pi.add_apply]
    rw [mul_add, mul_one] at this
    linarith
  have hmono : ∫ u in Ioc c ε, Φ u ≤ ∫ u in Ioc 0 ε, Φ u :=
    setIntegral_mono_set hΦi
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun u hu => hΦnn u hu.1))
      (Ioc_subset_Ioc_left hc0).eventuallyLE
  have hle2 : ∫ u in Ioc 0 ε, Φ u ≤ ∫ u in Ioc 0 ε, (u ^ (a - 1) * psiFn x u + u ^ (a - 1)) := by
    refine setIntegral_mono_on hΦi (hψi.add hri) measurableSet_Ioc fun u hu => ?_
    have := hbound u hu
    rw [mul_add, mul_one] at this
    linarith
  rw [integral_add hψi hri, CoercAux.integral_Ioc_rpow ha hε] at hle2
  have hF := nearF_eq_integral hd hs0 hsd hε hx
  have hB : CoercAux.nearB d s ε = KernelAux.subA d s * (ε ^ a / a) := rfl
  have key := mul_le_mul_of_nonneg_left (hmono.trans hle2) hA
  rw [mul_add] at key
  rw [hF, hB]
  linarith

theorem continuousOn_Icc_rpow {c ε r : ℝ} (hc : 0 < c) :
    ContinuousOn (fun u : ℝ => u ^ r) (Icc c ε) :=
  continuousOn_id.rpow_const fun _ hu => Or.inl (ne_of_gt (lt_of_lt_of_le hc hu.1))

theorem continuousOn_Icc_exp {c ε : ℝ} (hc : 0 < c) :
    ContinuousOn (fun u : ℝ => Real.exp (-c / u)) (Icc c ε) := by
  refine Real.continuous_exp.comp_continuousOn ?_
  exact ContinuousOn.div continuousOn_const continuousOn_id fun u (hu : u ∈ Icc c ε) =>
    ne_of_gt (lt_of_lt_of_le hc hu.1)

/-- Lower bound of the Euclidean Mellin integral, `s > 0`. -/
theorem pos_integral_lower {s : ℝ} (hs : 0 < s) {c ε : ℝ} (hc : 0 < c) (hcε : 4 * c ≤ ε) :
    Real.sqrt Real.pi ^ d * (Real.exp (-1) * ((2 / s) * (c ^ (-s / 2) - ε ^ (-s / 2)))) ≤
      ∫ u in Ioc c ε, Real.sqrt Real.pi ^ d * u ^ (-s / 2 - 1) * Real.exp (-c / u) := by
  have hc' : c ≤ ε := by linarith
  have hP : 0 ≤ Real.sqrt Real.pi ^ d := by positivity
  have hcont : ContinuousOn (fun u : ℝ => Real.sqrt Real.pi ^ d * u ^ (-s / 2 - 1) * Real.exp (-c / u))
      (Icc c ε) :=
    ((continuousOn_const.mul (continuousOn_Icc_rpow hc))).mul (continuousOn_Icc_exp hc)
  have hL : IntegrableOn (fun u : ℝ => u ^ (-s / 2 - 1)) (Ioc c ε) :=
    (continuousOn_Icc_rpow (ε := ε) (r := -s / 2 - 1) hc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hU : IntegrableOn (fun u : ℝ => Real.sqrt Real.pi ^ d * u ^ (-s / 2 - 1) * Real.exp (-c / u))
      (Ioc c ε) := hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hpt : ∀ u ∈ Ioc c ε, Real.sqrt Real.pi ^ d * (Real.exp (-1) * u ^ (-s / 2 - 1)) ≤
      Real.sqrt Real.pi ^ d * u ^ (-s / 2 - 1) * Real.exp (-c / u) := by
    intro u hu
    have hu0 : 0 < u := lt_of_le_of_lt hc.le hu.1
    have hcu : -c / u ≥ -1 := by
      rw [ge_iff_le, le_div_iff₀ hu0]; linarith [hu.1]
    have he : Real.exp (-1) ≤ Real.exp (-c / u) := Real.exp_le_exp.mpr hcu
    have hr := Real.rpow_pos_of_pos hu0 (-s / 2 - 1)
    calc Real.sqrt Real.pi ^ d * (Real.exp (-1) * u ^ (-s / 2 - 1))
        = Real.sqrt Real.pi ^ d * u ^ (-s / 2 - 1) * Real.exp (-1) := by ring
      _ ≤ Real.sqrt Real.pi ^ d * u ^ (-s / 2 - 1) * Real.exp (-c / u) := by gcongr
  have hint : ∫ u in Ioc c ε, u ^ (-s / 2 - 1) = (2 / s) * (c ^ (-s / 2) - ε ^ (-s / 2)) := by
    rw [← intervalIntegral.integral_of_le hc', integral_rpow (Or.inr ⟨by intro h; linarith,
      by rw [Set.uIcc_of_le hc']; intro h; linarith [h.1]⟩)]
    have e : -s / 2 - 1 + 1 = -s / 2 := by ring
    rw [e]
    have hs2 : (-s / 2) ≠ 0 := by intro h; linarith
    field_simp
    ring
  calc Real.sqrt Real.pi ^ d * (Real.exp (-1) * ((2 / s) * (c ^ (-s / 2) - ε ^ (-s / 2))))
      = ∫ u in Ioc c ε, Real.sqrt Real.pi ^ d * (Real.exp (-1) * u ^ (-s / 2 - 1)) := by
        rw [integral_const_mul, integral_const_mul, hint]
    _ ≤ _ := setIntegral_mono_on ((hL.const_mul (Real.exp (-1))).const_mul _) hU measurableSet_Ioc hpt

theorem rpow_zero_eq_inv (u : ℝ) : u ^ (-(0:ℝ) / 2 - 1) = u⁻¹ := by
  rw [show -(0:ℝ) / 2 - 1 = -1 by norm_num, Real.rpow_neg_one]

/-- Lower bound of the Euclidean Mellin integral, `s = 0`. -/
theorem zero_integral_lower {c ε : ℝ} (hc : 0 < c) (hcε : c ≤ ε) :
    Real.sqrt Real.pi ^ d * (Real.log (ε / c) - 1) ≤
      ∫ u in Ioc c ε, Real.sqrt Real.pi ^ d * u ^ (-(0:ℝ) / 2 - 1) * Real.exp (-c / u) := by
  have hε : 0 < ε := lt_of_lt_of_le hc hcε
  have hP : 0 ≤ Real.sqrt Real.pi ^ d := by positivity
  have hi1 : IntegrableOn (fun u : ℝ => u⁻¹) (Ioc c ε) := by
    refine (ContinuousOn.inv₀ continuousOn_id (fun u (hu : u ∈ Icc c ε) =>
      ne_of_gt (lt_of_lt_of_le hc hu.1))).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hi2 : IntegrableOn (fun u : ℝ => u ^ (-2 : ℝ)) (Ioc c ε) :=
    (continuousOn_Icc_rpow (ε := ε) (r := -2) hc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  -- the explicit antiderivatives
  have hA1 : ∫ u in c..ε, u⁻¹ = Real.log (ε / c) := integral_inv_of_pos hc hε
  have hA2 : ∫ u in c..ε, u ^ (-2 : ℝ) = c⁻¹ - ε⁻¹ := by
    rw [integral_rpow (Or.inr ⟨by norm_num, by rw [Set.uIcc_of_le hcε]; intro h; linarith [h.1]⟩)]
    norm_num [Real.rpow_neg_one]
    ring
  have hlow : Real.log (ε / c) - 1 ≤ ∫ u in Ioc c ε, (u⁻¹ - c * u ^ (-2 : ℝ)) := by
    have ii1 : IntervalIntegrable (fun u : ℝ => u⁻¹) volume c ε :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hcε).mpr hi1
    have ii2 : IntervalIntegrable (fun u : ℝ => c * u ^ (-2 : ℝ)) volume c ε :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hcε).mpr hi2).const_mul c
    rw [← intervalIntegral.integral_of_le hcε, intervalIntegral.integral_sub ii1 ii2,
      intervalIntegral.integral_const_mul, hA1, hA2]
    have : c * (c⁻¹ - ε⁻¹) = 1 - c / ε := by
      field_simp
    rw [this]
    have : 0 ≤ c / ε := div_nonneg hc.le hε.le
    linarith
  have hmono : ∫ u in Ioc c ε, Real.sqrt Real.pi ^ d * (u⁻¹ - c * u ^ (-2 : ℝ)) ≤
      ∫ u in Ioc c ε, Real.sqrt Real.pi ^ d * u ^ (-(0:ℝ) / 2 - 1) * Real.exp (-c / u) := by
    refine setIntegral_mono_on ((hi1.sub (hi2.const_mul c)).const_mul _) ?_ measurableSet_Ioc ?_
    · have hcont : ContinuousOn (fun u : ℝ => Real.sqrt Real.pi ^ d * u ^ (-(0:ℝ) / 2 - 1) * Real.exp (-c / u))
          (Icc c ε) := by
        have e : (fun u : ℝ => Real.sqrt Real.pi ^ d * u ^ (-(0:ℝ) / 2 - 1) * Real.exp (-c / u)) =
            fun u : ℝ => Real.sqrt Real.pi ^ d * u⁻¹ * Real.exp (-c / u) := by
          funext u; rw [rpow_zero_eq_inv]
        rw [e]
        exact ((continuousOn_const.mul (ContinuousOn.inv₀ continuousOn_id (fun u (hu : u ∈ Icc c ε) =>
          ne_of_gt (lt_of_lt_of_le hc hu.1)))).mul (continuousOn_Icc_exp hc))
      exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · intro u hu
      have hu0 : 0 < u := lt_of_le_of_lt hc.le hu.1
      rw [rpow_zero_eq_inv]
      have h1 := Real.add_one_le_exp (-c / u)
      have h2 : u ^ (-2 : ℝ) = u⁻¹ * u⁻¹ := by
        rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hu0.le, Real.rpow_natCast]
        ring
      have h3 : u⁻¹ * (1 + -c / u) ≤ u⁻¹ * Real.exp (-c / u) :=
        mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hu0.le)
      have h4 : u⁻¹ - c * u ^ (-2 : ℝ) = u⁻¹ * (1 + -c / u) := by
        rw [h2]; field_simp; ring
      rw [h4]
      have := mul_le_mul_of_nonneg_left h3 hP
      linarith [this, mul_assoc (Real.sqrt Real.pi ^ d) u⁻¹ (Real.exp (-c / u))]
  have := mul_le_mul_of_nonneg_left hlow hP
  rw [integral_const_mul] at hmono
  linarith [hmono, this]

theorem rpow_pi_sq (s : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (Real.pi ^ 2 * r ^ 2) ^ (-s / 2) = Real.pi ^ (-s) * r ^ (-s) := by
  rw [Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  · rw [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]; congr 1; push_cast; ring
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hr]; congr 1; push_cast; ring

end NearFieldAux

/-- Exact splitting of the modulated energy with the near-field pair sum retained (one direction
suffices): `(1/2N²)∑_{i≠j} nearF_ε(x_i-x_j) ≤ F_N + gT_ε(0)/(2N) + (1+Λ) B'_ε`. -/
theorem energy_split_near (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε)
    {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ x, ρ x ≤ Λ)
    {N : ℕ} (hN : 0 < N) (X : Config d N) (hX : X ∉ collisionSet d N) :
    (1 / (2 * (N : ℝ) ^ 2)) *
        ∑ i, ∑ j ∈ Finset.univ.erase i, CoercAux.nearF d s ε (X i - X j) ≤
      rieszEnergy d s X (withDensityReal ρ) + CoercAux.gT d s ε 0 / (2 * N) +
        (1 + Λ) * CoercAux.nearB d s ε := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have := isProb_withDensityReal hρ
  have hB0 : 0 ≤ CoercAux.nearB d s ε := CoercAux.nearB_nonneg hd hs0 hsd hε
  have hΛB : 0 ≤ Λ * CoercAux.nearB d s ε := mul_nonneg hΛ0 hB0
  have hdist : ∀ i j : Fin N, i ≠ j → X i - X j ≠ 0 := by
    intro i j hij h
    exact hX ⟨i, j, hij, sub_eq_zero.mp h⟩
  -- the smooth part and the near part, as functions of `x`
  have hGc : Continuous fun x => ∫ y, CoercAux.gT d s ε (x - y) ∂(withDensityReal ρ) :=
    continuous_conv0 (CoercAux.continuous_gT hd hs0 hsd hε) _
  have hGi : Integrable (fun x => ∫ y, CoercAux.gT d s ε (x - y) ∂(withDensityReal ρ))
      (withDensityReal ρ) :=
    hGc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgint : ∀ x : Torus d, Integrable (fun y => CoercAux.gT d s ε (x - y)) (withDensityReal ρ) := by
    intro x
    exact ((CoercAux.continuous_gT hd hs0 hsd hε).comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hFb : ∀ x : Torus d, -CoercAux.nearB d s ε ≤ ∫ y, CoercAux.nearF d s ε (x - y) ∂(withDensityReal ρ) ∧
      ∫ y, CoercAux.nearF d s ε (x - y) ∂(withDensityReal ρ) ≤ Λ * CoercAux.nearB d s ε := by
    intro x
    obtain ⟨_, h1, h2⟩ := CoercAux.nearF_conv_bounds hd hs0 hsd hε hρ hΛ0 hΛ x
    exact ⟨h1, h2⟩
  have hFint : ∀ x : Torus d, Integrable (fun y => CoercAux.nearF d s ε (x - y)) (withDensityReal ρ) :=
    fun x => (CoercAux.nearF_conv_bounds hd hs0 hsd hε hρ hΛ0 hΛ x).1
  have hFm : StronglyMeasurable fun x => ∫ y, CoercAux.nearF d s ε (x - y) ∂(withDensityReal ρ) :=
    StronglyMeasurable.integral_prod_right'
      (f := fun p : Torus d × Torus d => CoercAux.nearF d s ε (p.1 - p.2))
      ((CoercAux.measurable_nearF hd hs0 hsd hε).comp (measurable_fst.sub measurable_snd)).stronglyMeasurable
  have hFi : Integrable (fun x => ∫ y, CoercAux.nearF d s ε (x - y) ∂(withDensityReal ρ))
      (withDensityReal ρ) := by
    refine Integrable.mono' (integrable_const ((1 + Λ) * CoercAux.nearB d s ε)) hFm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_le]
    obtain ⟨h1, h2⟩ := hFb x
    constructor <;> nlinarith
  -- the Riesz kernel splits pointwise off the diagonal (a.e. in the integrated variable)
  have hPint : ∀ x : Torus d, ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ) =
      (∫ y, CoercAux.gT d s ε (x - y) ∂(withDensityReal ρ)) +
        ∫ y, CoercAux.nearF d s ε (x - y) ∂(withDensityReal ρ) := by
    intro x
    have h0 : ∀ᵐ y ∂(volume : Measure (Torus d)), y ≠ x := by
      rw [ae_iff]; simpa using volume_singleton_torus hd x
    have h1 : ∀ᵐ y ∂(withDensityReal ρ), y ≠ x := withDensity_absolutelyContinuous _ _ h0
    have h2 : ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ) =
        ∫ y, (CoercAux.gT d s ε (x - y) + CoercAux.nearF d s ε (x - y)) ∂(withDensityReal ρ) :=
      integral_congr_ae (h1.mono fun y hy =>
        CoercAux.periodicRiesz_eq_add (x - y) (sub_ne_zero.mpr (Ne.symm hy)))
    rw [h2, integral_add (hgint x) (hFint x)]
  have hPD : ∫ x, ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ) ∂(withDensityReal ρ) =
      (∫ x, ∫ y, CoercAux.gT d s ε (x - y) ∂(withDensityReal ρ) ∂(withDensityReal ρ)) +
        ∫ x, ∫ y, CoercAux.nearF d s ε (x - y) ∂(withDensityReal ρ) ∂(withDensityReal ρ) := by
    simp only [hPint]
    rw [integral_add hGi hFi]
  have hIF : -CoercAux.nearB d s ε ≤ ∫ x, ∫ y, CoercAux.nearF d s ε (x - y) ∂(withDensityReal ρ) ∂(withDensityReal ρ) := by
    have := integral_mono (integrable_const (-CoercAux.nearB d s ε)) hFi (fun x => (hFb x).1)
    simpa using this
  have hFs : ∑ i, ∫ y, CoercAux.nearF d s ε (X i - y) ∂(withDensityReal ρ) ≤
      N * (Λ * CoercAux.nearB d s ε) := by
    calc ∑ i, ∫ y, CoercAux.nearF d s ε (X i - y) ∂(withDensityReal ρ)
        ≤ ∑ _i : Fin N, Λ * CoercAux.nearB d s ε :=
          Finset.sum_le_sum fun i _ => (hFb (X i)).2
      _ = N * (Λ * CoercAux.nearB d s ε) := by simp
  have hFs' : (1 / (N : ℝ)) * ∑ i, ∫ y, CoercAux.nearF d s ε (X i - y) ∂(withDensityReal ρ) ≤
      Λ * CoercAux.nearB d s ε := by
    have h := mul_le_mul_of_nonneg_left hFs (by positivity : (0:ℝ) ≤ 1 / (N : ℝ))
    have e : (1 / (N : ℝ)) * (N * (Λ * CoercAux.nearB d s ε)) = Λ * CoercAux.nearB d s ε := by
      field_simp
    linarith
  -- pair sums
  have hpair : ∑ i, ∑ j ∈ Finset.univ.erase i, periodicRiesz d s (X i - X j) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, (CoercAux.gT d s ε (X i - X j) + CoercAux.nearF d s ε (X i - X j)) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj =>
      CoercAux.periodicRiesz_eq_add (X i - X j) (hdist i j (Finset.ne_of_mem_erase hj).symm)
  have hsplit : ∑ i, ∑ j ∈ Finset.univ.erase i, (CoercAux.gT d s ε (X i - X j) + CoercAux.nearF d s ε (X i - X j)) =
      (∑ i, ∑ j ∈ Finset.univ.erase i, CoercAux.gT d s ε (X i - X j)) +
        ∑ i, ∑ j ∈ Finset.univ.erase i, CoercAux.nearF d s ε (X i - X j) := by
    simp only [Finset.sum_add_distrib]
  have hgerase : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, CoercAux.gT d s ε (X i - X j) =
      ∑ j, CoercAux.gT d s ε (X i - X j) - CoercAux.gT d s ε 0 := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp
  have hgsum : ∑ i, ∑ j ∈ Finset.univ.erase i, CoercAux.gT d s ε (X i - X j) =
      (∑ i, ∑ j, CoercAux.gT d s ε (X i - X j)) - N * CoercAux.gT d s ε 0 := by
    rw [Finset.sum_congr rfl fun i _ => hgerase i, Finset.sum_sub_distrib]
    simp
  have hSP : ∑ i, ∑ j ∈ Finset.univ.erase i, periodicRiesz d s (X i - X j) =
      ((∑ i, ∑ j, CoercAux.gT d s ε (X i - X j)) - N * CoercAux.gT d s ε 0) +
        ∑ i, ∑ j ∈ Finset.univ.erase i, CoercAux.nearF d s ε (X i - X j) := by
    rw [hpair, hsplit, hgsum]
  have hTP : ∑ i, ∫ y, periodicRiesz d s (X i - y) ∂(withDensityReal ρ) =
      (∑ i, ∫ y, CoercAux.gT d s ε (X i - y) ∂(withDensityReal ρ)) +
        ∑ i, ∫ y, CoercAux.nearF d s ε (X i - y) ∂(withDensityReal ρ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hPint (X i)
  -- the exact Fourier identity for the smooth part
  have hsum : Summable fun k : Lattice d => |CoercAux.cT d s ε k| :=
    (CoercAux.summable_cT hd hs0 hsd hε).abs
  have hQ : (1 / (N : ℝ) ^ 2) * (∑ i, ∑ j, CoercAux.gT d s ε (X i - X j))
      - (2 / (N : ℝ)) * (∑ i, ∫ y, CoercAux.gT d s ε (X i - y) ∂(withDensityReal ρ))
      + ∫ x, ∫ y, CoercAux.gT d s ε (x - y) ∂(withDensityReal ρ) ∂(withDensityReal ρ)
      = CoercAux.Esq d s ε X (withDensityReal ρ) :=
    CoercAux.Q_eq_tsum hN hsum X (withDensityReal ρ)
  have hEsq := CoercAux.Esq_nonneg hd hs0 hsd hε X (withDensityReal ρ)
  have hR : rieszEnergy d s X (withDensityReal ρ) =
      (1 / (2 * (N : ℝ) ^ 2)) * (∑ i, ∑ j ∈ Finset.univ.erase i, periodicRiesz d s (X i - X j))
        - (1 / (N : ℝ)) * (∑ i, ∫ y, periodicRiesz d s (X i - y) ∂(withDensityReal ρ))
        + (1 / 2) * ∫ x, ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ) ∂(withDensityReal ρ) := rfl
  rw [hR, hSP, hTP, hPD]
  -- algebra
  have e1 : (1 / (2 * (N : ℝ) ^ 2)) * (N * CoercAux.gT d s ε 0) = CoercAux.gT d s ε 0 / (2 * N) := by
    field_simp
  have e2 : (2 / (N : ℝ)) * (∑ i, ∫ y, CoercAux.gT d s ε (X i - y) ∂(withDensityReal ρ)) =
      2 * ((1 / (N : ℝ)) * (∑ i, ∫ y, CoercAux.gT d s ε (X i - y) ∂(withDensityReal ρ))) := by ring
  have e3 : (1 / (2 * (N : ℝ) ^ 2)) * (∑ i, ∑ j, CoercAux.gT d s ε (X i - X j)) =
      (1 / 2) * ((1 / (N : ℝ) ^ 2) * (∑ i, ∑ j, CoercAux.gT d s ε (X i - X j))) := by ring
  have e4 : (1 / (N : ℝ)) * ∑ i, ∫ y, CoercAux.gT d s ε (X i - y) ∂(withDensityReal ρ) =
      (1 / (N : ℝ)) * ∑ i, ∫ y, CoercAux.gT d s ε (X i - y) ∂(withDensityReal ρ) := rfl
  have e5 : (1 / (2 * (N : ℝ) ^ 2)) * (∑ i, ∑ j ∈ Finset.univ.erase i, CoercAux.nearF d s ε (X i - X j)) =
      (1 / (2 * (N : ℝ) ^ 2)) * (∑ i, ∑ j ∈ Finset.univ.erase i, CoercAux.nearF d s ε (X i - X j)) := rfl
  nlinarith [hFs', hIF, hEsq, hQ, e1, e2, e3, hB0, hΛB]


/-- Lower bound of the near part of the kernel, `s > 0`. -/
theorem nearF_lower_pos (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) :
    ∃ δ c C : ℝ, 0 < δ ∧ 0 < c ∧ 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x : Torus d, x ≠ 0 →
      KernelGrad.tdist x 0 ≤ δ * Real.sqrt ε →
        c * KernelGrad.tdist x 0 ^ (-s) - C * ε ^ (bexp d s) ≤ CoercAux.nearF d s ε x := by
  unfold bexp
  have hs0 : (0:ℝ) ≤ s := hs.le
  have hA := CoercAux.subA_pos_one hd hs0 hsd
  have ha : 0 < ((d:ℝ) - s) / 2 := by linarith
  set q : ℝ := (4:ℝ) ^ (-s / 2) with hq_def
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  set K0 : ℝ := KernelAux.subA d s * Real.sqrt Real.pi ^ d * Real.exp (-1) * (2 / s) * (1 - q)
    with hK0
  have hK0pos : 0 < K0 := by
    rw [hK0]
    have h1 := Real.exp_pos (-1)
    have h2 : 0 < Real.sqrt Real.pi ^ d := by have := Real.sqrt_pos.mpr Real.pi_pos; positivity
    have h3 : 0 < 1 - q := by linarith
    have h4 : 0 < 2 / s := by positivity
    have h5 : 0 < KernelAux.subA d s := hA
    exact mul_pos (mul_pos (mul_pos (mul_pos h5 h2) h1) h4) h3
  refine ⟨1 / (2 * Real.pi), K0 * Real.pi ^ (-s), KernelAux.subA d s / (((d:ℝ) - s) / 2),
    by positivity, mul_pos hK0pos (Real.rpow_pos_of_pos Real.pi_pos _),
    div_nonneg hA.le ha.le, ?_⟩
  intro ε hε hε1 x hx hr
  obtain ⟨y, hy, rfl⟩ := NearFieldAux.exists_box x
  set r := KernelGrad.tdist (KernelAux.boxPt y) 0 with hr_def
  have hrpos : 0 < r := KernelGrad.tdist_pos hx
  have hsum : ∑ i, y i ^ 2 = r ^ 2 := NearFieldAux.sum_sq_eq_tdist hy
  have hc : Real.pi ^ 2 * ∑ i, y i ^ 2 = Real.pi ^ 2 * r ^ 2 := by rw [hsum]
  have hc4 : 4 * (Real.pi ^ 2 * r ^ 2) ≤ ε := by
    have h1 : r ^ 2 ≤ (1 / (2 * Real.pi) * Real.sqrt ε) ^ 2 := pow_le_pow_left₀ hrpos.le hr 2
    have h2 : (1 / (2 * Real.pi) * Real.sqrt ε) ^ 2 = ε / (4 * Real.pi ^ 2) := by
      rw [mul_pow, Real.sq_sqrt hε.le]; field_simp; ring
    rw [h2] at h1
    have hpi : 0 < Real.pi ^ 2 := by positivity
    calc 4 * (Real.pi ^ 2 * r ^ 2) ≤ 4 * (Real.pi ^ 2 * (ε / (4 * Real.pi ^ 2))) := by gcongr
      _ = ε := by field_simp
  have hcpos : 0 < Real.pi ^ 2 * r ^ 2 := by positivity
  have hcore := NearFieldAux.nearF_ge_core hd hs0 hsd hε hx
  have hpos := NearFieldAux.pos_integral_lower (d := d) hs hcpos hc4
  rw [hc] at hcore
  rw [NearFieldAux.rpow_pi_sq s hrpos.le] at hpos
  have hεq : ε ^ (-s / 2) ≤ q * (Real.pi ^ 2 * r ^ 2) ^ (-s / 2) := by
    have h1 := Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ) < 4 * (Real.pi ^ 2 * r ^ 2))
      hc4 (by linarith : -s / 2 ≤ 0)
    rw [Real.mul_rpow (by norm_num) hcpos.le] at h1
    rw [hq_def]; exact h1
  rw [NearFieldAux.rpow_pi_sq s hrpos.le] at hεq
  have hM : 0 ≤ KernelAux.subA d s * Real.sqrt Real.pi ^ d * Real.exp (-1) * (2 / s) := by
    have h2 : 0 < 2 / s := by positivity
    have := Real.exp_pos (-1)
    have : 0 ≤ Real.sqrt Real.pi ^ d := by positivity
    have := hA.le
    positivity
  have h5 := mul_le_mul_of_nonneg_left hpos hA.le
  have h6 : K0 * (Real.pi ^ (-s) * r ^ (-s)) ≤
      KernelAux.subA d s * (Real.sqrt Real.pi ^ d * (Real.exp (-1) * ((2 / s) *
        (Real.pi ^ (-s) * r ^ (-s) - ε ^ (-s / 2))))) := by
    have key := mul_nonneg hM (sub_nonneg.mpr hεq)
    rw [hK0]
    nlinarith [key]
  have hB : KernelAux.subA d s / (((d:ℝ) - s) / 2) * ε ^ (((d:ℝ) - s) / 2) =
      CoercAux.nearB d s ε := by
    unfold CoercAux.nearB; ring
  rw [hB]
  linarith [h5, h6, hcore]


/-- Lower bound of the near part of the kernel, `s = 0`: `nearF_ε(x) ≥ log(√ε/|x|) - C`
(the coefficient `1` is exact: `subA d 0 · π^{d/2} = 1/2`, `CoercAux.subA_zero_mul`). -/
theorem nearF_lower_zero (hd : 1 ≤ d) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x : Torus d, x ≠ 0 →
      KernelGrad.tdist x 0 ≤ δ * Real.sqrt ε →
        Real.log (Real.sqrt ε / KernelGrad.tdist x 0) - C ≤ CoercAux.nearF d 0 ε x := by
  have hsd : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd' : (0:ℝ) < d := hsd
  have hA := CoercAux.subA_nonneg_one hd (le_refl (0:ℝ)) hsd
  have hP := CoercAux.subA_zero_mul hd
  have hlogpi : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  refine ⟨1 / (2 * Real.pi), Real.log Real.pi + 1 / 2 + 2 * KernelAux.subA d 0 / d, by positivity,
    by have h2 : 0 ≤ 2 * KernelAux.subA d 0 / d := div_nonneg (by linarith) hd'.le
       linarith, ?_⟩
  intro ε hε hε1 x hx hr
  obtain ⟨y, hy, rfl⟩ := NearFieldAux.exists_box x
  set r := KernelGrad.tdist (KernelAux.boxPt y) 0 with hr_def
  have hrpos : 0 < r := KernelGrad.tdist_pos hx
  have hsum : ∑ i, y i ^ 2 = r ^ 2 := NearFieldAux.sum_sq_eq_tdist hy
  have hc : Real.pi ^ 2 * ∑ i, y i ^ 2 = Real.pi ^ 2 * r ^ 2 := by rw [hsum]
  have hc4 : 4 * (Real.pi ^ 2 * r ^ 2) ≤ ε := by
    have h1 : r ^ 2 ≤ (1 / (2 * Real.pi) * Real.sqrt ε) ^ 2 := pow_le_pow_left₀ hrpos.le hr 2
    have h2 : (1 / (2 * Real.pi) * Real.sqrt ε) ^ 2 = ε / (4 * Real.pi ^ 2) := by
      rw [mul_pow, Real.sq_sqrt hε.le]; field_simp; ring
    rw [h2] at h1
    have hpi : 0 < Real.pi ^ 2 := by positivity
    calc 4 * (Real.pi ^ 2 * r ^ 2) ≤ 4 * (Real.pi ^ 2 * (ε / (4 * Real.pi ^ 2))) := by gcongr
      _ = ε := by field_simp
  have hcpos : 0 < Real.pi ^ 2 * r ^ 2 := by positivity
  have hcε : Real.pi ^ 2 * r ^ 2 ≤ ε := by linarith
  have hcore := NearFieldAux.nearF_ge_core (s := 0) hd (le_refl (0:ℝ)) hsd hε hx
  rw [hc] at hcore
  have hz := NearFieldAux.zero_integral_lower (d := d) hcpos hcε
  have hAmul := mul_le_mul_of_nonneg_left hz hA
  have hkey : KernelAux.subA d 0 * (Real.sqrt Real.pi ^ d * (Real.log (ε / (Real.pi ^ 2 * r ^ 2)) - 1)) =
      1 / 2 * (Real.log (ε / (Real.pi ^ 2 * r ^ 2)) - 1) := by
    rw [← mul_assoc, hP]
  have hlog : Real.log (ε / (Real.pi ^ 2 * r ^ 2)) = 2 * Real.log (Real.sqrt ε / r) - 2 * Real.log Real.pi := by
    rw [Real.log_div hε.ne' hcpos.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_div (Real.sqrt_pos.mpr hε).ne' hrpos.ne', Real.log_sqrt hε.le]
    push_cast; ring
  have hB : CoercAux.nearB d 0 ε ≤ 2 * KernelAux.subA d 0 / d := by
    have ha0 : 0 < ((d:ℝ) - 0) / 2 := by linarith
    have hea : ε ^ (((d:ℝ) - 0) / 2) ≤ 1 := Real.rpow_le_one hε.le hε1 ha0.le
    have h1 : ε ^ (((d:ℝ) - 0) / 2) / (((d:ℝ) - 0) / 2) ≤ 2 / d := by
      rw [div_le_iff₀ ha0]
      have : 2 / (d:ℝ) * (((d:ℝ) - 0) / 2) = 1 := by field_simp; ring
      nlinarith [this, hea]
    unfold CoercAux.nearB
    have := mul_le_mul_of_nonneg_left h1 hA
    have e : KernelAux.subA d 0 * (2 / (d:ℝ)) = 2 * KernelAux.subA d 0 / d := by ring
    linarith [this, e]
  linarith [hcore, hAmul, hkey, hlog, hB]


/-! ### Assembly helpers for `nearField_control` -/

theorem smearScale_neg_s {N : ℕ} {Λ : ℝ} (hN : 1 ≤ N) (hΛ : 0 < Λ) (s : ℝ) :
    smearScale d N Λ ^ (-s) = ((N : ℝ) * Λ) ^ (s / d) := by
  unfold smearScale
  rw [← Real.rpow_mul (mul_nonneg (Nat.cast_nonneg N) hΛ.le)]
  congr 1
  ring

theorem smearScale_pow_ds (hd : 1 ≤ d) {N : ℕ} {Λ : ℝ} (hΛ : 0 < Λ) (s : ℝ) :
    smearScale d N Λ ^ ((d : ℝ) - s) = ((N : ℝ) * Λ) ^ (s / d - 1) := by
  unfold smearScale
  rw [← Real.rpow_mul (mul_nonneg (Nat.cast_nonneg N) hΛ.le)]
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    exact ne_of_gt this
  congr 1
  field_simp
  ring

theorem aNΛ_eq_div (hd : 1 ≤ d) {N : ℕ} {Λ : ℝ} (hN : 1 ≤ N) (hΛ : 0 < Λ) (s : ℝ) :
    ((N : ℝ) * Λ) ^ (s / d) / N = aNΛ d s Λ N := by
  unfold aNΛ
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    exact ne_of_gt (by linarith)
  rw [Real.mul_rpow (Nat.cast_nonneg N) hΛ.le, Real.rpow_sub_one hN0]
  field_simp

theorem smear_rpow_le (hd : 1 ≤ d) {N : ℕ} {Λ : ℝ} (hN : 1 ≤ N) (hΛ : 1 ≤ Λ) (s : ℝ) :
    smearScale d N Λ ^ ((d : ℝ) - s) ≤ aNΛ d s Λ N := by
  rw [smearScale_pow_ds hd (by linarith) s]
  unfold aNΛ
  rw [Real.mul_rpow (Nat.cast_nonneg N) (by linarith)]
  have h1 : Λ ^ (s / d - 1) ≤ Λ ^ (s / d) := Real.rpow_le_rpow_of_exponent_le hΛ (by linarith)
  have h2 : 0 ≤ (N : ℝ) ^ (s / d - 1) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  nlinarith [mul_le_mul_of_nonneg_left h1 h2]

theorem aNΛ_zero (Λ : ℝ) (N : ℕ) : aNΛ d 0 Λ N = 1 / N := by
  unfold aNΛ
  simp [Real.rpow_neg_one]

theorem sq_rpow_half {lm : ℝ} (hlm : 0 ≤ lm) (s : ℝ) :
    (lm ^ 2) ^ (((d : ℝ) - s) / 2) = lm ^ ((d : ℝ) - s) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hlm]
  congr 1
  push_cast
  ring

theorem sum_pair_lower {N : ℕ} (φ : Fin N → Fin N → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ i j, -B ≤ φ i j) (jj : Fin N → Fin N) (hjj : ∀ i, jj i ≠ i) (i : Fin N) :
    φ i (jj i) ≤ ∑ j ∈ Finset.univ.erase i, φ i j + N * B := by
  have hmem : jj i ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hjj i, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase _ _ hmem]
  have hcard : ((Finset.univ.erase i).erase (jj i)).card ≤ N := by
    have := Finset.card_le_univ ((Finset.univ.erase i).erase (jj i))
    simpa using this
  have hlow : ∑ _j ∈ (Finset.univ.erase i).erase (jj i), (-B) ≤
      ∑ j ∈ (Finset.univ.erase i).erase (jj i), φ i j :=
    Finset.sum_le_sum fun j _ => hB i j
  simp only [Finset.sum_const, nsmul_eq_mul] at hlow
  have hc' : (((Finset.univ.erase i).erase (jj i)).card : ℝ) ≤ N := by exact_mod_cast hcard
  have : (((Finset.univ.erase i).erase (jj i)).card : ℝ) * (-B) ≥ -(N * B) := by nlinarith
  linarith

theorem esq_form_nonneg (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε)
    {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {N : ℕ} (hN : 0 < N) (X : Config d N) :
    0 ≤ (1 / (N : ℝ) ^ 2) * (∑ i, ∑ j, CoercAux.gT d s ε (X i - X j))
      - (2 / (N : ℝ)) * (∑ i, ∫ y, CoercAux.gT d s ε (X i - y) ∂(withDensityReal ρ))
      + ∫ x, ∫ y, CoercAux.gT d s ε (x - y) ∂(withDensityReal ρ) ∂(withDensityReal ρ) := by
  have := isProb_withDensityReal hρ
  have hsum : Summable fun k : Lattice d => |CoercAux.cT d s ε k| :=
    (CoercAux.summable_cT hd hs0 hsd hε).abs
  have hQ : (1 / (N : ℝ) ^ 2) * (∑ i, ∑ j, CoercAux.gT d s ε (X i - X j))
      - (2 / (N : ℝ)) * (∑ i, ∫ y, CoercAux.gT d s ε (X i - y) ∂(withDensityReal ρ))
      + ∫ x, ∫ y, CoercAux.gT d s ε (x - y) ∂(withDensityReal ρ) ∂(withDensityReal ρ)
      = CoercAux.Esq d s ε X (withDensityReal ρ) :=
    CoercAux.Q_eq_tsum hN hsum X (withDensityReal ρ)
  rw [hQ]
  exact CoercAux.Esq_nonneg hd hs0 hsd hε X (withDensityReal ρ)

theorem riesz_lower_aux (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε)
    {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ x, ρ x ≤ Λ)
    {N : ℕ} (hN : 0 < N) (X : Config d N) (hX : X ∉ collisionSet d N) :
    -(CoercAux.gT d s ε 0 / (2 * N) + (1 + Λ) * CoercAux.nearB d s ε) ≤
      rieszEnergy d s X (withDensityReal ρ) := by
  have h1 := CoercAux.rieszEnergy_ge_aux hd hs0 hsd hε hρ hΛ0 hΛ hN X hX
  have h2 := esq_form_nonneg hd hs0 hsd hε hρ hN X
  linarith

theorem sum_bound_gen {N : ℕ} (hN : 1 ≤ N) (SE : Fin N → ℝ) (φ : Fin N → Fin N → ℝ)
    (jj : Fin N → Fin N) (hjj : ∀ i, jj i ≠ i) {B κ Fb M : ℝ} (hB0 : 0 ≤ B) (hκ : 0 ≤ κ)
    (hB : ∀ i j, -B ≤ φ i j) (hpt : ∀ i, SE i ≤ κ * (φ i (jj i) + B) + M)
    (hFb : (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, φ i j ≤ Fb) :
    (1 / (N : ℝ) ^ 2) * ∑ i, SE i ≤ 2 * κ * Fb + 2 * κ * B + (1 / (N : ℝ)) * M := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNne : (N : ℝ) ≠ 0 := hN0.ne'
  have h1 : ∑ i, SE i ≤ ∑ i, (κ * (φ i (jj i) + B) + M) := Finset.sum_le_sum fun i _ => hpt i
  have h2 : ∑ i, φ i (jj i) ≤ ∑ i, (∑ j ∈ Finset.univ.erase i, φ i j + N * B) :=
    Finset.sum_le_sum fun i _ => sum_pair_lower φ hB0 hB jj hjj i
  have h3 : ∑ i, (κ * (φ i (jj i) + B) + M) = κ * ∑ i, φ i (jj i) + N * (κ * B) + N * M := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have h4 : ∑ i, (∑ j ∈ Finset.univ.erase i, φ i j + N * B) =
      (∑ i, ∑ j ∈ Finset.univ.erase i, φ i j) + N * (N * B) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [h4] at h2
  have h5 : κ * ∑ i, φ i (jj i) ≤ κ * ((∑ i, ∑ j ∈ Finset.univ.erase i, φ i j) + N * (N * B)) :=
    mul_le_mul_of_nonneg_left h2 hκ
  have hA : (1 / (N : ℝ) ^ 2) * ∑ i, SE i ≤
      (1 / (N : ℝ) ^ 2) * (κ * ∑ i, φ i (jj i) + N * (κ * B) + N * M) := by
    rw [← h3]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have e1 : (1 / (N : ℝ) ^ 2) * (κ * ((∑ i, ∑ j ∈ Finset.univ.erase i, φ i j) + N * (N * B))) =
      κ * ((1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, φ i j) + κ * B := by
    field_simp
  have e2 : (1 / (N : ℝ) ^ 2) * (N * (κ * B)) ≤ κ * B := by
    have h : (1 / (N : ℝ) ^ 2) * (N * (κ * B)) = (1 / (N : ℝ)) * (κ * B) := by
      field_simp
    rw [h]
    have hk : 0 ≤ κ * B := mul_nonneg hκ hB0
    have h1N : (1 / (N : ℝ)) ≤ 1 := by
      rw [div_le_one hN0]; exact hN1
    exact mul_le_of_le_one_left hk h1N
  have e3 : (1 / (N : ℝ) ^ 2) * (N * M) = (1 / (N : ℝ)) * M := by
    field_simp
  have e4 : (1 / (N : ℝ) ^ 2) * (κ * ∑ i, φ i (jj i)) ≤
      (1 / (N : ℝ) ^ 2) * (κ * ((∑ i, ∑ j ∈ Finset.univ.erase i, φ i j) + N * (N * B))) :=
    mul_le_mul_of_nonneg_left h5 (by positivity)
  have e5 : (1 / (N : ℝ) ^ 2) * (κ * ∑ i, φ i (jj i) + N * (κ * B) + N * M) =
      (1 / (N : ℝ) ^ 2) * (κ * ∑ i, φ i (jj i)) + (1 / (N : ℝ) ^ 2) * (N * (κ * B)) +
        (1 / (N : ℝ) ^ 2) * (N * M) := by ring
  have hF2 : κ * ((1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, φ i j) ≤ 2 * κ * Fb := by
    have h6 := mul_le_mul_of_nonneg_left hFb hκ
    have h7 : κ * ((1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, φ i j) =
        2 * (κ * ((1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, φ i j)) := by
      field_simp
    rw [h7]
    linarith
  linarith [hA, e1, e2, e3, e4, e5, hF2]

theorem assembly (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {C₀₁ : ℝ}
    (hdiag : ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N →
      CoercAux.gT d s (smearScale d N Λ ^ 2) 0 / (2 * N) +
        (1 + Λ) * CoercAux.nearB d s (smearScale d N Λ ^ 2) ≤ oNΛ d s C₀₁ Λ N)
    {κ Bc Kc : ℝ} (hκ : 0 ≤ κ) (hBc : 0 ≤ Bc) (hKc : 0 ≤ Kc)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {N : ℕ} (hN : 2 ≤ N)
    {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hρΛ : ∀ x, ρ x ≤ Λ)
    (X : Config d N) (hX : X ∉ collisionSet d N)
    (SE : Fin N → ℝ) (M : ℝ) (hM : M ≤ Kc * N * aNΛ d s Λ N)
    (hBbd : CoercAux.nearB d s (smearScale d N Λ ^ 2) ≤ Bc * aNΛ d s Λ N)
    (jj : Fin N → Fin N) (hjj : ∀ i, jj i ≠ i)
    (hpt : ∀ i, SE i ≤ κ * (CoercAux.nearF d s (smearScale d N Λ ^ 2) (X i - X (jj i)) +
      CoercAux.nearB d s (smearScale d N Λ ^ 2)) + M) :
    (1 / (N : ℝ) ^ 2) * ∑ i, SE i ≤
      (2 * κ + 1) * (rieszEnergy d s X (withDensityReal ρ) +
        oNΛ d s (C₀₁ + (2 * κ * Bc + Kc) / (2 * κ + 1)) Λ N) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
  have hlmpos : 0 < smearScale d N Λ := CoercAux.smearScale_pos (by omega) (by linarith)
  have hε : 0 < smearScale d N Λ ^ 2 := pow_pos hlmpos 2
  have hsplit := energy_split_near hd hs0 hsd hε hρ hΛ0 hρΛ (by omega : 0 < N) X hX
  have hY := riesz_lower_aux hd hs0 hsd hε hρ hΛ0 hρΛ (by omega : 0 < N) X hX
  have hQ := hdiag Λ hΛ N hN
  have hB0 : 0 ≤ CoercAux.nearB d s (smearScale d N Λ ^ 2) :=
    CoercAux.nearB_nonneg hd hs0 hsd hε
  have hf : ∀ i j, -CoercAux.nearB d s (smearScale d N Λ ^ 2) ≤
      CoercAux.nearF d s (smearScale d N Λ ^ 2) (X i - X j) :=
    fun i j => CoercAux.nearF_ge hd hs0 hsd hε _
  have hsb := sum_bound_gen (by omega : 1 ≤ N) SE
    (fun i j => CoercAux.nearF d s (smearScale d N Λ ^ 2) (X i - X j)) jj hjj hB0 hκ hf hpt
    (Fb := rieszEnergy d s X (withDensityReal ρ) + CoercAux.gT d s (smearScale d N Λ ^ 2) 0 / (2 * N)
      + (1 + Λ) * CoercAux.nearB d s (smearScale d N Λ ^ 2)) hsplit
  set F := rieszEnergy d s X (withDensityReal ρ) with hF_def
  set Bn := CoercAux.nearB d s (smearScale d N Λ ^ 2) with hBn_def
  set Gq := CoercAux.gT d s (smearScale d N Λ ^ 2) 0 / (2 * N) with hGq_def
  set on1 := oNΛ d s C₀₁ Λ N with hon1_def
  set aN := aNΛ d s Λ N with haN_def
  have haN0 : 0 ≤ aN := aNΛ_nonneg d s Λ N hΛ0
  have hY0 : 0 ≤ F + on1 := by
    have : -(Gq + (1 + Λ) * Bn) ≤ F := hY
    have : Gq + (1 + Λ) * Bn ≤ on1 := hQ
    linarith
  have hκ2 : 0 ≤ 2 * κ := by linarith
  have hBterm : 2 * κ * Bn ≤ 2 * κ * (Bc * aN) := mul_le_mul_of_nonneg_left hBbd hκ2
  have hMterm : (1 / (N : ℝ)) * M ≤ Kc * aN := by
    have h1 : (1 / (N : ℝ)) * M ≤ (1 / (N : ℝ)) * (Kc * N * aN) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    have h2 : (1 / (N : ℝ)) * (Kc * N * aN) = Kc * aN := by field_simp
    linarith
  have hFb : 2 * κ * (F + Gq + (1 + Λ) * Bn) ≤ 2 * κ * (F + on1) := by
    apply mul_le_mul_of_nonneg_left _ hκ2
    linarith
  have hoN : oNΛ d s (C₀₁ + (2 * κ * Bc + Kc) / (2 * κ + 1)) Λ N =
      on1 + ((2 * κ * Bc + Kc) / (2 * κ + 1)) * aN := by
    rw [hon1_def, haN_def, oNΛ_eq, oNΛ_eq]; ring
  have hk : (2 * κ + 1) * ((2 * κ * Bc + Kc) / (2 * κ + 1)) = 2 * κ * Bc + Kc := by
    field_simp
  rw [hoN]
  have hmain : (1 / (N : ℝ) ^ 2) * ∑ i, SE i ≤ 2 * κ * (F + Gq + (1 + Λ) * Bn) + 2 * κ * Bn
      + (1 / (N : ℝ)) * M := by
    have := hsb
    linarith
  have hfinal : (2 * κ + 1) * (F + (on1 + ((2 * κ * Bc + Kc) / (2 * κ + 1)) * aN)) =
      (2 * κ + 1) * (F + on1) + (2 * κ * Bc + Kc) * aN := by
    linear_combination aN * hk
  linarith [hmain, hFb, hBterm, hMterm, hfinal, hY0]

theorem pw_real_pos {s lm nn f B P Cf c δ r : ℝ} (hs : 0 < s) (hlm : 0 < lm) (hnn : 0 < nn)
    (hc : 0 < c) (hδ : 0 < δ) (hB : 0 ≤ B) (hP : 0 ≤ P) (hCf : 0 ≤ Cf) (hf : -B ≤ f)
    (hlow : nn ≤ δ * lm → c * nn ^ (-s) - Cf * P ≤ f) (hr : r = min (nn / 4) (lm / 8)) :
    r ^ (-s) ≤ (4 ^ s / c) * (f + B) + ((4 ^ s / c) * Cf * P + (8 ^ s + 4 ^ s * δ ^ (-s)) * lm ^ (-s)) := by
  have hk : 0 ≤ (4 : ℝ) ^ s / c := by positivity
  have h4 : (nn / 4) ^ (-s) = 4 ^ s * nn ^ (-s) := by
    rw [Real.div_rpow hnn.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4), div_inv_eq_mul]
    ring
  have h8 : (lm / 8) ^ (-s) = 8 ^ s * lm ^ (-s) := by
    rw [Real.div_rpow hlm.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 8), div_inv_eq_mul]
    ring
  have hnn0 : 0 ≤ nn ^ (-s) := Real.rpow_nonneg hnn.le _
  have hlm0 : 0 ≤ lm ^ (-s) := Real.rpow_nonneg hlm.le _
  have h4p : (0:ℝ) ≤ 4 ^ s := by positivity
  have h8p : (0:ℝ) ≤ 8 ^ s := by positivity
  have hr_le : r ^ (-s) ≤ 4 ^ s * nn ^ (-s) + 8 ^ s * lm ^ (-s) := by
    rcases min_choice (nn / 4) (lm / 8) with h | h
    · rw [hr, h, h4]
      have := mul_nonneg h8p hlm0
      linarith
    · rw [hr, h, h8]
      have := mul_nonneg h4p hnn0
      linarith
  have hfB : 0 ≤ (4 ^ s / c) * (f + B) := mul_nonneg hk (by linarith)
  have hCP : 0 ≤ (4 ^ s / c) * Cf * P := mul_nonneg (mul_nonneg hk hCf) hP
  have hδlm0 : (0:ℝ) ≤ δ ^ (-s) := Real.rpow_nonneg hδ.le _
  have hC1 : 0 ≤ (8 ^ s + 4 ^ s * δ ^ (-s)) * lm ^ (-s) := by
    have : 0 ≤ 8 ^ s + 4 ^ s * δ ^ (-s) := by positivity
    exact mul_nonneg this hlm0
  by_cases hcase : nn ≤ δ * lm
  · have hl := hlow hcase
    have hnn' : c * nn ^ (-s) ≤ f + Cf * P := by linarith
    have hk2 : 4 ^ s * nn ^ (-s) ≤ (4 ^ s / c) * (f + Cf * P) := by
      have e : 4 ^ s * nn ^ (-s) = (4 ^ s / c) * (c * nn ^ (-s)) := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left hnn' hk
    have e2 : (4 ^ s / c) * (f + Cf * P) = (4 ^ s / c) * (f + B) + (4 ^ s / c) * Cf * P -
        (4 ^ s / c) * B := by ring
    have hB' : 0 ≤ (4 ^ s / c) * B := mul_nonneg hk hB
    have : 8 ^ s * lm ^ (-s) ≤ (8 ^ s + 4 ^ s * δ ^ (-s)) * lm ^ (-s) := by
      have e3 : (8 ^ s + 4 ^ s * δ ^ (-s)) * lm ^ (-s) = 8 ^ s * lm ^ (-s) + 4 ^ s * δ ^ (-s) * lm ^ (-s) := by
        ring
      have : 0 ≤ 4 ^ s * δ ^ (-s) * lm ^ (-s) := mul_nonneg (mul_nonneg h4p hδlm0) hlm0
      linarith
    linarith
  · push_neg at hcase
    have hδlm : 0 < δ * lm := mul_pos hδ hlm
    have h5 : nn ^ (-s) ≤ (δ * lm) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos hδlm hcase.le (by linarith)
    have h6 : (δ * lm) ^ (-s) = δ ^ (-s) * lm ^ (-s) := Real.mul_rpow hδ.le hlm.le
    have h7 : 4 ^ s * nn ^ (-s) ≤ 4 ^ s * (δ ^ (-s) * lm ^ (-s)) :=
      mul_le_mul_of_nonneg_left (h6 ▸ h5) h4p
    have e4 : 4 ^ s * δ ^ (-s) * lm ^ (-s) = 4 ^ s * (δ ^ (-s) * lm ^ (-s)) := by ring
    have : 8 ^ s * lm ^ (-s) + 4 ^ s * δ ^ (-s) * lm ^ (-s) = (8 ^ s + 4 ^ s * δ ^ (-s)) * lm ^ (-s) := by
      ring
    nlinarith

theorem pw_real_zero {lm nn f B C δ r : ℝ} (hlm : 0 < lm) (hnn : 0 < nn) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hf : -B ≤ f) (hlow : nn ≤ δ * lm → Real.log (lm / nn) - C ≤ f) (hr : r = min (nn / 4) (lm / 8)) :
    Real.log (lm / r) ≤ (f + B) + (|C| + |Real.log δ| + Real.log 8 + Real.log 4) := by
  have hl8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hC0 := abs_nonneg C
  have hδ0 := abs_nonneg (Real.log δ)
  have hfB : 0 ≤ f + B := by linarith
  rcases min_choice (nn / 4) (lm / 8) with h | h
  · rw [hr, h]
    have hlogr : Real.log (lm / (nn / 4)) = Real.log (lm / nn) + Real.log 4 := by
      rw [Real.log_div hlm.ne' (by positivity), Real.log_div hlm.ne' hnn.ne',
        Real.log_div hnn.ne' (by norm_num)]
      ring
    rw [hlogr]
    by_cases hcase : nn ≤ δ * lm
    · have hl := hlow hcase
      have := le_abs_self C
      linarith
    · push_neg at hcase
      have hratio : lm / nn ≤ 1 / δ := by
        rw [div_le_div_iff₀ hnn hδ]
        linarith
      have hlog : Real.log (lm / nn) ≤ -Real.log δ := by
        calc Real.log (lm / nn) ≤ Real.log (1 / δ) := Real.log_le_log (div_pos hlm hnn) hratio
          _ = -Real.log δ := by rw [one_div, Real.log_inv]
      have := neg_le_abs (Real.log δ)
      linarith
  · rw [hr, h]
    have h8 : lm / (lm / 8) = 8 := by field_simp
    rw [h8]
    linarith

theorem nearB_le_aN (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {N : ℕ} {Λ : ℝ} (hN : 1 ≤ N)
    (hΛ : 1 ≤ Λ) :
    CoercAux.nearB d s (smearScale d N Λ ^ 2) ≤
      (KernelAux.subA d s / (((d : ℝ) - s) / 2)) * aNΛ d s Λ N := by
  have hlm : 0 < smearScale d N Λ := CoercAux.smearScale_pos hN (by linarith)
  have ha : 0 < ((d : ℝ) - s) / 2 := by linarith
  have hA := CoercAux.subA_nonneg_one hd hs0 hsd
  have hPle := smear_rpow_le hd hN hΛ s
  unfold CoercAux.nearB
  rw [sq_rpow_half hlm.le s]
  have h1 : smearScale d N Λ ^ ((d : ℝ) - s) / (((d : ℝ) - s) / 2) ≤
      aNΛ d s Λ N / (((d : ℝ) - s) / 2) := div_le_div_of_nonneg_right hPle ha.le
  have h2 := mul_le_mul_of_nonneg_left h1 hA
  have e : KernelAux.subA d s / (((d : ℝ) - s) / 2) * aNΛ d s Λ N =
      KernelAux.subA d s * (aNΛ d s Λ N / (((d : ℝ) - s) / 2)) := by ring
  rw [e]
  exact h2

theorem pw_pos_discrete (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) {δ c Cf : ℝ} (hδ : 0 < δ)
    (hc : 0 < c) (hCf : 0 ≤ Cf)
    (hlow : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x : Torus d, x ≠ 0 →
      KernelGrad.tdist x 0 ≤ δ * Real.sqrt ε →
        c * KernelGrad.tdist x 0 ^ (-s) - Cf * ε ^ (bexp d s) ≤ CoercAux.nearF d s ε x)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {N : ℕ} (hN : 2 ≤ N) (X : Config d N) (hX : X ∉ collisionSet d N)
    (i : Fin N) :
    ∃ j : Fin N, j ≠ i ∧ selfExcess d s Λ N (smearRadius Λ X i) ≤
      (4 ^ s / c) * (CoercAux.nearF d s (smearScale d N Λ ^ 2) (X i - X j) +
        CoercAux.nearB d s (smearScale d N Λ ^ 2)) +
      ((4 ^ s / c) * Cf * smearScale d N Λ ^ ((d : ℝ) - s) +
        (8 ^ s + 4 ^ s * δ ^ (-s)) * smearScale d N Λ ^ (-s)) := by
  have hΛpos : 0 < Λ := by linarith
  have hlmpos : 0 < smearScale d N Λ := CoercAux.smearScale_pos (by omega) hΛpos
  have hlm1 : smearScale d N Λ < 1 := CoercAux.smearScale_lt_one hd (by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith)
  -- nearest neighbour
  haveI : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr hN
  obtain ⟨j0, hj0⟩ := exists_ne i
  haveI : Nonempty {j : Fin N // j ≠ i} := ⟨⟨j0, hj0⟩⟩
  obtain ⟨jm, hjm⟩ := exists_eq_ciInf_of_finite
    (f := fun j : {j : Fin N // j ≠ i} => KernelGrad.tdist (X i) (X j.1))
  have hjne : jm.1 ≠ i := jm.2
  have hnn_def : nnDist X i = KernelGrad.tdist (X i) (X jm.1) := by
    unfold nnDist; rw [hjm]
  have hXne : X i - X jm.1 ≠ 0 := fun h => hX ⟨i, jm.1, Ne.symm hjne, sub_eq_zero.mp h⟩
  have hnnpos : 0 < nnDist X i := by
    rw [hnn_def, NearFieldAux.tdist_sub_zero (X i) (X jm.1)]
    exact KernelGrad.tdist_pos hXne
  have e1 : KernelGrad.tdist (X i - X jm.1) 0 = nnDist X i := by
    rw [hnn_def, NearFieldAux.tdist_sub_zero (X i) (X jm.1)]
  have hr : smearRadius Λ X i = min (nnDist X i / 4) (smearScale d N Λ / 8) := by
    unfold smearRadius thetaStar
    congr 1
    ring
  have hsel : selfExcess d s Λ N (smearRadius Λ X i) = (smearRadius Λ X i) ^ (-s) := by
    unfold selfExcess
    rw [if_neg hs.ne']
  have hB0 : 0 ≤ CoercAux.nearB d s (smearScale d N Λ ^ 2) :=
    CoercAux.nearB_nonneg hd hs.le hsd (pow_pos hlmpos 2)
  have hf : -CoercAux.nearB d s (smearScale d N Λ ^ 2) ≤
      CoercAux.nearF d s (smearScale d N Λ ^ 2) (X i - X jm.1) :=
    CoercAux.nearF_ge hd hs.le hsd (pow_pos hlmpos 2) _
  have hlowcase : nnDist X i ≤ δ * smearScale d N Λ →
      c * (nnDist X i) ^ (-s) - Cf * smearScale d N Λ ^ ((d : ℝ) - s) ≤
        CoercAux.nearF d s (smearScale d N Λ ^ 2) (X i - X jm.1) := by
    intro hcase
    have hsq : δ * Real.sqrt (smearScale d N Λ ^ 2) = δ * smearScale d N Λ := by
      rw [Real.sqrt_sq hlmpos.le]
    have hle1 : smearScale d N Λ ^ 2 ≤ 1 := pow_le_one₀ hlmpos.le hlm1.le
    have h := hlow (smearScale d N Λ ^ 2) (pow_pos hlmpos 2) hle1 (X i - X jm.1) hXne
      (by rw [e1, hsq]; exact hcase)
    rw [e1] at h
    unfold bexp at h
    rw [sq_rpow_half hlmpos.le s] at h
    exact h
  have key := pw_real_pos hs hlmpos hnnpos hc hδ hB0
    (Real.rpow_nonneg hlmpos.le _) hCf hf hlowcase hr
  refine ⟨jm.1, hjne, ?_⟩
  rw [hsel]
  exact key

theorem pw_zero_discrete (hd : 1 ≤ d) (hsd0 : (0 : ℝ) < d) {δ C : ℝ} (hδ : 0 < δ)
    (hlow : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x : Torus d, x ≠ 0 →
      KernelGrad.tdist x 0 ≤ δ * Real.sqrt ε →
        Real.log (Real.sqrt ε / KernelGrad.tdist x 0) - C ≤ CoercAux.nearF d 0 ε x)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {N : ℕ} (hN : 2 ≤ N) (X : Config d N) (hX : X ∉ collisionSet d N)
    (i : Fin N) :
    ∃ j : Fin N, j ≠ i ∧ selfExcess d 0 Λ N (smearRadius Λ X i) ≤
      (CoercAux.nearF d 0 (smearScale d N Λ ^ 2) (X i - X j) +
        CoercAux.nearB d 0 (smearScale d N Λ ^ 2)) +
      (|C| + |Real.log δ| + Real.log 8 + Real.log 4) := by
  have hΛpos : 0 < Λ := by linarith
  have hlmpos : 0 < smearScale d N Λ := CoercAux.smearScale_pos (by omega) hΛpos
  have hlm1 : smearScale d N Λ < 1 := CoercAux.smearScale_lt_one hd (by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith)
  haveI : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr hN
  obtain ⟨j0, hj0⟩ := exists_ne i
  haveI : Nonempty {j : Fin N // j ≠ i} := ⟨⟨j0, hj0⟩⟩
  obtain ⟨jm, hjm⟩ := exists_eq_ciInf_of_finite
    (f := fun j : {j : Fin N // j ≠ i} => KernelGrad.tdist (X i) (X j.1))
  have hjne : jm.1 ≠ i := jm.2
  have hnn_def : nnDist X i = KernelGrad.tdist (X i) (X jm.1) := by
    unfold nnDist; rw [hjm]
  have hXne : X i - X jm.1 ≠ 0 := fun h => hX ⟨i, jm.1, Ne.symm hjne, sub_eq_zero.mp h⟩
  have hnnpos : 0 < nnDist X i := by
    rw [hnn_def, NearFieldAux.tdist_sub_zero (X i) (X jm.1)]
    exact KernelGrad.tdist_pos hXne
  have e1 : KernelGrad.tdist (X i - X jm.1) 0 = nnDist X i := by
    rw [hnn_def, NearFieldAux.tdist_sub_zero (X i) (X jm.1)]
  have hr : smearRadius Λ X i = min (nnDist X i / 4) (smearScale d N Λ / 8) := by
    unfold smearRadius thetaStar
    congr 1
    ring
  have hsel : selfExcess d 0 Λ N (smearRadius Λ X i) =
      Real.log (smearScale d N Λ / smearRadius Λ X i) := by
    unfold selfExcess
    rw [if_pos rfl]
  have hB0 : 0 ≤ CoercAux.nearB d 0 (smearScale d N Λ ^ 2) :=
    CoercAux.nearB_nonneg hd le_rfl hsd0 (pow_pos hlmpos 2)
  have hf : -CoercAux.nearB d 0 (smearScale d N Λ ^ 2) ≤
      CoercAux.nearF d 0 (smearScale d N Λ ^ 2) (X i - X jm.1) :=
    CoercAux.nearF_ge hd le_rfl hsd0 (pow_pos hlmpos 2) _
  have hlowcase : nnDist X i ≤ δ * smearScale d N Λ →
      Real.log (smearScale d N Λ / nnDist X i) - C ≤
        CoercAux.nearF d 0 (smearScale d N Λ ^ 2) (X i - X jm.1) := by
    intro hcase
    have hsq : Real.sqrt (smearScale d N Λ ^ 2) = smearScale d N Λ := Real.sqrt_sq hlmpos.le
    have hle1 : smearScale d N Λ ^ 2 ≤ 1 := pow_le_one₀ hlmpos.le hlm1.le
    have h := hlow (smearScale d N Λ ^ 2) (pow_pos hlmpos 2) hle1 (X i - X jm.1) hXne
      (by rw [e1, Real.sqrt_sq hlmpos.le]; exact hcase)
    rw [e1, hsq] at h
    exact h
  have key := pw_real_zero hlmpos hnnpos hδ hB0 hf hlowcase hr
  refine ⟨jm.1, hjne, ?_⟩
  rw [hsel]
  exact key

/-- **Near-field control** (`[HCRS] (2.50)`, `[RS] (2.29)`): the excess self energies of the
smearing radii are controlled by the modulated energy.  Quantifier order: `C₀, C` depend only on
`d, s`; for `s = 0` the log coefficient is exactly the one of `o_N` (`selfExcess` subtracts
`g(lm)`), which is why the statement is *not* `N⁻²∑ g(r_i) ≲ F_N + o_N`. -/
theorem nearField_control (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
        (1 / (N : ℝ) ^ 2) * ∑ i, selfExcess d s Λ N (smearRadius Λ X i) ≤
          C * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) := by
  rcases eq_or_lt_of_le hs0 with hs | hs
  · -- the case `s = 0`
    subst hs
    obtain ⟨δ, C, hδ, hC0, hlow⟩ := nearF_lower_zero hd
    obtain ⟨C₀₁, hC₀₁, hdiag⟩ := CoercAux.diag_const hd (le_refl (0:ℝ)) hsd
    have hsd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hA0 : 0 ≤ KernelAux.subA d 0 := CoercAux.subA_nonneg_one hd (le_refl (0:ℝ)) hsd
    have hlen : (0:ℝ) < ((d : ℝ) - 0) / 2 := by linarith
    have hl8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hK0 : 0 ≤ |C| + |Real.log δ| + Real.log 8 + Real.log 4 := by
      have := abs_nonneg C; have := abs_nonneg (Real.log δ); linarith
    refine ⟨C₀₁ + (2 * 1 * (KernelAux.subA d 0 / (((d : ℝ) - 0) / 2)) +
        (|C| + |Real.log δ| + Real.log 8 + Real.log 4)) / (2 * 1 + 1), 2 * 1 + 1, ?_, by norm_num, ?_⟩
    · have : 0 ≤ (2 * 1 * (KernelAux.subA d 0 / (((d : ℝ) - 0) / 2)) +
          (|C| + |Real.log δ| + Real.log 8 + Real.log 4)) / (2 * 1 + 1) :=
        div_nonneg (by have := div_nonneg hA0 hlen.le; linarith) (by norm_num)
      linarith
    intro Λ hΛ N hN ρ hρ hρΛ X hX
    choose jj hjj hpt using fun i => pw_zero_discrete hd hsd0 hδ hlow hΛ hN X hX i
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hM : (|C| + |Real.log δ| + Real.log 8 + Real.log 4) ≤
        (|C| + |Real.log δ| + Real.log 8 + Real.log 4) * N * aNΛ d 0 Λ N := by
      rw [aNΛ_zero]
      have : (|C| + |Real.log δ| + Real.log 8 + Real.log 4) * N * (1 / N) =
          |C| + |Real.log δ| + Real.log 8 + Real.log 4 := by field_simp
      linarith
    exact assembly (κ := 1) (Bc := KernelAux.subA d 0 / (((d : ℝ) - 0) / 2))
      (Kc := |C| + |Real.log δ| + Real.log 8 + Real.log 4) hd (le_refl (0:ℝ)) hsd hdiag
      (by norm_num) (div_nonneg hA0 hlen.le) hK0 hΛ hN hρ hρΛ X hX
      (fun i => selfExcess d 0 Λ N (smearRadius Λ X i)) _ hM
      (nearB_le_aN hd (le_refl (0:ℝ)) hsd (by omega) hΛ) jj hjj
      (fun i => by have := hpt i; linarith)
  · -- the case `s > 0`
    obtain ⟨δ, c, Cf, hδ, hc, hCf, hlow⟩ := nearF_lower_pos hd hs hsd
    obtain ⟨C₀₁, hC₀₁, hdiag⟩ := CoercAux.diag_const hd hs.le hsd
    have hA0 : 0 ≤ KernelAux.subA d s := CoercAux.subA_nonneg_one hd hs.le hsd
    have hlen : (0:ℝ) < ((d : ℝ) - s) / 2 := by linarith
    have hκ : 0 ≤ (4 : ℝ) ^ s / c := by positivity
    have hBc : 0 ≤ KernelAux.subA d s / (((d : ℝ) - s) / 2) := div_nonneg hA0 hlen.le
    have hδs : 0 ≤ δ ^ (-s) := Real.rpow_nonneg hδ.le _
    have hKc : 0 ≤ (4 : ℝ) ^ s / c * Cf + (8 ^ s + 4 ^ s * δ ^ (-s)) := by
      have : 0 ≤ (8:ℝ) ^ s + 4 ^ s * δ ^ (-s) := by positivity
      exact add_nonneg (mul_nonneg hκ hCf) this
    refine ⟨C₀₁ + (2 * ((4 : ℝ) ^ s / c) * (KernelAux.subA d s / (((d : ℝ) - s) / 2)) +
        ((4 : ℝ) ^ s / c * Cf + (8 ^ s + 4 ^ s * δ ^ (-s)))) / (2 * ((4 : ℝ) ^ s / c) + 1),
      2 * ((4 : ℝ) ^ s / c) + 1, ?_, by linarith, ?_⟩
    · have : 0 ≤ (2 * ((4 : ℝ) ^ s / c) * (KernelAux.subA d s / (((d : ℝ) - s) / 2)) +
          ((4 : ℝ) ^ s / c * Cf + (8 ^ s + 4 ^ s * δ ^ (-s)))) / (2 * ((4 : ℝ) ^ s / c) + 1) :=
        div_nonneg (by have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hκ) hBc; linarith)
          (by linarith)
      linarith
    intro Λ hΛ N hN ρ hρ hρΛ X hX
    choose jj hjj hpt using fun i => pw_pos_discrete hd hs hsd hδ hc hCf hlow hΛ hN X hX i
    have hN1 : 1 ≤ N := by omega
    have hΛpos : 0 < Λ := by linarith
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have haN0 : 0 ≤ aNΛ d s Λ N := aNΛ_nonneg d s Λ N hΛpos.le
    have hlam : smearScale d N Λ ^ (-s) = (N : ℝ) * aNΛ d s Λ N := by
      rw [smearScale_neg_s hN1 hΛpos s, ← aNΛ_eq_div hd hN1 hΛpos s]
      field_simp
    have hP := smear_rpow_le hd hN1 hΛ s
    have hM : (4 ^ s / c) * Cf * smearScale d N Λ ^ ((d : ℝ) - s) +
        (8 ^ s + 4 ^ s * δ ^ (-s)) * smearScale d N Λ ^ (-s) ≤
        ((4 : ℝ) ^ s / c * Cf + (8 ^ s + 4 ^ s * δ ^ (-s))) * N * aNΛ d s Λ N := by
      rw [hlam]
      have h1 : (4 ^ s / c) * Cf * smearScale d N Λ ^ ((d : ℝ) - s) ≤
          (4 ^ s / c) * Cf * aNΛ d s Λ N :=
        mul_le_mul_of_nonneg_left hP (mul_nonneg hκ hCf)
      have h3 : 0 ≤ (4 ^ s / c) * Cf * ((N : ℝ) - 1) * aNΛ d s Λ N :=
        mul_nonneg (mul_nonneg (mul_nonneg hκ hCf) (by linarith)) haN0
      nlinarith
    exact assembly hd hs0 hsd hdiag hκ hBc hKc hΛ hN hρ hρΛ X hX
      (fun i => selfExcess d s Λ N (smearRadius Λ X i)) _ hM
      (nearB_le_aN hd hs0 hsd hN1 hΛ) jj hjj hpt

end HRS.Commutator
