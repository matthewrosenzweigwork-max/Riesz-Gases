import HRS.PDE.MeanFieldDecayGap

/-!
# Decay of the finite-regularity mean-field solution, packet P7a2 (package MF-01)
(plan `MeanFieldDecayPlan.md`, §1 P7a2)

Two-sided bounds of the free-energy gap by the `L²` distance to the thermal density, the Poincaré
inequality on the torus, the dissipation identity `D(ρ) = ∫ ρ |∇(ν log ρ + W)|²`, the lower bound
of the dissipation by the `L²` distance, and the entropy-production inequality
`D(ρ) ≥ κ (F(ρ) - F(ρ_β))`.

Statement check (`pp.parens`): none of the packet statements has the `∫`-precedence trap.  In
`poincare` and `dissipation_eq` every integral is either the last summand of a product
(`c * ∫ …`), the whole side of an `≤`/`=`, or inside parentheses; the only place where `∫` is
followed by a `+` is the statement `freeEnergy'_sub_thermal` of P7a1, which this file uses through
the corrected `MFDecay.freeEnergy'_sub_thermal'`.

This file does not import the scaffold `mf_apriori_bound_real_on` (nor `HRS.PDE.MeanField`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate

namespace HRS.PDE.MFDecay

open MFApriori

variable {d : ℕ}

/-! ### Section 1: the entropy part and the interaction part of the gap -/

theorem integrable_of_continuous' {f : Torus d → ℝ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Pointwise bounds integrated: for continuous positive `a, b` of equal mass,
`(1/2M) ∫ (a-b)² ≤ ∫ a (log a - log b) ≤ (1/lam) ∫ (a-b)²`. -/
theorem entropy_term_bounds (a b : Torus d → ℝ) (ha : Continuous a) (hb : Continuous b)
    (hapos : ∀ x, 0 < a x) (hbpos : ∀ x, 0 < b x) (M lam : ℝ) (haM : ∀ x, a x ≤ M)
    (hbM : ∀ x, b x ≤ M) (hlam : 0 < lam) (hbl : ∀ x, lam ≤ b x)
    (hmass : ∫ x, a x = ∫ x, b x) :
    (1 / (2 * M)) * (∫ x, (a x - b x) ^ 2) ≤ ∫ x, a x * (Real.log (a x) - Real.log (b x)) ∧
      (∫ x, a x * (Real.log (a x) - Real.log (b x))) ≤ (1 / lam) * (∫ x, (a x - b x) ^ 2) := by
  have hlogA : Continuous fun x => Real.log (a x) := ha.log fun x => (hapos x).ne'
  have hlogB : Continuous fun x => Real.log (b x) := hb.log fun x => (hbpos x).ne'
  have cE : Continuous fun x => a x * (Real.log (a x) - Real.log (b x)) :=
    ha.mul (hlogA.sub hlogB)
  have cZ : Continuous fun x => (a x - b x) ^ 2 := (ha.sub hb).pow 2
  have cL : Continuous fun x => a x - b x := ha.sub hb
  have hz : ∫ x, (a x - b x) = 0 := by
    rw [integral_sub (integrable_of_continuous' ha) (integrable_of_continuous' hb), hmass]; ring
  have hE : ∫ x, a x * (Real.log (a x) - Real.log (b x)) =
      ∫ x, (a x * (Real.log (a x) - Real.log (b x)) - (a x - b x)) := by
    rw [integral_sub (integrable_of_continuous' cE) (integrable_of_continuous' cL), hz]; ring
  have cP : Continuous fun x => a x * (Real.log (a x) - Real.log (b x)) - (a x - b x) :=
    cE.sub cL
  rw [hE]
  have hM : 0 < M := lt_of_lt_of_le (hapos (Classical.arbitrary _)) (haM _)
  constructor
  · have : ∫ x, (a x - b x) ^ 2 / (2 * M) ≤
        ∫ x, (a x * (Real.log (a x) - Real.log (b x)) - (a x - b x)) :=
      integral_mono (integrable_of_continuous' (cZ.div_const _)) (integrable_of_continuous' cP)
        fun x => mulLog_sub_ge (hapos x) (hbpos x) (haM x) (hbM x)
    rw [integral_div] at this
    calc (1 / (2 * M)) * (∫ x, (a x - b x) ^ 2) = (∫ x, (a x - b x) ^ 2) / (2 * M) := by
          rw [one_div, inv_mul_eq_div]
      _ ≤ _ := this
  · have : ∫ x, (a x * (Real.log (a x) - Real.log (b x)) - (a x - b x)) ≤
        ∫ x, (a x - b x) ^ 2 / lam :=
      integral_mono (integrable_of_continuous' cP) (integrable_of_continuous' (cZ.div_const _))
        fun x => (mulLog_sub_le (hapos x) (hbpos x)).trans
          (div_le_div_of_nonneg_left (sq_nonneg _) hlam (hbl x))
    rw [integral_div] at this
    calc _ ≤ _ := this
      _ = (1 / lam) * (∫ x, (a x - b x) ^ 2) := by rw [one_div, inv_mul_eq_div]

/-- The interaction part of the gap is between `0` and `gmax ‖z‖²`. -/
theorem interaction_gap_bounds (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (z : Coeff d)
    (hz : MemHs 0 z) :
    0 ≤ ∑' k, rieszCoeff d s k * ‖z k‖ ^ 2 ∧
      ∑' k, rieszCoeff d s k * ‖z k‖ ^ 2 ≤
        (|rieszConst d s| * 2 ^ (((d : ℝ) - s) / 2)) * hsNormSq 0 z := by
  have hz' : Summable fun k : Lattice d => ‖z k‖ ^ 2 := by
    have := hz
    unfold MemHs at this
    simpa [Aux.sobWeight_zero_aux] using this
  have hs : Summable fun k : Lattice d => rieszCoeff d s k * ‖z k‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (rieszCoeff_nonneg hd hs0 hsd k)
      (sq_nonneg _)) (fun k => ?_)
      (hz'.mul_left (|rieszConst d s| * 2 ^ (((d : ℝ) - s) / 2)))
    exact mul_le_mul_of_nonneg_right (rieszCoeff_le_gmax s hsd k) (sq_nonneg _)
  refine ⟨tsum_nonneg fun k => mul_nonneg (rieszCoeff_nonneg hd hs0 hsd k) (sq_nonneg _), ?_⟩
  unfold hsNormSq
  simp_rw [Aux.sobWeight_zero_aux, one_mul]
  rw [← tsum_mul_left]
  exact hs.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_right (rieszCoeff_le_gmax s hsd k)
    (sq_nonneg _)) (hz'.mul_left _)

theorem gap_bounds (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 2 < K) (V : Torus d → ℝ) (hV : Torus.IsCk 2 V) (β : ℝ) (hβ : 0 < β)
    (c : Coeff d) (hc : MemHs K c) (hreal : IsRealCoeff c) (h0 : c 0 = 1) (cL cU : ℝ)
    (hcL : 0 < cL) (hbd : ∀ x, cL ≤ toFun c x ∧ toFun c x ≤ cU) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρc : Continuous ρβ)
    (lam Lam : ℝ) (hlam : 0 < lam) (hρbd : ∀ x, lam ≤ ρβ x ∧ ρβ x ≤ Lam)
    (hmem : MemHs K (coeffOf ρβ)) :
    (β⁻¹ / (2 * max cU Lam)) * hsNormSq 0 (c - coeffOf ρβ) ≤
        freeEnergy' d s V β⁻¹ c - freeEnergy' d s V β⁻¹ (coeffOf ρβ) ∧
      freeEnergy' d s V β⁻¹ c - freeEnergy' d s V β⁻¹ (coeffOf ρβ) ≤
        (β⁻¹ / lam + |rieszConst d s| * 2 ^ (((d : ℝ) - s) / 2) / 2) *
          hsNormSq 0 (c - coeffOf ρβ) := by
  have hK0 : (d : ℝ) / 2 < K := by linarith
  have hs : Summable fun k => ‖c k‖ := summable_norm_of_memHs K hK0 c hc
  have hρ : Continuous (toFun c) := MFProduct.continuous_toFun c hs
  have hpos : ∀ x, 0 < toFun c x := fun x => lt_of_lt_of_le hcL (hbd x).1
  have hρp : ∀ x, 0 < ρβ x := fun x => lt_of_lt_of_le hlam (hρbd x).1
  have hgap := freeEnergy'_sub_thermal' hd s hs0 hsd K hK V hV β hβ c hc hreal hpos h0 ρβ hρβ hρc
    hρp hmem
  have hcoef : coeffOf (toFun c) = c := coeffOf_toFun c hreal hs
  obtain ⟨hmemz, hnorm⟩ := hsNormSq_zero_coeffOf_sub (toFun c) ρβ hρ hρc
  rw [hcoef] at hmemz hnorm
  have hmass : ∫ x, toFun c x = ∫ x, ρβ x := by
    rw [integral_toFun_eq_one K hK0 c hc hreal h0, hρβ.1.integral_one]
  obtain ⟨hE1, hE2⟩ := entropy_term_bounds (toFun c) ρβ hρ hρc hpos hρp (max cU Lam) lam
    (fun x => (hbd x).2.trans (le_max_left _ _)) (fun x => (hρbd x).2.trans (le_max_right _ _))
    hlam (fun x => (hρbd x).1) hmass
  obtain ⟨hI1, hI2⟩ := interaction_gap_bounds hd s hs0 hsd _ hmemz
  simp only [Pi.sub_apply] at hI1 hI2
  rw [← hnorm] at hE1 hE2
  rw [hgap]
  have hν : 0 < β⁻¹ := inv_pos.mpr hβ
  constructor
  · have := mul_le_mul_of_nonneg_left hE1 hν.le
    calc β⁻¹ / (2 * max cU Lam) * hsNormSq 0 (c - coeffOf ρβ)
        = β⁻¹ * (1 / (2 * max cU Lam) * hsNormSq 0 (c - coeffOf ρβ)) := by ring
      _ ≤ _ := by linarith
  · have := mul_le_mul_of_nonneg_left hE2 hν.le
    calc _ ≤ β⁻¹ * (1 / lam * hsNormSq 0 (c - coeffOf ρβ)) +
        (1 / 2 : ℝ) * ((|rieszConst d s| * 2 ^ (((d : ℝ) - s) / 2)) *
          hsNormSq 0 (c - coeffOf ρβ)) := by linarith
      _ = _ := by ring


/-! ### Section 2: Poincaré inequality on the torus -/

/-- Mode-wise Poincaré: `‖û(k)‖² (2π)² ≤ ∑_j ‖(∂_j u)^(k)‖²` for `k ≠ 0`. -/
theorem sq_le_sum_deriv (u : Torus d → ℝ) (hu : Torus.IsCk 1 u) (k : Lattice d) (hk : k ≠ 0) :
    (2 * Real.pi) ^ 2 * ‖coeffOf u k‖ ^ 2 ≤
      ∑ j, ‖coeffOf (Torus.partialDeriv j u) k‖ ^ 2 := by
  have e : ∀ j : Fin d, ‖coeffOf (Torus.partialDeriv j u) k‖ ^ 2 =
      (2 * Real.pi) ^ 2 * (((k j : ℤ) : ℝ) ^ 2 * ‖coeffOf u k‖ ^ 2) := by
    intro j
    rw [coeffOf_partialDeriv j u hu]
    have : ‖(2 * (Real.pi : ℂ) * Complex.I * ((k j : ℤ) : ℂ))‖ ^ 2 =
        (2 * Real.pi) ^ 2 * ((k j : ℤ) : ℝ) ^ 2 := by
      rw [norm_mul, norm_mul, mul_pow, mul_pow]
      simp [abs_of_pos Real.pi_pos]
    show ‖(2 * (Real.pi : ℂ) * Complex.I * ((k j : ℤ) : ℂ)) * coeffOf u k‖ ^ 2 = _
    rw [norm_mul, mul_pow, this]; ring
  simp_rw [e]
  rw [← Finset.mul_sum, ← Finset.sum_mul, ← enorm_sq]
  have h1 := one_le_enorm k hk
  have h2 : (1 : ℝ) ≤ Lattice.enorm k ^ 2 := by nlinarith
  have h3 : 0 ≤ (2 * Real.pi) ^ 2 * ‖coeffOf u k‖ ^ 2 := by positivity
  calc (2 * Real.pi) ^ 2 * ‖coeffOf u k‖ ^ 2 = 1 * ((2 * Real.pi) ^ 2 * ‖coeffOf u k‖ ^ 2) := by ring
    _ ≤ Lattice.enorm k ^ 2 * ((2 * Real.pi) ^ 2 * ‖coeffOf u k‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h2 h3
    _ = _ := by ring

theorem poincare (u : Torus d → ℝ) (hu : Torus.IsCk 1 u) :
    ∫ x, (u x - ∫ y, u y) ^ 2 ≤ (2 * Real.pi) ^ (-2 : ℤ) * ∫ x, ‖Torus.grad u x‖ ^ 2 := by
  have huc : Continuous u := continuous_of_isCk' hu le_rfl
  have hpc : ∀ j, Continuous (Torus.partialDeriv j u) := fun j => continuous_partialDeriv j _ hu
  set m : ℝ := ∫ y, u y with hm
  have hw : Continuous fun x => u x - m := huc.sub continuous_const
  have hW := hasSum_norm_sq_coeffOf _ hw
  have hD : ∀ j, HasSum (fun k : Lattice d => ‖coeffOf (Torus.partialDeriv j u) k‖ ^ 2)
      (∫ x, (Torus.partialDeriv j u x) ^ 2) := fun j => hasSum_norm_sq_coeffOf _ (hpc j)
  have hDsum := hasSum_sum (s := Finset.univ) (fun j _ => hD j)
  have hgrad : ∫ x, ‖Torus.grad u x‖ ^ 2 = ∑ j, ∫ x, (Torus.partialDeriv j u x) ^ 2 := by
    simp_rw [norm_grad_sq]
    exact integral_finsetSum _ (fun j _ => integrable_of_continuous' ((hpc j).pow 2))
  rw [hgrad]
  have hP : (2 * Real.pi) ^ (-2 : ℤ) = ((2 * Real.pi) ^ 2)⁻¹ := by
    rw [zpow_neg]; norm_cast
  have hPpos : 0 < (2 * Real.pi) ^ 2 := by positivity
  rw [hP, ← div_eq_inv_mul, le_div_iff₀ hPpos, mul_comm]
  have hscaled := hW.mul_left ((2 * Real.pi) ^ 2)
  refine hasSum_le (fun k => ?_) hscaled hDsum
  by_cases hk : k = 0
  · subst hk
    have : coeffOf (fun x => u x - m) 0 = 0 := by
      rw [coeffOf_sub u (fun _ => m) huc continuous_const 0, coeffOf_zero_eq_integral']
      simp [coeffOf_const, deltaCoeff, hm]
    rw [this]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  · have : coeffOf (fun x => u x - m) k = coeffOf u k := by
      rw [coeffOf_sub u (fun _ => m) huc continuous_const k, coeffOf_const]
      simp [deltaCoeff, hk]
    simp only [this]
    exact sq_le_sum_deriv u hu k hk


/-! ### Section 3: the dissipation as a weighted Dirichlet integral -/

theorem dissipation_eq (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 2 < K) (V : Torus d → ℝ) (hV : Torus.IsCk 2 V) (ν : ℝ)
    (c : Coeff d) (hc : MemHs K c) (hreal : IsRealCoeff c) (hpos : ∀ x, 0 < toFun c x) :
    Torus.IsCk 1 (fun x => ν * Real.log (toFun c x) + Wpot d s V c x) ∧
    dissipation d s V ν c = ∫ x, toFun c x *
      ‖Torus.grad (fun y => ν * Real.log (toFun c y) + Wpot d s V c y) x‖ ^ 2 := by
  obtain ⟨C₂, -, hC₂⟩ := exists_mfPath_isCk (d := d) 2 K (by simpa using hK)
  have hρ2 : Torus.IsCk 2 (toFun c) := (hC₂ c hc hreal).1
  have hρ1 : Torus.IsCk 1 (toFun c) := hρ2.of_le (by norm_num)
  have hW2 := isCk_two_Wpot hd s hs0 hsd K hK V hV c hc hreal
  have hW1 : Torus.IsCk 1 (Wpot d s V c) := hW2.of_le (by norm_num)
  set ρ := toFun c with hρdef
  set W := Wpot d s V c with hWdef
  have hΦ : ContDiffOn ℝ 1 (fun r : ℝ => ν * Real.log r) (Ioi 0) :=
    contDiffOn_const.mul (Real.contDiffOn_log.mono fun y hy => ne_of_gt hy)
  have hrange : ∀ x, ρ x ∈ Ioi (0 : ℝ) := fun x => hpos x
  have hlog1 : Torus.IsCk 1 (fun x => ν * Real.log (ρ x)) :=
    isCk_comp (fun r : ℝ => ν * Real.log r) (Ioi 0) hΦ ρ hρ1 hrange
  have hw1 : Torus.IsCk 1 (fun x => ν * Real.log (ρ x) + W x) := isCk_add _ _ hlog1 hW1
  refine ⟨hw1, ?_⟩
  have hder : ∀ j x, Torus.partialDeriv j (fun y => ν * Real.log (ρ y) + W y) x =
      ν * (ρ x)⁻¹ * Torus.partialDeriv j ρ x + Torus.partialDeriv j W x := by
    intro j x
    rw [MFApriori.partialDeriv_add j _ _ hlog1 hW1 x,
      partialDeriv_comp j (fun r : ℝ => ν * Real.log r) (Ioi 0) isOpen_Ioi hΦ ρ hρ1 hrange x]
    have : deriv (fun r : ℝ => ν * Real.log r) (ρ x) = ν * (ρ x)⁻¹ := by
      rw [deriv_const_mul _ (Real.differentiableAt_log (hpos x).ne'), Real.deriv_log]
    rw [this]
  unfold dissipation
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hne := (hpos x).ne'
  have hv : Torus.grad (fun y => ν * Real.log (ρ y) + W y) x =
      (ρ x)⁻¹ • (ν • Torus.grad ρ x + ρ x • Torus.grad W x) := by
    ext j
    simp only [MFAux.grad_apply, hder, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    field_simp
  show ‖ν • Torus.grad ρ x + ρ x • Torus.grad W x‖ ^ 2 / ρ x = ρ x * _
  rw [hv, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  field_simp


/-! ### Section 4: the dissipation controls the `L²` distance to the thermal density -/

/-- `∫ z (w - a) = ∫ z w` when `∫ z = 0`. -/
theorem integral_mul_sub_const (z w : Torus d → ℝ) (hz : Continuous z) (hw : Continuous w)
    (a : ℝ) (hz0 : ∫ x, z x = 0) : ∫ x, z x * (w x - a) = ∫ x, z x * w x := by
  have e : ∀ x, z x * (w x - a) = z x * w x - a * z x := fun x => by ring
  simp_rw [e]
  rw [integral_sub (integrable_of_continuous' (f := fun x => z x * w x) (hz.mul hw))
    (integrable_of_continuous' (f := fun x => a * z x) (continuous_const.mul hz)),
    integral_const_mul, hz0]
  ring

/-- Young's inequality, integrated: `ε² ∫ z² ≤ ∫ u²` if `ε ∫ z² ≤ ∫ z u`. -/
theorem sq_integral_le_of_young (z u : Torus d → ℝ) (hz : Continuous z) (hu : Continuous u)
    (ε : ℝ) (hε : 0 < ε) (h : ε * (∫ x, z x ^ 2) ≤ ∫ x, z x * u x) :
    ε ^ 2 * (∫ x, z x ^ 2) ≤ ∫ x, u x ^ 2 := by
  have hpt : ∀ x, z x * u x ≤ ε / 2 * z x ^ 2 + (1 / (2 * ε)) * u x ^ 2 := by
    intro x
    have h0 : 0 ≤ (ε * z x - u x) ^ 2 / (2 * ε) := by positivity
    have : ε / 2 * z x ^ 2 + (1 / (2 * ε)) * u x ^ 2 - z x * u x =
        (ε * z x - u x) ^ 2 / (2 * ε) := by field_simp; ring
    linarith
  have hint := integral_mono (integrable_of_continuous' (f := fun x => z x * u x) (hz.mul hu))
    (integrable_of_continuous' (f := fun x => ε / 2 * z x ^ 2 + (1 / (2 * ε)) * u x ^ 2)
      ((continuous_const.mul (hz.pow 2)).add (continuous_const.mul (hu.pow 2)))) hpt
  rw [integral_add (integrable_of_continuous' (f := fun x => ε / 2 * z x ^ 2)
      (continuous_const.mul (hz.pow 2)))
    (integrable_of_continuous' (f := fun x => (1 / (2 * ε)) * u x ^ 2)
      (continuous_const.mul (hu.pow 2))), integral_const_mul,
    integral_const_mul] at hint
  have h2 : ε * (∫ x, z x ^ 2) ≤ ε / 2 * (∫ x, z x ^ 2) + (1 / (2 * ε)) * ∫ x, u x ^ 2 :=
    h.trans hint
  generalize (∫ x, z x ^ 2) = Z at h2 ⊢
  generalize (∫ x, u x ^ 2) = U at h2 ⊢
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * ε)
  have e : 2 * ε * (ε / 2 * Z + (1 / (2 * ε)) * U) = ε ^ 2 * Z + U := by field_simp
  nlinarith [h3, e]

theorem dissipation_ge (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 2 < K) (V : Torus d → ℝ) (hV : Torus.IsCk 2 V) (β : ℝ) (hβ : 0 < β)
    (c : Coeff d) (hc : MemHs K c) (hreal : IsRealCoeff c) (h0 : c 0 = 1) (cL cU : ℝ)
    (hcL : 0 < cL) (hbd : ∀ x, cL ≤ toFun c x ∧ toFun c x ≤ cU) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρc : Continuous ρβ)
    (lam Lam : ℝ) (hlam : 0 < lam) (hρbd : ∀ x, lam ≤ ρβ x ∧ ρβ x ≤ Lam)
    (hmem : MemHs K (coeffOf ρβ)) :
    cL * (2 * Real.pi) ^ 2 * (β⁻¹ / max cU Lam) ^ 2 * hsNormSq 0 (c - coeffOf ρβ) ≤
      dissipation d s V β⁻¹ c := by
  have hK0 : (d : ℝ) / 2 < K := by linarith
  have hs : Summable fun k => ‖c k‖ := summable_norm_of_memHs K hK0 c hc
  have hsb : Summable fun k => ‖coeffOf ρβ k‖ := summable_norm_of_memHs K hK0 _ hmem
  have hρ : Continuous (toFun c) := MFProduct.continuous_toFun c hs
  have hpos : ∀ x, 0 < toFun c x := fun x => lt_of_lt_of_le hcL (hbd x).1
  have hρp : ∀ x, 0 < ρβ x := fun x => lt_of_lt_of_le hlam (hρbd x).1
  have hrealβ : IsRealCoeff (coeffOf ρβ) := isRealCoeff_coeffOf ρβ (integrable_of_continuous' hρc)
  have hρβeq : toFun (coeffOf ρβ) = ρβ := toFun_coeffOf ρβ hρc hsb
  have hcoef : coeffOf (toFun c) = c := coeffOf_toFun c hreal hs
  -- the difference `e = ĉ - ρ̂_β`
  set e : Coeff d := c - coeffOf ρβ with hedef
  have he : MemHs K e := HRS.PDE.memHs_sub hc hmem
  have hereal : IsRealCoeff e := fun k => by
    simp only [hedef, Pi.sub_apply, map_sub]
    rw [hreal k, hrealβ k]
  have hse : Summable fun k => ‖e k‖ := summable_norm_of_memHs K hK0 e he
  have htoe : ∀ x, toFun e x = toFun c x - ρβ x := fun x => by
    rw [hedef, Aux.toFun_sub c _ hs hsb, hρβeq]
  have hRc : Summable fun k => ‖rieszMult d s c k‖ :=
    summable_norm_of_memHs K hK0 _ (hs_rieszMult s hsd K c hc).1
  have hRb : Summable fun k => ‖rieszMult d s (coeffOf ρβ) k‖ :=
    summable_norm_of_memHs K hK0 _ (hs_rieszMult s hsd K _ hmem).1
  have hrieszE : ∀ x, riesz d s e x = riesz d s c x - riesz d s (coeffOf ρβ) x := fun x => by
    have : rieszMult d s e = rieszMult d s c - rieszMult d s (coeffOf ρβ) := by
      funext k; simp [rieszMult, hedef, mul_sub]
    unfold riesz
    rw [this, Aux.toFun_sub _ _ hRc hRb]
  have hzc : Continuous (toFun e) := by
    have : toFun e = fun x => toFun c x - ρβ x := funext htoe
    rw [this]; exact hρ.sub hρc
  have hRe : Continuous (riesz d s e) :=
    MFProduct.continuous_toFun _ (summable_norm_of_memHs K hK0 _ (hs_rieszMult s hsd K e he).1)
  -- the weighted Dirichlet form
  obtain ⟨hw1, hDeq⟩ := dissipation_eq hd s hs0 hsd K hK V hV β⁻¹ c hc hreal hpos
  set w : Torus d → ℝ := fun x => β⁻¹ * Real.log (toFun c x) + Wpot d s V c x with hwdef
  have hwc : Continuous w := continuous_of_isCk' hw1 le_rfl
  have hν : 0 < β⁻¹ := inv_pos.mpr hβ
  have hD1 : cL * ∫ x, ‖Torus.grad w x‖ ^ 2 ≤ dissipation d s V β⁻¹ c := by
    rw [hDeq, ← integral_const_mul]
    exact integral_mono (integrable_of_continuous' (continuous_const.mul
        (continuous_norm_grad_sq hw1)))
      (integrable_of_continuous' (hρ.mul (continuous_norm_grad_sq hw1)))
      fun x => mul_le_mul_of_nonneg_right (hbd x).1 (sq_nonneg _)
  have hPoin := poincare w hw1
  -- masses
  have hmass : ∫ x, toFun c x = ∫ x, ρβ x := by
    rw [integral_toFun_eq_one K hK0 c hc hreal h0, hρβ.1.integral_one]
  have hz0 : ∫ x, toFun e x = 0 := by
    simp_rw [htoe]
    rw [integral_sub (integrable_of_continuous' hρ) (integrable_of_continuous' hρc), hmass]; ring
  -- Euler-Lagrange equation
  obtain ⟨μ, hμ⟩ := thermal_log_add_Wpot_const hd s hs0 hsd K hK0 V β hβ ρβ hρβ hρc hρp hmem
  have hwμ : ∀ x, w x - μ = β⁻¹ * (Real.log (toFun c x) - Real.log (ρβ x)) + riesz d s e x := by
    intro x
    have h1 := hμ x
    unfold Wpot at h1
    simp only [hwdef, Wpot, hrieszE]
    linarith
  set M := max cU Lam with hMdef
  have hM : 0 < M := lt_of_lt_of_le (hpos (Classical.arbitrary _)) ((hbd _).2.trans (le_max_left _ _))
  -- the key inequality `(ν/M) ∫ z² ≤ ∫ z (w - w̄)`
  have hlogc : Continuous fun x => Real.log (toFun c x) := hρ.log fun x => (hpos x).ne'
  have hlogb : Continuous fun x => Real.log (ρβ x) := hρc.log fun x => (hρp x).ne'
  have hA : (∫ x, (toFun e x) ^ 2 / M) ≤
      ∫ x, toFun e x * (Real.log (toFun c x) - Real.log (ρβ x)) := by
    refine integral_mono (integrable_of_continuous' ((hzc.pow 2).div_const _))
      (integrable_of_continuous' (hzc.mul (hlogc.sub hlogb))) fun x => ?_
    simp only [htoe]
    have := log_sub_mul_ge (hpos x) (hρp x) ((hbd x).2.trans (le_max_left _ _))
      ((hρbd x).2.trans (le_max_right _ _))
    nlinarith [this]
  have hB : 0 ≤ ∫ x, toFun e x * riesz d s e x := by
    rw [← interaction_eq_integral hd s hs0 hsd K hK0 e he hereal]
    exact tsum_nonneg fun k => mul_nonneg (rieszCoeff_nonneg hd hs0 hsd k) (sq_nonneg _)
  have hC : ∫ x, toFun e x * (w x - μ) =
      β⁻¹ * (∫ x, toFun e x * (Real.log (toFun c x) - Real.log (ρβ x))) +
        ∫ x, toFun e x * riesz d s e x := by
    have : ∀ x, toFun e x * (w x - μ) =
        β⁻¹ * (toFun e x * (Real.log (toFun c x) - Real.log (ρβ x))) +
          toFun e x * riesz d s e x := fun x => by rw [hwμ x]; ring
    simp_rw [this]
    rw [integral_add (integrable_of_continuous' (f := fun x => β⁻¹ *
      (toFun e x * (Real.log (toFun c x) - Real.log (ρβ x))))
      (continuous_const.mul (hzc.mul (hlogc.sub hlogb))))
      (integrable_of_continuous' (f := fun x => toFun e x * riesz d s e x) (hzc.mul hRe)),
      integral_const_mul]
  have hwbar : ∀ a : ℝ, ∫ x, toFun e x * (w x - a) = ∫ x, toFun e x * w x := fun a =>
    integral_mul_sub_const _ _ hzc hwc a hz0
  have hyoung : (β⁻¹ / M) * (∫ x, toFun e x ^ 2) ≤ ∫ x, toFun e x * (w x - ∫ y, w y) := by
    rw [hwbar, ← hwbar μ, hC]
    have : (∫ x, (toFun e x) ^ 2 / M) = (1 / M) * ∫ x, toFun e x ^ 2 := by
      rw [integral_div, one_div, inv_mul_eq_div]
    calc β⁻¹ / M * (∫ x, toFun e x ^ 2) = β⁻¹ * (1 / M * ∫ x, toFun e x ^ 2) := by ring
      _ ≤ β⁻¹ * (∫ x, toFun e x * (Real.log (toFun c x) - Real.log (ρβ x))) := by
          rw [← this]; exact mul_le_mul_of_nonneg_left hA hν.le
      _ ≤ _ := by linarith
  have hkey := sq_integral_le_of_young (toFun e) (fun x => w x - ∫ y, w y) hzc
    (hwc.sub continuous_const) (β⁻¹ / M) (div_pos hν hM) hyoung
  -- assemble
  obtain ⟨-, hnorm⟩ := hsNormSq_zero_coeffOf_sub (toFun c) ρβ hρ hρc
  rw [hcoef] at hnorm
  have hnorm' : hsNormSq 0 e = ∫ x, toFun e x ^ 2 := by
    rw [hnorm]; simp_rw [htoe]
  rw [hnorm']
  have hP : (2 * Real.pi) ^ (-2 : ℤ) = ((2 * Real.pi) ^ 2)⁻¹ := by
    rw [zpow_neg]; norm_cast
  have hPpos : 0 < (2 * Real.pi) ^ 2 := by positivity
  rw [hP] at hPoin
  have hG : (2 * Real.pi) ^ 2 * (∫ x, (w x - ∫ y, w y) ^ 2) ≤ ∫ x, ‖Torus.grad w x‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hPoin hPpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hPpos.ne', one_mul] at this
  calc cL * (2 * Real.pi) ^ 2 * (β⁻¹ / M) ^ 2 * (∫ x, toFun e x ^ 2)
      = cL * ((2 * Real.pi) ^ 2 * ((β⁻¹ / M) ^ 2 * (∫ x, toFun e x ^ 2))) := by ring
    _ ≤ cL * ((2 * Real.pi) ^ 2 * (∫ x, (w x - ∫ y, w y) ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkey hPpos.le) hcL.le
    _ ≤ cL * ∫ x, ‖Torus.grad w x‖ ^ 2 := mul_le_mul_of_nonneg_left hG hcL.le
    _ ≤ _ := hD1


/-! ### Section 5: the entropy-production rate and the entropy-production inequality -/

/-- The entropy-production rate `κ(β, cL, cU, lam, Lam)`. -/
def rate (d : ℕ) (s β cL cU lam Lam : ℝ) : ℝ :=
  cL * (2 * Real.pi) ^ 2 * (β⁻¹ / max cU Lam) ^ 2 /
    (β⁻¹ / lam + |rieszConst d s| * 2 ^ (((d : ℝ) - s) / 2) / 2)

theorem rate_denom_pos (d : ℕ) (s β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) :
    0 < β⁻¹ / lam + |rieszConst d s| * 2 ^ (((d : ℝ) - s) / 2) / 2 := by
  have : 0 ≤ |rieszConst d s| * 2 ^ (((d : ℝ) - s) / 2) / 2 := by positivity
  have h2 : 0 < β⁻¹ / lam := div_pos (inv_pos.mpr hβ) hlam
  linarith

theorem rate_pos (s β cL cU lam Lam : ℝ) (hβ : 0 < β) (hcL : 0 < cL) (hlam : 0 < lam)
    (hcU : cL ≤ cU) (hLam : lam ≤ Lam) : 0 < rate d s β cL cU lam Lam := by
  unfold rate
  have hM : 0 < max cU Lam := lt_of_lt_of_le (hcL.trans_le hcU) (le_max_left _ _)
  have hν : 0 < β⁻¹ := inv_pos.mpr hβ
  exact div_pos (by positivity) (rate_denom_pos d s β lam hβ hlam)

theorem entropy_production (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 2 < K) (V : Torus d → ℝ) (hV : Torus.IsCk 2 V) (β : ℝ) (hβ : 0 < β)
    (c : Coeff d) (hc : MemHs K c) (hreal : IsRealCoeff c) (h0 : c 0 = 1) (cL cU : ℝ)
    (hcL : 0 < cL) (hbd : ∀ x, cL ≤ toFun c x ∧ toFun c x ≤ cU) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρc : Continuous ρβ)
    (lam Lam : ℝ) (hlam : 0 < lam) (hρbd : ∀ x, lam ≤ ρβ x ∧ ρβ x ≤ Lam)
    (hmem : MemHs K (coeffOf ρβ)) :
    rate d s β cL cU lam Lam * (freeEnergy' d s V β⁻¹ c - freeEnergy' d s V β⁻¹ (coeffOf ρβ)) ≤
      dissipation d s V β⁻¹ c := by
  have hG := (gap_bounds hd s hs0 hsd K hK V hV β hβ c hc hreal h0 cL cU hcL hbd ρβ hρβ hρc lam
    Lam hlam hρbd hmem).2
  have hD := dissipation_ge hd s hs0 hsd K hK V hV β hβ c hc hreal h0 cL cU hcL hbd ρβ hρβ hρc
    lam Lam hlam hρbd hmem
  have hden := rate_denom_pos d s β lam hβ hlam
  have hnum : 0 ≤ cL * (2 * Real.pi) ^ 2 * (β⁻¹ / max cU Lam) ^ 2 := by positivity
  have hrate : 0 ≤ rate d s β cL cU lam Lam := div_nonneg hnum hden.le
  calc rate d s β cL cU lam Lam * (freeEnergy' d s V β⁻¹ c - freeEnergy' d s V β⁻¹ (coeffOf ρβ))
      ≤ rate d s β cL cU lam Lam * ((β⁻¹ / lam + |rieszConst d s| * 2 ^ (((d : ℝ) - s) / 2) / 2) *
          hsNormSq 0 (c - coeffOf ρβ)) := mul_le_mul_of_nonneg_left hG hrate
    _ = cL * (2 * Real.pi) ^ 2 * (β⁻¹ / max cU Lam) ^ 2 * hsNormSq 0 (c - coeffOf ρβ) := by
        unfold rate
        field_simp
    _ ≤ _ := hD

end HRS.PDE.MFDecay
