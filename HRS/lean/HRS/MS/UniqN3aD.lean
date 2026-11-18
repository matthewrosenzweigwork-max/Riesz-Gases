import HRS.MS.UniqN3aA

/-!
# N3a, part D: Fourier-side bounds for the symbol `m_q(ξ) = c (2π⟨ξ,q⟩)² ‖ξ‖^{s-d}`

* `mq_sq_le`: `m_q² ≤ 2 K² ((2π)⁴ + d Σ_l (2π ξ_l)⁴)`, `K = c ‖q‖²` (needs `d - 2 ≤ s < d`);
* `xi4_ae`, `energy`, `mq_schwartz`: for a real Schwartz `ψ`, `m_q ψ̂ ∈ L²` with
  `∫ |m_q ψ̂|² ≤ 2 K² E(ψ)`, `E(ψ) = (2π)⁴ ∫ψ² + d Σ_l ∫ (D_l² ψ)²`;
* `cs_L2`: Cauchy–Schwarz for complex `L²` functions.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate SchwartzMap LineDeriv

namespace HRS.MS.UniqN3a
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UniqT2

variable {d : ℕ}

/-- The symbol `c (2π⟨ξ,q⟩)² ‖ξ‖^{s-d}`. -/
def mq (c s : ℝ) (q : Euc d) (ξ : Euc d) : ℝ :=
  c * (2 * Real.pi * inner ℝ ξ q) ^ 2 * ‖ξ‖ ^ (s - d)

theorem measurable_mq (c s : ℝ) (q : Euc d) : Measurable (mq c s q) := by
  unfold mq
  exact (measurable_const.mul ((measurable_const.mul
    (Continuous.measurable (by fun_prop : Continuous fun ξ : Euc d => inner ℝ ξ q))).pow_const 2)).mul
    (measurable_norm.pow_const _)

theorem mq_nonneg {c : ℝ} (hc : 0 < c) (s : ℝ) (q ξ : Euc d) : 0 ≤ mq c s q ξ := by
  unfold mq; positivity

theorem mq_le {c s : ℝ} (hc : 0 < c) (hs2 : (d : ℝ) - 2 ≤ s) (hsd : s < d) (q ξ : Euc d) :
    mq c s q ξ ≤ c * ‖q‖ ^ 2 * (2 * Real.pi) ^ 2 * (1 + ‖ξ‖ ^ 2) := by
  by_cases hξ : ξ = 0
  · subst hξ; simp [mq]; positivity
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  unfold mq
  have h1 : (inner ℝ ξ q) ^ 2 ≤ ‖ξ‖ ^ 2 * ‖q‖ ^ 2 := by
    have := abs_real_inner_le_norm ξ q
    calc (inner ℝ ξ q) ^ 2 = |inner ℝ ξ q| ^ 2 := (sq_abs _).symm
      _ ≤ (‖ξ‖ * ‖q‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = _ := by ring
  have h2 : ‖ξ‖ ^ 2 * ‖ξ‖ ^ (s - d) = ‖ξ‖ ^ (s - d + 2) := by
    rw [show s - d + 2 = (s - d) + (2 : ℕ) by norm_num, Real.rpow_add hn, Real.rpow_natCast, mul_comm]
  have h3 : ‖ξ‖ ^ (s - d + 2) ≤ 1 + ‖ξ‖ ^ 2 := by
    rcases le_total ‖ξ‖ 1 with h | h
    · have := Real.rpow_le_one (norm_nonneg ξ) h (by linarith : 0 ≤ s - d + 2)
      nlinarith [sq_nonneg ‖ξ‖]
    · have := Real.rpow_le_rpow_of_exponent_le h (by linarith : s - d + 2 ≤ (2 : ℝ))
      rw [Real.rpow_two] at this
      linarith [sq_nonneg ‖ξ‖]
  have hp : 0 ≤ ‖ξ‖ ^ (s - d) := Real.rpow_nonneg (norm_nonneg _) _
  calc c * (2 * Real.pi * inner ℝ ξ q) ^ 2 * ‖ξ‖ ^ (s - d)
      = c * (2 * Real.pi) ^ 2 * ((inner ℝ ξ q) ^ 2 * ‖ξ‖ ^ (s - d)) := by ring
    _ ≤ c * (2 * Real.pi) ^ 2 * ((‖ξ‖ ^ 2 * ‖q‖ ^ 2) * ‖ξ‖ ^ (s - d)) := by gcongr
    _ = c * (2 * Real.pi) ^ 2 * ‖q‖ ^ 2 * (‖ξ‖ ^ 2 * ‖ξ‖ ^ (s - d)) := by ring
    _ ≤ c * (2 * Real.pi) ^ 2 * ‖q‖ ^ 2 * (1 + ‖ξ‖ ^ 2) := by rw [h2]; gcongr
    _ = _ := by ring

theorem mq_sq_le {c s : ℝ} (hc : 0 < c) (hs2 : (d : ℝ) - 2 ≤ s) (hsd : s < d) (q ξ : Euc d) :
    (mq c s q ξ) ^ 2 ≤ 2 * (c * ‖q‖ ^ 2) ^ 2 *
      ((2 * Real.pi) ^ 4 + (d : ℝ) * ∑ l, (2 * Real.pi * ξ l) ^ 4) := by
  have h0 := mq_nonneg hc s q ξ
  have h1 := mq_le hc hs2 hsd q ξ
  set K := c * ‖q‖ ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hnorm : (2 * Real.pi * ‖ξ‖) ^ 2 = ∑ l, (2 * Real.pi * ξ l) ^ 2 := by
    simp only [mul_pow, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, Finset.mul_sum]
  have hcs : (∑ l, (2 * Real.pi * ξ l) ^ 2) ^ 2 ≤ (d : ℝ) * ∑ l, (2 * Real.pi * ξ l) ^ 4 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun l => (2 * Real.pi * ξ l) ^ 2)
    simpa [← pow_mul, Finset.card_univ] using this
  have h2 : mq c s q ξ ≤ K * ((2 * Real.pi) ^ 2 + (2 * Real.pi * ‖ξ‖) ^ 2) := by
    refine h1.trans (le_of_eq ?_); simp only [hK]; ring
  calc (mq c s q ξ) ^ 2 ≤ (K * ((2 * Real.pi) ^ 2 + (2 * Real.pi * ‖ξ‖) ^ 2)) ^ 2 :=
        pow_le_pow_left₀ h0 h2 2
    _ = K ^ 2 * ((2 * Real.pi) ^ 2 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ 2 := by ring
    _ ≤ K ^ 2 * (2 * ((2 * Real.pi) ^ 4 + ((2 * Real.pi * ‖ξ‖) ^ 2) ^ 2)) := by
        gcongr; nlinarith [sq_nonneg ((2 * Real.pi) ^ 2 - (2 * Real.pi * ‖ξ‖) ^ 2)]
    _ ≤ K ^ 2 * (2 * ((2 * Real.pi) ^ 4 + (d : ℝ) * ∑ l, (2 * Real.pi * ξ l) ^ 4)) := by
        rw [hnorm]; gcongr
    _ = _ := by ring

/-- Plancherel for `D_l² ψ`: `((2π ξ_l)² |ψ̂|)² = |\widehat{D_l² ψ}|²` a.e. -/
theorem xi4_ae (l : Fin d) (ψ : SchwartzMap (Euc d) ℝ) :
    (fun ξ : Euc d => ((2 * Real.pi * ξ l) ^ 2 * ‖fourierL2 ψ ξ‖) ^ 2) =ᵐ[volume]
      fun ξ => ‖fourierL2 (dl l (dl l ψ)) ξ‖ ^ 2 := by
  filter_upwards [fourierL2_schwartz ψ, fourierL2_schwartz (dl l (dl l ψ))] with ξ h1 h2
  rw [h1, h2, fourier_dl l (dl l ψ) ξ, fourier_dl l ψ ξ]
  have e : (2 * Real.pi * Complex.I * ((ξ l : ℝ) : ℂ)) *
      ((2 * Real.pi * Complex.I * ((ξ l : ℝ) : ℂ)) * 𝓕 (fun x : Euc d => ((ψ x : ℝ) : ℂ)) ξ) =
      ((-(2 * Real.pi * ξ l) ^ 2 : ℝ) : ℂ) * 𝓕 (fun x : Euc d => ((ψ x : ℝ) : ℂ)) ξ := by
    push_cast; ring_nf; simp [Complex.I_sq]
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (sq_nonneg _)]

theorem xi4_integral (l : Fin d) (ψ : SchwartzMap (Euc d) ℝ) :
    Integrable (fun ξ : Euc d => ((2 * Real.pi * ξ l) ^ 2 * ‖fourierL2 ψ ξ‖) ^ 2) ∧
    ∫ ξ : Euc d, ((2 * Real.pi * ξ l) ^ 2 * ‖fourierL2 ψ ξ‖) ^ 2 = ∫ x, (dl l (dl l ψ) x) ^ 2 := by
  have hm : MemLp (⇑(dl l (dl l ψ))) 2 volume := (dl l (dl l ψ)).memLp 2 volume
  refine ⟨(integrable_norm_sq_fourierL2 hm).congr (xi4_ae l ψ).symm, ?_⟩
  rw [integral_congr_ae (xi4_ae l ψ), integral_norm_sq_fourierL2 hm]

/-- The `H²`-type energy of a Schwartz function. -/
def energy (ψ : SchwartzMap (Euc d) ℝ) : ℝ :=
  (2 * Real.pi) ^ 4 * (∫ x, ψ x ^ 2) + (d : ℝ) * ∑ l, ∫ x, (dl l (dl l ψ) x) ^ 2

/-- `m_q ψ̂ ∈ L²` for Schwartz `ψ`, with an energy bound. -/
theorem mq_schwartz {c s : ℝ} (hc : 0 < c) (hs2 : (d : ℝ) - 2 ≤ s) (hsd : s < d) (q : Euc d)
    (ψ : SchwartzMap (Euc d) ℝ) :
    Integrable (fun ξ => ‖((mq c s q ξ : ℝ) : ℂ) * fourierL2 ψ ξ‖ ^ 2) ∧
    ∫ ξ, ‖((mq c s q ξ : ℝ) : ℂ) * fourierL2 ψ ξ‖ ^ 2 ≤ 2 * (c * ‖q‖ ^ 2) ^ 2 * energy ψ := by
  have hmψ : MemLp (⇑ψ) 2 volume := ψ.memLp 2 volume
  have hI0 := integrable_norm_sq_fourierL2 hmψ
  have hI : ∀ l, Integrable (fun ξ : Euc d => ((2 * Real.pi * ξ l) ^ 2 * ‖fourierL2 ψ ξ‖) ^ 2) :=
    fun l => (xi4_integral l ψ).1
  set bd : Euc d → ℝ := fun ξ => 2 * (c * ‖q‖ ^ 2) ^ 2 *
    ((2 * Real.pi) ^ 4 * ‖fourierL2 ψ ξ‖ ^ 2 + d * ∑ l, ((2 * Real.pi * ξ l) ^ 2 * ‖fourierL2 ψ ξ‖) ^ 2)
    with hbd
  have hbdi : Integrable bd :=
    ((hI0.const_mul _).add ((integrable_finsetSum _ fun l _ => hI l).const_mul _)).const_mul _
  have hle : ∀ ξ, ‖((mq c s q ξ : ℝ) : ℂ) * fourierL2 ψ ξ‖ ^ 2 ≤ bd ξ := by
    intro ξ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mq_nonneg hc s q ξ), mul_pow]
    have h := mq_sq_le hc hs2 hsd q ξ
    have h2 := sq_nonneg ‖fourierL2 ψ ξ‖
    simp only [hbd]
    calc mq c s q ξ ^ 2 * ‖fourierL2 ψ ξ‖ ^ 2
        ≤ (2 * (c * ‖q‖ ^ 2) ^ 2 * ((2 * Real.pi) ^ 4 + (d : ℝ) * ∑ l, (2 * Real.pi * ξ l) ^ 4)) *
            ‖fourierL2 ψ ξ‖ ^ 2 := by gcongr
      _ = _ := by
        have e : ∑ l, ((2 * Real.pi * ξ l) ^ 2 * ‖fourierL2 ψ ξ‖) ^ 2 =
            (∑ l, (2 * Real.pi * ξ l) ^ 4) * ‖fourierL2 ψ ξ‖ ^ 2 := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun l _ => by ring
        rw [e]; ring
  have hmeas : AEStronglyMeasurable (fun ξ => ‖((mq c s q ξ : ℝ) : ℂ) * fourierL2 ψ ξ‖ ^ 2) volume :=
    (((Complex.measurable_ofReal.comp (measurable_mq c s q)).aestronglyMeasurable.mul
      (aestronglyMeasurable_fourierL2 hmψ)).norm).pow 2
  have hint : Integrable (fun ξ => ‖((mq c s q ξ : ℝ) : ℂ) * fourierL2 ψ ξ‖ ^ 2) :=
    hbdi.mono' hmeas (Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hle ξ)
  refine ⟨hint, (integral_mono hint hbdi hle).trans (le_of_eq ?_)⟩
  simp only [hbd]
  rw [integral_const_mul, integral_add (hI0.const_mul _) ((integrable_finsetSum _ fun l _ => hI l).const_mul _),
    integral_const_mul, integral_const_mul, integral_finsetSum _ fun l _ => hI l,
    integral_norm_sq_fourierL2 hmψ]
  simp only [energy, (xi4_integral _ ψ).2]

/-- Cauchy–Schwarz for complex `L²` functions. -/
theorem cs_L2 {f g : Euc d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ‖∫ ξ, f ξ * conj (g ξ)‖ ≤ Real.sqrt (∫ ξ, ‖f ξ‖ ^ 2) * Real.sqrt (∫ ξ, ‖g ξ‖ ^ 2) := by
  have hP : Integrable (fun ξ => ‖f ξ‖ ^ 2) := hf.norm.integrable_sq
  have hQ : Integrable (fun ξ => ‖g ξ‖ ^ 2) := hg.norm.integrable_sq
  have hR : Integrable (fun ξ => ‖f ξ‖ * ‖g ξ‖) := by
    refine Integrable.mono' ((hP.add hQ).div_const 2)
      (hf.aestronglyMeasurable.norm.mul hg.aestronglyMeasurable.norm)
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖f ξ‖ - ‖g ξ‖)]
  have h1 : ‖∫ ξ, f ξ * conj (g ξ)‖ ≤ ∫ ξ, ‖f ξ‖ * ‖g ξ‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp [norm_mul]
  have h2 : (∫ ξ, ‖f ξ‖ * ‖g ξ‖) ^ 2 ≤ (∫ ξ, ‖f ξ‖ ^ 2) * (∫ ξ, ‖g ξ‖ ^ 2) :=
    cs_aux hP hQ hR fun t ξ => by nlinarith [sq_nonneg (t * ‖f ξ‖ - ‖g ξ‖)]
  rw [← Real.sqrt_mul (integral_nonneg fun ξ => sq_nonneg _)]
  exact h1.trans ((le_abs_self _).trans (Real.abs_le_sqrt h2))

end HRS.MS.UniqN3a
