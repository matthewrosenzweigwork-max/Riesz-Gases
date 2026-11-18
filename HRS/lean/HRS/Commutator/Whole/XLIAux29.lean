import HRS.Commutator.Whole.XLIAux28

/-!
# X-LI part 29: the Hörmander condition for dyadic kernel families
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- the integral of the profile `(1+|v|)^{-(d+1/2)}` -/
def Jhalf (d : ℕ) : ℝ≥0∞ :=
  ∫⁻ v : EuclideanSpace ℝ (Fin d), ENNReal.ofReal ((1 + ‖v‖) ^ (-((d : ℝ) + 1 / 2)))

lemma integrable_phiHalf (d : ℕ) :
    Integrable (fun v : EuclideanSpace ℝ (Fin d) => (1 + ‖v‖) ^ (-((d : ℝ) + 1 / 2))) := by
  have := integrable_one_add_norm (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (r := (d : ℝ) + 1 / 2) (by rw [finrank_euclideanSpace]; simp)
  exact this

lemma Jhalf_ne_top : Jhalf d ≠ ⊤ := by
  unfold Jhalf
  have h := (integrable_phiHalf d).hasFiniteIntegral
  have : ∫⁻ v : 𝔼, ENNReal.ofReal ((1 + ‖v‖) ^ (-((d : ℝ) + 1 / 2))) =
      ∫⁻ v : 𝔼, ‖(1 + ‖v‖) ^ (-((d : ℝ) + 1 / 2))‖ₑ := by
    refine lintegral_congr fun v => ?_
    rw [← ofReal_norm, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  rw [this]
  exact h.ne

lemma lintegral_phiHalf_scale (j : ℤ) :
    ∫⁻ z : 𝔼, ENNReal.ofReal (((2 : ℝ) ^ j) ^ d * (1 + (2 : ℝ) ^ j * ‖z‖) ^ (-((d : ℝ) + 1 / 2))) =
      Jhalf d := by
  have hc : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  set f : 𝔼 → ℝ := fun v => (1 + ‖v‖) ^ (-((d : ℝ) + 1 / 2)) with hf
  have hfi : Integrable f := integrable_phiHalf d
  have hfn : ∀ v, 0 ≤ f v := fun v => Real.rpow_nonneg (by positivity) _
  have hg : (fun z : 𝔼 => ((2 : ℝ) ^ j) ^ d * (1 + (2 : ℝ) ^ j * ‖z‖) ^ (-((d : ℝ) + 1 / 2))) =
      fun z => ((2 : ℝ) ^ j) ^ d * f (((2 : ℝ) ^ j) • z) := by
    funext z
    simp only [hf, norm_smul, Real.norm_of_nonneg hc.le]
  have hlg : ∫⁻ z : 𝔼, ENNReal.ofReal (((2 : ℝ) ^ j) ^ d * (1 + (2 : ℝ) ^ j * ‖z‖) ^ (-((d : ℝ) + 1 / 2))) =
      ∫⁻ z : 𝔼, ENNReal.ofReal (((2 : ℝ) ^ j) ^ d * f (((2 : ℝ) ^ j) • z)) :=
    lintegral_congr fun z => by rw [congrFun hg z]
  rw [hlg]
  have hgi : Integrable (fun z : 𝔼 => ((2 : ℝ) ^ j) ^ d * f (((2 : ℝ) ^ j) • z)) := by
    refine Integrable.const_mul ?_ _
    exact hfi.comp_smul hc.ne'
  rw [← ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun z => by
    have := hfn (((2 : ℝ) ^ j) • z); positivity)]
  unfold Jhalf
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall hfn)]
  congr 1
  rw [integral_const_mul, Measure.integral_comp_smul (volume : Measure 𝔼) f ((2 : ℝ) ^ j)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  rw [abs_of_pos (by positivity)]
  field_simp


lemma phiR_le_tail {j : ℤ} {ρ : ℝ} (hρ : 0 < ρ) {z : 𝔼} (hz : 2 * ρ ≤ ‖z‖) :
    phiR j z ≤ (1 + (2 : ℝ) ^ j * (2 * ρ)) ^ (-(1 / 2 : ℝ)) *
      (((2 : ℝ) ^ j) ^ d * (1 + (2 : ℝ) ^ j * ‖z‖) ^ (-((d : ℝ) + 1 / 2))) := by
  have hc : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  set a : ℝ := 1 + (2 : ℝ) ^ j * (2 * ρ) with ha
  set b : ℝ := 1 + (2 : ℝ) ^ j * ‖z‖ with hb
  have ha0 : 0 < a := by positivity
  have hab : a ≤ b := by
    rw [ha, hb]
    have : (2 : ℝ) ^ j * (2 * ρ) ≤ (2 : ℝ) ^ j * ‖z‖ := by gcongr
    linarith
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have e1 : b ^ (-((d : ℝ) + 1 / 2)) * b ^ (-(1 / 2 : ℝ)) = ((b ^ (d + 1)))⁻¹ := by
    rw [← Real.rpow_add hb0]
    have : -((d : ℝ) + 1 / 2) + -(1 / 2 : ℝ) = -((d + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.rpow_neg hb0.le, Real.rpow_natCast]
  have e2 : b ^ (-(1 / 2 : ℝ)) ≤ a ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ha0 hab (by norm_num)
  unfold phiR
  rw [← hb, ← e1]
  have h3 : 0 ≤ ((2 : ℝ) ^ j) ^ d := by positivity
  have h4 : 0 ≤ b ^ (-((d : ℝ) + 1 / 2)) := Real.rpow_nonneg hb0.le _
  calc ((2 : ℝ) ^ j) ^ d * (b ^ (-((d : ℝ) + 1 / 2)) * b ^ (-(1 / 2 : ℝ)))
      ≤ ((2 : ℝ) ^ j) ^ d * (b ^ (-((d : ℝ) + 1 / 2)) * a ^ (-(1 / 2 : ℝ))) := by gcongr
    _ = _ := by ring

lemma tail_Phi (j : ℤ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ z in {z : 𝔼 | 2 * ρ ≤ ‖z‖}, Phi j z ≤
      ENNReal.ofReal ((1 + (2 : ℝ) ^ j * (2 * ρ)) ^ (-(1 / 2 : ℝ))) * Jhalf d := by
  have hc : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hpt : ∀ z ∈ {z : 𝔼 | 2 * ρ ≤ ‖z‖}, Phi j z ≤
      ENNReal.ofReal ((1 + (2 : ℝ) ^ j * (2 * ρ)) ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (((2 : ℝ) ^ j) ^ d * (1 + (2 : ℝ) ^ j * ‖z‖) ^ (-((d : ℝ) + 1 / 2))) := by
    intro z hz
    rw [Phi_eq_phiR, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
    exact ENNReal.ofReal_le_ofReal (phiR_le_tail hρ hz)
  calc ∫⁻ z in {z : 𝔼 | 2 * ρ ≤ ‖z‖}, Phi j z
      ≤ ∫⁻ z in {z : 𝔼 | 2 * ρ ≤ ‖z‖}, ENNReal.ofReal ((1 + (2 : ℝ) ^ j * (2 * ρ)) ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (((2 : ℝ) ^ j) ^ d * (1 + (2 : ℝ) ^ j * ‖z‖) ^ (-((d : ℝ) + 1 / 2))) :=
        setLIntegral_mono' (measurableSet_le measurable_const measurable_norm) hpt
    _ ≤ ∫⁻ z, ENNReal.ofReal ((1 + (2 : ℝ) ^ j * (2 * ρ)) ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (((2 : ℝ) ^ j) ^ d * (1 + (2 : ℝ) ^ j * ‖z‖) ^ (-((d : ℝ) + 1 / 2))) :=
        setLIntegral_le_lintegral _ _
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_phiHalf_scale]

/-- the geometric sum over `ℤ` is finite -/
lemma tsum_geom_int {r : ℝ≥0∞} (hr : r < 1) : ∑' k : ℤ, r ^ k.natAbs ≠ ⊤ := by
  have h := tsum_of_nat_of_neg_add_one (f := fun k : ℤ => r ^ k.natAbs) ENNReal.summable
    ENNReal.summable
  rw [h]
  have e1 : ∑' n : ℕ, r ^ (n : ℤ).natAbs = ∑' n : ℕ, r ^ n := by simp
  have e2 : ∑' n : ℕ, r ^ (-((n : ℤ) + 1)).natAbs = ∑' n : ℕ, r ^ (n + 1) := by
    refine tsum_congr fun n => ?_
    congr 1
  rw [e1, e2, ENNReal.tsum_geometric]
  simp only [pow_succ]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
  have h1 : (1 - r)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr).ne'
  exact ENNReal.add_ne_top.2 ⟨h1, ENNReal.mul_ne_top h1 (ne_top_of_lt (hr.trans ENNReal.one_lt_top))⟩

/-- the Hörmander smoothness condition for a family of kernels -/
def HormK (K : ℤ → 𝔼 → ℂ) (H : ℝ≥0∞) : Prop :=
  ∀ w : 𝔼, ∫⁻ z in {z : 𝔼 | 2 * ‖w‖ ≤ ‖z‖}, ∑' j, ‖K j (z - w) - K j z‖ₑ ≤ H

lemma r0_lt_one : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

lemma geomA {ρ : ℝ} (hρ : 0 < ρ) {n j : ℤ} (hn : (2 : ℝ) ^ n * ρ < 1) (hj : j ≤ n) :
    (2 : ℝ) ^ j * ρ ≤ ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ (j - n).natAbs := by
  set k : ℕ := (j - n).natAbs with hk
  have hkn : (k : ℤ) = n - j := by omega
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have h1 : (2 : ℝ) ^ j * 2 ^ k = 2 ^ n := by
    rw [← zpow_natCast, hkn, ← zpow_add₀ (by norm_num)]
    congr 1; ring
  have h2 : (2 : ℝ) ^ j * ρ ≤ ((2 : ℝ)⁻¹) ^ k := by
    rw [inv_pow, ← one_div, le_div_iff₀ h2k]
    calc (2 : ℝ) ^ j * ρ * 2 ^ k = ((2 : ℝ) ^ j * 2 ^ k) * ρ := by ring
      _ = 2 ^ n * ρ := by rw [h1]
      _ ≤ 1 := hn.le
  refine h2.trans ?_
  have h3 : (2 : ℝ)⁻¹ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have : (2 : ℝ)⁻¹ = (2 : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]
    rw [this]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  exact pow_le_pow_left₀ (by norm_num) h3 k

lemma geomB {ρ : ℝ} (hρ : 0 < ρ) {n j : ℤ} (hn : 1 ≤ (2 : ℝ) ^ (n + 1) * ρ) (hj : n < j) :
    (1 + (2 : ℝ) ^ j * (2 * ρ)) ^ (-(1 / 2 : ℝ)) ≤ ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ (j - n).natAbs := by
  set k : ℕ := (j - n).natAbs with hk
  have hkn : (k : ℤ) = j - n := by omega
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have h1 : (2 : ℝ) ^ j * (2 * ρ) = 2 ^ k * (2 ^ (n + 1) * ρ) := by
    rw [← zpow_natCast, hkn]
    have : (2 : ℝ) ^ j * (2 * ρ) = (2 : ℝ) ^ (j + 1) * ρ := by
      rw [zpow_add₀ (by norm_num), zpow_one]; ring
    rw [this, ← mul_assoc, ← zpow_add₀ (by norm_num)]
    congr 2; ring
  have h2 : (2 : ℝ) ^ k ≤ 1 + (2 : ℝ) ^ j * (2 * ρ) := by
    rw [h1]
    nlinarith
  have h3 : (1 + (2 : ℝ) ^ j * (2 * ρ)) ^ (-(1 / 2 : ℝ)) ≤ ((2 : ℝ) ^ k) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos h2k h2 (by norm_num)
  refine h3.trans (le_of_eq ?_)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
    Real.rpow_mul_natCast (by norm_num)]

/-- **the Hörmander condition** for the dyadic kernels of a symbol family whose gradient symbols
are again symbol families -/
lemma hormK_dK {R R' : ℝ} {Θ : ℤ → 𝔼 → ℂ} (hΘ : SymFam R Θ)
    (hG : ∀ l : Fin d, SymFam R' (gradS Θ (EuclideanSpace.single l (1 : ℝ)))) :
    ∃ H : ℝ≥0∞, H ≠ ⊤ ∧ HormK (fun j => dK Θ j) H := by
  obtain ⟨C, hC0, hC⟩ := dK_diff_le hΘ hG
  set r : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (-(1 / 2 : ℝ))) with hr
  have hr1 : r < 1 := by
    rw [hr, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 r0_lt_one
  set G : ℝ≥0∞ := ∑' k : ℤ, r ^ k.natAbs with hGdef
  have hGne : G ≠ ⊤ := tsum_geom_int hr1
  set Cn : ℝ≥0∞ := ENNReal.ofReal C * (KP d + Jhalf d) with hCn
  have hCnne : Cn ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨KP_ne_top, Jhalf_ne_top⟩)
  refine ⟨Cn * G, ENNReal.mul_ne_top hCnne hGne, fun w => ?_⟩
  by_cases hw : w = 0
  · subst hw; simp
  have hρ : 0 < ‖w‖ := norm_pos_iff.2 hw
  set ρ : ℝ := ‖w‖ with hρdef
  set S : Set 𝔼 := {z : 𝔼 | 2 * ρ ≤ ‖z‖} with hS
  have hSm : MeasurableSet S := measurableSet_le measurable_const measurable_norm
  have hKm : ∀ j, Measurable (dK Θ j) := fun j => (dK_continuous hΘ j).measurable
  have hmeas : ∀ j, AEMeasurable (fun z : 𝔼 => ‖dK Θ j (z - w) - dK Θ j z‖ₑ)
      (volume.restrict S) := fun j =>
    ((((hKm j).comp (measurable_id.sub_const w)).sub (hKm j)).enorm).aemeasurable
  show ∫⁻ z in S, ∑' j, ‖dK Θ j (z - w) - dK Θ j z‖ₑ ≤ Cn * G
  rw [lintegral_tsum hmeas]
  obtain ⟨n, hn1, hn2⟩ := _root_.exists_mem_Ioc_zpow (show 0 < 1 / ρ by positivity)
    (one_lt_two : (1 : ℝ) < 2)
  have hn1' : (2 : ℝ) ^ n * ρ < 1 := by
    have := (lt_div_iff₀ hρ).1 hn1
    exact this
  have hn2' : 1 ≤ (2 : ℝ) ^ (n + 1) * ρ := by
    have := (div_le_iff₀ hρ).1 hn2
    exact this
  -- the pointwise bounds on `S`
  have hpt1 : ∀ j, ∀ z ∈ S, ‖dK Θ j (z - w) - dK Θ j z‖ₑ ≤
      ENNReal.ofReal (C * ((2 : ℝ) ^ j * ρ)) * Phi j z := by
    intro j z hz
    rw [← ofReal_norm, Phi_eq_phiR, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (hC j z w hz).1
  have hpt2 : ∀ j, ∀ z ∈ S, ‖dK Θ j (z - w) - dK Θ j z‖ₑ ≤ ENNReal.ofReal C * Phi j z := by
    intro j z hz
    rw [← ofReal_norm, Phi_eq_phiR, ← ENNReal.ofReal_mul hC0]
    exact ENNReal.ofReal_le_ofReal (hC j z w hz).2
  have hIj : ∀ j : ℤ, ∫⁻ z in S, ‖dK Θ j (z - w) - dK Θ j z‖ₑ ≤ Cn * r ^ (j - n).natAbs := by
    intro j
    by_cases hj : j ≤ n
    · have h1 : ∫⁻ z in S, ‖dK Θ j (z - w) - dK Θ j z‖ₑ ≤
          ENNReal.ofReal (C * ((2 : ℝ) ^ j * ρ)) * KP d := by
        calc ∫⁻ z in S, ‖dK Θ j (z - w) - dK Θ j z‖ₑ
            ≤ ∫⁻ z in S, ENNReal.ofReal (C * ((2 : ℝ) ^ j * ρ)) * Phi j z :=
              setLIntegral_mono' hSm (hpt1 j)
          _ ≤ ∫⁻ z, ENNReal.ofReal (C * ((2 : ℝ) ^ j * ρ)) * Phi j z := setLIntegral_le_lintegral _ _
          _ = ENNReal.ofReal (C * ((2 : ℝ) ^ j * ρ)) * ∫⁻ z, Phi j z :=
              lintegral_const_mul _ (Phi_measurable j)
          _ ≤ _ := mul_le_mul_right (lintegral_Phi_le_KP j) _
      refine h1.trans ?_
      have h2 : ENNReal.ofReal (C * ((2 : ℝ) ^ j * ρ)) ≤ ENNReal.ofReal C * r ^ (j - n).natAbs := by
        rw [ENNReal.ofReal_mul hC0, hr, ← ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) _)]
        exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (geomA hρ hn1' hj)) _
      calc ENNReal.ofReal (C * ((2 : ℝ) ^ j * ρ)) * KP d
          ≤ (ENNReal.ofReal C * r ^ (j - n).natAbs) * KP d := mul_le_mul_left h2 _
        _ ≤ (ENNReal.ofReal C * r ^ (j - n).natAbs) * (KP d + Jhalf d) :=
            mul_le_mul_right le_self_add _
        _ = Cn * r ^ (j - n).natAbs := by rw [hCn]; ring
    · have hj' : n < j := not_le.1 hj
      have h1 : ∫⁻ z in S, ‖dK Θ j (z - w) - dK Θ j z‖ₑ ≤
          ENNReal.ofReal C * (ENNReal.ofReal ((1 + (2 : ℝ) ^ j * (2 * ρ)) ^ (-(1 / 2 : ℝ))) *
            Jhalf d) := by
        calc ∫⁻ z in S, ‖dK Θ j (z - w) - dK Θ j z‖ₑ
            ≤ ∫⁻ z in S, ENNReal.ofReal C * Phi j z := setLIntegral_mono' hSm (hpt2 j)
          _ = ENNReal.ofReal C * ∫⁻ z in S, Phi j z := lintegral_const_mul _ (Phi_measurable j)
          _ ≤ _ := mul_le_mul_right (tail_Phi j hρ) _
      refine h1.trans ?_
      have h2 : ENNReal.ofReal ((1 + (2 : ℝ) ^ j * (2 * ρ)) ^ (-(1 / 2 : ℝ))) ≤
          r ^ (j - n).natAbs := by
        rw [hr, ← ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) _)]
        exact ENNReal.ofReal_le_ofReal (geomB hρ hn2' hj')
      calc ENNReal.ofReal C * (ENNReal.ofReal ((1 + (2 : ℝ) ^ j * (2 * ρ)) ^ (-(1 / 2 : ℝ))) *
            Jhalf d)
          ≤ ENNReal.ofReal C * (r ^ (j - n).natAbs * Jhalf d) :=
            mul_le_mul_right (mul_le_mul_left h2 _) _
        _ ≤ ENNReal.ofReal C * (r ^ (j - n).natAbs * (KP d + Jhalf d)) :=
            mul_le_mul_right (mul_le_mul_right le_add_self _) _
        _ = Cn * r ^ (j - n).natAbs := by rw [hCn]; ring
  calc ∑' j : ℤ, ∫⁻ z in S, ‖dK Θ j (z - w) - dK Θ j z‖ₑ
      ≤ ∑' j : ℤ, Cn * r ^ (j - n).natAbs := ENNReal.tsum_le_tsum hIj
    _ = Cn * ∑' j : ℤ, r ^ (j - n).natAbs := ENNReal.tsum_mul_left
    _ = Cn * G := by
        congr 1
        exact (Equiv.subRight n).tsum_eq (fun k : ℤ => r ^ k.natAbs)

end HRS.Commutator.Whole.XLI
