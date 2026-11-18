import HRS.Main.EqBiasAux9

/-!
# EQ-BIAS, S9a: abstract variance lemmas

* `eqbias_var_sum`: for an exchangeable `P` and `φ ≥ 0` with one- and two-point moment bounds,
  `|Var[∑ φ(Y_i)] - n E φ(Y_0)²| ≤ n² max(Cone², Cpair)`.
* `eqbias_var_mink`: `|Var(X+Y) - Var X| ≤ Var Y + 2√(Var X Var Y)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

open HRS.External HRS.CavResp HRS.MarginalAux

theorem eqbias_var_sum {n : ℕ} (hn : 0 < n) {P : Measure (Config d n)} [IsProbabilityMeasure P]
    (hP : Entropy.IsExchangeable P) {φ : Torus d → ℝ} (hφm : Measurable φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (h2 : ∀ i : Fin n, Integrable (fun Y : Config d n => φ (Y i) ^ 2) P) {Cone Cpair : ℝ}
    (hCone : 0 ≤ Cone) (hCpair : 0 ≤ Cpair)
    (hone : ∀ i : Fin n, ∫ Y, φ (Y i) ∂P ≤ Cone)
    (hpair : ∀ i j : Fin n, i ≠ j → ∫ Y, φ (Y i) * φ (Y j) ∂P ≤ Cpair) :
    MemLp (fun Y : Config d n => ∑ i, φ (Y i)) 2 P ∧
      |Var[fun Y : Config d n => ∑ i, φ (Y i); P] -
          n * ∫ Y, φ (Y ⟨0, hn⟩) ^ 2 ∂P| ≤ (n : ℝ) ^ 2 * max (Cone ^ 2) Cpair := by
  have ham : ∀ i : Fin n, Measurable fun Y : Config d n => φ (Y i) := fun i =>
    hφm.comp (measurable_pi_apply i)
  have hmem : ∀ i : Fin n, MemLp (fun Y : Config d n => φ (Y i)) 2 P := fun i =>
    (memLp_two_iff_integrable_sq (ham i).aestronglyMeasurable).2 (h2 i)
  have hF : MemLp (fun Y : Config d n => ∑ i, φ (Y i)) 2 P :=
    memLp_finset_sum _ fun i _ => hmem i
  refine ⟨hF, ?_⟩
  have hint : ∀ i : Fin n, Integrable (fun Y : Config d n => φ (Y i)) P := fun i =>
    (hmem i).integrable one_le_two
  have hprod : ∀ i j : Fin n, Integrable (fun Y : Config d n => φ (Y i) * φ (Y j)) P :=
    fun i j => (hmem i).integrable_mul (hmem j)
  have hsq : ∀ i : Fin n, ∫ Y, φ (Y i) ^ 2 ∂P = ∫ Y, φ (Y ⟨0, hn⟩) ^ 2 ∂P := by
    intro i
    have := hP.marginal_eq i ⟨0, hn⟩
    have e1 : ∫ Y, φ (Y i) ^ 2 ∂P = ∫ y, φ y ^ 2 ∂(P.map fun Y => Y i) := by
      rw [integral_map (measurable_pi_apply i).aemeasurable
        ((hφm.pow_const 2).aestronglyMeasurable)]
    have e2 : ∫ Y, φ (Y ⟨0, hn⟩) ^ 2 ∂P = ∫ y, φ y ^ 2 ∂(P.map fun Y => Y ⟨0, hn⟩) := by
      rw [integral_map (measurable_pi_apply (⟨0, hn⟩ : Fin n)).aemeasurable
        ((hφm.pow_const 2).aestronglyMeasurable)]
    rw [e1, e2, this]
  have hvs := variance_eq_sub hF
  simp only [Pi.pow_apply] at hvs
  rw [hvs]
  have hEF2 : ∫ Y, (∑ i, φ (Y i)) ^ 2 ∂P =
      ∑ i, ∫ Y, φ (Y i) ^ 2 ∂P + ∑ i, ∑ j ∈ Finset.univ.erase i, ∫ Y, φ (Y i) * φ (Y j) ∂P := by
    have e : ∀ Y : Config d n, (∑ i, φ (Y i)) ^ 2 =
        ∑ i, (φ (Y i) ^ 2 + ∑ j ∈ Finset.univ.erase i, φ (Y i) * φ (Y j)) := by
      intro Y
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), sq]
    simp_rw [e]
    rw [integral_finset_sum _ fun i _ => ?_]
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_add (h2 i) (integrable_finset_sum _ fun j _ => hprod i j),
        integral_finset_sum _ fun j _ => hprod i j]
    · exact (h2 i).add (integrable_finset_sum _ fun j _ => hprod i j)
  have hEF : ∫ Y, ∑ i, φ (Y i) ∂P = ∑ i, ∫ Y, φ (Y i) ∂P := integral_finset_sum _ fun i _ => hint i
  have hnn : 0 ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, ∫ Y, φ (Y i) * φ (Y j) ∂P :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      integral_nonneg fun Y => mul_nonneg (hφ0 _) (hφ0 _)
  have hcard : ∀ i : Fin n, ((Finset.univ.erase i).card : ℝ) ≤ n := by
    intro i
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    push_cast; have : (0 : ℝ) ≤ 1 := by norm_num
    have : (n : ℝ) - 1 ≤ n := by linarith
    have h1 : (((n - 1 : ℕ)) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    exact h1
  have hup : ∑ i, ∑ j ∈ Finset.univ.erase i, ∫ Y, φ (Y i) * φ (Y j) ∂P ≤ (n : ℝ) ^ 2 * Cpair := by
    calc _ ≤ ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, Cpair :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj =>
            hpair i j (Finset.ne_of_mem_erase hj).symm
      _ = ∑ i : Fin n, ((Finset.univ.erase i).card : ℝ) * Cpair := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ _i : Fin n, (n : ℝ) * Cpair :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hcard i) hCpair
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hmean : (∑ i, ∫ Y, φ (Y i) ∂P) ^ 2 ≤ (n : ℝ) ^ 2 * Cone ^ 2 := by
    have h0 : 0 ≤ ∑ i, ∫ Y, φ (Y i) ∂P := Finset.sum_nonneg fun i _ => integral_nonneg fun Y => hφ0 _
    have h1 : ∑ i, ∫ Y, φ (Y i) ∂P ≤ (n : ℝ) * Cone := by
      calc _ ≤ ∑ _i : Fin n, Cone := Finset.sum_le_sum fun i _ => hone i
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    nlinarith
  have hmean0 : 0 ≤ (∑ i, ∫ Y, φ (Y i) ∂P) ^ 2 := sq_nonneg _
  have hdiag : ∑ i, ∫ Y, φ (Y i) ^ 2 ∂P = n * ∫ Y, φ (Y ⟨0, hn⟩) ^ 2 ∂P := by
    simp_rw [hsq]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hm1 : (n : ℝ) ^ 2 * Cone ^ 2 ≤ (n : ℝ) ^ 2 * max (Cone ^ 2) Cpair :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hn2
  have hm2 : (n : ℝ) ^ 2 * Cpair ≤ (n : ℝ) ^ 2 * max (Cone ^ 2) Cpair :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hn2
  rw [hEF2, hEF, hdiag]
  rw [abs_le]
  constructor <;> nlinarith

theorem eqbias_sqrt_int_add_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {a b : Ω → ℝ} (ha : MemLp a 2 P) (hb : MemLp b 2 P) :
    Real.sqrt (∫ x, (a x + b x) ^ 2 ∂P) ≤
      Real.sqrt (∫ x, a x ^ 2 ∂P) + Real.sqrt (∫ x, b x ^ 2 ∂P) := by
  have hcs := EF.cs_integral ha hb
  have hA : 0 ≤ ∫ x, a x ^ 2 ∂P := integral_nonneg fun x => sq_nonneg _
  have hB : 0 ≤ ∫ x, b x ^ 2 ∂P := integral_nonneg fun x => sq_nonneg _
  have hab : ∫ x, a x * b x ∂P ≤ Real.sqrt (∫ x, a x ^ 2 ∂P) * Real.sqrt (∫ x, b x ^ 2 ∂P) := by
    rw [← Real.sqrt_mul hA]
    exact Real.le_sqrt_of_sq_le hcs
  have e : ∫ x, (a x + b x) ^ 2 ∂P =
      ∫ x, a x ^ 2 ∂P + 2 * ∫ x, a x * b x ∂P + ∫ x, b x ^ 2 ∂P := by
    have h1 : Integrable (fun x => a x ^ 2) P := ha.integrable_sq
    have h2 : Integrable (fun x => b x ^ 2) P := hb.integrable_sq
    have h3 : Integrable (fun x => a x * b x) P := ha.integrable_mul hb
    have : (fun x => (a x + b x) ^ 2) = fun x => (a x ^ 2 + 2 * (a x * b x)) + b x ^ 2 := by
      funext x; ring
    rw [this]
    have h4 : ∫ x, ((a x ^ 2 + 2 * (a x * b x)) + b x ^ 2) ∂P =
        ∫ x, (a x ^ 2 + 2 * (a x * b x)) ∂P + ∫ x, b x ^ 2 ∂P :=
      integral_add (h1.add (h3.const_mul 2)) h2
    have h5 : ∫ x, (a x ^ 2 + 2 * (a x * b x)) ∂P =
        ∫ x, a x ^ 2 ∂P + ∫ x, 2 * (a x * b x) ∂P := integral_add h1 (h3.const_mul 2)
    rw [h4, h5, integral_const_mul]
  rw [e]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt hA
  have h2 := Real.sq_sqrt hB
  nlinarith [Real.sqrt_nonneg (∫ x, a x ^ 2 ∂P), Real.sqrt_nonneg (∫ x, b x ^ 2 ∂P)]

theorem eqbias_var_mink {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    |Var[fun ω => X ω + Y ω; P] - Var[X; P]| ≤ Var[Y; P] + 2 * Real.sqrt (Var[X; P] * Var[Y; P]) := by
  have hXY : MemLp (fun ω => X ω + Y ω) 2 P := hX.add hY
  have hv : ∀ {Z : Ω → ℝ}, MemLp Z 2 P → Var[Z; P] = ∫ ω, (Z ω - ∫ ω', Z ω' ∂P) ^ 2 ∂P := by
    intro Z hZ
    rw [variance_eq_integral hZ.aemeasurable]
  have hc : ∀ {Z : Ω → ℝ}, MemLp Z 2 P → MemLp (fun ω => Z ω - ∫ ω', Z ω' ∂P) 2 P :=
    fun hZ => hZ.sub (memLp_const _)
  set a := Real.sqrt Var[X; P]
  set b := Real.sqrt Var[Y; P]
  set z := Real.sqrt Var[fun ω => X ω + Y ω; P]
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have haa : a ^ 2 = Var[X; P] := Real.sq_sqrt (variance_nonneg _ _)
  have hbb : b ^ 2 = Var[Y; P] := Real.sq_sqrt (variance_nonneg _ _)
  have hzz : z ^ 2 = Var[fun ω => X ω + Y ω; P] := Real.sq_sqrt (variance_nonneg _ _)
  have hI : ∫ ω, (X ω + Y ω) ∂P = ∫ ω, X ω ∂P + ∫ ω, Y ω ∂P :=
    integral_add (hX.integrable one_le_two) (hY.integrable one_le_two)
  -- Minkowski
  have h1 : z ≤ a + b := by
    have := eqbias_sqrt_int_add_le (hc hX) (hc hY)
    have e : ∫ ω, ((X ω - ∫ ω', X ω' ∂P) + (Y ω - ∫ ω', Y ω' ∂P)) ^ 2 ∂P =
        Var[fun ω => X ω + Y ω; P] := by
      rw [hv hXY, hI]
      exact integral_congr_ae (Eventually.of_forall fun ω => by simp only; ring)
    rw [e, ← hv hX, ← hv hY] at this
    exact this
  have h2 : a ≤ z + b := by
    have hnI : ∫ ω, -Y ω ∂P = -∫ ω, Y ω ∂P := integral_neg _
    have this : Real.sqrt (∫ ω, ((X ω + Y ω - ∫ ω', (X ω' + Y ω') ∂P) +
          (-Y ω - ∫ ω', -Y ω' ∂P)) ^ 2 ∂P) ≤
        Real.sqrt (∫ ω, (X ω + Y ω - ∫ ω', (X ω' + Y ω') ∂P) ^ 2 ∂P) +
          Real.sqrt (∫ ω, (-Y ω - ∫ ω', -Y ω' ∂P) ^ 2 ∂P) :=
      eqbias_sqrt_int_add_le (hc hXY) (hc hY.neg)
    have e : ∫ ω, ((X ω + Y ω - ∫ ω', (X ω' + Y ω') ∂P) + (-Y ω - ∫ ω', -Y ω' ∂P)) ^ 2 ∂P =
        Var[X; P] := by
      rw [hv hX, hnI, hI]
      exact integral_congr_ae (Eventually.of_forall fun ω => by simp only; ring)
    have e2 : ∫ ω, (-Y ω - ∫ ω', -Y ω' ∂P) ^ 2 ∂P = Var[Y; P] := by
      rw [hv hY, hnI]
      exact integral_congr_ae (Eventually.of_forall fun ω => by simp only; ring)
    have e1 : ∫ ω, (X ω + Y ω - ∫ ω', (X ω' + Y ω') ∂P) ^ 2 ∂P =
        Var[fun ω => X ω + Y ω; P] := (hv hXY).symm
    rw [e, e2, e1] at this
    exact this
  have hzab : |z - a| ≤ b := by rw [abs_le]; constructor <;> linarith
  have e3 : Var[fun ω => X ω + Y ω; P] - Var[X; P] = (z - a) * (z + a) := by
    rw [← hzz, ← haa]; ring
  rw [e3, abs_mul]
  have hza : |z + a| ≤ 2 * a + b := by
    rw [abs_of_nonneg (by positivity)]; linarith
  have : |z - a| * |z + a| ≤ b * (2 * a + b) := mul_le_mul hzab hza (abs_nonneg _) hb0
  have e4 : Real.sqrt (Var[X; P] * Var[Y; P]) = a * b := by
    rw [Real.sqrt_mul (variance_nonneg _ _)]
  rw [e4, ← hbb]
  nlinarith

end Main

end HRS

end
