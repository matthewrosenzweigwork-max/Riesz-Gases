import HRS.MS.R26T8AG00
import HRS.MS.R26T8AB07a1

/-!
# S8.2 observed-time layer, packet T8A.B07a: source envelope for the centered pair forcing

`scalarForcing = (√N/2) (g - ∫ g dP)` with `g = centeredPairFunctional (hSource f) · ν`.  Off collisions
`|g X| ≤ A (2s + 3C₀) · env X` (pair terms by the commutator-kernel bound of O00c, the two integral terms by B07a1),
where `env = configPoleEnvelope s ≥ 1` dominates every pair factor `1 + |X_i - X_j|^{-s}`; the centering constant is
bounded by the same envelope integrated against the probability measure (G00 gives the square integrability).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_b07a_explicit (d N : ℕ) (hd : 2≤d) (hN : 2≤N)
    (a beta : ℝ) (ha : 0<a) (hbeta : 0<beta) (rho : Euc d → ℝ)
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) :
    ∃ c K : ℝ, 0 ≤ c ∧ 0 ≤ K ∧
      Measurable (r26t8a_configPoleEnvelope (d := d) (N := N) (criticalS d)) ∧
      (∀ X : EucConfig d N, 1 ≤ r26t8a_configPoleEnvelope (d := d) (N := N) (criticalS d) X) ∧
      MemLp (r26t8a_configPoleEnvelope (d := d) (N := N) (criticalS d)) 2 (canonicalP d N a beta) ∧
      ∀ f : Euc d → ℝ, ∀ A : ℝ, 0≤A → TestBound (testOrder d) A f →
        (∀ X ∉ eucCollisionSet d N,
          |centeredPairFunctional (hSource f) X (HRS.Whole.withDensityReal rho)| ≤
            A * c * r26t8a_configPoleEnvelope (d := d) (N := N) (criticalS d) X) ∧
        ∀ X ∉ eucCollisionSet d N, |scalarForcing a beta rho f X| ≤
          A * (K * r26t8a_configPoleEnvelope (d := d) (N := N) (criticalS d) X) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hs0 : 0 < criticalS d := HRS.MS.S82R.s82r_criticalS_pos hd1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨C0, hC0, hCb⟩ := r26t8a_b07a1_int_bound d hd a beta ha hbeta
  obtain ⟨hprob, hbnd⟩ := hCb rho hrho
  haveI hP : IsProbabilityMeasure (canonicalP d N a beta) := HRS.MS.S82U.u4_prob (N := N) hd ha hbeta
  have hG := r26t8a_gibbs_pole_moments d N hd hN a beta ha hbeta (criticalS d) hs0.le
  set s := criticalS d with hs
  set env : EucConfig d N → ℝ := r26t8a_configPoleEnvelope (d := d) (N := N) s with henvdef
  have henvU : ∀ X : EucConfig d N, env X = (1 + ‖X‖) ^ s *
      ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-s)) := fun X => rfl
  have hone : ∀ {ι : Type} (t : Finset ι) (g : ι → ℝ), (∀ i ∈ t, 1 ≤ g i) → 1 ≤ ∏ i ∈ t, g i := by
    intro ι t g h
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      rw [Finset.prod_insert ha]
      have h1 := h a (Finset.mem_insert_self a t)
      have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      nlinarith
  have hsingle : ∀ {ι : Type} (t : Finset ι) (g : ι → ℝ), (∀ i ∈ t, 1 ≤ g i) → ∀ j ∈ t,
      g j ≤ ∏ i ∈ t, g i := by
    intro ι t g h j hj
    rw [← Finset.mul_prod_erase t g hj]
    have h1 : 1 ≤ ∏ i ∈ t.erase j, g i := hone _ _ fun i hi => h i (Finset.mem_of_mem_erase hi)
    have h2 : 0 ≤ g j := by linarith [h j hj]
    nlinarith
  have hq : ∀ (X : EucConfig d N) (i j : Fin N), 1 ≤ 1 + ‖X i - X j‖ ^ (-s) := fun X i j => by
    have := Real.rpow_nonneg (norm_nonneg (X i - X j)) (-s)
    linarith
  have hprod1 : ∀ (X : EucConfig d N) (i : Fin N),
      1 ≤ ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-s)) := fun X i =>
    hone _ _ fun j _ => hq X i j
  have hpow1 : ∀ X : EucConfig d N, 1 ≤ (1 + ‖X‖) ^ s := fun X =>
    Real.one_le_rpow (by linarith [norm_nonneg X]) hs0.le
  have henv1 : ∀ X : EucConfig d N, 1 ≤ env X := fun X => by
    rw [henvU]
    have h2 : 1 ≤ ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-s)) :=
      hone _ _ fun i _ => hprod1 X i
    nlinarith [hpow1 X]
  have hpair : ∀ (X : EucConfig d N) (i j : Fin N), j ≠ i → 1 + ‖X i - X j‖ ^ (-s) ≤ env X := by
    intro X i j hji
    rw [henvU]
    have h1 : 1 + ‖X i - X j‖ ^ (-s) ≤ ∏ j' ∈ Finset.univ.erase i, (1 + ‖X i - X j'‖ ^ (-s)) :=
      hsingle _ (fun j' => 1 + ‖X i - X j'‖ ^ (-s)) (fun j' _ => hq X i j')
        j (Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩)
    have h2 : ∏ j' ∈ Finset.univ.erase i, (1 + ‖X i - X j'‖ ^ (-s)) ≤
        ∏ i', ∏ j' ∈ Finset.univ.erase i', (1 + ‖X i' - X j'‖ ^ (-s)) :=
      hsingle _ (fun i' => ∏ j' ∈ Finset.univ.erase i', (1 + ‖X i' - X j'‖ ^ (-s)))
        (fun i' _ => hprod1 X i') i (Finset.mem_univ i)
    have h3 := hpow1 X
    have h4 : 0 ≤ 1 + ‖X i - X j‖ ^ (-s) := by linarith [hq X i j]
    nlinarith
  -- the pointwise bound of the centered pair functional
  set c : ℝ := 2 * s + 3 * C0 with hc
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  have hkey : ∀ f : Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → TestBound (testOrder d) A f →
      ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      |centeredPairFunctional (hSource f) X (HRS.Whole.withDensityReal rho)| ≤ A * c * env X := by
    intro f A hA hT X _
    have hf : ContDiff ℝ ∞ f := hT.1
    have h1 : ∀ y, ‖iteratedFDeriv ℝ 1 f y‖ ≤ A := fun y => hT.2 1 le_rfl (by unfold testOrder; omega) y
    have h2 : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ A :=
      fun y => hT.2 2 (by norm_num) (by unfold testOrder; omega) y
    have hpt : ∀ i j : Fin N, j ≠ i → |hSource f (X i) (X j)| ≤ 2 * A * s * env X := by
      intro i j hji
      have h := r26t8a_o00c_pt hs0 f hf A hA h1 h2 (X i) (X j)
      have hind : (Metric.ball (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (-s)) (X i - X j) ≤
          ‖X i - X j‖ ^ (-s) := by
        by_cases hb : X i - X j ∈ Metric.ball (0 : Euc d) 1
        · rw [Set.indicator_of_mem hb]
        · rw [Set.indicator_of_notMem hb]
          exact Real.rpow_nonneg (norm_nonneg _) _
      have hAs : 0 ≤ A * s := mul_nonneg hA hs0.le
      have hnn := Real.rpow_nonneg (norm_nonneg (X i - X j)) (-s)
      have hp := hpair X i j hji
      calc |hSource f (X i) (X j)| = ‖commutatorKernel d s (gradient f) (X i) (X j)‖ := by
            rw [Real.norm_eq_abs]; rfl
        _ ≤ A * s * ((Metric.ball (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (-s)) (X i - X j) + 2) := h
        _ ≤ A * s * (‖X i - X j‖ ^ (-s) + 2) := by gcongr
        _ ≤ A * s * (2 * (1 + ‖X i - X j‖ ^ (-s))) := by gcongr; linarith
        _ ≤ A * s * (2 * env X) := by gcongr
        _ = 2 * A * s * env X := by ring
    have hsum1 : |∑ i, ∑ j ∈ Finset.univ.erase i, hSource f (X i) (X j)| ≤
        (N : ℝ) * N * (2 * A * s * env X) := by
      have hB : 0 ≤ 2 * A * s * env X := by
        have h0 : 0 ≤ env X := by linarith [henv1 X]
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) hs0.le) h0
      calc |∑ i, ∑ j ∈ Finset.univ.erase i, hSource f (X i) (X j)|
          ≤ ∑ i, |∑ j ∈ Finset.univ.erase i, hSource f (X i) (X j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, |hSource f (X i) (X j)| :=
            Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, (2 * A * s * env X) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj =>
              hpt i j (Finset.mem_erase.1 hj).1
        _ ≤ ∑ i : Fin N, ∑ j : Fin N, (2 * A * s * env X) :=
            Finset.sum_le_sum fun i _ =>
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun _ _ _ => hB
        _ = (N : ℝ) * N * (2 * A * s * env X) := by simp [Finset.sum_const, Finset.card_univ]; ring
    have hint : ∀ x : Euc d, |∫ y, hSource f x y ∂(HRS.Whole.withDensityReal rho)| ≤ A * C0 := fun x => by
      have := hbnd f A hA hT x
      rw [Real.norm_eq_abs] at this
      exact this
    have hsum2 : |∑ i, ∫ y, hSource f (X i) y ∂(HRS.Whole.withDensityReal rho)| ≤ N * (A * C0) := by
      calc _ ≤ ∑ i, |∫ y, hSource f (X i) y ∂(HRS.Whole.withDensityReal rho)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin N, (A * C0) := Finset.sum_le_sum fun i _ => hint _
        _ = N * (A * C0) := by simp
    have hdbl : |∫ x, ∫ y, hSource f x y ∂(HRS.Whole.withDensityReal rho)
        ∂(HRS.Whole.withDensityReal rho)| ≤ A * C0 := by
      have := norm_integral_le_of_norm_le_const (μ := HRS.Whole.withDensityReal rho)
        (f := fun x => ∫ y, hSource f x y ∂(HRS.Whole.withDensityReal rho)) (C := A * C0)
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hint x)
      simpa [Real.norm_eq_abs] using this
    unfold centeredPairFunctional
    have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    have e1 : |1 / (N : ℝ) ^ 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, hSource f (X i) (X j)| ≤
        2 * A * s * env X := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (N : ℝ) ^ 2)]
      calc 1 / (N : ℝ) ^ 2 * |∑ i, ∑ j ∈ Finset.univ.erase i, hSource f (X i) (X j)|
          ≤ 1 / (N : ℝ) ^ 2 * ((N : ℝ) * N * (2 * A * s * env X)) := by gcongr
        _ = 2 * A * s * env X := by field_simp
    have e2 : |2 * (1 / (N : ℝ) * ∑ i, ∫ y, hSource f (X i) y ∂(HRS.Whole.withDensityReal rho))| ≤
        2 * (A * C0) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul, abs_of_pos (by positivity : 0 < 1 / (N : ℝ))]
      have : 1 / (N : ℝ) * |∑ i, ∫ y, hSource f (X i) y ∂(HRS.Whole.withDensityReal rho)| ≤
          1 / (N : ℝ) * (N * (A * C0)) := by gcongr
      have e : 1 / (N : ℝ) * (N * (A * C0)) = A * C0 := by field_simp
      linarith
    have henvX := henv1 X
    have hAC : 0 ≤ A * C0 := mul_nonneg hA hC0
    have hAs : 0 ≤ A * s := mul_nonneg hA hs0.le
    calc _ ≤ |1 / (N : ℝ) ^ 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, hSource f (X i) (X j) -
          2 * (1 / (N : ℝ) * ∑ i, ∫ y, hSource f (X i) y ∂(HRS.Whole.withDensityReal rho))| +
          |∫ x, ∫ y, hSource f x y ∂(HRS.Whole.withDensityReal rho) ∂(HRS.Whole.withDensityReal rho)| :=
            abs_add_le _ _
      _ ≤ (|1 / (N : ℝ) ^ 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, hSource f (X i) (X j)| +
          |2 * (1 / (N : ℝ) * ∑ i, ∫ y, hSource f (X i) y ∂(HRS.Whole.withDensityReal rho))|) +
          |∫ x, ∫ y, hSource f x y ∂(HRS.Whole.withDensityReal rho) ∂(HRS.Whole.withDensityReal rho)| := by
            gcongr; exact abs_sub _ _
      _ ≤ (2 * A * s * env X + 2 * (A * C0)) + A * C0 := by gcongr
      _ ≤ A * c * env X := by
        rw [hc]
        nlinarith [mul_nonneg hAC (sub_nonneg.2 henvX), mul_nonneg hAs (sub_nonneg.2 henvX)]
  -- the centering constant
  have hint_env : Integrable env (canonicalP d N a beta) := hG.1.integrable one_le_two
  have hnull : ∀ᵐ X ∂(canonicalP d N a beta), X ∉ eucCollisionSet d N := by
    rw [ae_iff]; simpa using hG.2
  set I : ℝ := ∫ X, env X ∂(canonicalP d N a beta) with hI
  have hI0 : 0 ≤ I := integral_nonneg fun X => le_trans zero_le_one (henv1 X)
  have hmeasE : Measurable env := by
    rw [show env = fun X : EucConfig d N => (1 + ‖X‖) ^ s *
      ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-s)) from funext henvU]
    refine ((measurable_const.add measurable_norm).pow_const s).mul ?_
    refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
    exact measurable_const.add
      (((measurable_pi_apply i).sub (measurable_pi_apply j)).norm.pow_const (-s))
  refine ⟨c, (Real.sqrt N / 2) * (c * (1 + I)), hc0,
    mul_nonneg (by positivity) (mul_nonneg hc0 (by linarith)), hmeasE, henv1, hG.1,
    fun f A hA hT => ⟨fun X hX => hkey f A hA hT X hX, ?_⟩⟩
  · intro X hX
    have hgX := hkey f A hA hT X hX
    have hgint : |∫ Y, centeredPairFunctional (hSource f) Y (HRS.Whole.withDensityReal rho)
        ∂(canonicalP d N a beta)| ≤ A * c * I := by
      have := norm_integral_le_of_norm_le (hint_env.const_mul (A * c))
        (f := fun Y => centeredPairFunctional (hSource f) Y (HRS.Whole.withDensityReal rho))
        (hnull.mono fun Y hY => by rw [Real.norm_eq_abs]; exact hkey f A hA hT Y hY)
      rw [integral_const_mul, Real.norm_eq_abs] at this
      exact this
    have e : scalarForcing a beta rho f X = (Real.sqrt N / 2) *
        (centeredPairFunctional (hSource f) X (HRS.Whole.withDensityReal rho) -
          ∫ Y, centeredPairFunctional (hSource f) Y (HRS.Whole.withDensityReal rho)
            ∂(canonicalP d N a beta)) := rfl
    rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt N / 2)]
    have h1 : |centeredPairFunctional (hSource f) X (HRS.Whole.withDensityReal rho) -
        ∫ Y, centeredPairFunctional (hSource f) Y (HRS.Whole.withDensityReal rho)
          ∂(canonicalP d N a beta)| ≤ A * c * env X + A * c * I :=
      (abs_sub _ _).trans (add_le_add hgX hgint)
    have henvX := henv1 X
    have hAc : 0 ≤ A * c := mul_nonneg hA hc0
    calc Real.sqrt N / 2 * |_| ≤ Real.sqrt N / 2 * (A * c * env X + A * c * I) := by gcongr
      _ ≤ A * ((Real.sqrt N / 2) * (c * (1 + I)) * env X) := by
        have : A * c * I ≤ A * c * I * env X := by nlinarith [mul_nonneg hAc hI0]
        have h3 : 0 ≤ Real.sqrt N / 2 := by positivity
        nlinarith [mul_nonneg h3 (mul_nonneg hAc hI0), mul_nonneg h3 (mul_nonneg hAc (sub_nonneg.2 henvX)),
          mul_nonneg h3 (mul_nonneg (mul_nonneg hAc hI0) (sub_nonneg.2 henvX))]

theorem r26t8a_source_envelope (d N : ℕ) (hd : 2≤d) (hN : 2≤N)
    (a beta : ℝ) (ha : 0<a) (hbeta : 0<beta) (rho : Euc d → ℝ)
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) :
    ∃ E : EucConfig d N → ℝ, Measurable E ∧ (∀ X, 0≤E X) ∧ MemLp E 2 (canonicalP d N a beta) ∧
      ∀ f : Euc d → ℝ, ∀ A : ℝ, 0≤A → TestBound (testOrder d) A f →
        ∀ X∉eucCollisionSet d N, |scalarForcing a beta rho f X|≤A*E X := by
  obtain ⟨c, K, hc, hK, hm, h1, hL2, h⟩ := r26t8a_b07a_explicit d N hd hN a beta ha hbeta rho hrho
  refine ⟨fun X => K * r26t8a_configPoleEnvelope (d := d) (N := N) (criticalS d) X,
    measurable_const.mul hm, fun X => mul_nonneg hK (by linarith [h1 X]), hL2.const_mul _, ?_⟩
  intro f A hA hT X hX
  exact (h f A hA hT).2 X hX

end HRS.MS.R26T8A

end
