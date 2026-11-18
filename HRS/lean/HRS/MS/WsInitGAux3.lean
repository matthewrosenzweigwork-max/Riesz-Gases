import HRS.MS.WsInitGAux2
import HRS.MS.R2IidPathAux2
import HRS.MS.PoisSgAux2

/-!
# S21 packet G, part 3: the cosine coefficients `f_{n,α} = r2CosOrbitTest` of the orbit in `C_b^J`

* `s21g_cont_iter`: `τ ↦ D^j G(τ)(x)` is continuous on `[0,T]` in the operator norm.
* `s21g_F_memCb`: `x ↦ ∫_0^T e_n(t) G(t)(x) dt` is in `C_b^J` and its derivatives are the integrals of the derivatives
  (`HRS.MS.PoisSg.sg_iteratedFDeriv_integral` with `Ω = [0,T]`).
* `s21g_orbit_cos`: for an orbit `S21GOrbit` and `T > 0`, every `f_{n,α}` is in `C_b^J` and
  `cbNorm J f_{n,α} ≤ (J+1) K a_n b_α` with `∑_n a_n < ∞`; hence `hmem`, `hsum`, `hcont` of the rows `r2_static_observation_path*`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS HRS.Whole

variable {d : ℕ}

/-- Operator-level version of the quotient identity. -/
theorem s21g_iter_quot_op {J j : ℕ} (hj : j ≤ J) {g1 g2 g' : Euc d → ℝ} (h1 : MemCb J g1) (h2 : MemCb J g2)
    (h3 : MemCb J g') (a : ℝ) (x : Euc d) :
    iteratedFDeriv ℝ j (fun y => a * (g1 y - g2 y) - g' y) x =
      a • (iteratedFDeriv ℝ j g1 x - iteratedFDeriv ℝ j g2 x) - iteratedFDeriv ℝ j g' x := by
  have c1 : ContDiffAt ℝ (j : WithTop ℕ∞) g1 x := (h1.1.of_le (by exact_mod_cast hj)).contDiffAt
  have c2 : ContDiffAt ℝ (j : WithTop ℕ∞) g2 x := (h2.1.of_le (by exact_mod_cast hj)).contDiffAt
  have c3 : ContDiffAt ℝ (j : WithTop ℕ∞) g' x := (h3.1.of_le (by exact_mod_cast hj)).contDiffAt
  have e : (fun y => a * (g1 y - g2 y) - g' y) = (a • (g1 - g2)) - g' := by
    funext y; simp [smul_eq_mul]
  have hd : ContDiffAt ℝ (j : WithTop ℕ∞) (g1 - g2) x := c1.sub c2
  have hs : ContDiffAt ℝ (j : WithTop ℕ∞) (a • (g1 - g2)) x := hd.const_smul a
  rw [e, iteratedFDeriv_sub_apply hs c3, iteratedFDeriv_const_smul_apply hd,
    iteratedFDeriv_sub_apply c1 c2]

/-- Continuity in the time parameter (operator norm). -/
theorem s21g_cont_iter {J : ℕ} {T : ℝ} {G G' : ℝ → Euc d → ℝ}
    (hG : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb J (G τ)) (hG' : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb J (G' τ))
    (hD : S21GDiff J T G G') {j : ℕ} (hj : j ≤ J) (x : Euc d) :
    ContinuousOn (fun t => iteratedFDeriv ℝ j (G t) x) (Set.Icc (0 : ℝ) T) := by
  intro τ hτ
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set M : ℝ := ‖iteratedFDeriv ℝ j (G' τ) x‖ + 1 with hM
  have hM0 : 0 < M := by positivity
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := hD τ hτ 1 one_pos
  refine ⟨min δ₁ (ε / M), lt_min hδ₁ (by positivity), fun y hy hdy => ?_⟩
  rw [dist_eq_norm]
  rw [Real.dist_eq] at hdy
  by_cases hyτ : y = τ
  · subst hyτ; simp [hε]
  have hne : y - τ ≠ 0 := sub_ne_zero.2 hyτ
  have hlt1 : |y - τ| < δ₁ := lt_of_lt_of_le hdy (min_le_left _ _)
  have hlt2 : |y - τ| < ε / M := lt_of_lt_of_le hdy (min_le_right _ _)
  have hmem : τ + (y - τ) ∈ Set.Icc (0 : ℝ) T := by rw [add_sub_cancel]; exact hy
  have hb := hδ₁' (y - τ) hne hlt1 hmem j hj x
  rw [add_sub_cancel] at hb
  rw [s21g_iter_quot_op hj (hG y hy) (hG τ hτ) (hG' τ hτ)] at hb
  have h1 : iteratedFDeriv ℝ j (G y) x - iteratedFDeriv ℝ j (G τ) x =
      (y - τ) • ((y - τ)⁻¹ • (iteratedFDeriv ℝ j (G y) x - iteratedFDeriv ℝ j (G τ) x) -
        iteratedFDeriv ℝ j (G' τ) x) + (y - τ) • iteratedFDeriv ℝ j (G' τ) x := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hne, one_smul]; abel
  rw [h1]
  refine (norm_add_le _ _).trans_lt ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs]
  have : |y - τ| * ‖(y - τ)⁻¹ • (iteratedFDeriv ℝ j (G y) x - iteratedFDeriv ℝ j (G τ) x) -
      iteratedFDeriv ℝ j (G' τ) x‖ + |y - τ| * ‖iteratedFDeriv ℝ j (G' τ) x‖ ≤
      |y - τ| * M := by
    rw [hM]; nlinarith [abs_nonneg (y - τ)]
  refine lt_of_le_of_lt this ?_
  calc |y - τ| * M < ε / M * M := mul_lt_mul_of_pos_right hlt2 hM0
    _ = ε := by field_simp

/-- `x ↦ ∫_0^T e_n(t) G(t)(x) dt` is `C_b^J`, with derivatives the integrals of the derivatives. -/
theorem s21g_F_memCb {J : ℕ} {T : ℝ} (hT : 0 < T) (n : ℕ) {G : ℝ → Euc d → ℝ}
    (hG : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb J (G τ)) {Mg : ℝ}
    (hM : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j (G τ) x‖ ≤ Mg)
    (hcont : ∀ j ≤ J, ∀ x, ContinuousOn (fun t => iteratedFDeriv ℝ j (G t) x) (Set.Icc (0 : ℝ) T)) :
    MemCb J (fun x => ∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T n t * G t x) ∧
      ∀ j ≤ J, ∀ (x : Euc d) (v : Fin j → Euc d),
        iteratedFDeriv ℝ j (fun x => ∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T n t * G t x) x v =
          ∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T n t * iteratedFDeriv ℝ j (G t) x v := by
  classical
  have : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) := Real.isFiniteMeasure_restrict_Icc 0 T
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  have hMg : 0 ≤ Mg := by
    have := hM 0 ⟨le_rfl, hT.le⟩ 0 (Nat.zero_le _) 0
    exact (norm_nonneg _).trans this
  set Gt : ℝ → Euc d → ℝ := fun t x => if t ∈ Set.Icc (0 : ℝ) T then r2CosBasis T n t * G t x else 0 with hGt
  set Fx : Euc d → ℝ := fun x => ∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T n t * G t x with hFx
  have hGin : ∀ q ∈ Set.Icc (0 : ℝ) T, Gt q = r2CosBasis T n q • G q := by
    intro q h
    funext x
    show (if q ∈ Set.Icc (0 : ℝ) T then r2CosBasis T n q * G q x else 0) = r2CosBasis T n q * G q x
    rw [if_pos h]
  have hGout : ∀ q ∉ Set.Icc (0 : ℝ) T, Gt q = fun _ => 0 := by
    intro q h
    funext x
    show (if q ∈ Set.Icc (0 : ℝ) T then r2CosBasis T n q * G q x else 0) = 0
    rw [if_neg h]
  have hcd : ∀ q, ContDiff ℝ (J : WithTop ℕ∞) (Gt q) := by
    intro q
    by_cases h : q ∈ Set.Icc (0 : ℝ) T
    · rw [hGin q h]; exact (hG q h).1.const_smul (r2CosBasis T n q)
    · rw [hGout q h]; exact contDiff_const
  have hit : ∀ i ≤ J, ∀ q ∈ Set.Icc (0 : ℝ) T, ∀ x,
      iteratedFDeriv ℝ i (Gt q) x = r2CosBasis T n q • iteratedFDeriv ℝ i (G q) x := by
    intro i hi q h x
    rw [hGin q h]
    exact iteratedFDeriv_const_smul_apply ((hG q h).1.of_le (by exact_mod_cast hi)).contDiffAt
  have hit0 : ∀ i, ∀ q ∉ Set.Icc (0 : ℝ) T, ∀ x, iteratedFDeriv ℝ i (Gt q) x = 0 := by
    intro i q h x
    rw [hGout q h, iteratedFDeriv_fun_zero]; rfl
  have hbd : ∀ i ≤ J, ∃ M : ℝ, ∀ (q : ℝ) (x : Euc d), ‖iteratedFDeriv ℝ i (Gt q) x‖ ≤ M := by
    intro i hi
    refine ⟨Real.sqrt (2 / T) * Mg, fun q x => ?_⟩
    by_cases h : q ∈ Set.Icc (0 : ℝ) T
    · rw [hit i hi q h x, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (s11p_cos_bound hT n q) (hM q h i hi x) (norm_nonneg _) (Real.sqrt_nonneg _)
    · rw [hit0 i q h x, norm_zero]; positivity
  have hmeas : ∀ i ≤ J, ∀ x : Euc d,
      AEStronglyMeasurable (fun q => iteratedFDeriv ℝ i (Gt q) x) μ := by
    intro i hi x
    have h1 : ContinuousOn (fun q => r2CosBasis T n q • iteratedFDeriv ℝ i (G q) x) (Set.Icc (0 : ℝ) T) :=
      (s11p_cos_continuous T n).continuousOn.smul (hcont i hi x)
    have h2 := h1.aestronglyMeasurable (μ := volume) measurableSet_Icc
    refine h2.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with q hq
    rw [hit i hi q hq x]
  obtain ⟨hCD, hDeriv⟩ := HRS.MS.PoisSg.sg_iteratedFDeriv_integral (μ := μ) Gt J hcd hbd hmeas
  have hFeq : Fx = fun x => ∫ q, Gt q x ∂μ := by
    funext x
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with q hq
    show r2CosBasis T n q * G q x = Gt q x
    rw [hGin q hq]; rfl
  have hCD' : ContDiff ℝ (J : WithTop ℕ∞) Fx := by rw [hFeq]; exact hCD
  have hDeriv' : ∀ i ≤ J, ∀ x, iteratedFDeriv ℝ i Fx x = ∫ q, iteratedFDeriv ℝ i (Gt q) x ∂μ := by
    intro i hi x; rw [hFeq]; exact hDeriv i hi x
  have hint : ∀ i ≤ J, ∀ x, Integrable (fun q => iteratedFDeriv ℝ i (Gt q) x) μ := by
    intro i hi x
    obtain ⟨M, hM'⟩ := hbd i hi
    exact Integrable.of_bound (hmeas i hi x) M (Filter.Eventually.of_forall fun q => hM' q x)
  refine ⟨⟨hCD', fun i hi => ?_⟩, fun j hj x v => ?_⟩
  · obtain ⟨M, hM'⟩ := hbd i hi
    refine ⟨M * μ.real Set.univ, ?_⟩
    rintro _ ⟨x, rfl⟩
    show ‖iteratedFDeriv ℝ i Fx x‖ ≤ _
    rw [hDeriv' i hi x]
    exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun q => hM' q x)
  · show iteratedFDeriv ℝ j Fx x v = _
    rw [hDeriv' j hj x]
    have := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ v).integral_comp_comm (hint j hj x)
    simp only [ContinuousMultilinearMap.apply_apply] at this
    rw [← this]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with q hq
    rw [hit j hj q hq x]
    simp

end HRS.MS.S21
