import HRS.MC.CepH2Aux11

/-!
# CEPH2, helper 12: integration by parts for the mollified generator

`∫_cell φ(x) ∫ A(x,y) dμ(y) dx = - ∫_cell ∫ B_φ(x,y) dμ(y) dx` for `φ ∈ C¹` periodic with transversally bounded
support, where `A` is the generator integrand and `B_φ` its integrated-by-parts form.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

/-- Coordinate direction. -/
def h2_e (k : Fin N) : Ch N := EuclideanSpace.single k 1

theorem h2_norm_e (k : Fin N) : ‖h2_e k‖ = 1 := by simp [h2_e]

/-- Generator integrand: `θ Δ_x Ĝ(x-y) + ⟨∇U(y), ∇_x Ĝ(x-y)⟩`. -/
def h2_A (θ v : ℝ) (U : Ch N → ℝ) (x y : Ch N) : ℝ :=
  θ * ∑ k, h2_per2 v (x - y) (h2_e k) (h2_e k) + h2_per1 v (x - y) (gradient U y)

/-- Integrated-by-parts integrand. -/
def h2_B (θ v : ℝ) (U : Ch N → ℝ) (φ : Ch N → ℝ) (x y : Ch N) : ℝ :=
  θ * ∑ k, fderiv ℝ φ x (h2_e k) * h2_per1 v (x - y) (h2_e k) + fderiv ℝ φ x (gradient U y) * h2_per v (x - y)

theorem h2_bdd_of_far {φ : Ch N → ℝ} (hφ : ContDiff ℝ 1 φ) (hper : ∀ x, φ (x + cep_diag N) = φ x) {R : ℝ}
    (hR : ∀ x, R < ‖h2_perp x‖ → φ x = 0) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |φ x| ≤ C ∧ ‖fderiv ℝ φ x‖ ≤ C := by
  obtain ⟨C1, hC1⟩ := h2_bdd_tube hφ.continuous hper R
  obtain ⟨C2, hC2⟩ := h2_bdd_tube (hφ.continuous_fderiv (by simp)) (fun x => h2_fderiv_periodic hper x) R
  refine ⟨max |C1| |C2|, le_max_of_le_left (abs_nonneg _), fun x => ?_⟩
  by_cases hx : ‖h2_perp x‖ ≤ R
  · exact ⟨((hC1 x hx).trans (le_abs_self _)).trans (le_max_left _ _) |> fun h => by simpa using h,
      ((hC2 x hx).trans (le_abs_self _)).trans (le_max_right _ _)⟩
  · rw [hR x (not_le.1 hx), h2_fderiv_eq_zero_of_far hR (not_le.1 hx)]
    simp [le_max_of_le_left (abs_nonneg _)]

theorem h2_integrable_prod_tube {μ : Measure (Ch N)} [IsFiniteMeasure μ] {H : Ch N → Ch N → ℝ}
    (hH : Continuous (Function.uncurry H)) {R C : ℝ} (hsupp : ∀ x y, R < ‖h2_perp x‖ → H x y = 0)
    {G : Ch N → ℝ} (hG : Integrable G μ) (hbd : ∀ x y, |H x y| ≤ C * |G y|) :
    Integrable (Function.uncurry H) ((volume.restrict (cep_cell N)).prod μ) := by
  have hf := h2_integrable_tube_indicator (N := N) R |C|
  have hb := hf.mul_prod hG.abs
  refine Integrable.mono' hb hH.aestronglyMeasurable (ae_of_all _ fun z => ?_)
  rcases z with ⟨x, y⟩
  by_cases hx : ‖h2_perp x‖ ≤ R
  · simp only [Function.uncurry_apply_pair, Set.indicator_of_mem (show x ∈ {x : Ch N | ‖h2_perp x‖ ≤ R} from hx)]
    rw [Real.norm_eq_abs]
    exact (hbd x y).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg _))
  · have h0 : H x y = 0 := hsupp x y (not_le.1 hx)
    simp only [Function.uncurry_apply_pair, h0, norm_zero]
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => abs_nonneg C) x) (abs_nonneg _)

theorem h2_continuous_gradient {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) : Continuous (gradient U) := by
  have : gradient U = fun x => (InnerProductSpace.toDual ℝ (Ch N)).symm (fderiv ℝ U x) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (Ch N)).symm.continuous.comp (hU.continuous_fderiv (by simp))

theorem h2_per2_sub_periodic (v : ℝ) (y x : Ch N) : h2_per2 v (x + cep_diag N - y) = h2_per2 v (x - y) := by
  rw [add_sub_right_comm]; exact h2_per2_periodic v _

theorem h2_integrable_mul_far {a b : Ch N → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hpa : ∀ x, a (x + cep_diag N) = a x) (hpb : ∀ x, b (x + cep_diag N) = b x) {R : ℝ}
    (hRa : ∀ x, R < ‖h2_perp x‖ → a x = 0) : Integrable (fun x => a x * b x) (volume.restrict (cep_cell N)) :=
  h2_integrable_cell_of_far (ha.mul hb) (fun x => by simp only [hpa, hpb]) (R := R)
    (fun x hx => by simp [hRa x hx])

theorem h2_cell_ibp_single {v : ℝ} (hv : 0 < v) {φ : Ch N → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hper : ∀ x, φ (x + cep_diag N) = φ x) {R : ℝ} (hR : ∀ x, R < ‖h2_perp x‖ → φ x = 0) (y : Ch N)
    (θ : ℝ) (U : Ch N → ℝ) (hU : ContDiff ℝ 1 U) :
    ∫ x in cep_cell N, φ x * h2_A θ v U x y = - ∫ x in cep_cell N, h2_B θ v U φ x y := by
  have hφc : Continuous φ := hφ.continuous
  have hdφ : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hdR : ∀ x, R < ‖h2_perp x‖ → fderiv ℝ φ x = 0 := fun x hx => h2_fderiv_eq_zero_of_far hR hx
  have hper2c : Continuous (h2_per2 (N := N) v) := h2_continuous_per2 hv
  have hper1c : Continuous (h2_per1 (N := N) v) := h2_continuous_per1 hv
  have hperc : Continuous (h2_per (N := N) v) := h2_continuous_per hv
  have hsub : Continuous fun x : Ch N => x - y := continuous_id.sub continuous_const
  -- integrability of the pieces
  have I1 : ∀ k : Fin N, Integrable (fun x => φ x * h2_per2 v (x - y) (h2_e k) (h2_e k)) (volume.restrict (cep_cell N)) :=
    fun k => h2_integrable_mul_far hφc (((hper2c.comp hsub).clm_apply continuous_const).clm_apply continuous_const)
      hper (fun x => by simp only [h2_per2_sub_periodic]) hR
  have I2 : ∀ k : Fin N, Integrable (fun x => fderiv ℝ φ x (h2_e k) * h2_per1 v (x - y) (h2_e k))
      (volume.restrict (cep_cell N)) :=
    fun k => h2_integrable_mul_far (hdφ.clm_apply continuous_const) ((hper1c.comp hsub).clm_apply continuous_const)
      (fun x => by simp only [h2_fderiv_periodic hper]) (fun x => by simp only [h2_per1_sub_periodic]) (R := R)
      (fun x hx => by simp [hdR x hx])
  have I3 : Integrable (fun x => φ x * h2_per1 v (x - y) (gradient U y)) (volume.restrict (cep_cell N)) :=
    h2_integrable_mul_far hφc ((hper1c.comp hsub).clm_apply continuous_const) hper
      (fun x => by simp only [h2_per1_sub_periodic]) hR
  have I4 : Integrable (fun x => fderiv ℝ φ x (gradient U y) * h2_per v (x - y)) (volume.restrict (cep_cell N)) :=
    h2_integrable_mul_far (hdφ.clm_apply continuous_const) (hperc.comp hsub)
      (fun x => by simp only [h2_fderiv_periodic hper]) (fun x => by simp only [h2_per_sub_periodic]) (R := R)
      (fun x hx => by simp [hdR x hx])
  have E1 : ∀ k : Fin N, ∫ x in cep_cell N, φ x * h2_per2 v (x - y) (h2_e k) (h2_e k) =
      - ∫ x in cep_cell N, fderiv ℝ φ x (h2_e k) * h2_per1 v (x - y) (h2_e k) := by
    intro k
    have := h2_kernel_ibp2 hv hφ hper hR y (h2_e k) (h2_e k)
    rw [integral_add (I2 k) (I1 k)] at this
    linarith
  have E2 : ∫ x in cep_cell N, φ x * h2_per1 v (x - y) (gradient U y) =
      - ∫ x in cep_cell N, fderiv ℝ φ x (gradient U y) * h2_per v (x - y) := by
    have := h2_kernel_ibp1 hv hφ hper hR y (gradient U y)
    rw [integral_add I4 I3] at this
    linarith
  have hA : ∀ x, φ x * h2_A θ v U x y =
      θ * ∑ k, φ x * h2_per2 v (x - y) (h2_e k) (h2_e k) + φ x * h2_per1 v (x - y) (gradient U y) := by
    intro x; unfold h2_A; rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1; refine Finset.sum_congr rfl fun k _ => by ring
  have hB : ∀ x, h2_B θ v U φ x y =
      θ * ∑ k, fderiv ℝ φ x (h2_e k) * h2_per1 v (x - y) (h2_e k) + fderiv ℝ φ x (gradient U y) * h2_per v (x - y) :=
    fun x => rfl
  have L : ∫ x in cep_cell N, φ x * h2_A θ v U x y =
      θ * ∑ k, (∫ x in cep_cell N, φ x * h2_per2 v (x - y) (h2_e k) (h2_e k)) +
        ∫ x in cep_cell N, φ x * h2_per1 v (x - y) (gradient U y) := by
    simp_rw [hA]
    rw [integral_add ((integrable_finset_sum _ fun k _ => I1 k).const_mul θ) I3, integral_const_mul,
      integral_finset_sum _ fun k _ => I1 k]
  have Rr : ∫ x in cep_cell N, h2_B θ v U φ x y =
      θ * ∑ k, (∫ x in cep_cell N, fderiv ℝ φ x (h2_e k) * h2_per1 v (x - y) (h2_e k)) +
        ∫ x in cep_cell N, fderiv ℝ φ x (gradient U y) * h2_per v (x - y) := by
    simp_rw [hB]
    rw [integral_add ((integrable_finset_sum _ fun k _ => I2 k).const_mul θ) I4, integral_const_mul,
      integral_finset_sum _ fun k _ => I2 k]
  rw [L, Rr]
  simp_rw [E1, E2]
  rw [Finset.sum_neg_distrib]
  ring

theorem h2_ibp_mollified {θ v : ℝ} (hv : 0 < v) {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) {μ : Measure (Ch N)}
    [IsFiniteMeasure μ] (hGU : Integrable (fun y => ‖gradient U y‖) μ) {φ : Ch N → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hper : ∀ x, φ (x + cep_diag N) = φ x) {R : ℝ} (hR : ∀ x, R < ‖h2_perp x‖ → φ x = 0) :
    ∫ x in cep_cell N, φ x * (∫ y, h2_A θ v U x y ∂μ) = - ∫ x in cep_cell N, ∫ y, h2_B θ v U φ x y ∂μ := by
  obtain ⟨B, hB0, hB⟩ := h2_per_le (N := N) hv
  obtain ⟨Cφ, hCφ0, hCφ⟩ := h2_bdd_of_far hφ hper hR
  have hgc := h2_continuous_gradient hU
  have hper2c : Continuous (h2_per2 (N := N) v) := h2_continuous_per2 hv
  have hper1c : Continuous (h2_per1 (N := N) v) := h2_continuous_per1 hv
  have hperc : Continuous (h2_per (N := N) v) := h2_continuous_per hv
  have hdφ : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hsub : Continuous fun z : Ch N × Ch N => z.1 - z.2 := continuous_fst.sub continuous_snd
  have hG : Integrable (fun y => 1 + ‖gradient U y‖) μ := (integrable_const 1).add hGU
  -- continuity
  have cA : Continuous (Function.uncurry fun x y => h2_A θ v U x y) := by
    unfold h2_A
    refine Continuous.add (continuous_const.mul (continuous_finset_sum _ fun k _ => ?_)) ?_
    · exact ((hper2c.comp hsub).clm_apply continuous_const).clm_apply continuous_const
    · exact (hper1c.comp hsub).clm_apply (hgc.comp continuous_snd)
  have cB : Continuous (Function.uncurry fun x y => h2_B θ v U φ x y) := by
    unfold h2_B
    refine Continuous.add (continuous_const.mul (continuous_finset_sum _ fun k _ => ?_)) ?_
    · exact ((hdφ.comp continuous_fst).clm_apply continuous_const).mul ((hper1c.comp hsub).clm_apply continuous_const)
    · exact ((hdφ.comp continuous_fst).clm_apply (hgc.comp continuous_snd)).mul (hperc.comp hsub)
  -- bounds
  have bA : ∀ x y, |φ x * h2_A θ v U x y| ≤ (Cφ * (|θ| * N * B + B)) * |1 + ‖gradient U y‖| := by
    intro x y
    have h1 : |h2_A θ v U x y| ≤ |θ| * (N * B) + B * ‖gradient U y‖ := by
      unfold h2_A
      refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
      · rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ k, |h2_per2 v (x - y) (h2_e k) (h2_e k)| ≤ ∑ _k : Fin N, B := by
              refine Finset.sum_le_sum fun k _ => ?_
              rw [← Real.norm_eq_abs]
              calc ‖h2_per2 v (x - y) (h2_e k) (h2_e k)‖ ≤ ‖h2_per2 v (x - y)‖ * ‖h2_e k‖ * ‖h2_e k‖ :=
                    ContinuousLinearMap.le_opNorm₂ _ _ _
                _ ≤ B := by rw [h2_norm_e]; simpa using (hB _).2.2
          _ = N * B := by simp
      · rw [← Real.norm_eq_abs]
        calc ‖h2_per1 v (x - y) (gradient U y)‖ ≤ ‖h2_per1 v (x - y)‖ * ‖gradient U y‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ B * ‖gradient U y‖ := mul_le_mul_of_nonneg_right (hB _).2.1 (norm_nonneg _)
    rw [abs_mul]
    have hpos : 0 ≤ 1 + ‖gradient U y‖ := by positivity
    rw [abs_of_nonneg hpos]
    calc |φ x| * |h2_A θ v U x y| ≤ Cφ * (|θ| * (N * B) + B * ‖gradient U y‖) :=
          mul_le_mul (hCφ x).1 h1 (abs_nonneg _) hCφ0
      _ ≤ _ := by
          have : 0 ≤ |θ| * N * B := by positivity
          nlinarith [norm_nonneg (gradient U y), mul_nonneg hCφ0 this, mul_nonneg hCφ0 hB0,
            mul_nonneg (mul_nonneg hCφ0 hB0) (norm_nonneg (gradient U y))]
  have bB : ∀ x y, |h2_B θ v U φ x y| ≤ (Cφ * (|θ| * N * B + B)) * |1 + ‖gradient U y‖| := by
    intro x y
    have h1 : |h2_B θ v U φ x y| ≤ Cφ * (|θ| * N * B) + Cφ * B * ‖gradient U y‖ := by
      unfold h2_B
      refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
      · rw [abs_mul]
        calc |θ| * |∑ k, fderiv ℝ φ x (h2_e k) * h2_per1 v (x - y) (h2_e k)|
            ≤ |θ| * ∑ _k : Fin N, Cφ * B := by
              refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
                (Finset.sum_le_sum fun k _ => ?_)) (abs_nonneg _)
              rw [abs_mul]
              refine mul_le_mul ?_ ?_ (abs_nonneg _) hCφ0
              · rw [← Real.norm_eq_abs]
                calc ‖fderiv ℝ φ x (h2_e k)‖ ≤ ‖fderiv ℝ φ x‖ * ‖h2_e k‖ := ContinuousLinearMap.le_opNorm _ _
                  _ ≤ Cφ := by rw [h2_norm_e]; simpa using (hCφ x).2
              · rw [← Real.norm_eq_abs]
                calc ‖h2_per1 v (x - y) (h2_e k)‖ ≤ ‖h2_per1 v (x - y)‖ * ‖h2_e k‖ := ContinuousLinearMap.le_opNorm _ _
                  _ ≤ B := by rw [h2_norm_e]; simpa using (hB _).2.1
          _ = Cφ * (|θ| * N * B) := by simp; ring
      · rw [abs_mul]
        calc |fderiv ℝ φ x (gradient U y)| * |h2_per v (x - y)| ≤ (Cφ * ‖gradient U y‖) * B := by
              refine mul_le_mul ?_ ?_ (abs_nonneg _) (by positivity)
              · rw [← Real.norm_eq_abs]
                calc ‖fderiv ℝ φ x (gradient U y)‖ ≤ ‖fderiv ℝ φ x‖ * ‖gradient U y‖ := ContinuousLinearMap.le_opNorm _ _
                  _ ≤ Cφ * ‖gradient U y‖ := mul_le_mul_of_nonneg_right (hCφ x).2 (norm_nonneg _)
              · rw [← Real.norm_eq_abs]; exact (hB _).1
          _ = Cφ * B * ‖gradient U y‖ := by ring
    rw [abs_of_nonneg (by positivity : 0 ≤ 1 + ‖gradient U y‖)]
    have : 0 ≤ |θ| * N * B := by positivity
    nlinarith [norm_nonneg (gradient U y), mul_nonneg hCφ0 this, mul_nonneg hCφ0 hB0,
      mul_nonneg (mul_nonneg hCφ0 hB0) (norm_nonneg (gradient U y))]
  have cA' : Continuous (Function.uncurry fun x y => φ x * h2_A θ v U x y) := by
    exact (hφ.continuous.comp continuous_fst).mul cA
  have iA : Integrable (Function.uncurry fun x y => φ x * h2_A θ v U x y) ((volume.restrict (cep_cell N)).prod μ) :=
    h2_integrable_prod_tube cA' (R := R) (fun x y hx => by simp [hR x hx]) hG bA
  have iB : Integrable (Function.uncurry fun x y => h2_B θ v U φ x y) ((volume.restrict (cep_cell N)).prod μ) := by
    refine h2_integrable_prod_tube cB (R := R) (fun x y hx => ?_) hG bB
    unfold h2_B
    simp [h2_fderiv_eq_zero_of_far hR hx]
  have e1 : ∫ x in cep_cell N, φ x * (∫ y, h2_A θ v U x y ∂μ) = ∫ x in cep_cell N, ∫ y, φ x * h2_A θ v U x y ∂μ := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [integral_const_mul]
  rw [e1, integral_integral_swap iA, integral_integral_swap iB, ← integral_neg]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  exact h2_cell_ibp_single hv hφ hper hR y θ U hU

end HRS.MC.CepH2
