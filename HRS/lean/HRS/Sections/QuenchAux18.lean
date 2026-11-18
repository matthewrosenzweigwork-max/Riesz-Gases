import HRS.Sections.QuenchAux17

/-!
# Packet QUENCH (Q27), part 18: expectation of a bounded bilinear form of `E_m`-valued random variables

`E B(U,V) = ∑_j B(e_j,e_j) c_j` when the coordinates of `U,V` are uncorrelated across modes with
`E[U_j V_j] = c_j` and `‖U‖‖V‖ ∈ L¹` (Hilbert basis truncation and dominated convergence).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

variable {d : ℕ} {m : ℝ}

/-- Finite Fourier truncation. -/
def eproj (F : Finset (NonzeroLattice d)) (x : NegSobolev d m) : NegSobolev d m :=
  ∑ j ∈ F, NegSobolev.coord x j • esingle m j

lemma coord_eproj (F : Finset (NonzeroLattice d)) (x : NegSobolev d m) (j' : NonzeroLattice d) :
    NegSobolev.coord (eproj F x) j' = if j' ∈ F then NegSobolev.coord x j' else 0 := by
  classical
  unfold eproj
  have hadd : ∀ (s : Finset (NonzeroLattice d)) (f : NonzeroLattice d → NegSobolev d m),
      NegSobolev.coord (∑ j ∈ s, f j) j' = ∑ j ∈ s, NegSobolev.coord (f j) j' := by
    intro s f
    induction s using Finset.induction_on with
    | empty => rfl
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl
  rw [hadd]
  simp_rw [coord_smul_esingle]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

lemma norm_eproj_le (F : Finset (NonzeroLattice d)) (x : NegSobolev d m) : ‖eproj F x‖ ≤ ‖x‖ := by
  classical
  obtain ⟨h1, h2⟩ := NegSobolev.coord_sq (eproj F x)
  obtain ⟨h3, h4⟩ := NegSobolev.coord_sq x
  have : ‖eproj F x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [h2, h4]
    refine h1.tsum_le_tsum (fun j => ?_) h3
    rw [coord_eproj]
    split_ifs
    · exact le_rfl
    · simpa using sq_nonneg (NegSobolev.coord x j)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

lemma hasSum_esingle (x : NegSobolev d m) :
    HasSum (fun j : NonzeroLattice d => NegSobolev.coord x j • esingle m j) x := by
  have := lp.hasSum_single (p := (2 : ℝ≥0∞)) (E := fun _ : NonzeroLattice d => ℝ) (by simp)
    (show lp (fun _ : NonzeroLattice d => ℝ) 2 from x)
  have e : (fun j : NonzeroLattice d => NegSobolev.coord x j • esingle m j) =
      fun j => (lp.single 2 j (NegSobolev.coord x j) : lp (fun _ : NonzeroLattice d => ℝ) 2) := by
    funext j
    show ofLp' m (NegSobolev.coord x j • lp.single 2 j (1 : ℝ)) = _
    rw [← lp.single_smul]
    simp only [smul_eq_mul, mul_one]
    rfl
  rw [e]
  exact this

lemma abs_coord_le (x : NegSobolev d m) (j : NonzeroLattice d) : |NegSobolev.coord x j| ≤ ‖x‖ := by
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (show lp (fun _ : NonzeroLattice d => ℝ) 2 from x) j
  unfold NegSobolev.coord
  exact h

lemma measurable_coord (j : NonzeroLattice d) : Measurable (fun x : NegSobolev d m => NegSobolev.coord x j) :=
  (q38b_continuous_coord (m := m) j).measurable

section Expect

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma eproj_bilin (B : NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ) (F : Finset (NonzeroLattice d))
    (x y : NegSobolev d m) :
    B (eproj F x) (eproj F y) = ∑ j ∈ F, ∑ j' ∈ F, (NegSobolev.coord x j * NegSobolev.coord y j') *
      B (esingle m j) (esingle m j') := by
  unfold eproj
  have h1 : B (∑ j ∈ F, NegSobolev.coord x j • esingle m j) =
      ∑ j ∈ F, NegSobolev.coord x j • B (esingle m j) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => map_smul B _ _
  rw [h1, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.smul_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [map_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem expect_bilinear (B : NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ) {U V : Ω → NegSobolev d m}
    (hU : Measurable U) (hV : Measurable V) (hUV : Integrable (fun ω => ‖U ω‖ * ‖V ω‖) P)
    (c : NonzeroLattice d → ℝ)
    (hcov : ∀ j j', ∫ ω, NegSobolev.coord (U ω) j * NegSobolev.coord (V ω) j' ∂P =
      if j = j' then c j else 0) :
    HasSum (fun j => B (esingle m j) (esingle m j) * c j) (∫ ω, B (U ω) (V ω) ∂P) := by
  classical
  have hint : ∀ j j', Integrable (fun ω => NegSobolev.coord (U ω) j * NegSobolev.coord (V ω) j') P := by
    intro j j'
    refine hUV.mono' (((measurable_coord j).comp hU).mul ((measurable_coord j').comp hV)).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_coord_le _ _) (abs_coord_le _ _) (abs_nonneg _) (norm_nonneg _)
  have hmeasA : ∀ F : Finset (NonzeroLattice d), AEStronglyMeasurable
      (fun ω => B (eproj F (U ω)) (eproj F (V ω))) P := by
    intro F
    simp_rw [eproj_bilin]
    exact (Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun j' _ =>
      (((measurable_coord j).comp hU).mul ((measurable_coord j').comp hV)).mul_const _).aestronglyMeasurable
  have hintA : ∀ F : Finset (NonzeroLattice d), ∫ ω, B (eproj F (U ω)) (eproj F (V ω)) ∂P =
      ∑ j ∈ F, B (esingle m j) (esingle m j) * c j := by
    intro F
    simp_rw [eproj_bilin]
    rw [integral_finset_sum _ fun j _ => integrable_finset_sum _ fun j' _ => (hint j j').mul_const _]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [integral_finset_sum _ fun j' _ => (hint j j').mul_const _]
    simp_rw [integral_mul_const, hcov]
    rw [Finset.sum_eq_single_of_mem j hj]
    · simp; ring
    · intro j' _ hj'
      simp [Ne.symm hj']
  have hbound : Integrable (fun ω => ‖B‖ * (‖U ω‖ * ‖V ω‖)) P := hUV.const_mul _
  have hlim := tendsto_integral_filter_of_dominated_convergence (l := atTop (α := Finset (NonzeroLattice d)))
    (F := fun F ω => B (eproj F (U ω)) (eproj F (V ω))) (f := fun ω => B (U ω) (V ω))
    (fun ω => ‖B‖ * (‖U ω‖ * ‖V ω‖)) (Eventually.of_forall hmeasA)
    (Eventually.of_forall fun F => Eventually.of_forall fun ω => by
      have h1 := B.le_opNorm₂ (eproj F (U ω)) (eproj F (V ω))
      calc ‖B (eproj F (U ω)) (eproj F (V ω))‖ ≤ ‖B‖ * ‖eproj F (U ω)‖ * ‖eproj F (V ω)‖ := h1
        _ ≤ ‖B‖ * ‖U ω‖ * ‖V ω‖ := by
            gcongr
            · exact norm_eproj_le F _
            · exact norm_eproj_le F _
        _ = ‖B‖ * (‖U ω‖ * ‖V ω‖) := by ring)
    hbound
    (Eventually.of_forall fun ω => by
      have hc := B.continuous₂
      have h1 : Tendsto (fun F : Finset (NonzeroLattice d) => eproj F (U ω)) atTop (𝓝 (U ω)) := hasSum_esingle (U ω)
      have h2 : Tendsto (fun F : Finset (NonzeroLattice d) => eproj F (V ω)) atTop (𝓝 (V ω)) := hasSum_esingle (V ω)
      exact (hc.tendsto (U ω, V ω)).comp (h1.prodMk_nhds h2))
  simp_rw [hintA] at hlim
  exact hlim

end Expect

end Qch

end HRS
