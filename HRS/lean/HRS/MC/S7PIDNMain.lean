import HRS.MC.S7PIDNLin

/-!
# Packet PI-D, sub-packet N (part 2): proof of `s7_PID_nuc_mem` (D4b)

The statement is copied verbatim from `HRS/MC/S7PIDPlan.lean`.  Route: see the note at the head of `S7PIDNLin.lean`.
Helpers here: the bilinear map `(a,b) ↦ elemTensor ![a,b]` is bounded (hence continuous), and an integrable function with values in
`projTensor` has its integral in `projTensor` (closed submodule, `Convex.average_mem`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDN

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

section Elem

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

omit [NormedAddCommGroup B] [NormedSpace ℝ B] in
theorem S7PIDN_vec_update (a b a' : B) :
    (![a, b] : Fin 2 → B) = Function.update ![a', b] 0 a := by
  ext i; fin_cases i <;> simp

omit [NormedAddCommGroup B] [NormedSpace ℝ B] in
theorem S7PIDN_vec_update' (a b b' : B) :
    (![a, b] : Fin 2 → B) = Function.update ![a, b'] 1 b := by
  ext i; fin_cases i <;> simp

theorem S7PIDN_elem_add_left (M : B [×2]→L[ℝ] ℝ) (a a' b : B) :
    M ![a + a', b] = M ![a, b] + M ![a', b] := by
  have h := M.map_update_add ![a, b] 0 a a'
  rw [S7PIDN_vec_update (a + a') b a, S7PIDN_vec_update a b a, S7PIDN_vec_update a' b a]
  simpa using h

theorem S7PIDN_elem_add_right (M : B [×2]→L[ℝ] ℝ) (a b b' : B) :
    M ![a, b + b'] = M ![a, b] + M ![a, b'] := by
  have h := M.map_update_add ![a, b] 1 b b'
  rw [S7PIDN_vec_update' a (b + b') b, S7PIDN_vec_update' a b b, S7PIDN_vec_update' a b' b]
  simpa using h

theorem S7PIDN_elem_smul_left (M : B [×2]→L[ℝ] ℝ) (r : ℝ) (a b : B) :
    M ![r • a, b] = r • M ![a, b] := by
  have h := M.map_update_smul ![a, b] 0 r a
  rw [S7PIDN_vec_update (r • a) b a, S7PIDN_vec_update a b a]
  simpa using h

theorem S7PIDN_elem_smul_right (M : B [×2]→L[ℝ] ℝ) (r : ℝ) (a b : B) :
    M ![a, r • b] = r • M ![a, b] := by
  have h := M.map_update_smul ![a, b] 1 r b
  rw [S7PIDN_vec_update' a (r • b) b, S7PIDN_vec_update' a b b]
  simpa using h

theorem S7PIDN_elem_norm_le (a b : B) : ‖(elemTensor ![a, b] : TensorDual B 2)‖ ≤ ‖a‖ * ‖b‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun M => ?_
  rw [elemTensor_apply]
  calc ‖M ![a, b]‖ ≤ ‖M‖ * ∏ i, ‖(![a, b] : Fin 2 → B) i‖ := M.le_opNorm _
    _ = ‖a‖ * ‖b‖ * ‖M‖ := by simp [Fin.prod_univ_two]; ring

/-- `(a,b) ↦ elemTensor ![a,b]` is a bounded bilinear map `B × B → TensorDual B 2` -/
theorem S7PIDN_elem_bilin :
    IsBoundedBilinearMap ℝ (fun p : B × B => (elemTensor ![p.1, p.2] : TensorDual B 2)) where
  add_left a a' b := by
    refine ContinuousLinearMap.ext fun M => ?_
    simp only [elemTensor_apply, ContinuousLinearMap.add_apply]
    exact S7PIDN_elem_add_left M a a' b
  smul_left r a b := by
    refine ContinuousLinearMap.ext fun M => ?_
    simp only [elemTensor_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact S7PIDN_elem_smul_left M r a b
  add_right a b b' := by
    refine ContinuousLinearMap.ext fun M => ?_
    simp only [elemTensor_apply, ContinuousLinearMap.add_apply]
    exact S7PIDN_elem_add_right M a b b'
  smul_right r a b := by
    refine ContinuousLinearMap.ext fun M => ?_
    simp only [elemTensor_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact S7PIDN_elem_smul_right M r a b
  bound := ⟨1, one_pos, fun a b => by
    simpa using S7PIDN_elem_norm_le a b⟩

theorem S7PIDN_elem_continuous :
    Continuous fun p : B × B => (elemTensor ![p.1, p.2] : TensorDual B 2) :=
  S7PIDN_elem_bilin.continuous

set_option maxSynthPendingDepth 3 in
theorem S7PIDN_elem_mem (a b : B) : (elemTensor ![a, b] : TensorDual B 2) ∈ projTensor B 2 :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨_, rfl⟩)

set_option maxSynthPendingDepth 3 in
/-- an integrable function with values in the closed submodule `projTensor` has its integral there -/
theorem S7PIDN_integral_mem (μ : Measure ℝ) [IsFiniteMeasure μ] (f : ℝ → TensorDual B 2)
    (hf : Integrable f μ) (hmem : ∀ u, f u ∈ projTensor B 2) : ∫ u, f u ∂μ ∈ projTensor B 2 := by
  by_cases hμ : μ = 0
  · subst hμ
    simp only [integral_zero_measure]
    exact Submodule.zero_mem _
  · have hcl : IsClosed (projTensor B 2 : Set (TensorDual B 2)) := Submodule.isClosed_topologicalClosure _
    have : NeZero μ := ⟨hμ⟩
    have havg := Convex.average_mem (Submodule.convex (projTensor B 2)) hcl
      (Filter.Eventually.of_forall hmem) hf
    have hpos : μ.real Set.univ ≠ 0 := by
      intro h
      rw [Measure.real, ENNReal.toReal_eq_zero_iff] at h
      rcases h with h | h
      · exact hμ (Measure.measure_univ_eq_zero.1 h)
      · exact measure_ne_top μ _ h
    have hav : ∫ u, f u ∂μ = μ.real Set.univ • ⨍ u, f u ∂μ := by
      rw [average_eq, smul_smul, mul_inv_cancel₀ hpos, one_smul]
    rw [hav]
    exact Submodule.smul_mem _ _ havg

end Elem

set_option maxSynthPendingDepth 3 in
/-- **s7_PID_nuc_mem_proof**: proof of `HRS.MC.Sec7.PIDPlan.s7_PID_nuc_mem` (statement verbatim). -/
theorem s7_PID_nuc_mem_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (c c' : ℝ) (hc : 0 ≤ c) (hcc : c ≤ c') (hc' : c' ≤ T) (n : ℕ) (w w' : ℝ → ℕ → NegSobolev d m)
    (hw : ∀ i, Measurable fun u => w u i) (hw' : ∀ i, Measurable fun u => w' u i) (b : ℝ)
    (hb : ∀ u i, ‖w u i‖ ≤ b) (hb' : ∀ u i, ‖w' u i‖ ≤ b) :
    Integrable (fun u => elemTensor ![polyPath R.D R.ρ m T c c' n (w u), polyPath R.D R.ρ m T c c' n (w' u)])
        (volume.restrict (Set.Ioc c c')) ∧
      nuc R.D R.ρ m T c c' n w w' ∈ projTensor (PathSpace d m T) 2 := by
  rcases eq_or_lt_of_le hcc with heq | hlt
  · -- degenerate interval: the measure is zero
    subst heq
    rw [Set.Ioc_self, Measure.restrict_empty]
    refine ⟨integrable_zero_measure, ?_⟩
    unfold nuc
    rw [Set.Ioc_self, Measure.restrict_empty, integral_zero_measure]
    exact Submodule.zero_mem _
  · obtain ⟨C₁, hC₁, hLip⟩ := S7PIDN_Phi_lip R m hm T hT
    obtain ⟨C₁', hC₁', hC⟩ := S7PIDP.s7_PID_poly_proof R m hm T hT
    have hΦc : Continuous (S7PIDN_Phi R.D R.ρ m T c c' n) := by
      have : LipschitzWith ⟨C₁, by linarith⟩ (S7PIDN_Phi R.D R.ρ m T c c' n) :=
        LipschitzWith.of_dist_le_mul fun x y => by
          rw [dist_eq_norm, dist_eq_norm]
          exact hLip c c' hc hlt hc' n x y
      exact this.continuous
    have hψ : Measurable fun u => (fun i : Fin (2 ^ n + 1) => w u i.1) :=
      measurable_pi_iff.2 fun i => hw i.1
    have hψ' : Measurable fun u => (fun i : Fin (2 ^ n + 1) => w' u i.1) :=
      measurable_pi_iff.2 fun i => hw' i.1
    have hpair : StronglyMeasurable fun u => ((fun i : Fin (2 ^ n + 1) => w u i.1),
        (fun i : Fin (2 ^ n + 1) => w' u i.1)) := (hψ.prodMk hψ').stronglyMeasurable
    have hmeas : StronglyMeasurable fun u =>
        (elemTensor ![polyPath R.D R.ρ m T c c' n (w u), polyPath R.D R.ρ m T c c' n (w' u)] :
          TensorDual (PathSpace d m T) 2) := by
      have hcont : Continuous fun z : (Fin (2 ^ n + 1) → NegSobolev d m) × (Fin (2 ^ n + 1) → NegSobolev d m) =>
          (elemTensor ![S7PIDN_Phi R.D R.ρ m T c c' n z.1, S7PIDN_Phi R.D R.ρ m T c c' n z.2] :
            TensorDual (PathSpace d m T) 2) :=
        S7PIDN_elem_continuous.comp ((hΦc.comp continuous_fst).prodMk (hΦc.comp continuous_snd))
      have := Continuous.comp_stronglyMeasurable hcont hpair
      simpa only [S7PIDN_Phi_eq] using this
    have hbd : ∀ u, ‖(elemTensor ![polyPath R.D R.ρ m T c c' n (w u), polyPath R.D R.ρ m T c c' n (w' u)] :
          TensorDual (PathSpace d m T) 2)‖ ≤ (C₁' * b) * (C₁' * b) := by
      intro u
      have h1 := (hC c c' hc hcc hc' n (w u)).2.1 b fun i _ => hb u i
      have h2 := (hC c c' hc hcc hc' n (w' u)).2.1 b fun i _ => hb' u i
      exact (S7PIDN_elem_norm_le _ _).trans (mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1))
    have hint : Integrable (fun u => (elemTensor ![polyPath R.D R.ρ m T c c' n (w u),
        polyPath R.D R.ρ m T c c' n (w' u)] : TensorDual (PathSpace d m T) 2))
        (volume.restrict (Set.Ioc c c')) :=
      Integrable.of_bound hmeas.aestronglyMeasurable _ (ae_of_all _ hbd)
    refine ⟨hint, ?_⟩
    unfold nuc
    exact S7PIDN_integral_mem _ _ hint fun u => S7PIDN_elem_mem _ _

end HRS.MC.Sec7.S7PIDN

end
