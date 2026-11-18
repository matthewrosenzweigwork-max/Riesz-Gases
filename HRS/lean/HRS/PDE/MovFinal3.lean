import HRS.PDE.MovFinal1
import HRS.PDE.MovFFinal
import HRS.PDE.MovGFinal
import HRS.PDE.MovSpec3

/-!
# MOV-FINAL (part 3): the modulated free energy glue re-run with the relocated packet proofs

Verbatim copy of `mov_mfe_ineq` (`HRS/PDE/MovSpec3.lean`) with frozen packets replaced by `_proof`
(`mov_ent_ineq_proof`, `movT_relEntropy_split_proof`, `movT_logK_integral_proof`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-- **`mov_mfe_ineq_proof` (modulated free energy dissipation, Fisher term dropped).**  The integrated form of
`B:eq:mfe-dissipation` (M L3221-3224): for all `t ∈ [0,T]`, `𝖤_N(f_N^t,μ^t) < ∞`, `Comm_N(u_V^r;·,μ^r)` is
`f_N^r`-integrable, `r ↦ ∫Comm_N f_N^r` is integrable and
`𝖤_N(f_N^t,μ^t) ≤ 𝖤_N(f_N^0,μ^0) - ½∫_0^t∫Comm_N(u_V^r;X,μ^r) f_N^r(dX) dr`.
Standing assumptions: `MovHyp` (the hypotheses of `MFEHyp` on the process and the background, with the regularity of
`MovTraj`), `𝖤_N(f_N^0,μ^0) < ∞`.  Proof: `mov_ent_ineq_proof` (the finite relative entropy `H(f^0|Q^0)` follows from
`MFEFinite` by `movT_relEntropy_split_proof`), `movT_relEntropy_split_proof` at times `0` and `t`, `movT_logK_integral_proof`, and
`movT_commAt_eq_half`; the terms `∫E_Q C_N` cancel exactly.  Discharges the first sentence of the proof of Prop 3.41
(M L3220-3224: modulated free energy calculation for the regularised laws, passage to the selected law by lower
semicontinuity, discarding the Fisher information) for `mfe_uniform` (`Coercivity.lean:3395`). -/
theorem mov_mfe_ineq_proof (hN : 2 ≤ N) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (h : MovHyp P D N T ρ X₀ W X)
    (hfin : MFEFinite d D.s (P.map X₀) (withDensityReal (ρ 0))) :
    ∀ t ∈ Set.Icc 0 T,
      MFEFinite d D.s (P.map (X t.toNNReal)) (withDensityReal (ρ t)) ∧
      (∀ r ∈ Set.Icc 0 t, Integrable
        (fun Z => commQuantity d D.s (mfeTransport D (ρ r)) Z (withDensityReal (ρ r)))
        (P.map (X r.toNNReal))) ∧
      IntegrableOn (fun r => ∫ Z, commQuantity d D.s (mfeTransport D (ρ r)) Z (withDensityReal (ρ r))
        ∂(P.map (X r.toNNReal))) (Set.Icc 0 t) ∧
      modulatedFreeEnergy d D.s D.invβ (P.map (X t.toNNReal)) (withDensityReal (ρ t)) ≤
        modulatedFreeEnergy d D.s D.invβ (P.map X₀) (withDensityReal (ρ 0)) -
          (1 / 2) * ∫ r in Set.Icc 0 t, ∫ Z, commQuantity d D.s (mfeTransport D (ρ r)) Z
            (withDensityReal (ρ r)) ∂(P.map (X r.toNNReal)) := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hS := h.sol
  have hβ := h.traj.pos_temp
  haveI : IsProbabilityMeasure (P.map X₀) := inferInstance
  haveI hfp : ∀ r : ℝ, IsProbabilityMeasure (P.map (X r.toNNReal)) := fun r =>
    inferInstance
  have hsplit : ∀ r ∈ Set.Icc 0 T, ∀ (ν : Measure (Config d N)) [IsProbabilityMeasure ν],
      (relEntropy ν (movT_Q (periodicRiesz d D.s) D N ρ r) ≠ ⊤ ↔ MFEFinite d D.s ν (withDensityReal (ρ r))) ∧
      (MFEFinite d D.s ν (withDensityReal (ρ r)) →
        modulatedFreeEnergy d D.s D.invβ ν (withDensityReal (ρ r)) =
          D.invβ / N * ((relEntropy ν (movT_Q (periodicRiesz d D.s) D N ρ r)).toReal -
            Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ r))))) := by
    intro r hr ν _
    obtain ⟨h1, h2⟩ := movT_relEntropy_split_proof hN (D := D) hβ (h.traj.mf.density r hr)
      (h.traj.ck r hr) (h.traj.pos r hr) (ν := ν)
    refine ⟨h1, fun hfin' => ?_⟩
    have h3 := h2 hfin'
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    unfold modulatedFreeEnergy normRelEntropy
    rw [ENNReal.toReal_div, ENNReal.toReal_natCast]
    have hinv : D.invβ * D.invβ⁻¹ = 1 := mul_inv_cancel₀ hβ.ne'
    have h4 : (relEntropy ν (Measure.pi fun _ : Fin N => withDensityReal (ρ r))).toReal =
        (relEntropy ν (movT_Q (periodicRiesz d D.s) D N ρ r)).toReal -
          D.invβ⁻¹ * N * ∫ X, rieszEnergy d D.s X (withDensityReal (ρ r)) ∂ν -
          Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ r))) := by
      unfold movT_Q; linarith
    rw [h4]
    field_simp
    have : D.invβ * (D.invβ⁻¹ * (N : ℝ) * ∫ X, rieszEnergy d D.s X (withDensityReal (ρ r)) ∂ν) =
        N * ∫ X, rieszEnergy d D.s X (withDensityReal (ρ r)) ∂ν := by
      rw [← mul_assoc, ← mul_assoc, hinv, one_mul]
    nlinarith
  -- finiteness of the initial entropy and the entropy inequality
  have hfinQ : relEntropy (P.map X₀) (movT_Q (periodicRiesz d D.s) D N ρ 0) ≠ ⊤ :=
    ((hsplit 0 ⟨le_rfl, hT⟩ (P.map X₀)).1).2 hfin
  obtain ⟨hHt, hint, hintOn, hineq⟩ := (mov_ent_ineq_proof hN P h hfinQ).1 t ht
  have hMFEt := ((hsplit t ht (P.map (X t.toNNReal))).1).1 hHt
  obtain ⟨hlogKint, hlogK⟩ := movT_logK_integral_proof hN h.traj
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hβN : 0 < D.invβ⁻¹ * N := mul_pos (inv_pos.2 hβ) hNpos
  set f : ℝ → Measure (Config d N) := fun r => P.map (X r.toNNReal) with hf
  set Cf : ℝ → ℝ := fun r => ∫ Z, movT_comm D N ρ r Z ∂(f r) with hCf
  set EQ : ℝ → ℝ := fun r => ∫ Z, movT_comm D N ρ r Z ∂(movT_Q (periodicRiesz d D.s) D N ρ r) with hEQ
  set G : ℝ → ℝ := fun r => ∫ Z, movT_source D N ρ r Z ∂(f r) with hG
  have hsrc : ∀ r Z, movT_source D N ρ r Z = -(D.invβ⁻¹ * N) * (movT_comm D N ρ r Z - EQ r) :=
    fun r Z => rfl
  have hcomm_int : ∀ r ∈ Set.Icc 0 t, Integrable (movT_comm D N ρ r) (f r) := by
    intro r hr
    have h1 := hint r hr
    have h2 : Integrable (fun Z => EQ r - (D.invβ⁻¹ * N)⁻¹ * movT_source D N ρ r Z) (f r) :=
      (integrable_const _).sub (h1.const_mul _)
    refine h2.congr (Eventually.of_forall fun Z => ?_)
    simp only [hsrc]
    field_simp
    ring
  have hG_eq : ∀ r ∈ Set.Icc 0 t, G r = -(D.invβ⁻¹ * N) * (Cf r - EQ r) := by
    intro r hr
    haveI := hfp r
    simp only [hG, hCf, hsrc]
    rw [integral_const_mul, integral_sub (hcomm_int r hr) (integrable_const _)]
    simp
  have hCf_eq : ∀ r ∈ Set.Icc 0 t, Cf r = EQ r - (D.invβ⁻¹ * N)⁻¹ * G r := by
    intro r hr
    rw [hG_eq r hr]
    field_simp
    ring
  have hEQint : IntegrableOn EQ (Set.Icc 0 t) :=
    hlogKint.mono_set (Set.Icc_subset_Icc le_rfl ht.2)
  have hCfint : IntegrableOn Cf (Set.Icc 0 t) := by
    have : IntegrableOn (fun r => EQ r - (D.invβ⁻¹ * N)⁻¹ * G r) (Set.Icc 0 t) :=
      hEQint.sub (hintOn.const_mul _)
    exact this.congr_fun (fun r hr => (hCf_eq r hr).symm) measurableSet_Icc
  have hint_G : ∫ r in Set.Icc 0 t, G r = -(D.invβ⁻¹ * N) * ((∫ r in Set.Icc 0 t, Cf r) - ∫ r in Set.Icc 0 t, EQ r) := by
    rw [← integral_sub hCfint hEQint, ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Icc fun r hr => hG_eq r hr
  have hq : ∀ r Z, commQuantity d D.s (mfeTransport D (ρ r)) Z (withDensityReal (ρ r)) =
      2 * movT_comm D N ρ r Z := by
    intro r Z
    have := movT_commAt_eq_half D N (ρ r) Z
    unfold movT_comm
    linarith
  refine ⟨hMFEt, fun r hr => ?_, ?_, ?_⟩
  · have := (hcomm_int r hr).const_mul 2
    exact this.congr (Eventually.of_forall fun Z => (hq r Z).symm)
  · have this : IntegrableOn (fun r => 2 * Cf r) (Set.Icc 0 t) := hCfint.const_mul 2
    refine this.congr_fun (fun r hr => ?_) measurableSet_Icc
    simp only [hCf]
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun Z => (hq r Z).symm)
  · have hE0 := (hsplit 0 ⟨le_rfl, hT⟩ (P.map X₀)).2 hfin
    have hEt := (hsplit t ht (P.map (X t.toNNReal))).2 hMFEt
    rw [hEt, hE0]
    have hK := hlogK t ht
    have hcq : ∫ r in Set.Icc 0 t, ∫ Z, commQuantity d D.s (mfeTransport D (ρ r)) Z
        (withDensityReal (ρ r)) ∂(P.map (X r.toNNReal)) = 2 * ∫ r in Set.Icc 0 t, Cf r := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Icc fun r _ => ?_
      simp only [hCf, hf]
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun Z => hq r Z)
    rw [hcq]
    have hH : (relEntropy (P.map (X t.toNNReal)) (movT_Q (periodicRiesz d D.s) D N ρ t)).toReal ≤
        (relEntropy (P.map X₀) (movT_Q (periodicRiesz d D.s) D N ρ 0)).toReal +
          ∫ r in Set.Icc 0 t, G r := hineq
    have hinvβ : D.invβ * D.invβ⁻¹ = 1 := mul_inv_cancel₀ hβ.ne'
    have hpos : 0 < D.invβ / N := div_pos hβ hNpos
    -- H_t - log K_t - (H_0 - log K_0) ≤ -βN ∫ Cf
    have key : (relEntropy (P.map (X t.toNNReal)) (movT_Q (periodicRiesz d D.s) D N ρ t)).toReal -
        Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ t))) ≤
        (relEntropy (P.map X₀) (movT_Q (periodicRiesz d D.s) D N ρ 0)).toReal -
        Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ 0))) -
          D.invβ⁻¹ * N * ∫ r in Set.Icc 0 t, Cf r := by
      rw [hint_G] at hH
      have hK' : Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ t))) =
          Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ 0))) +
            D.invβ⁻¹ * N * ∫ r in Set.Icc 0 t, EQ r := by
        have := hK; simp only [hEQ] at *; linarith
      rw [hK']
      nlinarith
    have := mul_le_mul_of_nonneg_left key hpos.le
    have h5 : D.invβ / N * (D.invβ⁻¹ * N * ∫ r in Set.Icc 0 t, Cf r) = ∫ r in Set.Icc 0 t, Cf r := by
      field_simp
    nlinarith

example := (@mov_mfe_ineq_proof : type_of% @HRS.mov_mfe_ineq)

end HRS

end
