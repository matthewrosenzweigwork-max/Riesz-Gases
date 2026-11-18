import HRS.MS.R2InterpAux124
import HRS.MS.R2InterpAux96

/-!
# S10.2 (worker S10S), part 125 (packet M1): the drift structure `S102Drift` of the quadratic field with an integrable pathwise constant `Mb`

`Mb ζ u = c₁ N (Env(X_u ζ) + E Env(X_u))`; `Env` is the polynomial envelope of S10.2 (Aux121-123).  No dual-norm bridge is needed
(`HANDOFF_S10R`, section 5).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ}

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 1600000 in
theorem s102_M1 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {C : WholeCoeff d} {m T : ℝ} {r : ℕ}
    {c : MultiIndex d → ℝ} (hS : S102Std C m T r c) (hT : 0 < T) (hr : (d : ℝ) / 2 + 2 < r) {Pw : ℝ}
    (hP0 : 0 ≤ Pw) {β p K M L C₀ c₀ : ℝ} (hc : 0 < c₀) (hβ : 0 < β) (hp : 1 < p) {ρ : Euc d → ℝ}
    (hρR : IsRound2Density d s M L ρ) (hG : ∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → EucConfig d N)
    (hXm : ∀ t, Measurable (X t))
    (hXjm : ∀ t ∈ Icc (0 : ℝ) T, Measurable fun q : ℝ × Ω => X (min q.1 t).toNNReal q.2)
    (hdens : ∀ r ∈ Icc (0 : ℝ) T,
      HasR2ActualDensity s β p K (HRS.Whole.withDensityReal ρ) (P.map (X r.toNNReal))) :
    ∃ Mb : Ω → ℝ → ℝ,
      (∀ᵐ ζ ∂P, S102Drift C m T r Pw (fun u => r2QuadField s (HRS.Whole.withDensityReal ρ) P X u ζ) (Mb ζ)) ∧
      Integrable (fun ζ => ∫ u in Ioc 0 T, Mb ζ u) P := by
  classical
  have hd1 : 1 ≤ d := by omega
  haveI hμp : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.MS.R2Mt.s92_isProb_mu hρR.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  obtain ⟨c1, hc1, hker⟩ := s102_comm_poly hd1 hs0 hP0 r hr
  obtain ⟨CE, hCE0, hCE⟩ := s102_Env_bound hd hs0 hs M L C₀ c₀ β p K hc hβ hp hP0
  obtain ⟨A, hA0, hApoly⟩ := s102_gk_int hd1 hs0 hs M C₀ c₀ hc hP0
  obtain ⟨hgi, hgH, -⟩ := hApoly ρ hρR.prob hρR.bdd hG
  have hEint : ∀ u ∈ Icc (0 : ℝ) T, Integrable (fun ζ => s102_Env (s102_gk s Pw) (X u.toNNReal ζ) μ) P ∧
      ∫ ζ, s102_Env (s102_gk s Pw) (X u.toNNReal ζ) μ ∂P ≤ CE := fun u hu =>
    hCE hρR hG hN P (X u.toNNReal) (hXm _) (hdens u hu)
  set Envf : ℝ × Ω → ℝ := fun q => s102_Env (s102_gk s Pw) (X (min q.1 T).toNNReal q.2) μ with hEnvf
  have hEnvm : Measurable Envf := (s102_Env_meas (s102_gk_meas s Pw)).comp (hXjm T ⟨hT.le, le_rfl⟩)
  set ec : ℝ → ℝ := fun u => ∫ ζ', Envf (u, ζ') ∂P with hec
  have hecm : Measurable ec := (hEnvm.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  have hEnn : ∀ q, 0 ≤ Envf q := fun q => s102_Env_nonneg (s102_gk_nonneg s Pw) _ _
  have hecn : ∀ u, 0 ≤ ec u := fun u => integral_nonneg fun ζ => hEnn _
  set Mt : ℝ × Ω → ℝ := fun q => c1 * N * (Envf q + ec q.1) with hMt
  have hMtm : Measurable Mt := measurable_const.mul (hEnvm.add (hecm.comp measurable_fst))
  have hMt0 : ∀ q, 0 ≤ Mt q := fun q =>
    mul_nonneg (mul_nonneg hc1 (Nat.cast_nonneg N)) (add_nonneg (hEnn q) (hecn q.1))
  -- the time slices
  have hslice : ∀ u ∈ Icc (0 : ℝ) T, (∀ ζ, Envf (u, ζ) = s102_Env (s102_gk s Pw) (X u.toNNReal ζ) μ) ∧
      ec u = ∫ ζ, s102_Env (s102_gk s Pw) (X u.toNNReal ζ) μ ∂P := by
    intro u hu
    have e : ∀ ζ, Envf (u, ζ) = s102_Env (s102_gk s Pw) (X u.toNNReal ζ) μ := fun ζ => by
      simp only [hEnvf, min_eq_left hu.2]
    exact ⟨e, by simp only [hec, e]⟩
  have hprod : Integrable Mt ((volume.restrict (Icc (0 : ℝ) T)).prod P) := by
    refine s102_prodInt (C := c1 * N * (2 * CE)) hMtm fun u hu => ?_
    obtain ⟨hi, hb⟩ := hEint u hu
    obtain ⟨he, hecu⟩ := hslice u hu
    have e : ∀ ζ, ‖Mt (u, ζ)‖ₑ = ENNReal.ofReal (c1 * N * (s102_Env (s102_gk s Pw) (X u.toNNReal ζ) μ + ec u)) := by
      intro ζ
      rw [Real.enorm_eq_ofReal (hMt0 _)]
      simp only [hMt, he]
    simp_rw [e]
    have hint : Integrable (fun ζ => c1 * N * (s102_Env (s102_gk s Pw) (X u.toNNReal ζ) μ + ec u)) P :=
      (hi.add (integrable_const _)).const_mul _
    have hnn : ∀ ζ, 0 ≤ c1 * N * (s102_Env (s102_gk s Pw) (X u.toNNReal ζ) μ + ec u) := fun ζ =>
      mul_nonneg (mul_nonneg hc1 (Nat.cast_nonneg N))
        (add_nonneg (s102_Env_nonneg (s102_gk_nonneg s Pw) (X u.toNNReal ζ) μ) (hecn u))
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_const_mul, integral_add hi (integrable_const _), integral_const, hecu]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    have hc1N : 0 ≤ c1 * N := mul_nonneg hc1 (Nat.cast_nonneg N)
    exact mul_le_mul_of_nonneg_left (by linarith) hc1N
  have hae : ∀ᵐ ζ ∂P, IntegrableOn (fun u => Mt (u, ζ)) (Icc (0 : ℝ) T) := hprod.prod_left_ae
  refine ⟨fun ζ u => Mt (u, ζ), ?_, ?_⟩
  · filter_upwards [hae] with ζ hζ
    refine ⟨fun u hu => ?_, fun u hu f hf => ?_, fun u => hMt0 _, hζ, fun t ht α => ?_⟩
    · obtain ⟨hi, -⟩ := hEint u hu
      exact (s102_Z_quad r hr hc1 hker hgi hgH P (X u.toNNReal) (hXm _) hi ζ).1
    · obtain ⟨hi, -⟩ := hEint u hu
      obtain ⟨he, hecu⟩ := hslice u hu
      have h1 := (s102_Z_quad r hr hc1 hker hgi hgH P (X u.toNNReal) (hXm _) hi ζ).2 f hf
      have h2 : Mt (u, ζ) = c1 * N * (s102_Env (s102_gk s Pw) (X u.toNNReal ζ) μ +
          ∫ ζ', s102_Env (s102_gk s Pw) (X u.toNNReal ζ') μ ∂P) := by
        simp only [hMt, he, hecu]
      show |r2QuadField s μ P X u ζ f| ≤ Mt (u, ζ) * (weightedSobolevE r Pw f).toReal
      rw [h2]
      exact h1
    · have hf := s102_propagator_classical (hS.hcls α t ht)
      obtain ⟨hK, B, hKm, hKr, -⟩ := s102_kernel_pkg hs0 hf
      have hXt := hXjm t ht
      have hpE : Measurable fun q : ℝ × EucConfig d N => pairEnergy (hK q.1) q.2 μ :=
        HRS.MS.R2Chaos.s94_pairEnergy_measurable hKm
      set cc : ℝ → ℝ := fun u => ∫ ζ', pairEnergy (hK u) (X (min u t).toNNReal ζ') μ ∂P with hcc
      have hccm : Measurable cc :=
        ((hpE.comp (measurable_fst.prodMk hXt)).stronglyMeasurable.integral_prod_right' (ν := P)).measurable
      have hRm : Measurable fun u : ℝ =>
          (N : ℝ) * (pairEnergy (hK u) (X (min u t).toNNReal ζ) μ - cc u) :=
        measurable_const.mul ((hpE.comp (measurable_id.prodMk (hXt.comp (measurable_id.prodMk measurable_const)))).sub
          hccm)
      refine hRm.aestronglyMeasurable.congr ?_
      refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun u hu => ?_)
      show (N : ℝ) * (pairEnergy (hK u) (X (min u t).toNNReal ζ) μ - cc u) =
        r2QuadField s μ P X u ζ (propagatorW C u t (oscTestFun m α))
      simp only [r2QuadField, hcc, min_eq_left hu.2, hKr u hu]
  · have := hprod.integral_prod_right
    refine this.congr (Eventually.of_forall fun ζ => ?_)
    exact integral_Icc_eq_integral_Ioc

end HRS.MS.R2Interp

end
