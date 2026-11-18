import HRS.MS.R2InterpAux115

/-!
# S10.2 (worker S10R), part 116 (packet M3h): `ζ ↦ ∫ cylA` is a.e.-measurable
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MC.Sec7.PI

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}

set_option maxHeartbeats 1600000 in
theorem s102_cylA_meas (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hS : S102Std C m T r c)
    (hlin : S102Lin C m T) (hP : (d : ℝ) < 2 * Pw) (hP0 : 0 ≤ Pw) (hr : (d : ℝ) / 2 < r) (hm : (d : ℝ) < m)
    (hT : 0 < T) (L : ℕ) {β p K M Lr : ℝ} (hβ : 0 < β) (hp : 1 < p) {ρ : Euc d → ℝ}
    (hρR : IsRound2Density d s M Lr ρ) {N : ℕ} (hN : 2 ≤ N) {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsProgressive ℱ (ofNNRealTime X)) (hXm : ∀ t, Measurable (X t))
    (hcont : ∀ᵐ ζ ∂P, ∀ k, Continuous fun t : ℝ≥0 => X t ζ k)
    (hdens : ∀ r ∈ Icc (0 : ℝ) T, HasR2ActualDensity s β p K (HRS.Whole.withDensityReal ρ) (P.map (X r.toNNReal)))
    (hmom : ∀ u ∈ Icc (0 : ℝ) T, Integrable (fun x : Euc d => jbracket x ^ Pw)
      (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))))
    (γ : ℝ → Measure (OscPath d m T)) (hγ : ∀ u ∈ Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u))
    {Φ : OscPath d m T → ℝ} (hΦ : MemCb 5 Φ) :
    AEStronglyMeasurable (fun ζ => ∫ u in Ioc 0 T, s102_cylA C m T s (HRS.Whole.withDensityReal ρ) P X
      (s102_tauk hT L) (s102_alk L) (fun x => Φ (s102_Lam T L x)) ζ u) P := by
  classical
  have hN0 : 0 < N := by omega
  have hd1 : 1 ≤ d := by omega
  have hG5 : MemCb 5 (fun x => Φ (s102_Lam T L x)) := (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof (s102_Lam T L) hΦ).1
  have hG2 : MemCb 2 (fun x => Φ (s102_Lam T L x)) := ⟨hG5.1.of_le (by norm_num), fun j hj => hG5.2 j (by omega)⟩
  have hGi := s102_gramInt hS hT L
  have hXjm : ∀ t ∈ Icc (0 : ℝ) T, Measurable fun q : ℝ × Ω => X (min q.1 t).toNNReal q.2 := fun t _ =>
    measurable_progressive_min_gen (u := ofNNRealTime X) hX t
  obtain ⟨Ob, hObm, hObeq⟩ := s102_obsY_jmeas hS hT L hN0 P X hXm hXjm
  have hbdc := fun i : Fin (s102_q d L) =>
    (s102_bdc_prog_int hd hs0 hs hS hT L hβ hp hρR hN P X hX hdens i).1
  have hbdm : ∀ i : Fin (s102_q d L), Measurable fun x : ℝ × Ω =>
      s102_bdc C m hT L s (HRS.Whole.withDensityReal ρ) P X i (min x.1 T) x.2 := fun i =>
    measurable_progressive_min_gen (hbdc i) T
  set F1 : ℝ × Ω → ℝ := fun q => ∑ i : Fin (s102_q d L),
    (if q.1 ∈ Icc (0 : ℝ) T then fderiv ℝ (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L))
        (fun x => Φ (s102_Lam T L x)) q.1) (Ob q) (EuclideanSpace.single i 1) else 0) *
      (-Real.sqrt N * s102_bdc C m hT L s (HRS.Whole.withDensityReal ρ) P X i (min q.1 T) q.2) with hF1
  have hF1m : Measurable F1 := by
    refine Finset.measurable_sum _ fun i _ => ?_
    have h1 := s102_heatFderiv_meas hT L hGi γ hγ hG2 i
    exact (h1.comp (measurable_fst.prodMk hObm)).mul ((hbdm i).const_mul _)
  have hcz := s102_zeta_cont hm hN0 P X hXm hcont
  have hae : ∀ᵐ ζ ∂P, ∀ u ∈ Ioc (0 : ℝ) T, s102_cylA C m T s (HRS.Whole.withDensityReal ρ) P X
      (s102_tauk hT L) (s102_alk L) (fun x => Φ (s102_Lam T L x)) ζ u = F1 (u, ζ) := by
    filter_upwards [hcz] with ζ hc u hu
    have huT : u ∈ Icc (0 : ℝ) T := ⟨hu.1.le, hu.2⟩
    have hobs : s102_obs (s102_tauk hT L) (s102_alk L) (s102_Y C m T P X ζ u) = Ob (u, ζ) := by
      rw [← hObeq u hu.1.le ζ]
      ext i
      exact s102_obs_Y hS hP hlin hT hd1 hP0 hr hm hN0 P X hXm hmom L ζ hc huT i
    unfold s102_cylA
    simp only [hF1, hobs, if_pos huT]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    unfold s102_bdc
    rw [min_eq_left hu.2, if_pos hu.1.le]
    have hsq : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hN0)).ne'
    field_simp
  have hF1s : Measurable fun q : Ω × ℝ => F1 (q.2, q.1) := hF1m.comp measurable_swap
  have hint : Measurable fun ζ => ∫ u in Ioc 0 T, F1 (u, ζ) :=
    (hF1s.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) T))).measurable
  refine hint.aestronglyMeasurable.congr ?_
  filter_upwards [hae] with ζ h
  exact setIntegral_congr_fun measurableSet_Ioc (fun u hu => (h u hu).symm)

end HRS.MS.R2Interp

end
