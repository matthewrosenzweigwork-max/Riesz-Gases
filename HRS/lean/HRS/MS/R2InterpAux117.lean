import HRS.MS.R2InterpAux116

/-!
# S10.2 (worker S10R), part 117 (packet M3h): `ζ ↦ ∫ cylJ` is a.e.-measurable, and the full `hmeas` of `S102Rest`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MC.Sec7.PI

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}

set_option maxHeartbeats 3200000 in
theorem s102_cylJ_meas (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hS : S102Std C m T r c)
    (hlin : S102Lin C m T) (hP : (d : ℝ) < 2 * Pw) (hP0 : 0 ≤ Pw) (hr : (d : ℝ) / 2 < r) (hm : (d : ℝ) < m)
    (hT : 0 < T) (L : ℕ) {β p K M Lr : ℝ} (hβ : 0 < β) (hp : 1 < p) {ρ : Euc d → ℝ}
    (hρR : IsRound2Density d s M Lr ρ) {N : ℕ} (hN : 2 ≤ N) {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsProgressive ℱ (ofNNRealTime X)) (hXm : ∀ t, Measurable (X t))
    (hcont : ∀ᵐ ζ ∂P, ∀ k, Continuous fun t : ℝ≥0 => X t ζ k)
    (hdens : ∀ r ∈ Icc (0 : ℝ) T, HasR2ActualDensity s β p K (HRS.Whole.withDensityReal ρ) (P.map (X r.toNNReal)))
    (hmom : ∀ u ∈ Icc (0 : ℝ) T, Integrable (fun x : Euc d => jbracket x ^ Pw)
      (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))))
    (hμ : ∀ u ∈ Icc (0 : ℝ) T, ∀ g : Euc d → ℝ, HRS.Whole.pair (HRS.Whole.withDensityReal ρ) g = ∫ x, g x * C.ρ u x)
    (γ : ℝ → Measure (OscPath d m T)) (hγ : ∀ u ∈ Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u))
    {Φ : OscPath d m T → ℝ} (hΦ : MemCb 5 Φ) :
    AEStronglyMeasurable (fun ζ => ∫ u in Ioc 0 T, s102_cylJ C m T (HRS.Whole.withDensityReal ρ) P X
      (s102_tauk hT L) (s102_alk L) (fun x => Φ (s102_Lam T L x)) ζ u) P := by
  classical
  have hN0 : 0 < N := by omega
  have hd1 : 1 ≤ d := by omega
  haveI hμp : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.MS.R2Mt.s92_isProb_mu hρR.prob
  set μ := HRS.Whole.withDensityReal ρ with hμdef
  have hG5 : MemCb 5 (fun x => Φ (s102_Lam T L x)) := (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof (s102_Lam T L) hΦ).1
  have hG2 : MemCb 2 (fun x => Φ (s102_Lam T L x)) := ⟨hG5.1.of_le (by norm_num), fun j hj => hG5.2 j (by omega)⟩
  have hGi := s102_gramInt hS hT L
  have hXjm : ∀ t ∈ Icc (0 : ℝ) T, Measurable fun q : ℝ × Ω => X (min q.1 t).toNNReal q.2 := fun t _ =>
    measurable_progressive_min_gen (u := ofNNRealTime X) hX t
  obtain ⟨Ob, hObm, hObeq⟩ := s102_obsY_jmeas hS hT L hN0 P X hXm hXjm
  -- the gradient fields of the observations
  set Gv : Fin (s102_q d L) → ℝ × Euc d → Euc d := fun i p =>
    if p.1 ∈ Icc (0 : ℝ) (s102_tk hT L i) then gradient (s102_orb C m hT L i p.1) p.2 else 0 with hGv
  have hGvm : ∀ i, Measurable (Gv i) := fun i => s102_gradJoint_meas (s102_orb_classical hS hT L i)
  set G2 : Fin (s102_q d L) → Fin (s102_q d L) → ℝ × Euc d → ℝ := fun i j p => inner ℝ (Gv i p) (Gv j p) with hG2d
  have hG2m : ∀ i j, Measurable (G2 i j) := fun i j => (hGvm i).inner (hGvm j)
  set hh2m : Fin (s102_q d L) → Fin (s102_q d L) → ℝ × Ω → ℝ := fun i j q =>
    if q.1 ≤ min (s102_tk hT L i) (s102_tk hT L j) then
      Real.sqrt N * ((N : ℝ)⁻¹ * ∑ k, G2 i j (q.1, X (min q.1 T).toNNReal q.2 k) - ∫ x, G2 i j (q.1, x) ∂μ)
    else 0 with hhh
  have hhm : ∀ i j, Measurable (hh2m i j) := by
    intro i j
    refine Measurable.ite (measurableSet_le measurable_fst measurable_const) ?_ measurable_const
    refine (((measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)).sub ?_)).const_mul _
    · exact (hG2m i j).comp (measurable_fst.prodMk ((measurable_pi_apply k).comp (hXjm T ⟨hT.le, le_rfl⟩)))
    · exact ((hG2m i j).stronglyMeasurable.integral_prod_right' (ν := μ)).measurable.comp measurable_fst
  set F2 : ℝ × Ω → ℝ := fun q => ∑ i : Fin (s102_q d L), ∑ j : Fin (s102_q d L),
    (if q.1 ∈ Icc (0 : ℝ) T then iteratedFDeriv ℝ 2 (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L))
        (fun x => Φ (s102_Lam T L x)) q.1) (Ob q) ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] else 0) *
      (2 * C.ν * hh2m i j q) with hF2
  have hF2m : Measurable F2 := by
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    exact ((s102_heatD2_meas hT L hGi γ hγ hG2 i j).comp (measurable_fst.prodMk hObm)).mul
      (((hhm i j)).const_mul _)
  have hcz := s102_zeta_cont hm hN0 P X hXm hcont
  have hae : ∀ᵐ ζ ∂P, ∀ u ∈ Ioc (0 : ℝ) T, s102_cylJ C m T μ P X (s102_tauk hT L) (s102_alk L)
      (fun x => Φ (s102_Lam T L x)) ζ u = F2 (u, ζ) := by
    filter_upwards [hcz] with ζ hc u hu
    have huT : u ∈ Icc (0 : ℝ) T := ⟨hu.1.le, hu.2⟩
    have hobs : s102_obs (s102_tauk hT L) (s102_alk L) (s102_Y C m T P X ζ u) = Ob (u, ζ) := by
      rw [← hObeq u hu.1.le ζ]
      ext i
      exact s102_obs_Y hS hP hlin hT hd1 hP0 hr hm hN0 P X hXm hmom L ζ hc huT i
    unfold s102_cylJ
    simp only [hF2, hobs, if_pos huT]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    unfold s102_hh2
    by_cases hle : u ≤ min (s102_tk hT L i) (s102_tk hT L j)
    · have hle' : u ∈ Iic (min (s102_tauk hT L i : ℝ) (s102_tauk hT L j : ℝ)) := hle
      rw [indicator_of_mem hle']
      simp only [hhh, if_pos hle]
      have hi : u ∈ Icc (0 : ℝ) (s102_tk hT L i) := ⟨hu.1.le, hle.trans (min_le_left _ _)⟩
      have hj : u ∈ Icc (0 : ℝ) (s102_tk hT L j) := ⟨hu.1.le, hle.trans (min_le_right _ _)⟩
      have hg : (fun x => inner ℝ (gradient (propagatorW C u (s102_tauk hT L i) (oscTestFun m (s102_alk L i))) x)
          (gradient (propagatorW C u (s102_tauk hT L j) (oscTestFun m (s102_alk L j))) x)) = fun x => G2 i j (u, x) := by
        funext x
        simp only [hG2d, hGv, if_pos hi, if_pos hj, s102_orb]
        rfl
      rw [hg]
      simp only [s102_etaf, HRS.Whole.pair_empirical hN0, min_eq_left hu.2]
      rfl
    · have hle' : u ∉ Iic (min (s102_tauk hT L i : ℝ) (s102_tauk hT L j : ℝ)) := hle
      rw [indicator_of_notMem hle']
      simp only [hhh, if_neg hle]
  have hF2s : Measurable fun q : Ω × ℝ => F2 (q.2, q.1) := hF2m.comp measurable_swap
  have hint : Measurable fun ζ => ∫ u in Ioc 0 T, F2 (u, ζ) :=
    (hF2s.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) T))).measurable
  refine hint.aestronglyMeasurable.congr ?_
  filter_upwards [hae] with ζ h
  exact setIntegral_congr_fun measurableSet_Ioc (fun u hu => (h u hu).symm)

end HRS.MS.R2Interp

end
