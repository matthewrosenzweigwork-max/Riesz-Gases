import HRS.MS.R2InterpAux100

/-!
# S10.2 (worker S10R), part 101 (packet F5): `S102ItoRep` for the particle system (the Itô representation of the observations)
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.CovMeas

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
set_option maxSynthPendingDepth 3 in
theorem s102_itoRep (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {T : ℝ} (hT : 0 < T) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → EucConfig d N)
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P (quadraticGradientDyn d s a β) T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (hneg : ∀ t : ℝ, t ≤ 0 → ℱ t = ℱ 0) {M Lr p K : ℝ} (hp : 1 < p) (hρR : IsRound2Density d s M Lr ρ)
    (hdens : ∀ r ∈ Icc (0 : ℝ) T, HasR2ActualDensity s β p K (HRS.Whole.withDensityReal ρ) (P.map (X r.toNNReal)))
    {m : ℝ} (hm : (d : ℝ) < m) {r : ℕ} {c : MultiIndex d → ℝ}
    (hS : S102Std ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) m T r c)
    (hlin : S102Lin ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) m T) {Pw : ℝ} (hP : (d : ℝ) < 2 * Pw)
    (hP0 : 0 ≤ Pw) (hr : (d : ℝ) / 2 < r)
    (hmom : ∀ u ∈ Icc (0 : ℝ) T, Integrable (fun x : Euc d => jbracket x ^ Pw)
      (HRS.Whole.meanEmpirical (P.map (X u.toNNReal)))) (L : ℕ) :
    S102ItoRep ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) m T s (HRS.Whole.withDensityReal ρ) hT L P X ℱ W' := by
  classical
  set D := quadraticGradientDyn d s a β with hD
  set C := D.coeff (fun _ => ρ) with hC
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hN0 : 0 < N := by omega
  have hd1 : 1 ≤ d := by omega
  have hXm : ∀ t, Measurable (X t) := hX.adapted
  have hXprog : IsProgressive ℱ (ofNNRealTime X) := hF.progressive
  have hbdE := s102_bdE_locL1 (C := C) hd hs0 hs hS hT L hβ hp hρR hN P X hXprog hdens
  have hΦE := s102_PhicE_locL2 hS hT L P X hXprog
  refine ⟨s102_bdE C m hT L s μ P X, s102_PhicE C m hT L X, hbdE, hΦE, ?_, ?_, ?_, ?_⟩
  · -- measurability of the initial observation
    intro t
    have hle : ℱ 0 ≤ ℱ t := by
      rcases le_total 0 t with h | h
      · exact ℱ.mono h
      · exact le_of_eq (hneg t h).symm
    have hfun : (fun ζ => s102_obs (s102_tauk hT L) (s102_alk L) (s102_y0 C m T P X ζ)) =
        fun ζ => (EuclideanSpace.equiv (Fin (s102_q d L)) ℝ).symm
          (fun i => s102_zf P X ζ 0 (s102_orb C m hT L i 0)) := by
      funext ζ
      ext i
      exact s102_obs_y0 hS hP hlin hT hd1 hP0 hr hN0 P X (by simpa using hmom 0 ⟨le_rfl, hT.le⟩) L ζ i
    rw [hfun]
    refine (EuclideanSpace.equiv (Fin (s102_q d L)) ℝ).symm.continuous.measurable.comp
      ((@measurable_pi_iff _ _ _ (ℱ t) _).2 fun i => ?_)
    have hg : Measurable (s102_orb C m hT L i 0) :=
      ((s102_orb_classical hS hT L i).c2 0 ⟨le_rfl, (s102_tauk hT L i).2.1⟩).continuous.measurable
    have h0 : Measurable[ℱ 0] (X 0) := hF.adapted 0
    have h1 : Measurable[ℱ 0] fun ζ => HRS.Whole.pair (HRS.Whole.empirical (X 0 ζ)) (s102_orb C m hT L i 0) :=
      @Measurable.comp _ _ _ (ℱ 0) _ _ _ _ (s102_pairEmp_meas hN0 hg) h0
    have h2 : Measurable[ℱ t] fun ζ => s102_zf P X ζ 0 (s102_orb C m hT L i 0) := by
      have := ((h1.mono hle le_rfl).sub (@measurable_const _ _ _ (ℱ t)
        (HRS.Whole.pair (HRS.Whole.meanEmpirical (P.map (X 0))) (s102_orb C m hT L i 0)))).const_mul (Real.sqrt N)
      simpa [s102_zf, Real.toNNReal_zero] using this
    exact h2
  · intro u ζ i hu
    simp only [s102_bdE, s102_bdc, if_pos hu]
    rfl
  · intro u ζ k i hu
    exact s102_PhicE_form C m hT L X u hu ζ k i
  · have hcontz := s102_zeta_cont hm hN0 P X hXm hX.cont
    have horb : ∀ i : Fin (s102_q d L), ∀ᵐ ζ ∂P, ∀ τ' ∈ Icc (0 : ℝ) (s102_tk hT L i),
        s102_zf P X ζ τ' (s102_orb C m hT L i τ') = s102_zf P X ζ 0 (s102_orb C m hT L i 0) +
          (Real.sqrt N * (Real.sqrt (2 * β⁻¹) / N)) *
            itoIntegral P ℱ W' (s102_Ig (s102_orb C m hT L i) (s102_tk hT L i) X) τ' ζ +
          ∫ r in Icc (0 : ℝ) τ', (-(Real.sqrt N)⁻¹ * r2QuadField s μ P X r ζ (s102_orb C m hT L i r)) := fun i =>
      s102_orbit_zeta hd hs0 hs ha hβ hρ hT.le hN P X₀ W X hX ℱ W' hF hp hρR hdens (s102_tauk hT L i).2 m
        (s102_alk L i) (hS.hcls (s102_alk L i) _ (s102_tauk hT L i).2)
    have hloc := fun i : Fin (s102_q d L) => s102_loc_coord hS hT L P hF.brownian X hXprog i
    have hbdint := fun i : Fin (s102_q d L) =>
      (s102_bdc_prog_int hd hs0 hs hS hT L hβ hp hρR hN P X hXprog hdens i).2
    filter_upwards [hcontz, ae_all_iff.2 horb, ae_all_iff.2 hloc, ae_all_iff.2 hbdint] with ζ hc ho hl hb u hu
    ext i
    have hτ := (s102_tauk hT L i).2
    have hτ' : min u (s102_tk hT L i) ∈ Icc (0 : ℝ) (s102_tk hT L i) :=
      ⟨le_min hu.1 hτ.1, min_le_right _ _⟩
    have e0 := s102_obs_Y hS hP hlin hT hd1 hP0 hr hm hN0 P X hXm hmom L ζ hc hu i
    have e1 := ho i _ hτ'
    have e2 := s102_obs_y0 hS hP hlin hT hd1 hP0 hr hN0 P X (by simpa using hmom 0 ⟨le_rfl, hT.le⟩) L ζ i
    have e3 := s102_bd_integral_coord (C := C) (m := m) hT L s μ P X ζ u (fun j => hb j u) i
    have e3' := s102_bdc_integral (C := C) (m := m) hT L s μ P X ζ hu.1 i
    obtain ⟨e4, e5⟩ := hl i u
    show (s102_obs (s102_tauk hT L) (s102_alk L) (s102_Y C m T P X ζ u)) i =
      (s102_obs (s102_tauk hT L) (s102_alk L) (s102_y0 C m T P X ζ) +
        (∫ s' in Icc 0 u, s102_bdE C m hT L s μ P X s' ζ) +
        localItoIntegralE P ℱ W' (s102_PhicE C m hT L X) u ζ) i
    rw [PiLp.add_apply, PiLp.add_apply, e0, e2, e3, e3', e4, e5]
    refine e1.trans ?_
    have hν : C.ν = β⁻¹ := rfl
    rw [hν]
    ring


end HRS.MS.R2Interp

end
