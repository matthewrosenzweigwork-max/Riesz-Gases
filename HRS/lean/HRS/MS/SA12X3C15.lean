import HRS.MS.SA12X3C15M
import HRS.MS.SA12X3C9G
import HRS.MS.SA12X3C10

/-!
# S.A.12 C15 (SA12X3): `periodic_uloc_bound`

Cell energies `f z = cellEnergy` at the fine-lattice centres satisfy, for the periodic solution with zero source,
`∂_τ f z ≤ -ν D z + κ ∑_{k∈E₇} D (z+k) + A_gr ⨆ f` (C9 with `G = -perNonlocal`, C7 `periodic_nonlocal_regimes`, the mass term by
C12 `sa12x3_cellMass_le`), then the integral cell Gronwall bound (`sa12x3_cell_sup_dissipation_int`) and C10.
-/

set_option autoImplicit false
set_option maxHeartbeats 25600000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem periodic_uloc_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m) (Rg : PDE.Regime)
    (MB Λ ΛV νbar Cb T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C L₁ : ℝ, 0 < C ∧ ∀ (ν₀ L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (μ : ℝ → Euc d → ℝ)
      (V : Euc d → ℝ) (b : ℝ → Euc d → Euc d), L₁ ≤ L → PerData s m MB Λ ΛV νbar Cb T L γ M ν μ V b →
      RdRegimeHolds Rg d s M ν ν₀ → ∀ t ∈ Ioc (0 : ℝ) T, ∀ F : ℝ → Euc d → ℝ,
        IsPerSol m L γ M ν μ b (fun _ _ => 0) t F → ∀ τ ∈ Icc (0 : ℝ) t,
          ulocNormE m χ (F τ) ≤
            ENNReal.ofReal (C * Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ)) * ulocNormE m χ (F 0) := by
  obtain ⟨χh, hχp⟩ := sa12x3_cutoffPair hχ
  obtain ⟨E7, C7, CK, L₇, hE7, hC7, hCK, hNl⟩ := periodic_nonlocal_regimes hd s hs0 hsd m hm Rg MB Λ ΛV νbar Cb T χ χh hχp
  obtain ⟨E9, A9, hA9, h9⟩ := cell_local_operator hd m Cb T νbar χ χh hχp
  obtain ⟨c1, c2, hc1, hc2, h10⟩ := moving_uloc_equivalence hd m Cb T χ χh hχp
  obtain ⟨Nm, hNm, hmass⟩ := sa12x3_cellMass_le hd m χ hχ
  set a : ℝ := A9 * (E9.card : ℝ) with ha
  set b' : ℝ := (E7.card : ℝ) + CK * Nm with hb'
  have ha0 : 0 ≤ a := by positivity
  have hb'0 : 0 ≤ b' := by positivity
  refine ⟨Real.sqrt 2 * c2 / c1 + a + C7 * b' + 1, L₇, by positivity, ?_⟩
  intro ν₀ L γ M ν μ V b hL hPD hreg t ht F hF τ hτ
  set C : ℝ := Real.sqrt 2 * c2 / c1 + a + C7 * b' + 1 with hC
  have hT : 0 ≤ T := ht.1.le.trans ht.2
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hb := hPD.b_drift
  obtain ⟨k, hk1, hklam⟩ := sa12x3_lam_lin hreg (PDE.thetaOrder d s)
  obtain ⟨Ψ, hΨ⟩ := HRS.MS.UniqG2d.g2d_flow hT hb
  have hfl := HRS.MS.UniqC3.uc3_flowFacts hT hb hΨ
  have hsol := hF.sol
  set G : ℝ → Euc d → ℝ := fun τ y => -perNonlocal L γ M (μ τ) (F τ) y + (fun (_ : ℝ) (_ : Euc d) => (0 : ℝ)) τ y with hG
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hPD.hL
  obtain ⟨B, hB⟩ := sa12x3_uniform_jets hL0 m (fun j idx => hsol.contF j idx) hF.periodic
  obtain ⟨Be, hBe⟩ := sa12x3_cell_uniform hd m Cb T χ χh hχp t b Ψ hb hΨ htT F hB
  -- the data of the cell Gronwall lemma
  set f : (Fin d → ℤ) → ℝ → ℝ := fun z τ => cellEnergy m χ Ψ τ (cellPt d z) (F τ) with hf
  set D : (Fin d → ℤ) → ℝ → ℝ := fun z τ => cellDissip m χ Ψ τ (cellPt d z) (F τ) with hD
  set g : (Fin d → ℤ) → ℝ → ℝ := fun z τ => cellRate m χ Ψ τ (cellPt d z) ν (b τ) (F τ) (G τ) with hg
  set A7 : ℝ := Rg.lambdaM C7 ν₀ (PDE.thetaOrder d s) with hA7
  have hA7k : A7 = C7 * k := hklam C7
  have hA70 : 0 ≤ A7 := by rw [hA7k]; exact mul_nonneg hC7.le (by linarith)
  set Agr : ℝ := a + A7 * b' with hAgr
  have hAgr0 : 0 ≤ Agr := by positivity
  have hbddf : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t, f z τ ≤ Be := fun z τ hτ' => (hBe τ hτ' (cellPt d z)).1
  have hSle : ∀ τ' ∈ Icc (0 : ℝ) t, ∀ z, f z τ' ≤ ⨆ j, f j τ' := fun τ' hτ' z =>
    le_ciSup (⟨Be, by rintro _ ⟨j, rfl⟩; exact hbddf j τ' hτ'⟩ : BddAbove (range fun j => f j τ')) z
  have hderiv : ∀ z, ∀ τ' ∈ Icc (0 : ℝ) t, HasDerivWithinAt (f z) (g z τ') (Icc (0 : ℝ) t) τ' :=
    fun z τ' hτ' => cell_energy_derivative hd m Cb T χ χh hχp b Ψ hb hΨ ν G t htT F hsol (cellPt d z) τ' hτ'
  have hineq : ∀ z, ∀ τ' ∈ Icc (0 : ℝ) t, g z τ' ≤ -ν * D z τ' +
      nearSpill Rg ν₀ E7 * ∑ j ∈ E7.image (fun k => z + k), D j τ' + Agr * (⨆ j, f j τ') + (fun _ => (0 : ℝ)) τ' := by
    intro z τ' hτ'
    have hτ'T : τ' ∈ Icc (0 : ℝ) T := ⟨hτ'.1, hτ'.2.trans ht.2⟩
    have hbdd' : ∀ τ'' ∈ Icc (0 : ℝ) t, BddJets m (F τ'') := fun τ'' h => hF.bdd τ'' h
    have e9 := h9 b Ψ hb hΨ ν hPD.hν hPD.hν' G t htT F hsol hbdd' τ' hτ' z
    obtain ⟨Kc, hrow, hcol, hmain⟩ := hNl ν ν₀ L γ M ν μ V b hL hPD ⟨hPD.hM, hreg⟩ Ψ hΨ τ' hτ'T
    have e7 := hmain (F τ') (hF.bdd τ' hτ') (hF.periodic τ' hτ') z
    have hjp : 2 * jetPair m (advCutoff χ Ψ τ' (cellPt d z)) (F τ') (G τ') =
        -(2 * jetPair m (advCutoff χ Ψ τ' (cellPt d z)) (F τ') (fun x => perNonlocal L γ M (μ τ') (F τ') x)) := by
      have := sa12x3_jetPair_neg m (advCutoff χ Ψ τ' (cellPt d z)) (F τ') (fun x => perNonlocal L γ M (μ τ') (F τ') x)
      show 2 * jetPair m _ (F τ') (fun y => -perNonlocal L γ M (μ τ') (F τ') y + 0) = _
      rw [this]; ring
    rw [hjp] at e9
    set S : ℝ := ⨆ j, f j τ' with hSdef
    have hS0 : 0 ≤ S := (sa12x2_cellEnergy_nonneg m χ Ψ τ' (cellPt d 0) (F τ')).trans (hSle τ' hτ' 0)
    -- the neighbour sums
    have hsumE9 : ∑ k ∈ E9, cellEnergy m χ Ψ τ' (cellPt d (z + k)) (F τ') ≤ (E9.card : ℝ) * S := by
      calc _ ≤ ∑ _k ∈ E9, S := Finset.sum_le_sum fun k _ => hSle τ' hτ' (z + k)
        _ = _ := by simp
    have hsumE7 : ∑ k ∈ E7, cellEnergy m χ Ψ τ' (cellPt d (z + k)) (F τ') ≤ (E7.card : ℝ) * S := by
      calc _ ≤ ∑ _k ∈ E7, S := Finset.sum_le_sum fun k _ => hSle τ' hτ' (z + k)
        _ = _ := by simp
    -- the mass term
    have hΨc : Continuous (Ψ τ') := (hfl.contDiff τ' hτ'T).continuous
    have hΨi : Continuous (Function.invFun (Ψ τ')) := (hfl.contDiff_inv τ' hτ'T).continuous
    have hbij := hΨ.bij τ' hτ'T
    have hmz : ∀ z', cellMass m Ψ τ' z' (F τ') ≤ Nm * S := fun z' =>
      hmass Ψ τ' hbij hΨc hΨi (F τ') (hsol.smooth τ' hτ').1
        (fun z'' j idx => sa12x3_adv_cut_integrable hχp.1.1 hχp.1.2.1 hb hΨ hτ'T (cellPt d z'') (hsol.smooth τ' hτ').1 idx)
        S (fun z'' => hSle τ' hτ' z'') z'
    have hmassterm : (∑' z', (Kc z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ' z' (F τ'))).toReal ≤ CK * (Nm * S) := by
      have h1 : ∑' z', (Kc z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ' z' (F τ')) ≤
          ENNReal.ofReal CK * ENNReal.ofReal (Nm * S) := by
        calc _ ≤ ∑' z', (Kc z z' : ℝ≥0∞) * ENNReal.ofReal (Nm * S) :=
              ENNReal.tsum_le_tsum fun z' => by gcongr; exact hmz z'
          _ = (∑' z', (Kc z z' : ℝ≥0∞)) * ENNReal.ofReal (Nm * S) := ENNReal.tsum_mul_right
          _ ≤ ENNReal.ofReal CK * ENNReal.ofReal (Nm * S) := by
              gcongr
              exact le_trans (le_iSup (fun z => ∑' z', (Kc z z' : ℝ≥0∞)) z) hrow
      have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) h1
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCK, ENNReal.toReal_ofReal (by positivity)] at h2
    have hsumD : ∑ j ∈ E7.image (fun k => z + k), D j τ' = ∑ k ∈ E7, cellDissip m χ Ψ τ' (cellPt d (z + k)) (F τ') := by
      rw [Finset.sum_image (fun x _ y _ h => add_left_cancel h)]
    rw [hsumD]
    have hnonneg7 : 0 ≤ A7 := hA70
    have e7' : -(2 * jetPair m (advCutoff χ Ψ τ' (cellPt d z)) (F τ') (fun x => perNonlocal L γ M (μ τ') (F τ') x)) ≤
        nearSpill Rg ν₀ E7 * ∑ k ∈ E7, cellDissip m χ Ψ τ' (cellPt d (z + k)) (F τ') +
          A7 * ((E7.card : ℝ) * S + CK * (Nm * S)) := by
      refine e7.trans ?_
      gcongr
    have e9' : A9 * ∑ k ∈ E9, cellEnergy m χ Ψ τ' (cellPt d (z + k)) (F τ') ≤ a * S := by
      rw [ha, mul_assoc]; gcongr
    show cellRate m χ Ψ τ' (cellPt d z) ν (b τ') (F τ') (G τ') ≤ _
    have hAgrS : Agr * S = a * S + A7 * ((E7.card : ℝ) * S + CK * (Nm * S)) := by
      rw [hAgr, hb']; ring
    simp only [add_zero]
    nlinarith [e9, e7', e9', hAgrS]
  -- apply the cell Gronwall lemma
  have hgr := sa12x3_cell_sup_dissipation_int (ι := Fin d → ℤ) t Agr ν (nearSpill Rg ν₀ E7) E7.card hAgr0
    (sa12x3_spill_ok hPD.hν hreg E7).1 hPD.hν (sa12x3_spill_ok hPD.hν hreg E7).2
    (fun z => E7.image (fun k => z + k)) (fun z => Finset.card_image_le) f g D (fun _ => 0)
    (fun z τ' _ => sa12x2_cellEnergy_nonneg m χ Ψ τ' (cellPt d z) (F τ'))
    (fun z τ' _ => sa12x2_cellDissip_nonneg m χ Ψ τ' (cellPt d z) (F τ'))
    ⟨Be, fun z τ' hτ' => hbddf z τ' hτ'⟩
    (fun z => (sa12x3_cellDissip_cont hd m Cb T χ χh hχp b Ψ hb hΨ ν G t htT F hsol (cellPt d z)).integrableOn_Icc)
    ⟨Be * (volume (Icc (0 : ℝ) t)).toReal, fun z => by
      have := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ)) (s := Icc (0 : ℝ) t) (C := Be)
        measure_Icc_lt_top (f := D z) (fun σ hσ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sa12x2_cellDissip_nonneg m χ Ψ σ (cellPt d z) (F σ))]
          exact (hBe σ hσ (cellPt d z)).2)
      exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, Measure.real, mul_comm] using this)⟩
    (fun z => fun τ' hτ' => (hderiv z τ' hτ').continuousWithinAt)
    hderiv
    (fun z => sa12x3_cellRate_integrable hd m Cb T χ χh hχp b Ψ hb hΨ ν G t htT F hsol (cellPt d z))
    (fun _ _ => le_rfl) (integrableOn_const (by simp)) hineq
  -- back to the uloc norm
  have hτT : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.trans ht.2⟩
  have h0T : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hbddAt : ∀ τ' ∈ Icc (0 : ℝ) t, BddAbove (range fun j => f j τ') := fun τ' hτ' =>
    ⟨Be, by rintro _ ⟨j, rfl⟩; exact hbddf j τ' hτ'⟩
  have hcsle : ∀ τ' ∈ Icc (0 : ℝ) t, cellSup m χ Ψ τ' (F τ') ≤ ENNReal.ofReal (⨆ j, f j τ') := fun τ' hτ' =>
    iSup_le fun z => ENNReal.ofReal_le_ofReal (le_ciSup (hbddAt τ' hτ') z)
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht.1.le⟩
  have hcs0 : cellSup m χ Ψ 0 (F 0) ≤ ENNReal.ofReal Be :=
    iSup_le fun z => ENNReal.ofReal_le_ofReal (hbddf z 0 h00)
  have hS0le : ENNReal.ofReal (⨆ j, f j 0) ≤ cellSup m χ Ψ 0 (F 0) := by
    have hfin : cellSup m χ Ψ 0 (F 0) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcs0
    have : (⨆ j, f j 0) ≤ (cellSup m χ Ψ 0 (F 0)).toReal := by
      refine Real.iSup_le (fun z => ?_) ENNReal.toReal_nonneg
      have h1 : ENNReal.ofReal (f z 0) ≤ cellSup m χ Ψ 0 (F 0) := le_iSup (fun z : Fin d → ℤ =>
        ENNReal.ofReal (cellEnergy m χ Ψ 0 (cellPt d z) (F 0))) z
      have := ENNReal.toReal_mono hfin h1
      rwa [ENNReal.toReal_ofReal (sa12x2_cellEnergy_nonneg m χ Ψ 0 (cellPt d z) (F 0))] at this
    calc ENNReal.ofReal (⨆ j, f j 0) ≤ ENNReal.ofReal (cellSup m χ Ψ 0 (F 0)).toReal := ENNReal.ofReal_le_ofReal this
      _ = _ := ENNReal.ofReal_toReal hfin
  obtain ⟨hlow, -⟩ := h10 b Ψ hb hΨ τ hτT (F τ) (hF.bdd τ hτ)
  obtain ⟨-, hup⟩ := h10 b Ψ hb hΨ 0 h0T (F 0) (hF.bdd 0 h00)
  have hmain := sa12x3_conv hc1 hc2 hlow (hcsle τ hτ) (by simpa using hgr τ hτ) hS0le hup
  refine hmain.trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hCpos : 0 < C := by positivity
  have hlam : Rg.lambdaM C ν₀ (PDE.thetaOrder d s) = C * k := hklam C
  have hAle : Agr ≤ C * k := by
    rw [hAgr, hA7k, hb']
    have : a + C7 * k * b' ≤ (a + C7 * b') * k := by nlinarith [mul_nonneg ha0 (sub_nonneg.2 hk1)]
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (by rw [hC]; linarith [div_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hc2.le) hc1.le]) (by linarith)
  have hpre : c1⁻¹ * Real.sqrt 2 * c2 ≤ C := by
    have : c1⁻¹ * Real.sqrt 2 * c2 = Real.sqrt 2 * c2 / c1 := by ring
    rw [this, hC]; linarith [mul_nonneg ha0 le_rfl, mul_nonneg hC7.le hb'0]
  rw [hlam]
  calc c1⁻¹ * (Real.sqrt 2 * Real.exp (Agr * τ)) * c2 = (c1⁻¹ * Real.sqrt 2 * c2) * Real.exp (Agr * τ) := by ring
    _ ≤ C * Real.exp (C * k * τ) := by
        gcongr
        exact hτ.1

end HRS.MH.AdjointRd.Phase2SA12Construction
