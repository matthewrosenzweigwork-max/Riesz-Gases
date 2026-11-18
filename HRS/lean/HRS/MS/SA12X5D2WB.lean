import HRS.MS.SA12X4W6
import HRS.MS.SA12X4D1
import HRS.MS.SA12X5D2A
import HRS.MS.SA12X5D2WA

/-!
# S.A.12 X5 D2WB: the weighted cell energy bound for a periodic solution with a source term

`sa12x5_periodic_cellWeighted_src` is `sa12x4_periodic_cellWeighted` (SA12X4W6) with a source: for a periodic solution with source
`Sc`, zero datum and `∑_z ω_z 𝓕_z(Sc σ) ≤ Hf σ`, `cellWeighted (F τ) ≤ C e^{2Λτ} τ ∫₀^τ Hf`.  The source pairing is handled by
Young (d1) with `ε = 1/τ`, the weighted Gronwall lemma by `sa12x5_weighted_gronwall_src`.
-/

set_option autoImplicit false
set_option maxHeartbeats 25600000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12
  HRS.MH.AdjointRd.Phase2SA12Near HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12X4

variable {d : ℕ}

theorem sa12x5_periodic_cellWeighted_src (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Rg : PDE.Regime) (MB Λ ΛV νbar Cb T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C L₁ : ℝ, 0 < C ∧ ∀ (ν₀ L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (μ : ℝ → Euc d → ℝ)
      (V : Euc d → ℝ) (b : ℝ → Euc d → Euc d), L₁ ≤ L → PerData s m MB Λ ΛV νbar Cb T L γ M ν μ V b →
      RdRegimeHolds Rg d s M ν ν₀ → ∀ t ∈ Ioc (0 : ℝ) T, ∀ (Sc F : ℝ → Euc d → ℝ),
        IsPerSol m L γ M ν μ b Sc t F → (∀ τ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (Sc τ)) →
        F 0 = (fun _ => (0 : ℝ)) → ∀ Hf : ℝ → ℝ, (∀ σ ∈ Icc (0 : ℝ) t, 0 ≤ Hf σ) →
        IntegrableOn Hf (Icc (0 : ℝ) t) →
        ∀ Ψ : ℝ → Euc d → Euc d, IsNegDriftFlow T b Ψ →
        (∀ σ ∈ Icc (0 : ℝ) t, ∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
          ENNReal.ofReal (cellEnergy m χ Ψ σ (cellPt d z) (Sc σ)) ≤ ENNReal.ofReal (Hf σ)) →
        ∀ τ ∈ Icc (0 : ℝ) t,
          cellWeighted m χ Ψ τ (F τ) ≤
            ENNReal.ofReal (C * Real.exp (2 * Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ) * τ *
              ∫ σ in Icc (0 : ℝ) τ, Hf σ) := by
  classical
  obtain ⟨χh, hχp⟩ := sa12x3_cutoffPair hχ
  obtain ⟨E7, C7, CK, L₇, hE7, hC7, hCK, hNl⟩ := periodic_nonlocal_regimes hd s hs0 hsd m hm Rg MB Λ ΛV νbar Cb T χ χh hχp
  obtain ⟨E9, A9, hA9, h9⟩ := cell_local_operator hd m Cb T νbar χ χh hχp
  obtain ⟨c7, hc7, hsh7⟩ := sa12x4_shift_weight E7
  obtain ⟨c9, hc9, hsh9⟩ := sa12x4_shift_weight E9
  obtain ⟨C12, hC12, hmassW⟩ := sa12x4_cellMass_weighted hd m χ hχ
  set Kw : ℝ := (⌈Real.sqrt d⌉ : ℝ) ^ ((d : ℝ) + 3) with hKw
  have hκ1 : (1 : ℝ) ≤ (⌈Real.sqrt d⌉ : ℝ) := sa12c12_kappa_ge hd
  have hKw0 : 0 ≤ Kw := Real.rpow_nonneg (by linarith) _
  set θ : ℝ := PDE.thetaOrder d s with hθ
  set q : ℝ := 1 / (1 + c7) with hq
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq1 : q ≤ 1 := by rw [hq, div_le_one (by linarith)]; linarith
  set Kq : ℝ := max 1 (q ^ (-(θ / (2 - θ)))) with hKq
  have hKq1 : 1 ≤ Kq := le_max_left _ _
  set Bc : ℝ := A9 * c9 + Kq * C7 * (c7 + Kw * CK * C12) with hBc
  have hBc0 : 0 ≤ Bc := by rw [hBc]; positivity
  set C : ℝ := Bc + Real.exp 1 + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; have := Real.exp_pos 1; linarith
  refine ⟨C, L₇, hCpos, ?_⟩
  intro ν₀ L γ M ν μ V b hL hPD hR t ht Sc F hF hSs hF0 Hf hHf0 hHfi Ψ hΨ hHf τ hτ
  obtain ⟨ε, hε0, hετ⟩ : ∃ ε : ℝ, 0 < ε ∧ (τ = 0 ∨ ε * τ = 1) := by
    by_cases h0 : τ = 0
    · exact ⟨1, one_pos, Or.inl h0⟩
    · exact ⟨τ⁻¹, inv_pos.2 (lt_of_le_of_ne hτ.1 (Ne.symm h0)), Or.inr (inv_mul_cancel₀ h0)⟩
  have hT : 0 ≤ T := ht.1.le.trans ht.2
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hb := hPD.b_drift
  obtain ⟨k0, hk01, hk0lam⟩ := sa12x3_lam_lin hR θ
  obtain ⟨hR', hrate⟩ := sa12x4_regime_scale hR hq0 hq1 θ
  obtain ⟨k1, hk11, hk1lam⟩ := sa12x3_lam_lin hR' θ
  have hfl := HRS.MS.UniqC3.uc3_flowFacts hT hb hΨ
  have hsol := hF.sol
  set G : ℝ → Euc d → ℝ := fun τ y => -perNonlocal L γ M (μ τ) (F τ) y + Sc τ y with hG
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hPD.hL
  obtain ⟨B, hB⟩ := sa12x3_uniform_jets hL0 m (fun j idx => hsol.contF j idx) hF.periodic
  obtain ⟨Be, hBe⟩ := sa12x3_cell_uniform hd m Cb T χ χh hχp t b Ψ hb hΨ htT F hB
  -- the data of the weighted Gronwall lemma
  set f : (Fin d → ℤ) → ℝ → ℝ := fun z τ => cellEnergy m χ Ψ τ (cellPt d z) (F τ) with hf
  set D : (Fin d → ℤ) → ℝ → ℝ := fun z τ => cellDissip m χ Ψ τ (cellPt d z) (F τ) with hD
  set g : (Fin d → ℤ) → ℝ → ℝ := fun z τ => cellRate m χ Ψ τ (cellPt d z) ν (b τ) (F τ) (G τ) with hg
  set A7 : ℝ := Rg.lambdaM C7 (q * ν₀) θ with hA7
  have hA7k : A7 = C7 * k1 := hk1lam C7
  have hA70 : 0 ≤ A7 := by rw [hA7k]; exact mul_nonneg hC7.le (by linarith)
  set κ' : ℝ := nearSpill Rg (q * ν₀) E7 with hκ'
  obtain ⟨hκ'0, hκ'c⟩ := sa12x4_spill_weighted hPD.hν hR E7 hc7
  have hbddf : ∀ z, ∀ τ ∈ Icc (0 : ℝ) t, f z τ ≤ Be := fun z τ hτ' => (hBe τ hτ' (cellPt d z)).1
  have hderiv : ∀ z, ∀ τ' ∈ Icc (0 : ℝ) t, HasDerivWithinAt (f z) (g z τ') (Icc (0 : ℝ) t) τ' :=
    fun z τ' hτ' => cell_energy_derivative hd m Cb T χ χh hχp b Ψ hb hΨ ν G t htT F hsol (cellPt d z) τ' hτ'
  -- the per-time cell inequality (with the nonlocal coefficients chosen per time)
  have hKc : ∀ τ' : ℝ, ∃ Kc : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0, τ' ∈ Icc (0 : ℝ) t →
      (∀ z', ∑' z, ENNReal.ofReal (cellWeight d z) * (Kc z z' : ℝ≥0∞) ≤
        ENNReal.ofReal CK * ENNReal.ofReal (cellWeight d z')) ∧
      ∀ z, g z τ' + ν * D z τ' ≤ A9 * ∑ k ∈ E9, f (z + k) τ' + κ' * ∑ k ∈ E7, D (z + k) τ' +
        A7 * (∑ k ∈ E7, f (z + k) τ') +
        A7 * (∑' z', (Kc z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ' z' (F τ'))).toReal +
        ε * f z τ' + ε⁻¹ * cellEnergy m χ Ψ τ' (cellPt d z) (Sc τ') := by
    intro τ'
    by_cases hτ' : τ' ∈ Icc (0 : ℝ) t
    · have hτ'T : τ' ∈ Icc (0 : ℝ) T := ⟨hτ'.1, hτ'.2.trans ht.2⟩
      obtain ⟨Kc, hrow, hcol, hmain⟩ := hNl ν (q * ν₀) L γ M ν μ V b hL hPD ⟨hPD.hM, hR'⟩ Ψ hΨ τ' hτ'T
      refine ⟨Kc, fun _ => ⟨hcol, fun z => ?_⟩⟩
      have hbdd' : ∀ τ'' ∈ Icc (0 : ℝ) t, BddJets m (F τ'') := fun τ'' h => hF.bdd τ'' h
      have e9 := h9 b Ψ hb hΨ ν hPD.hν hPD.hν' G t htT F hsol hbdd' τ' hτ' z
      have hwc : Continuous (advCutoff χ Ψ τ' (cellPt d z)) :=
        hχp.1.1.continuous.comp ((hfl.contDiff_inv τ' hτ'T).continuous.sub continuous_const)
      have hwk : HasCompactSupport (advCutoff χ Ψ τ' (cellPt d z)) :=
        sa12x2_advCutoff_hasCompactSupport hT hb hΨ hτ'T hχp.1.2.1 _
      have hNs : ContDiff ℝ ∞ (fun x => perNonlocal L γ M (μ τ') (F τ') x) := by
        have e : (fun x => perNonlocal L γ M (μ τ') (F τ') x) = fun x => Sc τ' x - G τ' x := by
          funext x; simp only [hG]; ring
        rw [e]
        exact (hSs τ' hτ').sub (hsol.smooth τ' hτ').2
      have hjp : 2 * jetPair m (advCutoff χ Ψ τ' (cellPt d z)) (F τ') (G τ') =
          -(2 * jetPair m (advCutoff χ Ψ τ' (cellPt d z)) (F τ') (fun x => perNonlocal L γ M (μ τ') (F τ') x)) +
            2 * jetPair m (advCutoff χ Ψ τ' (cellPt d z)) (F τ') (Sc τ') := by
        have := sa12x5_jetPair_split m hwc hwk (hsol.smooth τ' hτ').1 hNs (hSs τ' hτ')
        show 2 * jetPair m _ (F τ') (fun y => -perNonlocal L γ M (μ τ') (F τ') y + Sc τ' y) = _
        rw [this]; ring
      have hyoung := HRS.MH.AdjointRd.Phase2SA12X4.sa12x4_jetPair_young m hwc (hsol.smooth τ' hτ').1 (hSs τ' hτ')
        (fun {j} _ idx => sa12x3_adv_cut_integrable hχp.1.1 hχp.1.2.1 hb hΨ hτ'T (cellPt d z) (hsol.smooth τ' hτ').1 idx)
        (fun {j} _ idx => sa12x3_adv_cut_integrable hχp.1.1 hχp.1.2.1 hb hΨ hτ'T (cellPt d z) (hSs τ' hτ') idx)
        hε0
      have hyoung' : 2 * jetPair m (advCutoff χ Ψ τ' (cellPt d z)) (F τ') (Sc τ') ≤
          ε * f z τ' + ε⁻¹ * cellEnergy m χ Ψ τ' (cellPt d z) (Sc τ') := hyoung
      rw [hjp] at e9
      have e7 := hmain (F τ') (hF.bdd τ' hτ') (hF.periodic τ' hτ') z
      have e9' : cellRate m χ Ψ τ' (cellPt d z) ν (b τ') (F τ') (G τ') ≤ -ν * D z τ' +
          A9 * ∑ k ∈ E9, f (z + k) τ' + (-(2 * jetPair m (advCutoff χ Ψ τ' (cellPt d z)) (F τ')
            (fun x => perNonlocal L γ M (μ τ') (F τ') x)) +
            2 * jetPair m (advCutoff χ Ψ τ' (cellPt d z)) (F τ') (Sc τ')) := by
        simpa [hD, hf] using e9
      have hgz : g z τ' = cellRate m χ Ψ τ' (cellPt d z) ν (b τ') (F τ') (G τ') := rfl
      rw [hgz]
      have e7' : -(2 * jetPair m (advCutoff χ Ψ τ' (cellPt d z)) (F τ') (fun x => perNonlocal L γ M (μ τ') (F τ') x)) ≤
          κ' * ∑ k ∈ E7, D (z + k) τ' + A7 * (∑ k ∈ E7, f (z + k) τ' +
            (∑' z', (Kc z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ' z' (F τ'))).toReal) := by
        simpa [hD, hf, hκ', hA7] using e7
      nlinarith [e9', e7', hyoung']
    · exact ⟨fun _ _ => 0, fun h => absurd h hτ'⟩
  choose Kc hKc using hKc
  -- the rate term of each cell (without the source)
  set r0 : (Fin d → ℤ) → ℝ → ℝ≥0∞ := fun z τ' =>
    ENNReal.ofReal (A9 * ∑ k ∈ E9, f (z + k) τ') + ENNReal.ofReal (κ' * ∑ k ∈ E7, D (z + k) τ') +
      ENNReal.ofReal (A7 * ∑ k ∈ E7, f (z + k) τ') +
        ENNReal.ofReal A7 * ∑' z', (Kc τ' z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ' z' (F τ')) with hr0
  set r : (Fin d → ℤ) → ℝ → ℝ≥0∞ := fun z τ' =>
    r0 z τ' + ENNReal.ofReal (ε * f z τ') +
      ENNReal.ofReal (ε⁻¹ * cellEnergy m χ Ψ τ' (cellPt d z) (Sc τ')) with hr
  have hfnn : ∀ z, ∀ τ' ∈ Icc (0 : ℝ) t, 0 ≤ f z τ' := fun z τ' _ => sa12x2_cellEnergy_nonneg m χ Ψ τ' (cellPt d z) (F τ')
  have hDnn : ∀ z, ∀ τ' ∈ Icc (0 : ℝ) t, 0 ≤ D z τ' := fun z τ' _ => sa12x2_cellDissip_nonneg m χ Ψ τ' (cellPt d z) (F τ')
  have hhz0 : ∀ z τ', 0 ≤ cellEnergy m χ Ψ τ' (cellPt d z) (Sc τ') :=
    fun z τ' => sa12x2_cellEnergy_nonneg m χ Ψ τ' (cellPt d z) (Sc τ')
  set a : ℝ := A9 * c9 + A7 * (c7 + Kw * CK * C12) with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hgr := sa12x5_weighted_gronwall_src (ι := Fin d → ℤ) t ν (κ' * c7) (a + ε) ht.1.le hPD.hν (mul_nonneg hκ'0 hc7) hκ'c
    (by linarith)
    (fun z => ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3)))) (sa12x4_wt_tsum_lt_top hd)
    f g D r hfnn hDnn ⟨Be, fun z τ hτ' => hbddf z τ hτ'⟩
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
    (fun σ => ε⁻¹ * Hf σ) (fun σ hσ => mul_nonneg (inv_nonneg.2 hε0.le) (hHf0 σ hσ)) (hHfi.const_mul ε⁻¹)
    (fun z τ' hτ' => by
      obtain ⟨-, hz⟩ := hKc τ' hτ'
      have h1 := hz z
      have hx1 : 0 ≤ A9 * ∑ k ∈ E9, f (z + k) τ' := mul_nonneg hA9 (Finset.sum_nonneg fun k _ => hfnn _ τ' hτ')
      have hx2 : 0 ≤ κ' * ∑ k ∈ E7, D (z + k) τ' := mul_nonneg hκ'0 (Finset.sum_nonneg fun k _ => hDnn _ τ' hτ')
      have hx3 : 0 ≤ A7 * ∑ k ∈ E7, f (z + k) τ' := mul_nonneg hA70 (Finset.sum_nonneg fun k _ => hfnn _ τ' hτ')
      have hbase : ENNReal.ofReal (A9 * ∑ k ∈ E9, f (z + k) τ' + κ' * ∑ k ∈ E7, D (z + k) τ' +
              A7 * (∑ k ∈ E7, f (z + k) τ') +
              A7 * (∑' z', (Kc τ' z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ' z' (F τ'))).toReal) ≤ r0 z τ' := by
        calc ENNReal.ofReal (A9 * ∑ k ∈ E9, f (z + k) τ' + κ' * ∑ k ∈ E7, D (z + k) τ' +
              A7 * (∑ k ∈ E7, f (z + k) τ') +
              A7 * (∑' z', (Kc τ' z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ' z' (F τ'))).toReal)
            ≤ ENNReal.ofReal (A9 * ∑ k ∈ E9, f (z + k) τ' + κ' * ∑ k ∈ E7, D (z + k) τ' +
              A7 * (∑ k ∈ E7, f (z + k) τ')) +
            ENNReal.ofReal (A7 * (∑' z', (Kc τ' z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ' z' (F τ'))).toReal) :=
            ENNReal.ofReal_add_le
          _ ≤ r0 z τ' := by
            refine add_le_add ?_ ?_
            · rw [ENNReal.ofReal_add (add_nonneg hx1 hx2) hx3, ENNReal.ofReal_add hx1 hx2]
            · rw [ENNReal.ofReal_mul hA70]
              gcongr
              exact ENNReal.ofReal_toReal_le
      calc ENNReal.ofReal (g z τ' + ν * D z τ')
          ≤ ENNReal.ofReal ((A9 * ∑ k ∈ E9, f (z + k) τ' + κ' * ∑ k ∈ E7, D (z + k) τ' +
              A7 * (∑ k ∈ E7, f (z + k) τ') +
              A7 * (∑' z', (Kc τ' z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ' z' (F τ'))).toReal) +
              ε * f z τ' + ε⁻¹ * cellEnergy m χ Ψ τ' (cellPt d z) (Sc τ')) := ENNReal.ofReal_le_ofReal h1
        _ ≤ ENNReal.ofReal ((A9 * ∑ k ∈ E9, f (z + k) τ' + κ' * ∑ k ∈ E7, D (z + k) τ' +
              A7 * (∑ k ∈ E7, f (z + k) τ') +
              A7 * (∑' z', (Kc τ' z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ' z' (F τ'))).toReal) +
              ε * f z τ') + ENNReal.ofReal (ε⁻¹ * cellEnergy m χ Ψ τ' (cellPt d z) (Sc τ')) :=
            ENNReal.ofReal_add_le
        _ ≤ (ENNReal.ofReal (A9 * ∑ k ∈ E9, f (z + k) τ' + κ' * ∑ k ∈ E7, D (z + k) τ' +
              A7 * (∑ k ∈ E7, f (z + k) τ' ) +
              A7 * (∑' z', (Kc τ' z z' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ' z' (F τ'))).toReal) +
              ENNReal.ofReal (ε * f z τ')) + ENNReal.ofReal (ε⁻¹ * cellEnergy m χ Ψ τ' (cellPt d z) (Sc τ')) := by
            gcongr
            exact ENNReal.ofReal_add_le
        _ ≤ r z τ' := by
            show _ ≤ r0 z τ' + _ + _
            gcongr)
    (fun τ' hτ' => by
      obtain ⟨hcol, -⟩ := hKc τ' hτ'
      have hτ'T : τ' ∈ Icc (0 : ℝ) T := ⟨hτ'.1, hτ'.2.trans ht.2⟩
      have hΨc : Continuous (Ψ τ') := (hfl.contDiff τ' hτ'T).continuous
      have hΨi : Continuous (Function.invFun (Ψ τ')) := (hfl.contDiff_inv τ' hτ'T).continuous
      have hbij := hΨ.bij τ' hτ'T
      have hmz := hmassW Ψ τ' hbij hΨc hΨi (F τ') (hsol.smooth τ' hτ').1
        (fun z'' j idx => sa12x3_adv_cut_integrable hχp.1.1 hχp.1.2.1 hb hΨ hτ'T (cellPt d z'') (hsol.smooth τ' hτ').1 idx)
      have := sa12x4_weighted_rate_dom E7 E9 hsh7 hsh9 A9 κ' A7 Kw CK C12 hC12 hA9 hκ'0 hA70 hKw0 hCK hc7 hc9
        (fun z => sa12x4_wt_le_cellWeight hd z) (fun z => f z τ') (fun z => D z τ')
        (fun z => hfnn z τ' hτ') (fun z => hDnn z τ' hτ')
        (fun z' => ENNReal.ofReal (cellMass m Ψ τ' z' (F τ'))) (Kc τ') hcol hmz
      have h0 : ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) * r0 z τ' ≤
          ENNReal.ofReal (κ' * c7) * ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
            ENNReal.ofReal (D z τ') +
          ENNReal.ofReal a * ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
            ENNReal.ofReal (f z τ') := by
        simpa [hr0, ha] using this
      have hB : ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) * ENNReal.ofReal (ε * f z τ') =
          ENNReal.ofReal ε * ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
            ENNReal.ofReal (f z τ') := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun z => by rw [ENNReal.ofReal_mul hε0.le]; ring
      have e1 : ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) * r z τ' =
          ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) * r0 z τ' +
          ENNReal.ofReal ε * ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
            ENNReal.ofReal (f z τ') +
          ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
            ENNReal.ofReal (ε⁻¹ * cellEnergy m χ Ψ τ' (cellPt d z) (Sc τ')) := by
        simp only [hr, mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_add, hB]
      have e2 : ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
          ENNReal.ofReal (ε⁻¹ * cellEnergy m χ Ψ τ' (cellPt d z) (Sc τ')) ≤ ENNReal.ofReal (ε⁻¹ * Hf τ') := by
        calc _ = ENNReal.ofReal ε⁻¹ * ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
              ENNReal.ofReal (cellEnergy m χ Ψ τ' (cellPt d z) (Sc τ')) := by
              rw [← ENNReal.tsum_mul_left]
              exact tsum_congr fun z => by rw [ENNReal.ofReal_mul (inv_nonneg.2 hε0.le)]; ring
          _ ≤ ENNReal.ofReal ε⁻¹ * ENNReal.ofReal (Hf τ') := by gcongr; exact hHf τ' hτ'
          _ = ENNReal.ofReal (ε⁻¹ * Hf τ') := by rw [ENNReal.ofReal_mul (inv_nonneg.2 hε0.le)]
      beta_reduce
      rw [e1, ENNReal.ofReal_add ha0 hε0.le, add_mul]
      calc _ ≤ (ENNReal.ofReal (κ' * c7) * ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
            ENNReal.ofReal (D z τ') +
          ENNReal.ofReal a * ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
            ENNReal.ofReal (f z τ')) +
          ENNReal.ofReal ε * ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
            ENNReal.ofReal (f z τ') + ENNReal.ofReal (ε⁻¹ * Hf τ') := by gcongr
        _ = _ := by ring) τ hτ
  have hexp : Real.exp (a * τ) ≤ Real.exp (Rg.lambdaM C ν₀ θ * τ) := by
    refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ hτ.1)
    have h1 : A7 ≤ Kq * C7 * k0 := by
      have := hrate C7 hC7.le
      rw [hk0lam] at this
      rw [hA7]
      exact this
    rw [hk0lam C]
    have hB : 0 ≤ c7 + Kw * CK * C12 := by positivity
    calc a = A9 * c9 + A7 * (c7 + Kw * CK * C12) := rfl
      _ ≤ A9 * c9 + Kq * C7 * k0 * (c7 + Kw * CK * C12) := by gcongr
      _ ≤ (A9 * c9 + Kq * C7 * (c7 + Kw * CK * C12)) * k0 := by
          have : 0 ≤ A9 * c9 := by positivity
          nlinarith [mul_nonneg this (sub_nonneg.2 hk01)]
      _ ≤ C * k0 := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          rw [hCdef, hBc]; linarith [Real.exp_pos 1]
  have hlam0 : 0 ≤ Rg.lambdaM C ν₀ θ := by rw [hk0lam C]; exact mul_nonneg hCpos.le (by linarith)
  have hf0 : ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) * ENNReal.ofReal (f z 0) = 0 := by
    have : ∀ z, f z 0 = 0 := fun z => by simp [hf, cellEnergy, jetSq, hF0, partialDeriv]
    simp [this]
  have hI0 : 0 ≤ ∫ σ in Icc (0 : ℝ) τ, Hf σ :=
    setIntegral_nonneg measurableSet_Icc (fun σ hσ => hHf0 σ ⟨hσ.1, hσ.2.trans hτ.2⟩)
  have hmain := hgr
  rw [hf0, zero_add, integral_const_mul] at hmain
  unfold cellWeighted
  refine hmain.trans ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  set Iτ : ℝ := ∫ σ in Icc (0 : ℝ) τ, Hf σ with hIτ
  rcases hετ with h0 | h1
  · have : Iτ = 0 := by rw [hIτ, h0, Set.Icc_self]; simp
    rw [this, h0]; simp
  · have hτ0 : 0 ≤ τ := hτ.1
    have hinv : ε⁻¹ = τ := inv_eq_of_mul_eq_one_right h1
    have e1 : (a + ε) * τ = a * τ + 1 := by nlinarith [h1]
    have hE : Real.exp (a * τ) ≤ Real.exp (2 * Rg.lambdaM C ν₀ θ * τ) :=
      hexp.trans (Real.exp_le_exp.2 (by nlinarith [mul_nonneg hlam0 hτ0]))
    have hec : Real.exp 1 ≤ C := by rw [hCdef]; linarith [hBc0]
    rw [hinv, e1, Real.exp_add]
    have e2 : Real.exp (a * τ) * Real.exp 1 * (τ * Iτ) = Real.exp 1 * Real.exp (a * τ) * (τ * Iτ) := by ring
    have e3 : C * Real.exp (2 * Rg.lambdaM C ν₀ θ * τ) * τ * Iτ =
        C * Real.exp (2 * Rg.lambdaM C ν₀ θ * τ) * (τ * Iτ) := by ring
    rw [e3]
    have hτI : 0 ≤ τ * Iτ := mul_nonneg hτ0 hI0
    calc Real.exp (a * τ) * Real.exp 1 * (τ * Iτ) = Real.exp 1 * Real.exp (a * τ) * (τ * Iτ) := e2
      _ ≤ C * Real.exp (2 * Rg.lambdaM C ν₀ θ * τ) * (τ * Iτ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hec hE (Real.exp_pos _).le hCpos.le) hτI

end HRS.MH.AdjointRd.Phase2SA12X5
