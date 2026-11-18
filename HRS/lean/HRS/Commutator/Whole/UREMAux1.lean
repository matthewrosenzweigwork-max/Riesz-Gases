import HRS.Commutator.Whole.Defs
import HRS.Commutator.Whole.Energy
import HRS.Commutator.Whole.Local
import HRS.Commutator.Whole.DECAux3
import HRS.Commutator.Whole.Continuous

/-!
# Packet CMX-REM: the Fourier remainder bound `(5.remainderbound)` (`[N] L655-677`)

`|𝒞_{g_{>1}}(v,ν)| ≲ C(v) Ec`.  `𝒞_{g_{>1}}(v,ν) = pairGen (commKer g_{>1} v) X ρ` is split into the
particle–particle term `(5.remainder-particles)` (Lemma 3.1, `|x||∇g_{>1}| ≲ f_1`, and `(2.energy-control)`),
the mixed term `(5.remainder-mixed)` (Hölder, `‖f_1‖_{L^{p'}}‖μ‖_{L^p} ≤ Ec`), and the density–density
term `(5.remainder-density)` (Lemma 4.2 with `a = μ`, then `(1.intro-control)`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole.UREM

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- Hölder's inequality for the one-point convolution, in absolute value:
`∫ ‖f(z-y) ρ(y)‖ dy ≤ ‖f‖_q ‖ρ‖_p`. -/
theorem urem_holder_norm {p q : ℝ≥0∞} (hpq : p⁻¹ + q⁻¹ = 1) (f ρ : Euc d → ℝ)
    (hfq : MemLp f q volume) (hρp : MemLp ρ p volume) (z : Euc d) :
    ∫ y, ‖f (z - y) * ρ y‖ ≤ (eLpNorm f q volume).toReal * (eLpNorm ρ p volume).toReal := by
  have hT1 : ENNReal.HolderTriple q p 1 :=
    ENNReal.holderConjugate_iff.2 (by rw [add_comm]; exact hpq)
  have hfz : eLpNorm (fun y => f (z - y)) q volume = eLpNorm f q volume :=
    eLpNorm_comp_measurePreserving hfq.aestronglyMeasurable
      ((volume : Measure (Euc d)).measurePreserving_sub_left z)
  have hfzm : AEStronglyMeasurable (fun y => f (z - y)) volume :=
    (hfq.aestronglyMeasurable).comp_measurePreserving
      ((volume : Measure (Euc d)).measurePreserving_sub_left z)
  have hH : eLpNorm (fun y => f (z - y) * ρ y) 1 volume ≤
      eLpNorm (fun y => f (z - y)) q volume * eLpNorm ρ p volume := by
    have := MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm (p := q) (q := p) (r := 1)
      (fun a b : ℝ => a * b) (1 : ℝ≥0∞) (continuous_mul) hfzm hρp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simp [enorm_mul])
    simpa using this
  have hfin1 : eLpNorm (fun y => f (z - y)) q volume ≠ ⊤ := by
    rw [hfz]; exact (hfq.eLpNorm_lt_top).ne
  have hfin2 : eLpNorm ρ p volume ≠ ⊤ := (hρp.eLpNorm_lt_top).ne
  have hmeas : AEStronglyMeasurable (fun y => f (z - y) * ρ y) volume :=
    hfzm.mul hρp.aestronglyMeasurable
  have hstep2 : ∫ y, ‖f (z - y) * ρ y‖ = (eLpNorm (fun y => f (z - y) * ρ y) 1 volume).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm hmeas, integral_norm_eq_lintegral_enorm hmeas]
  have hstep3 : (eLpNorm (fun y => f (z - y) * ρ y) 1 volume).toReal ≤
      (eLpNorm (fun y => f (z - y)) q volume * eLpNorm ρ p volume).toReal := by
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top hfin1 hfin2) ?_
    simpa using hH
  rw [hfz] at hstep3
  rw [ENNReal.toReal_mul] at hstep3
  linarith

theorem urem_main (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ p q : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p → p⁻¹ + q⁻¹ = 1 →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp →
      ∀ ρ : Euc d → ℝ, BddCptDensity ρ →
      ∀ (N : ℕ) (X : Fin N → Euc d), 1 ≤ N → Function.Injective X →
      ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
        |Ccomm (ghiForce s) v (chargeOf X ρ)| ≤
          C * K * (modEnergy s X ρ + Cp * (1 / (N : ℝ) + normE p ρ)) := by
  obtain ⟨Cr, hCr, hrem⟩ := kernel_remainder (d := d) (s := s) hd hs0 hsd
  obtain ⟨Ci, hCi, hinh⟩ := inhomogeneous hd hs0 hsd
  obtain ⟨Cn, hCn, hint⟩ := intro_control hd hs0 hsd
  obtain ⟨Cb, hCb, hEC⟩ := energy_control hd hs0 hsd
  refine ⟨4 * Cr + Ci * Cn, by positivity, fun p q hp hpq => ?_⟩
  obtain ⟨Cp1, hCp1, hI⟩ := hint p q hp hpq
  obtain ⟨Cp2, hCp2, hE⟩ := hEC p q hp hpq
  refine ⟨max Cp1 Cp2, lt_max_of_lt_left hCp1, fun Cp hCp ρ hρ N X hN hX v K hv => ?_⟩
  have h1 := hI Cp (le_trans (le_max_left _ _) hCp) ρ hρ N X hN hX
  obtain ⟨h0, h2, -⟩ := hE Cp (le_trans (le_max_right _ _) hCp) ρ hρ N X hN hX
  set Ec := modEnergy s X ρ + Cp * (1 / (N : ℝ) + normE p ρ) with hEc
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  have hnp : 0 ≤ normE p ρ := ENNReal.toReal_nonneg
  have hf0 : 0 ≤ normE q (fTrunc s 1 : Euc d → ℝ) := ENNReal.toReal_nonneg
  have hEc0 : 0 ≤ Ec := by
    have : 0 ≤ (1 + normE q (fTrunc s 1 : Euc d → ℝ)) * normE p ρ :=
      mul_nonneg (by linarith) hnp
    linarith
  have hfq : normE q (fTrunc s 1 : Euc d → ℝ) * normE p ρ ≤ Ec := by
    have : 0 ≤ normE p ρ := hnp
    nlinarith
  obtain ⟨L, hL, hLK⟩ : ∃ L : ℝ≥0, LipschitzWith L v ∧ (L : ℝ) ≤ K := by
    obtain ⟨L, F, hF, hL, -, hLF⟩ := hv
    exact ⟨L, hL, by linarith⟩
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  have hK0 : 0 ≤ K := le_trans hL0 hLK
  -- the pairing formula
  have hG := DEC.ghi_good hd hs0 hsd hρ hL
  have hid : Ccomm (ghiForce s) v (chargeOf X ρ) = pairGen (commKer (ghiForce s) v) X ρ := by
    unfold Ccomm
    rw [DEC.pair2_formula hρ hN X hG,
      DEC.pairGen_formula hρ hN X hG (fun x => DEC.dec_commKer_diag (ghiForce s) v x)]
  -- pointwise bound on the kernel off the diagonal
  have hkb : ∀ x y : Euc d, x ≠ y →
      ‖commKer (ghiForce s) v x y‖ ≤ (L : ℝ) * Cr * fTrunc s 1 (x - y) := by
    intro x y hxy
    have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
    unfold commKer
    rw [if_neg hxy]
    have h1 : ‖inner ℝ (v x - v y) (ghiForce s (x - y))‖ ≤
        ‖v x - v y‖ * ‖ghiForce s (x - y)‖ := norm_inner_le_norm _ _
    have h2 : ‖v x - v y‖ ≤ (L : ℝ) * ‖x - y‖ := by
      have := hL.dist_le_mul x y
      rwa [dist_eq_norm, dist_eq_norm] at this
    have h3 := hrem (x - y) hz
    calc ‖inner ℝ (v x - v y) (ghiForce s (x - y))‖
        ≤ ‖v x - v y‖ * ‖ghiForce s (x - y)‖ := h1
      _ ≤ ((L : ℝ) * ‖x - y‖) * ‖ghiForce s (x - y)‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = (L : ℝ) * (‖x - y‖ * ‖ghiForce s (x - y)‖) := by ring
      _ ≤ (L : ℝ) * (Cr * fTrunc s 1 (x - y)) := mul_le_mul_of_nonneg_left h3 hL0
      _ = (L : ℝ) * Cr * fTrunc s 1 (x - y) := by ring
  -- (A) particle-particle
  obtain ⟨hT0, hT1, hT2⟩ := energy_terms_nonneg hd hs0 hsd ρ hρ hN X hX
  set S := (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTrunc s 1 (X i - X j) with hS
  have hS2 : S ≤ 2 * Ec := by linarith
  have hA : |(1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
      commKer (ghiForce s) v (X i) (X j)| ≤ (L : ℝ) * Cr * S := by
    have hsum : |∑ i, ∑ j ∈ Finset.univ.erase i, commKer (ghiForce s) v (X i) (X j)| ≤
        (L : ℝ) * Cr * ∑ i, ∑ j ∈ Finset.univ.erase i, fTrunc s 1 (X i - X j) := by
      rw [Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      have := hkb (X i) (X j) (fun h => hji (hX h).symm)
      simpa [Real.norm_eq_abs] using this
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 2), hS]
    calc 1 / (N : ℝ) ^ 2 * |∑ i, ∑ j ∈ Finset.univ.erase i, commKer (ghiForce s) v (X i) (X j)|
        ≤ 1 / (N : ℝ) ^ 2 * ((L : ℝ) * Cr *
            ∑ i, ∑ j ∈ Finset.univ.erase i, fTrunc s 1 (X i - X j)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (L : ℝ) * Cr * (1 / (N : ℝ) ^ 2 *
            ∑ i, ∑ j ∈ Finset.univ.erase i, fTrunc s 1 (X i - X j)) := by ring
  -- (B) mixed
  have hfMem : MemLp (fTrunc s 1 : Euc d → ℝ) q volume := fTrunc_Lq hd hs0 hsd p q hp hpq
  have hρMem : MemLp ρ p volume := energyAux_memLp_bdd ρ hρ p
  have hBi : ∀ i, |∫ y, commKer (ghiForce s) v (X i) y * ρ y| ≤
      (L : ℝ) * Cr * (normE q (fTrunc s 1 : Euc d → ℝ) * normE p ρ) := by
    intro i
    have hint1 : Integrable (fun y => ‖fTrunc s 1 (X i - y) * ρ y‖) :=
      (energyAux_integrable_fTrunc_mul hd hs0 hsd ρ hρ (X i)).norm
    calc |∫ y, commKer (ghiForce s) v (X i) y * ρ y|
        ≤ ∫ y, ‖commKer (ghiForce s) v (X i) y * ρ y‖ := by
          rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
      _ ≤ ∫ y, (L : ℝ) * Cr * ‖fTrunc s 1 (X i - y) * ρ y‖ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
            (hint1.const_mul _) ?_
          filter_upwards [energyAux_ae_ne hd (X i)] with y hy
          rw [norm_mul, norm_mul]
          have hk := hkb (X i) y (Ne.symm hy)
          have hf := fTrunc_pos hd hs0 hsd (X i - y) (sub_ne_zero.2 (Ne.symm hy))
          rw [Real.norm_of_nonneg hf.le]
          calc ‖commKer (ghiForce s) v (X i) y‖ * ‖ρ y‖
              ≤ ((L : ℝ) * Cr * fTrunc s 1 (X i - y)) * ‖ρ y‖ :=
                mul_le_mul_of_nonneg_right hk (norm_nonneg _)
            _ = (L : ℝ) * Cr * (fTrunc s 1 (X i - y) * ‖ρ y‖) := by ring
      _ = (L : ℝ) * Cr * ∫ y, ‖fTrunc s 1 (X i - y) * ρ y‖ := by rw [integral_const_mul]
      _ ≤ (L : ℝ) * Cr * (normE q (fTrunc s 1 : Euc d → ℝ) * normE p ρ) :=
          mul_le_mul_of_nonneg_left (urem_holder_norm hpq _ ρ hfMem hρMem (X i))
            (by positivity)
  have hB : |(2 / (N : ℝ)) * ∑ i, ∫ y, commKer (ghiForce s) v (X i) y * ρ y| ≤
      2 * ((L : ℝ) * Cr * (normE q (fTrunc s 1 : Euc d → ℝ) * normE p ρ)) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / N)]
    have hsum := (Finset.abs_sum_le_sum_abs (fun i => ∫ y, commKer (ghiForce s) v (X i) y * ρ y)
      Finset.univ).trans (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hBi i)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    calc 2 / (N : ℝ) * |∑ i, ∫ y, commKer (ghiForce s) v (X i) y * ρ y|
        ≤ 2 / (N : ℝ) * ((N : ℝ) * ((L : ℝ) * Cr *
            (normE q (fTrunc s 1 : Euc d → ℝ) * normE p ρ))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 2 * ((L : ℝ) * Cr * (normE q (fTrunc s 1 : Euc d → ℝ) * normE p ρ)) := by
          field_simp
  -- (C) density-density
  have hρ2 : MemLp ρ 2 volume := energyAux_memLp_two ρ hρ
  have hC : |CcommFun (ghiForce s) v ρ| ≤ Ci * K * (Cn * Ec) := by
    have h3 := hinh v K hv ρ hρ2
    have h4 : sobSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 ρ) ≤ ENNReal.ofReal (Cn * Ec) :=
      le_trans (le_trans le_add_self le_self_add) h1
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity)]
    calc ENNReal.ofReal |CcommFun (ghiForce s) v ρ|
        ≤ ENNReal.ofReal (Ci * K) * sobSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 ρ) := h3
      _ ≤ ENNReal.ofReal (Ci * K) * ENNReal.ofReal (Cn * Ec) := by gcongr
      _ = ENNReal.ofReal (Ci * K * (Cn * Ec)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
  -- assemble
  rw [hid]
  have hPG : pairGen (commKer (ghiForce s) v) X ρ =
      (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, commKer (ghiForce s) v (X i) (X j) -
        (2 / (N : ℝ)) * (∑ i, ∫ y, commKer (ghiForce s) v (X i) y * ρ y) +
        CcommFun (ghiForce s) v ρ := by
    unfold pairGen CcommFun
    rfl
  rw [hPG]
  have a1 := abs_le.1 hA
  have a2 := abs_le.1 hB
  have a3 := abs_le.1 hC
  have e1 : (L : ℝ) * Cr * S ≤ K * Cr * (2 * Ec) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hLK hCr.le) hS2 (by rw [hS]; positivity) (by positivity)
  have e2 : (L : ℝ) * Cr * (normE q (fTrunc s 1 : Euc d → ℝ) * normE p ρ) ≤ K * Cr * Ec :=
    mul_le_mul (mul_le_mul_of_nonneg_right hLK hCr.le) hfq (by positivity) (by positivity)
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, e1, e2]

end HRS.Commutator.Whole.UREM
