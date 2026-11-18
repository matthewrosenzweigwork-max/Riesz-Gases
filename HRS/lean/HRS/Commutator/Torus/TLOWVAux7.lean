import HRS.Commutator.Torus.TLOWVAux6

/-!
# T-LOWV, part 7: Lemma 4.1 on the torus (`low_velocity_T`), conditional on `nrs_T`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

theorem tlowv_main (hn : TlowvNRS d s) (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (v : Torus d → Euc d) (K : ℝ),
      TorusSubTransport d s v K → ∀ σ : SMT d, σ.IsFinite → σ.mass = 0 →
        ENNReal.ofReal |CcommT (gloForceT s η) (PleqT η v) σ| ≤
          ENNReal.ofReal (C * K) * homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef) := by
  obtain ⟨Cn, hCn, hnrs⟩ := hn
  obtain ⟨C₁, hC₁, hvlo⟩ := tsamp_vlo_core hd hs0 hsd
  obtain ⟨CW, hCW, hW⟩ := tlowv_ghi_W hd hs0 hsd
  have hd1 : 1 ≤ d := by omega
  have he : 0 < (d : ℝ) - s := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hP0 : 0 < (16 * Real.pi) ^ ((d : ℝ) - s) := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨Cn * C₁ + C₁ * CW * (16 * Real.pi) ^ ((d : ℝ) - s) + 1, by positivity, ?_⟩
  intro η hη hη1 v K hT σ hσ hm
  have hT' := hvlo η hη hη1 v K hT
  have hT'c := hT'
  obtain ⟨L, F, hL, hF, hLip, -, -⟩ := hT
  obtain ⟨L', F', hL', hF', hLip', -, hLF'⟩ := hT'
  have hK : 0 ≤ C₁ * K := by linarith
  have hvc : Continuous v := tsamp_lip_continuous hLip
  have hVc : Continuous (PleqT η v) := tsamp_lip_continuous hLip'
  have hη4 : 0 < η / 4 := by positivity
  obtain ⟨a, hac, hasm, hco⟩ := tlowv_density σ hσ hη
  obtain ⟨Ba, hBa⟩ := ten_bound_of_continuous hac
  have hBa' : ∀ x, |a x| ≤ Ba := fun x => by simpa using hBa x
  have hfin : (SMT.ofDensity a).IsFinite := tlowv_ofDensity_finite a hac.measurable hBa'
  -- Step 1: only the low frequencies of `σ` matter
  have hR1 : CcommT (gloForceT s η) (PleqT η v) σ =
      CcommT (gloForceT s η) (PleqT η v) (SMT.ofDensity a) := by
    refine tlowv_comm_congr σ (SMT.ofDensity a) hσ hfin (HRS.PDE.Kern.boxF d ⌈2 / η⌉₊)
      (PleqT η v) (gloForceT s η)
      (fun i k => ((tkrChi η k : ℝ) : ℂ) * Torus.fcoef (fun x => v x i) k)
      (fun i m => ((tkrChi η m : ℝ) : ℂ) * tkrCI d s i m)
      (fun i z => tlowv_Pleq_trig hd1 hη hη1 hL hLip i z)
      (fun i z => tlowv_glo_trig hd hs0 hsd hη i z) (R := 2 / η) ?_ ?_ ?_
    · intro i k hk
      by_contra hcon
      push Not at hcon
      apply hk
      have : tkrChi η k = 0 := by
        apply tkrChi_eq_zero _ hη
        rw [div_le_iff₀ hη] at hcon
        linarith
      simp [this]
    · intro i m hm
      by_contra hcon
      push Not at hcon
      apply hm
      have : tkrChi η m = 0 := by
        apply tkrChi_eq_zero _ hη
        rw [div_le_iff₀ hη] at hcon
        linarith
      simp [this]
    · intro j hj
      rw [tlowv_ofDensity_coef a hac.measurable hBa', hco j]
      have : tkrChi (η / 4) j = 1 := by
        apply tkrChi_eq_one _ hη4
        have : Lattice.enorm j < 4 / η := by
          have h2 : 2 * (2 / η) = 4 / η := by ring
          rwa [h2] at hj
        rw [lt_div_iff₀ hη] at this
        nlinarith
      rw [this]; simp
  -- Step 2: the density
  have hR2 := tlowv_pair2_density (tsamp_gloForce_continuous hd hs0 hsd hη) hL' hLip' hVc hac
  -- Step 3: split `∇g_≤ = ∇g - ∇g_>`
  obtain ⟨hgm, hgW⟩ := tlowv_glo_W hd hs0 hsd hη
  obtain ⟨hWi, hWb⟩ := hW η hη hη1
  have hadd := tlowv_CcommFun_add hgm (tlowv_glo_odd hd hs0 hsd hη) hgW
    (tkr_ghi_measurable (by omega) hs0 (by
      have : (3 : ℝ) ≤ d := by exact_mod_cast hd
      linarith) hη)
    (tlowv_ghi_odd hd hs0 hsd hη) hWi hL' hLip' hVc hac
  have hG : (fun z => gloForceT s η z + ghiForceT s η z) = periodicRieszGrad d s := by
    funext z
    unfold ghiForceT
    abel
  rw [hG] at hadd
  -- Step 4: bounds
  have hsmooth := hasm
  have hmean : ∫ x, a x = 0 := by
    have h0 := Torus.fcoef_zero a
    rw [hco 0] at h0
    have hcoef0 : σ.coef 0 = 0 := by
      rw [tlowv_coef_zero, hm]; simp
    rw [hcoef0, mul_zero] at h0
    have : Torus.mean a = 0 := by exact_mod_cast h0.symm
    exact this
  have hc0 : Torus.fcoef a 0 = 0 := by
    rw [hco 0]
    have hcoef0 : σ.coef 0 = 0 := by
      rw [tlowv_coef_zero, hm]; simp
    rw [hcoef0, mul_zero]
  have hsupp : ∀ k : Lattice d, η * Lattice.enorm k ≥ 8 → Torus.fcoef a k = 0 := by
    intro k hk
    rw [hco k]
    have : tkrChi (η / 4) k = 0 := by
      apply tkrChi_eq_zero _ hη4
      nlinarith
    simp [this]
  have hB1 := hnrs (PleqT η v) (C₁ * K) hT'c a hsmooth hmean
  have hB2 := tlowv_ghi_part hd hs0 hsd hW hη hη1 hL' hLip' hVc hac hc0 hsupp
  have hcoefeq : (fun k => Torus.fcoef a k) = lowFreqT η 4 σ.coef := by
    funext k
    rw [hco k]
    rfl
  rw [hcoefeq] at hB1 hB2
  -- assemble
  have hsplit : CcommFunT (gloForceT s η) (PleqT η v) a =
      CcommFunT (periodicRieszGrad d s) (PleqT η v) a - CcommFunT (ghiForceT s η) (PleqT η v) a := by
    linarith
  rw [hR1, hR2, hsplit]
  set X := CcommFunT (periodicRieszGrad d s) (PleqT η v) a
  set Y := CcommFunT (ghiForceT s η) (PleqT η v) a
  set Hm := homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef)
  have h1 : ENNReal.ofReal |X - Y| ≤ ENNReal.ofReal |X| + ENNReal.ofReal |Y| := by
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub _ _)
  have hLK : L' ≤ C₁ * K := by linarith
  have hCW0 : 0 ≤ CW := hCW.le
  calc ENNReal.ofReal |X - Y| ≤ ENNReal.ofReal |X| + ENNReal.ofReal |Y| := h1
    _ ≤ ENNReal.ofReal (Cn * (C₁ * K)) * Hm +
          ENNReal.ofReal (L' * CW * (16 * Real.pi) ^ ((d : ℝ) - s)) * Hm := add_le_add hB1 hB2
    _ = ENNReal.ofReal (Cn * (C₁ * K) + L' * CW * (16 * Real.pi) ^ ((d : ℝ) - s)) * Hm := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((Cn * C₁ + C₁ * CW * (16 * Real.pi) ^ ((d : ℝ) - s) + 1) * K) * Hm := by
        gcongr
        have h2 : L' * CW * (16 * Real.pi) ^ ((d : ℝ) - s) ≤
            C₁ * K * CW * (16 * Real.pi) ^ ((d : ℝ) - s) := by gcongr
        nlinarith [hK, hP0, hCW0]

end HRS.Commutator.TorusNote
