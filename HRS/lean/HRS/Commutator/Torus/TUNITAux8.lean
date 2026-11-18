import HRS.Commutator.Torus.TUNITAux7

/-!
# T-UNIT-a helpers, part 8: `high_background_T`

Prefix `tunit_`.  Torus analogue of `UHIGH.uhigh_background_main` (`(5.backgroundclosing)`): Sobolev duality
`η^d|∫ρ H| ≤ (sobSqT η (-α) ρ̂)^{1/2}(sobSqT η α Ĥ)^{1/2}` with `H = ⟨v_>, u⟩`, `product_T`,
`energy_control_T (c)`.  Powers of `η`: `η^{s/2}·η^{(2d-s)/2} = η^d`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS HRS.KernelGrad

variable {d : ℕ} {s : ℝ}

theorem tunit_background_main (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ η₀ C : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧ 0 < C ∧ ∀ p : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp → ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ ρ : Torus d → ℝ, BddDensityT ρ → ∀ (N : ℕ) (X : Config d N), 1 ≤ N → X ∉ collisionSet d N →
      ∀ (v : Torus d → Euc d) (K : ℝ), TorusSubTransport d s v K →
        |∫ x, ρ x * inner ℝ (PgtT η v x) ((chargeT X ρ).convForce (gloForceT s η) x)| ≤
          C * K * scaleQT s Cp p η X ρ := by
  obtain ⟨Cb, η₀, hCb, hη₀, hη₀1, hEC⟩ := energy_control_T hd hs0 hsd
  obtain ⟨Cn, hCn, hun⟩ := tunit_u_norm_bound hd hs0 hsd
  obtain ⟨Cpr, hCpr, hprod⟩ := product_T hd hs0 hsd
  have hK2 : 0 < 2 + ten2K d s := by have := ten2K_nonneg hd hs0 hsd; linarith
  refine ⟨η₀, Cpr * Cn * Real.sqrt Cb * Real.sqrt (2 + ten2K d s), hη₀, hη₀1, by positivity,
    fun p hp => ?_⟩
  obtain ⟨Cp0, hCp0, hE⟩ := hEC p hp
  refine ⟨Cp0, hCp0, fun Cp hCp η hη hηη₀ ρ hρ N X hN hX v K hv => ?_⟩
  have hη1 : η ≤ 1 := hηη₀.trans hη₀1
  have hp1 : 1 ≤ p := (tunit_one_lt_p hd hs0 hsd hp).le
  obtain ⟨hA, hB, hc, -⟩ := hE Cp hCp η hη hηη₀ ρ hρ N X hN hX
  set Q := scaleQT s Cp p η X ρ with hQ
  have hnp1 : 1 ≤ normT p ρ := ten2_normT_ge_one hp1 hρ
  have hQ0 : 0 ≤ Q := by
    have h0 : 0 ≤ η ^ (-s) / (N : ℝ) + normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := by
      have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      have h1 : 0 ≤ η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := Real.rpow_nonneg hη.le _
      positivity
    linarith
  set Kc := 2 + ten2K d s with hKc
  have hker : kerEnergyT (gTorus s η) (chargeT X ρ) ≤ Kc * Q :=
    tunit_kerEnergy_le hd hs0 hsd hp1 hη hη1 hρ hN X hA hB
  have hE0 : 0 ≤ Kc * Q := mul_nonneg hK2.le hQ0
  have hu := hun η hη hη1 ρ hρ hN X (Kc * Q) hE0 hker
  obtain ⟨L, F, w, hfd, hL0, hF0, hLF⟩ := tunit_hasFracData hv
  have hFK : F ≤ K := by linarith
  have hfin := ten2_charge_finite hN X hρ
  have hcont := tunit_u_continuous hd hs0 hsd hη _ hfin
  obtain ⟨hHmem, hHbd⟩ := hprod η hη hη1 v L w F hfd
    (fun x => (chargeT X ρ).convForce (gloForceT s η) x) hcont (tunit_u_memLp hd hs0 hsd hη _ hfin _)
    (tunit_u_fcoef hd hs0 hsd hη _ hfin)
  obtain ⟨Bρ, hBρ⟩ := hρ.bdd
  have hρ2 : MemLp ρ 2 volume :=
    MemLp.of_bound hρ.measurable.aestronglyMeasurable Bρ
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hBρ x)
  have hdual := tunit_duality hρ2 hHmem hη (Whole.alphaE d s)
  set H : Torus d → ℝ := fun x => inner ℝ (PgtT η v x) ((chargeT X ρ).convForce (gloForceT s η) x)
    with hH
  set Sm := sobSqT η (-Whole.alphaE d s) (fun k => Torus.fcoef ρ k) with hSm
  set Sp := sobSqT η (Whole.alphaE d s) (fun k => Torus.fcoef H k) with hSp
  set Nu := eLpNorm (fun x => ‖(chargeT X ρ).convForce (gloForceT s η) x‖)
    (ENNReal.ofReal (Whole.p2E d s)) volume with hNu
  have hηs : 0 ≤ η ^ s := Real.rpow_nonneg hη.le _
  have hηd : 0 < η ^ d := pow_pos hη d
  -- the bound on `Sm`
  have hSm1 : Sm ≤ ENNReal.ofReal (η ^ s * (Cb * Q)) := by
    have hone : ENNReal.ofReal (η ^ s) * ENNReal.ofReal (η ^ (-s)) = 1 := by
      rw [← ENNReal.ofReal_mul hηs, ← Real.rpow_add hη, add_neg_cancel, Real.rpow_zero,
        ENNReal.ofReal_one]
    calc Sm = ENNReal.ofReal (η ^ s) * (ENNReal.ofReal (η ^ (-s)) * Sm) := by
          rw [← mul_assoc, hone, one_mul]
      _ ≤ ENNReal.ofReal (η ^ s) * ENNReal.ofReal (Cb * Q) := by gcongr
      _ = ENNReal.ofReal (η ^ s * (Cb * Q)) := (ENNReal.ofReal_mul hηs).symm
  have hSm2 : Sm ^ ((1 : ℝ) / 2) ≤ ENNReal.ofReal ((η ^ s * (Cb * Q)) ^ ((1 : ℝ) / 2)) := by
    calc Sm ^ ((1 : ℝ) / 2) ≤ (ENNReal.ofReal (η ^ s * (Cb * Q))) ^ ((1 : ℝ) / 2) :=
          ENNReal.rpow_le_rpow hSm1 (by norm_num)
      _ = _ := ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
  -- the bound on `Sp`
  set e : ℝ := (s - 2 * (d : ℝ)) * (1 / 2) with he
  have hSp1 : ENNReal.ofReal (η ^ e) * Sp ^ ((1 : ℝ) / 2) ≤
      ENNReal.ofReal (Cpr * F) * Nu := by
    refine le_trans (le_of_eq ?_) hHbd
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hη.le _) (by norm_num), ← Real.rpow_mul hη.le]
  have hSp2 : Sp ^ ((1 : ℝ) / 2) ≤ ENNReal.ofReal (η ^ (-e)) * (ENNReal.ofReal (Cpr * F) * Nu) := by
    have hone : ENNReal.ofReal (η ^ (-e)) * ENNReal.ofReal (η ^ e) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hη.le _), ← Real.rpow_add hη, neg_add_cancel,
        Real.rpow_zero, ENNReal.ofReal_one]
    calc Sp ^ ((1 : ℝ) / 2)
        = ENNReal.ofReal (η ^ (-e)) * (ENNReal.ofReal (η ^ e) * Sp ^ ((1 : ℝ) / 2)) := by
          rw [← mul_assoc, hone, one_mul]
      _ ≤ _ := by gcongr
  -- combine
  have hNu' : Nu ≤ ENNReal.ofReal (Cn * Real.sqrt (Kc * Q)) := hu
  have hcomb : ENNReal.ofReal (η ^ d) * ENNReal.ofReal |∫ x, ρ x * H x| ≤
      ENNReal.ofReal (η ^ d) * ENNReal.ofReal ((Cpr * Cn * Real.sqrt Cb * Real.sqrt Kc) * F * Q) := by
    refine hdual.trans ?_
    have hF0' : 0 ≤ Cpr * F := by positivity
    have hn0 : 0 ≤ Cn * Real.sqrt (Kc * Q) := by positivity
    have hq0 : 0 ≤ (η ^ s * (Cb * Q)) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
    calc Sm ^ ((1 : ℝ) / 2) * Sp ^ ((1 : ℝ) / 2)
        ≤ ENNReal.ofReal ((η ^ s * (Cb * Q)) ^ ((1 : ℝ) / 2)) *
            (ENNReal.ofReal (η ^ (-e)) * (ENNReal.ofReal (Cpr * F) * ENNReal.ofReal (Cn * Real.sqrt (Kc * Q)))) := by
          refine mul_le_mul' hSm2 (hSp2.trans ?_)
          gcongr
      _ = ENNReal.ofReal ((η ^ s * (Cb * Q)) ^ ((1 : ℝ) / 2) *
            (η ^ (-e) * ((Cpr * F) * (Cn * Real.sqrt (Kc * Q))))) := by
          rw [ENNReal.ofReal_mul hq0, ENNReal.ofReal_mul (Real.rpow_nonneg hη.le _),
            ENNReal.ofReal_mul hF0']
      _ = ENNReal.ofReal (η ^ d) * ENNReal.ofReal ((Cpr * Cn * Real.sqrt Cb * Real.sqrt Kc) * F * Q) := by
          rw [← ENNReal.ofReal_mul hηd.le]
          congr 1
          have h1 : (η ^ s * (Cb * Q)) ^ ((1 : ℝ) / 2) = Real.sqrt Cb * η ^ (s / 2) * Real.sqrt Q := by
            have hηs' : Real.sqrt (η ^ s) = η ^ (s / 2) := by
              rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hη.le]
              congr 1
              ring
            rw [← Real.sqrt_eq_rpow, Real.sqrt_mul hηs, Real.sqrt_mul hCb.le, hηs']
            ring
          have h2 : Real.sqrt (Kc * Q) = Real.sqrt Kc * Real.sqrt Q := Real.sqrt_mul hK2.le Q
          have h3 : Real.sqrt Q * Real.sqrt Q = Q := Real.mul_self_sqrt hQ0
          have h4 : η ^ (s / 2) * η ^ (-e) = η ^ d := by
            rw [← Real.rpow_add hη, ← Real.rpow_natCast]
            congr 1
            rw [he]
            ring
          rw [h1, h2]
          calc Real.sqrt Cb * η ^ (s / 2) * Real.sqrt Q *
                (η ^ (-e) * (Cpr * F * (Cn * (Real.sqrt Kc * Real.sqrt Q))))
              = (η ^ (s / 2) * η ^ (-e)) * ((Cpr * Cn * Real.sqrt Cb * Real.sqrt Kc) * F *
                  (Real.sqrt Q * Real.sqrt Q)) := by ring
            _ = η ^ d * ((Cpr * Cn * Real.sqrt Cb * Real.sqrt Kc) * F * Q) := by rw [h3, h4]
  have hX : ENNReal.ofReal |∫ x, ρ x * H x| ≤
      ENNReal.ofReal ((Cpr * Cn * Real.sqrt Cb * Real.sqrt Kc) * F * Q) :=
    (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 hηd).ne'
      ENNReal.ofReal_ne_top).1 hcomb
  have hCpos : 0 < Cpr * Cn * Real.sqrt Cb * Real.sqrt Kc := by positivity
  have hRHS : 0 ≤ (Cpr * Cn * Real.sqrt Cb * Real.sqrt Kc) * F * Q :=
    mul_nonneg (mul_nonneg hCpos.le hF0) hQ0
  have hfinal : (Cpr * Cn * Real.sqrt Cb * Real.sqrt Kc) * F * Q ≤
      (Cpr * Cn * Real.sqrt Cb * Real.sqrt Kc) * K * Q :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFK hCpos.le) hQ0
  exact ((ENNReal.ofReal_le_ofReal_iff hRHS).1 hX).trans hfinal

end HRS.Commutator.TorusNote
