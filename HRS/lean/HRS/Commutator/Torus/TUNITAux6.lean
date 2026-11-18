import HRS.Commutator.Torus.TUNITAux5

/-!
# T-UNIT-a helpers, part 6: `high_particles_T`

Prefix `tunit_`.  Torus analogue of `UHIGH.uhigh_particles_main` (`(5.atomicclosing)`).  Powers of `η`:
`(∑ n_j²)^{1/2} ≲ η^{s/2}Q^{1/2}`, `(∑ sup|v_>|^{p₁})^{1/p₁} ≲ ηF`, `(∑ sup|u|^{p₂})^{1/p₂} ≲
η^{-(s+2)/2}‖u‖_{p₂}`, `‖u‖_{p₂} ≲ Q^{1/2}`; the total power of `η` is `s/2 + 1 - (s+2)/2 = 0`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS HRS.KernelGrad

variable {d : ℕ} {s : ℝ}

/-- `p > d/(d-s)` forces `p > 1`. -/
theorem tunit_one_lt_p (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {p : ℝ≥0∞}
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) : 1 < p := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hds : 0 < (d : ℝ) - s := by linarith
  have hρ1 : 1 ≤ (d : ℝ) / (d - s) := by rw [le_div_iff₀ hds]; linarith
  exact lt_of_le_of_lt (by simpa using ENNReal.ofReal_le_ofReal hρ1) hp

/-- The `η`-exponent of the particle contribution cancels. -/
theorem tunit_exp_cancel (hd : 3 ≤ d) (hs0 : 0 ≤ s) {η : ℝ} (hη : 0 < η) :
    η ^ (s / 2) * η * η ^ (-(d : ℝ) / Whole.p2E d s) = 1 := by
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hs2 : s + 2 ≠ 0 := by linarith
  have he : -(d : ℝ) / Whole.p2E d s = -(s + 2) / 2 := by
    unfold Whole.p2E
    field_simp
  rw [he]
  have : η = η ^ (1 : ℝ) := (Real.rpow_one η).symm
  calc η ^ (s / 2) * η * η ^ (-(s + 2) / 2) = η ^ (s / 2) * η ^ (1 : ℝ) * η ^ (-(s + 2) / 2) := by
        rw [Real.rpow_one]
    _ = η ^ (s / 2 + 1 + -(s + 2) / 2) := by
        rw [Real.rpow_add hη, Real.rpow_add hη]
    _ = 1 := by
        have : s / 2 + 1 + -(s + 2) / 2 = 0 := by ring
        rw [this, Real.rpow_zero]

/-- `TorusSubTransport` gives the fractional data. -/
theorem tunit_hasFracData {v : Torus d → Euc d} {K : ℝ} (hv : TorusSubTransport d s v K) :
    ∃ (L F : ℝ) (w : Torus d → Euc d), HasFracDataT d s v L w F ∧ 0 ≤ L ∧ 0 ≤ F ∧ L + F ≤ K := by
  obtain ⟨L, F, hL0, hF0, hlip, ⟨w, hrep, hw⟩, hLF⟩ := hv
  refine ⟨L, F, w, ⟨⟨hL0, hF0⟩, hlip, hrep, ?_⟩, hL0, hF0, hLF⟩
  have hwm : AEStronglyMeasurable w volume :=
    aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hw)
  have e : eLpNorm (fun x => ‖w x‖) (ENNReal.ofReal (Whole.p1E d s)) volume =
      eLpNorm w (ENNReal.ofReal (Whole.p1E d s)) volume := eLpNorm_norm w hwm
  rw [e]
  exact hw

theorem tunit_particles_main (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ η₀ C : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧ 0 < C ∧ ∀ p : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp → ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ ρ : Torus d → ℝ, BddDensityT ρ → ∀ (N : ℕ) (X : Config d N), 1 ≤ N → X ∉ collisionSet d N →
      ∀ (v : Torus d → Euc d) (K : ℝ), TorusSubTransport d s v K →
        (1 / (N : ℝ)) * ∑ i, |inner ℝ (PgtT η v (X i))
            ((chargeT X ρ).convForce (gloForceT s η) (X i))| ≤ C * K * scaleQT s Cp p η X ρ := by
  obtain ⟨Cb, η₀, hCb, hη₀, hη₀1, hEC⟩ := energy_control_T hd hs0 hsd
  obtain ⟨Cn, hCn, hun⟩ := tunit_u_norm_bound hd hs0 hsd
  obtain ⟨Cz, hCz, hzs⟩ := vhi_cell_sampling_T hd hs0 hsd
  obtain ⟨Cu, hCu, hus⟩ := usample_T hd hs0 hsd
  obtain ⟨hp1pos, hp2pos, hrel⟩ := tunit_exponent_relation hd hs0 hsd
  have hK2 : 0 < 2 + ten2K d s := by have := ten2K_nonneg hd hs0 hsd; linarith
  refine ⟨η₀, Cz * Cu * Cn * Real.sqrt Cb * Real.sqrt (2 + ten2K d s), hη₀, hη₀1, by positivity,
    fun p hp => ?_⟩
  obtain ⟨Cp0, hCp0, hE⟩ := hEC p hp
  refine ⟨Cp0, hCp0, fun Cp hCp η hη hηη₀ ρ hρ N X hN hX v K hv => ?_⟩
  have hη1 : η ≤ 1 := hηη₀.trans hη₀1
  have hp1 : 1 ≤ p := (tunit_one_lt_p hd hs0 hsd hp).le
  obtain ⟨hA, hB, -, hocc⟩ := hE Cp hCp η hη hηη₀ ρ hρ N X hN hX
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
  have hK0 : 0 ≤ K := by linarith
  have hz := hzs η hη hη1 v L w F hfd
  have hfin := ten2_charge_finite hN X hρ
  obtain ⟨U, -, -, hcell⟩ := hus η hη hη1 (fun x => (chargeT X ρ).convForce (gloForceT s η) x)
    (tunit_u_continuous hd hs0 hsd hη _ hfin) (tunit_u_memLp hd hs0 hsd hη _ hfin _)
    (tunit_u_fcoef hd hs0 hsd hη _ hfin)
  have hocc' : ENNReal.ofReal (∑ j : Fin d → Fin (nCells η), occT η X j ^ 2) ≤
      ENNReal.ofReal (Cb * η ^ s * Q) := ENNReal.ofReal_le_ofReal hocc
  set V : Torus d → Euc d := PgtT η v with hV
  set u : Torus d → Euc d := fun x => (chargeT X ρ).convForce (gloForceT s η) x with hu'
  have hηs : 0 ≤ η ^ s := Real.rpow_nonneg hη.le _
  have hηe : 0 ≤ η ^ (-(d : ℝ) / Whole.p2E d s) := Real.rpow_nonneg hη.le _
  have hsum : ENNReal.ofReal ((1 / (N : ℝ)) * ∑ i, |inner ℝ (V (X i)) (u (X i))|) ≤
      (N : ℝ≥0∞)⁻¹ * ∑ i, (‖V (X i)‖ₑ * ‖u (X i)‖ₑ) := by
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _),
      one_div, ENNReal.ofReal_inv_of_pos hN0, ENNReal.ofReal_natCast]
    gcongr with i _
    calc ENNReal.ofReal |inner ℝ (V (X i)) (u (X i))|
        ≤ ENNReal.ofReal (‖V (X i)‖ * ‖u (X i)‖) :=
          ENNReal.ofReal_le_ofReal (abs_real_inner_le_norm _ _)
      _ = ‖V (X i)‖ₑ * ‖u (X i)‖ₑ := by
          rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
  have hhold := tunit_particle_holder hη hη1 hN X V u hp1pos hp2pos hrel
  have hmain : ENNReal.ofReal ((1 / (N : ℝ)) * ∑ i, |inner ℝ (V (X i)) (u (X i))|) ≤
      ENNReal.ofReal ((Cb * η ^ s * Q) ^ ((1 : ℝ) / 2) *
        (Cz * η * F * (Cu * η ^ (-(d : ℝ) / Whole.p2E d s) * (Cn * Real.sqrt (Kc * Q))))) := by
    calc ENNReal.ofReal ((1 / (N : ℝ)) * ∑ i, |inner ℝ (V (X i)) (u (X i))|)
        ≤ (N : ℝ≥0∞)⁻¹ * ∑ i, (‖V (X i)‖ₑ * ‖u (X i)‖ₑ) := hsum
      _ ≤ (ENNReal.ofReal (∑ j : Fin d → Fin (nCells η), occT η X j ^ 2)) ^ ((1 : ℝ) / 2) *
            (cellSupNorm η (Whole.p1E d s) V * cellSupNorm η (Whole.p2E d s) u) := hhold
      _ ≤ (ENNReal.ofReal (Cb * η ^ s * Q)) ^ ((1 : ℝ) / 2) *
            (ENNReal.ofReal (Cz * η * F) * (ENNReal.ofReal (Cu * η ^ (-(d : ℝ) / Whole.p2E d s)) *
              ENNReal.ofReal (Cn * Real.sqrt (Kc * Q)))) := by
          refine mul_le_mul' (ENNReal.rpow_le_rpow hocc' (by norm_num)) (mul_le_mul' hz (hcell.trans ?_))
          gcongr
      _ = ENNReal.ofReal ((Cb * η ^ s * Q) ^ ((1 : ℝ) / 2) *
            (Cz * η * F * (Cu * η ^ (-(d : ℝ) / Whole.p2E d s) * (Cn * Real.sqrt (Kc * Q))))) := by
          have hx : 0 ≤ Cb * η ^ s * Q := by positivity
          have hc0 : 0 ≤ Cn * Real.sqrt (Kc * Q) := by positivity
          have hb0 : 0 ≤ Cu * η ^ (-(d : ℝ) / Whole.p2E d s) := by positivity
          have ha0 : 0 ≤ Cz * η * F := by positivity
          rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num), ← ENNReal.ofReal_mul hb0,
            ← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_mul (Real.rpow_nonneg hx _)]
  have hreal : (Cb * η ^ s * Q) ^ ((1 : ℝ) / 2) *
        (Cz * η * F * (Cu * η ^ (-(d : ℝ) / Whole.p2E d s) * (Cn * Real.sqrt (Kc * Q)))) =
      (Cz * Cu * Cn * Real.sqrt Cb * Real.sqrt Kc) * F * Q := by
    have hexp := tunit_exp_cancel hd hs0 hη
    have h1 : (Cb * η ^ s * Q) ^ ((1 : ℝ) / 2) = Real.sqrt Cb * η ^ (s / 2) * Real.sqrt Q := by
      have hηs' : Real.sqrt (η ^ s) = η ^ (s / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hη.le]
        congr 1
        ring
      rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity), Real.sqrt_mul hCb.le, hηs']
    have h2 : Real.sqrt (Kc * Q) = Real.sqrt Kc * Real.sqrt Q := Real.sqrt_mul hK2.le Q
    have h3 : Real.sqrt Q * Real.sqrt Q = Q := Real.mul_self_sqrt hQ0
    rw [h1, h2]
    calc Real.sqrt Cb * η ^ (s / 2) * Real.sqrt Q *
          (Cz * η * F * (Cu * η ^ (-(d : ℝ) / Whole.p2E d s) * (Cn * (Real.sqrt Kc * Real.sqrt Q))))
        = (Cz * Cu * Cn * Real.sqrt Cb * Real.sqrt Kc) * F * (Real.sqrt Q * Real.sqrt Q) *
            (η ^ (s / 2) * η * η ^ (-(d : ℝ) / Whole.p2E d s)) := by ring
      _ = (Cz * Cu * Cn * Real.sqrt Cb * Real.sqrt Kc) * F * Q := by rw [h3, hexp, mul_one]
  rw [hreal] at hmain
  have hCpos : 0 < Cz * Cu * Cn * Real.sqrt Cb * Real.sqrt Kc := by positivity
  have hfinal : (Cz * Cu * Cn * Real.sqrt Cb * Real.sqrt Kc) * F * Q ≤
      (Cz * Cu * Cn * Real.sqrt Cb * Real.sqrt Kc) * K * Q := by
    have := mul_le_mul_of_nonneg_left hFK hCpos.le
    exact mul_le_mul_of_nonneg_right this hQ0
  have hRHS : 0 ≤ (Cz * Cu * Cn * Real.sqrt Cb * Real.sqrt Kc) * F * Q :=
    mul_nonneg (mul_nonneg hCpos.le hF0) hQ0
  exact ((ENNReal.ofReal_le_ofReal_iff hRHS).1 hmain).trans hfinal

end HRS.Commutator.TorusNote
