import HRS.Commutator.Torus.TUNITAux3
import HRS.Commutator.Torus.TEN2Aux10
import HRS.Commutator.Torus.TEN2Aux11

/-!
# T-UNIT-a helpers, part 4: the potential `u = ∇g_≤ * ν`

Prefix `tunit_`.  Regularity and Fourier support of `u`, the bound `‖u‖_{p₂} ≲ ‖ν‖_{g_η}^{1/2}`
(`potential_T`, `scoercive_T`), and `‖ν‖²_{g_η} ≲ Q_η` (from `energy_control_T`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS HRS.KernelGrad

variable {d : ℕ} {s η : ℝ}

theorem tunit_u_continuous (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η)
    (σ : SMT d) (hσ : σ.IsFinite) : Continuous (fun x => σ.convForce (gloForceT s η) x) :=
  tsamp_convForce_continuous hd hs0 hsd hη σ hσ

theorem tunit_u_memLp (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η)
    (σ : SMT d) (hσ : σ.IsFinite) (q : ℝ≥0∞) :
    MemLp (fun x => ‖σ.convForce (gloForceT s η) x‖) q volume := by
  have hc := (tunit_u_continuous hd hs0 hsd hη σ hσ).norm
  obtain ⟨B, hB⟩ := ten_bound_of_continuous hc
  exact MemLp.of_bound hc.aestronglyMeasurable B (ae_of_all _ hB)

theorem tunit_u_fcoef (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η)
    (σ : SMT d) (hσ : σ.IsFinite) :
    ∀ (i : Fin d) (k : Lattice d), 2 < η * Lattice.enorm k →
      Torus.fcoef (fun x => σ.convForce (gloForceT s η) x i) k = 0 := by
  intro i k hk
  set e : Lattice d → ℂ := fun k => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k * σ.coef k with he
  have hT3 : HRS.PDE.IsTrigPoly ⌈2 / η⌉₊ e := tkr_isTrigPoly hη (fun k hk => by
    intro h0; apply hk; simp [he, h0])
  have hhe : ∀ x, (((σ.convForce (gloForceT s η) x) i : ℝ) : ℂ) = HRS.PDE.Kern.trig e x :=
    fun x => tsamp_convForce_trig hd hs0 hsd hη σ hσ x i
  have hfc := tsamp_trig_fcoef hT3 hhe k
  rw [hfc]
  have hz : tkrChi η k = 0 := tkrChi_eq_zero hk.le hη
  simp [he, hz]

/-- The charge has total mass zero. -/
theorem tunit_charge_mass {N : ℕ} (ρ : Torus d → ℝ) (hρ : BddDensityT ρ) (hN : 1 ≤ N) (X : Config d N) :
    (chargeT X ρ).mass = 0 := by
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    exact this.ne'
  unfold SMT.mass
  have h := tunit_charge_int ρ hρ hN X (fun _ => (1 : ℝ)) measurable_const
    (by simpa using (integrable_of_integral_eq_one hρ.mass))
  rw [h]
  simp [hρ.mass, hN0]

/-- `‖ν‖²_{g_η} ≤ (2 + K_s) Q_η` from `(a)` and `(b)` of `energy_control_T`. -/
theorem tunit_kerEnergy_le (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {ρ : Torus d → ℝ} (hρ : BddDensityT ρ) {N : ℕ} (hN : 1 ≤ N)
    (X : Config d N) {Q : ℝ}
    (hA : η ^ (-s) / (N : ℝ) + normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) ≤ Q)
    (hB : kerEnergyT (gTorus s η) (chargeT X ρ) +
        (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTorus s η (X i - X j) +
        ∫ x, ∫ y, fTorus s η (x - y) * ρ x * ρ y ≤ 2 * Q) :
    kerEnergyT (gTorus s η) (chargeT X ρ) ≤ (2 + ten2K d s) * Q := by
  obtain ⟨cb, hcb0, hcb⟩ := tpos_coef_bounds hd hs0 hsd
  have hI := ten2_quad_nonneg hd hs0 hsd (cb := cb) (η := η)
    (fun k hk => (hcb η hη hη1 k hk).2.2) hcb0 hη hρ
  have hS := ten2_S_lower hd hs0 hsd hη hN X
  have hK := ten2K_nonneg hd hs0 hsd
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hnp1 : 1 ≤ normT p ρ := ten2_normT_ge_one hp1 hρ
  have hpinv0 : 0 ≤ (p⁻¹).toReal := ENNReal.toReal_nonneg
  have hηe : 0 < η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := Real.rpow_pos_of_pos hη _
  have hηs : 0 < η ^ (-s) := Real.rpow_pos_of_pos hη _
  have hA0 : 0 ≤ η ^ (-s) / (N : ℝ) := by positivity
  have hdB : η ^ ((d : ℝ) - s) ≤ normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := by
    have h1 : η ^ ((d : ℝ) - s) ≤ η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) :=
      Real.rpow_le_rpow_of_exponent_ge hη hη1 (by
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        nlinarith)
    calc η ^ ((d : ℝ) - s) ≤ η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := h1
      _ = 1 * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hnp1 hηe.le
  have hηQ : η ^ ((d : ℝ) - s) ≤ Q := by
    have : 0 ≤ normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := by positivity
    linarith
  have hKQ : ten2K d s * η ^ ((d : ℝ) - s) ≤ ten2K d s * Q := mul_le_mul_of_nonneg_left hηQ hK
  nlinarith

/-- `‖∇g_≤ * ν‖_{p₂} ≲ (‖ν‖²_{g_η})^{1/2}`: from `potential_T` and `scoercive_T`. -/
theorem tunit_u_norm_bound (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ ρ : Torus d → ℝ, BddDensityT ρ →
      ∀ {N : ℕ}, 1 ≤ N → ∀ (X : Config d N) (E : ℝ), 0 ≤ E →
        kerEnergyT (gTorus s η) (chargeT X ρ) ≤ E →
        eLpNorm (fun x => ‖(chargeT X ρ).convForce (gloForceT s η) x‖)
          (ENNReal.ofReal (Whole.p2E d s)) volume ≤ ENNReal.ofReal (Cn * Real.sqrt E) := by
  obtain ⟨Cpot, hCpot, hpot⟩ := potential_T hd hs0 hsd
  obtain ⟨Cs, hCs, hsc⟩ := scoercive_T hd hs0 hsd
  refine ⟨Cpot * Real.sqrt Cs, by positivity, fun η hη hη1 ρ hρ N hN X E hE0 hE => ?_⟩
  have hfin := ten2_charge_finite hN X hρ
  have h1 := hpot η hη hη1 (chargeT X ρ) hfin
  have h2 := hsc η hη hη1 (chargeT X ρ) hfin (tunit_charge_mass ρ hρ hN X)
  set H := homSqT (-Whole.alphaE d s) (lowFreqT η 4 (chargeT X ρ).coef) with hH
  have hHle : H ≤ ENNReal.ofReal (Cs * E) :=
    le_trans (le_trans le_self_add h2)
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hE hCs.le))
  have h3 : H ^ ((1 : ℝ) / 2) ≤ ENNReal.ofReal (Real.sqrt Cs * Real.sqrt E) := by
    calc H ^ ((1 : ℝ) / 2) ≤ (ENNReal.ofReal (Cs * E)) ^ ((1 : ℝ) / 2) :=
          ENNReal.rpow_le_rpow hHle (by norm_num)
      _ = ENNReal.ofReal ((Cs * E) ^ ((1 : ℝ) / 2)) :=
          (ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hCs.le hE0) (by norm_num))
      _ = ENNReal.ofReal (Real.sqrt Cs * Real.sqrt E) := by
          rw [← Real.sqrt_eq_rpow, Real.sqrt_mul hCs.le]
  calc eLpNorm (fun x => ‖(chargeT X ρ).convForce (gloForceT s η) x‖)
        (ENNReal.ofReal (Whole.p2E d s)) volume
      ≤ ENNReal.ofReal Cpot * H ^ ((1 : ℝ) / 2) := h1
    _ ≤ ENNReal.ofReal Cpot * ENNReal.ofReal (Real.sqrt Cs * Real.sqrt E) := by gcongr
    _ = ENNReal.ofReal (Cpot * Real.sqrt Cs * Real.sqrt E) := by
        rw [← ENNReal.ofReal_mul hCpot.le]; congr 1; ring
    _ = ENNReal.ofReal (Cpot * Real.sqrt Cs * Real.sqrt E) := rfl

end HRS.Commutator.TorusNote
