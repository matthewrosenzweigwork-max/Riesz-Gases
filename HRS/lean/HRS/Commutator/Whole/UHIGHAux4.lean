import HRS.Commutator.Whole.UHIGHAux3

/-!
# Packet CMX-HIGH auxiliary 4: `high_particles` (`(5.atomicclosing)`, `[N] L699-714`)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole.UHIGH

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

theorem uhigh_exponent_relation (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    0 < p1E d s ∧ 0 < p2E d s ∧ (1 : ℝ) / 2 + 1 / p1E d s + 1 / p2E d s = 1 := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 0 < (d : ℝ) - s - 2 := by linarith
  have h2 : 0 < s + 2 := by linarith
  have h3 : 0 < (d : ℝ) := by linarith
  refine ⟨by unfold p1E; positivity, by unfold p2E; positivity, ?_⟩
  unfold p1E p2E
  field_simp
  ring

theorem uhigh_particles_main (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ p q : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p → p⁻¹ + q⁻¹ = 1 →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp →
      ∀ ρ : Euc d → ℝ, BddCptDensity ρ →
      ∀ (N : ℕ) (X : Fin N → Euc d), 1 ≤ N → Function.Injective X →
      ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
        (1 / (N : ℝ)) * ∑ i, |inner ℝ (Pgt 1 v (X i)) ((chargeOf X ρ).convForce (gloForce s) (X i))| ≤
          C * K * (modEnergy s X ρ + Cp * (1 / (N : ℝ) + normE p ρ)) := by
  obtain ⟨Cz, hCz, hzs⟩ := vhi_cube_sampling hd hs0 hsd
  obtain ⟨Cps, Cu, hCps, hCu, hu⟩ := uhigh_u_main hd hs0 hsd
  obtain ⟨Ci, hCi, hint⟩ := intro_control hd hs0 hsd
  obtain ⟨Cb, hCb, hEC⟩ := energy_control hd hs0 hsd
  obtain ⟨hp1pos, hp2pos, hrel⟩ := uhigh_exponent_relation hd hs0 hsd
  refine ⟨Cz * Cu * Cps * Ci, by positivity, fun p q hp hpq => ?_⟩
  obtain ⟨Cp1, hCp1, hI⟩ := hint p q hp hpq
  obtain ⟨Cp2, hCp2, hE⟩ := hEC p q hp hpq
  refine ⟨max Cp1 Cp2, lt_max_of_lt_left hCp1,
    fun Cp hCp ρ hρ N X hN hX v K hv => ?_⟩
  have h1 := hI Cp (le_trans (le_max_left _ _) hCp) ρ hρ N X hN hX
  obtain ⟨h0, -⟩ := hE Cp (le_trans (le_max_right _ _) hCp) ρ hρ N X hN hX
  set Ec := modEnergy s X ρ + Cp * (1 / (N : ℝ) + normE p ρ) with hEc
  have hNpos : (0 : ℝ) < 1 / (N : ℝ) := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hnp : 0 ≤ normE p ρ := ENNReal.toReal_nonneg
  have hf0 : 0 ≤ normE q (fTrunc s 1 : Euc d → ℝ) := ENNReal.toReal_nonneg
  have hEc0 : 0 ≤ Ec := by
    have : 0 ≤ (1 + normE q (fTrunc s 1 : Euc d → ℝ)) * normE p ρ :=
      mul_nonneg (by linarith) hnp
    linarith
  obtain ⟨L, F, hF0, hL, ⟨w, hrep, hw⟩, hLF⟩ := hv
  have hfd : HasFracData d s v L w F := ⟨hL, hrep, hw⟩
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  have hFK : F ≤ K := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hadm := chargeOf_admissible ρ hρ hN X
  set T : ℝ≥0∞ := ENNReal.ofReal (Ci * Ec) with hT
  have hTtop : T ≠ ⊤ := ENNReal.ofReal_ne_top
  have hhom : homSqE (-alphaE d s) (lowFreq 4 (chargeOf X ρ).fourier) ≤ T :=
    le_trans (le_trans le_self_add le_self_add) h1
  have hocc : ENNReal.ofReal (∑' j : Fin d → ℤ, occ X j ^ 2) ≤ T := le_trans le_add_self h1
  obtain ⟨-, -, -, -, hcube⟩ :=
    hu (chargeOf X ρ) hadm.1 hadm.2.1 (fun _ => hadm.2.2) T hTtop hhom
  have hzv := hzs v L w F hfd
  set V : Euc d → Euc d := Pgt 1 v with hV
  set u : Euc d → Euc d := fun x => (chargeOf X ρ).convForce (gloForce s) x with hu'
  -- the ENNReal inequality
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
  have hTq : T ^ ((1 : ℝ) / 2) < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) hTtop
  have hmain : ENNReal.ofReal ((1 / (N : ℝ)) * ∑ i, |inner ℝ (V (X i)) (u (X i))|) ≤
      ENNReal.ofReal (Cz * Cu * Cps * Ci * K * Ec) := by
    calc ENNReal.ofReal ((1 / (N : ℝ)) * ∑ i, |inner ℝ (V (X i)) (u (X i))|)
        ≤ (N : ℝ≥0∞)⁻¹ * ∑ i, (‖V (X i)‖ₑ * ‖u (X i)‖ₑ) := hsum
      _ ≤ (ENNReal.ofReal (∑' j, occ X j ^ 2)) ^ ((1 : ℝ) / 2) *
            (cubeSupNorm (p1E d s) V * cubeSupNorm (p2E d s) u) :=
          uhigh_particle_holder hN X V u hp1pos hp2pos hrel
      _ ≤ T ^ ((1 : ℝ) / 2) * (ENNReal.ofReal (Cz * F) *
            (ENNReal.ofReal Cu * (ENNReal.ofReal Cps * T ^ ((1 : ℝ) / 2)))) := by
          gcongr
      _ = ENNReal.ofReal (Cz * F) * ENNReal.ofReal Cu * ENNReal.ofReal Cps * T := by
          have := uhigh_sqrt_mul_sqrt T
          generalize T ^ ((1 : ℝ) / 2) = Y at this ⊢
          rw [← this]
          ring
      _ = ENNReal.ofReal (Cz * F * Cu * Cps * (Ci * Ec)) := by
          rw [hT, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (Cz * Cu * Cps * Ci * K * Ec) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have e1 : Cz * F * Cu * Cps * (Ci * Ec) = (Cz * Cu * Cps * Ci * Ec) * F := by ring
          have e2 : Cz * Cu * Cps * Ci * K * Ec = (Cz * Cu * Cps * Ci * Ec) * K := by ring
          rw [e1, e2]
          exact mul_le_mul_of_nonneg_left hFK (by positivity)
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hmain

end HRS.Commutator.Whole.UHIGH
