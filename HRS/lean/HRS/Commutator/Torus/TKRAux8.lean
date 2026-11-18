import HRS.Commutator.Torus.TKRAux7

/-!
# T-KR helpers, part 8: size of `∇g_{≤}` and the near-field bound of `∇g_{>}`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.TorusNote

open HRS HRS.KernelGrad HRS.PDE.Kern

variable {d : ℕ} {s η : ℝ}

lemma tkr_norm_le_sum (w : Euc d) : ‖w‖ ≤ ∑ j, |w j| := by
  have h1 := HRS.KernelAux.norm_toLp_le_sum (WithLp.ofLp w)
  rwa [WithLp.toLp_ofLp] at h1

/-- `|(∇g_{≤})_i| ≲ η^{-(s+1)}`. -/
lemma tkr_glo_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd1 : s + 1 < d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (i : Fin d) (x : Torus d),
      |PleqT η (periodicRieszGrad d s) x i| ≤ K * η ^ (-(s + 1)) := by
  obtain ⟨A, hA0, hA⟩ := LatSum.low_sum (d := d) (by omega) (σ := s + 1) (by linarith)
  refine ⟨2 * Real.pi * |HDB.kapC d s| * (A * 3 ^ (s + 1)), by positivity, fun η hη hη1 i x => ?_⟩
  have hT2 : HRS.PDE.IsTrigPoly ⌈2 / η⌉₊
      (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k) :=
    tkr_isTrigPoly hη (fun k hk => by
      intro h0; apply hk; simp [h0])
  have h1 := tkr_glo hd hs0 hsd1 hη x i
  have h2 := HDB.norm_trig_le hT2 x
  rw [← h1, Complex.norm_real, Real.norm_eq_abs] at h2
  refine h2.trans ?_
  set J : ℕ := ⌈2 / η⌉₊ with hJ
  have hterm : ∀ k : Lattice d, ‖((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k‖ ≤
      2 * Real.pi * |HDB.kapC d s| *
        (if k = 0 then (0 : ℝ) else Lattice.enorm k ^ ((s + 1) - (d : ℝ))) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp [tkrCI, rieszCoeff]
    · rw [if_neg hk]
      have hχ0 : 0 ≤ tkrChi η k := Whole.cmxFB_chi_nonneg _
      have hχ1 : tkrChi η k ≤ 1 := Whole.cmxFB_chi_le_one _
      have hen : 0 < Lattice.enorm k := norm_pos_iff.2 (HDB.toEuc_ne_zero hk)
      have hc : ‖(2 * (Real.pi : ℂ) * Complex.I * ((k i : ℤ) : ℂ))‖ = 2 * Real.pi * |((k i : ℤ) : ℝ)| := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_intCast]
        simp [abs_of_pos Real.pi_pos]
      have hnorm : ‖((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k‖ =
          tkrChi η k * (2 * Real.pi * |((k i : ℤ) : ℝ)| * (|HDB.kapC d s| * ‖Lattice.toEuc k‖ ^ (s - (d : ℝ)))) := by
        unfold tkrCI
        rw [norm_mul, norm_mul, hc, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg hχ0, HDB.rieszCoeff_eq (by linarith : s < d) k, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      rw [hnorm]
      have hki := HRS.KernelAux.abs_coord_le_enorm k i
      have hpw : Lattice.enorm k ^ ((s + 1) - (d : ℝ)) = Lattice.enorm k * Lattice.enorm k ^ (s - (d : ℝ)) := by
        rw [show (s + 1) - (d : ℝ) = 1 + (s - (d : ℝ)) by ring, Real.rpow_add hen, Real.rpow_one]
      rw [hpw]
      have hp0 : 0 ≤ Lattice.enorm k ^ (s - (d : ℝ)) := Real.rpow_nonneg hen.le _
      have : ‖Lattice.toEuc k‖ = Lattice.enorm k := rfl
      rw [this]
      calc tkrChi η k * (2 * Real.pi * |((k i : ℤ) : ℝ)| * (|HDB.kapC d s| * Lattice.enorm k ^ (s - (d : ℝ))))
          ≤ 1 * (2 * Real.pi * Lattice.enorm k * (|HDB.kapC d s| * Lattice.enorm k ^ (s - (d : ℝ)))) := by
            gcongr
        _ = _ := by ring
  calc ∑ k ∈ boxF d J, ‖((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k‖
      ≤ ∑ k ∈ boxF d J, 2 * Real.pi * |HDB.kapC d s| *
        (if k = 0 then (0 : ℝ) else Lattice.enorm k ^ ((s + 1) - (d : ℝ))) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = 2 * Real.pi * |HDB.kapC d s| * ∑ k ∈ boxF d J,
        (if k = 0 then (0 : ℝ) else Lattice.enorm k ^ ((s + 1) - (d : ℝ))) := by rw [Finset.mul_sum]
    _ ≤ 2 * Real.pi * |HDB.kapC d s| * (A * (J : ℝ) ^ (s + 1)) :=
        mul_le_mul_of_nonneg_left (hA J) (by positivity)
    _ ≤ 2 * Real.pi * |HDB.kapC d s| * (A * (3 / η) ^ (s + 1)) := by
        gcongr
        have h3 : (J : ℝ) < 2 / η + 1 := Nat.ceil_lt_add_one (by positivity)
        have h4 : (1 : ℝ) ≤ 1 / η := by rw [le_div_iff₀ hη]; linarith
        have : 3 / η = 2 / η + 1 / η := by ring
        linarith
    _ = 2 * Real.pi * |HDB.kapC d s| * (A * 3 ^ (s + 1)) * η ^ (-(s + 1)) := by
        rw [Real.div_rpow (by norm_num) hη.le, Real.rpow_neg hη.le, div_eq_mul_inv]
        ring

/-- near-field bound for `∇g_{>}`: `|∇g_>(x)| ≲ |x|^{-s-1} + η^{-s-1}`. -/
lemma tkr_ghi_near (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd1 : s + 1 < d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ x : Torus d, x ≠ 0 →
      ‖ghiForceT s η x‖ ≤ K * (KernelGrad.tdist x 0 ^ (-s - 1) + η ^ (-(s + 1))) := by
  obtain ⟨C, hC⟩ := periodicRieszGrad_bound_tdist hd hs0 (by linarith : s < d)
  obtain ⟨K1, hK10, hK1⟩ := tkr_glo_bound hd hs0 hsd1
  refine ⟨|C| + d * K1, by positivity, fun η hη hη1 x hx => ?_⟩
  have hG := hC x hx
  have hglo : ‖gloForceT s η x‖ ≤ d * (K1 * η ^ (-(s + 1))) := by
    refine (tkr_norm_le_sum _).trans ?_
    calc ∑ j, |gloForceT s η x j| ≤ ∑ _j : Fin d, K1 * η ^ (-(s + 1)) :=
          Finset.sum_le_sum fun j _ => hK1 η hη hη1 j x
      _ = _ := by simp
  have h1 : 1 ≤ η ^ (-(s + 1)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hη hη1 (by linarith)
  have htd : 0 ≤ KernelGrad.tdist x 0 ^ (-s - 1) := Real.rpow_nonneg (KernelGrad.tdist_nonneg _ _) _
  calc ‖ghiForceT s η x‖ = ‖periodicRieszGrad d s x - gloForceT s η x‖ := rfl
    _ ≤ ‖periodicRieszGrad d s x‖ + ‖gloForceT s η x‖ := norm_sub_le _ _
    _ ≤ C * (KernelGrad.tdist x 0 ^ (-s - 1) + 1) + d * (K1 * η ^ (-(s + 1))) := add_le_add hG hglo
    _ ≤ |C| * (KernelGrad.tdist x 0 ^ (-s - 1) + η ^ (-(s + 1))) +
          d * K1 * (KernelGrad.tdist x 0 ^ (-s - 1) + η ^ (-(s + 1))) := by
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        have e1 : C * (KernelGrad.tdist x 0 ^ (-s - 1) + 1) ≤ |C| * (KernelGrad.tdist x 0 ^ (-s - 1) + η ^ (-(s + 1))) :=
          calc C * (KernelGrad.tdist x 0 ^ (-s - 1) + 1) ≤ |C| * (KernelGrad.tdist x 0 ^ (-s - 1) + 1) :=
                mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
            _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)
        have e2 : d * (K1 * η ^ (-(s + 1))) ≤ d * K1 * (KernelGrad.tdist x 0 ^ (-s - 1) + η ^ (-(s + 1))) := by
          have : 0 ≤ d * K1 := by positivity
          nlinarith [mul_nonneg this htd]
        linarith
    _ = _ := by ring

end HRS.Commutator.TorusNote
