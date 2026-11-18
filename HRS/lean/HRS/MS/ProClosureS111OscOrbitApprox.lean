import HRS.MS.ProClosureS111OscillatorCb
import HRS.MS.ProClosureS111InitialTestsApprox
import HRS.MS.S111K4ATD
import HRS.MS.R2WinOrbAux9
import HRS.MS.R26T6CD02

/-!
The actual thermal propagator satisfies the all-oscillator-test approximation
used by the interval operators. Constants in this approximation may depend
on the fixed finite horizon. The moving-window age estimates are supplied
separately by `physical_window_orbit_input`.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.S111X1 HRS.MS.S111K4AT

variable {d : ℕ}

theorem weightedSup_zero_le_cbNorm {k : ℕ} {f : Euc d → ℝ}
    (hf : MemCb k f) : weightedSupE k 0 f ≤ ENNReal.ofReal (cbNorm k f) := by
  unfold weightedSupE derivSupE
  refine iSup_le fun j => iSup_le fun i => iSup_le fun x => ?_
  simp only [Real.rpow_zero, one_mul]
  apply ENNReal.ofReal_le_ofReal
  have hj : (j : ℕ) ≤ k := Nat.lt_succ_iff.1 j.2
  calc
    |partialDeriv i f x| ≤ ‖iteratedFDeriv ℝ (j : ℕ) f x‖ :=
      HRS.MS.Lc.lc4_partial_le (j : ℕ) i x
    _ ≤ ⨆ y, ‖iteratedFDeriv ℝ (j : ℕ) f y‖ := le_ciSup (hf.2 j hj) x
    _ ≤ cbNorm k f := Finset.single_le_sum
      (f := fun l => ⨆ y, ‖iteratedFDeriv ℝ l f y‖)
      (fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _)
      (Finset.mem_range.2 (by omega))

/-- Quantitative finite-horizon regularity of the actual physical propagator
on every original oscillator test. -/
theorem physical_oscillator_cb_bound (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho) {H : ℝ} (hH : 0 ≤ H) :
    let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
    ∃ B : ℝ, 0 ≤ B ∧ ∀ phi : Euc d → ℝ,
      IsOscTest (wholeSpaceIndex d : ℝ) phi →
      ∀ v t : ℝ, 0 ≤ v → v ≤ t → t ≤ H →
        (∃ f, IsClassicalAdjointW C t phi f) ∧
        MemCb (2 * d + 9) (propagatorW C v t phi) ∧
        cbNorm (2 * d + 9) (propagatorW C v t phi) ≤
          B * oscNorm (wholeSpaceIndex d : ℝ) phi := by
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  obtain ⟨theta, htheta⟩ := HRS.MS.S52B.s52b_exists_ulCutoff d
  have hSch := HRS.MS.R2WinOrb.s103_rho_schwartz hd hs0 hsd ha hbeta hrho
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by
    unfold Matrix.IsSymm
    simp
  obtain ⟨K, hK⟩ := HRS.MS.S85.s85_witness5 hd s hs0 hsd theta htheta
    (2 * d + 9) (by omega) H beta⁻¹
    (a • (1 : Matrix (Fin d) (Fin d) ℝ)) (-1) 0 rho hH
    (inv_pos.2 hbeta) hQ hSch
  let k : ℕ := (2 * d + 9) + 1 + ⌈(d : ℝ) / 2⌉₊
  have hceil : ⌈(d : ℝ) / 2⌉₊ ≤ d :=
    Nat.ceil_le.2 (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  have hceil' : (⌈(d : ℝ) / 2⌉₊ : ℝ) ≤ d := by exact_mod_cast hceil
  have hn : (k : ℝ) + (d : ℝ) / 2 < (k + d + 1 : ℕ) := by
    push_cast
    linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hm : (d : ℝ) < ((wholeSpaceIndex d : ℝ) - (k + d + 1 : ℕ)) / 2 := by
    dsimp [k]
    unfold wholeSpaceIndex
    push_cast
    linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  obtain ⟨A, hA, hAb⟩ := oscillator_ulNorm_bound k (k + d + 1) hn hm htheta
  refine ⟨max K 0 * A, mul_nonneg (le_max_right _ _) hA, ?_⟩
  intro phi hphi v t hv hvt htH
  have hfin : ulNormE k theta phi < ⊤ :=
    lt_of_le_of_lt (hAb phi hphi) ENNReal.ofReal_lt_top
  have hcl : ContDiff ℝ (k : WithTop ℕ∞) phi :=
    hphi.1.of_le (by exact_mod_cast le_top)
  have hout := hK v t hv hvt htH phi hcl hfin
  have hC : C =
      (⟨s, -1, quadV (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0,
        beta⁻¹⟩ : WholeDyn d).coeff (fun _ => rho) := by
    dsimp [C]
    rw [HRS.MS.S21.s21_dyn_eq]
  rw [← hC] at hout
  refine ⟨hout.1, hout.2.1, hout.2.2.trans ?_⟩
  have hto : (ulNormE k theta phi).toReal ≤ A * oscNorm (wholeSpaceIndex d) phi := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hAb phi hphi)
    unfold oscNorm at h
    rw [ENNReal.toReal_ofReal (mul_nonneg hA (Real.sqrt_nonneg _))] at h
    exact h
  calc
    K * (ulNormE k theta phi).toReal ≤ max K 0 * (ulNormE k theta phi).toReal :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg
    _ ≤ max K 0 * (A * oscNorm (wholeSpaceIndex d) phi) :=
      mul_le_mul_of_nonneg_left hto (le_max_right _ _)
    _ = _ := by ring

theorem hermiteSection_eq_initialTestSection (m : ℝ) (n : ℕ)
    (phi : oscSub d m) : k4hs m n phi = (initialTestSection phi n : Euc d → ℝ) := by
  funext x
  rw [initialTestSection_apply]
  rfl

/-- The exact accepted all-test approximation structure is produced from
the physical thermal parameters. No orbit approximation premise is used. -/
theorem physical_osc_orbit_approx (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho) {H : ℝ} (hH : 0 ≤ H) :
    K4OscOrbitApprox ((quadraticGradientDyn d s a beta).coeff (fun _ => rho))
      (wholeSpaceIndex d : ℝ) H (2 * d + 8) := by
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  have hsd : s < (d : ℝ) := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨B, hB, hb⟩ := physical_oscillator_cb_bound hd hs0 hsd ha hbeta hrho hH
  have hX := x1Input_of_exist hd hs0 hs ha hbeta 0 hrho
    (exist_of_thermal hd hs0 hs ha hbeta hrho)
  have hbd : ∀ phi : Euc d → ℝ, IsOscTest (wholeSpaceIndex d : ℝ) phi →
      ∀ v ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc v H,
        weightedSupE (2 * d + 8 + 1) 0 (propagatorW C v t phi) ≤
          ENNReal.ofReal (B * oscNorm (wholeSpaceIndex d) phi) := by
    intro phi hphi v hv t ht
    have hh := hb phi hphi v t hv.1 ht.1 ht.2
    exact (weightedSup_zero_le_cbNorm hh.2.1).trans (ENNReal.ofReal_le_ofReal hh.2.2)
  refine ⟨?_, ?_, ⟨B, hB, hbd⟩, ?_⟩
  · intro phi hphi t ht
    exact (hb phi hphi 0 t le_rfl ht.1 ht.2).1
  · intro phi hphi v hv t ht
    exact (hb phi hphi v t hv.1 ht.1 ht.2).2.1.1
  · intro phi hphi
    let p : oscSub d (wholeSpaceIndex d) := ⟨phi, hphi⟩
    let pn : ℕ → oscSub d (wholeSpaceIndex d) := fun n => initialTestSection p n
    have hnorm : ∀ n,
        oscNorm (wholeSpaceIndex d) ((pn n - p : oscSub d (wholeSpaceIndex d)) : Euc d → ℝ) =
        oscNorm (wholeSpaceIndex d) ((p - pn n : oscSub d (wholeSpaceIndex d)) : Euc d → ℝ) := by
      intro n
      rw [← OscSpace.norm_ofFun _ (pn n - p).property.2,
        ← OscSpace.norm_ofFun _ (p - pn n).property.2,
        initialTest_ofFun_sub, initialTest_ofFun_sub, norm_sub_rev]
    have hlim : Tendsto (fun n => ENNReal.ofReal (B *
        oscNorm (wholeSpaceIndex d) ((pn n - p : oscSub d (wholeSpaceIndex d)) :
          Euc d → ℝ))) atTop (𝓝 0) := by
      have ht := (initialTestSection_tail p).const_mul B
      have he := ENNReal.tendsto_ofReal ht
      simpa only [hnorm, mul_zero, ENNReal.ofReal_zero] using he
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hlim (fun _ => bot_le)
    intro n
    refine iSup_le fun v => iSup_le fun hv => iSup_le fun t => iSup_le fun ht => ?_
    have hp : propagatorW C v t
        ((pn n - p : oscSub d (wholeSpaceIndex d)) : Euc d → ℝ) =
        propagatorW C v t (pn n : Euc d → ℝ) - propagatorW C v t phi := by
      change propagatorW C v t
          (fun x => (pn n : Euc d → ℝ) x - phi x) =
        (fun x => propagatorW C v t (pn n : Euc d → ℝ) x -
          propagatorW C v t phi x)
      have hh := hX.prop_lin (hv.1.trans ht.1) (pn n).property hphi (-1)
        v ⟨hv.1, ht.1⟩
      simpa only [x1C, C, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        neg_one_mul, sub_eq_add_neg] using hh
    have hsec : k4hs (wholeSpaceIndex d : ℝ) n phi = (pn n : Euc d → ℝ) :=
      hermiteSection_eq_initialTestSection _ n p
    rw [hsec, ← hp]
    exact hbd _ (pn n - p).property v hv t ht

/-- The same physical producer in the exact frozen D02 vocabulary. -/
theorem physical_frozen_osc_orbit_approx (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho) {H : ℝ} (hH : 0 ≤ H) :
    HRS.MS.R26T6.r26t6_OscOrbitApprox
      ((quadraticGradientDyn d s a beta).coeff (fun _ => rho))
      (wholeSpaceIndex d : ℝ) H (2 * d + 8) := by
  have h := physical_osc_orbit_approx hd hs0 hs ha hbeta hrho hH
  exact ⟨h.classical, h.smooth, h.bound, h.limit⟩

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.physical_osc_orbit_approx
#print axioms HRS.MS.ProClosureS111.physical_frozen_osc_orbit_approx
