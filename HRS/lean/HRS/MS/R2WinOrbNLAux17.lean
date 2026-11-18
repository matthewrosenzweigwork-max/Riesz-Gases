import HRS.MS.R2WinOrbNLAux16

/-!
# S10.3 (nonlinear branch), part 17: the jets of the fifth orbit datum `L_t²φ_α + ∂_tL_tφ_α`

Prefix `s103n_`, namespace `HRS.MS.R2WinOrbNL`.  `s103n_g5_data`: for a density `h = ρ_t` and a derivative `h' = ρ'_t` with the weighted decay
`U2Dec (8d+83) L A_ρ h`, `U2Dec (8d+81) L A_d h'`, the function `L_h(L_hφ_α) + Q_{h'}φ_α` lies in `Bd (8d+80) (K₅ (1+A_ρ)²(1+A_d) b_α)`.
Route: `L_hφ_α ∈ Sy (8d+82)` (`s103n_Lt_sy`, the partial derivatives of `φ_α` decay like `⟨x⟩⁻²`), `L_h` maps `Sy (N+2)` into `Bd N` (`s103n_Lt_bd`),
and `Q_{h'}φ_α ∈ Bd N` (`s103n_Q_bd`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Ul HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.Mov63 HRS.MS.Who HRS.MS.BreakdownS67
  HRS.MS.MovAdj HRS.MS.R2WinOrb

variable {d : ℕ}

theorem s103n_phi_smooth (α : MultiIndex d) :
    ContDiff ℝ ∞ (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) := by
  obtain ⟨f, hf⟩ : ∃ f : SchwartzMap (Euc d) ℝ, ⇑f = oscTestFun ((24 * d + 240 : ℕ) : ℝ) α := by
    have hmem : oscTestFun ((24 * d + 240 : ℕ) : ℝ) α ∈ mo_Hspan d := by
      have : oscTestFun ((24 * d + 240 : ℕ) : ℝ) α =
          (oscEigenvalue d α ^ (-(((24 * d + 240 : ℕ) : ℝ) / 2))) • hermiteFunD α := by
        funext x; simp [oscTestFun]
      rw [this]
      exact Submodule.smul_mem _ _ (mova3_hermite_mem α)
    exact mova3c_hspan_schwartz hmem
  rw [← hf]
  exact f.smooth _

theorem s103n_gen_frozen {s a β : ℝ} (ρ : ℝ → Euc d → ℝ) (t : ℝ) (u : Euc d → ℝ) (x : Euc d) :
    generatorW ((quadraticGradientDyn d s a β).coeff ρ) t u x =
      generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ t)) 0 u x := by
  rw [HRS.MH.DualityRd.generatorW_coeff, HRS.MH.DualityRd.generatorW_coeff]

set_option maxHeartbeats 3200000 in
theorem s103n_g5_data {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) {L : ℝ}
    (hL : (d : ℝ) + ((8 * d + 80 : ℕ) : ℝ) + s + 5 < L) :
    ∃ K5 : ℝ, 0 ≤ K5 ∧ ∀ (Aρ Ad : ℝ), 0 ≤ Aρ → 0 ≤ Ad → ∀ (h h' : Euc d → ℝ) (α : MultiIndex d),
      U2Dec (8 * d + 83) L Aρ h → U2Dec (8 * d + 81) L Ad h' →
      Bd (8 * d + 80) (K5 * (1 + Aρ) ^ 2 * (1 + Ad) * s103_b d α)
        (fun x => generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => h)) 0
            (fun y => generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => h)) 0
              (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) y) x +
          s103nQ d s h' (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) x) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  obtain ⟨Kφ, hKφ0, hKφ⟩ := s103n_phi_sy H.hd H.hs0 H.hsd
  have hL1 : (d : ℝ) + ((8 * d + 82 : ℕ) : ℝ) + s + 3 < L := by push_cast at hL ⊢; linarith
  have hL2 : (d : ℝ) + ((8 * d + 80 : ℕ) : ℝ) + s + 3 < L := by push_cast at hL ⊢; linarith
  obtain ⟨C0, C1, hC0, hC1, hSy⟩ := s103n_Lt_sy H.hd H.hs0 H.hsd a β (8 * d + 82) hL1
  obtain ⟨C0', C1', hC0', hC1', hBd⟩ := s103n_Lt_bd H.hd H.hs0 H.hsd a β (8 * d + 80) hL2
  obtain ⟨Cq, hCq0, hQ⟩ := s103n_Q_bd H.hd H.hs0 H.hsd (8 * d + 80) hL2
  refine ⟨Kφ * ((C0' + C1') * (C0 + C1) + Cq), by positivity, fun Aρ Ad hAρ hAd h h' α hh hh' => ?_⟩
  have hb0 := s103_b_nonneg (d := d) α
  set φ : Euc d → ℝ := oscTestFun ((24 * d + 240 : ℕ) : ℝ) α with hφ
  have hDS : ∀ i : Fin d, SyN 2 (8 * d + 82 + 1) (Kφ * s103_b d α)
      (fun y => fderiv ℝ φ y (EuclideanSpace.single i (1 : ℝ))) := fun i => hKφ α i
  have hφsm : ContDiff ℝ ((8 * d + 82 + 2 : ℕ) : WithTop ℕ∞) φ :=
    (s103n_phi_smooth α).of_le (s103_cast_le_infty _)
  have hh1 : U2Dec (8 * d + 82 + 1) L Aρ h := hh
  have hg1 := hSy Aρ h hAρ hh1 (Kφ * s103_b d α) φ hφsm hDS
  have hh2 : U2Dec (8 * d + 80 + 1) L Aρ h := ⟨hh.1.of_le (by exact_mod_cast (by omega : 8 * d + 80 + 1 ≤ 8 * d + 83)),
    fun m hm => hh.2 m (by omega)⟩
  have hg2 := hBd Aρ h hAρ hh2 _ _ hg1
  -- the derivative of the generator
  have hDg : ∀ i : Fin d, Bd (8 * d + 80 + 1) (Kφ * s103_b d α)
      (fun y => fderiv ℝ φ y (EuclideanSpace.single i (1 : ℝ))) := fun i => ((hDS i).bd).mono_N (by omega)
  have hh'1 : U2Dec (8 * d + 80 + 1) L Ad h' := hh'
  have hq := hQ Ad h' hAd hh'1 _ φ hDg
  have hsum := hg2.add hq
  refine hsum.mono_A ?_
  have hKb : 0 ≤ Kφ * s103_b d α := mul_nonneg hKφ0 hb0
  have h1 : C0' + C1' * Aρ ≤ (C0' + C1') * (1 + Aρ) := by nlinarith
  have h2 : C0 + C1 * Aρ ≤ (C0 + C1) * (1 + Aρ) := by nlinarith
  have h3 : 0 ≤ C0' + C1' * Aρ := by positivity
  have h4 : 0 ≤ C0 + C1 * Aρ := by positivity
  have hP : (C0' + C1' * Aρ) * ((C0 + C1 * Aρ) * (Kφ * s103_b d α)) ≤
      ((C0' + C1') * (C0 + C1) * (1 + Aρ) ^ 2) * (Kφ * s103_b d α) := by
    calc (C0' + C1' * Aρ) * ((C0 + C1 * Aρ) * (Kφ * s103_b d α)) =
        ((C0' + C1' * Aρ) * (C0 + C1 * Aρ)) * (Kφ * s103_b d α) := by ring
      _ ≤ (((C0' + C1') * (1 + Aρ)) * ((C0 + C1) * (1 + Aρ))) * (Kφ * s103_b d α) := by
          gcongr
      _ = _ := by ring
  have hQb : Cq * Ad * (Kφ * s103_b d α) ≤ (Cq * (1 + Aρ) ^ 2 * (1 + Ad)) * (Kφ * s103_b d α) := by
    have : Cq * Ad ≤ Cq * (1 + Aρ) ^ 2 * (1 + Ad) := by
      have e1 : (1 : ℝ) ≤ (1 + Aρ) ^ 2 := by nlinarith
      nlinarith [mul_nonneg hCq0 hAd, mul_nonneg hCq0 hAρ]
    exact mul_le_mul_of_nonneg_right this hKb
  have hP' : ((C0' + C1') * (C0 + C1) * (1 + Aρ) ^ 2) * (Kφ * s103_b d α) ≤
      ((C0' + C1') * (C0 + C1) * (1 + Aρ) ^ 2 * (1 + Ad)) * (Kφ * s103_b d α) := by
    refine mul_le_mul_of_nonneg_right ?_ hKb
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (add_nonneg hC0' hC1') (add_nonneg hC0 hC1))
      (sq_nonneg (1 + Aρ))) hAd]
  calc _ ≤ ((C0' + C1') * (C0 + C1) * (1 + Aρ) ^ 2 * (1 + Ad)) * (Kφ * s103_b d α) +
        (Cq * (1 + Aρ) ^ 2 * (1 + Ad)) * (Kφ * s103_b d α) := by
        refine add_le_add (hP.trans hP') hQb
    _ = _ := by ring

end HRS.MS.R2WinOrbNL

end
