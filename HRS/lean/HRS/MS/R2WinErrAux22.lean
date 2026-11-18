import HRS.MS.R2WinErrAux21

/-!
# S10.4 input `hdyn` for the stationary trajectory (part 2): identification of the forcing families and `hevol`

`s104_Fm_eq`, `s104_F2_eq`: `r2CommForcingMov (t,r) = D(G0(t-r))(X_r)` and `s104_F2 (s',r) = D(G1(s'-r))(X_r)` for the stationary coefficient;
`s104_hevol_stat`: the integrated evolution inequality of `S104RealInput`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinErr

open HRS HRS.Whole HRS.MS.S53

variable {d N : ℕ}


variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
  {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρβ) (α : MultiIndex d) {T0 : ℝ}
  {G0 G1 G2 : ℝ → Euc d → ℝ}

include hd hs0 hsd ha hβ hρ in
theorem s104_Fm_eq {Ω : Type*}
    (hG : S104StatOrbit ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
      (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) T0 G0 G1 G2)
    (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) {t r : ℝ} (ht : t ∈ Icc (0 : ℝ) T0) (hr : r ∈ Icc (0 : ℝ) t) :
    r2CommForcingMov ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) s
      ((24 * d + 240 : ℕ) : ℝ) (fun _ => ρβ) X α t r ζ = s53_Dk s ρβ (G0 (t - r)) (X r.toNNReal ζ) := by
  unfold r2CommForcingMov s53_Dk
  rw [s104_prop_shift hd hs0 hsd ha hβ hρ hr (hG.ex0 t ht), ← hG.eq0 (t - r) ⟨by linarith [hr.2], by linarith [ht.2, hr.1]⟩]

include hd hs0 hsd ha hβ hρ in
theorem s104_F2_eq {Ω : Type*}
    (hG : S104StatOrbit ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
      (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) T0 G0 G1 G2)
    (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) {s' r : ℝ} (hs' : s' ∈ Icc (0 : ℝ) T0) (hr : r ∈ Icc (0 : ℝ) s') :
    s104_F2 ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) s ((24 * d + 240 : ℕ) : ℝ) (fun _ => ρβ) X α
      (s', r) ζ = s53_Dk s ρβ (G1 (s' - r)) (X r.toNNReal ζ) := by
  unfold s104_F2 s53_Dk
  simp only [if_pos hr.2]
  have hgen : ∀ g : Euc d → ℝ, generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) s' g =
      generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) 0 g := fun g => rfl
  rw [hgen, s104_prop_shift hd hs0 hsd ha hβ hρ hr (hG.ex1 s' hs'),
    ← hG.eq1 (s' - r) ⟨by linarith [hr.2], by linarith [hs'.2, hr.1]⟩]


include hd hs0 hsd ha hβ hρ in
theorem s104_hevol_stat {Ω : Type*} {Mρ : ℝ} (hN : 0 < N)
    (hG : S104StatOrbit ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
      (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) T0 G0 G1 G2) (ctx : S53Ctx s ρβ Mρ)
    (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) {r t0 t : ℝ} (hr0 : 0 ≤ r) (hrt0 : r ≤ t0) (ht0t : t0 ≤ t)
    (htT : t ≤ T0) :
    ENNReal.ofReal |r2CommForcingMov ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) s
        ((24 * d + 240 : ℕ) : ℝ) (fun _ => ρβ) X α t r ζ| ≤
      ENNReal.ofReal |r2CommForcingMov ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) s
        ((24 * d + 240 : ℕ) : ℝ) (fun _ => ρβ) X α t0 r ζ| +
      ∫⁻ s' in Ioc t0 t, ENNReal.ofReal |s104_F2 ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) s
        ((24 * d + 240 : ℕ) : ℝ) (fun _ => ρβ) X α (s', r) ζ| := by
  have ht0 : t0 ∈ Icc (0 : ℝ) T0 := ⟨hr0.trans hrt0, ht0t.trans htT⟩
  have ht : t ∈ Icc (0 : ℝ) T0 := ⟨hr0.trans (hrt0.trans ht0t), htT⟩
  rw [s104_Fm_eq hd hs0 hsd ha hβ hρ α hG X ζ ht ⟨hr0, hrt0.trans ht0t⟩,
    s104_Fm_eq hd hs0 hsd ha hβ hρ α hG X ζ ht0 ⟨hr0, hrt0⟩]
  set Z := X r.toNNReal ζ with hZ
  have hc1 : S53Cont T0 G1 := s53_cont_of_diff hG.cb1 hG.cb2 hG.diff12
  have hft := s104_stat_ftc ctx hN hG.cb0 hG.cb1 hG.diff01 hc1 Z (τ0 := t0 - r) (τ := t - r)
    (by linarith) (by linarith) (by linarith)
  rw [hft]
  have hint : ∫⁻ s' in Ioc t0 t, ENNReal.ofReal |s104_F2 ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) s
        ((24 * d + 240 : ℕ) : ℝ) (fun _ => ρβ) X α (s', r) ζ| =
      ∫⁻ σ in Ioc (t0 - r) (t - r), ENNReal.ofReal |s53_Dk s ρβ (G1 σ) Z| := by
    rw [s104_lintegral_Ioc_sub (fun σ => ENNReal.ofReal |s53_Dk s ρβ (G1 σ) Z|) t0 t r]
    refine setLIntegral_congr_fun measurableSet_Ioc fun s' hs' => ?_
    have hs'T : s' ∈ Icc (0 : ℝ) T0 := ⟨by linarith [hs'.1], hs'.2.trans htT⟩
    rw [s104_F2_eq hd hs0 hsd ha hβ hρ α hG X ζ hs'T ⟨hr0, by linarith [hs'.1]⟩]
  rw [hint]
  calc ENNReal.ofReal |s53_Dk s ρβ (G0 (t0 - r)) Z + ∫ σ in Ioc (t0 - r) (t - r), s53_Dk s ρβ (G1 σ) Z|
      ≤ ENNReal.ofReal (|s53_Dk s ρβ (G0 (t0 - r)) Z| + |∫ σ in Ioc (t0 - r) (t - r), s53_Dk s ρβ (G1 σ) Z|) :=
        ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ ≤ ENNReal.ofReal |s53_Dk s ρβ (G0 (t0 - r)) Z| +
        ENNReal.ofReal |∫ σ in Ioc (t0 - r) (t - r), s53_Dk s ρβ (G1 σ) Z| := ENNReal.ofReal_add_le
    _ ≤ _ := by
        refine add_le_add le_rfl ?_
        have := enorm_integral_le_lintegral_enorm (μ := volume.restrict (Ioc (t0 - r) (t - r)))
          (fun σ => s53_Dk s ρβ (G1 σ) Z)
        simpa [Real.enorm_eq_ofReal_abs] using this

end HRS.MS.R2WinErr
