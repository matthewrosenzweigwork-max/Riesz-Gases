import HRS.MS.R26T8AV1
import HRS.MS.R26T8AP16f

/-!
# S8.2 T8A V2: additivity of `pairA` on conormal pair functions
`r26t8a_V2_pairA_add`: for `G1, G2` of class `Conormal 2 1 M (σ-2)` (`σ < d`) and `x ≠ y`, `pairA (G1 + G2) x y = pairA G1 x y + pairA G2 x y`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_V2_rows (hd : 2 ≤ d) (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (hsd : sigma < d) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {Q : Euc d → Euc d → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hQ : Conormal 2 1 M (sigma - 2) A Q) :
    (∀ y, Integrable (r26t8a_Lop (critCoeff d a beta rho) (fun w => Q w y)) (HRS.Whole.withDensityReal rho) ∧
      Integrable (oneJ (critCoeff d a beta rho) (fun w => Q w y)) (HRS.Whole.withDensityReal rho)) ∧
    (∀ x, Integrable (r26t8a_Lop (critCoeff d a beta rho) (Q x)) (HRS.Whole.withDensityReal rho) ∧
      Integrable (oneJ (critCoeff d a beta rho) (Q x)) (HRS.Whole.withDensityReal rho)) := by
  have hCnu : (critCoeff d a beta rho).ν = beta⁻¹ := r26t8a_critCoeff_nu a beta rho
  have hLop : ∀ (G : Euc d → Euc d → ℝ) (y : Euc d),
      (fun x => r26t8a_Lop (critCoeff d a beta rho) (fun w => G w y) x) =
      fun x => beta⁻¹ * Laplacian.laplacian (fun z => G z y) x +
        inner ℝ ((critCoeff d a beta rho).drift 0 x) (pairGradX G x y) := by
    intro G y; funext x
    unfold r26t8a_Lop; rw [hCnu]; rfl
  have hQs : Conormal 2 1 M (sigma - 2) A (fun x y => Q y x) := r26t8a_f24_conormal_swap hchi hQ
  refine ⟨fun y => ⟨?_, (r26t8a_g5_row d hd 0 1 a beta M sigma ha hbeta hM hsd rho hrho Q A hA hQ y).1⟩,
    fun x => ⟨?_, (r26t8a_g5_row d hd 0 1 a beta M sigma ha hbeta hM hsd rho hrho (fun x y => Q y x) A hA hQs x).1⟩⟩
  · have := (r26t8a_local_ibp_gen d hd 0 1 a beta M sigma A ha hbeta hM hsd hA rho hrho Q hQ y).1
    have e := hLop Q y
    show Integrable (fun x => r26t8a_Lop (critCoeff d a beta rho) (fun w => Q w y) x) _
    rw [e]; exact this
  · have := (r26t8a_local_ibp_gen d hd 0 1 a beta M sigma A ha hbeta hM hsd hA rho hrho
      (fun x y => Q y x) hQs x).1
    have e := hLop (fun x y => Q y x) x
    show Integrable (fun y => r26t8a_Lop (critCoeff d a beta rho) (Q x) y) _
    rw [show (fun y => r26t8a_Lop (critCoeff d a beta rho) (Q x) y) =
      fun y => r26t8a_Lop (critCoeff d a beta rho) (fun w => (fun x y => Q y x) w x) y from rfl, e]
    exact this

theorem r26t8a_V2_projGen_add (C : WholeCoeff d) (mu : Measure (Euc d)) (hmu : mu ≪ volume)
    (hd : 2 ≤ d) {g1 g2 : Euc d → ℝ} {y0 x : Euc d}
    (hL1 : Integrable (r26t8a_Lop C g1) mu) (hL2 : Integrable (r26t8a_Lop C g2) mu)
    (hJ1 : Integrable (oneJ C g1) mu) (hJ2 : Integrable (oneJ C g2) mu)
    (hLadd : ∀ u, u ≠ y0 → r26t8a_Lop C (fun w => g1 w + g2 w) u = r26t8a_Lop C g1 u + r26t8a_Lop C g2 u)
    (hJadd : ∀ u, u ≠ y0 → oneJ C (fun w => g1 w + g2 w) u = oneJ C g1 u + oneJ C g2 u) (hx : x ≠ y0) :
    HRS.Whole.projGeneratorW C mu 0 (fun w => g1 w + g2 w) x =
      HRS.Whole.projGeneratorW C mu 0 g1 x + HRS.Whole.projGeneratorW C mu 0 g2 x := by
  haveI : Nontrivial (Euc d) := r26t8a_nontrivial hd
  have hgen : ∀ u, u ≠ y0 → generatorW C 0 (fun w => g1 w + g2 w) u = generatorW C 0 g1 u + generatorW C 0 g2 u := by
    intro u hu
    have e := fun g => congrFun (r26t8a_generatorW_split C g) u
    rw [e (fun w => g1 w + g2 w), e g1, e g2, hLadd u hu, hJadd u hu]
    ring
  have hi1 : Integrable (generatorW C 0 g1) mu := by
    rw [r26t8a_generatorW_split]; exact hL1.add hJ1
  have hi2 : Integrable (generatorW C 0 g2) mu := by
    rw [r26t8a_generatorW_split]; exact hL2.add hJ2
  have hae : ∀ᵐ u ∂mu, u ≠ y0 := hmu.ae_le (compl_mem_ae_iff.mpr (measure_singleton y0))
  have hint : ∫ u, generatorW C 0 (fun w => g1 w + g2 w) u ∂mu =
      ∫ u, generatorW C 0 g1 u ∂mu + ∫ u, generatorW C 0 g2 u ∂mu := by
    rw [← integral_add hi1 hi2]
    refine integral_congr_ae ?_
    filter_upwards [hae] with u hu using hgen u hu
  unfold HRS.Whole.projGeneratorW
  rw [hgen x hx, hint]
  ring

theorem r26t8a_V2_pairA_add (hd : 2 ≤ d) (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (hsd : sigma < d) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {G1 G2 : Euc d → Euc d → ℝ} {A1 A2 : ℝ}
    (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (h1 : Conormal 2 1 M (sigma - 2) A1 G1) (h2 : Conormal 2 1 M (sigma - 2) A2 G2)
    {x y : Euc d} (hxy : x ≠ y) :
    pairA (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) (fun x y => G1 x y + G2 x y) x y =
      pairA (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) G1 x y +
      pairA (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) G2 x y := by
  have hmu : HRS.Whole.withDensityReal rho ≪ (volume : Measure (Euc d)) :=
    withDensity_absolutelyContinuous _ _
  obtain ⟨r1, c1⟩ := r26t8a_V2_rows hd a beta M sigma ha hbeta hM hsd rho hrho hchi hA1 h1
  obtain ⟨r2, c2⟩ := r26t8a_V2_rows hd a beta M sigma ha hbeta hM hsd rho hrho hchi hA2 h2
  have h1s : Conormal 2 1 M (sigma - 2) A1 (fun x y => G1 y x) := r26t8a_f24_conormal_swap hchi h1
  have h2s : Conormal 2 1 M (sigma - 2) A2 (fun x y => G2 y x) := r26t8a_f24_conormal_swap hchi h2
  have hx := r26t8a_V2_projGen_add (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) hmu hd (y0 := y)
    (g1 := fun w => G1 w y) (g2 := fun w => G2 w y) (r1 y).1 (r2 y).1 (r1 y).2 (r2 y).2
    (fun u hu => r26t8a_V1_Lop_add _ (r26t8a_V1_slice1 h1 hu) (r26t8a_V1_slice1 h2 hu))
    (fun u hu => r26t8a_V1_oneJ_add hd a beta M sigma ha hbeta hM hsd rho hrho hA1 hA2 hchi h1 h2 hu) hxy
  have hy := r26t8a_V2_projGen_add (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) hmu hd (y0 := x)
    (g1 := G1 x) (g2 := G2 x) (c1 x).1 (c2 x).1 (c1 x).2 (c2 x).2
    (fun u hu => r26t8a_V1_Lop_add _ (r26t8a_V1_slice2 h1 (Ne.symm hu)) (r26t8a_V1_slice2 h2 (Ne.symm hu)))
    (fun u hu => r26t8a_V1_oneJ_add hd a beta M sigma ha hbeta hM hsd rho hrho hA1 hA2 hchi h1s h2s hu) hxy.symm
  unfold pairA
  beta_reduce
  linarith [hx, hy]

end HRS.MS.R26T8A
