import HRS.MS.GenPathAux13

/-!
# S5.6 packet P3 (moments): `E sup_t ‖R_N(t)‖_{ℓ²}` in `L^p`, `p ∈ {1,2}`

`s56_rem_moment`: `(E (sup_{t≤T} ‖σ_N ∫_0^t flucInteractionRd(U^{r,t}φ_·)(X_r,ρ_r) dr‖_{ℓ²})^p)^{1/p} ≤ C σ_N E_{N,p}`
(`E_{N,p} = S.energyMomentE N p P X`), from the pathwise bound `s56_rem_bound`, `s56_rem_moment_p1/p2` and the joint
measurability of the energy (`s56_energy_aemeas`).  This is the remainder term `‖R_N‖_{L^p(C_tℓ²)}` of the proof of S5.6.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

theorem s56_l2NormE_mul {ι : Type*} (c : ℝ) (v : ι → ℝ) :
    l2NormE (fun i => c * v i) = ENNReal.ofReal |c| * l2NormE v := by
  unfold l2NormE
  have h : ∀ i, ENNReal.ofReal ((c * v i) ^ 2) = ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (v i ^ 2) := fun i => by
    rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg c)]
  simp only [h]
  rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.ofReal_rpow_of_nonneg (sq_nonneg c) (by norm_num), ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]

theorem s56_rem_moment (b₀ : WholeBounds d) (hb : b₀.Valid) (p : ℝ) (hp : p = 1 ∨ p = 2) :
    ∃ C₀min : ℝ, ∀ b : WholeBounds d, b = { b₀ with C₀ := b.C₀ } → C₀min ≤ b.C₀ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : WholeSetup b, ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ) (X : ℝ≥0 → Ω → EucConfig d N), IsProgressive ℱ (ofNNRealTime X) →
      (∀ᵐ ζ ∂P, ∀ r ∈ Set.Icc (0 : ℝ) b.T, Function.Injective (X (Real.toNNReal r) ζ)) →
      (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) b.T, l2NormE (fun α : MultiIndex d =>
          S.σ N * ∫ r in Set.Icc (0 : ℝ) t, flucInteractionRd (S.dyn N)
            (propagatorW (S.coeff N) r t (oscTestFun b.m α)) (X (Real.toNNReal r) ζ) (S.ρ N r))) ^ p ∂P) ^
          (1 / p) ≤
        ENNReal.ofReal (C * S.σ N) * S.energyMomentE N p P X := by
  have hp1 : 1 ≤ p := by rcases hp with rfl | rfl <;> norm_num
  have hp0 : 0 < p := by linarith
  obtain ⟨C₀min, hC⟩ := s56_rem_bound b₀ hb
  refine ⟨C₀min, fun b hbeq hC0 => ?_⟩
  obtain ⟨C₁, hC₁0, hrem⟩ := hC b hbeq hC0
  have hbv : b.Valid := s56_valid_of_eq hb hbeq
  have hT0 : 0 ≤ b.T := hbv.hT.le
  refine ⟨C₁ * b.T, by positivity, fun S N hN Ω _ P _ ℱ X hprog hinj => ?_⟩
  have hσ : 0 ≤ S.σ N := by
    unfold WholeSetup.σ sigmaScale
    have := S.hκ N
    have := (S.hinvβ N).1
    split_ifs
    · exact (S.hκ N).le
    · exact le_min (S.hκ N).le (Real.sqrt_nonneg _)
  set en : Ω → ℝ → ℝ := fun ζ r => rieszModulatedEnergy d b.s (X (Real.toNNReal r) ζ)
    (HRS.Whole.withDensityReal (S.ρ N r)) + HRS.oN d b.s b.C₀ N with hen
  have hmeas : AEMeasurable (fun q : Ω × ℝ => en q.1 q.2) (P.prod (volume.restrict (Set.Icc 0 b.T))) :=
    s56_energy_aemeas b hbv S N P ℱ X hprog
  set Y : Ω → ℝ≥0∞ := fun ζ => ∫⁻ r in Set.Icc (0 : ℝ) b.T, ENNReal.ofReal (en ζ r) with hY
  have hpt : ∀ᵐ ζ ∂P, (⨆ t : Set.Icc (0 : ℝ) b.T, l2NormE (fun α : MultiIndex d =>
      S.σ N * ∫ r in Set.Icc (0 : ℝ) t, flucInteractionRd (S.dyn N)
        (propagatorW (S.coeff N) r t (oscTestFun b.m α)) (X (Real.toNNReal r) ζ) (S.ρ N r))) ≤
      ENNReal.ofReal (C₁ * S.σ N) * Y ζ := by
    filter_upwards [hinj] with ζ hζ
    refine iSup_le fun t => ?_
    have h1 := hrem S N hN (fun r => X (Real.toNNReal r) ζ) hζ t.1 t.2
    rw [s56_l2NormE_mul]
    rw [abs_of_nonneg hσ]
    calc ENNReal.ofReal (S.σ N) * l2NormE _ ≤ ENNReal.ofReal (S.σ N) * (ENNReal.ofReal C₁ * Y ζ) := by
          gcongr
      _ = ENNReal.ofReal (C₁ * S.σ N) * Y ζ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hσ, mul_comm (S.σ N) C₁]
  have hEset : ∀ r ∈ Set.Icc (0 : ℝ) b.T, (∫⁻ ζ, ENNReal.ofReal (en ζ r) ^ p ∂P) ^ (1 / p) ≤
      S.energyMomentE N p P X := by
    intro r hr
    have h := le_iSup (fun t : Set.Icc (0 : ℝ) b.T => (∫⁻ ζ, ENNReal.ofReal |rieszModulatedEnergy d b.s
        (X (Real.toNNReal t) ζ) (HRS.Whole.withDensityReal (S.ρ N t)) + HRS.oN d b.s b.C₀ N| ^ p ∂P) ^
        (1 / p)) ⟨r, hr⟩
    refine le_trans ?_ h
    gcongr with ζ
    exact le_abs_self _
  set E := S.energyMomentE N p P X
  rcases hp with rfl | rfl
  · -- `p = 1`
    have hE1 : ∀ r ∈ Set.Icc (0 : ℝ) b.T, ∫⁻ ζ, ENNReal.ofReal (en ζ r) ∂P ≤ E := fun r hr => by
      have := hEset r hr
      simpa using this
    have h1 := s56_rem_moment_p1 P en hmeas hE1
    calc (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) b.T, l2NormE (fun α : MultiIndex d =>
          S.σ N * ∫ r in Set.Icc (0 : ℝ) t, flucInteractionRd (S.dyn N)
            (propagatorW (S.coeff N) r t (oscTestFun b.m α)) (X (Real.toNNReal r) ζ) (S.ρ N r))) ^ (1 : ℝ) ∂P) ^
          (1 / (1 : ℝ))
        ≤ ∫⁻ ζ, ENNReal.ofReal (C₁ * S.σ N) * Y ζ ∂P := by
          simp only [ENNReal.rpow_one, div_one]
          exact lintegral_mono_ae hpt
      _ = ENNReal.ofReal (C₁ * S.σ N) * ∫⁻ ζ, Y ζ ∂P := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (C₁ * S.σ N) * (E * ENNReal.ofReal b.T) := by gcongr
      _ = ENNReal.ofReal (C₁ * b.T * S.σ N) * E := by
          rw [mul_comm E, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ C₁ * S.σ N)]
          congr 2; ring
  · -- `p = 2`
    have hE2 : ∀ r ∈ Set.Icc (0 : ℝ) b.T, ∫⁻ ζ, ENNReal.ofReal (en ζ r) ^ (2 : ℝ) ∂P ≤ E ^ (2 : ℝ) := by
      intro r hr
      have h := ENNReal.rpow_le_rpow (hEset r hr) (by norm_num : (0 : ℝ) ≤ 2)
      rwa [← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one] at h
    have h2 := s56_rem_moment_p2 P en hmeas hE2
    have hc0 : 0 ≤ C₁ * S.σ N := mul_nonneg hC₁0 hσ
    calc (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) b.T, l2NormE (fun α : MultiIndex d =>
          S.σ N * ∫ r in Set.Icc (0 : ℝ) t, flucInteractionRd (S.dyn N)
            (propagatorW (S.coeff N) r t (oscTestFun b.m α)) (X (Real.toNNReal r) ζ) (S.ρ N r))) ^ (2 : ℝ) ∂P) ^
          (1 / (2 : ℝ))
        ≤ (∫⁻ ζ, (ENNReal.ofReal (C₁ * S.σ N) * Y ζ) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by
          refine ENNReal.rpow_le_rpow (lintegral_mono_ae ?_) (by norm_num)
          filter_upwards [hpt] with ζ h
          exact ENNReal.rpow_le_rpow h (by norm_num)
      _ = ENNReal.ofReal (C₁ * S.σ N) * (∫⁻ ζ, Y ζ ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by
          have e : ∀ ζ, (ENNReal.ofReal (C₁ * S.σ N) * Y ζ) ^ (2 : ℝ) =
              ENNReal.ofReal (C₁ * S.σ N) ^ (2 : ℝ) * Y ζ ^ (2 : ℝ) := fun ζ =>
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
          simp only [e]
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top),
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ← ENNReal.rpow_mul]
          norm_num
      _ ≤ ENNReal.ofReal (C₁ * S.σ N) * (E * ENNReal.ofReal b.T) := by gcongr
      _ = ENNReal.ofReal (C₁ * b.T * S.σ N) * E := by
          rw [mul_comm E, ← mul_assoc, ← ENNReal.ofReal_mul hc0]
          congr 2; ring

end HRS.MS.GenPath
