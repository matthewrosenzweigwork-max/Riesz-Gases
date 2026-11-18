import HRS.MS.R2InterpAux34
import HRS.MC.S7PIHPde

/-!
# S10.2 (worker S102), part 35 (packet B2, interpolation): Gaussian expectations under a PSD covariance increment

For `S₀, Δ ⪰ 0` and `G ∈ C_b²(ℝ^q)`: if `|∑_{ij} Δ_ij E_θ ∂_ijG| ≤ K` along the path `S₀ + (1-θ)Δ`, then
`|E G(c + N(0,S₀ + Δ)) - E G(c + N(0,S₀))| ≤ K/2` (generic heat equation `s7_PIH_heat_pde_proof` with the constant rate `Δ` and the mean value theorem).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MC.Sec7.PI

theorem s102_gauss_interp {q : ℕ} (S0 Δ : Matrix (Fin q) (Fin q) ℝ) (hS0 : S0.PosSemidef) (hΔ : Δ.PosSemidef)
    {G : EuclideanSpace ℝ (Fin q) → ℝ} (hG : MemCb 2 G) (c : EuclideanSpace ℝ (Fin q)) {K : ℝ}
    (hK : ∀ θ ∈ Icc (0 : ℝ) 1, |∑ i, ∑ j, Δ i j * ∫ x, iteratedFDeriv ℝ 2 G (c + x)
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] ∂(multivariateGaussian 0 (S0 + (1 - θ) • Δ))| ≤ K) :
    |gaussHeat (fun _ => S0 + Δ) G 0 c - gaussHeat (fun _ => S0) G 0 c| ≤ K / 2 := by
  set S : ℝ → Matrix (Fin q) (Fin q) ℝ := fun θ => S0 + (1 - θ) • Δ with hS
  have hS1 : S 1 = S0 := by simp [hS]
  have hSb : (S 1).PosSemidef := by rw [hS1]; exact hS0
  have hpde := HRS.MC.Sec7.S7PIH.s7_PIH_heat_pde_proof (0 : ℝ) 1 zero_le_one (fun _ => Δ) S
    (fun i j => continuousOn_const) (fun _ _ => hΔ) hSb (fun u hu i j => by
      rw [hS1]
      simp only [hS, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, setIntegral_const, Real.volume_real_Ioc,
        Measure.real]
      have : max (1 - u) 0 = 1 - u := max_eq_left (by linarith [hu.2])
      simp [Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 hu.2)]) G hG c
  have hbd := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (f := fun s => gaussHeat S G s c)
    (f' := fun r => -(1 / 2) * ∑ i, ∑ j, Δ i j * ∫ x, iteratedFDeriv ℝ 2 G (c + x)
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] ∂(multivariateGaussian 0 (S r)))
    (s := Icc (0 : ℝ) 1) (C := K / 2) (fun r hr => hpde r hr)
    (fun r hr => by
      rw [Real.norm_eq_abs, abs_mul]
      have := hK r hr
      have h12 : |(-(1 / 2) : ℝ)| = 1 / 2 := by norm_num
      rw [h12]
      linarith)
    (convex_Icc 0 1) (x := 1) (y := 0) (by simp) (by simp)
  have e0 : gaussHeat S G 0 c = gaussHeat (fun _ => S0 + Δ) G 0 c := by
    unfold gaussHeat
    simp [hS]
  have e1 : gaussHeat S G 1 c = gaussHeat (fun _ => S0) G 0 c := by
    unfold gaussHeat
    simp [hS1]
  rw [e0, e1] at hbd
  simpa [Real.norm_eq_abs] using hbd

end HRS.MS.R2Interp

end
