import HRS.MC.S7PIB4
import HRS.MC.S7PIS3Cov2
import HRS.Sections.Q17Aux5

/-!
# Packet piB, part 5: `s7_PIB_rate_bound`

`∑_{ij} A_{ij}(u) N(Λe_i, Λe_j) = 2β⁻¹ ∫ ρ_u ∑_a N(Λ v_a(x), Λ v_a(x)) dx` with `v_a(x)_i = ∂_a ψ_i(x)`, and
`Λ v_a(x) = P_L w` for the path `w` of part 4 (`b = b_{x,a}`), so `‖Λ v_a(x)‖ ≤ A C_b`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIB

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.PIE HRS.MC.Sec7.S7PIDV
  HRS.MC.Sec7.S7PIS1

variable {d : ℕ}

theorem S7PIB_eval_zero {m : ℝ} (ψ : Torus d → ℝ) : NegSobolev.eval (0 : NegSobolev d m) ψ = 0 := by
  have h0 : ∀ k, NegSobolev.fourierCoeff (0 : NegSobolev d m) k = 0 := by
    intro k
    unfold NegSobolev.fourierCoeff NegSobolev.coord
    have : ((show lp (fun _ : NonzeroLattice d => ℝ) 2 from (0 : NegSobolev d m)) k) = 0 := rfl
    rw [this, mul_zero]
  unfold NegSobolev.eval
  simp [h0]

/-- bilinear expansion of a continuous bilinear form given as a 2-linear map -/
theorem S7PIB_bil_sum {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (N : X [×2]→L[ℝ] ℝ)
    {ι κ : Type*} [Fintype ι] [Fintype κ] (α : ι → ℝ) (β : κ → ℝ) (x : ι → X) (y : κ → X) :
    N ![∑ i, α i • x i, ∑ j, β j • y j] = ∑ i, ∑ j, α i * β j * N ![x i, y j] := by
  classical
  have hL : ∀ (y' x' : X), N ![x', y'] = (N.toMultilinearMap.toLinearMap ![0, y'] 0) x' := by
    intro y' x'
    have hup : Function.update (![0, y'] : Fin 2 → X) 0 x' = ![x', y'] := by
      ext k; fin_cases k <;> simp
    rw [MultilinearMap.toLinearMap_apply, hup]; rfl
  have hR : ∀ (x' y' : X), N ![x', y'] = (N.toMultilinearMap.toLinearMap ![x', 0] 1) y' := by
    intro x' y'
    have hup : Function.update (![x', 0] : Fin 2 → X) 1 y' = ![x', y'] := by
      ext k; fin_cases k <;> simp
    rw [MultilinearMap.toLinearMap_apply, hup]; rfl
  rw [hL, map_sum]
  simp_rw [map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hL, hR, map_sum]
  simp_rw [map_smul, smul_eq_mul, ← hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- the key pointwise bound of `Λ v_a(x)` -/
theorem S7PIB_vec_bound (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (L q : ℕ) (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
      (Λ : EuclideanSpace ℝ (Fin q) →L[ℝ] PathSpace d m T), IsGridData m T hT.le L q t φ Λ →
      ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ (a : Fin d) (x : Torus d),
        ‖Λ (WithLp.toLp 2 fun i => Torus.grad (obsTest R.D R.ρ t φ i u) x a)‖ ≤ C0 := by
  obtain ⟨A, hA0, hA⟩ := S7PIB_path_exists R m hm T hT
  obtain ⟨Cb, hCb0, hCb⟩ := S7PIB_norm_bvec_le (d := d) m (by linarith [R.hd])
  refine ⟨A * Cb, mul_nonneg hA0 hCb0, fun L q t φ Λ hgrid u hu a x => ?_⟩
  have hφ : ∀ i, Torus.IsSmooth (φ i) := fun i => by
    obtain ⟨k, hk⟩ := hgrid.2.1 i
    rw [hk]; exact HRS.FieldSingAux.isSmooth_realMode k
  obtain ⟨w, hwn, hwp⟩ := hA (S7PIB_bvec m a x) u hu t
  obtain ⟨J, k, hk1, hkJ, hm0, hm1, H⟩ := S7PIS1_data R m hm T hT
  have hv : (WithLp.toLp 2 fun i => Torus.grad (obsTest R.D R.ρ t φ i u) x a : EuclideanSpace ℝ (Fin q)) =
      obsVec m T t φ w := by
    ext i
    show Torus.grad (obsTest R.D R.ρ t φ i u) x a = NegSobolev.eval (pathAt w (t i)) (φ i)
    rw [hwp i (hgrid.1 i)]
    unfold obsTest
    by_cases h : u ≤ t i
    · rw [if_pos h, if_pos h, HRS.PDE.MFAux.grad_apply]
      rw [HRS.MC.Sec7.S7PIS1.s7_PIS_V_eval_proof R m hm T hT u (t i) hu.1 h (hgrid.1 i).2 _ (φ i) (hφ i),
        S7PIB_eval_bvec m (by linarith [R.hd]) a x]
      refine (S7PIB_partial_series H (k + 1) (by omega) (by omega) ?_ hu.1 h (hgrid.1 i).2 (hφ i) a x).trans ?_
      · have : (3 * (d : ℝ) + 6 < k) := by linarith
        push_cast
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        linarith
      · rfl
    · rw [if_neg h, if_neg h, S7PIB_eval_zero, HRS.MC.Sec7.S7PIS3.S7PIS3_grad_zero]
      simp
  rw [hv, ← hgrid.2.2 w]
  refine (q17_projPoly_norm_le hT L w).trans (hwn.trans ?_)
  exact mul_le_mul_of_nonneg_left (hCb a x) hA0

theorem s7_PIB_rate_bound_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, ∀ (L q : ℕ) (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
      (Λ : EuclideanSpace ℝ (Fin q) →L[ℝ] PathSpace d m T), IsGridData m T hT.le L q t φ Λ →
      ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ N : PathSpace d m T [×2]→L[ℝ] ℝ,
        |∑ i, ∑ j, obsRate R.D R.ρ t φ u i j *
            N ![Λ (EuclideanSpace.single i 1), Λ (EuclideanSpace.single j 1)]| ≤ C * ‖N‖ := by
  obtain ⟨C0, hC00, hvec⟩ := S7PIB_vec_bound R m hm T hT
  have hβ := HRS.MC.Sec7.S7PIS3.S7PIS3_invβ_pos R
  refine ⟨2 * R.D.invβ * (d * C0 ^ 2), fun L q t φ Λ hgrid u hu N => ?_⟩
  have hρnn := HRS.MC.Sec7.S7PIS3.S7PIS3_rho_nonneg R hu.1
  have hρc := HRS.MC.Sec7.S7FCF5A.S7FCF5A_rho_cont_x R hu.1
  have hρint : ∫ x, R.ρ u x = 1 := ((HRS.MC.L2C0.l2c0_rho_prob_cont R).1 u hu.1).integral_one
  set G : Fin q → Torus d → Euc d := fun i => Torus.grad (obsTest R.D R.ρ t φ i u) with hG
  have hGc : ∀ i, Continuous (G i) := fun i =>
    HRS.MC.Sec7.S7PIS3.S7PIS3_obsTest_grad_cont' R t φ i hu.1
  set Nij : Fin q → Fin q → ℝ := fun i j => N ![Λ (EuclideanSpace.single i 1), Λ (EuclideanSpace.single j 1)]
    with hNij
  set g : Fin q → Fin q → Torus d → ℝ := fun i j x => inner ℝ (G i x) (G j x) * R.ρ u x with hg
  have hint : ∀ i j, Integrable (g i j) := fun i j =>
    HRS.MC.Sec7.S7PIS3.S7PIS3_integrable_of_cont (((hGc i).inner (hGc j)).mul hρc)
  have e1 : ∑ i, ∑ j, obsRate R.D R.ρ t φ u i j * Nij i j =
      2 * R.D.invβ * ∫ x, ∑ i, ∑ j, g i j x * Nij i j := by
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => (hint i j).mul_const _)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ (fun j _ => (hint i j).mul_const _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const]
    simp only [obsRate, Matrix.of_apply, hg, hG]
    ring
  -- pointwise bound
  have hpt : ∀ x, |∑ i, ∑ j, g i j x * Nij i j| ≤ R.ρ u x * (d * (‖N‖ * C0 ^ 2)) := by
    intro x
    set vec : Fin d → EuclideanSpace ℝ (Fin q) := fun a => WithLp.toLp 2 fun i => G i x a with hvecdef
    have hexp : ∀ a, Λ (vec a) = ∑ i, G i x a • Λ (EuclideanSpace.single i 1) := by
      intro a
      have : vec a = ∑ i, G i x a • (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin q)) := by
        ext k
        simp [hvecdef, Pi.single_apply]
      rw [this, map_sum]
      simp_rw [map_smul]
    have hS : ∑ i, ∑ j, g i j x * Nij i j = R.ρ u x * ∑ a, N ![Λ (vec a), Λ (vec a)] := by
      have h1 : ∀ a, N ![Λ (vec a), Λ (vec a)] = ∑ i, ∑ j, G i x a * G j x a * Nij i j := by
        intro a
        rw [hexp a, S7PIB_bil_sum N (fun i => G i x a) (fun j => G j x a)]
      have h2 : ∀ i j, g i j x * Nij i j =
          R.ρ u x * ∑ a, G i x a * G j x a * Nij i j := by
        intro i j
        simp only [hg]
        rw [PiLp.inner_apply, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [RCLike.inner_apply, conj_trivial]
        ring
      have hc : ∀ F : Fin q → Fin q → Fin d → ℝ,
          ∑ i, ∑ j, ∑ a, F i j a = ∑ a, ∑ i, ∑ j, F i j a := by
        intro F
        calc ∑ i, ∑ j, ∑ a, F i j a = ∑ i, ∑ a, ∑ j, F i j a :=
              Finset.sum_congr rfl fun i _ => Finset.sum_comm
          _ = ∑ a, ∑ i, ∑ j, F i j a := Finset.sum_comm
      simp_rw [h1, h2, ← Finset.mul_sum]
      congr 1
      exact hc (fun i j a => G i x a * G j x a * Nij i j)
    rw [hS, abs_mul, abs_of_nonneg (hρnn x)]
    refine mul_le_mul_of_nonneg_left ?_ (hρnn x)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ a ∈ Finset.univ, |N ![Λ (vec a), Λ (vec a)]| ≤ ‖N‖ * C0 ^ 2 := by
      intro a _
      have hb := hvec L q t φ Λ hgrid u hu a x
      have hn := N.le_opNorm ![Λ (vec a), Λ (vec a)]
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs] at hn
      refine hn.trans ?_
      have h0 := norm_nonneg (Λ (vec a))
      calc ‖N‖ * (‖Λ (vec a)‖ * ‖Λ (vec a)‖) ≤ ‖N‖ * (C0 * C0) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hb hb h0 hC00) (norm_nonneg _)
        _ = _ := by ring
    refine (Finset.sum_le_sum this).trans ?_
    simp
  have hbound : |∫ x, ∑ i, ∑ j, g i j x * Nij i j| ≤ d * (‖N‖ * C0 ^ 2) := by
    have hρi : Integrable (R.ρ u) := HRS.MC.Sec7.S7PIS3.S7PIS3_integrable_of_cont hρc
    have := norm_integral_le_of_norm_le (f := fun x => ∑ i, ∑ j, g i j x * Nij i j)
      (hρi.mul_const ((d : ℝ) * (‖N‖ * C0 ^ 2)))
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hpt x)
    rw [integral_mul_const, hρint, one_mul] at this
    simpa [Real.norm_eq_abs] using this
  rw [e1, abs_mul, abs_of_pos (by positivity : 0 < 2 * R.D.invβ)]
  calc 2 * R.D.invβ * |∫ x, ∑ i, ∑ j, g i j x * Nij i j|
      ≤ 2 * R.D.invβ * (d * (‖N‖ * C0 ^ 2)) := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

end HRS.MC.Sec7.S7PIB

end
