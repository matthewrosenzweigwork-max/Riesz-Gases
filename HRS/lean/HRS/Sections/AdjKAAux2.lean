import HRS.Sections.AdjKAAux1

/-!
# ADJKA part 2: Lipschitz increment of the adjoint propagator along a smooth positive trajectory
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.AdjK

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

/-- For `t - u ≤ 1` and smooth `φ`: `‖U^{u,t}φ - φ‖_{H^j} ≤ M (t-u) ‖φ‖_{H^{j+2}}` (the diagonal included). -/
theorem adjka_traj_lip (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (j : ℕ)
    (hj : (d : ℝ) + 2 ≤ j) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (φ : Torus d → ℝ), Torus.IsSmooth φ → ∀ u t : ℝ, 0 ≤ u → u ≤ t → t - u ≤ 1 →
      MemSobolev (j : ℝ) (propagator htr.dyn ρ u t φ) ∧
      MemSobolev (j : ℝ) (fun x => propagator htr.dyn ρ u t φ x - φ x) ∧
        sobolevNorm (j : ℝ) (fun x => propagator htr.dyn ρ u t φ x - φ x) ≤
          M * (t - u) * sobolevNorm ((j : ℝ) + 2) φ := by
  have hd1 : 1 ≤ d := by omega
  set J : ℕ := j + 5 with hJ
  have hJr : (J : ℝ) = j + 5 := by rw [hJ]; push_cast; ring
  have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  set K : ℕ := 2 * J + 4 * d + 20 with hKdef
  have hKr : (K : ℝ) = 2 * J + 4 * d + 20 := by rw [hKdef]; push_cast; ring
  have hKgt : (d : ℝ) / 2 + 6 < K := by rw [hKr, hJr]; linarith
  have hKJ : 2 * J + 4 * d + 20 ≤ K := le_rfl
  have hJd : (d : ℝ) / 2 + 4 < J := by rw [hJr]; linarith
  have hJ3 : (3 : ℝ) < J := by rw [hJr]; linarith
  have hJm : mStar d ≤ J := by
    have h1 := Q54.mStar_le_aux d
    have : (mStar d : ℝ) ≤ J := by rw [hJr]; linarith
    exact_mod_cast this
  have hβI : β ∈ Set.Icc β β := ⟨le_rfl, le_rfl⟩
  have H := Q40b.q40b_finiteRegHyp htr hKgt
  obtain ⟨ρc, hρc, hρ⟩ := htr.global K hKgt
  obtain ⟨ρβ, hρβ, hρC, hpos, -⟩ := finite_reg_thermal hd1 s β β K V ρ₀ H β hβI
  obtain ⟨R, Λ, Λ₀, c₀, Cd, κ, hc₀, hκ, hall⟩ :=
    MFAdjoint.finiteReg_hypotheses hd1 s β β K V ρ₀ H J hJd hKJ
  obtain ⟨-, hAD, -⟩ := hall β hβI ρc hρc ρβ hρβ hρC hpos
  obtain ⟨Bμ, BV, hBμ, hBV, hGH⟩ := genHyp_of_mf hd1 s β β K V ρ₀ H
  have hβ' : 0 < β⁻¹ := inv_pos.2 htr.hβ
  have hK1 : (d : ℝ) + |(j : ℝ)| + 4 ≤ K := by
    rw [abs_of_nonneg hj0, hKr, hJr]; linarith
  have hK2 : (d : ℝ) + |(j : ℝ) + 2| + 4 ≤ K := by
    rw [abs_of_nonneg (by linarith), hKr, hJr]; linarith
  have hJa : (j : ℝ) + 2 + 2 < J := by rw [hJr]; linarith
  obtain ⟨A, B, hA0, hB0, hprop⟩ := adjka_prop_lip hd1 s htr.hs0 htr.hsd K 1 Bμ BV zero_le_one hBμ
    hBV (j : ℝ) hK1 hK2 β⁻¹ β⁻¹ hβ' J hJa hJ3 hJm
  refine ⟨Real.sqrt (B * Real.exp A), Real.sqrt_nonneg _, fun φ hφ u t hu hut htu => ?_⟩
  have hD : Dom J φ := dom_smooth hφ
  have hcongr : ∀ r ∈ Set.Icc (0 : ℝ) t, PDE.mfPath ρc r = ρ r := fun r hr => hρ r hr.1
  have hprop_eq : propagator htr.dyn ρ u t φ = propagator htr.dyn (PDE.mfPath ρc) u t φ :=
    (Q40b.q40b_propagator_congr (D := htr.dyn) (ρ := PDE.mfPath ρc) (ρ' := ρ) (t := t) hcongr u φ).symm
  rw [hprop_eq]
  have hAD' : ∀ T : ℝ, 0 < T → AdjointData s J R 1 Λ (Torus.cbNorm (J + 3) V) htr.dyn β⁻¹ T
      (PDE.mfPath ρc) := hAD
  have hG : ∀ T : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) T, GenHyp d s (K : ℝ) 1 Bμ BV htr.dyn (PDE.mfPath ρc r) :=
    fun T r hr => hGH β hβI ρc hρc r hr.1
  rcases hut.eq_or_lt with h0 | hlt
  · -- diagonal
    subst h0
    have hself : propagator htr.dyn (PDE.mfPath ρc) u u φ = φ := by
      rcases hu.eq_or_lt with h00 | hpos
      · rw [← h00]
        exact prop_self_zero hd1 s htr.hs0 htr.hsd J R 1 Λ _ htr.dyn β⁻¹ 1 _ (hAD' 1 one_pos) hφ
      · exact prop_self_pos hd1 s htr.hs0 htr.hsd J hJm R 1 Λ _ htr.dyn β⁻¹ u _ (hAD' u hpos)
          ⟨hpos, le_rfl⟩ hD
    rw [hself]
    refine ⟨MFSemigroup.memSobolev_of_isSmooth hφ _, ?_⟩
    have e : (fun x => φ x - φ x) = fun _ : Torus d => (0 : ℝ) := by funext x; ring
    rw [e]
    refine ⟨MFSemigroup.memSobolev_of_isSmooth (isSmooth_const' 0) _, ?_⟩
    have hz : sobolevNorm (j : ℝ) (fun _ : Torus d => (0 : ℝ)) = 0 := by
      unfold sobolevNorm
      rw [mean_const']
      have : ∀ k : NonzeroLattice d, Torus.funRealCoeff (fun _ : Torus d => (0 : ℝ)) k = 0 := by
        intro k
        unfold Torus.funRealCoeff
        simp
      simp [this]
    rw [hz]
    simp
  · have ht0 : 0 < t := lt_of_le_of_lt hu hlt
    obtain ⟨hm, hn⟩ := hprop R 1 Λ _ β⁻¹ htr.dyn t (PDE.mfPath ρc) (hAD' t ht0) (hG t) le_rfl le_rfl
      hD hu hut ht0 le_rfl
    have hdom := prop_dom hd1 s htr.hs0 htr.hsd J hJm R 1 Λ _ htr.dyn β⁻¹ t (PDE.mfPath ρc)
      (hAD' t ht0) ⟨ht0, le_rfl⟩ hD ⟨hu, hut⟩
    refine ⟨MFAdjoint.memSobolev_mono_idx (m := J) hdom.2 (by rw [hJr]; linarith), hm, ?_⟩
    have hτ0 : 0 ≤ t - u := by linarith
    have hE : Real.exp (A * (t - u)) ≤ Real.exp A := Real.exp_le_exp.2 (by nlinarith)
    have hN0 : 0 ≤ sobolevNorm ((j : ℝ) + 2) φ := Real.sqrt_nonneg _
    refine le_of_sq_le_sq ?_ (by positivity)
    calc sobolevNorm (j : ℝ) (fun x => propagator htr.dyn (PDE.mfPath ρc) u t φ x - φ x) ^ 2
        ≤ B * sobolevNorm ((j : ℝ) + 2) φ ^ 2 * (t - u) ^ 2 * Real.exp (A * (t - u)) := hn
      _ ≤ B * sobolevNorm ((j : ℝ) + 2) φ ^ 2 * (t - u) ^ 2 * Real.exp A :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ = (Real.sqrt (B * Real.exp A) * (t - u) * sobolevNorm ((j : ℝ) + 2) φ) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring

end HRS.AdjK
