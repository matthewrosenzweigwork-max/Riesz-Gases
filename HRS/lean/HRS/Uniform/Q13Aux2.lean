import HRS.Uniform.Q13Aux1

/-!
# Q13: from the `H^γ` form estimate to the `H^{-γ}` form estimate of the forward linearisation
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q13

open HRS HRS.PDE

variable {d : ℕ}

theorem q13_sobWeight_neg_mul (γ : ℝ) (k : Lattice d) :
    sobWeight γ k * sobWeight (-γ) k = 1 := by
  unfold sobWeight
  rw [← Real.rpow_add (by positivity)]
  simp

theorem q13_sobWeight_lattice_neg (m : ℝ) (k : Lattice d) : sobWeight m (-k) = sobWeight m k := by
  unfold sobWeight
  rw [HRS.enorm_neg]

theorem q13_hsInner_box_left {n : ℕ} (r : ℝ) (c c' : Coeff d) (hc : IsTrigPoly n c) :
    hsInner r c c' = ∑ k ∈ boxFin d n, ((sobWeight r k : ℝ) : ℂ) * (c k * conj (c' k)) := by
  unfold hsInner
  refine tsum_eq_sum fun k hk => ?_
  rw [eq_zero_of_isTrigPoly hc hk]; simp

theorem q13_hsNormSq_box {n : ℕ} (r : ℝ) (c : Coeff d) (hc : IsTrigPoly n c) :
    hsNormSq r c = ∑ k ∈ boxFin d n, sobWeight r k * ‖c k‖ ^ 2 := by
  unfold hsNormSq
  refine tsum_eq_sum fun k hk => ?_
  rw [eq_zero_of_isTrigPoly hc hk]; simp

/-- The `H^{-γ}` form of the forward linearisation equals the `H^γ` form of the forward generator
at `u = Λ^{-2γ} c`. -/
theorem q13_form {n : ℕ} (γ : ℕ) (D : DynData d) {μ : Torus d → ℝ}
    (hμ : IsRealCoeff (coeffOf μ)) (hV : IsRealCoeff (coeffOf D.V)) {c : Coeff d}
    (hc : IsTrigPoly n c) (hcr : IsRealCoeff c) (C₀ : ℝ)
    (hE : ∀ F : Coeff d, IsRealCoeff F → IsTrigPoly n F →
      (hsInner (γ : ℝ) (forwardGen D μ F) F).re ≤ C₀ * hsNormSq (γ : ℝ) F) :
    (hsInner (-(γ : ℝ)) c (fun k => ((D.invβ : ℝ) : ℂ) * laplaceCoeff c k
        - ∑ j : Fin d, derivCoeff j (mulCoeff (driftCoeff D μ j) c) k
        + forwardNonlocalCoeff D μ c k)).re ≤ C₀ * hsNormSq (-(γ : ℝ)) c := by
  set u : Coeff d := fun k => ((sobWeight (-(γ : ℝ)) k : ℝ) : ℂ) * c k with hu
  have hut : IsTrigPoly n u := fun k hk => hc k (fun h => hk (by simp [hu, h]))
  have hur : IsRealCoeff u := by
    intro k
    simp only [hu, q13_sobWeight_lattice_neg, hcr k, map_mul, Complex.conj_ofReal]
  set A : Coeff d := fun k => ((D.invβ : ℝ) : ℂ) * laplaceCoeff c k
        - ∑ j : Fin d, derivCoeff j (mulCoeff (driftCoeff D μ j) c) k
        + forwardNonlocalCoeff D μ c k with hA
  have h1 : hsInner (-(γ : ℝ)) c A = conj (pr n A u) := by
    rw [q13_hsInner_box_left _ _ _ hc]
    unfold pr
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hu, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    ring
  have h2 : pr n A u = pr n c (forwardGen D μ u) := q13_adjoint D hμ hV hc hut
  have h3 : hsInner (γ : ℝ) (forwardGen D μ u) u = conj (pr n c (forwardGen D μ u)) := by
    rw [hsInner_box _ _ _ hut]
    unfold pr
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hw : ((sobWeight (γ : ℝ) k : ℝ) : ℂ) * ((sobWeight (-(γ : ℝ)) k : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, q13_sobWeight_neg_mul]; simp
    simp only [hu, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    linear_combination (forwardGen D μ u k * conj (c k)) * hw
  have h4 : hsNormSq (γ : ℝ) u = hsNormSq (-(γ : ℝ)) c := by
    rw [q13_hsNormSq_box _ _ hut, q13_hsNormSq_box _ _ hc]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hw := q13_sobWeight_neg_mul (d := d) (γ : ℝ) k
    simp only [hu, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hp : 0 ≤ sobWeight (-(γ : ℝ)) k := by unfold sobWeight; positivity
    rw [abs_of_nonneg hp]
    calc sobWeight (γ : ℝ) k * (sobWeight (-(γ : ℝ)) k * ‖c k‖) ^ 2
        = (sobWeight (γ : ℝ) k * sobWeight (-(γ : ℝ)) k) * sobWeight (-(γ : ℝ)) k * ‖c k‖ ^ 2 := by ring
      _ = _ := by rw [hw]; ring
  have := hE u hur hut
  rw [h3, ← h2, ← h1, h4] at this
  exact this

theorem q13_real_of_isCk {m : ℕ} {f : Torus d → ℝ} (h : Torus.IsCk m f) :
    IsRealCoeff (coeffOf f) :=
  isRealCoeff_coeffOf f (integrable_of_continuous'
    (Torus.continuous_of_continuous_lift (by simpa [Torus.IsCk] using h.continuous)))

/-! ### The `H^γ` form estimate for `M = -I` in the three regimes -/

theorem q13_symNonpos_negOne : Torus.SymNonpos (-1 : Matrix (Fin d) (Fin d) ℝ) := by
  unfold Torus.SymNonpos Torus.symPart
  have : -((1 / 2 : ℝ) • ((-1 : Matrix (Fin d) (Fin d) ℝ) + (-1 : Matrix (Fin d) (Fin d) ℝ).transpose))
      = 1 := by
    rw [Matrix.transpose_neg, Matrix.transpose_one]
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> norm_num
  rw [this]
  exact Matrix.PosSemidef.one

theorem q13_matBound_negOne : MatBound 1 (-1 : Matrix (Fin d) (Fin d) ℝ) := by
  intro i j
  simp [Matrix.one_apply]
  split_ifs <;> norm_num

theorem q13_energy_const (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (γ : ℕ) (Λ m₀ : ℝ)
    (hm₀ : 0 < m₀) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ D : DynData d, D.M = -1 → D.s = s → Torus.IsCk ((γ + 3 : ℕ)) D.V →
      Torus.cbNorm (γ + 3) D.V ≤ Λ → ∀ μ : Torus d → ℝ, IsProbDensity μ →
      Torus.IsCk ((γ + 3 : ℕ)) μ → Torus.cbNorm (γ + 3) μ ≤ Λ →
      (thetaOrder d s ≤ 1 ∨ ∀ x, m₀ ≤ μ x) →
      ∀ (n : ℕ) (F : Coeff d), IsRealCoeff F → IsTrigPoly n F →
        (hsInner (γ : ℝ) (forwardGen D μ F) F).re ≤ C₀ * hsNormSq (γ : ℝ) F := by
  -- common construction of the data for the constant path
  have mkData : ∀ (R : Regime) (D : DynData d), D.M = -1 → D.s = s → Torus.IsCk ((γ + 3 : ℕ)) D.V →
      Torus.cbNorm (γ + 3) D.V ≤ Λ → ∀ μ : Torus d → ℝ, IsProbDensity μ →
      Torus.IsCk ((γ + 3 : ℕ)) μ → Torus.cbNorm (γ + 3) μ ≤ Λ →
      R.Holds d s D.M D.invβ 1 1 (fun _ => μ) →
      AdjointData s γ R 1 Λ Λ D 1 1 (fun _ => μ) := by
    intro R D hM hs hV hVb μ hp hk hb hR
    refine ⟨hs, ?_, ⟨hV, hVb⟩, ⟨fun _ _ => hp, fun _ _ => hk, fun _ _ => hb,
      fun ψ _ => continuousOn_const⟩, one_pos, hR⟩
    rw [hM]; exact q13_matBound_negOne
  by_cases h1 : s ≤ (d : ℝ) - 2
  · obtain ⟨C, hC, h⟩ := energy_form_estimate hd s hs0 hsd γ .R1 1 Λ Λ
    refine ⟨C, hC.le, ?_⟩
    intro D hM hs hV hVb μ hp hk hb _ n F hFr hFt
    have A := mkData .R1 D hM hs hV hVb μ hp hk hb (show s ≤ (d : ℝ) - 2 from h1)
    have hn : ¬ Regime.R1.IsR2 := by simp [Regime.IsR2]
    have := (h D 1 1 (fun _ => μ) A (fun _ => 0) (fun _ => 0) (fun h => absurd h hn) 0
      (by simp) n F hFr hFt).2
    refine this.trans ?_
    have := energyRHS_le hd .R1 (Regime.lambdaM .R1 C 1 (thetaOrder d s)) D γ (fun _ => 0)
      (fun _ => 0) (fun h => absurd h hn) μ F
    simpa [Regime.lambdaM] using this
  · have h1' : (d : ℝ) - 2 < s := not_le.mp h1
    by_cases h2 : thetaOrder d s ≤ 1
    · obtain ⟨C, hC, h⟩ := energy_form_estimate_R2c hd s h1' (by unfold thetaOrder at h2; linarith) γ 1 Λ Λ
      refine ⟨C, hC.le, ?_⟩
      intro D hM hs hV hVb μ hp hk hb _ n F hFr hFt
      have A := mkData .R2c D hM hs hV hVb μ hp hk hb
        ⟨h1', by unfold thetaOrder at h2; linarith, hM ▸ q13_symNonpos_negOne⟩
      exact h D 1 1 (fun _ => μ) A 0 (by simp) n F hFr hFt
    · obtain ⟨C, hC, h⟩ := energy_form_estimate hd s hs0 hsd γ (.R2b m₀) 1 Λ Λ
      refine ⟨C, hC.le, ?_⟩
      intro D hM hs hV hVb μ hp hk hb hcase n F hFr hFt
      have hlow : ∀ x, m₀ ≤ μ x := hcase.resolve_left h2
      have hreg : (Regime.R2b m₀).Holds d s D.M D.invβ 1 1 (fun _ => μ) :=
        ⟨h1', hM ▸ q13_symNonpos_negOne, hm₀, fun _ _ x => hlow x⟩
      have A := mkData (.R2b m₀) D hM hs hV hVb μ hp hk hb hreg
      obtain ⟨lam, q, hdiag⟩ := exists_symDiag (hM ▸ q13_symNonpos_negOne : Torus.SymNonpos D.M)
      have := (h D 1 1 (fun _ => μ) A lam q (fun _ => hdiag) 0 (by simp) n F hFr hFt).2
      refine this.trans ?_
      have := energyRHS_le hd (.R2b m₀) (Regime.lambdaM (.R2b m₀) C 1 (thetaOrder d s)) D γ lam q
        (fun _ l => hdiag.nonneg l) μ F
      simpa [Regime.lambdaM] using this

end HRS.Uniform.Q13
