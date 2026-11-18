import HRS.MS.FixEqP3Aux25

/-!
# S5.7 `fixed_equation` (worker S57P), part 38: Hilbert-Schmidt Hölder bound of `κ^N - κ`
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

/-- the data of a pair of families: orbit bounds and the bounds of `U - U_N` (conclusions of `s57p_pair_b`, `s57p_pair_d`) -/
structure S57pPairBd (θ : Euc d → ℝ) (T : ℝ) (n : ℕ) (K KN : ℝ) (s : ℝ) (M Q : Matrix (Fin d) (Fin d) ℝ) (ν νN : ℝ)
    (c cN : ℝ → Euc d → Euc d) (ρ ρN : ℝ → Euc d → ℝ) (A Λc νbar : ℝ) (m : ℝ) (J : ℕ)
    (Ca CaN Cd CdN Cp1 Cp2 Dt : ℝ) : Prop where
  Fx : S57pFx θ T n K s M Q ν c ρ A Λc νbar
  FxN : S57pFx θ T n KN s M Q νN cN ρN A Λc νbar
  hbd : S57pOrbBd (fixedEqCoeff s M Q ν c ρ) T n m J Ca Cd
  hbdN : S57pOrbBd (fixedEqCoeff s M Q νN cN ρN) T n m J CaN CdN
  hCa : 0 ≤ Ca
  hCaN : 0 ≤ CaN
  hCd : 0 ≤ Cd
  hCdN : 0 ≤ CdN
  hCp1 : 0 ≤ Cp1
  hCp2 : 0 ≤ Cp2
  hDt : 0 ≤ Dt
  hb : ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ i ≤ n, ∀ x,
    ‖iteratedFDeriv ℝ i (fun y => propagatorW (fixedEqCoeff s M Q ν c ρ) r t (oscTestFun m α) y -
      propagatorW (fixedEqCoeff s M Q νN cN ρN) r t (oscTestFun m α) y) x‖ ≤
      Cp1 * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) * Dt
  hd : ∀ α : MultiIndex d, ∀ s₀ t₀ : ℝ, 0 ≤ s₀ → s₀ ≤ t₀ → t₀ ≤ T → ∀ r ∈ Set.Icc (0 : ℝ) s₀, ∀ x,
    ‖iteratedFDeriv ℝ 1 (fun y => (propagatorW (fixedEqCoeff s M Q ν c ρ) r t₀ (oscTestFun m α) y -
        propagatorW (fixedEqCoeff s M Q νN cN ρN) r t₀ (oscTestFun m α) y) -
      (propagatorW (fixedEqCoeff s M Q ν c ρ) r s₀ (oscTestFun m α) y -
        propagatorW (fixedEqCoeff s M Q νN cN ρN) r s₀ (oscTestFun m α) y)) x‖ ≤
      Cp2 * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) * Dt * (t₀ - s₀)

theorem s57p_grad4 {f1 f2 f3 f4 : Euc d → ℝ} (h1 : ContDiff ℝ 1 f1) (h2 : ContDiff ℝ 1 f2) (h3 : ContDiff ℝ 1 f3)
    (h4 : ContDiff ℝ 1 f4) (x : Euc d) :
    gradient (fun y => (f1 y - f2 y) - (f3 y - f4 y)) x = (gradient f1 x - gradient f2 x) - (gradient f3 x - gradient f4 x) := by
  rw [HRS.MS.Fcau.fcau_gradient_sub (h1.sub h2) (h3.sub h4), HRS.MS.Fcau.fcau_gradient_sub h1 h2,
    HRS.MS.Fcau.fcau_gradient_sub h3 h4]

variable {θ : Euc d → ℝ} {T : ℝ} {n : ℕ} {K KN : ℝ} {s : ℝ} {M Q : Matrix (Fin d) (Fin d) ℝ} {ν νN : ℝ}
  {c cN : ℝ → Euc d → Euc d} {ρ ρN : ℝ → Euc d → ℝ} {A Λc νbar : ℝ} {m : ℝ} {J : ℕ}
  {Ca CaN Cd CdN Cp1 Cp2 Dt : ℝ}

theorem S57pPairBd.cont1 (P : S57pPairBd θ T n K KN s M Q ν νN c cN ρ ρN A Λc νbar m J Ca CaN Cd CdN Cp1 Cp2 Dt)
    (α : MultiIndex d) {t r : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (hr : r ∈ Set.Icc (0 : ℝ) t) :
    ContDiff ℝ 1 (propagatorW (fixedEqCoeff s M Q ν c ρ) r t (oscTestFun m α)) ∧
      ContDiff ℝ 1 (propagatorW (fixedEqCoeff s M Q νN cN ρN) r t (oscTestFun m α)) := by
  have hn := P.Fx.hn4
  exact ⟨(((P.hbd α).1 t ht).2 r hr).1.of_le (by exact_mod_cast (by omega : 1 ≤ n + 1)),
    (((P.hbdN α).1 t ht).2 r hr).1.of_le (by exact_mod_cast (by omega : 1 ≤ n + 1))⟩

theorem s57p_iter_neg {F G : Euc d → ℝ} {i : ℕ} (hF : ContDiff ℝ i F) (hG : (fun y => G y) = fun y => (-1 : ℝ) * F y)
    {B : ℝ} {x : Euc d} (h : ‖iteratedFDeriv ℝ i F x‖ ≤ B) : ‖iteratedFDeriv ℝ i G x‖ ≤ B := by
  have e : G = fun y => (-1 : ℝ) * F y := hG
  rw [e]
  refine (s57p_norm_const_mul hF (-1) x).trans ?_
  simpa using h

/-- the gradient fields of the two families, their difference and its Hölder increment -/
theorem S57pPairBd.Adiff (P : S57pPairBd θ T n K KN s M Q ν νN c cN ρ ρN A Λc νbar m J Ca CaN Cd CdN Cp1 Cp2 Dt)
    (α : MultiIndex d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Continuous (fun p => s57pA (fixedEqCoeff s M Q νN cN ρN) t (oscTestFun m α) p -
      s57pA (fixedEqCoeff s M Q ν c ρ) t (oscTestFun m α) p) ∧
    ∀ p, ‖s57pA (fixedEqCoeff s M Q νN cN ρN) t (oscTestFun m α) p -
      s57pA (fixedEqCoeff s M Q ν c ρ) t (oscTestFun m α) p‖ ≤ Cp1 * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) * Dt := by
  refine ⟨(s57p_A_cont ht.1 ((P.hbdN α).1 t ht).1).sub (s57p_A_cont ht.1 ((P.hbd α).1 t ht).1), fun p => ?_⟩
  have hcl : max 0 (min p.1 t) ∈ Set.Icc (0 : ℝ) t := ⟨le_max_left _ _, max_le ht.1 (min_le_right _ _)⟩
  obtain ⟨hc1, hc2⟩ := P.cont1 α ht hcl
  have e : s57pA (fixedEqCoeff s M Q νN cN ρN) t (oscTestFun m α) p - s57pA (fixedEqCoeff s M Q ν c ρ) t (oscTestFun m α) p =
      gradient (fun y => propagatorW (fixedEqCoeff s M Q νN cN ρN) (max 0 (min p.1 t)) t (oscTestFun m α) y -
        propagatorW (fixedEqCoeff s M Q ν c ρ) (max 0 (min p.1 t)) t (oscTestFun m α) y) p.2 := by
    unfold s57pA
    rw [HRS.MS.Fcau.fcau_gradient_sub hc2 hc1]
  rw [e, s57p_norm_gradient]
  exact s57p_iter_neg (hc1.sub hc2) (by funext y; ring) (P.hb α t ht _ hcl 1 (by have := P.Fx.hn4; omega) p.2)

theorem S57pPairBd.Hdiff (P : S57pPairBd θ T n K KN s M Q ν νN c cN ρ ρN A Λc νbar m J Ca CaN Cd CdN Cp1 Cp2 Dt)
    (α : MultiIndex d) {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (h2T : t₂ ≤ T) (p : ℝ × Euc d)
    (hp : p.1 ∈ Set.Icc (0 : ℝ) t₁) :
    ‖(s57pA (fixedEqCoeff s M Q νN cN ρN) t₂ (oscTestFun m α) p - s57pA (fixedEqCoeff s M Q ν c ρ) t₂ (oscTestFun m α) p) -
      (s57pA (fixedEqCoeff s M Q νN cN ρN) t₁ (oscTestFun m α) p - s57pA (fixedEqCoeff s M Q ν c ρ) t₁ (oscTestFun m α) p)‖ ≤
      Cp2 * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) * Dt * (t₂ - t₁) := by
  have ht1 : t₁ ∈ Set.Icc (0 : ℝ) T := ⟨h0, h12.trans h2T⟩
  have ht2 : t₂ ∈ Set.Icc (0 : ℝ) T := ⟨h0.trans h12, h2T⟩
  have hp2 : p.1 ∈ Set.Icc (0 : ℝ) t₂ := ⟨hp.1, hp.2.trans h12⟩
  obtain ⟨a1, a2⟩ := P.cont1 α ht1 hp
  obtain ⟨b1, b2⟩ := P.cont1 α ht2 hp2
  have e1 : max 0 (min p.1 t₂) = p.1 := by rw [min_eq_left hp2.2, max_eq_right hp.1]
  have e2 : max 0 (min p.1 t₁) = p.1 := by rw [min_eq_left hp.2, max_eq_right hp.1]
  have e : (s57pA (fixedEqCoeff s M Q νN cN ρN) t₂ (oscTestFun m α) p - s57pA (fixedEqCoeff s M Q ν c ρ) t₂ (oscTestFun m α) p) -
      (s57pA (fixedEqCoeff s M Q νN cN ρN) t₁ (oscTestFun m α) p - s57pA (fixedEqCoeff s M Q ν c ρ) t₁ (oscTestFun m α) p) =
      gradient (fun y => (propagatorW (fixedEqCoeff s M Q νN cN ρN) p.1 t₂ (oscTestFun m α) y -
        propagatorW (fixedEqCoeff s M Q ν c ρ) p.1 t₂ (oscTestFun m α) y) -
        (propagatorW (fixedEqCoeff s M Q νN cN ρN) p.1 t₁ (oscTestFun m α) y -
        propagatorW (fixedEqCoeff s M Q ν c ρ) p.1 t₁ (oscTestFun m α) y)) p.2 := by
    rw [s57p_grad4 b2 b1 a2 a1]
    unfold s57pA
    rw [e1, e2]
  rw [e, s57p_norm_gradient]
  refine s57p_iter_neg (F := fun y => (propagatorW (fixedEqCoeff s M Q ν c ρ) p.1 t₂ (oscTestFun m α) y -
        propagatorW (fixedEqCoeff s M Q νN cN ρN) p.1 t₂ (oscTestFun m α) y) -
        (propagatorW (fixedEqCoeff s M Q ν c ρ) p.1 t₁ (oscTestFun m α) y -
        propagatorW (fixedEqCoeff s M Q νN cN ρN) p.1 t₁ (oscTestFun m α) y)) ((b1.sub b2).sub (a1.sub a2))
    (by funext y; ring) ?_
  exact P.hd α t₁ t₂ h0 h12 h2T p.1 hp p.2

end HRS.MS.FixEq
