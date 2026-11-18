import HRS.MS.S111K2B04e

/-!
# S11.1 continuation, B04 (part 6): the vector `Y_v(s) = (z^v(U(v,s)φ_α))_α ∈ ℓ²`

`s111k2_Y_norm`: `‖Y_v(s)‖ ≤ ‖z^v‖ c_E √S e^{-c_0(s-v)}` (for `‖z^v‖_{F_{r,P}} < ∞`, `z^v(1) = 0`);
`s111k2_Y_cont_orbit`: `s ↦ Y_v(s)` is continuous on `[v,∞)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K2

open HRS HRS.Whole HRS.MS.Go HRS.MS.CovMeas HRS.MS.R2WinErr HRS.MS.FixEq

variable {d : ℕ}

/-- The coordinate vector of the forcing `z^v` propagated to the terminal time `s`. -/
def s111k2_Y (C : WholeCoeff d) (m : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) (v s : ℝ) : OscDual d m :=
  ellVec m (fun α => z v (propagatorW C v s (oscTestFun m α)))

lemma s111k2_Y_cont_orbit {C : WholeCoeff d} {m c0 : ℝ} {r : ℕ} {b : MultiIndex d → ℝ}
    (hW : S111k2WindowOrbitInput C m c0 r b) (hc0 : 0 < c0) (hbs : Summable fun α => b α ^ 2)
    {Pw H : ℝ} (hP : (d : ℝ) + 2 < 2 * Pw) {z : ℝ → (Euc d → ℝ) → ℝ} (hz : IsR2L1F r Pw H z)
    {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) H) (hone : z v (fun _ => 1) = 0)
    (hdual : dualNormE r Pw (z v) < ⊤) :
    ContinuousOn (fun s => s111k2_Y C m z v s) (Set.Ici v) := by
  have hη := s111k2_bounded_of_L1F hz hv
  have hweak : ∀ α, ∀ s ∈ Set.Ici v, ∀ j : ℕ, 1 ≤ j → j ≤ r + 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (propagatorW C v s (oscTestFun m α)) x‖ ≤ b α := by
    intro α s hs j h1 h2 x
    refine ((s111k2_orbit_data hW α hv.1 hs).2.1 j h1 h2 x).trans ?_
    refine mul_le_of_le_one_right (hW.nonneg α) ?_
    rw [Real.exp_le_one_iff]; nlinarith [hs.out]
  unfold s111k2_Y
  refine s111k2_Y_cont m r hP hη hdual (Set.Ici v) (fun α s => propagatorW C v s (oscTestFun m α)) b
    hW.nonneg hbs (fun α s hs => (s111k2_orbit_data hW α hv.1 hs).1) hweak
    (fun α s hs => (s111k2_orbit_data hW α hv.1 hs).2.2)
    (fun α x s hs => (hW.terminal_derivative α v s hv.1 hs x).continuousWithinAt)
    (fun α s hs => ?_)
  exact s111k2_zero hP hη hone (s111k2_orbit_data hW α hv.1 hs).1 (hW.nonneg α) (hweak α s hs)

lemma s111k2_Ycoord_sq_le {C : WholeCoeff d} {m c0 : ℝ} {r : ℕ} {b : MultiIndex d → ℝ}
    (hW : S111k2WindowOrbitInput C m c0 r b)
    {Pw H : ℝ} (hP : (d : ℝ) + 2 < 2 * Pw) {z : ℝ → (Euc d → ℝ) → ℝ} (hz : IsR2L1F r Pw H z)
    {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) H) (hone : z v (fun _ => 1) = 0)
    (hdual : dualNormE r Pw (z v) < ⊤) {s : ℝ} (hvs : v ≤ s) (α : MultiIndex d) :
    (z v (propagatorW C v s (oscTestFun m α))) ^ 2 ≤
      ((dualNormE r Pw (z v)).toReal * s111k2_CE d r Pw * Real.exp (-c0 * (s - v))) ^ 2 * b α ^ 2 := by
  have hη := s111k2_bounded_of_L1F hz hv
  set K : ℝ := (dualNormE r Pw (z v)).toReal * s111k2_CE d r Pw with hK
  have he0 : 0 ≤ Real.exp (-c0 * (s - v)) := (Real.exp_pos _).le
  obtain ⟨h1, h2, h3⟩ := s111k2_orbit_data hW α hv.1 hvs
  have := s111k2_coord_bound hP hη hdual hone h1
    (mul_nonneg (hW.nonneg α) he0) h2 h3
  have h4 : |z v (propagatorW C v s (oscTestFun m α))| ≤ K * Real.exp (-c0 * (s - v)) * b α := by
    calc _ ≤ (dualNormE r Pw (z v)).toReal * (s111k2_CE d r Pw * (b α * Real.exp (-c0 * (s - v)))) := this
      _ = _ := by rw [hK]; ring
  calc (z v (propagatorW C v s (oscTestFun m α))) ^ 2
      = |z v (propagatorW C v s (oscTestFun m α))| ^ 2 := (sq_abs _).symm
    _ ≤ (K * Real.exp (-c0 * (s - v)) * b α) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h4 2
    _ = _ := by rw [hK]; ring

lemma s111k2_Ycoord_memell {C : WholeCoeff d} {m c0 : ℝ} {r : ℕ} {b : MultiIndex d → ℝ}
    (hW : S111k2WindowOrbitInput C m c0 r b) (hbs : Summable fun α => b α ^ 2)
    {Pw H : ℝ} (hP : (d : ℝ) + 2 < 2 * Pw) {z : ℝ → (Euc d → ℝ) → ℝ} (hz : IsR2L1F r Pw H z)
    {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) H) (hone : z v (fun _ => 1) = 0)
    (hdual : dualNormE r Pw (z v) < ⊤) {s : ℝ} (hvs : v ≤ s) :
    Memℓp (fun α => z v (propagatorW C v s (oscTestFun m α))) 2 :=
  s111k2_memell_of_le (hbs.mul_left _) (s111k2_Ycoord_sq_le hW hP hz hv hone hdual hvs)

lemma s111k2_Y_norm {C : WholeCoeff d} {m c0 : ℝ} {r : ℕ} {b : MultiIndex d → ℝ}
    (hW : S111k2WindowOrbitInput C m c0 r b) (hbs : Summable fun α => b α ^ 2) {S : ℝ}
    (hS : (∑' α, b α ^ 2) ≤ S)
    {Pw H : ℝ} (hP : (d : ℝ) + 2 < 2 * Pw) {z : ℝ → (Euc d → ℝ) → ℝ} (hz : IsR2L1F r Pw H z)
    {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) H) (hone : z v (fun _ => 1) = 0)
    (hdual : dualNormE r Pw (z v) < ⊤) {s : ℝ} (hvs : v ≤ s) :
    ‖s111k2_Y C m z v s‖ ≤
      ((dualNormE r Pw (z v)).toReal * s111k2_CE d r Pw * Real.sqrt S) * Real.exp (-c0 * (s - v)) := by
  have hη := s111k2_bounded_of_L1F hz hv
  set K : ℝ := (dualNormE r Pw (z v)).toReal * s111k2_CE d r Pw with hK
  have hK0 : 0 ≤ K := mul_nonneg ENNReal.toReal_nonneg (s111k2_CE_nonneg r Pw)
  set e : ℝ := Real.exp (-c0 * (s - v)) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hcoord : ∀ α, |z v (propagatorW C v s (oscTestFun m α))| ≤ K * e * b α := by
    intro α
    obtain ⟨h1, h2, h3⟩ := s111k2_orbit_data hW α hv.1 hvs
    have := s111k2_coord_bound hP hη hdual hone h1 (mul_nonneg (hW.nonneg α) he0) h2 h3
    calc _ ≤ (dualNormE r Pw (z v)).toReal * (s111k2_CE d r Pw * (b α * e)) := this
      _ = K * e * b α := by rw [hK]; ring
  have hg : Summable fun α => (K * e) ^ 2 * b α ^ 2 := hbs.mul_left _
  have hv2 : ∀ α, (z v (propagatorW C v s (oscTestFun m α))) ^ 2 ≤ (K * e) ^ 2 * b α ^ 2 := fun α => by
    calc _ = |z v (propagatorW C v s (oscTestFun m α))| ^ 2 := (sq_abs _).symm
      _ ≤ (K * e * b α) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hcoord α) 2
      _ = _ := by ring
  have hn := (s57p_ellVec_norm_sq (m := m) hg hv2).2
  have hsum : ∑' α, (K * e) ^ 2 * b α ^ 2 ≤ (K * e) ^ 2 * S := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hS (sq_nonneg _)
  have hKe : 0 ≤ K * e * Real.sqrt S := by
    have : 0 ≤ S := le_trans (tsum_nonneg fun _ => sq_nonneg _) hS
    positivity
  have hS0 : 0 ≤ S := le_trans (tsum_nonneg fun _ => sq_nonneg _) hS
  have hsq : ‖s111k2_Y C m z v s‖ ^ 2 ≤ (K * e * Real.sqrt S) ^ 2 := by
    unfold s111k2_Y
    calc ‖(ellVec m (fun α => z v (propagatorW C v s (oscTestFun m α))) : OscDual d m)‖ ^ 2
        ≤ (K * e) ^ 2 * S := hn.trans hsum
      _ = (K * e * Real.sqrt S) ^ 2 := by rw [mul_pow (K * e) (Real.sqrt S), Real.sq_sqrt hS0]
  have hle := (pow_le_pow_iff_left₀ (norm_nonneg _) hKe (by norm_num : (2 : ℕ) ≠ 0)).1 hsq
  calc ‖s111k2_Y C m z v s‖ ≤ K * e * Real.sqrt S := hle
    _ = _ := by rw [hK, he]; ring

end HRS.MS.S111K2
