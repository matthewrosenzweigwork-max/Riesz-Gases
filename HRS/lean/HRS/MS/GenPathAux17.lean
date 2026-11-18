import HRS.MS.GenPathAux16

/-!
# S5.6 packet P5a: continuity in `r` of the pairings of the nonautonomous feature with elements of `𝒦`

`s56_gradComp_cont_r`: `r ↦ ∂_a U^{r,t}ψ(x)` is continuous on `[0,t]` for a classical adjoint solution.
`s56_inner_ellVec`: `⟨ellVec c, v⟩ = ∑ c_α v_α`.
`s56_feat_inner_cont`: for `e ∈ 𝒦` and `x ∈ ℝ^d`, `r ↦ ⟨Γ_{r,a}(x), e⟩` is continuous on `[0,T]` (dominated convergence in the
`L²_t` pairing: the integrand is continuous in `r` off the null set `{t = r}`).
Helper names carry the prefix `s56_`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole

variable {d : ℕ}

theorem s56_inner_ellVec (m : ℝ) {c : MultiIndex d → ℝ} (h : Memℓp c 2) (v : OscDual d m) :
    inner ℝ (ellVec (d := d) m c) v = ∑' α, c α * OscDual.coord v α := by
  have hv : ellVec (d := d) m c = (⟨c, h⟩ : lp (fun _ : MultiIndex d => ℝ) 2) := dif_pos h
  rw [hv]
  have := lp.inner_eq_tsum (𝕜 := ℝ) (G := fun _ : MultiIndex d => ℝ) (⟨c, h⟩ : lp (fun _ : MultiIndex d => ℝ) 2)
    (show lp (fun _ : MultiIndex d => ℝ) 2 from v)
  refine this.trans (tsum_congr fun α => ?_)
  simp [OscDual.coord, mul_comm]

theorem s56_gradComp_cont_r {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) (a : Fin d) (x : Euc d) :
    ContinuousOn (fun r => gradComp a (f r) x) (Set.Icc 0 t) := by
  have h := hf.cont_c2 1 (by norm_num)
  rw [continuousOn_iff_continuous_restrict]
  have e : (fun r : Set.Icc (0 : ℝ) t => gradComp a (f r) x) = fun r : Set.Icc (0 : ℝ) t =>
      (iteratedFDeriv ℝ 1 (f r) x) ![EuclideanSpace.single a (1 : ℝ)] := by
    funext r
    rw [iteratedFDeriv_one_apply]
    exact HRS.Whole.movtr_gradient_apply (f r) x a
  show Continuous fun r : Set.Icc (0 : ℝ) t => gradComp a (f r) x
  rw [e]
  have hp : Continuous fun r : Set.Icc (0 : ℝ) t => ((r, x) : Set.Icc (0 : ℝ) t × Euc d) :=
    continuous_id.prodMk continuous_const
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Euc d) ℝ
    ![EuclideanSpace.single a (1 : ℝ)]).continuous.comp (h.comp hp)

/-- The weights `b_α = λ_α^{(J-m)/2}` are in `[0,1]` and square summable. -/
theorem s56_b_le_one (b : WholeBounds d) (hbv : b.Valid) (α : MultiIndex d) :
    oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2) ≤ 1 := by
  refine Real.rpow_le_one_of_one_le_of_nonpos (oscEv_one_le α) ?_
  have hJ : (b.J : ℝ) + 3 * d + 4 < b.m := hbv.hm
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have : (0 : ℝ) ≤ b.J := Nat.cast_nonneg _
  linarith

theorem s56_b_sq_summable (b : WholeBounds d) (hbv : b.Valid) :
    Summable fun α : MultiIndex d => (oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2)) ^ 2 := by
  have hsum := HRS.MS.Go.s55f_summable b hbv
  refine hsum.of_nonneg_of_le (fun α => sq_nonneg _) (fun α => ?_)
  have h1 := s56_b_le_one b hbv α
  have h0 : 0 ≤ oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2) := Real.rpow_nonneg (oscEigenvalue_pos α).le _
  nlinarith

theorem s56_sq_summable_of_memℓp {c : MultiIndex d → ℝ} (h : Memℓp c 2) : Summable fun α => c α ^ 2 := by
  have := (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).1 h
  simpa using this

/-- Continuity of a coordinate pairing with a dominated family. -/
theorem s56_cont_pairing {bb : MultiIndex d → ℝ} (hb2 : Summable fun α => bb α ^ 2) (hb0 : ∀ α, 0 ≤ bb α)
    (Bco : ℝ) {s : Set ℝ} {c : MultiIndex d → ℝ → ℝ} (hcont : ∀ α, ContinuousOn (c α) s)
    (hbd : ∀ α r, r ∈ s → |c α r| ≤ Bco * bb α) {γ : MultiIndex d → ℝ} (hγ : Summable fun α => γ α ^ 2) :
    ContinuousOn (fun r => ∑' α, c α r * γ α) s := by
  refine continuousOn_tsum (u := fun α => |Bco| * ((bb α ^ 2 + γ α ^ 2) / 2)) (fun α => (hcont α).mul continuousOn_const)
    ((hb2.add hγ).div_const 2 |>.mul_left |Bco|) (fun α r hr => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 := hbd α r hr
  have h2 : bb α * |γ α| ≤ (bb α ^ 2 + γ α ^ 2) / 2 := by
    nlinarith [sq_nonneg (bb α - |γ α|), sq_abs (γ α)]
  calc |c α r| * |γ α| ≤ (Bco * bb α) * |γ α| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ ≤ |Bco| * (bb α * |γ α|) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg (hb0 α) (abs_nonneg _))
    _ ≤ |Bco| * ((bb α ^ 2 + γ α ^ 2) / 2) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

end HRS.MS.GenPath
