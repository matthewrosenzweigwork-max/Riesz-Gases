import HRS.MS.R26T8AP10a13
import HRS.MS.R26T8AP06b
import HRS.MS.R26T8AP01b

/-!
# S8.2 T8A P10a (part 14): jets of the slice `u ↦ Q(u,y)` from the conormal bounds
`r26t8a_p10a_slice_jet`: `‖D^j (Q(·,y)) (x)‖ ≤ ∑_{q ≤ j} C(j,q) A w(x,y) (1 + s^(-(σ+q)) (1+|log s|)^b)`, `s = min 1 |x-y|`,
for `Conormal (k+2) b M σ A Q`, `j ≤ k+2`, `x ≠ y`.  Route: `Q(u,y) = Ψ(Lu + c)`, `L u = (u/2, u)` (`‖L‖ ≤ 1`), `Ψ` the cutoff of `midPair Q`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_p10a_slice_jet {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k b : ℕ} {M σ A : ℝ}
    (hA : 0 ≤ A) {Q : Euc d → Euc d → ℝ} (hQ : Conormal (k + 2) b M σ A Q) {j : ℕ} (hj : j ≤ k + 2)
    {x y : Euc d} (hxy : x ≠ y) :
    ‖iteratedFDeriv ℝ j (fun u => Q u y) x‖ ≤
      ∑ q ∈ Finset.range (j + 1), (j.choose q : ℝ) * (A * pairWeight M x y *
        (1 + (min 1 ‖x - y‖) ^ (-(σ + q)) * (1 + |Real.log (min 1 ‖x - y‖)|) ^ b)) := by
  set X : Euc d := (1 / 2 : ℝ) • (x + y) with hX
  set z : Euc d := x - y with hz
  have hz0 : z ≠ 0 := sub_ne_zero.2 hxy
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hx1 : X + (1 / 2 : ℝ) • z = x := by rw [hX, hz]; module
  have hy1 : X - (1 / 2 : ℝ) • z = y := by rw [hX, hz]; module
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 * ‖z‖ := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hRdef]; positivity
  have hl : R / 4 < ‖z‖ := by rw [hRdef]; linarith
  set Ψ : Euc d × Euc d → ℝ := fun Yw => r26t8a_psiCut chi R Yw.2 * midPair Q Yw.1 Yw.2 with hΨdef
  have hΨ : ContDiff ℝ (j : WithTop ℕ∞) Ψ :=
    (r26t8a_gtilde_contDiff hchi hR hQ.1).of_le (by exact_mod_cast hj)
  -- the slice as a composition
  set L : Euc d →L[ℝ] Euc d × Euc d :=
    ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Euc d)).prod (ContinuousLinearMap.id ℝ (Euc d)) with hL
  set c : Euc d × Euc d := ((1 / 2 : ℝ) • y, -y) with hc
  have hLu : ∀ u : Euc d, L u + c = ((1 / 2 : ℝ) • (u + y), u - y) := by
    intro u; ext <;> simp [hL, hc] <;> try module
  have hLn : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    simp only [hL, ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, one_mul, Prod.norm_def]
    refine max_le ?_ le_rfl
    rw [norm_smul]
    have : ‖(1 / 2 : ℝ)‖ ≤ 1 := by norm_num
    nlinarith [norm_nonneg v]
  have hopen : IsOpen {u : Euc d | R / 4 < ‖u - y‖} :=
    isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
  have hev : (fun u : Euc d => Q u y) =ᶠ[𝓝 x] fun u => (fun w => Ψ (w + c)) (L u) := by
    filter_upwards [hopen.mem_nhds (show R / 4 < ‖x - y‖ from hl)] with u hu
    simp only [hLu, hΨdef, r26t8a_psiCut_one hchi hR (le_of_lt hu : R / 4 ≤ ‖u - y‖), one_mul, midPair]
    congr 1
    · module
    · module
  have hfe : iteratedFDeriv ℝ j (fun u : Euc d => Q u y) x =
      iteratedFDeriv ℝ j (fun u => (fun w => Ψ (w + c)) (L u)) x := (hev.iteratedFDeriv ℝ j).self_of_nhds
  have hsh : ContDiff ℝ (j : WithTop ℕ∞) (fun w => Ψ (w + c)) := hΨ.comp (contDiff_id.add contDiff_const)
  have hcomp := L.iteratedFDeriv_comp_right (n := (j : WithTop ℕ∞)) hsh x (i := j) le_rfl
  have hLx : L x + c = (X, z) := by rw [hLu x]
  have h1 : ‖iteratedFDeriv ℝ j (fun u : Euc d => Q u y) x‖ ≤ ‖iteratedFDeriv ℝ j Ψ (X, z)‖ := by
    rw [hfe]
    change ‖iteratedFDeriv ℝ j ((fun w => Ψ (w + c)) ∘ L) x‖ ≤ _
    rw [hcomp, iteratedFDeriv_comp_add_right, hLx]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have : ∏ _i : Fin j, ‖L‖ ≤ 1 := by simpa using pow_le_one₀ (norm_nonneg L) hLn
    calc ‖iteratedFDeriv ℝ j Ψ (X, z)‖ * ∏ _i : Fin j, ‖L‖ ≤ ‖iteratedFDeriv ℝ j Ψ (X, z)‖ * 1 :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = _ := mul_one _
  refine h1.trans ((r26t8a_joint_le_nest j Ψ X z hΨ).trans ?_)
  refine Finset.sum_le_sum fun q hq => ?_
  have hq' : q ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  rw [r26t8a_nest_gtilde hchi hR (F := Q) (j - q) q X z hl]
  have hb := hQ.2 (j - q) q (by omega) X z hz0
  rw [hx1, hy1] at hb
  exact hb

end HRS.MS.R26T8A
