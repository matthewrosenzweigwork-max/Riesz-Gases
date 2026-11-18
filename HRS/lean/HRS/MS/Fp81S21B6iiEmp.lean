import HRS.MS.Fp81S21CoeffMoments8
import HRS.MS.Fp81S21WickMomRep9

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- A configuration representative retains its agreement on the common
full-measure event supplied by the joint particle modification. -/
theorem fp81s21_emp_common_time_of_reference
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) (N : ℕ) (hN : 2 ≤ N)
    (A : Particle R N)
    (E : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (μ : ℝ → Measure (Euc p.d))
    (hμ : ∀ u, 0 ≤ u → μ u = r26t3_mu R u)
    (hi : ∀ u, Integrable (fun x : Euc p.d => jbracket x ^ ((p.d : ℝ) + 4)) (μ u))
    (hm : ∀ j, Measurable (fun u => HRS.Whole.pair (μ u) (E.test j))) :
    ∃ q : ℝ → A.Ω → r26t6_Coeff,
      Measurable (Function.uncurry q) ∧
      ∀ᵐ ω ∂A.P, ∀ u : ℝ, 0 ≤ u → ∀ f : Euc p.d → ℝ,
        IsR2Test f → fp81s21_chartAction E (q u ω) f =
          fp81s21_particleEmpField R N A u ω f := by
  have hd : 1 ≤ p.d := le_trans (by decide : 1 ≤ 2) p.hd
  have hp : 0 ≤ (p.d : ℝ) + 4 := by positivity
  have hr : (p.d : ℝ) / 2 < (2 * p.d + 6 : ℕ) := by push_cast; nlinarith
  have hc : (p.d : ℝ) < 2 * ((p.d : ℝ) + 4) := by nlinarith
  obtain ⟨z, hz, hzrep⟩ := fp81s21_emp_config_rep hd hp hr hc E (lt_of_lt_of_le (by decide : 0 < 2) hN) μ hi hm
  have hx : ∀ t, Measurable (A.X t) := (A.strong (1 : ℝ)).adapted
  obtain ⟨Y, hY, hYae⟩ := HRS.MS.R2S11.s11_X_joint hx (A.strong (1 : ℝ)).cont
  let q : ℝ → A.Ω → r26t6_Coeff := fun u ω => z (max u 0) (Y (max u 0, ω))
  have hclip : Measurable (fun u : ℝ => max u 0) := by fun_prop
  have hYclip : Measurable (fun x : ℝ × A.Ω => Y (max x.1 0, x.2)) :=
    hY.comp ((hclip.comp measurable_fst).prodMk measurable_snd)
  refine ⟨q, hz.comp ((hclip.comp measurable_fst).prodMk hYclip), ?_⟩
  filter_upwards [hYae] with ω hω
  intro u hu f hf
  have hclipu : max u 0 = u := max_eq_left hu
  have h := (hzrep u (A.X u.toNNReal ω)).1 f hf
  simpa [q, hclipu, hω u, hμ u hu, fp81s21_particleEmpField] using h

/-- Compact-test agreement determines chart coefficients. -/
theorem fp81s21_emp_coeff_unique {d r : ℕ} {Pw : ℝ}
    (E : r26t6_WeightedChart d r Pw) (z w : r26t6_Coeff)
    (h : ∀ f, IsR2Test f → fp81s21_chartAction E z f = fp81s21_chartAction E w f) :
    z = w := by
  apply lp.ext (funext fun j => ?_)
  have hcoord (v : r26t6_Coeff) : fp81s21_chartAction E v (E.test j) = v j := by
    have he : E.encode (E.test j) = (lp.single 2 j (1 : ℝ) : r26t6_Coeff) := by
      ext i
      change E.encode (E.test j) i = _
      rw [E.test_coord]
      simp [lp.single_apply, Pi.single_apply, eq_comm]
    rw [fp81s21_chartAction, he]
    simpa [lp.inner_single_right]
  rw [← hcoord z, ← hcoord w]
  exact h (E.test j) (E.test_smooth j)

#print axioms fp81s21_emp_common_time_of_reference
#print axioms fp81s21_emp_coeff_unique
end HRS.Fp81.S21
end
