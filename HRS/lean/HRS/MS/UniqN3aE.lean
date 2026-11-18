import HRS.MS.UniqN3aB
import HRS.MS.UniqN3aC
import HRS.MS.UniqN3aD

/-!
# N3a, part E: `m_q v̂ ∈ L²` for `v ∈ C²_c`

Mollify `v` to Schwartz functions `S_n = mo n v`; the energies `E(S_n)` are bounded, `Ŝ_n → v̂` in
`L²`, hence (Fatou along an a.e.-convergent subsequence) `m_q v̂ ∈ L²`.
-/

noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate SchwartzMap LineDeriv

namespace HRS.MS.UniqN3a
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UniqT2

variable {d : ℕ}

/-- The mollified Schwartz approximant. -/
def Sn (n : ℕ) {v : Euc d → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    SchwartzMap (Euc d) ℝ :=
  (mo_hasCompactSupport n hvc).toSchwartzMap (mo_contDiff n hv.continuous)

theorem Sn_apply (n : ℕ) {v : Euc d → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    ⇑(Sn n hv hvc) = mo n v := rfl

/-- Volume of the closed ball (as a real number). -/
def Vol (d : ℕ) (R : ℝ) : ℝ := (volume (closedBall (0 : Euc d) R)).toReal

theorem Vol_nonneg (R : ℝ) : 0 ≤ Vol d R := ENNReal.toReal_nonneg

theorem l2_le {h : Euc d → ℝ} {R M : ℝ} (hc : Continuous h)
    (hsupp : ∀ x, h x ≠ 0 → x ∈ closedBall (0 : Euc d) R) (hM : ∀ x, |h x| ≤ M) :
    Integrable (fun x => h x ^ 2) ∧ ∫ x, h x ^ 2 ≤ M ^ 2 * Vol d R := by
  have hind : Integrable ((closedBall (0 : Euc d) R).indicator (fun _ => M ^ 2)) volume :=
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const measure_closedBall_lt_top.ne)
  have hle : ∀ x, h x ^ 2 ≤ (closedBall (0 : Euc d) R).indicator (fun _ => M ^ 2) x := by
    intro x
    by_cases hx : h x = 0
    · rw [hx]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact Set.indicator_nonneg (fun _ _ => sq_nonneg M) x
    · rw [Set.indicator_of_mem (hsupp x hx)]
      calc h x ^ 2 = |h x| ^ 2 := (sq_abs _).symm
        _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hM x) 2
  have hint : Integrable (fun x => h x ^ 2) volume :=
    hind.mono' (hc.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hle x)
  refine ⟨hint, (integral_mono hint hind hle).trans (le_of_eq ?_)⟩
  rw [integral_indicator measurableSet_closedBall]
  simp [Vol, Measure.real]; ring

/-! ### Derivatives commute with mollification -/

theorem Da_mo (n : ℕ) {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (a : Euc d) :
    Da a (mo n f) = mo n (Da a f) := funext (mo_fderiv n hf hfc a)

theorem qq_mo (n : ℕ) {v : Euc d → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (q : Euc d) :
    qq q (mo n v) = mo n (qq q v) := by
  have h1 : ContDiff ℝ 1 (Da q v) := Da_contDiff (k := 1) (by simpa using hv)
  rw [qq_eq_Da, Da_mo n (hv.of_le (by norm_num)) hvc q, Da_mo n h1 (Da_hasCompactSupport hvc) q,
    qq_eq_Da]

theorem dl_dl_apply (l : Fin d) (S : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    dl l (dl l S) x = qq (EuclideanSpace.single l (1 : ℝ)) (⇑S) x := rfl

/-- Support of mollifications. -/
theorem mo_supp {f : Euc d → ℝ} {R : ℝ} (n : ℕ) (hsupp : Function.support f ⊆ closedBall 0 R) :
    ∀ x, mo n f x ≠ 0 → x ∈ closedBall (0 : Euc d) (R + 1) := fun x hx => mo_support n hsupp hx

/-! ### Uniform bounds on the energies -/

theorem mo_l2_bound {f : Euc d → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {R : ℝ}
    (hsupp : Function.support f ⊆ closedBall 0 R) :
    ∃ E : ℝ, ∀ᶠ n in atTop, ∫ x, mo n f x ^ 2 ≤ E := by
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  obtain ⟨N, hN⟩ := mo_unif hf hfc (ε := 1) one_pos
  refine ⟨(M + 1) ^ 2 * Vol d (R + 1), Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩⟩
  refine (l2_le (R := R + 1) (M := M + 1) ?_ (mo_supp n hsupp) (fun x => ?_)).2
  · exact (mo_contDiff n hf).continuous
  · have h1 := hN n hn x
    have h2 : |f x| ≤ M := by simpa [Real.norm_eq_abs] using hM x
    calc |mo n f x| = |(mo n f x - f x) + f x| := by ring_nf
      _ ≤ |mo n f x - f x| + |f x| := abs_add_le _ _
      _ ≤ _ := by linarith

theorem energy_bound {v : Euc d → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    ∃ E : ℝ, ∀ᶠ n in atTop, energy (Sn n hv hvc) ≤ E := by
  obtain ⟨R1, hR1⟩ := hvc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  have hsupp : Function.support v ⊆ closedBall (0 : Euc d) R1 := fun x hx => hR1 (subset_tsupport _ hx)
  obtain ⟨E0, hE0⟩ := mo_l2_bound hv.continuous hvc hsupp
  have hts : tsupport v ⊆ closedBall (0 : Euc d) R1 := closure_minimal hsupp isClosed_closedBall
  have hl : ∀ l : Fin d, ∃ E : ℝ, ∀ᶠ n in atTop,
      ∫ x, mo n (qq (EuclideanSpace.single l (1 : ℝ)) v) x ^ 2 ≤ E := fun l =>
    mo_l2_bound (qq_contDiff hv) (qq_hasCompactSupport hvc) (R := R1)
      (fun x hx => hts (qq_support_sub _ v hx))
  choose El hEl using hl
  have hall : ∀ᶠ n in atTop, ∀ l : Fin d,
      ∫ x, mo n (qq (EuclideanSpace.single l (1 : ℝ)) v) x ^ 2 ≤ El l :=
    Filter.eventually_all.2 hEl
  refine ⟨(2 * Real.pi) ^ 4 * E0 + d * ∑ l, El l, ?_⟩
  filter_upwards [hE0, hall] with n h0 hl
  unfold energy
  have e1 : ∀ l : Fin d, ∫ x, (dl l (dl l (Sn n hv hvc)) x) ^ 2 =
      ∫ x, mo n (qq (EuclideanSpace.single l (1 : ℝ)) v) x ^ 2 := by
    intro l
    congr 1; funext x
    rw [dl_dl_apply, Sn_apply, qq_mo n hv hvc]
  simp only [e1]
  have : ∫ x, (Sn n hv hvc) x ^ 2 = ∫ x, mo n v x ^ 2 := rfl
  rw [this]
  gcongr
  exact hl _

end HRS.MS.UniqN3a
