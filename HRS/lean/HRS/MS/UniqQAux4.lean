import HRS.MS.UniqQAux3

/-!
# UNIQ-Q, part 4: the abstract solution class and the one-step estimate

(plan: `UniqQAux1`.)  `UqSol Q ν t u S`: `u` is a bounded `C_b²` classical solution on `[0,t]` of
`-∂_r u = L₀ u + S`, `L₀ = νΔ + ⟨-Qx,∇·⟩` (`uqL0`).

* `uniqq_cmp`: comparison of two classical sub/super-solutions (from `uniqq_mp`).
* `uniqq_step`: for `0 ≤ a < b ≤ t` and `|S| ≤ m` on `(a,b) × ℝ^d`: `|u(a) - P_{b-a} u(b)| ≤ (b-a) m`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.UniqQ

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Lc

variable {d : ℕ}

/-- the OU generator -/
def uqL0 (Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (φ : Euc d → ℝ) (x : Euc d) : ℝ :=
  ν * Laplacian.laplacian φ x + inner ℝ (-(Torus.matVec Q x)) (gradient φ x)

theorem uqL0_sub (Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) {f g : Euc d → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (x : Euc d) :
    uqL0 Q ν (fun y => f y - g y) x = uqL0 Q ν f x - uqL0 Q ν g x := by
  unfold uqL0
  rw [lu_lap_sub hf hg, lu_grad_sub (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num)),
    inner_sub_right]
  ring

/-- a bounded classical solution of `-∂_r u = L₀ u + S` on `[0,t]` -/
structure UqSol (Q : Matrix (Fin d) (Fin d) ℝ) (ν t : ℝ) (u S : ℝ → Euc d → ℝ) : Prop where
  c2 : ∀ r ∈ Icc 0 t, ContDiff ℝ 2 (u r)
  bdd : ∃ B : ℝ, ∀ j ≤ 2, ∀ r ∈ Icc 0 t, ∀ x, ‖iteratedFDeriv ℝ j (u r) x‖ ≤ B
  cont : Continuous fun p : Icc (0 : ℝ) t × Euc d => u p.1 p.2
  der : ∀ x, ∀ r ∈ Ioo 0 t,
    HasDerivAt (fun r' => u r' x) (-(uqL0 Q ν (u r) x + S r x)) r

/-- comparison of a sub- and a super-solution -/
theorem uniqq_cmp {Q : Matrix (Fin d) (Fin d) ℝ} {ν M a b : ℝ} (hν : 0 ≤ ν)
    {f g Df Dg : ℝ → Euc d → ℝ}
    (hf2 : ∀ r ∈ Icc a b, ContDiff ℝ 2 (f r)) (hg2 : ∀ r ∈ Icc a b, ContDiff ℝ 2 (g r))
    (hfb : ∃ B, ∀ r ∈ Icc a b, ∀ x, |f r x| ≤ B) (hgb : ∃ B, ∀ r ∈ Icc a b, ∀ x, |g r x| ≤ B)
    (hfc : ContinuousOn (fun p : ℝ × Euc d => f p.1 p.2) (Icc a b ×ˢ univ))
    (hgc : ContinuousOn (fun p : ℝ × Euc d => g p.1 p.2) (Icc a b ×ˢ univ))
    (hterm : ∀ x, f b x ≤ g b x)
    (hdf : ∀ x, ∀ r ∈ Ioo a b, HasDerivAt (fun r' => f r' x) (Df r x) r)
    (hdg : ∀ x, ∀ r ∈ Ioo a b, HasDerivAt (fun r' => g r' x) (Dg r x) r)
    (hineq : ∀ x, ∀ r ∈ Ioo a b, -Df r x + Dg r x ≤ uqL0 Q ν (f r) x - uqL0 Q ν (g r) x + M)
    {r : ℝ} (hr : r ∈ Icc a b) (x : Euc d) : f r x - g r x ≤ (b - r) * M := by
  obtain ⟨Bf, hBf⟩ := hfb
  obtain ⟨Bg, hBg⟩ := hgb
  refine uniqq_mp (Q := Q) (ν := ν) (M := M) (a := a) (b := b) hν
    (w := fun r x => f r x - g r x) (Dt := fun r x => Df r x - Dg r x)
    (fun r hr => (hf2 r hr).sub (hg2 r hr)) ⟨Bf + Bg, fun r hr x => ?_⟩ (hfc.sub hgc)
    (fun x => by simpa using hterm x) (fun x r hr => (hdf x r hr).sub (hdg x r hr))
    (fun x r hr => ?_) hr x
  · exact (abs_sub _ _).trans (add_le_add (hBf r hr x) (hBg r hr x))
  · have h := hineq x r hr
    have e := uqL0_sub Q ν (hf2 r ⟨hr.1.le, hr.2.le⟩) (hg2 r ⟨hr.1.le, hr.2.le⟩) x
    show -(Df r x - Dg r x) ≤ uqL0 Q ν (fun y => f r y - g r y) x + M
    rw [e]
    linarith

/-- **one step**: `|u(a) - P_{b-a} u(b)| ≤ (b-a) m` when `|S| ≤ m` -/
theorem uniqq_step {Q : Matrix (Fin d) (Fin d) ℝ} {ν t : ℝ} (hν : 0 < ν) {u S : ℝ → Euc d → ℝ}
    (hu : UqSol Q ν t u S) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbt : b ≤ t)
    (hS : ∀ r ∈ Ioo a b, ∀ x, |S r x| ≤ m) (y : Euc d) :
    |u a y - ouSg Q ν (b - a) (u b) y| ≤ (b - a) * m := by
  obtain ⟨B, hB⟩ := hu.bdd
  have hb0 : 0 ≤ b := ha.trans hab.le
  have hIsub : Icc a b ⊆ Icc 0 t := Icc_subset_Icc ha hbt
  have hub : ContDiff ℝ 2 (u b) := hu.c2 b ⟨hb0, hbt⟩
  have hM : ∀ i ≤ 2, ∀ z, ‖iteratedFDeriv ℝ i (u b) z‖ ≤ B := fun i hi z => hB i hi b ⟨hb0, hbt⟩ z
  have hP := ou_backward Q hν.le hb0 hub hM
  set P : ℝ → Euc d → ℝ := fun r => ouSg Q ν (b - r) (u b) with hPdef
  have hcu : ContinuousOn (fun p : ℝ × Euc d => u p.1 p.2) (Icc a b ×ˢ univ) :=
    (lu_contOn hu.cont).mono (prod_mono hIsub subset_rfl)
  have hcP : ContinuousOn (fun p : ℝ × Euc d => P p.1 p.2) (Icc a b ×ˢ univ) :=
    (lu_contOn hP.cont).mono (prod_mono (Icc_subset_Icc ha le_rfl) subset_rfl)
  obtain ⟨BP, hBP⟩ := hP.bdd
  have hdu : ∀ x, ∀ r ∈ Ioo a b, HasDerivAt (fun r' => u r' x) (-(uqL0 Q ν (u r) x + S r x)) r :=
    fun x r hr => hu.der x r ⟨ha.trans_lt hr.1, hr.2.trans_le hbt⟩
  have hdP : ∀ x, ∀ r ∈ Ioo a b, HasDerivAt (fun r' => P r' x) (-(uqL0 Q ν (P r) x)) r := by
    intro x r hr
    exact hP.time_deriv x r ⟨ha.trans_lt hr.1, hr.2⟩
  have hu2 : ∀ r ∈ Icc a b, ContDiff ℝ 2 (u r) := fun r hr => hu.c2 r (hIsub hr)
  have hP2 : ∀ r ∈ Icc a b, ContDiff ℝ 2 (P r) := fun r hr => hP.c2 r ⟨ha.trans hr.1, hr.2⟩
  have hub' : ∃ B', ∀ r ∈ Icc a b, ∀ x, |u r x| ≤ B' :=
    ⟨B, fun r hr x => by
      have := hB 0 (by norm_num) r (hIsub hr) x
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this⟩
  have hPb' : ∃ B', ∀ r ∈ Icc a b, ∀ x, |P r x| ≤ B' :=
    ⟨BP, fun r hr x => hBP r ⟨ha.trans hr.1, hr.2⟩ x⟩
  have hm0 : 0 ≤ m := by
    by_contra hm
    push Not at hm
    have := hS ((a + b) / 2) ⟨by linarith, by linarith⟩ 0
    linarith [abs_nonneg (S ((a + b) / 2) 0)]
  rw [abs_le]
  have hPa : P a y = ouSg Q ν (b - a) (u b) y := rfl
  have hPbt : ∀ x, P b x = u b x := fun x => by simp [hPdef, ouSg_zero Q hν.le]
  constructor
  · -- lower bound: apply to (P, u)
    have := uniqq_cmp (Q := Q) (ν := ν) (M := m) (a := a) (b := b) hν.le hP2 hu2 hPb' hub' hcP hcu
      (fun x => by rw [hPbt]) hdP hdu (fun x r hr => by
        have := hS r hr x
        have h2 := neg_le_abs (S r x)
        linarith) (r := a) ⟨le_rfl, hab.le⟩ y
    linarith
  · have := uniqq_cmp (Q := Q) (ν := ν) (M := m) (a := a) (b := b) hν.le hu2 hP2 hub' hPb' hcu hcP
      (fun x => by rw [hPbt]) hdu hdP (fun x r hr => by
        have := hS r hr x
        have h2 := le_abs_self (S r x)
        linarith) (r := a) ⟨le_rfl, hab.le⟩ y
    linarith

end HRS.MS.UniqQ
