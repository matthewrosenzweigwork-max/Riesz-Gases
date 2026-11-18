import HRS.MS.MovLinAux5

/-!
# MOV-2a, part 2: `V = q'² |x|²/4 - q' d/2 + V_1`, `V_1 ∈ C_b^∞`, and `S = S_0 + ν V_1 + P`

Namespace `HRS.MS.MovLin`, helper prefix `mov2a_`.  Infrastructure for S6.2 (`W:lem:r2mov-linear`); not a manuscript row.

Notation: `q' = β q`, `ν = β⁻¹`, `F = movForce d s ρ = ∇(g * ρ)` (for the thermal `ρ`, `mov_force_tail_thermal`),
so that the Euler equation `ν ∇ log ρ + q x + F = 0` (`mv0_thermal_force`) reads `∇ log ρ = -q' x - β F`
(`B = -β F`).  Then `Δ log ρ = -q' d - β div F` and

`V = (q' x)²/4 + (β² q /2) ⟨x, F⟩ + (β²/4)|F|² - q' d/2 - (β/2) div F = q'²|x|²/4 - q' d/2 + V_1`,
`V_1 = (β² q/2) ⟨x, F⟩ + (β²/4) |F|² - (β/2) div F`  (`mov2a_V1`).

* `mov2a_V_decomp`: the decomposition, pointwise, for every thermal equilibrium.
* `mov2a_V1_smooth`, `mov2a_V1_bound`, `mov2a_V1_memCb`: `V_1 ∈ C^∞` and for every `N` there is `C` with
  `‖D^i V_1(x)‖ ≤ C` for all `i ≤ N`, `x`; `MemCb N V_1` and `cbNorm N V_1 ≤ (N+1) C`.  The constant is built from the
  bounds `‖D^j F‖, ‖x‖ ‖D^j F‖ ≤ C_j` of `mov_force_tail_thermal` (`j ≤ N+1`) and depends only on `(d,s,q,β,N)`, since
  `ρ = thermalDensity d s q β` is determined by these parameters (`mv0_rho_eq`).
* `mov_S_eq_S0`: for Schwartz `v`, `movS d s β ρ v = S_0 v + ν V_1 v + P v` pointwise, with `S_0 = mov_S0 d β q`
  of `MovLinAux2` (the shifted oscillator).

No statement of the plan sketch was weakened; `V_1` is written with `F = movForce d s ρ` instead of `U = g * ρ_*`
(`F = ∇U`, `mov_force_tail_thermal`), so `x · ∇U`, `|∇U|²`, `ΔU = div F` are `⟨x, F⟩`, `|F|²`, `div F`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovLin

open HRS HRS.Whole HRS.MS.MovForce HRS.MS.Mov0 HRS.MS.MovC1

variable {d : ℕ}

/-- The correction `V_1 = (β² q/2) ⟨x, F⟩ + (β²/4)|F|² - (β/2) div F`, `F = movForce d s ρ = ∇(g * ρ)`. -/
def mov2a_V1 (d : ℕ) (s β q : ℝ) (ρ : Euc d → ℝ) (x : Euc d) : ℝ :=
  (β ^ 2 * q / 2) * inner ℝ x (movForce d s ρ x) + (β ^ 2 / 4) * ‖movForce d s ρ x‖ ^ 2 -
    (β / 2) * movDiv (movForce d s ρ) x

/-! ### The decomposition of `V` -/

lemma mov2a_movDiv_id (x : Euc d) : movDiv (fun y : Euc d => y) x = d := by
  unfold movDiv
  simp

lemma mov2a_movDiv_lin {F : Euc d → Euc d} {x : Euc d} (hF : DifferentiableAt ℝ F x) (a b : ℝ) :
    movDiv (fun y => a • y + b • F y) x = a * d + b * movDiv F x := by
  unfold movDiv
  have h : fderiv ℝ (fun y => a • y + b • F y) x = a • ContinuousLinearMap.id ℝ (Euc d) + b • fderiv ℝ F x :=
    ((hasFDerivAt_id x).const_smul a |>.add (hF.hasFDerivAt.const_smul b)).fderiv
  rw [h]
  simp [Finset.mul_sum, Finset.sum_add_distrib]
  ring

/-- The Euler equation in the form `∇ log ρ = -(β q) x - β F`. -/
lemma mov2a_grad_log (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β q : ℝ} (hβ : 0 < β) (hq : 0 < q)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ) (x : Euc d) :
    gradient (fun y => Real.log (ρ y)) x = (-(β * q)) • x + (-β) • movForce d s ρ x := by
  have h := mv0_thermal_force hd hs0 hsd hq hβ hρ x
  have h2 : β⁻¹ • gradient (fun y => Real.log (ρ y)) x = -(q • x + movForce d s ρ x) := by
    have h' : β⁻¹ • gradient (fun y => Real.log (ρ y)) x + (q • x + movForce d s ρ x) = 0 := by
      rw [← add_assoc]; exact h
    exact eq_neg_of_add_eq_zero_left h'
  have h3 := congrArg (fun z => β • z) h2
  simp only [smul_smul, mul_inv_cancel₀ hβ.ne', one_smul, smul_neg, smul_add] at h3
  rw [h3]
  simp only [neg_smul]
  module

/-- **Decomposition of the potential** (S6.2 TeX L4300): `V = q'² |x|²/4 - q' d/2 + V_1`, `q' = β q`. -/
theorem mov2a_V_decomp (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β q : ℝ} (hβ : 0 < β) (hq : 0 < q)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ) (x : Euc d) :
    mov2a_V ρ x = (β * q) ^ 2 * ‖x‖ ^ 2 / 4 - (β * q) * d / 2 + mov2a_V1 d s β q ρ x := by
  obtain ⟨B, -, hR, -⟩ := mv0_gapref hd hs0 hsd hq hβ hρ
  have hφ : ContDiff ℝ ∞ (fun y => Real.log (ρ y)) := hR.smooth.log fun x => (hR.pos x).ne'
  have hF : ContDiff ℝ ∞ (movForce d s ρ) := by
    have := (mov_force_tail_thermal hd hs0 hsd β q hβ hq ρ hρ)
    have e : (fun y => gradient (HRS.Whole.convFun (rieszKernel d s) ρ) y) = movForce d s ρ :=
      funext fun y => (this.1 y).symm
    rw [← e]; exact this.2.1
  have hFd : DifferentiableAt ℝ (movForce d s ρ) x := (hF.differentiable (by simp)) x
  have e1 : (fun y => gradient (fun z => Real.log (ρ z)) y) =
      fun y => (-(β * q)) • y + (-β) • movForce d s ρ y :=
    funext fun y => mov2a_grad_log hd hs0 hsd hβ hq hρ y
  have hlap : Laplacian.laplacian (fun y => Real.log (ρ y)) x =
      -(β * q) * d + (-β) * movDiv (movForce d s ρ) x := by
    rw [← mov2a_movDiv_gradient hφ, e1, mov2a_movDiv_lin hFd]
  unfold mov2a_V mov2a_V1
  rw [hlap, mov2a_grad_log hd hs0 hsd hβ hq hρ x]
  have hn : ‖(-(β * q)) • x + (-β) • movForce d s ρ x‖ ^ 2 =
      (β * q) ^ 2 * ‖x‖ ^ 2 + 2 * (β ^ 2 * q) * inner ℝ x (movForce d s ρ x) +
        β ^ 2 * ‖movForce d s ρ x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right, inner_smul_left,
      inner_smul_left, inner_smul_right, inner_smul_right, inner_smul_left, inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm x (movForce d s ρ x)]
    simp only [conj_trivial, norm_smul, norm_neg, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [hn]
  ring

/-! ### Smoothness and `C_b^N` bounds of `V_1` -/

/-- Smoothness and weighted bounds of `F`, uniform in the order `≤ M`. -/
lemma mov2a_F_uniform (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β q : ℝ} (hβ : 0 < β) (hq : 0 < q)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ) (M : ℕ) :
    ContDiff ℝ ∞ (movForce d s ρ) ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ i ≤ M, ∀ x : Euc d,
      ‖iteratedFDeriv ℝ i (movForce d s ρ) x‖ ≤ K ∧ ‖x‖ * ‖iteratedFDeriv ℝ i (movForce d s ρ) x‖ ≤ K := by
  have this := (mov_force_tail_thermal hd hs0 hsd β q hβ hq ρ hρ)
  have e : (fun y => gradient (HRS.Whole.convFun (rieszKernel d s) ρ) y) = movForce d s ρ :=
    funext fun y => (this.1 y).symm
  rw [e] at this
  refine ⟨this.2.1, ?_⟩
  choose C hC using this.2.2
  refine ⟨∑ j ∈ Finset.range (M + 1), |C j|, Finset.sum_nonneg fun j _ => abs_nonneg _, fun i hi x => ?_⟩
  have hle : |C i| ≤ ∑ j ∈ Finset.range (M + 1), |C j| :=
    Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _) (Finset.mem_range.2 (by omega))
  exact ⟨((hC i x).1.trans (le_abs_self _)).trans hle, ((hC i x).2.trans (le_abs_self _)).trans hle⟩

/-- A linear combination of three `C^N` functions with bounded derivatives up to order `N`. -/
lemma mov2a_lin3 {N : ℕ} {u1 u2 u3 : Euc d → ℝ} (h1 : ContDiff ℝ (N : WithTop ℕ∞) u1)
    (h2 : ContDiff ℝ (N : WithTop ℕ∞) u2) (h3 : ContDiff ℝ (N : WithTop ℕ∞) u3) {K1 K2 K3 : ℝ}
    (b1 : ∀ i ≤ N, ∀ x, ‖iteratedFDeriv ℝ i u1 x‖ ≤ K1) (b2 : ∀ i ≤ N, ∀ x, ‖iteratedFDeriv ℝ i u2 x‖ ≤ K2)
    (b3 : ∀ i ≤ N, ∀ x, ‖iteratedFDeriv ℝ i u3 x‖ ≤ K3) (c1 c2 c3 : ℝ) :
    ContDiff ℝ (N : WithTop ℕ∞) (fun x => c1 * u1 x + c2 * u2 x - c3 * u3 x) ∧
      ∀ i ≤ N, ∀ x, ‖iteratedFDeriv ℝ i (fun x => c1 * u1 x + c2 * u2 x - c3 * u3 x) x‖ ≤
        |c1| * K1 + |c2| * K2 + |c3| * K3 := by
  refine ⟨((contDiff_const.mul h1).add (contDiff_const.mul h2)).sub (contDiff_const.mul h3), fun i hi x => ?_⟩
  have hi' : (i : WithTop ℕ∞) ≤ N := by exact_mod_cast hi
  have g1 : ContDiffAt ℝ (i : WithTop ℕ∞) (fun x => c1 * u1 x) x :=
    ((contDiff_const.mul h1).of_le hi').contDiffAt
  have g2 : ContDiffAt ℝ (i : WithTop ℕ∞) (fun x => c2 * u2 x) x :=
    ((contDiff_const.mul h2).of_le hi').contDiffAt
  have g3 : ContDiffAt ℝ (i : WithTop ℕ∞) (fun x => c3 * u3 x) x :=
    ((contDiff_const.mul h3).of_le hi').contDiffAt
  rw [show (fun x => c1 * u1 x + c2 * u2 x - c3 * u3 x) =
      (fun x => c1 * u1 x + c2 * u2 x) - (fun x => c3 * u3 x) from rfl,
    iteratedFDeriv_sub_apply (g1.add g2) g3,
    show (fun x => c1 * u1 x + c2 * u2 x) = (fun x => c1 * u1 x) + (fun x => c2 * u2 x) from rfl,
    iteratedFDeriv_add_apply g1 g2]
  have k : ∀ (c : ℝ) (u : Euc d → ℝ) (hu : ContDiff ℝ (N : WithTop ℕ∞) u) (K : ℝ),
      (∀ i ≤ N, ∀ x, ‖iteratedFDeriv ℝ i u x‖ ≤ K) →
      ‖iteratedFDeriv ℝ i (fun x => c * u x) x‖ ≤ |c| * K := by
    intro c u hu K hK
    have := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := c) (f := u) (x := x) (i := i)
      ((hu.of_le hi').contDiffAt)
    simp only [smul_eq_mul] at this
    rw [this, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hK i hi x) (abs_nonneg _)
  calc _ ≤ ‖iteratedFDeriv ℝ i (fun x => c1 * u1 x) x + iteratedFDeriv ℝ i (fun x => c2 * u2 x) x‖ +
        ‖iteratedFDeriv ℝ i (fun x => c3 * u3 x) x‖ := norm_sub_le _ _
    _ ≤ (‖iteratedFDeriv ℝ i (fun x => c1 * u1 x) x‖ + ‖iteratedFDeriv ℝ i (fun x => c2 * u2 x) x‖) +
        ‖iteratedFDeriv ℝ i (fun x => c3 * u3 x) x‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by
      have := k c1 u1 h1 K1 b1
      have := k c2 u2 h2 K2 b2
      have := k c3 u3 h3 K3 b3
      linarith

/-- **`V_1 ∈ C_b^N` for every `N`** (explicit bounds): `V_1` is `C^∞`, and for every `N` there is `C ≥ 0` (depending
on `(d,s,q,β,N)` only) with `‖D^i V_1(x)‖ ≤ C` for `i ≤ N`, all `x`. -/
theorem mov2a_V1_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β q : ℝ} (hβ : 0 < β) (hq : 0 < q)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ) :
    ContDiff ℝ ∞ (mov2a_V1 d s β q ρ) ∧ ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ N, ∀ x : Euc d,
      ‖iteratedFDeriv ℝ i (mov2a_V1 d s β q ρ) x‖ ≤ C := by
  obtain ⟨hF, -⟩ := mov2a_F_uniform hd hs0 hsd hβ hq hρ 0
  have hinf : ∀ N : ℕ, (N : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun N => by exact_mod_cast le_top
  have key : ∀ N : ℕ, ContDiff ℝ (N : WithTop ℕ∞) (mov2a_V1 d s β q ρ) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ N,
      ∀ x : Euc d, ‖iteratedFDeriv ℝ i (mov2a_V1 d s β q ρ) x‖ ≤ C := by
    intro N
    obtain ⟨-, K, hK0, hK⟩ := mov2a_F_uniform hd hs0 hsd hβ hq hρ (N + 1)
    have hFN : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) (movForce d s ρ) := hF.of_le (hinf _)
    have hFN' : ContDiff ℝ (N : WithTop ℕ∞) (movForce d s ρ) := hF.of_le (hinf _)
    -- the three building blocks
    obtain ⟨hdivc, hdivb⟩ := movb2_div_bound hFN
    have hid : ContDiff ℝ (N : WithTop ℕ∞) (fun y : Euc d => y) := contDiff_id
    have hu1c : ContDiff ℝ (N : WithTop ℕ∞) (fun x : Euc d => inner ℝ x (movForce d s ρ x)) :=
      hid.inner ℝ hFN'
    have hu2c : ContDiff ℝ (N : WithTop ℕ∞) (fun x : Euc d => ‖movForce d s ρ x‖ ^ 2) :=
      (contDiff_norm_sq ℝ).comp hFN'
    have hu1 : ∀ i ≤ N, ∀ x : Euc d, ‖iteratedFDeriv ℝ i (fun x : Euc d => inner ℝ x (movForce d s ρ x)) x‖ ≤
        2 ^ N * ((1 + 0 + 1) * (K * 1)) := by
      have := movb2_inner_bound (f := fun y : Euc d => y) (F := movForce d s ρ) (j := N) hid hFN'
        (a := 1) (M0 := 0) (Df := 1) (Fb := K) (E := 1) zero_le_one le_rfl zero_le_one (by simpa using hK0)
        (fun x => by simp)
        (fun l hl hlN x => by
          have := mov0_clm_iter (ContinuousLinearMap.id ℝ (Euc d)) (l - 1) x
          rw [Nat.sub_add_cancel hl] at this
          exact this.trans (ContinuousLinearMap.norm_id_le))
        (fun i hi x => by simpa using (hK i (by omega) x).1)
        (fun i hi x => by simpa using (hK i (by omega) x).2)
      exact this
    have hu2 : ∀ i ≤ N, ∀ x : Euc d, ‖iteratedFDeriv ℝ i (fun x : Euc d => ‖movForce d s ρ x‖ ^ 2) x‖ ≤
        2 ^ N * ((0 + K + K) * (K * 1)) := by
      intro i hi x
      have e : (fun x : Euc d => ‖movForce d s ρ x‖ ^ 2) = fun x => inner ℝ (movForce d s ρ x) (movForce d s ρ x) := by
        funext y; rw [real_inner_self_eq_norm_sq]
      rw [e]
      have := movb2_inner_bound (f := movForce d s ρ) (F := movForce d s ρ) (j := N) hFN' hFN'
        (a := 0) (M0 := K) (Df := K) (Fb := K) (E := 1) le_rfl hK0 hK0 (by simpa using hK0)
        (fun x => by
          have := (hK 0 (by omega) x).1
          rw [norm_iteratedFDeriv_zero] at this
          simpa using this)
        (fun l hl hlN x => (hK l (by omega) x).1)
        (fun i hi x => by simpa using (hK i (by omega) x).1)
        (fun i hi x => by simpa using (hK i (by omega) x).2)
      exact this i hi x
    have hu3 : ∀ i ≤ N, ∀ x : Euc d, ‖iteratedFDeriv ℝ i (fun x : Euc d => movDiv (movForce d s ρ) x) x‖ ≤
        ‖movb2_divL d‖ * K := fun i hi x =>
      (hdivb i hi x).trans (mul_le_mul_of_nonneg_left (hK (i + 1) (by omega) x).1
        (ContinuousLinearMap.opNorm_nonneg _))
    obtain ⟨hc, hb⟩ := mov2a_lin3 hu1c hu2c hdivc hu1 hu2 hu3 (β ^ 2 * q / 2) (β ^ 2 / 4) (β / 2)
    exact ⟨hc, _, by positivity, hb⟩
  refine ⟨?_, fun N => (key N).2⟩
  rw [contDiff_infty]
  exact fun N => (key N).1

theorem mov2a_V1_smooth (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β q : ℝ} (hβ : 0 < β) (hq : 0 < q)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ) : ContDiff ℝ ∞ (mov2a_V1 d s β q ρ) :=
  (mov2a_V1_bound hd hs0 hsd hβ hq hρ).1

/-- **`V_1 ∈ C_b^N`** in the sense of `MemCb`, with the explicit bound `cbNorm N V_1 ≤ (N+1) C`. -/
theorem mov2a_V1_memCb (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β q : ℝ} (hβ : 0 < β) (hq : 0 < q)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ) (N : ℕ) :
    MemCb N (mov2a_V1 d s β q ρ) ∧ ∃ C : ℝ, 0 ≤ C ∧ cbNorm N (mov2a_V1 d s β q ρ) ≤ (N + 1) * C := by
  obtain ⟨hsm, hb⟩ := mov2a_V1_bound hd hs0 hsd hβ hq hρ
  obtain ⟨C, hC0, hC⟩ := hb N
  refine ⟨⟨hsm.of_le (by exact_mod_cast le_top), fun i hi => ⟨C, ?_⟩⟩, C, hC0, ?_⟩
  · rintro _ ⟨x, rfl⟩; exact hC i hi x
  · unfold cbNorm
    calc ∑ i ∈ Finset.range (N + 1), ⨆ z : Euc d, ‖iteratedFDeriv ℝ i (mov2a_V1 d s β q ρ) z‖
        ≤ ∑ _i ∈ Finset.range (N + 1), C :=
          Finset.sum_le_sum fun i hi => ciSup_le fun x => hC i (by have := Finset.mem_range.1 hi; omega) x
      _ = (N + 1) * C := by simp

/-! ### `S = S_0 + ν V_1 + P` on Schwartz functions -/

/-- **MOV-2a, conclusion.**  For a thermal equilibrium `ρ` and Schwartz `v`:
`movS d s β ρ v = S_0 v + β⁻¹ V_1 v + movP d s ρ v` pointwise, with `S_0 = mov_S0 d β q`. -/
theorem mov_S_eq_S0 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β) (hq : 0 < q)
    (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ) (v : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    movS d s β ρ v x =
      mov_S0 d β q v x + β⁻¹ * mov2a_V1 d s β q ρ x * v x + movP d s ρ v x := by
  rw [mov_S_ground_state hd hs0 hsd β q hβ hq ρ hρ v x, mov2a_V_decomp hd hs0 hsd hβ hq hρ x]
  unfold mov_S0
  ring

end HRS.MS.MovLin

end
