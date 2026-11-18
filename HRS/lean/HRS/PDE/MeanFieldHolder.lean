import HRS.PDE.MeanFieldThermalReg
import HRS.Kernel.GradOp

/-!
# Hölder classes on the torus (package MF-01, packet P4b)

`HC m γ f` : `f ∈ C^{m,γ}(𝕋^d)`: `f` is `C¹`, its partial derivatives are in `HC (m-1) γ`, and for
`m = 0`, `f` is continuous with `|f x - f y| ≤ M ‖x - y‖^γ` (torus norm; for `γ = 0` this is just
continuity).  The class is stable under sums, products, and `exp` (`HC.exp`), and every `C^{m+1}`
function lies in `HC m γ` for `0 ≤ γ ≤ 1`.  This is the scale used by the Schauder bootstrap of
`MeanFieldSchauder.lean` / `MeanFieldThermalRegB.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.PDE.MFHolder

variable {d : ℕ}

theorem norm_torus_le_half (z : Torus d) : ‖z‖ ≤ 1 / 2 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
  have := AddCircle.norm_le_half_period (1 : ℝ) (x := z i) one_ne_zero
  simpa using this

theorem norm_torus_le_one (z : Torus d) : ‖z‖ ≤ 1 := (norm_torus_le_half z).trans (by norm_num)

theorem rpow_le_rpow_of_exponent_ge' {r a b : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hb : 0 ≤ b)
    (hab : b ≤ a) : r ^ a ≤ r ^ b :=
  Real.rpow_le_rpow_of_exponent_ge' hr0 hr1 hb hab

/-- The Hölder class `C^{0,γ}`: continuity plus a Hölder bound with respect to the torus norm. -/
def Hol0 (γ : ℝ) (f : Torus d → ℝ) : Prop :=
  Continuous f ∧ ∃ M : ℝ, ∀ x y, |f x - f y| ≤ M * ‖x - y‖ ^ γ

/-- The Hölder class `C^{m,γ}` on the torus. -/
def HC : ℕ → ℝ → (Torus d → ℝ) → Prop
  | 0, γ, f => Hol0 γ f
  | m + 1, γ, f => Torus.IsCk 1 f ∧ ∀ j : Fin d, HC m γ (Torus.partialDeriv j f)

theorem Hol0.bdd {γ : ℝ} {f : Torus d → ℝ} (h : Hol0 γ f) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |f x| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn h.1.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
  have := hB x (Set.mem_univ x)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem Hol0.mono {γ γ' : ℝ} {f : Torus d → ℝ} (h : Hol0 γ f) (h0 : 0 ≤ γ') (hγ : γ' ≤ γ) :
    Hol0 γ' f := by
  obtain ⟨hc, M, hM⟩ := h
  refine ⟨hc, |M|, fun x y => ?_⟩
  have h1 : ‖x - y‖ ^ γ ≤ ‖x - y‖ ^ γ' :=
    rpow_le_rpow_of_exponent_ge' (norm_nonneg _) (norm_torus_le_one _) h0 hγ
  calc |f x - f y| ≤ M * ‖x - y‖ ^ γ := hM x y
    _ ≤ |M| * ‖x - y‖ ^ γ := mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity)
    _ ≤ |M| * ‖x - y‖ ^ γ' := mul_le_mul_of_nonneg_left h1 (abs_nonneg M)

theorem Hol0.add {γ : ℝ} {f g : Torus d → ℝ} (hf : Hol0 γ f) (hg : Hol0 γ g) :
    Hol0 γ (fun x => f x + g x) := by
  obtain ⟨hfc, M, hM⟩ := hf
  obtain ⟨hgc, N, hN⟩ := hg
  refine ⟨hfc.add hgc, M + N, fun x y => ?_⟩
  have h1 := hM x y
  have h2 := hN x y
  have e : f x + g x - (f y + g y) = (f x - f y) + (g x - g y) := by ring
  rw [e, add_mul]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem Hol0.const_mul {γ : ℝ} {f : Torus d → ℝ} (hf : Hol0 γ f) (c : ℝ) :
    Hol0 γ (fun x => c * f x) := by
  obtain ⟨hfc, M, hM⟩ := hf
  refine ⟨continuous_const.mul hfc, |c| * M, fun x y => ?_⟩
  have h1 := hM x y
  have e : c * f x - c * f y = c * (f x - f y) := by ring
  rw [e, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg c)

theorem Hol0.const (γ c : ℝ) : Hol0 γ (fun _ : Torus d => c) :=
  ⟨continuous_const, 0, fun x y => by simp⟩

theorem Hol0.mul {γ : ℝ} {f g : Torus d → ℝ} (hf : Hol0 γ f) (hg : Hol0 γ g) :
    Hol0 γ (fun x => f x * g x) := by
  obtain ⟨Bf, hBf0, hBf⟩ := hf.bdd
  obtain ⟨Bg, hBg0, hBg⟩ := hg.bdd
  obtain ⟨hfc, M, hM⟩ := hf
  obtain ⟨hgc, N, hN⟩ := hg
  refine ⟨hfc.mul hgc, Bf * N + Bg * M, fun x y => ?_⟩
  have e : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
  rw [e]
  have hr : 0 ≤ ‖x - y‖ ^ γ := by positivity
  calc |f x * (g x - g y) + g y * (f x - f y)|
      ≤ |f x * (g x - g y)| + |g y * (f x - f y)| := abs_add_le _ _
    _ = |f x| * |g x - g y| + |g y| * |f x - f y| := by rw [abs_mul, abs_mul]
    _ ≤ Bf * (N * ‖x - y‖ ^ γ) + Bg * (M * ‖x - y‖ ^ γ) := by
        gcongr
        · exact hBf x
        · exact hN x y
        · exact hBg y
        · exact hM x y
    _ = (Bf * N + Bg * M) * ‖x - y‖ ^ γ := by ring

theorem Hol0.exp {γ : ℝ} {f : Torus d → ℝ} (hf : Hol0 γ f) :
    Hol0 γ (fun x => Real.exp (f x)) := by
  obtain ⟨B, hB0, hB⟩ := hf.bdd
  obtain ⟨hfc, M, hM⟩ := hf
  refine ⟨Real.continuous_exp.comp hfc, Real.exp B * M, fun x y => ?_⟩
  have h1 := MFThermalReg.abs_exp_sub_le (M := B) (le_trans (le_abs_self _) (hB x))
    (le_trans (le_abs_self _) (hB y))
  calc |Real.exp (f x) - Real.exp (f y)| ≤ Real.exp B * |f x - f y| := h1
    _ ≤ Real.exp B * (M * ‖x - y‖ ^ γ) := mul_le_mul_of_nonneg_left (hM x y) (Real.exp_pos B).le
    _ = _ := by ring

/-- A `C¹` function is Lipschitz for the torus norm. -/
theorem lipschitz_norm_of_isCk {f : Torus d → ℝ} (hf : Torus.IsCk 1 f) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, |f x - f y| ≤ L * ‖x - y‖ := by
  obtain ⟨L, hL0, hL⟩ := KernelGrad.isLipschitz_of_isCk hf
  refine ⟨L * d, by positivity, fun x y => ?_⟩
  have h1 := hL x y
  have h2 := KernelGrad.tdist_le_mul_norm (x - y)
  rw [KernelGrad.tdist_eq_sub_zero] at h1
  calc |f x - f y| ≤ L * KernelGrad.tdist (x - y) 0 := h1
    _ ≤ L * (d * ‖x - y‖) := mul_le_mul_of_nonneg_left h2 hL0
    _ = L * d * ‖x - y‖ := by ring

theorem hol0_of_isCk {f : Torus d → ℝ} (hf : Torus.IsCk 1 f) {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    Hol0 γ f := by
  obtain ⟨L, hL0, hL⟩ := lipschitz_norm_of_isCk hf
  refine ⟨continuous_of_isCk hf, L, fun x y => ?_⟩
  have h2 : ‖x - y‖ ≤ ‖x - y‖ ^ γ := by
    have := rpow_le_rpow_of_exponent_ge' (norm_nonneg (x - y)) (norm_torus_le_one (x - y)) h0 h1
    simpa using this
  exact (hL x y).trans (mul_le_mul_of_nonneg_left h2 hL0)


/-! ### Calculus of partial derivatives -/

theorem isCk_one_add {f g : Torus d → ℝ} (hf : Torus.IsCk 1 f) (hg : Torus.IsCk 1 g) :
    Torus.IsCk 1 (fun x => f x + g x) := hf.add hg

theorem isCk_one_const_mul {f : Torus d → ℝ} (hf : Torus.IsCk 1 f) (c : ℝ) :
    Torus.IsCk 1 (fun x => c * f x) := contDiff_const.mul hf

theorem isCk_one_mul {f g : Torus d → ℝ} (hf : Torus.IsCk 1 f) (hg : Torus.IsCk 1 g) :
    Torus.IsCk 1 (fun x => f x * g x) := hf.mul hg

theorem isCk_one_exp {f : Torus d → ℝ} (hf : Torus.IsCk 1 f) :
    Torus.IsCk 1 (fun x => Real.exp (f x)) := Real.contDiff_exp.comp hf

theorem isCk_one_const (c : ℝ) : Torus.IsCk 1 (fun _ : Torus d => c) := contDiff_const

theorem partialDeriv_add (j : Fin d) {f g : Torus d → ℝ} (hf : Torus.IsCk 1 f)
    (hg : Torus.IsCk 1 g) (x : Torus d) :
    Torus.partialDeriv j (fun y => f y + g y) x =
      Torus.partialDeriv j f x + Torus.partialDeriv j g x := by
  unfold Torus.partialDeriv
  have e : Torus.lift (fun y => f y + g y) = fun y => Torus.lift f y + Torus.lift g y := rfl
  rw [e, fderiv_fun_add ((hf.differentiable one_ne_zero) _) ((hg.differentiable one_ne_zero) _)]
  rfl

theorem partialDeriv_const_mul (j : Fin d) {f : Torus d → ℝ} (hf : Torus.IsCk 1 f) (c : ℝ)
    (x : Torus d) :
    Torus.partialDeriv j (fun y => c * f y) x = c * Torus.partialDeriv j f x := by
  unfold Torus.partialDeriv
  have e : Torus.lift (fun y => c * f y) = fun y => c * Torus.lift f y := rfl
  rw [e, fderiv_const_mul ((hf.differentiable one_ne_zero) _)]
  simp

theorem partialDeriv_exp (j : Fin d) {f : Torus d → ℝ} (hf : Torus.IsCk 1 f) (x : Torus d) :
    Torus.partialDeriv j (fun y => Real.exp (f y)) x =
      Real.exp (f x) * Torus.partialDeriv j f x := by
  unfold Torus.partialDeriv
  have e : Torus.lift (fun y => Real.exp (f y)) = fun y => Real.exp (Torus.lift f y) := rfl
  rw [e, fderiv_exp ((hf.differentiable one_ne_zero) _)]
  simp [Torus.lift, Torus.mk_rep]

/-! ### Stability of `HC` -/

theorem HC.hol0 : ∀ (m : ℕ) {γ : ℝ} {f : Torus d → ℝ}, 0 ≤ γ → γ ≤ 1 → HC m γ f → Hol0 γ f
  | 0, _, _, _, _, h => h
  | _ + 1, _, _, h0, h1, h => hol0_of_isCk h.1 h0 h1

theorem HC.isCk_one {m : ℕ} {γ : ℝ} {f : Torus d → ℝ} (h : HC (m + 1) γ f) : Torus.IsCk 1 f := h.1

theorem HC.continuous : ∀ (m : ℕ) {γ : ℝ} {f : Torus d → ℝ}, HC m γ f → Continuous f
  | 0, _, _, h => h.1
  | _ + 1, _, _, h => continuous_of_isCk h.1

theorem HC.succ_le : ∀ (m : ℕ) {γ : ℝ} {f : Torus d → ℝ}, 0 ≤ γ → γ ≤ 1 → HC (m + 1) γ f → HC m γ f
  | 0, _, _, h0, h1, h => hol0_of_isCk h.1 h0 h1
  | m + 1, _, _, h0, h1, h => ⟨h.1, fun j => HC.succ_le m h0 h1 (h.2 j)⟩

theorem HC.le : ∀ (m n : ℕ) {γ : ℝ} {f : Torus d → ℝ}, 0 ≤ γ → γ ≤ 1 → m ≤ n → HC n γ f →
    HC m γ f
  | m, n, _, _, h0, h1, hmn, h => by
    induction n, hmn using Nat.le_induction with
    | base => exact h
    | succ n hmn ih => exact ih (HC.succ_le n h0 h1 h)

theorem HC.mono_exp : ∀ (m : ℕ) {γ γ' : ℝ} {f : Torus d → ℝ}, 0 ≤ γ' → γ' ≤ γ → HC m γ f →
    HC m γ' f
  | 0, _, _, _, h0, hγ, h => Hol0.mono h h0 hγ
  | m + 1, _, _, _, h0, hγ, h => ⟨h.1, fun j => HC.mono_exp m h0 hγ (h.2 j)⟩

theorem HC.add : ∀ (m : ℕ) {γ : ℝ} {f g : Torus d → ℝ}, 0 ≤ γ → γ ≤ 1 → HC m γ f → HC m γ g →
    HC m γ (fun x => f x + g x)
  | 0, _, _, _, _, _, hf, hg => Hol0.add hf hg
  | m + 1, γ, f, g, h0, h1, hf, hg => by
    refine ⟨isCk_one_add hf.1 hg.1, fun j => ?_⟩
    have e : Torus.partialDeriv j (fun x => f x + g x) =
        fun x => Torus.partialDeriv j f x + Torus.partialDeriv j g x :=
      funext fun x => partialDeriv_add j hf.1 hg.1 x
    rw [e]
    exact HC.add m h0 h1 (hf.2 j) (hg.2 j)

theorem HC.const_mul : ∀ (m : ℕ) {γ : ℝ} {f : Torus d → ℝ}, HC m γ f → ∀ c : ℝ,
    HC m γ (fun x => c * f x)
  | 0, _, _, hf, c => Hol0.const_mul hf c
  | m + 1, γ, f, hf, c => by
    refine ⟨isCk_one_const_mul hf.1 c, fun j => ?_⟩
    have e : Torus.partialDeriv j (fun x => c * f x) =
        fun x => c * Torus.partialDeriv j f x :=
      funext fun x => partialDeriv_const_mul j hf.1 c x
    rw [e]
    exact HC.const_mul m (hf.2 j) c

theorem HC.const : ∀ (m : ℕ) (γ c : ℝ), HC m γ (fun _ : Torus d => c)
  | 0, γ, c => Hol0.const γ c
  | m + 1, γ, c => by
    refine ⟨isCk_one_const c, fun j => ?_⟩
    have e : Torus.partialDeriv j (fun _ : Torus d => c) = fun _ => 0 :=
      funext fun x => MFAux.partialDeriv_const j c x
    rw [e]
    exact HC.const m γ 0

theorem HC.mul : ∀ (m : ℕ) {γ : ℝ} {f g : Torus d → ℝ}, 0 ≤ γ → γ ≤ 1 → HC m γ f → HC m γ g →
    HC m γ (fun x => f x * g x)
  | 0, _, _, _, _, _, hf, hg => Hol0.mul hf hg
  | m + 1, γ, f, g, h0, h1, hf, hg => by
    refine ⟨isCk_one_mul hf.1 hg.1, fun j => ?_⟩
    have e : Torus.partialDeriv j (fun x => f x * g x) =
        fun x => Torus.partialDeriv j f x * g x + f x * Torus.partialDeriv j g x :=
      funext fun x => MFAux.partialDeriv_mul j f g hf.1 hg.1 x
    rw [e]
    exact HC.add m h0 h1 (HC.mul m h0 h1 (hf.2 j) (HC.succ_le m h0 h1 hg))
      (HC.mul m h0 h1 (HC.succ_le m h0 h1 hf) (hg.2 j))

theorem HC.exp : ∀ (m : ℕ) {γ : ℝ} {f : Torus d → ℝ}, 0 ≤ γ → γ ≤ 1 → HC m γ f →
    HC m γ (fun x => Real.exp (f x))
  | 0, _, _, _, _, hf => Hol0.exp hf
  | m + 1, γ, f, h0, h1, hf => by
    refine ⟨isCk_one_exp hf.1, fun j => ?_⟩
    have e : Torus.partialDeriv j (fun x => Real.exp (f x)) =
        fun x => Real.exp (f x) * Torus.partialDeriv j f x :=
      funext fun x => partialDeriv_exp j hf.1 x
    rw [e]
    exact HC.mul m h0 h1 (HC.exp m h0 h1 (HC.succ_le m h0 h1 hf)) (hf.2 j)


/-! ### Relation with `Torus.IsCk` -/

theorem euc_eq_sum (y : Euc d) : y = ∑ j, y j • EuclideanSpace.single j (1 : ℝ) := by
  have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr y
  simpa using this.symm

theorem isCk_succ_of_partials {m : ℕ} {f : Torus d → ℝ} (h1 : Torus.IsCk 1 f)
    (h : ∀ j : Fin d, Torus.IsCk (m : WithTop ℕ∞) (Torus.partialDeriv j f)) :
    Torus.IsCk ((m + 1 : ℕ) : WithTop ℕ∞) f := by
  unfold Torus.IsCk at *
  have e : ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 := by push_cast; rfl
  rw [e, contDiff_succ_iff_fderiv]
  refine ⟨h1.differentiable one_ne_zero, fun h => by simp at h, ?_⟩
  rw [contDiff_clm_apply_iff]
  intro y
  have hy : ∀ x, fderiv ℝ (Torus.lift f) x y =
      ∑ j, y j * Torus.lift (Torus.partialDeriv j f) x := by
    intro x
    conv_lhs => rw [euc_eq_sum y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
    congr 1
    exact (partialDeriv_mk j f h1 x).symm
  have : (fun x => fderiv ℝ (Torus.lift f) x y) =
      fun x => ∑ j, y j * Torus.lift (Torus.partialDeriv j f) x := funext hy
  rw [this]
  exact ContDiff.sum fun j _ => contDiff_const.mul (h j)

theorem HC.isCk : ∀ (m : ℕ) {γ : ℝ} {f : Torus d → ℝ}, HC m γ f → Torus.IsCk (m : WithTop ℕ∞) f
  | 0, _, _, h => by
    have hc : Continuous (Torus.lift _) := h.1.comp Torus.continuous_mk
    exact contDiff_zero.2 (by simpa using hc)
  | m + 1, _, _, h => isCk_succ_of_partials h.1 fun j => HC.isCk m (h.2 j)

theorem HC.of_isCk : ∀ (m : ℕ) {f : Torus d → ℝ}, Torus.IsCk ((m + 1 : ℕ) : WithTop ℕ∞) f →
    ∀ {γ : ℝ}, 0 ≤ γ → γ ≤ 1 → HC m γ f
  | 0, _, hf, _, h0, h1 => hol0_of_isCk (by simpa using hf) h0 h1
  | m + 1, _, hf, _, h0, h1 =>
    ⟨hf.of_le (by exact_mod_cast Nat.le_add_left 1 (m + 1)),
      fun j => HC.of_isCk m (ProdAux.isCk_partialDeriv hf j) h0 h1⟩

end HRS.PDE.MFHolder
