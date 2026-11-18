import HRS.MS.ThCorrUDAux2
import HRS.MS.EucRegH

/-!
# TC-U2 (part 3): the quantitative Hölder classes `qC`

Namespace `HRS.MS.TcU`; helper lemmas carry the prefix `tcu2_` (the class and its closure lemmas `qC_*`).

The merged hard-regime bootstrap (`EucRegH.lean`) works in the recursive class `regh_C d θ k E f`
(`f ∈ C^k`, bounded together with its derivatives, `D^k f` globally `θ`-Hölder), where all constants are
existentially hidden.  The class `qC d θ k E f L` records ONE constant `L`: `‖D^j f‖ ≤ L` for `j ≤ k` and `D^k f` is
`θ`-Hölder with constant `L`.  The closure lemmas are stated in the order
`∀ order and input constants, ∃ output constant, ∀ functions`:

* `qC_mono_L`, `qC_mono_k` (`k + 1 → k`, constant `3 L`), `qC_add`, `qC_smul`;
* `qC_prod` (bilinear maps), `qC_exp`;
* `qC_contDiff` (class → smoothness and iterated-derivative bounds), `qC_of_bdd` (the converse);
* `tcu2_gauss_q`: the Gaussian profile `exp(-β a ‖x‖²/2) / Z` is in `qC` with one constant for
  `a ∈ [am, ap]`, `β ∈ [βm, βp]`, `Z ≥ z₀`.
-/

open MeasureTheory Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace HRS.MS.TcU

open HRS HRS.Whole HRS.MS.LogReg HRS.MS.Thm

variable {d : ℕ}

/-- The quantitative class `qC d θ k E f L`. -/
def qC (d : ℕ) (θ : ℝ) : ℕ → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E], (Euc d → E) → ℝ → Prop
  | 0, E, _, _, f, L => AEStronglyMeasurable f volume ∧ (∀ x, ‖f x‖ ≤ L) ∧
      ∀ x h, ‖f (x + h) - f x‖ ≤ L * ‖h‖ ^ θ
  | k + 1, E, _, _, f, L => Differentiable ℝ f ∧ (∀ x, ‖f x‖ ≤ L) ∧
      qC d θ k (Euc d →L[ℝ] E) (fderiv ℝ f) L

section Cls

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma qC_nonneg {θ : ℝ} {k : ℕ} {f : Euc d → E} {L : ℝ} (hf : qC d θ k E f L) : 0 ≤ L := by
  cases k with
  | zero => obtain ⟨-, hB, -⟩ := hf; exact le_trans (norm_nonneg _) (hB 0)
  | succ k => obtain ⟨-, hB, -⟩ := hf; exact le_trans (norm_nonneg _) (hB 0)

lemma qC_bound {θ : ℝ} {k : ℕ} {f : Euc d → E} {L : ℝ} (hf : qC d θ k E f L) (x : Euc d) :
    ‖f x‖ ≤ L := by
  cases k with
  | zero => exact hf.2.1 x
  | succ k => exact hf.2.1 x

lemma qC_cont {θ : ℝ} (hθ : 0 < θ) {k : ℕ} {f : Euc d → E} {L : ℝ} (hf : qC d θ k E f L) :
    Continuous f := by
  cases k with
  | zero => obtain ⟨-, -, hK⟩ := hf; exact regh_hol_cont hθ hK
  | succ k => exact hf.1.continuous

lemma qC_mono_L {θ : ℝ} :
    ∀ (k : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Euc d → E} {L L' : ℝ},
      L ≤ L' → qC d θ k E f L → qC d θ k E f L' := by
  intro k
  induction k with
  | zero =>
    intro E _ _ f L L' hL hf
    obtain ⟨hm, hB, hH⟩ := hf
    refine ⟨hm, fun x => (hB x).trans hL, fun x h => (hH x h).trans ?_⟩
    exact mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (norm_nonneg h) _)
  | succ k ih =>
    intro E _ _ f L L' hL hf
    obtain ⟨hd, hB, hf'⟩ := hf
    exact ⟨hd, fun x => (hB x).trans hL, ih hL hf'⟩

/-- Lowering the differentiability order costs a factor `3`. -/
lemma qC_mono_k {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∀ (k : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Euc d → E} {L : ℝ},
      qC d θ (k + 1) E f L → qC d θ k E f (3 * L) := by
  intro k
  induction k with
  | zero =>
    intro E _ _ f L hf
    obtain ⟨hd, hB, -, hB', -⟩ := hf
    have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hB 0)
    have hL : ∀ x h, ‖f (x + h) - f x‖ ≤ max L 0 * ‖h‖ ^ (1 : ℝ) := fun x h => by
      rw [Real.rpow_one]
      have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := f) (C := max L 0)
        (s := Set.univ) (x := x) (y := x + h) (fun y _ => hd y)
        (fun y _ => (hB' y).trans (le_max_left _ _)) convex_univ (Set.mem_univ _) (Set.mem_univ _)
      simpa using this
    have h2 := regh_hol_mono hθ1 (le_max_right _ _) hL0 hB hL hθ0
    refine ⟨hd.continuous.aestronglyMeasurable, fun x => (hB x).trans (by linarith), fun x h => ?_⟩
    refine (h2 x h).trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg h) _))
    rw [max_eq_left hL0]; linarith
  | succ k ih =>
    intro E _ _ f L hf
    obtain ⟨hd, hB, hf'⟩ := hf
    have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hB 0)
    exact ⟨hd, fun x => (hB x).trans (by linarith), ih hf'⟩

lemma qC_add {θ : ℝ} :
    ∀ (k : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : Euc d → E} {L1 L2 : ℝ},
      qC d θ k E f L1 → qC d θ k E g L2 → qC d θ k E (fun x => f x + g x) (L1 + L2) := by
  intro k
  induction k with
  | zero =>
    intro E _ _ f g L1 L2 hf hg
    obtain ⟨hm1, hB1, hH1⟩ := hf
    obtain ⟨hm2, hB2, hH2⟩ := hg
    refine ⟨hm1.add hm2, fun x => (norm_add_le _ _).trans (add_le_add (hB1 x) (hB2 x)), fun x h => ?_⟩
    have e : f (x + h) + g (x + h) - (f x + g x) = (f (x + h) - f x) + (g (x + h) - g x) := by abel
    rw [e, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hH1 x h) (hH2 x h))
  | succ k ih =>
    intro E _ _ f g L1 L2 hf hg
    obtain ⟨hd1, hB1, hf'⟩ := hf
    obtain ⟨hd2, hB2, hg'⟩ := hg
    refine ⟨hd1.add hd2, fun x => (norm_add_le _ _).trans (add_le_add (hB1 x) (hB2 x)), ?_⟩
    have e : fderiv ℝ (fun x => f x + g x) = fun x => fderiv ℝ f x + fderiv ℝ g x :=
      funext fun x => fderiv_add (hd1 x) (hd2 x)
    rw [e]
    exact ih hf' hg'

lemma qC_smul {θ : ℝ} (c : ℝ) :
    ∀ (k : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Euc d → E} {L : ℝ},
      qC d θ k E f L → qC d θ k E (fun x => c • f x) (|c| * L) := by
  intro k
  induction k with
  | zero =>
    intro E _ _ f L hf
    obtain ⟨hm1, hB1, hH1⟩ := hf
    refine ⟨hm1.const_smul c, fun x => ?_, fun x h => ?_⟩
    · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hB1 x) (abs_nonneg c)
    · rw [← smul_sub, norm_smul, Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hH1 x h) (abs_nonneg c)
  | succ k ih =>
    intro E _ _ f L hf
    obtain ⟨hd1, hB1, hf'⟩ := hf
    refine ⟨hd1.const_smul c, fun x => ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hB1 x) (abs_nonneg c)
    · have e : fderiv ℝ (fun x => c • f x) = fun x => c • fderiv ℝ f x :=
        funext fun x => fderiv_const_smul (hd1 x) c
      rw [e]
      exact ih hf'

/-- Products: the output constant depends only on the order, the input constants and a bound for `‖B‖`. -/
lemma qC_prod {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∀ (k : ℕ) (nB L1 L2 : ℝ), ∃ L : ℝ, ∀ {E1 E2 E3 : Type} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
      [NormedAddCommGroup E2] [NormedSpace ℝ E2] [NormedAddCommGroup E3] [NormedSpace ℝ E3]
      (B : E1 →L[ℝ] E2 →L[ℝ] E3), ‖B‖ ≤ nB → ∀ {f : Euc d → E1} {g : Euc d → E2},
      qC d θ k E1 f L1 → qC d θ k E2 g L2 → qC d θ k E3 (fun x => B (f x) (g x)) L := by
  intro k
  induction k with
  | zero =>
    intro nB L1 L2
    refine ⟨2 * nB * L1 * L2, ?_⟩
    intro E1 E2 E3 _ _ _ _ _ _ B hBn f g hf hg
    obtain ⟨hm1, hB1, hH1⟩ := hf
    obtain ⟨hm2, hB2, hH2⟩ := hg
    have hB1' : 0 ≤ L1 := le_trans (norm_nonneg _) (hB1 0)
    have hB2' : 0 ≤ L2 := le_trans (norm_nonneg _) (hB2 0)
    have hnB : 0 ≤ nB := le_trans (norm_nonneg B) hBn
    have hbb : ‖B‖ * L1 * L2 ≤ nB * L1 * L2 := by gcongr
    refine ⟨B.aestronglyMeasurable_comp₂ hm1 hm2, fun x => ?_, fun x h => ?_⟩
    · refine (B.le_opNorm₂ _ _).trans ?_
      have : ‖B‖ * ‖f x‖ * ‖g x‖ ≤ ‖B‖ * L1 * L2 := by gcongr; exacts [hB1 x, hB2 x]
      nlinarith [mul_nonneg (mul_nonneg hnB hB1') hB2']
    · have e : B (f (x + h)) (g (x + h)) - B (f x) (g x) =
          B (f (x + h) - f x) (g (x + h)) + B (f x) (g (x + h) - g x) := by
        simp only [map_sub, ContinuousLinearMap.sub_apply]; abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      have hp : 0 ≤ ‖h‖ ^ θ := Real.rpow_nonneg (norm_nonneg h) _
      have h1 : ‖B (f (x + h) - f x) (g (x + h))‖ ≤ ‖B‖ * (L1 * ‖h‖ ^ θ) * L2 :=
        (B.le_opNorm₂ _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left (hH1 x h) (norm_nonneg B))
          (hB2 _) (norm_nonneg _) (by positivity))
      have h2 : ‖B (f x) (g (x + h) - g x)‖ ≤ ‖B‖ * L1 * (L2 * ‖h‖ ^ θ) :=
        (B.le_opNorm₂ _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left (hB1 x) (norm_nonneg B))
          (hH2 x h) (norm_nonneg _) (by positivity))
      have h3 : ‖B‖ * (L1 * ‖h‖ ^ θ) * L2 + ‖B‖ * L1 * (L2 * ‖h‖ ^ θ) =
          (2 * ‖B‖ * L1 * L2) * ‖h‖ ^ θ := by ring
      have h4 : 2 * ‖B‖ * L1 * L2 ≤ 2 * nB * L1 * L2 := by gcongr
      calc _ ≤ _ := add_le_add h1 h2
        _ = (2 * ‖B‖ * L1 * L2) * ‖h‖ ^ θ := h3
        _ ≤ _ := mul_le_mul_of_nonneg_right h4 hp
  | succ k ih =>
    intro nB L1 L2
    obtain ⟨La, hLa⟩ := ih nB (3 * L1) L2
    obtain ⟨Lb, hLb⟩ := ih nB L1 (3 * L2)
    refine ⟨max (nB * L1 * L2) (La + Lb), ?_⟩
    intro E1 E2 E3 _ _ _ _ _ _ B hBn f g hf hg
    have hf0 := qC_mono_k hθ0 hθ1 k hf
    have hg0 := qC_mono_k hθ0 hθ1 k hg
    obtain ⟨hd1, hB1, hf'⟩ := hf
    obtain ⟨hd2, hB2, hg'⟩ := hg
    have hB1' : 0 ≤ L1 := le_trans (norm_nonneg _) (hB1 0)
    have hB2' : 0 ≤ L2 := le_trans (norm_nonneg _) (hB2 0)
    have hnB : 0 ≤ nB := le_trans (norm_nonneg B) hBn
    have hder : ∀ x, HasFDerivAt (fun y => B (f y) (g y))
        (B.precompR (Euc d) (f x) (fderiv ℝ g x) + B.precompL (Euc d) (fderiv ℝ f x) (g x)) x :=
      fun x => B.hasFDerivAt_of_bilinear (hd1 x).hasFDerivAt (hd2 x).hasFDerivAt
    refine ⟨fun x => (hder x).differentiableAt, fun x => ?_, ?_⟩
    · refine (B.le_opNorm₂ _ _).trans ?_
      have : ‖B‖ * ‖f x‖ * ‖g x‖ ≤ nB * L1 * L2 := by
        have : ‖B‖ * ‖f x‖ * ‖g x‖ ≤ ‖B‖ * L1 * L2 := by gcongr; exacts [hB1 x, hB2 x]
        have h2 : ‖B‖ * L1 * L2 ≤ nB * L1 * L2 := by gcongr
        linarith
      exact this.trans (le_max_left _ _)
    · have e : fderiv ℝ (fun y => B (f y) (g y)) = fun x =>
          B.precompR (Euc d) (f x) (fderiv ℝ g x) + B.precompL (Euc d) (fderiv ℝ f x) (g x) :=
        funext fun x => (hder x).fderiv
      rw [e]
      refine qC_mono_L k (le_max_right _ _) (qC_add k ?_ ?_)
      · exact hLa (B.precompR (Euc d)) ((B.norm_precompR_le (Euc d)).trans hBn) hf0 hg'
      · exact hLb (B.precompL (Euc d)) ((B.norm_precompL_le (Euc d)).trans hBn) hf' hg0

lemma tcu2_exp_lip {a b B : ℝ} (ha : a ≤ B) (hb : b ≤ B) :
    |Real.exp a - Real.exp b| ≤ Real.exp B * |a - b| := regh_exp_lip ha hb

/-- `exp ∘ f`. -/
lemma qC_exp {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∀ (k : ℕ) (L : ℝ), ∃ L' : ℝ, ∀ {f : Euc d → ℝ}, qC d θ k ℝ f L →
      qC d θ k ℝ (fun x => Real.exp (f x)) L' := by
  intro k
  induction k with
  | zero =>
    intro L
    refine ⟨Real.exp L * (|L| + 1), ?_⟩
    intro f hf
    obtain ⟨hm, hB, hH⟩ := hf
    have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hB 0)
    have hb : ∀ y, f y ≤ L := fun y => (le_abs_self _).trans (by simpa using hB y)
    have hE : 1 ≤ |L| + 1 := by linarith [abs_nonneg L]
    have hE0 := (Real.exp_pos L).le
    refine ⟨Real.continuous_exp.comp_aestronglyMeasurable hm, fun x => ?_, fun x h => ?_⟩
    · rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact (Real.exp_le_exp.2 (hb x)).trans (by nlinarith)
    · rw [Real.norm_eq_abs]
      calc _ ≤ Real.exp L * |f (x + h) - f x| := tcu2_exp_lip (hb _) (hb _)
        _ ≤ Real.exp L * (L * ‖h‖ ^ θ) := by
          gcongr
          simpa using hH x h
        _ ≤ Real.exp L * (|L| + 1) * ‖h‖ ^ θ := by
          have hp : 0 ≤ ‖h‖ ^ θ := Real.rpow_nonneg (norm_nonneg h) _
          have : L ≤ |L| + 1 := by linarith [le_abs_self L]
          have h5 : Real.exp L * (L * ‖h‖ ^ θ) = Real.exp L * L * ‖h‖ ^ θ := by ring
          rw [h5]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hE0) hp
  | succ k ih =>
    intro L
    obtain ⟨L1, hL1⟩ := ih (3 * L)
    obtain ⟨L2, hL2⟩ := qC_prod (d := d) hθ0 hθ1 k 1 L1 L
    refine ⟨max (Real.exp L) L2, ?_⟩
    intro f hf
    have hf0 := qC_mono_k hθ0 hθ1 k hf
    obtain ⟨hd, hB, hf'⟩ := hf
    have hder : ∀ x, HasFDerivAt (fun y => Real.exp (f y)) (Real.exp (f x) • fderiv ℝ f x) x :=
      fun x => (hd x).hasFDerivAt.exp
    refine ⟨fun x => (hder x).differentiableAt, fun x => ?_, ?_⟩
    · rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact (Real.exp_le_exp.2 ((le_abs_self _).trans (by simpa using hB x))).trans (le_max_left _ _)
    · have e : fderiv ℝ (fun y => Real.exp (f y)) = fun x => Real.exp (f x) • fderiv ℝ f x :=
        funext fun x => (hder x).fderiv
      rw [e]
      refine qC_mono_L k (le_max_right _ _) ?_
      exact hL2 (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (Euc d →L[ℝ] ℝ) →L[ℝ] (Euc d →L[ℝ] ℝ))
        ContinuousLinearMap.opNorm_lsmul_le (hL1 hf0) hf'

/-- From the class to smoothness and bounds on all iterated derivatives. -/
lemma qC_contDiff {θ : ℝ} (hθ : 0 < θ) :
    ∀ (k : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Euc d → E} {L : ℝ},
      qC d θ k E f L → ContDiff ℝ k f ∧ ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ L := by
  intro k
  induction k with
  | zero =>
    intro E _ _ f L hf
    have hcont : Continuous f := qC_cont hθ hf
    obtain ⟨-, hB, -⟩ := hf
    refine ⟨by rw [Nat.cast_zero, contDiff_zero]; exact hcont, fun j hj x => ?_⟩
    obtain rfl : j = 0 := by omega
    rw [norm_iteratedFDeriv_zero]; exact hB x
  | succ k ih =>
    intro E _ _ f L hf
    obtain ⟨hd, hB, hf'⟩ := hf
    obtain ⟨hc, hM'⟩ := ih hf'
    refine ⟨?_, fun j hj x => ?_⟩
    · have hc' : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [hc', contDiff_succ_iff_fderiv]
      exact ⟨hd, fun h => absurd h (by simp), hc⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [norm_iteratedFDeriv_zero]; exact hB x
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [← norm_iteratedFDeriv_fderiv]
        exact hM' j' (by omega) x

/-- From smoothness and bounds on all iterated derivatives to the class (constant `3 M`). -/
lemma qC_of_bdd {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∀ (k : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Euc d → E} {M : ℝ},
      ContDiff ℝ (k + 1 : ℕ) f → (∀ j ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ M) →
      qC d θ k E f (3 * M) := by
  intro k
  induction k with
  | zero =>
    intro E _ _ f M hf hM
    have hd : Differentiable ℝ f := hf.differentiable (by simp)
    have hB : ∀ x, ‖f x‖ ≤ M := fun x => by simpa [norm_iteratedFDeriv_zero] using hM 0 (by omega) x
    have hD : ∀ x, ‖fderiv ℝ f x‖ ≤ M := fun x => by
      simpa [norm_iteratedFDeriv_one] using hM 1 le_rfl x
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hB 0)
    have hL : ∀ x h, ‖f (x + h) - f x‖ ≤ max M 0 * ‖h‖ ^ (1 : ℝ) := fun x h => by
      rw [Real.rpow_one]
      have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := f) (C := max M 0)
        (s := Set.univ) (x := x) (y := x + h) (fun y _ => hd y)
        (fun y _ => (hD y).trans (le_max_left _ _)) convex_univ (Set.mem_univ _) (Set.mem_univ _)
      simpa using this
    have h2 := regh_hol_mono hθ1 (le_max_right _ _) hM0 hB hL hθ0
    refine ⟨hd.continuous.aestronglyMeasurable, fun x => (hB x).trans (by linarith), fun x h => ?_⟩
    refine (h2 x h).trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg h) _))
    rw [max_eq_left hM0]; linarith
  | succ k ih =>
    intro E _ _ f M hf hM
    have hd : Differentiable ℝ f := hf.differentiable (by simp)
    have hB : ∀ x, ‖f x‖ ≤ M := fun x => by simpa [norm_iteratedFDeriv_zero] using hM 0 (by omega) x
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hB 0)
    refine ⟨hd, fun x => (hB x).trans (by linarith), ih ?_ fun j hj x => ?_⟩
    · exact hf.fderiv_right (by exact_mod_cast le_rfl)
    · rw [norm_iteratedFDeriv_fderiv]; exact hM (j + 1) (by omega) x

end Cls

/-! ### The Gaussian profile -/

/-- The Gaussian profile `exp(-β a ‖x‖²/2)/Z` lies in `qC` with one constant for all admissible `(a, β, Z)`. -/
lemma tcu2_gauss_q {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {am ap βm βp z₀ : ℝ} (ham : 0 < am)
    (hβm : 0 < βm) (hap : am ≤ ap) (hβp : βm ≤ βp) (hz₀ : 0 < z₀) (k : ℕ) :
    ∃ L : ℝ, ∀ a β Z : ℝ, am ≤ a → a ≤ ap → βm ≤ β → β ≤ βp → z₀ ≤ Z →
      qC d θ k ℝ (fun x : Euc d => Real.exp (-β * (a * ‖x‖ ^ 2 / 2 + 0)) / Z) L := by
  have hap0 : 0 < ap := ham.trans_le hap
  have hβp0 : 0 < βp := hβm.trans_le hβp
  set bg : ℝ := βm * am / 2 with hbg
  have hbg0 : 0 < bg := by positivity
  have hCp : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 ≤ r → (1 + r) ^ j * Real.exp (-bg * r ^ 2) ≤ C :=
    fun j => rege_poly_gauss_bdd hbg0 j
  choose Cp hCp0 hCpb using hCp
  set Kj : ℕ → ℝ := fun j => (Nat.factorial j : ℝ) * max z₀⁻¹ 0 * (max (βp * ap) 1) ^ j with hKj
  refine ⟨3 * ∑ j ∈ Finset.range (k + 2), Kj j * Cp j, fun a β Z h1 h2 h3 h4 h5 => ?_⟩
  have ha : 0 < a := ham.trans_le h1
  have hβ : 0 < β := hβm.trans_le h3
  have hZ : 0 < Z := hz₀.trans_le h5
  have hφ : ContDiff ℝ (k + 1 : ℕ) (fun x : Euc d => -β * (a * ‖x‖ ^ 2 / 2 + (fun _ => (0 : ℝ)) x)) :=
    contDiff_const.mul (((contDiff_const.mul (contDiff_norm_sq ℝ)).div_const 2).add contDiff_const)
  have hD := tcu2_exponent_bound (d := d) a β ha.le hβ.le (U := fun _ => (0 : ℝ)) (n := k + 1)
    contDiff_const (M := 0) le_rfl (fun i hi _ x => by
      simp [iteratedFDeriv_const_of_ne (by omega : i ≠ 0)])
  have hD' : ∀ i, 1 ≤ i → i ≤ k + 1 → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ i (fun x : Euc d => -β * (a * ‖x‖ ^ 2 / 2 + (fun _ => (0 : ℝ)) x)) x‖ ≤
        (βp * ap) * (1 + ‖x‖) := by
    intro i hi hik x
    refine ((hD i hi hik x).trans ?_)
    have h6 : β * a ≤ βp * ap := mul_le_mul h4 h2 ha.le hβp0.le
    have : (β * a + β * 0) * (1 + ‖x‖) ≤ (βp * ap) * (1 + ‖x‖) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    exact this
  have hup : ∀ x : Euc d, Real.exp (-β * (a * ‖x‖ ^ 2 / 2 + 0)) / Z ≤
      z₀⁻¹ * Real.exp (-bg * ‖x‖ ^ 2) := by
    intro x
    have e1 : Real.exp (-β * (a * ‖x‖ ^ 2 / 2 + 0)) ≤ Real.exp (-bg * ‖x‖ ^ 2) := by
      apply Real.exp_le_exp.2
      have : bg ≤ β * a / 2 := by
        rw [hbg]
        have := mul_le_mul h3 h1 ham.le hβ.le
        linarith
      nlinarith [sq_nonneg ‖x‖]
    have e2 : Z⁻¹ ≤ z₀⁻¹ := inv_anti₀ hz₀ h5
    rw [div_eq_inv_mul]
    exact mul_le_mul e2 e1 (Real.exp_pos _).le (inv_nonneg.2 hz₀.le)
  obtain ⟨hρk, hρD⟩ := tcu2_rho_deriv (d := d) (b := bg) (Z := Z) (C0 := z₀⁻¹) hZ
    (ρ := fun x : Euc d => Real.exp (-β * (a * ‖x‖ ^ 2 / 2 + 0)) / Z)
    (φ := fun x => -β * (a * ‖x‖ ^ 2 / 2 + (fun _ => (0 : ℝ)) x))
    (fun x => rfl) hup hφ (C := βp * ap) (by positivity) hD'
  refine qC_of_bdd hθ0 hθ1 k hρk fun j hj x => ?_
  refine (hρD j hj x).trans ?_
  have hKj0 : 0 ≤ Kj j := by positivity
  calc _ ≤ Kj j * ((1 + ‖x‖) ^ j * Real.exp (-bg * ‖x‖ ^ 2)) := by
        rw [hKj]; apply le_of_eq; ring
    _ ≤ Kj j * Cp j := mul_le_mul_of_nonneg_left (hCpb j _ (norm_nonneg x)) hKj0
    _ ≤ ∑ j ∈ Finset.range (k + 2), Kj j * Cp j :=
        Finset.single_le_sum (f := fun j => Kj j * Cp j)
          (fun j _ => mul_nonneg (by positivity) (hCp0 j).le)
          (Finset.mem_range.2 (by omega))

/-! ### Explicit-constant versions of the Hölder gain and the crossing -/

section Gain

/-- `regh_T_hold` with explicit constants: the Hölder constant of `T F` is
`C K + s Cd ∫φ + 2 Cd A`, where `‖F‖ ≤ Cd φ` and `F` is `θ`-Hölder with constant `K`. -/
lemma tcu2_T_hold {s σ θ : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hs2 : (d : ℝ) < s + 2)
    (hσs : s ≤ σ) (hσ2 : σ ≤ s + 2) (hσd : σ < d) (hθ0 : 0 ≤ θ) (hθ : θ + ((d : ℝ) - σ) < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      {F : Euc d → E} {K Cd : ℝ}, AEStronglyMeasurable F volume → lreg_RDec F → 0 ≤ K → 0 ≤ Cd →
      (∀ y, ‖F y‖ ≤ Cd * lreg_phi d y) → (∀ x h, ‖F (x + h) - F x‖ ≤ K * ‖h‖ ^ θ) →
      (∀ x, ‖regh_T s F x‖ ≤ Cd * lreg_A d s) ∧
      ∀ x h, ‖regh_T s F (x + h) - regh_T s F x‖ ≤
        (C * K + s * (Cd * ∫ y, lreg_phi d y) + 2 * (Cd * lreg_A d s)) *
          ‖h‖ ^ (θ + ((d : ℝ) - σ)) := by
  obtain ⟨C, hC0, hC⟩ := regh_Tk_hold (d := d) hd1 hs hsd hs2 hσs hσ2 hσd hθ0 hθ
  refine ⟨C, hC0, ?_⟩
  intro E _ _ _ F K Cd hm hR hK0 hCd hb hK
  have hB : ∀ y, ‖F y‖ ≤ Cd := fun y => (hb y).trans (by nlinarith [lreg_phi_le_one (d := d) y])
  have hFi : Integrable F := lreg_integrable_of_bound hm hb
  have hTb : ∀ x, ‖regh_T s F x‖ ≤ Cd * lreg_A d s := fun x =>
    (regh_T_integrable hd1 hs hsd hm hCd hb x).2
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = Cd * ∫ y, lreg_phi d y := ⟨_, rfl⟩
  have hIle : ∫ y, ‖F y‖ ≤ I := by
    rw [hIdef, ← integral_const_mul]
    exact integral_mono hFi.norm (lreg_phi_integrable.const_mul Cd) hb
  have hI : 0 ≤ I := by
    rw [hIdef]; exact mul_nonneg hCd (integral_nonneg fun y => (lreg_phi_pos y).le)
  obtain ⟨TA, hTAdef⟩ : ∃ T : ℝ, T = Cd * lreg_A d s := ⟨_, rfl⟩
  have hTA : 0 ≤ TA := by rw [hTAdef]; exact mul_nonneg hCd lreg_A_nonneg
  have hTb' : ∀ x, ‖regh_T s F x‖ ≤ TA := fun x => by rw [hTAdef]; exact hTb x
  rw [← hIdef, ← hTAdef]
  refine ⟨hTb', fun x h => ?_⟩
  have hTeq := regh_T_eq hd1 hs hsd hs2 hm hR
  have hKtk := hC hm hB hK0 hK x h
  have hT1 := regh_T1_lip hs hm hFi x h
  have hT1' : ‖regh_T1 s F (x + h) - regh_T1 s F x‖ ≤ s * ‖h‖ * I :=
    hT1.trans (mul_le_mul_of_nonneg_left hIle (by positivity))
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = ‖h‖ ^ (θ + ((d : ℝ) - σ)) := ⟨_, rfl⟩
  have hq : (0 : ℝ) < θ + ((d : ℝ) - σ) := by linarith
  have hq1 : θ + ((d : ℝ) - σ) ≤ 1 := hθ.le
  have hP0 : 0 ≤ P := by rw [hPdef]; exact Real.rpow_nonneg (norm_nonneg h) _
  rw [← hPdef] at hKtk ⊢
  have hCK : 0 ≤ C * K := mul_nonneg hC0 hK0
  have hsplit : regh_T s F (x + h) - regh_T s F x =
      (regh_Tk s F (x + h) - regh_Tk s F x) + (regh_T1 s F (x + h) - regh_T1 s F x) := by
    rw [hTeq]; simp only; abel
  rcases le_or_gt ‖h‖ 1 with hh | hh
  · have hpow : ‖h‖ ≤ P := by
      rw [hPdef]
      rcases eq_or_lt_of_le (norm_nonneg h) with h0' | h0'
      · rw [← h0', Real.zero_rpow hq.ne']
      · calc ‖h‖ = ‖h‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge h0' hh hq1
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have h5 : s * ‖h‖ * I ≤ s * P * I := by gcongr
    have h6 : 0 ≤ TA * P := mul_nonneg hTA hP0
    have e : (C * K + s * I + 2 * TA) * P = C * K * P + s * P * I + 2 * (TA * P) := by ring
    rw [e]
    linarith
  · have hpow : 1 ≤ P := by rw [hPdef]; exact Real.one_le_rpow hh.le hq.le
    have h2 : ‖regh_T s F (x + h) - regh_T s F x‖ ≤ 2 * TA := by
      calc _ ≤ ‖regh_T s F (x + h)‖ + ‖regh_T s F x‖ := norm_sub_le _ _
        _ ≤ TA + TA := add_le_add (hTb' _) (hTb' _)
        _ = _ := by ring
    have h3 : TA ≤ TA * P := by nlinarith
    have h4 : 0 ≤ C * K * P := mul_nonneg hCK hP0
    have h5 : 0 ≤ s * P * I := mul_nonneg (mul_nonneg hs.le hP0) hI
    have e : (C * K + s * I + 2 * TA) * P = C * K * P + s * P * I + 2 * (TA * P) := by ring
    rw [e]
    linarith

/-- `regh_cross` with explicit constants. -/
lemma tcu2_cross {s θ θ' : ℝ} (hd1 : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hs2 : (d : ℝ) < s + 2)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hθ'0 : 0 ≤ θ') (hθθ : θ' ≤ θ) (hθ'a : 1 < θ' + ((d : ℝ) - s))
    (hθb : θ + ((d : ℝ) - s) < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      {F : Euc d → E} {K Cd : ℝ}, AEStronglyMeasurable F volume → lreg_RDec F → 0 ≤ K → 0 ≤ Cd →
      (∀ y, ‖F y‖ ≤ Cd * lreg_phi d y) → (∀ x h, ‖F (x + h) - F x‖ ≤ K * ‖h‖ ^ θ) →
      ∃ P : Euc d → (Euc d →L[ℝ] E), (∀ x, HasFDerivAt (regh_T s F) (P x) x) ∧
        (∀ x, ‖P x‖ ≤ C * (K + Cd) + s * (Cd * ∫ y, lreg_phi d y)) ∧
        ∀ x h, ‖P (x + h) - P x‖ ≤ (C * K + s * (s + 3) * (Cd * ∫ y, lreg_phi d y) +
          2 * (C * (K + Cd) + s * (Cd * ∫ y, lreg_phi d y))) * ‖h‖ ^ (θ - θ') := by
  have hθa : 1 < θ + ((d : ℝ) - s) := by linarith
  have hθ'1 : s + 1 - θ' < d := by linarith
  have hs3 : (d : ℝ) < s + 3 := by linarith
  obtain ⟨C, hC0, hC⟩ := regh_Pk_hold (d := d) hd1 hs hθ hθ'0 hθθ hθ'1 hs3
  refine ⟨C, hC0, ?_⟩
  intro E _ _ _ F K Cd hm hR hK0 hCd hb hK
  have hB : ∀ y, ‖F y‖ ≤ Cd := fun y => (hb y).trans (by nlinarith [lreg_phi_le_one (d := d) y])
  have hFi : Integrable F := lreg_integrable_of_bound hm hb
  obtain ⟨hPb, hPh⟩ := hC hm hB hK0 hK
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = Cd * ∫ y, lreg_phi d y := ⟨_, rfl⟩
  have hIle : ∫ y, ‖F y‖ ≤ I := by
    rw [hIdef, ← integral_const_mul]
    exact integral_mono hFi.norm (lreg_phi_integrable.const_mul Cd) hb
  have hI : 0 ≤ I := by
    rw [hIdef]; exact mul_nonneg hCd (integral_nonneg fun y => (lreg_phi_pos y).le)
  have hP1b : ∀ x, ‖regh_P1 s F x‖ ≤ s * I := fun x =>
    (regh_P1_bound hs hm hFi x).trans (mul_le_mul_of_nonneg_left hIle hs.le)
  have hP1l : ∀ x h, ‖regh_P1 s F (x + h) - regh_P1 s F x‖ ≤ (s * (s + 3) * ‖h‖) * I := fun x h =>
    (regh_P1_lip hs hm hFi x h).trans (mul_le_mul_of_nonneg_left hIle (by positivity))
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = C * (K + Cd) + s * I := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  rw [← hIdef, ← hMdef]
  refine ⟨fun x => regh_Pk s F x + regh_P1 s F x, fun x => ?_, fun x => ?_, fun x h => ?_⟩
  · have hT := regh_T_eq hd1 hs hsd hs2 hm hR
    rw [hT]
    exact (regh_Tk_hasFDerivAt hd1 hs hsd hs2 hθ.le hθa hθb hm hB hK0 hK x).add
      (regh_T1_hasFDerivAt hs hm hFi x)
  · exact (norm_add_le _ _).trans (by rw [hMdef]; linarith [hPb x, hP1b x])
  · have hq : (0 : ℝ) ≤ θ - θ' := by linarith
    have hsplit : regh_Pk s F (x + h) + regh_P1 s F (x + h) - (regh_Pk s F x + regh_P1 s F x) =
        (regh_Pk s F (x + h) - regh_Pk s F x) + (regh_P1 s F (x + h) - regh_P1 s F x) := by abel
    show ‖regh_Pk s F (x + h) + regh_P1 s F (x + h) - (regh_Pk s F x + regh_P1 s F x)‖ ≤ _
    rw [hsplit]
    by_cases h0 : h = 0
    · subst h0
      simp only [add_zero, sub_self, add_zero, norm_zero]
      positivity
    have hρ : 0 < ‖h‖ := norm_pos_iff.2 h0
    have hP0 : 0 ≤ ‖h‖ ^ (θ - θ') := Real.rpow_nonneg hρ.le _
    rcases le_or_gt ‖h‖ 1 with hh | hh
    · have hpow : ‖h‖ ≤ ‖h‖ ^ (θ - θ') := by
        calc ‖h‖ = ‖h‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hρ hh (by linarith)
      refine (norm_add_le _ _).trans ?_
      have h1 := hPh x h hh
      have h2 := hP1l x h
      have h3 : (s * (s + 3) * ‖h‖) * I ≤ (s * (s + 3) * I) * ‖h‖ ^ (θ - θ') := by
        nlinarith [mul_nonneg (mul_nonneg hs.le (by positivity : (0 : ℝ) ≤ s + 3)) hI]
      have h4 : 0 ≤ M * ‖h‖ ^ (θ - θ') := mul_nonneg hM0 hP0
      nlinarith
    · have hpow : 1 ≤ ‖h‖ ^ (θ - θ') := Real.one_le_rpow hh.le hq
      have h2 : ‖regh_Pk s F (x + h) + regh_P1 s F (x + h) - (regh_Pk s F x + regh_P1 s F x)‖ ≤
          2 * M := by
        calc _ ≤ ‖regh_Pk s F (x + h) + regh_P1 s F (x + h)‖ + ‖regh_Pk s F x + regh_P1 s F x‖ :=
              norm_sub_le _ _
          _ ≤ M + M := add_le_add ((norm_add_le _ _).trans (by rw [hMdef]; linarith [hPb (x + h), hP1b (x + h)]))
              ((norm_add_le _ _).trans (by rw [hMdef]; linarith [hPb x, hP1b x]))
          _ = _ := by ring
      rw [← hsplit]
      have h5 : 0 ≤ C * K * ‖h‖ ^ (θ - θ') := by positivity
      have h6 : 0 ≤ s * (s + 3) * I * ‖h‖ ^ (θ - θ') := by positivity
      nlinarith

end Gain

end HRS.MS.TcU

end
