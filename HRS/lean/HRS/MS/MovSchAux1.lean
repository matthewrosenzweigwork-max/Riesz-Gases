import HRS.MS.Mov63Tie

/-!
# S64 (rows S6.4 `mov_schwartz`, S6.9 `mov_moving_reference`, S6.11 `mov_translated_*`), part 1: plan and the weighted Leibniz toolkit

Namespace `HRS.MS.MovSch`, helper prefix `s64_`.  Not manuscript rows.

## PLAN S6.4 `HRS.Whole.mov_schwartz` (Moving.lean ~:358, TeX S L4509-4523)

Statement check (frozen; TRUE, non-vacuous, no edit needed).  Constants are those of `mov63_decay_f0` exactly as in
`mnh_nonlinear` (`εstar, r, c₀ = c₁/2, c, C = max C₀ 2`), so the first conjunct (`MovNonlinearConclusion`) is the
same assembly as `mnh_nonlinear`.  Every `ρ ∈ MovInSmallClass r c₀ f0` equals the constructed solution
`ρ̂ = mneP d ρ₀ hm3 v` on `t ≥ 0` (`MovInSmallClass.mono_rate` + `mov_nl_unique_conjunct`), so the analytic facts
are proved for `ρ̂` (Duhamel structure available) and transported by that equality.
Junk-value traps: `ρ' t x := movDiv (mneY .. (v t)) x` is the genuine classical right derivative
(`mne_hasDeriv`, restricted from `Ici 0` to `Ici t`); `iteratedFDeriv` is only used on `C^K` functions (`ContDiff` is part of
the conclusion); `oscNorm` junk is excluded by `MemOsc` in `MovDecayBounds`; `hmK : K + d/2 + 4 < m` gives `K+3 + d/2 < m`
(a `C^{K+3}` representative of `v_t`) and `d/2 + K + 2 < m` (force in `C_b^{K+1}`, `mn_force_bound` with `j = K`).
Mathematics: `ρ_t - ρ₀ = h_t = √ρ₀ V_t`, `∂_tρ_t = div Y_t`; by the Euler equation `ν∇ρ₀ + ρ₀(qx+F₀) = 0`,
`Y_u = ν ∇h_u + h_u • A + (ρ₀ + h_u) • F_u` with `A = qx + F₀ = -ν ∇log ρ₀` (growth `≤ C⟨x⟩`, all derivatives bounded),
`F_u = ∇g*h_u`; each term is (Schwartz-class `√ρ₀`, `ρ₀`) times (`C_b^{K+2}` data linear in `u`, `F_u ∈ C_b^{K+1}` linear in
`u`, or the quadratic `h_u F_u`), so weighted `C^K` bounds `≤ C_L ‖u‖ (1+‖u‖)` follow from Leibniz, and
`‖u_t‖_{Σ^m} ≤ C εstar e^{-ct}` (`MovDecayBounds`, amplitude `εstar`).
Files: `MovSchAux1` (this toolkit), `MovSchAux2` (flux decomposition and bounds), `MovSchAux3` (weighted bounds of `ρ_u - ρ₀`
and `div Y_u`), `MovSchAux4` (assembly), `MovSchTie` (tie `mov_schwartz_proof`).

## Toolkit

* `s64_W n L f M` : `f ∈ C^n` and `⟨x⟩^L ‖D^k f x‖ ≤ M` for all `k ≤ n`, `x`.
* `s64_P n p A B` : `A ∈ C^n` and `‖D^k A x‖ ≤ B ⟨x⟩^p` (polynomial growth, polynomially bounded derivatives).
* `s64_W_smul` : Leibniz: `W (L+p) f M`, `P p A B` give `W L (f • A) (2^n M B)`.
* `s64_W_add`, `s64_W_const_smul`, `s64_W_gauss` (Gaussian derivative bounds give `W` for every `L`),
  `s64_W_gradient`, `s64_W_div` (derivative order shifts by one).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovSch

open HRS HRS.Whole

variable {d : ℕ}

section Toolkit

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Weighted `C^n` bound: `f ∈ C^n` and `⟨x⟩^L ‖D^k f x‖ ≤ M` for all `k ≤ n`. -/
def s64_W (n L : ℕ) (f : Euc d → F) (M : ℝ) : Prop :=
  ContDiff ℝ (n : WithTop ℕ∞) f ∧ ∀ k ≤ n, ∀ x, movBracket x ^ L * ‖iteratedFDeriv ℝ k f x‖ ≤ M

/-- Polynomially bounded `C^n` function: `‖D^k A x‖ ≤ B ⟨x⟩^p` for `k ≤ n`. -/
def s64_P (n p : ℕ) (A : Euc d → F) (B : ℝ) : Prop :=
  ContDiff ℝ (n : WithTop ℕ∞) A ∧ ∀ k ≤ n, ∀ x, ‖iteratedFDeriv ℝ k A x‖ ≤ B * movBracket x ^ p

lemma s64_bracket_pos (x : Euc d) : 0 < movBracket x := by
  unfold movBracket
  exact Real.sqrt_pos.2 (by positivity)

lemma s64_bracket_one_le (x : Euc d) : 1 ≤ movBracket x := by
  unfold movBracket
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖x‖])

lemma s64_norm_le_bracket (x : Euc d) : ‖x‖ ≤ movBracket x := by
  unfold movBracket
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖x‖])

lemma s64_bracket_zero : movBracket (0 : Euc d) = 1 := by
  unfold movBracket
  simp

lemma s64_bracket_le (x : Euc d) : movBracket x ≤ 1 + ‖x‖ := by
  unfold movBracket
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [norm_nonneg x]

lemma s64_W_nonneg {n L : ℕ} {f : Euc d → F} {M : ℝ} (h : s64_W n L f M) : 0 ≤ M := by
  have := h.2 0 (Nat.zero_le n) 0
  exact le_trans (mul_nonneg (pow_nonneg (s64_bracket_pos _).le _) (norm_nonneg _)) this

lemma s64_P_nonneg {n p : ℕ} {A : Euc d → F} {B : ℝ} (h : s64_P n p A B) : 0 ≤ B := by
  have := h.2 0 (Nat.zero_le n) 0
  rw [s64_bracket_zero, one_pow, mul_one] at this
  exact le_trans (norm_nonneg _) this

lemma s64_W_mono_L {n L L' : ℕ} (hL : L' ≤ L) {f : Euc d → F} {M : ℝ} (h : s64_W n L f M) :
    s64_W n L' f M := by
  refine ⟨h.1, fun k hk x => le_trans ?_ (h.2 k hk x)⟩
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (s64_bracket_one_le x) hL) (norm_nonneg _)

lemma s64_W_mono_n {n n' L : ℕ} (hn : n' ≤ n) {f : Euc d → F} {M : ℝ} (h : s64_W n L f M) :
    s64_W n' L f M :=
  ⟨h.1.of_le (by exact_mod_cast hn), fun k hk x => h.2 k (hk.trans hn) x⟩

lemma s64_W_mono_M {n L : ℕ} {f : Euc d → F} {M M' : ℝ} (hM : M ≤ M') (h : s64_W n L f M) :
    s64_W n L f M' := ⟨h.1, fun k hk x => (h.2 k hk x).trans hM⟩

lemma s64_P_mono_M {n p : ℕ} {A : Euc d → F} {B B' : ℝ} (hB : B ≤ B') (h : s64_P n p A B) :
    s64_P n p A B' :=
  ⟨h.1, fun k hk x => (h.2 k hk x).trans
    (mul_le_mul_of_nonneg_right hB (pow_nonneg (s64_bracket_pos x).le _))⟩

lemma s64_P_mono_p {n p p' : ℕ} (hp : p ≤ p') {A : Euc d → F} {B : ℝ} (h : s64_P n p A B) :
    s64_P n p' A B := by
  have hB := s64_P_nonneg h
  refine ⟨h.1, fun k hk x => (h.2 k hk x).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (s64_bracket_one_le x) hp) hB

lemma s64_P_of_W {n L : ℕ} {f : Euc d → F} {M : ℝ} (h : s64_W n L f M) : s64_P n 0 f M := by
  refine ⟨h.1, fun k hk x => ?_⟩
  have := h.2 k hk x
  have h1 : ‖iteratedFDeriv ℝ k f x‖ ≤ movBracket x ^ L * ‖iteratedFDeriv ℝ k f x‖ := by
    refine le_mul_of_one_le_left (norm_nonneg _) ?_
    exact one_le_pow₀ (s64_bracket_one_le x)
  simpa using h1.trans this

/-- Bounded derivatives give polynomial growth of every degree. -/
lemma s64_P_of_bdd {n : ℕ} (p : ℕ) {A : Euc d → F} {B : ℝ} (hA : ContDiff ℝ (n : WithTop ℕ∞) A)
    (h : ∀ k ≤ n, ∀ x, ‖iteratedFDeriv ℝ k A x‖ ≤ B) : s64_P n p A B := by
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (h 0 (Nat.zero_le n) 0)
  refine ⟨hA, fun k hk x => (h k hk x).trans ?_⟩
  exact le_mul_of_one_le_right hB (one_le_pow₀ (s64_bracket_one_le x))

/-- **Weighted Leibniz.** -/
lemma s64_W_smul {n L p : ℕ} {f : Euc d → ℝ} {A : Euc d → F} {M B : ℝ}
    (hf : s64_W n (L + p) f M) (hA : s64_P n p A B) :
    s64_W n L (fun x => f x • A x) (2 ^ n * (M * B)) := by
  have hM := s64_W_nonneg hf
  have hB := s64_P_nonneg hA
  refine ⟨hf.1.smul hA.1, fun k hk x => ?_⟩
  have h1 := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (𝕜' := ℝ) hf.1 hA.1 x (n := k) (by exact_mod_cast hk)
  have hb := s64_bracket_pos x
  set b := movBracket x with hbdef
  have hterm : ∀ i ∈ Finset.range (k + 1), b ^ L * ((k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
      ‖iteratedFDeriv ℝ (k - i) A x‖) ≤ (k.choose i : ℝ) * (M * B) := by
    intro i hi
    have hik : i ≤ k := by simpa [Nat.lt_succ_iff] using hi
    have a1 := hf.2 i (hik.trans hk) x
    have a2 := hA.2 (k - i) ((Nat.sub_le k i).trans hk) x
    have hc : (0 : ℝ) ≤ k.choose i := Nat.cast_nonneg _
    have e : b ^ L * ((k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k - i) A x‖) =
        (k.choose i : ℝ) * (b ^ L * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k - i) A x‖) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hc
    calc b ^ L * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k - i) A x‖
        ≤ b ^ L * ‖iteratedFDeriv ℝ i f x‖ * (B * b ^ p) :=
          mul_le_mul_of_nonneg_left a2 (mul_nonneg (pow_nonneg hb.le _) (norm_nonneg _))
      _ = (b ^ (L + p) * ‖iteratedFDeriv ℝ i f x‖) * B := by rw [pow_add]; ring
      _ ≤ M * B := mul_le_mul_of_nonneg_right a1 hB
  calc b ^ L * ‖iteratedFDeriv ℝ k (fun y => f y • A y) x‖
      ≤ b ^ L * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
          ‖iteratedFDeriv ℝ (k - i) A x‖ := mul_le_mul_of_nonneg_left h1 (pow_nonneg hb.le _)
    _ = ∑ i ∈ Finset.range (k + 1), b ^ L * ((k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
          ‖iteratedFDeriv ℝ (k - i) A x‖) := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (M * B) := Finset.sum_le_sum hterm
    _ = 2 ^ k * (M * B) := by
        rw [← Finset.sum_mul]
        have : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by
          exact_mod_cast Nat.sum_range_choose k
        rw [this]
    _ ≤ 2 ^ n * (M * B) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) (mul_nonneg hM hB)

lemma s64_W_add {n L : ℕ} {f g : Euc d → F} {M1 M2 : ℝ} (hf : s64_W n L f M1) (hg : s64_W n L g M2) :
    s64_W n L (fun x => f x + g x) (M1 + M2) := by
  refine ⟨hf.1.add hg.1, fun k hk x => ?_⟩
  have hb := s64_bracket_pos x
  have e : iteratedFDeriv ℝ k (fun x => f x + g x) x = iteratedFDeriv ℝ k f x + iteratedFDeriv ℝ k g x :=
    iteratedFDeriv_add_apply (hf.1.contDiffAt.of_le (by exact_mod_cast hk))
      (hg.1.contDiffAt.of_le (by exact_mod_cast hk))
  rw [e]
  calc movBracket x ^ L * ‖iteratedFDeriv ℝ k f x + iteratedFDeriv ℝ k g x‖
      ≤ movBracket x ^ L * (‖iteratedFDeriv ℝ k f x‖ + ‖iteratedFDeriv ℝ k g x‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (pow_nonneg hb.le _)
    _ = movBracket x ^ L * ‖iteratedFDeriv ℝ k f x‖ + movBracket x ^ L * ‖iteratedFDeriv ℝ k g x‖ := by ring
    _ ≤ M1 + M2 := add_le_add (hf.2 k hk x) (hg.2 k hk x)

lemma s64_W_const_smul {n L : ℕ} {f : Euc d → F} {M : ℝ} (c : ℝ) (hf : s64_W n L f M) :
    s64_W n L (fun x => c • f x) (|c| * M) := by
  refine ⟨hf.1.const_smul c, fun k hk x => ?_⟩
  have hb := s64_bracket_pos x
  have e : iteratedFDeriv ℝ k (fun x => c • f x) x = c • iteratedFDeriv ℝ k f x :=
    iteratedFDeriv_const_smul_apply (hf.1.contDiffAt.of_le (by exact_mod_cast hk))
  rw [e, norm_smul, Real.norm_eq_abs]
  calc movBracket x ^ L * (|c| * ‖iteratedFDeriv ℝ k f x‖)
      = |c| * (movBracket x ^ L * ‖iteratedFDeriv ℝ k f x‖) := by ring
    _ ≤ |c| * M := mul_le_mul_of_nonneg_left (hf.2 k hk x) (abs_nonneg c)

lemma s64_W_neg {n L : ℕ} {f : Euc d → F} {M : ℝ} (hf : s64_W n L f M) :
    s64_W n L (fun x => -f x) M := by
  have := s64_W_const_smul (-1) hf
  simp only [neg_smul, one_smul, abs_neg, abs_one, one_mul] at this
  exact this

lemma s64_W_sum {n L : ℕ} {ι : Type*} (S : Finset ι) {f : ι → Euc d → F} {M : ι → ℝ}
    (h : ∀ i ∈ S, s64_W n L (f i) (M i)) :
    s64_W n L (fun x => ∑ i ∈ S, f i x) (∑ i ∈ S, M i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using contDiff_const (c := (0 : F)), fun k hk x => ?_⟩
    simp only [Finset.sum_empty]
    simp
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact s64_W_add (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Gaussian derivative bounds give weighted bounds with every weight. -/
lemma s64_W_gauss {n : ℕ} (L : ℕ) {f : Euc d → F} {c : ℝ} (hc : 0 < c)
    (hf : ContDiff ℝ (n : WithTop ℕ∞) f)
    (hb : ∀ k : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2)) :
    ∃ M : ℝ, s64_W n L f M := by
  choose C hC using hb
  have ha : (0 : ℝ) < 2 * c := by positivity
  set K : ℝ := (L.factorial : ℝ) * Real.exp (1 + (0 + 1) ^ 2 / (2 * c)) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨(∑ k ∈ Finset.range (n + 1), |C k|) * K, hf, fun k hk x => ?_⟩
  have hbx := s64_bracket_pos x
  have h1 : movBracket x ^ L ≤ (1 + ‖x‖) ^ L :=
    pow_le_pow_left₀ hbx.le (s64_bracket_le x) L
  have h2 := HRS.MS.Mov0.mov0_pow_exp_bound (a := 2 * c) (M := 0) ha L ‖x‖ (norm_nonneg _)
  have h3 : Real.exp (-(2 * c * ‖x‖ ^ 2 / 2) + 0 * ‖x‖) = Real.exp (-c * ‖x‖ ^ 2) := by
    congr 1; ring
  rw [h3] at h2
  have h4 : Real.exp (-(2 * c / 4) * ‖x‖ ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (2 * c / 4) * ‖x‖ ^ 2 := by positivity
    linarith
  have h5 : (1 + ‖x‖) ^ L * Real.exp (-c * ‖x‖ ^ 2) ≤ K := by
    refine h2.trans ?_
    calc (L.factorial : ℝ) * Real.exp (1 + (0 + 1) ^ 2 / (2 * c)) * Real.exp (-(2 * c / 4) * ‖x‖ ^ 2)
        ≤ (L.factorial : ℝ) * Real.exp (1 + (0 + 1) ^ 2 / (2 * c)) * 1 :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = K := by rw [hK]; ring
  have hCk : |C k| ≤ ∑ j ∈ Finset.range (n + 1), |C j| :=
    Finset.single_le_sum (f := fun j => |C j|) (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (by omega))
  have hexp : 0 ≤ Real.exp (-c * ‖x‖ ^ 2) := (Real.exp_pos _).le
  calc movBracket x ^ L * ‖iteratedFDeriv ℝ k f x‖
      ≤ (1 + ‖x‖) ^ L * (|C k| * Real.exp (-c * ‖x‖ ^ 2)) := by
        refine mul_le_mul h1 ((hC k x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hexp))
          (norm_nonneg _) (by positivity)
    _ = |C k| * ((1 + ‖x‖) ^ L * Real.exp (-c * ‖x‖ ^ 2)) := by ring
    _ ≤ |C k| * K := mul_le_mul_of_nonneg_left h5 (abs_nonneg _)
    _ ≤ (∑ j ∈ Finset.range (n + 1), |C j|) * K := mul_le_mul_of_nonneg_right hCk hK0

end Toolkit

section Calculus

/-- The gradient shifts the derivative order by one. -/
lemma s64_W_gradient {n L : ℕ} {f : Euc d → ℝ} {M : ℝ} (h : s64_W (n + 1) L f M) :
    s64_W n L (gradient f) M := by
  refine ⟨HRS.MS.Mov63.mne_grad_cd (by exact_mod_cast h.1), fun k hk x => ?_⟩
  rw [HRS.MS.Gap.gap1_norm_iter_gradient]
  exact h.2 (k + 1) (by omega) x

/-- The divergence shifts the derivative order by one. -/
lemma s64_W_div {n L : ℕ} {Y : Euc d → Euc d} {M : ℝ} (h : s64_W (n + 1) L Y M) :
    s64_W n L (fun x => movDiv Y x) (‖HRS.MS.MovForce.movb2_divL d‖ * M) := by
  have hb := HRS.MS.MovForce.movb2_div_bound (d := d) (F := Y) (j := n) (by exact_mod_cast h.1)
  refine ⟨hb.1, fun k hk x => ?_⟩
  have hbx := s64_bracket_pos x
  have h1 := hb.2 k hk x
  have h2 := h.2 (k + 1) (by omega) x
  calc movBracket x ^ L * ‖iteratedFDeriv ℝ k (fun x => movDiv Y x) x‖
      ≤ movBracket x ^ L * (‖HRS.MS.MovForce.movb2_divL d‖ * ‖iteratedFDeriv ℝ (k + 1) Y x‖) :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg hbx.le _)
    _ = ‖HRS.MS.MovForce.movb2_divL d‖ * (movBracket x ^ L * ‖iteratedFDeriv ℝ (k + 1) Y x‖) := by ring
    _ ≤ ‖HRS.MS.MovForce.movb2_divL d‖ * M :=
        mul_le_mul_of_nonneg_left h2 (ContinuousLinearMap.opNorm_nonneg _)

end Calculus

end HRS.MS.MovSch

end
