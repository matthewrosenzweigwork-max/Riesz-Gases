import HRS.MS.MovForceAux6
import HRS.MS.MovThermAux2
import HRS.MS.MovOscAux4
import HRS.Whole.Moving

/-!
# MOV-B2 (4): the force theorem `mov_operators_force` (S6.1, step 6)

Namespace `HRS.MS.MovForce`, helper prefix `movb2_`.

* `movb2_GA_mul`: Leibniz bound `‖D^i (ψ v)‖ ≤ 2^K C_ψ M e^{-c‖x‖²}` for the profile `h = ψ v`
  (`ψ = √ρ` with Gaussian derivative bounds, `‖D^k v‖ ≤ M`), linear in `M`;
* `movb2_div_bound`: `div F ∈ C^j` with `‖D^i div F‖ ≤ ‖Λ‖ ‖D^{i+1} F‖`, `F ∈ C^{j+1}`
  (`div F = Λ (DF)` for a fixed continuous linear functional `Λ`, so no Laplacian identity is needed);
* `movb2_inner_bound`: Leibniz bound for `⟨∇log ρ, F⟩` (linear growth of `∇log ρ`, bounded higher
  derivatives, and `‖x‖ ‖D^i F‖` bounded);
* `mov_operators_force_gen`: the force theorem for any density `ρ` with `√ρ`, `∇log ρ` as above and for any
  `v ∈ C^{j+2}` with `‖D^k v‖_∞ ≤ M` (`k ≤ j+2`), the bound being `C M` with `C` independent of `v`; this is the
  non-Schwartz form needed by S6.3;
* `mov_operators_force_proof`: the frozen statement `HRS.Whole.mov_operators_force`, from the thermal data of
  MOV-0 (`mv0_gapref`, `mv0_sqrt_gauss`, `mv0_dlog_bounds`), the embedding `mo_sobolev_emb` at the integer
  `n = ⌊d/2⌋ + j + 3 ≤ m` and `mo_mono`; the file ends with the tie
  `example := (@mov_operators_force_proof : type_of% @mov_operators_force)`.

Statement adjustment relative to the plan: the force theorem does not need the splitting of `Δ g * h` and
`∇g * h` separately; `‖F‖_{C_b^{j+1}}` and `‖div F + ⟨∇log ρ, F⟩‖_{C_b^j}` are bounded through the derivative bounds of
`F` (`mv1_force_deriv_bound`), the thermal bound `‖∇log ρ(x)‖ ≤ β q ‖x‖ + M0`, and the weighted bound
`‖x‖ ‖D^k F(x)‖ ≤ C E` which comes from the far-field decay (step 4(a)) and the first moment of `g_loc` (step 5).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovForce

open HRS.Whole

variable {d : ℕ} {s : ℝ}

lemma movb2_le_infty (n : ℕ) : ((n : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top

/-- Leibniz for a product with Gaussian amplitude: `‖D^i(ψ v)‖ ≤ 2^K C_ψ M e^{-c‖x‖²}`. -/
lemma movb2_GA_mul {K : ℕ} {ψ v : Euc d → ℝ} (hψ : ContDiff ℝ (K : WithTop ℕ∞) ψ)
    (hv : ContDiff ℝ (K : WithTop ℕ∞) v) {c Cψ M : ℝ} (hCψ : 0 ≤ Cψ) (hM : 0 ≤ M)
    (hψb : ∀ i ≤ K, ∀ y, ‖iteratedFDeriv ℝ i ψ y‖ ≤ Cψ * Real.exp (-c * ‖y‖ ^ 2))
    (hvb : ∀ i ≤ K, ∀ y, ‖iteratedFDeriv ℝ i v y‖ ≤ M) :
    movb2_GA K c (2 ^ K * Cψ * M) (fun y => ψ y * v y) := by
  intro n hn y
  have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := (K : WithTop ℕ∞)) hψ hv y (n := n)
    (by exact_mod_cast hn)
  refine h1.trans ?_
  have hterm : ∀ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ *
      ‖iteratedFDeriv ℝ (n - i) v y‖ ≤ (n.choose i : ℝ) * (Cψ * M * Real.exp (-c * ‖y‖ ^ 2)) := by
    intro i hi
    have hik : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
    have a := hψb i (hik.trans hn) y
    have b := hvb (n - i) ((Nat.sub_le n i).trans hn) y
    calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ * ‖iteratedFDeriv ℝ (n - i) v y‖
        ≤ (n.choose i : ℝ) * (Cψ * Real.exp (-c * ‖y‖ ^ 2)) * M :=
          mul_le_mul (mul_le_mul_of_nonneg_left a (Nat.cast_nonneg _)) b (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans a))
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [← Finset.sum_mul, hsum]
  have h2 : (2 : ℝ) ^ n ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hn
  have hCM : 0 ≤ Cψ * M * Real.exp (-c * ‖y‖ ^ 2) := by positivity
  calc (2 : ℝ) ^ n * (Cψ * M * Real.exp (-c * ‖y‖ ^ 2)) ≤ 2 ^ K * (Cψ * M * Real.exp (-c * ‖y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_right h2 hCM
    _ = _ := by ring

/-! ### The divergence as a continuous linear functional of `DF` -/

/-- `A ↦ ∑ i, (A e_i)_i`. -/
def movb2_divL (d : ℕ) : (Euc d →L[ℝ] Euc d) →L[ℝ] ℝ :=
  ∑ i : Fin d, (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp
    (ContinuousLinearMap.apply ℝ (Euc d) (EuclideanSpace.single i (1 : ℝ)))

lemma movb2_movDiv_eq (F : Euc d → Euc d) (x : Euc d) : movDiv F x = movb2_divL d (fderiv ℝ F x) := by
  simp [movDiv, movb2_divL]

/-- `div F ∈ C^j` with `‖D^i div F‖ ≤ ‖Λ‖ ‖D^{i+1} F‖` for `F ∈ C^{j+1}`. -/
lemma movb2_div_bound {F : Euc d → Euc d} {j : ℕ} (hF : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) F) :
    ContDiff ℝ (j : WithTop ℕ∞) (fun x => movDiv F x) ∧ ∀ i ≤ j, ∀ x,
      ‖iteratedFDeriv ℝ i (fun x => movDiv F x) x‖ ≤ ‖movb2_divL d‖ * ‖iteratedFDeriv ℝ (i + 1) F x‖ := by
  have hfd : ContDiff ℝ (j : WithTop ℕ∞) (fderiv ℝ F) := hF.fderiv_right (m := j) (by rw [Nat.cast_succ])
  have hfun : (fun x => movDiv F x) = (movb2_divL d) ∘ (fderiv ℝ F) := funext fun x => movb2_movDiv_eq F x
  rw [hfun]
  refine ⟨(movb2_divL d).contDiff.comp hfd, fun i hi x => ?_⟩
  have := (movb2_divL d).norm_iteratedFDeriv_comp_left (f := fderiv ℝ F) (x := x) (N := (j : WithTop ℕ∞))
    (n := i) hfd.contDiffAt (by exact_mod_cast hi)
  rwa [norm_iteratedFDeriv_fderiv] at this

/-! ### The product term `⟨∇log ρ, F⟩` -/

lemma movb2_innerSL_norm_le : ‖(innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  simp [innerSL_apply_norm]

lemma movb2_inner_bound {f F : Euc d → Euc d} {j : ℕ} (hf : ContDiff ℝ (j : WithTop ℕ∞) f)
    (hF : ContDiff ℝ (j : WithTop ℕ∞) F) {a M0 Df Fb E : ℝ} (ha : 0 ≤ a) (hM0 : 0 ≤ M0) (hDf : 0 ≤ Df)
    (hFb : 0 ≤ Fb * E)
    (hf0 : ∀ x, ‖f x‖ ≤ a * ‖x‖ + M0)
    (hfD : ∀ l, 1 ≤ l → l ≤ j → ∀ x, ‖iteratedFDeriv ℝ l f x‖ ≤ Df)
    (hF1 : ∀ i ≤ j, ∀ x, ‖iteratedFDeriv ℝ i F x‖ ≤ Fb * E)
    (hF2 : ∀ i ≤ j, ∀ x, ‖x‖ * ‖iteratedFDeriv ℝ i F x‖ ≤ Fb * E) :
    ∀ i ≤ j, ∀ x, ‖iteratedFDeriv ℝ i (fun y => inner ℝ (f y) (F y)) x‖ ≤
      2 ^ j * ((a + M0 + Df) * (Fb * E)) := by
  intro i hi x
  have h1 := (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).norm_iteratedFDeriv_le_of_bilinear
    (hf.of_le (by exact_mod_cast hi)) (hF.of_le (by exact_mod_cast hi)) x (n := i) le_rfl
  have h2 : (fun y => (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (f y) (F y)) =
      fun y => inner ℝ (f y) (F y) := by funext y; simp
  rw [h2] at h1
  have hT : 0 ≤ (a + M0 + Df) * (Fb * E) := mul_nonneg (by linarith) hFb
  have hterm : ∀ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l f x‖ *
      ‖iteratedFDeriv ℝ (i - l) F x‖ ≤ (i.choose l : ℝ) * ((a + M0 + Df) * (Fb * E)) := by
    intro l hl
    have hli : l ≤ i := by simpa [Nat.lt_succ_iff] using hl
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hFi := hF1 (i - l) ((Nat.sub_le i l).trans hi) x
    have hFi2 := hF2 (i - l) ((Nat.sub_le i l).trans hi) x
    rcases Nat.eq_zero_or_pos l with rfl | hl1
    · rw [norm_iteratedFDeriv_zero]
      have := hf0 x
      calc ‖f x‖ * ‖iteratedFDeriv ℝ (i - 0) F x‖ ≤ (a * ‖x‖ + M0) * ‖iteratedFDeriv ℝ (i - 0) F x‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ = a * (‖x‖ * ‖iteratedFDeriv ℝ (i - 0) F x‖) + M0 * ‖iteratedFDeriv ℝ (i - 0) F x‖ := by ring
        _ ≤ a * (Fb * E) + M0 * (Fb * E) := add_le_add (mul_le_mul_of_nonneg_left hFi2 ha)
            (mul_le_mul_of_nonneg_left hFi hM0)
        _ ≤ (a + M0 + Df) * (Fb * E) := by nlinarith [mul_nonneg hDf hFb]
    · have hD := hfD l hl1 (hli.trans hi) x
      calc ‖iteratedFDeriv ℝ l f x‖ * ‖iteratedFDeriv ℝ (i - l) F x‖ ≤ Df * (Fb * E) :=
            mul_le_mul hD hFi (norm_nonneg _) hDf
        _ ≤ (a + M0 + Df) * (Fb * E) := by nlinarith [mul_nonneg ha hFb, mul_nonneg hM0 hFb]
  refine (h1.trans ?_)
  calc ‖(innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)‖ * ∑ l ∈ Finset.range (i + 1),
        (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l f x‖ * ‖iteratedFDeriv ℝ (i - l) F x‖
      ≤ 1 * ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * ((a + M0 + Df) * (Fb * E)) :=
        mul_le_mul movb2_innerSL_norm_le (Finset.sum_le_sum hterm)
          (Finset.sum_nonneg fun l _ => by positivity) zero_le_one
    _ = 2 ^ i * ((a + M0 + Df) * (Fb * E)) := by
        rw [one_mul, ← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose i
    _ ≤ 2 ^ j * ((a + M0 + Df) * (Fb * E)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi) hT

/-! ### The generic force theorem -/

/-- The force of `h = √ρ v`. -/
def movb2_F (d : ℕ) (s : ℝ) (ρ v : Euc d → ℝ) : Euc d → Euc d :=
  movForce d s (fun x => Real.sqrt (ρ x) * v x)

/-- The source term `div F + ⟨∇log ρ, F⟩`. -/
def movb2_G (d : ℕ) (s : ℝ) (ρ v : Euc d → ℝ) (x : Euc d) : ℝ :=
  movDiv (movb2_F d s ρ v) x + inner ℝ (gradient (fun y => Real.log (ρ y)) x) (movb2_F d s ρ v x)

/-- **`mov_operators_force_gen`** (S6.1, step 6; generic form, `v` is only `C^{j+2}` with bounded derivatives).

Hypotheses on the density `ρ`: `ψ = √ρ` is smooth with a common Gaussian rate `c` for all derivatives;
`∇ log ρ` is smooth with linear growth `a‖x‖ + M0` and bounded derivatives of every positive order.
For `v ∈ C^{j+2}` with `‖D^k v‖ ≤ M` for `k ≤ j+2`, the force `F = ∇g * (√ρ v)` is `C^{j+1}`,
`div F + ⟨∇log ρ, F⟩ ∈ C_b^j` and `‖F‖_{C_b^{j+1}} + ‖div F + ⟨∇log ρ, F⟩‖_{C_b^j} ≤ C M`, `C` independent of `v`. -/
theorem mov_operators_force_gen (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ} {c a M0 : ℝ}
    (hc : 0 < c) (ha : 0 ≤ a) (hM0 : 0 ≤ M0)
    (hψs : ContDiff ℝ ∞ (fun x => Real.sqrt (ρ x)))
    (hψb : ∀ k : ℕ, ∃ C : ℝ, ∀ x,
      ‖iteratedFDeriv ℝ k (fun y => Real.sqrt (ρ y)) x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2))
    (hfs : ContDiff ℝ ∞ (fun x => gradient (fun y => Real.log (ρ y)) x))
    (hf0 : ∀ x, ‖gradient (fun y => Real.log (ρ y)) x‖ ≤ a * ‖x‖ + M0)
    (hfD : ∀ l : ℕ, 1 ≤ l → ∃ Df : ℝ, ∀ x,
      ‖iteratedFDeriv ℝ l (fun y => gradient (fun z => Real.log (ρ z)) y) x‖ ≤ Df) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : Euc d → ℝ) (M : ℝ), 0 ≤ M →
      ContDiff ℝ ((j + 2 : ℕ) : WithTop ℕ∞) v → (∀ k ≤ j + 2, ∀ x, ‖iteratedFDeriv ℝ k v x‖ ≤ M) →
      ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (movb2_F d s ρ v) ∧ MemCb j (movb2_G d s ρ v) ∧
        cbNormVecE (j + 1) (movb2_F d s ρ v) + ENNReal.ofReal (cbNorm j (movb2_G d s ρ v)) ≤
          ENNReal.ofReal (C * M) := by
  -- constants
  choose Cψk hCψk using hψb
  set Cψ : ℝ := ∑ k ∈ Finset.range (j + 3), |Cψk k| with hCψdef
  have hCψ0 : 0 ≤ Cψ := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hψb' : ∀ i ≤ j + 2, ∀ y, ‖iteratedFDeriv ℝ i (fun z => Real.sqrt (ρ z)) y‖ ≤
      Cψ * Real.exp (-c * ‖y‖ ^ 2) := fun i hi y => by
    refine (hCψk i y).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    refine (le_abs_self _).trans ?_
    exact Finset.single_le_sum (f := fun k => |Cψk k|) (fun k _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega))
  obtain ⟨Cf, hCf0, hCf⟩ : ∃ Cf : ℕ → ℝ, (∀ k, 0 ≤ Cf k) ∧ ∀ k, ∀ {E : ℝ} {u : Euc d → ℝ},
      ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) u → movb2_GA (k + 1) c E u →
        ContDiff ℝ (k : WithTop ℕ∞) (movForce d s u) ∧ ∀ x : Euc d,
          ‖iteratedFDeriv ℝ k (movForce d s u) x‖ ≤ Cf k * E ∧
            ‖x‖ * ‖iteratedFDeriv ℝ k (movForce d s u) x‖ ≤ Cf k * E := by
    choose C hC0 hC using fun k => mv1_force_deriv_bound (d := d) (s := s) hd hs0 hsd hc k
    exact ⟨C, hC0, fun k => hC k⟩
  set Fb : ℝ := ∑ k ∈ Finset.range (j + 2), Cf k with hFbdef
  have hFb0 : 0 ≤ Fb := Finset.sum_nonneg fun k _ => hCf0 k
  have hCfFb : ∀ k ≤ j + 1, Cf k ≤ Fb := fun k hk =>
    Finset.single_le_sum (f := Cf) (fun k _ => hCf0 k) (Finset.mem_range.2 (by omega))
  choose Dfk hDfk using hfD
  set Df : ℝ := ∑ l ∈ Finset.range (j + 1), if h : 1 ≤ l then |Dfk l h| else 0 with hDfdef
  have hDf0 : 0 ≤ Df := Finset.sum_nonneg fun l _ => by split_ifs <;> positivity
  have hDfl : ∀ l, 1 ≤ l → l ≤ j → ∀ x, ‖iteratedFDeriv ℝ l
      (fun y => gradient (fun z => Real.log (ρ z)) y) x‖ ≤ Df := fun l hl hlj x => by
    refine (hDfk l hl x).trans ?_
    refine (le_abs_self _).trans ?_
    have := Finset.single_le_sum (f := fun l => if h : 1 ≤ l then |Dfk l h| else 0)
      (fun l _ => by split_ifs <;> positivity) (Finset.mem_range.2 (show l < j + 1 by omega))
    simpa [hl] using this
  set Λn : ℝ := ‖movb2_divL d‖ with hΛn
  set C2 : ℝ := Λn * Fb + 2 ^ j * ((a + M0 + Df) * Fb) with hC2
  have hC20 : 0 ≤ C2 := by positivity
  refine ⟨((j + 2) * Fb + (j + 1) * C2) * (2 ^ (j + 2) * Cψ), by positivity, ?_⟩
  intro v M hM hv hvb
  set E : ℝ := 2 ^ (j + 2) * Cψ * M with hE
  have hE0 : 0 ≤ E := by positivity
  set h : Euc d → ℝ := fun y => Real.sqrt (ρ y) * v y with hh
  have hψc : ContDiff ℝ ((j + 2 : ℕ) : WithTop ℕ∞) (fun x => Real.sqrt (ρ x)) :=
    hψs.of_le (movb2_le_infty (j + 2))
  have hhc : ContDiff ℝ ((j + 2 : ℕ) : WithTop ℕ∞) h := hψc.mul hv
  have hGA : movb2_GA (j + 2) c E h :=
    movb2_GA_mul hψc hv hCψ0 hM hψb' (fun i hi y => hvb i hi y)
  -- the force
  have hFk : ∀ k ≤ j + 1, ContDiff ℝ (k : WithTop ℕ∞) (movForce d s h) ∧ ∀ x : Euc d,
      ‖iteratedFDeriv ℝ k (movForce d s h) x‖ ≤ Fb * E ∧
        ‖x‖ * ‖iteratedFDeriv ℝ k (movForce d s h) x‖ ≤ Fb * E := fun k hk => by
    obtain ⟨h1, h2⟩ := hCf k (E := E) (u := h) (hhc.of_le (by exact_mod_cast (by omega : k + 1 ≤ j + 2)))
      (movb2_GA_mono (by omega) hGA)
    refine ⟨h1, fun x => ?_⟩
    obtain ⟨h3, h4⟩ := h2 x
    exact ⟨h3.trans (mul_le_mul_of_nonneg_right (hCfFb k hk) hE0),
      h4.trans (mul_le_mul_of_nonneg_right (hCfFb k hk) hE0)⟩
  have hF : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (movForce d s h) := (hFk (j + 1) le_rfl).1
  have hFj : ContDiff ℝ (j : WithTop ℕ∞) (movForce d s h) := hF.of_le (by exact_mod_cast Nat.le_succ j)
  -- the source term
  obtain ⟨hdivc, hdivb⟩ := movb2_div_bound hF
  have hfc : ContDiff ℝ (j : WithTop ℕ∞) (fun x => gradient (fun y => Real.log (ρ y)) x) :=
    hfs.of_le (movb2_le_infty j)
  have hinner := movb2_inner_bound hfc hFj ha hM0 hDf0 (mul_nonneg hFb0 hE0) hf0 hDfl
    (fun i hi x => ((hFk i (by omega)).2 x).1) (fun i hi x => ((hFk i (by omega)).2 x).2)
  have hinnerc : ContDiff ℝ (j : WithTop ℕ∞)
      (fun x => inner ℝ (gradient (fun y => Real.log (ρ y)) x) (movForce d s h x)) := hfc.inner ℝ hFj
  have hGeq : movb2_G d s ρ v = (fun x => movDiv (movForce d s h) x) +
      (fun x => inner ℝ (gradient (fun y => Real.log (ρ y)) x) (movForce d s h x)) := rfl
  have hGc : ContDiff ℝ (j : WithTop ℕ∞) (movb2_G d s ρ v) := by
    rw [hGeq]; exact hdivc.add hinnerc
  have hGb : ∀ i ≤ j, ∀ x, ‖iteratedFDeriv ℝ i (movb2_G d s ρ v) x‖ ≤ C2 * E := fun i hi x => by
    rw [hGeq, iteratedFDeriv_add_apply (hdivc.of_le (by exact_mod_cast hi)).contDiffAt
      (hinnerc.of_le (by exact_mod_cast hi)).contDiffAt]
    refine (norm_add_le _ _).trans ?_
    have h1 := (hdivb i hi x).trans (mul_le_mul_of_nonneg_left
      ((hFk (i + 1) (by omega)).2 x).1 (ContinuousLinearMap.opNorm_nonneg _))
    have h2 := hinner i hi x
    calc _ ≤ Λn * (Fb * E) + 2 ^ j * ((a + M0 + Df) * (Fb * E)) := add_le_add h1 h2
      _ = C2 * E := by rw [hC2]; ring
  have hmem : MemCb j (movb2_G d s ρ v) :=
    ⟨hGc, fun i hi => ⟨C2 * E, by rintro _ ⟨x, rfl⟩; exact hGb i hi x⟩⟩
  have hcb : cbNorm j (movb2_G d s ρ v) ≤ (j + 1) * (C2 * E) := by
    unfold cbNorm
    calc ∑ i ∈ Finset.range (j + 1), ⨆ z : Euc d, ‖iteratedFDeriv ℝ i (movb2_G d s ρ v) z‖
        ≤ ∑ _i ∈ Finset.range (j + 1), (C2 * E) :=
          Finset.sum_le_sum fun i hi => ciSup_le fun x => hGb i (by
            have := Finset.mem_range.1 hi; omega) x
      _ = (j + 1) * (C2 * E) := by simp
  have hcbv : cbNormVecE (j + 1) (movb2_F d s ρ v) ≤ ENNReal.ofReal ((j + 2) * (Fb * E)) := by
    unfold cbNormVecE
    calc ∑ i ∈ Finset.range (j + 1 + 1), ⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ i (movb2_F d s ρ v) x‖
        ≤ ∑ _i ∈ Finset.range (j + 1 + 1), ENNReal.ofReal (Fb * E) :=
          Finset.sum_le_sum fun i hi => iSup_le fun x => ENNReal.ofReal_le_ofReal
            ((hFk i (by have := Finset.mem_range.1 hi; omega)).2 x).1
      _ = ENNReal.ofReal (∑ _i ∈ Finset.range (j + 1 + 1), (Fb * E)) :=
          (ENNReal.ofReal_sum_of_nonneg fun _ _ => mul_nonneg hFb0 hE0).symm
      _ = ENNReal.ofReal ((j + 2) * (Fb * E)) := by
          congr 1
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  refine ⟨hF, hmem, ?_⟩
  calc cbNormVecE (j + 1) (movb2_F d s ρ v) + ENNReal.ofReal (cbNorm j (movb2_G d s ρ v))
      ≤ ENNReal.ofReal ((j + 2) * (Fb * E)) + ENNReal.ofReal ((j + 1) * (C2 * E)) :=
        add_le_add hcbv (ENNReal.ofReal_le_ofReal hcb)
    _ = ENNReal.ofReal ((j + 2) * (Fb * E) + (j + 1) * (C2 * E)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ = ENNReal.ofReal (((j + 2) * Fb + (j + 1) * C2) * (2 ^ (j + 2) * Cψ) * M) := by
        congr 1; rw [hE]; ring

/-! ### The tie with the frozen statement -/

/-- **`mov_operators_force_proof`**: the frozen statement `HRS.Whole.mov_operators_force` (S6.1, third assertion). -/
theorem mov_operators_force_proof {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ)
    (hβ : 0 < β) (hq : 0 < q) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ)
    (j : ℕ) (m : ℝ) (hm : (d : ℝ) / 2 + j + 4 < m) :
    ∃ C : ℝ, ∀ v : SchwartzMap (Euc d) ℝ,
      ContDiff ℝ (j + 1) (movForce d s (fun x => Real.sqrt (ρ x) * v x)) ∧
      MemCb j (fun x => movDiv (movForce d s (fun y => Real.sqrt (ρ y) * v y)) x +
        inner ℝ (gradient (fun y => Real.log (ρ y)) x)
          (movForce d s (fun y => Real.sqrt (ρ y) * v y) x)) ∧
      cbNormVecE (j + 1) (movForce d s (fun x => Real.sqrt (ρ x) * v x)) +
        ENNReal.ofReal (cbNorm j (fun x => movDiv (movForce d s (fun y => Real.sqrt (ρ y) * v y)) x +
          inner ℝ (gradient (fun y => Real.log (ρ y)) x)
            (movForce d s (fun y => Real.sqrt (ρ y) * v y) x))) ≤
        ENNReal.ofReal (C * oscNorm m v) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨B, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd hq hβ hρ
  have hq' : 0 < β * q := mul_pos hβ hq
  obtain ⟨hψs, hgrad, c, hc, hψb⟩ := HRS.MS.Mov0.mv0_sqrt_gauss hq' hR
  obtain ⟨hdlog, M0, hM0⟩ := HRS.MS.Mov0.mv0_dlog_bounds hq'.le hR
  have hM00 : 0 ≤ M0 := by
    have := hM0 0
    simp only [norm_zero, mul_zero, zero_add] at this
    exact (norm_nonneg _).trans this
  have hfs : ContDiff ℝ ∞ (fun x => gradient (fun y => Real.log (ρ y)) x) := by
    have : (fun x => gradient (fun y => Real.log (ρ y)) x) = fun x => (-(β * q)) • x + B x :=
      funext hgrad
    rw [this]
    exact (contDiff_id.const_smul (-(β * q))).add (HRS.MS.Mov0.mov0_B_smooth hR)
  obtain ⟨C0, hC00, hC0⟩ := mov_operators_force_gen hd1 hs0 hsd hc hq'.le hM00 hψs hψb hfs hM0 hdlog j
  -- the Sobolev embedding
  set n : ℕ := ⌊(d : ℝ) / 2⌋₊ + j + 3 with hn
  have hfl : (d : ℝ) / 2 < (⌊(d : ℝ) / 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hnm : (n : ℝ) ≤ m := by
    have h1 : (⌊(d : ℝ) / 2⌋₊ : ℝ) ≤ (d : ℝ) / 2 := Nat.floor_le (by positivity)
    rw [hn]; push_cast; linarith
  have hemb : ∀ k : ℕ, ∃ Ck : ℝ, 0 ≤ Ck ∧ ((k : ℝ) + d / 2 < n → ∀ (f : SchwartzMap (Euc d) ℝ) (x : Euc d),
      ‖iteratedFDeriv ℝ k f x‖ ≤ Ck * oscNorm n f) := fun k => by
    by_cases hk : (k : ℝ) + d / 2 < n
    · obtain ⟨C, hC0, hC⟩ := HRS.MS.MovOsc.mo_sobolev_emb (d := d) k n hk
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h => absurd h hk⟩
  choose Ck hCk0 hCk using hemb
  set Cm : ℝ := ∑ k ∈ Finset.range (j + 3), Ck k with hCm
  have hCm0 : 0 ≤ Cm := Finset.sum_nonneg fun k _ => hCk0 k
  refine ⟨C0 * Cm, fun v => ?_⟩
  have hosc0 : 0 ≤ oscNorm m v := Real.sqrt_nonneg _
  have hmono : oscNorm (n : ℝ) v ≤ oscNorm m v :=
    (HRS.MS.MovOsc.mo_mono hnm (memOsc_schwartz m v)).2
  have hvb : ∀ k ≤ j + 2, ∀ x : Euc d, ‖iteratedFDeriv ℝ k v x‖ ≤ Cm * oscNorm m v := fun k hk x => by
    have hkn : (k : ℝ) + d / 2 < n := by
      have : (k : ℝ) ≤ j + 2 := by exact_mod_cast hk
      rw [hn]; push_cast; linarith
    have hCkm : Ck k ≤ Cm := Finset.single_le_sum (f := Ck) (fun k _ => hCk0 k)
      (Finset.mem_range.2 (by omega))
    exact (hCk k hkn v x).trans (mul_le_mul hCkm hmono (Real.sqrt_nonneg _) hCm0)
  obtain ⟨h1, h2, h3⟩ := hC0 v (Cm * oscNorm m v) (mul_nonneg hCm0 hosc0) (v.smooth _) hvb
  refine ⟨by exact_mod_cast h1, h2, ?_⟩
  have := h3
  rwa [← mul_assoc] at this

end HRS.MS.MovForce

/-- Tie: `mov_operators_force_proof` has exactly the type of the frozen statement. -/
example := (@HRS.MS.MovForce.mov_operators_force_proof : type_of% @HRS.Whole.mov_operators_force)

end
