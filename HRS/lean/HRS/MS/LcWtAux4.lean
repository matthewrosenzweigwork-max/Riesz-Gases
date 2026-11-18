import HRS.MS.LcWtAux3

/-!
# LC-2, part 4: the chain rule count and the final statements `lc_weights`, `lc_chain_decay`

* `lc2_decay_op_scalar`: `decayNormE m b f ≤ ofReal Λ'` gives `⟨x⟩^{b+j} ‖D^j f(x)‖ ≤ d^j Λ'`.
* `lc2_chain_sum`: Faà di Bruno for `f ∘ X` at a point, with decay bounds on `D^ℓ f(X x)` and on the
  variations `D^a X(x)`; the exponent count is `lc2_comb` (TeX S L3040-3050).
* `lc_weights` and `lc_chain_decay`: the two statements consumed by LC-4 and the adjoint decay proof.

## Statements (LC-2 contract)

Data: `LcHyp Q k Λc ΛB c B` (LC-1), the decay hypothesis
`∀ v ≥ 0, decayNormVecE (k+1) (s+1) (B v) ≤ ofReal ΛB` (as in `HRS.Whole.local_decay`; for data given on
`[0,T]` only use `lcHyp_clamp` and `lcDecay_clamp`, which replace `c v, B v` by `c (min v T), B (min v T)`),
a continuous noise path `g`, `0 ≤ r ≤ v ≤ T`, and any `κ` with `‖lcU Q g r u‖ ≤ κ` for `u ∈ [r, v]`
(an upper bound instead of the supremum, so that the consumer may take `κ = sup` itself or any
measurable majorant; the statements are monotone in `κ`).  The constants `C, N` are quantified before
the data and depend only on `d, Q, k, s, T, Λc, ΛB` (and `b` for the chain decay); `κ` enters only through
`(1+κ)^N`, `N : ℕ`.  Here `X_v^x = lcFlow Q c B g r v x`.

* `lc_weights` (plan step 2 (i), (ii)): `(C(1+κ))⁻¹ ⟨x⟩ ≤ ⟨X_v^x⟩ ≤ C (1+κ) ⟨x⟩` and, for
  `2 ≤ j ≤ k+1` (one order more than the plan: the flow is `C^{k+1}`, `B_v ∈ C^{k+1}` with the weighted
  norm through order `k+1`), `⟨x⟩^{s+1+j} ‖D^j X_v^x‖ ≤ C (1+κ)^N` (operator norm of the `j`-th
  derivative; `⟨x⟩ = jbracket x`).
* `lc_chain_decay` (plan step 2 (iii)): for `b ≥ 0`, `f ∈ C^k`, `0 ≤ j ≤ k`, all `x`:
  `ofReal (⟨x⟩^{b+j} ‖D^j (f ∘ X_v)(x)‖) ≤ ofReal (C (1+κ)^N) * decayNormE k b f` in `ℝ≥0∞`
  (`decayNormE k b f` may be `⊤`, then the bound is vacuous; `C ≥ 1` so the right side is never `0 * ⊤`).
  The operator norm of `D^j (f ∘ X)` is bounded by the supremum norm over index tuples of
  `decayNormE`, at the price of the constant `d^j` (`lc2_ml_bound`).  `b > 0` of `local_decay` is
  only used through `b ≥ 0`.

Differences from the sketch of `docs/S4_PLAN.md`: `κ` is an upper bound, `j` ranges to `k+1` in (ii),
the decay hypothesis is the one of `local_decay` (so no operator-norm form is assumed), `s ≥ 0`
(`hs`) is needed for the exponent count `lc2_comb`.  No statement is vacuous (`B = 0, c = 0, g = 0`
satisfy all hypotheses) and no Bochner/`tsum`/`log` junk value enters.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

noncomputable section

namespace HRS.MS.Lc

variable {d : ℕ}

/-- From the weighted norm `decayNormE m b f ≤ ofReal Λ'` of a scalar function to operator norms. -/
theorem lc2_decay_op_scalar {m : ℕ} {b Λ' : ℝ} {f : Euc d → ℝ} (hΛ' : 0 ≤ Λ')
    (h : decayNormE m b f ≤ ENNReal.ofReal Λ') (j : ℕ) (hj : j ≤ m) (x : Euc d) :
    jbracket x ^ (b + (j : ℝ)) * ‖iteratedFDeriv ℝ j f x‖ ≤ (d : ℝ) ^ j * Λ' := by
  have hw : 0 < jbracket x ^ (b + (j : ℝ)) := Real.rpow_pos_of_pos (lc2_jb_pos x) _
  set w := jbracket x ^ (b + (j : ℝ)) with hwdef
  have hcomp : ∀ idx : Fin j → Fin d,
      |iteratedFDeriv ℝ j f x (fun l => EuclideanSpace.single (idx l) 1)| ≤ Λ' / w := by
    intro idx
    rw [le_div_iff₀ hw, mul_comm]
    have hle : ENNReal.ofReal (w * |partialDeriv idx f x|) ≤ ENNReal.ofReal Λ' := by
      refine le_trans ?_ h
      unfold decayNormE derivSupE
      refine le_trans ?_ (le_iSup _ ⟨j, by omega⟩)
      refine le_trans ?_ (le_iSup _ idx)
      refine le_trans ?_ (le_iSup _ x)
      exact le_rfl
    exact (ENNReal.ofReal_le_ofReal_iff hΛ').1 hle
  have hM := lc2_ml_bound (iteratedFDeriv ℝ j f x) (div_nonneg hΛ' hw.le) hcomp
  calc w * ‖iteratedFDeriv ℝ j f x‖ ≤ w * ((d : ℝ) ^ j * (Λ' / w)) :=
        mul_le_mul_of_nonneg_left hM hw.le
    _ = (d : ℝ) ^ j * Λ' := by field_simp

/-- Faà di Bruno at a point with weighted bounds on both factors. -/
theorem lc2_chain_sum {X : Euc d → Euc d} {f : Euc d → ℝ} {k : ℕ}
    (hf : ContDiff ℝ (k : WithTop ℕ∞) f) (hX : ContDiff ℝ (k : WithTop ℕ∞) X) {j : ℕ}
    (hj1 : 1 ≤ j) (hjk : j ≤ k) (x : Euc d) {F Kt b σ ω : ℝ} (hF : 0 ≤ F) (hK : 1 ≤ Kt)
    (hσ : 0 ≤ σ) (hω0 : 0 < ω) (hω1 : ω ≤ 1)
    (hq : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ j → ‖iteratedFDeriv ℝ ℓ f (X x)‖ ≤ F * ω ^ (b + (ℓ : ℝ)))
    (hp : ∀ a : ℕ, 1 ≤ a → a ≤ j → ‖iteratedFDeriv ℝ a X x‖ ≤ Kt * ω ^ (lc2_e σ a)) :
    ‖iteratedFDeriv ℝ j (f ∘ X) x‖ ≤
      Fintype.card (OrderedFinpartition j) * (F * Kt ^ j * ω ^ (b + (j : ℝ))) := by
  classical
  have hjn : (j : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hjk
  have hcomp : HasFTaylorSeriesUpTo (k : WithTop ℕ∞) (f ∘ X)
      (fun y => (ftaylorSeries ℝ f (X y)).taylorComp (ftaylorSeries ℝ X y)) :=
    hasFTaylorSeriesUpToOn_univ_iff.1
      (HasFTaylorSeriesUpToOn.comp (hasFTaylorSeriesUpToOn_univ_iff.2 hf.ftaylorSeries)
        (hasFTaylorSeriesUpToOn_univ_iff.2 hX.ftaylorSeries) (mapsTo_univ _ _))
  have hD := hcomp.eq_iteratedFDeriv hjn x
  rw [← hD]
  unfold FormalMultilinearSeries.taylorComp
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ c : OrderedFinpartition j,
      ‖(ftaylorSeries ℝ f (X x)).compAlongOrderedFinpartition (ftaylorSeries ℝ X x) c‖ ≤
        F * Kt ^ j * ω ^ (b + (j : ℝ)) := by
    intro c
    have hlen1 : 1 ≤ c.length := c.length_pos hj1
    have hlenj : c.length ≤ j := c.length_le
    have hcomb := lc2_comb c b hσ hω0 hω1
    have hprod : ∏ i, ‖iteratedFDeriv ℝ (c.partSize i) X x‖ ≤
        ∏ i : Fin c.length, (Kt * ω ^ (lc2_e σ (c.partSize i))) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun i _ => hp _ (c.partSize_pos i) (c.partSize_le i))
    have hpe : ∏ i : Fin c.length, (Kt * ω ^ (lc2_e σ (c.partSize i))) =
        Kt ^ c.length * ∏ i : Fin c.length, ω ^ (lc2_e σ (c.partSize i)) := by
      rw [Finset.prod_mul_distrib]; simp
    have hqb := hq c.length hlen1 hlenj
    have hK0 : 0 ≤ Kt := by linarith
    calc ‖(ftaylorSeries ℝ f (X x)).compAlongOrderedFinpartition (ftaylorSeries ℝ X x) c‖
        ≤ ‖ftaylorSeries ℝ f (X x) c.length‖ *
            ∏ i, ‖ftaylorSeries ℝ X x (c.partSize i)‖ :=
          c.norm_compAlongOrderedFinpartition_le _ _
      _ ≤ (F * ω ^ (b + (c.length : ℝ))) *
            (Kt ^ c.length * ∏ i : Fin c.length, ω ^ (lc2_e σ (c.partSize i))) := by
          rw [← hpe]
          exact mul_le_mul hqb hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _)
            (mul_nonneg hF (Real.rpow_nonneg hω0.le _))
      _ = F * Kt ^ c.length * (ω ^ (b + (c.length : ℝ)) *
            ∏ i : Fin c.length, ω ^ (lc2_e σ (c.partSize i))) := by ring
      _ ≤ F * Kt ^ j * ω ^ (b + (j : ℝ)) := by
          have h1 : F * Kt ^ c.length ≤ F * Kt ^ j :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK hlenj) hF
          have h2 : 0 ≤ ω ^ (b + (c.length : ℝ)) *
              ∏ i : Fin c.length, ω ^ (lc2_e σ (c.partSize i)) :=
            mul_nonneg (Real.rpow_nonneg hω0.le _)
              (Finset.prod_nonneg fun _ _ => Real.rpow_nonneg hω0.le _)
          exact mul_le_mul h1 hcomb h2 (mul_nonneg hF (pow_nonneg hK0 _))
  calc ∑ c : OrderedFinpartition j,
        ‖(ftaylorSeries ℝ f (X x)).compAlongOrderedFinpartition (ftaylorSeries ℝ X x) c‖
      ≤ ∑ _c : OrderedFinpartition j, F * Kt ^ j * ω ^ (b + (j : ℝ)) :=
        Finset.sum_le_sum fun c _ => hterm c
    _ = Fintype.card (OrderedFinpartition j) * (F * Kt ^ j * ω ^ (b + (j : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Scaling of a weighted bound when the bracket changes by a factor. -/
theorem lc2_scale {x y : Euc d} {a e u R : ℝ} (hu : 0 ≤ u) (ha : 0 ≤ a) (he : 0 ≤ e)
    (hxy : jbracket x ≤ a * jbracket y) (h : u * jbracket y ^ e ≤ R) :
    u * jbracket x ^ e ≤ a ^ e * R := by
  have h1 : jbracket x ^ e ≤ a ^ e * jbracket y ^ e := by
    rw [← Real.mul_rpow ha (lc2_jb_pos y).le]
    exact Real.rpow_le_rpow (lc2_jb_pos x).le hxy he
  calc u * jbracket x ^ e ≤ u * (a ^ e * jbracket y ^ e) := by gcongr
    _ = a ^ e * (u * jbracket y ^ e) := by ring
    _ ≤ a ^ e * R := by gcongr

/-- **LC-2 (weights).**  Under `LcHyp Q k Λc ΛB c B` and the decay hypothesis
`decayNormVecE (k+1) (s+1) (B v) ≤ ofReal ΛB` (`v ≥ 0`), for every continuous noise path `g`,
`0 ≤ r ≤ v ≤ T` and every `κ` with `‖lcU Q g r u‖ ≤ κ` on `[r, v]`:
(i) `⟨X_v^x⟩ ≍ (1+κ)^{±1} ⟨x⟩` and (ii) `⟨x⟩^{s+1+j} ‖D^j X_v^x‖ ≤ C (1+κ)^N`, `2 ≤ j ≤ k+1`
(`X_v^x = lcFlow Q c B g r v x`).  `C, N` depend only on `d, Q, k, s, T, Λc, ΛB`. -/
theorem lc_weights (Q : Matrix (Fin d) (Fin d) ℝ) (k : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (T Λc ΛB : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N : ℕ, ∀ (c : ℝ → Euc d) (B : ℝ → Euc d → Euc d),
      LcHyp Q k Λc ΛB c B →
      (∀ v, 0 ≤ v → decayNormVecE (k + 1) (s + 1) (B v) ≤ ENNReal.ofReal ΛB) →
      ∀ g : ℝ → Euc d, Continuous g → ∀ r v κ : ℝ, 0 ≤ r → r ≤ v → v ≤ T →
      (∀ u ∈ Icc r v, ‖lcU Q g r u‖ ≤ κ) → ∀ x : Euc d,
        (C * (1 + κ))⁻¹ * jbracket x ≤ jbracket (lcFlow Q c B g r v x) ∧
        jbracket (lcFlow Q c B g r v x) ≤ C * (1 + κ) * jbracket x ∧
        ∀ j : ℕ, 2 ≤ j → j ≤ k + 1 →
          jbracket x ^ (s + 1 + (j : ℝ)) * ‖iteratedFDeriv ℝ j (lcFlow Q c B g r v) x‖ ≤
            C * (1 + κ) ^ N := by
  obtain ⟨C2, hC21, N, hN⟩ := lc2_weights_deriv Q k s hs T Λc ΛB
  refine ⟨max (2 * Real.exp (lcLam Q Λc ΛB * T)) C2,
    hC21.trans (le_max_right _ _), N, ?_⟩
  intro c B H hdec g hg r v κ hr hrv hvT hκ x
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ v ⟨hrv, le_rfl⟩)
  have hcomp := lc2_jb_comp H hg hr hrv (T := T) (by linarith) hκ x
  set C := max (2 * Real.exp (lcLam Q Λc ΛB * T)) C2 with hC
  have hAC : 2 * Real.exp (lcLam Q Λc ΛB * T) ≤ C := le_max_left _ _
  have hC0 : 0 < C := lt_of_lt_of_le one_pos (hC21.trans (le_max_right _ _))
  have hk1 : 0 < 1 + κ := by linarith
  have hjx := lc2_jb_pos x
  have hjX := lc2_jb_pos (lcFlow Q c B g r v x)
  refine ⟨?_, ?_, ?_⟩
  · rw [inv_mul_le_iff₀ (by positivity)]
    refine hcomp.2.trans ?_
    gcongr
  · refine hcomp.1.trans ?_
    gcongr
  · intro j hj2 hjk
    refine (hN c B H hdec g hg r v κ hr hrv hvT hκ j hj2 hjk x).trans ?_
    gcongr
    exact le_max_right _ _

/-- Time clamp for the decay hypothesis: data given on `[0,T]` only. -/
theorem lcDecay_clamp {B : ℝ → Euc d → Euc d} {k : ℕ} {σ ΛB T : ℝ} (hT : 0 ≤ T)
    (h : ∀ t ∈ Icc 0 T, decayNormVecE (k + 1) σ (B t) ≤ ENNReal.ofReal ΛB) :
    ∀ v, 0 ≤ v → decayNormVecE (k + 1) σ (B (min v T)) ≤ ENNReal.ofReal ΛB :=
  fun v hv => h _ ⟨le_min hv hT, min_le_right _ _⟩

theorem lc2_inv_form {x : Euc d} {u R e : ℝ} (h : u * jbracket x ^ e ≤ R) :
    u ≤ R * ((jbracket x)⁻¹) ^ e := by
  have hw : 0 < jbracket x ^ e := Real.rpow_pos_of_pos (lc2_jb_pos x) _
  rw [Real.inv_rpow (lc2_jb_pos x).le, ← div_eq_mul_inv, le_div_iff₀ hw]
  exact h

/-- **LC-2 (chain rule decay).**  Same data as `lc_weights`; for `b ≥ 0`, `f ∈ C^k` and `0 ≤ j ≤ k`,
`⟨x⟩^{b+j} ‖D^j (f ∘ X_v)(x)‖ ≤ C (1+κ)^N ‖f‖_{k,b}` (in `ℝ≥0∞`; `‖f‖_{k,b} = decayNormE k b f` may
be `⊤`).  `C, N` depend only on `d, Q, k, s, T, Λc, ΛB, b`. -/
theorem lc_chain_decay (Q : Matrix (Fin d) (Fin d) ℝ) (k : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (T Λc ΛB b : ℝ) (hb : 0 ≤ b) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N : ℕ, ∀ (c : ℝ → Euc d) (B : ℝ → Euc d → Euc d),
      LcHyp Q k Λc ΛB c B →
      (∀ v, 0 ≤ v → decayNormVecE (k + 1) (s + 1) (B v) ≤ ENNReal.ofReal ΛB) →
      ∀ g : ℝ → Euc d, Continuous g → ∀ r v κ : ℝ, 0 ≤ r → r ≤ v → v ≤ T →
      (∀ u ∈ Icc r v, ‖lcU Q g r u‖ ≤ κ) →
      ∀ f : Euc d → ℝ, ContDiff ℝ (k : WithTop ℕ∞) f → ∀ j : ℕ, j ≤ k → ∀ x : Euc d,
        ENNReal.ofReal (jbracket x ^ (b + (j : ℝ)) *
            ‖iteratedFDeriv ℝ j (f ∘ lcFlow Q c B g r v) x‖) ≤
          ENNReal.ofReal (C * (1 + κ) ^ N) * decayNormE k b f := by
  classical
  obtain ⟨C2, hC21, N2, hN2⟩ := lc2_weights_deriv Q k s hs T Λc ΛB
  set Λ0 := lcLam Q Λc ΛB with hΛ0
  set A : ℝ := 2 * Real.exp (Λ0 * T) with hA
  set M' : ℕ := ⌈b⌉₊ + k with hM'
  set E1 : ℝ := Real.exp (Λ0 * T) + C2 with hE1
  set Cc : ℝ := ∑ i ∈ Finset.range (k + 1), (Fintype.card (OrderedFinpartition i) : ℝ) with hCc
  set Ctot : ℝ := Cc * ((d : ℝ) + 1) ^ k * A ^ M' * E1 ^ k with hCtot
  refine ⟨max 1 Ctot, le_max_left _ _, M' + N2 * k, ?_⟩
  intro c B H hdec g hg r v κ hr hrv hvT hκ f hf j hjk x
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ v ⟨hrv, le_rfl⟩)
  have hT0 : 0 ≤ T := hr.trans (hrv.trans hvT)
  have hΛ0nn : 0 ≤ Λ0 := H.lam_nonneg
  have hexp1 : 1 ≤ Real.exp (Λ0 * T) := Real.one_le_exp (mul_nonneg hΛ0nn hT0)
  have hA1 : 1 ≤ A := by rw [hA]; linarith
  set κ1 : ℝ := 1 + κ with hκ1
  have hκ11 : 1 ≤ κ1 := by linarith
  have hAκ : 1 ≤ A * κ1 := one_le_mul_of_one_le_of_one_le hA1 hκ11
  set C : ℝ := max 1 Ctot with hC
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCc1 : 1 ≤ Cc := by
    have h0 : (1 : ℝ) ≤ Fintype.card (OrderedFinpartition 0) := by
      exact Nat.one_le_cast.2 Fintype.card_pos
    refine h0.trans ?_
    rw [hCc]
    exact Finset.single_le_sum (f := fun i => (Fintype.card (OrderedFinpartition i) : ℝ))
      (fun i _ => Nat.cast_nonneg _) (Finset.mem_range.2 (Nat.succ_pos k))
  have hE11 : 1 ≤ E1 := by rw [hE1]; linarith
  have hd1 : 1 ≤ (d : ℝ) + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hCpos : 0 < C * κ1 ^ (M' + N2 * k) := by positivity
  by_cases hG : decayNormE k b f = ⊤
  · rw [hG, ENNReal.mul_top (ENNReal.ofReal_pos.2 hCpos).ne']
    exact le_top
  have hGe : decayNormE k b f = ENNReal.ofReal (decayNormE k b f).toReal :=
    (ENNReal.ofReal_toReal hG).symm
  set Gr : ℝ := (decayNormE k b f).toReal with hGr
  have hGr0 : 0 ≤ Gr := ENNReal.toReal_nonneg
  rw [hGe, ← ENNReal.ofReal_mul hCpos.le]
  refine ENNReal.ofReal_le_ofReal ?_
  set X : Euc d → Euc d := lcFlow Q c B g r v with hX
  -- the full constant
  set Ufull : ℝ := Cc * ((d : ℝ) + 1) ^ k * (A * κ1) ^ M' * (E1 * κ1 ^ N2) ^ k with hUfull
  have hUC : Ufull ≤ C * κ1 ^ (M' + N2 * k) := by
    have e1 : (A * κ1) ^ M' = A ^ M' * κ1 ^ M' := mul_pow _ _ _
    have e2 : (E1 * κ1 ^ N2) ^ k = E1 ^ k * κ1 ^ (N2 * k) := by rw [mul_pow, ← pow_mul]
    have e : Ufull = Ctot * κ1 ^ (M' + N2 * k) := by
      rw [hUfull, hCtot, e1, e2, pow_add]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hU1 : (A * κ1) ^ M' ≤ Ufull := by
    have h1 : 1 ≤ Cc * ((d : ℝ) + 1) ^ k := one_le_mul_of_one_le_of_one_le hCc1 (one_le_pow₀ hd1)
    have h2 : 1 ≤ (E1 * κ1 ^ N2) ^ k :=
      one_le_pow₀ (one_le_mul_of_one_le_of_one_le hE11 (one_le_pow₀ hκ11))
    rw [hUfull]
    have hX0 : 0 ≤ (A * κ1) ^ M' := by positivity
    calc (A * κ1) ^ M' = 1 * (A * κ1) ^ M' * 1 := by ring
      _ ≤ (Cc * ((d : ℝ) + 1) ^ k) * (A * κ1) ^ M' * (E1 * κ1 ^ N2) ^ k :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1 hX0) h2 zero_le_one
            (mul_nonneg (le_trans zero_le_one h1) hX0)
  -- decay of f
  have hq0 : ∀ ℓ : ℕ, ℓ ≤ k → ∀ y : Euc d,
      ‖iteratedFDeriv ℝ ℓ f y‖ * jbracket y ^ (b + (ℓ : ℝ)) ≤ (d : ℝ) ^ ℓ * Gr :=
    fun ℓ hℓ y => by rw [mul_comm]; exact lc2_decay_op_scalar hGr0 hGe.le ℓ hℓ y
  have hcompx := (lc2_jb_comp H hg hr hrv (T := T) (by linarith) hκ x).2
  have hAM : ∀ ℓ : ℕ, ℓ ≤ k → (A * κ1) ^ (b + (ℓ : ℝ)) ≤ (A * κ1) ^ M' := by
    intro ℓ hℓ
    have : b + (ℓ : ℝ) ≤ (M' : ℝ) := by
      rw [hM']
      have h1 : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
      have h2 : (ℓ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hℓ
      push_cast
      linarith
    calc (A * κ1) ^ (b + (ℓ : ℝ)) ≤ (A * κ1) ^ (M' : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hAκ this
      _ = (A * κ1) ^ M' := Real.rpow_natCast _ _
  have hdk : ∀ ℓ : ℕ, ℓ ≤ k → (d : ℝ) ^ ℓ ≤ ((d : ℝ) + 1) ^ k := fun ℓ hℓ =>
    calc (d : ℝ) ^ ℓ ≤ ((d : ℝ) + 1) ^ ℓ := pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _
      _ ≤ ((d : ℝ) + 1) ^ k := pow_le_pow_right₀ hd1 hℓ
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · -- j = 0
    subst hj0
    simp only [Nat.cast_zero, add_zero, norm_iteratedFDeriv_zero, Function.comp_apply]
    have h0 := hq0 0 (Nat.zero_le _) (X x)
    simp only [Nat.cast_zero, add_zero, norm_iteratedFDeriv_zero, pow_zero, one_mul] at h0
    have h1 := lc2_scale (norm_nonneg (f (X x))) (by positivity : 0 ≤ A * κ1) hb hcompx h0
    rw [mul_comm]
    refine h1.trans ?_
    have hAb : (A * κ1) ^ b ≤ (A * κ1) ^ M' := by
      have := hAM 0 (Nat.zero_le _)
      simpa using this
    calc (A * κ1) ^ b * Gr ≤ (A * κ1) ^ M' * Gr := mul_le_mul_of_nonneg_right hAb hGr0
      _ ≤ Ufull * Gr := mul_le_mul_of_nonneg_right hU1 hGr0
      _ ≤ C * κ1 ^ (M' + N2 * k) * Gr := mul_le_mul_of_nonneg_right hUC hGr0
  · -- j ≥ 1
    have hjt : j ≤ k := hjk
    have hjb := lc2_jb_pos x
    set ω : ℝ := (jbracket x)⁻¹ with hω
    have hω0 : 0 < ω := inv_pos.2 hjb
    have hω1 : ω ≤ 1 := inv_le_one_of_one_le₀ (lc2_jb_ge_one x)
    set F : ℝ := Gr * (((d : ℝ) + 1) ^ k * (A * κ1) ^ M') with hF
    have hF0 : 0 ≤ F := by positivity
    set Kt : ℝ := Real.exp (Λ0 * T) + C2 * κ1 ^ N2 with hKt
    have hKt1 : 1 ≤ Kt := by
      have : 1 ≤ C2 * κ1 ^ N2 := one_le_mul_of_one_le_of_one_le hC21 (one_le_pow₀ hκ11)
      rw [hKt]; linarith [Real.exp_pos (Λ0 * T)]
    have hq : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ j → ‖iteratedFDeriv ℝ ℓ f (X x)‖ ≤ F * ω ^ (b + (ℓ : ℝ)) := by
      intro ℓ hℓ1 hℓj
      have hℓk : ℓ ≤ k := hℓj.trans hjt
      have h0 := hq0 ℓ hℓk (X x)
      have h1 := lc2_scale (norm_nonneg _) (by positivity : 0 ≤ A * κ1)
        (by positivity : 0 ≤ b + (ℓ : ℝ)) hcompx h0
      refine lc2_inv_form (h1.trans ?_)
      calc (A * κ1) ^ (b + (ℓ : ℝ)) * ((d : ℝ) ^ ℓ * Gr)
          ≤ (A * κ1) ^ M' * (((d : ℝ) + 1) ^ k * Gr) := by
            gcongr
            · exact hAM ℓ hℓk
            · exact hdk ℓ hℓk
        _ = F := by rw [hF]; ring
    have hp : ∀ a : ℕ, 1 ≤ a → a ≤ j → ‖iteratedFDeriv ℝ a X x‖ ≤ Kt * ω ^ (lc2_e (s + 1) a) := by
      intro a ha1 haj
      by_cases ha : a = 1
      · subst ha
        rw [lc2_e_one, Real.rpow_zero, mul_one, norm_iteratedFDeriv_one (𝕜 := ℝ)]
        have h1 := lcFlow_fderiv_le H hg hr hrv x
        refine h1.trans ?_
        have : Real.exp (Λ0 * (v - r)) ≤ Real.exp (Λ0 * T) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hΛ0nn)
        rw [hKt]
        have : 0 ≤ C2 * κ1 ^ N2 := by positivity
        linarith
      · have ha2 : 2 ≤ a := by omega
        have hak : a ≤ k + 1 := by omega
        have h1 := hN2 c B H hdec g hg r v κ hr hrv hvT hκ a ha2 hak x
        rw [lc2_e_of_ne ha]
        have h1' : ‖iteratedFDeriv ℝ a X x‖ * jbracket x ^ (s + 1 + (a : ℝ)) ≤ C2 * κ1 ^ N2 := by
          rw [mul_comm]; exact h1
        refine (lc2_inv_form h1').trans ?_
        have : 0 ≤ ω ^ (s + 1 + (a : ℝ)) := Real.rpow_nonneg hω0.le _
        have h2 : C2 * κ1 ^ N2 ≤ Kt := by
          rw [hKt]; linarith [Real.exp_pos (Λ0 * T)]
        gcongr
    have hXk : ContDiff ℝ (k : WithTop ℕ∞) X := by
      have := lcFlow_contDiff H hg hr hrv
      exact this.of_le (by exact_mod_cast Nat.le_succ k)
    have hsum := lc2_chain_sum hf hXk hj1 hjt x hF0 hKt1 (by linarith : 0 ≤ s + 1) hω0 hω1 hq hp
    -- multiply by the weight
    have hwj : 0 < jbracket x ^ (b + (j : ℝ)) := Real.rpow_pos_of_pos hjb _
    have hωj : jbracket x ^ (b + (j : ℝ)) * ω ^ (b + (j : ℝ)) = 1 := by
      rw [hω, Real.inv_rpow hjb.le, mul_inv_cancel₀ hwj.ne']
    have hcardj : (Fintype.card (OrderedFinpartition j) : ℝ) ≤ Cc :=
      Finset.single_le_sum (f := fun i => (Fintype.card (OrderedFinpartition i) : ℝ))
        (fun i _ => Nat.cast_nonneg _) (Finset.mem_range.2 (by omega))
    have hKtE : Kt ≤ E1 * κ1 ^ N2 := by
      have h1 : 1 ≤ κ1 ^ N2 := one_le_pow₀ hκ11
      rw [hKt, hE1]
      nlinarith [Real.exp_pos (Λ0 * T)]
    have hKtj : Kt ^ j ≤ (E1 * κ1 ^ N2) ^ k :=
      (pow_le_pow_right₀ hKt1 hjt).trans (pow_le_pow_left₀ (by linarith) hKtE _)
    calc jbracket x ^ (b + (j : ℝ)) * ‖iteratedFDeriv ℝ j (f ∘ X) x‖
        ≤ jbracket x ^ (b + (j : ℝ)) * (Fintype.card (OrderedFinpartition j) *
            (F * Kt ^ j * ω ^ (b + (j : ℝ)))) := mul_le_mul_of_nonneg_left hsum hwj.le
      _ = Fintype.card (OrderedFinpartition j) * (F * Kt ^ j) *
            (jbracket x ^ (b + (j : ℝ)) * ω ^ (b + (j : ℝ))) := by ring
      _ = Fintype.card (OrderedFinpartition j) * (F * Kt ^ j) := by rw [hωj, mul_one]
      _ ≤ Cc * (F * (E1 * κ1 ^ N2) ^ k) :=
          mul_le_mul hcardj (mul_le_mul_of_nonneg_left hKtj hF0) (by positivity) (by linarith)
      _ = Ufull * Gr := by rw [hUfull, hF]; ring
      _ ≤ C * κ1 ^ (M' + N2 * k) * Gr := mul_le_mul_of_nonneg_right hUC hGr0

end HRS.MS.Lc
