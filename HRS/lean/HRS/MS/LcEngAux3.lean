import HRS.MS.LcEngAux2

/-!
# LC-4, part 3: the engine `lc_engine` (supplement S4.11/S4.12)

**Statement** (`lc_engine`, shared by `local_decay` and `adjoint_decay`).  Let `Q` be a matrix, `s ≥ 0`,
`k : ℕ`, `T, ν*, b, Λc, ΛB` reals with `b > 0`.  There is a constant `C` (quantified before everything
else; depending only on `d, s, Q, k, T, ν*, b, Λc, ΛB`) such that for every probability space with a
Brownian filtration `(P, ℱ, W)`, every continuous `ν` with `0 ≤ ν ≤ ν*`, every data `c, B` with
`LcHyp Q k Λc ΛB c B` and `decayNormVecE (k+1) (s+1) (B v) ≤ ofReal ΛB` for all `v ≥ 0`, every
`0 ≤ r ≤ t ≤ T` and every `g ∈ C^k` with `decayNormE k b g < ⊤`:
`lcSg P W ν Q c B r t g` is `C^k` and `decayNormE k b (lcSg P W ν Q c B r t g) ≤ ofReal C * decayNormE k b g`.

Statement adjustments relative to `docs/S4_PLAN.md` section 2.1 (all harmless):
* the hypotheses on `c, B` are those of `LcHyp` and the decay hypothesis for ALL times `v ≥ 0`
  (`lcFlow` is defined through a global solution, so the data must be controlled for all `v ≥ 0`; a
  consumer with data on `[0,T]` only applies the engine to `c (min · T), B (min · T)` through
  `lcHyp_clamp`, `lcDecay_clamp`; on `[0,T]` the drift is unchanged, `lcB_clamp_eq`);
* the plan's hypotheses `hd : 2 ≤ d` and `hk : 1 ≤ k` are not needed and are dropped (the statement is
  stronger); the test function `g` is only `C^k` (`ContDiff ℝ k g`), as in the plan;
* `d` is implicit (determined by `Q`).

Proof.  Pathwise, `lc_chain_decay` bounds `⟨x⟩^{b+j} ‖D^j (g ∘ X_t^{r,·})(x)‖ ≤ C (1+κ)^N ‖g‖_{k,b}` with
`κ = C_U · sup_{v ≤ T}‖G_v‖` (`lc_U_bound`).  The factor `(1+κ)^N ≤ A^N (1 + sup‖G‖)^N` is integrable with
integral `≤ C_m` (`lc_sup_moment`).  Differentiation under `E` with this integrable majorant
(`lc4_iteratedFDeriv_integral`; joint measurability `lc4_meas_flow`) gives `C^k` and the formula
`D^j lcSg = E D^j (g ∘ X)`, hence the bound.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open HRS HRS.Whole HRS.MD.EQLawPath

noncomputable section

universe u

namespace HRS.MS.Lc

variable {d : ℕ}

/-- **LC-4 (engine).**  See the file docstring. -/
theorem lc_engine (s : ℝ) (hs : 0 ≤ s) (Q : Matrix (Fin d) (Fin d) ℝ) (k : ℕ)
    (T νstar bexp Λc ΛB : ℝ) (hb : 0 < bexp) :
    ∃ C : ℝ, ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ) (ν : ℝ → ℝ) (c : ℝ → Euc d)
      (B : ℝ → Euc d → Euc d),
      IsBrownianFiltration P ℱ W → Continuous ν → (∀ r, 0 ≤ ν r ∧ ν r ≤ νstar) →
      LcHyp Q k Λc ΛB c B →
      (∀ v, 0 ≤ v → decayNormVecE (k + 1) (s + 1) (B v) ≤ ENNReal.ofReal ΛB) →
      ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T →
      ∀ g : Euc d → ℝ, ContDiff ℝ (k : WithTop ℕ∞) g → decayNormE k bexp g < ⊤ →
        ContDiff ℝ (k : WithTop ℕ∞) (lcSg P W ν Q c B r t g) ∧
        decayNormE k bexp (lcSg P W ν Q c B r t g) ≤ ENNReal.ofReal C * decayNormE k bexp g := by
  obtain ⟨C0, hC01, N, hN⟩ := lc_chain_decay Q k s hs T Λc ΛB bexp hb.le
  obtain ⟨Cm, hCm⟩ := lc_sup_moment.{u} d N T νstar
  obtain ⟨Cu, hCu0, hCu⟩ := lc_U_bound Q T
  set A : ℝ := max 1 Cu with hA
  have hA1 : 1 ≤ A := le_max_left _ _
  have hAu : Cu ≤ A := le_max_right _ _
  have hAN : 1 ≤ A ^ N := one_le_pow₀ hA1
  refine ⟨C0 * A ^ N * max Cm 0, ?_⟩
  intro Ω mΩ P hP ℱ W ν c B hW hν hν' H hdec r t hr hrt htT g hg hgfin
  set G : Ω → ℝ → Euc d := fun ω v => lcNoiseE W ν v ω with hGdef
  have hGm : ∀ v, Measurable fun ω => G ω v := fun v => lc_noiseE_measurable hW v
  have hGc : ∀ ω, Continuous (G ω) := fun ω => lc_noiseE_cont hW hν ω
  set S : Ω → ℝ := fun ω => ⨆ v ∈ Icc (0 : ℝ) T, ‖lcNoiseE W ν v ω‖ with hSdef
  have hSm : Measurable S := lc_noise_sup_measurable hW hν T
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω => lc3_sup_nonneg (g := fun v => lcNoiseE W ν v ω) T
  obtain ⟨hint, hmom⟩ := hCm P ℱ W ν hW hν hν'
  set Gr : ℝ := (decayNormE k bexp g).toReal with hGr
  have hGr0 : 0 ≤ Gr := ENNReal.toReal_nonneg
  have hGe : decayNormE k bexp g = ENNReal.ofReal Gr := (ENNReal.ofReal_toReal hgfin.ne).symm
  set K0 : ℝ := C0 * A ^ N * Gr with hK0
  have hK00 : 0 ≤ K0 := by
    have : 0 ≤ C0 := by linarith
    positivity
  set Φ : Ω → ℝ := fun ω => K0 * (1 + S ω) ^ N with hΦdef
  have hΦint : Integrable Φ P := hint.const_mul K0
  -- the pathwise bound
  set G' : Ω → Euc d → ℝ := fun ω y => g (lcFlow Q c B (G ω) r t y) with hG'
  have hpt : ∀ ω, ∀ j ≤ k, ∀ x, jbracket x ^ (bexp + (j : ℝ)) *
      ‖iteratedFDeriv ℝ j (G' ω) x‖ ≤ Φ ω := by
    intro ω j hj x
    have hκ : ∀ u ∈ Icc r t, ‖lcU Q (G ω) r u‖ ≤ Cu * S ω := fun u hu =>
      hCu (hGc ω) r u hr hu.1 (hu.2.trans htT)
    have h1 := hN c B H hdec (G ω) (hGc ω) r t (Cu * S ω) hr hrt htT hκ g hg j hj x
    have hS1 := hS0 ω
    have hbase : 0 ≤ 1 + Cu * S ω := by positivity
    have hle : 1 + Cu * S ω ≤ A * (1 + S ω) := by nlinarith
    have hpow : (1 + Cu * S ω) ^ N ≤ A ^ N * (1 + S ω) ^ N := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hbase hle N
    rw [hGe, ← ENNReal.ofReal_mul (by positivity)] at h1
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
    refine h2.trans ?_
    calc C0 * (1 + Cu * S ω) ^ N * Gr ≤ C0 * (A ^ N * (1 + S ω) ^ N) * Gr := by
          gcongr
      _ = Φ ω := by rw [hΦdef, hK0]; ring
  have hGfun : ∀ ω, ContDiff ℝ (k : WithTop ℕ∞) (G' ω) := fun ω =>
    hg.comp ((lcFlow_contDiff H (hGc ω) hr hrt).of_le (by exact_mod_cast Nat.le_succ k))
  have hbd : ∀ i ≤ k, ∀ ω x, ‖iteratedFDeriv ℝ i (G' ω) x‖ ≤ Φ ω := by
    intro i hi ω x
    have h1 := hpt ω i hi x
    have hjb : 1 ≤ jbracket x ^ (bexp + (i : ℝ)) :=
      Real.one_le_rpow (lc2_jb_ge_one x) (by positivity)
    have : 0 ≤ ‖iteratedFDeriv ℝ i (G' ω) x‖ := norm_nonneg _
    nlinarith
  have hjoint : StronglyMeasurable (fun p : Ω × Euc d => G' p.1 p.2) :=
    (hg.continuous.measurable.comp (lc4_meas_flow H hGm hGc hr hrt)).stronglyMeasurable
  have hmeas : ∀ i ≤ k, ∀ x, AEStronglyMeasurable (fun ω => iteratedFDeriv ℝ i (G' ω) x) P := by
    intro i hi x
    have := PoisSg.sg_stronglyMeasurable_iteratedFDeriv G' hjoint i
      (fun ω => (hGfun ω).of_le (by exact_mod_cast hi))
    exact (this.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  obtain ⟨hcd, hform⟩ := lc4_iteratedFDeriv_integral (μ := P) G' k hGfun hΦint hbd hmeas
  have hSg : lcSg P W ν Q c B r t g = fun x => ∫ ω, G' ω x ∂P := rfl
  rw [hSg]
  refine ⟨hcd, ?_⟩
  -- the bound
  have hCpos : 0 ≤ C0 * A ^ N * max Cm 0 := by
    have : 0 ≤ C0 := by linarith
    positivity
  have hmain : ∀ j ≤ k, ∀ x : Euc d, jbracket x ^ (bexp + (j : ℝ)) *
      ‖iteratedFDeriv ℝ j (fun x => ∫ ω, G' ω x ∂P) x‖ ≤ (C0 * A ^ N * max Cm 0) * Gr := by
    intro j hj x
    rw [hform j hj x]
    have hjb : 0 ≤ jbracket x ^ (bexp + (j : ℝ)) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    calc jbracket x ^ (bexp + (j : ℝ)) * ‖∫ ω, iteratedFDeriv ℝ j (G' ω) x ∂P‖
        ≤ jbracket x ^ (bexp + (j : ℝ)) * ∫ ω, ‖iteratedFDeriv ℝ j (G' ω) x‖ ∂P :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hjb
      _ = ∫ ω, jbracket x ^ (bexp + (j : ℝ)) * ‖iteratedFDeriv ℝ j (G' ω) x‖ ∂P :=
          (integral_const_mul _ _).symm
      _ ≤ ∫ ω, Φ ω ∂P := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun ω => ?_) hΦint
            (Eventually.of_forall fun ω => hpt ω j hj x)
          exact mul_nonneg hjb (norm_nonneg _)
      _ = K0 * ∫ ω, (1 + S ω) ^ N ∂P := integral_const_mul _ _
      _ ≤ K0 * max Cm 0 := mul_le_mul_of_nonneg_left (hmom.trans (le_max_left _ _)) hK00
      _ = (C0 * A ^ N * max Cm 0) * Gr := by rw [hK0]; ring
  refine (lc4_decayNormE_le hmain).trans ?_
  rw [hGe, ← ENNReal.ofReal_mul hCpos]

end HRS.MS.Lc
