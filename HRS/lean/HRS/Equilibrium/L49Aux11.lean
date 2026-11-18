/-
# HRS.Equilibrium.L49Aux11 — Proposition 4.9, part 11: pointwise-in-`t` variance estimate

`l49_V_close` (`R:eq:offdiagonal-bound` and `R:eq:diagonal-reduction`): under `P_t`,
`|Var(F) - n J(tλ)| ≤ n (K₁ + K₂ √(1 + |log tλ|) + K₃ √δ_N (1 + |log tλ|))`,
`F = ∑_i g(x - y_i)`, `J(u) = ∫ g² e^{-ug} dμ`.
-/
import HRS.Equilibrium.L49Aux10

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace L49

variable {d : ℕ} {s c : ℝ}

open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp

theorem l49_abs_le_sqrt_mul {A B X : ℝ} (hA : 0 ≤ A) (hX : X ^ 2 ≤ A * B) : |X| ≤ Real.sqrt A * Real.sqrt B := by
  rw [← Real.sqrt_mul hA]
  exact Real.abs_le_sqrt hX

set_option maxHeartbeats 6400000 in
theorem l49_V_close (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) {c : ℝ} (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ K₁ K₂ K₃ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧ 0 ≤ K₃ ∧ ∀ N : ℕ, 2 ≤ N → β / N ≤ 1 → ∀ x : Torus d,
      ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      MemLp (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i)) 2 (critPole d s c β ρ N x t) ∧
      |(evariance (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i))
            (critPole d s c β ρ N x t)).toReal - ((N - 1 : ℕ) : ℝ) * l49_J d s c ρ x (t * (β / N))| ≤
        ((N - 1 : ℕ) : ℝ) * (K₁ + K₂ * Real.sqrt (1 + |Real.log (t * (β / N))|) +
          K₃ * Real.sqrt (deltaN d s N) * (1 + |Real.log (t * (β / N))|)) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨C48, h48⟩ := conditional_singular_observation_proof hd hcrit β hβ ρ hρ c hc
  obtain ⟨Cv, hCv0, hvar⟩ := l49_var_bound hd hcrit hβ hρ hc
  obtain ⟨CQ, hCQ0, hQ⟩ := l49_Q_close hd hcrit hβ hρ hc
  obtain ⟨Csl, hCsl0, hsl⟩ := l49_sqlog hd hcrit hβ hρ hc
  have hgm := measurable_gPlus hd hs0 hsd c
  set C4 : ℝ := |C48| with hC4
  have hC40 : 0 ≤ C4 := abs_nonneg _
  refine ⟨C4, Real.sqrt (Cv * C4), CQ * Csl, hC40, Real.sqrt_nonneg _, by positivity, ?_⟩
  intro N hN hlamle x t ht
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hn1 : 0 < N - 1 := by omega
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  set u : ℝ := t * (β / N) with hu
  have hu0 : 0 < u := mul_pos ht.1 (by positivity)
  have hu1 : u ≤ 1 := by
    have : t * (β / N) ≤ 1 * (β / N) := mul_le_mul_of_nonneg_right ht.2 hlam
    linarith
  set L : ℝ := |Real.log u| with hL
  have hL0 : 0 ≤ L := abs_nonneg _
  set n : ℕ := N - 1 with hn
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (by omega : N - 1 ≤ N)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set P := critPole d s c β ρ N x t with hP
  haveI hPprob : IsProbabilityMeasure P := by
    rw [hP, critPole_eq_poleLaw (c := c) hd hs0 hsd β hβ hρ hN x t]
    exact pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam x t ht.1.le
  set f : Fin n → Config d n → ℝ := fun i Y => gPlus d s c (x - Y i) with hf
  set F : Config d n → ℝ := fun Y => ∑ i, f i Y with hF
  have hfm : ∀ i, Measurable (f i) := fun i => hgm.comp (measurable_const.sub (measurable_pi_apply i))
  have hFm : Measurable F := Finset.measurable_sum _ fun i _ => hfm i
  -- finite variance, hence `F ∈ L²`
  have hvb := hvar N hN hlamle x t ht
  have hFvar : evariance F P ≤ ENNReal.ofReal (Cv * (n : ℝ) * (1 + L)) := hvb
  have hFmem : MemLp F 2 P :=
    (evariance_lt_top_iff_memLp hFm.aestronglyMeasurable).1 (lt_of_le_of_lt hFvar ENNReal.ofReal_lt_top)
  refine ⟨hFmem, ?_⟩
  set V : ℝ := (evariance F P).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hVbd : V ≤ Cv * (n : ℝ) * (1 + L) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hFvar
  have hfmem : ∀ i, MemLp (f i) 2 P := by
    intro i
    refine hFmem.mono' (hfm i).aestronglyMeasurable (Eventually.of_forall fun Y => ?_)
    have h0 : 0 ≤ f i Y := hc _
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact Finset.single_le_sum (f := fun j => f j Y) (fun j _ => hc _) (Finset.mem_univ i)
  have hfint : ∀ i, Integrable (f i) P := fun i => (hfmem i).integrable (by norm_num)
  -- the conditioning σ-algebras
  have hmle : ∀ i : Fin n, othersSigma (d := d) i ≤ MeasurableSpace.pi := fun i =>
    (measurable_pi_iff.2 fun j => measurable_pi_apply _ :
      Measurable (fun (Y : Config d n) (j : {j // j ≠ i}) => Y j)).comap_le
  have hfsm : ∀ i j : Fin n, j ≠ i → StronglyMeasurable[othersSigma i] (f j) := by
    intro i j hji
    have h1 : Measurable[othersSigma i] fun Y : Config d n => Y j :=
      (measurable_pi_apply (⟨j, hji⟩ : {j' : Fin n // j' ≠ i})).comp
        (comap_measurable (m := MeasurableSpace.pi)
          (fun (Y : Config d n) (j' : {j' // j' ≠ i}) => Y j'))
    exact (hgm.comp (measurable_const.sub h1)).stronglyMeasurable
  have hid := l49_variance_identity (P := P) (fun i => othersSigma (d := d) i) hmle f hfmem hfsm
  -- the variance as an integral
  have hVint : V = ∫ ω, (∑ i, f i ω - ∑ i, ∫ ω', f i ω' ∂P) ^ 2 ∂P := by
    have h1 : ∑ i, ∫ ω', f i ω' ∂P = ∫ ω', F ω' ∂P := by
      rw [hF]; exact (integral_finset_sum _ fun i _ => hfint i).symm
    rw [h1]
    have e : variance F P = V := rfl
    rw [← e, variance_eq_integral hFm.aemeasurable]
  rw [hVint, hid]
  -- the bounds from Proposition 4.8 for each index
  have hT := fun i : Fin n => h48 N hN x t ht i
  set T : Fin n → Config d n → ℝ := fun i => P[f i | othersSigma i] with hTdef
  have hTmem : ∀ i, MemLp (T i) 2 P := fun i => (hfmem i).condExp (by norm_num)
  have hTsq : ∀ i, ∫ ω, (T i ω) ^ 2 ∂P ≤ C4 := by
    intro i
    obtain ⟨-, -, -, h4⟩ := hT i
    have hint : Integrable (fun ω => (T i ω) ^ 2) P := by simpa using (hTmem i).integrable_sq
    have e1 : ∫⁻ ω, ‖T i ω‖ₑ ^ 2 ∂P = ∫⁻ ω, ENNReal.ofReal ((T i ω) ^ 2) ∂P := by
      refine lintegral_congr fun ω => ?_
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    have h4' : ∫⁻ ω, ENNReal.ofReal ((T i ω) ^ 2) ∂P ≤ ENNReal.ofReal C48 := by
      rw [← e1]; exact h4
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω => sq_nonneg _)] at h4'
    exact (ENNReal.ofReal_le_ofReal_iff hC40).1
      (h4'.trans (ENNReal.ofReal_le_ofReal (le_abs_self C48)))
  have hTvar : ∀ i, ∫ ω, (T i ω - ∫ ω', f i ω' ∂P) ^ 2 ∂P ≤ C4 / N := by
    intro i
    obtain ⟨-, -, h3, -⟩ := hT i
    have hmean : ∫ ω, T i ω ∂P = ∫ ω', f i ω' ∂P := integral_condExp (hmle i)
    have h1 : variance (T i) P = ∫ ω, (T i ω - ∫ ω', f i ω' ∂P) ^ 2 ∂P := by
      rw [variance_eq_integral (hTmem i).aestronglyMeasurable.aemeasurable]
      simp only [hTdef] at hmean ⊢
      rw [hmean]
    rw [← h1]
    have h2 : variance (T i) P = (evariance (T i) P).toReal := rfl
    rw [h2]
    have h5 : evariance (T i) P ≤ ENNReal.ofReal (C4 / N) :=
      h3.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_abs_self C48) hN0.le))
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h5
  -- covariance bound
  have hcov : ∀ i, |∫ ω, (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) * ((T i ω) - ∫ ω', f i ω' ∂P) ∂P| ≤
      Real.sqrt (Cv * C4) * Real.sqrt (1 + L) := by
    intro i
    have hFM : MemLp (fun ω => ∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) 2 P :=
      (memLp_finsetSum _ fun j _ => hfmem j).sub (memLp_const _)
    have hTM : MemLp (fun ω => T i ω - ∫ ω', f i ω' ∂P) 2 P := (hTmem i).sub (memLp_const _)
    have hcs := l49_cs hFM hTM
    have e1 : ∫ ω, (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) ^ 2 ∂P = V := hVint.symm
    have hA : 0 ≤ ∫ ω, (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    have h1 := l49_abs_le_sqrt_mul hA hcs
    refine h1.trans ?_
    rw [e1]
    have hb := hTvar i
    calc Real.sqrt V * Real.sqrt (∫ ω, (T i ω - ∫ ω', f i ω' ∂P) ^ 2 ∂P)
        ≤ Real.sqrt (Cv * n * (1 + L)) * Real.sqrt (C4 / N) :=
          mul_le_mul (Real.sqrt_le_sqrt hVbd) (Real.sqrt_le_sqrt hb) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt (Cv * n * (1 + L) * (C4 / N)) := (Real.sqrt_mul (by positivity) _).symm
      _ ≤ Real.sqrt ((Cv * C4) * (1 + L)) := by
          apply Real.sqrt_le_sqrt
          have : (n : ℝ) / N ≤ 1 := (div_le_one hN0).2 hnN
          calc Cv * n * (1 + L) * (C4 / N) = (Cv * C4) * (1 + L) * ((n : ℝ) / N) := by ring
            _ ≤ (Cv * C4) * (1 + L) * 1 := by gcongr
            _ = _ := by ring
      _ = _ := Real.sqrt_mul (by positivity) _
  -- the diagonal
  have hdiag : ∀ i, |∫ ω, f i ω ^ 2 ∂P - l49_J d s c ρ x u| ≤ CQ * Csl * Real.sqrt (deltaN d s N) * (1 + L) := by
    intro i
    have h1 := hQ N hN hlamle x t ht i
    have hJ := (hsl u hu0 hu1 x).2.2
    refine h1.trans ?_
    have : CQ * Real.sqrt (deltaN d s N) * l49_J d s c ρ x u ≤
        CQ * Real.sqrt (deltaN d s N) * (Csl * (1 + L)) :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    nlinarith
  -- assemble
  have hsumle : ∀ g : Fin n → ℝ, ∀ B : ℝ, (∀ i, g i ≤ B) → ∑ i, g i ≤ (n : ℝ) * B := by
    intro g B hg
    have := Finset.sum_le_card_nsmul Finset.univ g B (fun i _ => hg i)
    simpa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  have hS1 : |∑ i, (∫ ω, f i ω ^ 2 ∂P - l49_J d s c ρ x u)| ≤
      (n : ℝ) * (CQ * Csl * Real.sqrt (deltaN d s N) * (1 + L)) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (hsumle _ _ hdiag)
  have hS2 : |∑ i, ∫ ω, (T i ω) ^ 2 ∂P| ≤ (n : ℝ) * C4 := by
    have h0 : 0 ≤ ∑ i, ∫ ω, (T i ω) ^ 2 ∂P := Finset.sum_nonneg fun i _ => integral_nonneg fun ω => sq_nonneg _
    rw [abs_of_nonneg h0]
    exact hsumle _ _ hTsq
  have hS3 : |∑ i, ∫ ω, (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) * ((T i ω) - ∫ ω', f i ω' ∂P) ∂P| ≤
      (n : ℝ) * (Real.sqrt (Cv * C4) * Real.sqrt (1 + L)) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (hsumle _ _ hcov)
  have hrew : ∑ i, (∫ ω, f i ω ^ 2 ∂P - ∫ ω, ((T i ω)) ^ 2 ∂P) +
      ∑ i, ∫ ω, (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) * ((T i ω) - ∫ ω', f i ω' ∂P) ∂P -
        (n : ℝ) * l49_J d s c ρ x u =
      ∑ i, (∫ ω, f i ω ^ 2 ∂P - l49_J d s c ρ x u) - ∑ i, ∫ ω, (T i ω) ^ 2 ∂P +
      ∑ i, ∫ ω, (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) * ((T i ω) - ∫ ω', f i ω' ∂P) ∂P := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  show |∑ i, (∫ ω, f i ω ^ 2 ∂P - ∫ ω, ((T i ω)) ^ 2 ∂P) +
      ∑ i, ∫ ω, (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) * ((T i ω) - ∫ ω', f i ω' ∂P) ∂P -
        (n : ℝ) * l49_J d s c ρ x u| ≤ _
  rw [hrew]
  calc _ ≤ |∑ i, (∫ ω, f i ω ^ 2 ∂P - l49_J d s c ρ x u)| + |∑ i, ∫ ω, (T i ω) ^ 2 ∂P| +
        |∑ i, ∫ ω, (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) * ((T i ω) - ∫ ω', f i ω' ∂P) ∂P| := by
        refine (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ _ := by nlinarith [hS1, hS2, hS3]

end L49

end HRS

end
