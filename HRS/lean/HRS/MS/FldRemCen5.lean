import HRS.MS.FldRemCen4
import HRS.MS.FldRemTie

/-!
# S5.3 (`field_remainder_centered`), part 5: the assembly, conditional on the orbit input

`s53_field_remainder_centered_of_orbit`: the conclusion of the frozen `field_remainder_centered` for any coefficient `C`
with `S53Orbit C m T K b G0 G1 G2` (the orbit input of `field_remainder`).  Route: the modification `X'` of `X`
(jointly measurable, equal on a full set `Gs`), stationarity and the variance bound transferred to `X'`
(`S53Var`), the mean functional is bounded (`s53_mean_bound`), one coordinate at a time (`s53_alpha_c`), then
`(⨆_t ‖c(t)‖_{ℓ²})² ≤ ∑_α (√N/2)² g_α²` and `N E g_α² ≤ C δ b_α²`.
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S53

open HRS HRS.Whole

variable {d N : ℕ}

lemma s53_evariance_congr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f g : Ω → ℝ}
    (h : f =ᵐ[P] g) : evariance f P = evariance g P := by
  unfold evariance
  rw [integral_congr_ae h]
  refine lintegral_congr_ae (h.mono fun ζ hζ => ?_)
  beta_reduce
  rw [hζ]

lemma s53_arith2 {T v : ℝ} (hT : 0 ≤ T) (hv : 0 ≤ v) :
    ENNReal.ofReal (1 / 4) * (ENNReal.ofReal T * (ENNReal.ofReal T *
      (2 * ENNReal.ofReal v + 2 * (ENNReal.ofReal T * (ENNReal.ofReal T * ENNReal.ofReal v))))) =
    ENNReal.ofReal ((1 / 4) * (T * (T * (2 * v + 2 * (T * (T * v)))))) := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  have e1 : ENNReal.ofReal T * ENNReal.ofReal v = ENNReal.ofReal (T * v) := (ENNReal.ofReal_mul hT).symm
  have e2 : ENNReal.ofReal T * ENNReal.ofReal (T * v) = ENNReal.ofReal (T * (T * v)) :=
    (ENNReal.ofReal_mul hT).symm
  rw [e1, e2, h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [← ENNReal.ofReal_mul hT, ← ENNReal.ofReal_mul hT, ← ENNReal.ofReal_mul (by norm_num)]

lemma s53_sq_summable {b : MultiIndex d → ℝ} (hb0 : ∀ α, 0 ≤ b α) (hb : Summable b) :
    Summable fun α => b α ^ 2 := by
  refine Summable.of_nonneg_of_le (fun α => sq_nonneg _) (fun α => ?_) (hb.mul_left (∑' α, b α))
  have : b α ≤ ∑' α, b α := hb.le_tsum α fun j _ => hb0 j
  nlinarith [hb0 α]

lemma s53_sqrt_rpow {x : ℝ} (hx : 0 ≤ x) : ENNReal.ofReal x ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt x) := by
  rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num), Real.sqrt_eq_rpow]


variable {s : ℝ} {ρ : Euc d → ℝ} {Mρ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X' : ℝ≥0 → Ω → EucConfig d N} {T CA δ : ℝ}

/-- **One Hermite coordinate, centered**: the dominating function `g` and its second moment. -/
lemma s53_alpha_c [IsProbabilityMeasure P] (ctx : S53Ctx s ρ Mρ) (hN : 0 < N) (hδ : 0 ≤ δ) (hT : 0 ≤ T)
    (H : S53Var s ρ P X' T CA δ) {Cm : ℝ} (hCm0 : 0 ≤ Cm)
    (hCm : ∀ f : Euc d → ℝ, MemCb 2 f → |s53_ell s ρ P X' f| ≤ Cm * cbNorm 2 f)
    {C : WholeCoeff d} {m : ℝ} {α : MultiIndex d} {G G' G'' : ℝ → Euc d → ℝ}
    (hom : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → propagatorW C r t (oscTestFun m α) = G (t - r))
    (hG : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G τ)) (hG' : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G' τ))
    (hG'' : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G'' τ))
    (hd0 : S53Diff T G G') (hd1 : S53Diff T G' G'') {L : ℝ}
    (hL0 : ∀ τ ∈ Set.Icc (0 : ℝ) T, cbNorm 2 (G τ) ≤ L) (hL1 : ∀ σ ∈ Set.Icc (0 : ℝ) T, cbNorm 2 (G' σ) ≤ L)
    {X : ℝ≥0 → Ω → EucConfig d N} {Gs : Set Ω}
    (hX'j : Measurable fun p : ℝ × Ω => X' (Real.toNNReal p.1) p.2)
    (hGs : ∀ ζ ∈ Gs, ∀ t, X' t ζ = X t ζ) (hGsae : ∀ᵐ ζ ∂P, ζ ∈ Gs) :
    ∃ g : Ω → ℝ≥0∞, Measurable g ∧
      (N : ℝ≥0∞) * ∫⁻ ζ, g ζ ^ 2 ∂P ≤ ENNReal.ofReal T * (ENNReal.ofReal T *
        (2 * ENNReal.ofReal (max CA 0 * δ * L ^ 2) + 2 * (ENNReal.ofReal T * (ENNReal.ofReal T *
          ENNReal.ofReal (max CA 0 * δ * L ^ 2))))) ∧
      ∀ ζ ∈ Gs, ∀ t ∈ Set.Icc (0 : ℝ) T,
        (∫⁻ r in Set.Icc (0 : ℝ) t, ‖commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ -
            ∫ ζ', commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P‖ₑ ≤ g ζ) ∧
        (∫⁻ r in Set.Icc (0 : ℝ) t, ‖commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ‖ₑ ≤
          g ζ + ENNReal.ofReal T * ENNReal.ofReal (Cm * L)) ∧
        AEStronglyMeasurable (fun r => commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ)
          (volume.restrict (Set.Icc (0 : ℝ) t)) := by
  have h0T : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hc1 : S53Cont T G' := s53_cont_of_diff hG' hG'' hd1
  have hG0m : Measurable fun x : Euc d => gradient (G 0) x :=
    s53_gradient_measurable ((hG 0 h0T).1.of_le (by norm_num))
  have hG1m := s53_grad_measurable hT hG' hc1
  have hae : ∀ t, ∀ᵐ ζ ∂P, X' t ζ = X t ζ := fun t => hGsae.mono fun ζ hζ => hGs ζ hζ t
  have hℓm := s53_ell_clamp_measurable ctx H T hG1m
  have hHc := s53_Hc_measurable (N := N) (ρ := ρ) (s := s) ctx T hG0m hG1m
    (ℓ0 := s53_ell s ρ P X' (G 0)) hℓm
  have hjoint : Measurable fun q : Ω × ℝ =>
      s53_Hc s ρ T G G' (s53_ell s ρ P X' (G 0))
        (fun σ => s53_ell s ρ P X' (G' (s53_clamp T σ))) (X' (Real.toNNReal q.2) q.1) :=
    hHc.comp (hX'j.comp measurable_swap)
  refine ⟨fun ζ => ∫⁻ r in Set.Icc (0 : ℝ) T, s53_Hc s ρ T G G' (s53_ell s ρ P X' (G 0))
      (fun σ => s53_ell s ρ P X' (G' (s53_clamp T σ))) (X' (Real.toNNReal r) ζ),
    hjoint.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T)), ?_, ?_⟩
  · exact s53_g_second (h := fun ζ r => s53_Hc s ρ T G G' (s53_ell s ρ P X' (G 0))
      (fun σ => s53_ell s ρ P X' (G' (s53_clamp T σ))) (X' (Real.toNNReal r) ζ)) hjoint T
      (fun r hr => s53_exp_Hc_sq ctx hδ hT H hG hG' hG0m hG1m (hL0 0 h0T) hL1 hr)
  · intro ζ hζ t ht
    obtain ⟨p1, p2, p3⟩ := s53_alpha_c_path ctx hN hδ hT H hCm0 hCm hom hG hG' hG'' hd0 hd1 hL0 hL1
      hX'j hGs hae hζ ht
    exact ⟨p1, p2.trans (add_le_add p1 le_rfl), p3⟩


theorem s53_field_remainder_centered_of_orbit (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m T : ℝ)
    (hT : 0 ≤ T) {ρ : Euc d → ℝ} (hρ : IsSchwartzDensity ρ) (D : WholeDyn d) (C : WholeCoeff d)
    {b : MultiIndex d → ℝ} {K : ℝ} {G0 G1 G2 : MultiIndex d → ℝ → Euc d → ℝ}
    (O : S53Orbit C m T K b G0 G1 G2) (CA : ℝ) :
    ∃ CT : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
      (X : ℝ≥0 → Ω → EucConfig d N), IsVectorBrownian P W →
      IsWholeStrongSolution P D T X₀ W X →
      (∀ t ∈ Set.Icc (0 : ℝ) T, law P (X (Real.toNNReal t)) = law P (X 0)) →
      (∀ f : Euc d → ℝ, MemCb 2 f →
        (N : ℝ≥0∞) * evariance (fun ζ => centeredPairFunctional
            (commutatorKernel d s (fun x => gradient f x)) (X 0 ζ) (HRS.Whole.withDensityReal ρ)) P ≤
          ENNReal.ofReal (CA * deltaN d s N * (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) ^ 2)) →
      (∀ᵐ ζ ∂P, ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        IntegrableOn (fun r => commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ)
          (Set.Icc 0 t)) ∧
      (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
          -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) t,
            (commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ -
              ∫ ζ', commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P))) ^ 2 ∂P) ^
          (1 / 2 : ℝ) ≤ ENNReal.ofReal (CT * Real.sqrt (deltaN d s N)) := by
  obtain ⟨Mρ, ctx⟩ := s53_ctx_of_schwartz hd hs0 hsd hρ
  set Cc : ℝ := (1 / 4) * (T * (T * (2 + 2 * (T * T)))) with hCc
  have hCc0 : 0 ≤ Cc := by positivity
  set A : ℝ := Cc * max CA 0 * K ^ 2 * ∑' α, b α ^ 2 with hA
  have hA0 : 0 ≤ A := by
    have : 0 ≤ ∑' α, b α ^ 2 := tsum_nonneg fun α => sq_nonneg _
    positivity
  refine ⟨Real.sqrt A, ?_⟩
  intro N hN Ω _ P _ X₀ W X _ hX hstat0 hvar0
  have hNpos : 0 < N := by omega
  have hδ := s53_deltaN_nonneg (d := d) (N := N) s hNpos
  obtain ⟨X', Gs, hGsm, hGs0, hGs, hX'm, hX'j⟩ := s53_modify P X hX.cont hX.adapted
  have hGsae : ∀ᵐ ζ ∂P, ζ ∈ Gs := by
    rw [ae_iff]; exact hGs0
  have hae : ∀ t, ∀ᵐ ζ ∂P, X' t ζ = X t ζ := fun t => hGsae.mono fun ζ hζ => hGs ζ hζ t
  have H : S53Var s ρ P X' T CA (deltaN d s N) := by
    refine ⟨hX'm, fun t ht => ?_, fun f hf => ?_⟩
    · rw [Measure.map_congr (hae _), Measure.map_congr (hae 0)]
      exact hstat0 t ht
    · have := hvar0 f hf
      rw [s53_evariance_congr (f := fun ζ => s53_Dk s ρ f (X' 0 ζ)) (g := fun ζ => s53_Dk s ρ f (X 0 ζ))
        ((hae 0).mono fun ζ hζ => by beta_reduce; rw [hζ])]
      exact this
  obtain ⟨Cm, hCm0, hCm⟩ := s53_mean_bound ctx hNpos hδ H
  choose g hgm hgint hgpath using fun α : MultiIndex d =>
    s53_alpha_c (P := P) (X := X) (X' := X') (Gs := Gs) ctx hNpos hδ hT H hCm0 hCm (C := C) (m := m)
      (α := α) (O.hom α) (O.mem0 α) (O.mem1 α) (O.mem2 α) (O.diff0 α) (O.diff1 α)
      (L := K * b α) (O.cb0 α) (O.cb1 α) hX'j hGs hGsae
  have hsq : 0 ≤ Real.sqrt N / 2 := by positivity
  set w : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt N / 2) with hw
  have hNne : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hfin : ∀ α : MultiIndex d, ∀ᵐ ζ ∂P, g α ζ < ⊤ := fun α => by
    have hW : (N : ℝ≥0∞) * ∫⁻ ζ, g α ζ ^ 2 ∂P ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (hgint α)
      simp [ENNReal.mul_eq_top, ENNReal.add_eq_top]
    have h2 : ∫⁻ ζ, g α ζ ^ 2 ∂P ≠ ⊤ := fun h => hW (by rw [h, ENNReal.mul_top hNne])
    have := ae_lt_top ((hgm α).pow_const 2) h2
    refine this.mono fun ζ hζ => ?_
    by_contra hc
    exact hζ.ne (by rw [not_lt_top_iff.1 hc]; simp)
  constructor
  · have hall : ∀ᵐ ζ ∂P, ∀ α, g α ζ < ⊤ := ae_all_iff.2 hfin
    filter_upwards [hall, hGsae] with ζ hζ hζs α t ht
    obtain ⟨-, h2, h3⟩ := hgpath α ζ hζs t ht
    refine ⟨h3, ?_⟩
    refine lt_of_le_of_lt h2 (ENNReal.add_lt_top.2 ⟨hζ α, ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top⟩)
  · -- the maximal estimate
    have hpath : ∀ ζ ∈ Gs, (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
        -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) t,
          (commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ -
            ∫ ζ', commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P))) ^ 2 ≤
        ∑' α, (w * g α ζ) ^ 2 := by
      intro ζ hζ
      have key : ∀ t : Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
          -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) t,
            (commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ -
              ∫ ζ', commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P)) ≤
          (∑' α, (w * g α ζ) ^ 2) ^ (1 / 2 : ℝ) := by
        intro t
        unfold l2NormE
        refine ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum fun α => ?_) (by norm_num)
        have h1 := (hgpath α ζ hζ t t.2).1
        set I := ∫ r in Set.Icc (0 : ℝ) t,
          (commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ -
            ∫ ζ', commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P) with hI
        have h2 : ENNReal.ofReal |I| ≤ g α ζ := by
          rw [← Real.norm_eq_abs, ofReal_norm]
          exact (enorm_integral_le_lintegral_enorm _).trans h1
        have h3 : ENNReal.ofReal ((-(Real.sqrt N / 2) * I) ^ 2) = (w * ENNReal.ofReal |I|) ^ 2 := by
          rw [← sq_abs, abs_mul, abs_neg, abs_of_nonneg hsq, ENNReal.ofReal_pow (by positivity),
            ENNReal.ofReal_mul hsq]
        rw [h3]
        exact pow_le_pow_left' (mul_le_mul_right h2 _) 2
      have h1 : (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
          -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) t,
            (commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ -
              ∫ ζ', commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P))) ≤
          (∑' α, (w * g α ζ) ^ 2) ^ (1 / 2 : ℝ) := iSup_le key
      calc _ ≤ ((∑' α, (w * g α ζ) ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left' h1 2
        _ = _ := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    have hv0 : ∀ α, 0 ≤ max CA 0 * deltaN d s N * (K * b α) ^ 2 := fun α => by positivity
    have hw2 : w ^ 2 = ENNReal.ofReal (1 / 4) * (N : ℝ≥0∞) := by
      rw [hw, ← ENNReal.ofReal_pow hsq, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg N)]; ring
    calc (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
          -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) t,
            (commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ -
              ∫ ζ', commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P))) ^ 2 ∂P) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal (A * deltaN d s N)) ^ (1 / 2 : ℝ) := by
          refine ENNReal.rpow_le_rpow ?_ (by norm_num)
          calc ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
                -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) t,
                  (commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ -
                    ∫ ζ', commForcing C s m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P))) ^ 2 ∂P
              ≤ ∫⁻ ζ, ∑' α, (w * g α ζ) ^ 2 ∂P :=
                lintegral_mono_ae (hGsae.mono fun ζ hζ => hpath ζ hζ)
            _ = ∑' α, ∫⁻ ζ, (w * g α ζ) ^ 2 ∂P :=
                lintegral_tsum fun α => (((hgm α).const_mul w).pow_const 2).aemeasurable
            _ = ∑' α, ENNReal.ofReal (1 / 4) * ((N : ℝ≥0∞) * ∫⁻ ζ, g α ζ ^ 2 ∂P) := by
                refine tsum_congr fun α => ?_
                simp only [mul_pow]
                rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top), hw2]
                ring
            _ ≤ ∑' α, ENNReal.ofReal (Cc * (max CA 0 * deltaN d s N * (K * b α) ^ 2)) := by
                refine ENNReal.tsum_le_tsum fun α => ?_
                refine (mul_le_mul_right (hgint α) _).trans (le_of_eq ?_)
                rw [s53_arith2 hT (hv0 α)]
                congr 1
                simp only [hCc]; ring
            _ = ENNReal.ofReal (A * deltaN d s N) := by
                have e : ∀ α, Cc * (max CA 0 * deltaN d s N * (K * b α) ^ 2) =
                    (Cc * max CA 0 * deltaN d s N * K ^ 2) * b α ^ 2 := fun α => by ring
                have hsum : Summable fun α => Cc * (max CA 0 * deltaN d s N * (K * b α) ^ 2) := by
                  simp only [e]
                  exact (s53_sq_summable O.b_nonneg O.b_summable).mul_left _
                rw [← ENNReal.ofReal_tsum_of_nonneg (fun α => by have := hv0 α; positivity) hsum]
                congr 1
                simp only [e]
                rw [tsum_mul_left, hA]
                ring
    _ = ENNReal.ofReal (Real.sqrt A * Real.sqrt (deltaN d s N)) := by
          rw [s53_sqrt_rpow (by positivity), Real.sqrt_mul hA0]

end HRS.MS.S53
