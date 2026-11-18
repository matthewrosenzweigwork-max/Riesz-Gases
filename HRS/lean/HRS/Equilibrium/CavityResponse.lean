/-
# HRS.Equilibrium.CavityResponse — Lemma 4.6 (`M:R:lem:cavity`)

`cavity_response_proof` restates `HRS.cavity_response` verbatim (its inputs, Lemma 4.1 variance,
Proposition 4.2 and the exact cavity equation, live in modules that import `PoleCavity.lean`).
-/
import HRS.Equilibrium.ProductTransfer
import HRS.Equilibrium.MarginalDensity

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace CavResp

variable {d : ℕ} {s c : ℝ}

open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer

/-! ### The exponent of the insertion pole -/

/-- `X = -λ ∑_i g_+(x - y_i)`. -/
def Xp (d : ℕ) (s c lam : ℝ) (x : Torus d) {n : ℕ} (Y : Config d n) : ℝ :=
  -lam * ∑ i, gPlus d s c (x - Y i)

theorem measurable_Xp (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (c lam : ℝ) (x : Torus d) {n : ℕ} :
    Measurable (Xp d s c lam x (n := n)) :=
  (Finset.measurable_sum _ fun i _ =>
    (measurable_gPlus hd hs0 hsd c).comp (measurable_const.sub (measurable_pi_apply i))).const_mul _

theorem Xp_le_zero (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) {lam : ℝ} (hlam : 0 ≤ lam) {n : ℕ}
    (x : Torus d) (Y : Config d n) : Xp d s c lam x Y ≤ 0 := by
  unfold Xp
  have : 0 ≤ ∑ i, gPlus d s c (x - Y i) := Finset.sum_nonneg fun i _ => hc _
  nlinarith

theorem critCavity_isProb (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (c β : ℝ) (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {N : ℕ} (hN : 2 ≤ N) :
    IsProbabilityMeasure (critCavity d s c β ρ N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [critCavity_eq hd hs0 hsd c β hρ N]
  exact cavity_isProb hd hs0 hsd β hρ _ _ (by positivity)

theorem critPole_eq_tilted (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (c β : ℝ) (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {N : ℕ} (hN : 2 ≤ N) (x : Torus d) (t : ℝ) :
    critPole d s c β ρ N x t =
      (critCavity d s c β ρ N).tilted (fun Y => t * Xp d s c (β / N) x Y) := by
  haveI := critCavity_isProb hd hs0 hsd c β hβ hρ hN
  have hm : Measurable fun Y : Config d (N - 1) => t * Xp d s c (β / N) x Y :=
    (measurable_Xp hd hs0 hsd c _ x).const_mul t
  have hw : (fun Y : Config d (N - 1) => -(t * (β / N)) * ∑ i, gPlus d s c (x - Y i)) =
      fun Y => t * Xp d s c (β / N) x Y := by
    funext Y; unfold Xp; ring
  have h0 : critPole d s c β ρ N x t = tiltMeasure (critCavity d s c β ρ N)
      (fun Y : Config d (N - 1) => -(t * (β / N)) * ∑ i, gPlus d s c (x - Y i)) := rfl
  rw [h0, hw]
  exact Glue.tiltMeasure_eq_tilted_of_measurable _ _ hm

theorem insertionPressure_eq (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (ρ : Torus d → ℝ)
    (N : ℕ) (x : Torus d) (t : ℝ) :
    insertionPressure d s c β ρ N x t = cgf (Xp d s c (β / N) x) (critCavity d s c β ρ N) t := by
  unfold insertionPressure cgf mgf Xp
  congr 2
  funext Y
  congr 1
  ring

theorem insertionDefect_eq' (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (ρ : Torus d → ℝ)
    (N : ℕ) (x : Torus d) :
    insertionDefect d s c β ρ N x =
      cgf (Xp d s c (β / N) x) (critCavity d s c β ρ N) 1 -
        (critCavity d s c β ρ N)[Xp d s c (β / N) x] := by
  unfold insertionDefect
  rw [insertionPressure_eq hd hs0 hsd]
  unfold Xp
  rw [integral_const_mul]
  ring

/-! ### Abstract cumulant facts: right derivative at `0` and the Taylor identity -/

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ} {b : ℝ}

theorem hasDerivWithinAt_cgf_zero (hXm : Measurable X) (hb : ∀ ω, X ω ≤ b) (hXi : Integrable X P) :
    HasDerivWithinAt (cgf X P) (P[X]) (Ici 0) 0 := by
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0) ?_ ?_ self_mem_nhdsWithin ?_
  · intro t ht
    exact (EF.hasDerivAt_cgf hXm hb ht).differentiableAt.differentiableWithinAt
  · have h0 : cgf X P 0 = 0 := by simp [cgf_zero]
    rw [ContinuousWithinAt, h0]
    exact EF.tendsto_cgf_zero hXm hb
  · refine (EF.tendsto_mean_zero hXm hb hXi).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ((EF.hasDerivAt_cgf hXm hb ht).deriv).symm

theorem taylor_identity (hXm : Measurable X) (hb : ∀ ω, X ω ≤ b) (hXi : Integrable X P) :
    ENNReal.ofReal (cgf X P 1 - P[X]) =
      ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - t) * Var[X; P.tilted (fun ω => t * X ω)]) := by
  set F := cgf X P with hFdef
  set H : ℝ → ℝ := fun u => (P.tilted (fun ω => u * X ω))[X] with hHdef
  set V : ℝ → ℝ := fun t => Var[X; P.tilted (fun ω => t * X ω)] with hVdef
  set H0 : ℝ := P[X] with hH0def
  have hF : ∀ t, 0 < t → HasDerivAt F (H t) t := fun t ht => EF.hasDerivAt_cgf hXm hb ht
  have hH : ∀ t, 0 < t → HasDerivAt H (V t) t := fun t ht => EF.hasDerivAt_mean hXm hb ht
  have hV0 : ∀ t, 0 ≤ V t := fun t => variance_nonneg _ _
  have hVc : ContinuousOn V (Ioi 0) := EF.continuousOn_var hXm hb
  have hlimH : Tendsto H (𝓝[>] 0) (𝓝 H0) := EF.tendsto_mean_zero hXm hb hXi
  have hlimF : Tendsto F (𝓝[>] 0) (𝓝 0) := EF.tendsto_cgf_zero hXm hb
  set g : ℝ → ℝ := fun t => (1 - t) * V t with hg
  have hgc : ContinuousOn g (Ioi 0) := (continuousOn_const.sub continuousOn_id).mul hVc
  -- the integral over `[ε, 1]`
  have hI : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∫ t in ε..1, g t = F 1 - F ε - (1 - ε) * H ε := by
    intro ε hε hε1
    have hsub : Set.uIcc ε 1 ⊆ Ioi 0 := by
      rw [Set.uIcc_of_le hε1]; intro x hx; exact lt_of_lt_of_le hε hx.1
    have hd : ∀ x ∈ Set.uIcc ε 1, HasDerivAt (fun t => F t + (1 - t) * H t) (g x) x := by
      intro x hx
      have hx0 : 0 < x := hsub hx
      have h1 := ((hasDerivAt_id x).const_sub 1).mul (hH x hx0)
      have h2 := (hF x hx0).add h1
      refine h2.congr_deriv ?_
      simp only [hg, id]
      ring
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hgc.mono hsub).intervalIntegrable
    rw [this]
    ring
  -- the limit of the real integrals
  have hlim : Tendsto (fun ε : ℝ => ∫ t in ε..1, g t) (𝓝[>] 0) (𝓝 (F 1 - H0)) := by
    have h1 : Tendsto (fun ε : ℝ => F 1 - F ε - (1 - ε) * H ε) (𝓝[>] 0) (𝓝 (F 1 - 0 - (1 - 0) * H0)) :=
      (tendsto_const_nhds.sub hlimF).sub
        (((tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds).mul hlimH)
    simp only [sub_zero, one_mul] at h1
    refine h1.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact (hI ε hε.1 hε.2.le).symm
  -- the sequence `ε_k = 1/(k+2)`
  set e : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 2) with he
  have he0 : ∀ k, 0 < e k := fun k => by simp only [he]; positivity
  have he1 : ∀ k, e k ≤ 1 := fun k => by
    simp only [he]; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have heanti : Antitone e := fun a b hab => by
    simp only [he]
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hetend : Tendsto e atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => he0 k⟩
    have h := (tendsto_add_atTop_iff_nat 1).2 (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    refine h.congr fun k => ?_
    simp only [he]; push_cast; ring_nf
  set Ik : ℕ → ℝ := fun k => ∫ t in e k..1, g t with hIk
  have hlimk : Tendsto Ik atTop (𝓝 (F 1 - H0)) := hlim.comp hetend
  have hg0 : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ g t := fun t ht => mul_nonneg (by linarith [ht.2]) (hV0 t)
  have hlint : ∀ k, ∫⁻ t in Ioc (e k) 1, ENNReal.ofReal (g t) = ENNReal.ofReal (Ik k) := by
    intro k
    have hsub : Icc (e k) 1 ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le (he0 k) hx.1
    have hint : IntegrableOn g (Ioc (e k) 1) :=
      ((hgc.mono hsub).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Ioc
      (fun t ht => hg0 t ⟨lt_of_lt_of_le (he0 k) ht.1.le, ht.2⟩))]
    simp only [hIk]
    rw [intervalIntegral.integral_of_le (he1 k)]
  have hunion : (⋃ k, Ioc (e k) 1) = Ioc (0 : ℝ) 1 := by
    ext t
    simp only [mem_iUnion, mem_Ioc]
    constructor
    · rintro ⟨k, h1, h2⟩; exact ⟨lt_trans (he0 k) h1, h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨k, hk⟩ := (hetend.eventually (Ioo_mem_nhdsGT h1)).exists
      exact ⟨k, hk.2, h2⟩
  have hdir : Directed (· ⊆ ·) fun k => Ioc (e k) 1 :=
    Monotone.directed_le fun a b hab => Ioc_subset_Ioc_left (heanti hab)
  have hsup : ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (g t) = ⨆ k, ENNReal.ofReal (Ik k) := by
    rw [← hunion, setLIntegral_iUnion_of_directed _ hdir]
    exact iSup_congr hlint
  have hmono : Monotone fun k => ENNReal.ofReal (Ik k) := by
    intro a b hab
    show ENNReal.ofReal (Ik a) ≤ ENNReal.ofReal (Ik b)
    rw [← hlint a, ← hlint b]
    exact lintegral_mono_set (Ioc_subset_Ioc_left (heanti hab))
  have ht1 : Tendsto (fun k => ENNReal.ofReal (Ik k)) atTop (𝓝 (ENNReal.ofReal (F 1 - H0))) :=
    ENNReal.tendsto_ofReal hlimk
  have ht2 := tendsto_atTop_iSup hmono
  have : ENNReal.ofReal (F 1 - H0) = ⨆ k, ENNReal.ofReal (Ik k) := tendsto_nhds_unique ht1 ht2
  rw [this, ← hsup]

end Abstract

/-! ### Part A: the insertion defect -/

theorem Xp_eq_Xx (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (c lam : ℝ) (x : Torus d) {n : ℕ}
    (Y : Config d n) :
    Xp d s c lam x Y = Xx (periodicRiesz d s) lam x Y + (-(lam * n * c)) := by
  unfold Xp Xx gPlus
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

theorem insertionDefect_eq_insDefect (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (c β : ℝ)
    (hβ : 0 < β) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {N : ℕ} (hN : 2 ≤ N) (x : Torus d) :
    insertionDefect d s c β ρ N x =
      insDefect (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  haveI := cavity_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam
  rw [insertionDefect_eq' hd hs0 hsd, critCavity_eq hd hs0 hsd c β hρ N,
    insDefect_eq hd hs0 hsd β hρ (N - 1) (β / N) hlam x]
  obtain ⟨B, hB0, hB⟩ := MarginalAux.rieszB hd hs0 hsd
  have hln : β / N * ((N - 1 : ℕ) : ℝ) ≤ β := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    have : β / N * ((N : ℝ) - 1) = β - β / N := by field_simp
    rw [this]; linarith
  have hgm := measurable_periodicRiesz hd hs0 hsd
  have hXm := measurable_Xx hgm (n := N - 1) (β / N) x
  have hb := Xx_le hd hs0 hsd hlam hln hB0 hB x
  have hXi := integrable_Xx hd hs0 hsd hβ hρ hN x
  set P0 := cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β with hP0
  set k : ℝ := -((β / N) * ((N - 1 : ℕ) : ℝ) * c) with hk
  have hXp : Xp d s c (β / N) x (n := N - 1) =
      fun Y : Config d (N - 1) => Xx (periodicRiesz d s) (β / N) x Y + k := by
    funext Y; exact Xp_eq_Xx hd hs0 hsd c _ x Y
  rw [hXp]
  have hcgf : cgf (fun Y => Xx (periodicRiesz d s) (β / N) x Y + k) P0 1 =
      cgf (Xx (periodicRiesz d s) (β / N) x) P0 1 + k := by
    have hint : Integrable (fun ω => Real.exp (1 * Xx (periodicRiesz d s) (β / N) x ω)) P0 :=
      EF.integrable_exp_mul hXm hb zero_le_one
    unfold cgf
    rw [mgf_add_const]
    have hpos : 0 < mgf (Xx (periodicRiesz d s) (β / N) x) P0 1 := by
      unfold mgf; exact integral_exp_pos hint
    rw [Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hmean : ∫ Y, (Xx (periodicRiesz d s) (β / N) x Y + k) ∂P0 =
      ∫ Y, Xx (periodicRiesz d s) (β / N) x Y ∂P0 + k := by
    rw [integral_add hXi (integrable_const _)]
    simp
  rw [hcgf, hmean]
  ring

/-- Lemma 4.6, first display (`R:eq:D-integral`) and the derivative statement. -/
theorem partA (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      Integrable (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i))
          (critCavity d s c β ρ N) ∧
        HasDerivWithinAt (insertionPressure d s c β ρ N x)
          (-((β / N) * ∫ Y, ∑ i, gPlus d s c (x - Y i) ∂(critCavity d s c β ρ N)))
          (Set.Ici 0) 0 ∧
        0 ≤ insertionDefect d s c β ρ N x ∧
        ENNReal.ofReal (insertionDefect d s c β ρ N x) =
          ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - t) * (β / N) ^ 2) *
            evariance (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i))
              (critPole d s c β ρ N x t) ∧
        insertionDefect d s c β ρ N x ≤ C * deltaN d s N := by
  obtain ⟨C, hC⟩ := insDefect_le hd hs0 hsd hβ hρ
  obtain ⟨A0, hA0, hA⟩ := coord_mean_le hd hs0 hsd c β hβ hρ hc
  refine ⟨C, fun N hN x => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 < β / N := by positivity
  haveI := critCavity_isProb hd hs0 hsd c β hβ hρ hN
  set P0 := critCavity d s c β ρ N with hP0
  have hSi : Integrable (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i)) P0 :=
    integrable_finset_sum _ fun i _ => (hA N hN x i).1
  have hXm := measurable_Xp hd hs0 hsd c (β / N) x (n := N - 1)
  have hb : ∀ Y : Config d (N - 1), Xp d s c (β / N) x Y ≤ 0 := fun Y => Xp_le_zero hc hlam.le x Y
  have hXi : Integrable (Xp d s c (β / N) x) P0 := hSi.const_mul _
  have hmean : P0[Xp d s c (β / N) x] =
      -((β / N) * ∫ Y, ∑ i, gPlus d s c (x - Y i) ∂P0) := by
    unfold Xp; rw [integral_const_mul]; ring
  refine ⟨hSi, ?_, ?_, ?_, ?_⟩
  · have := hasDerivWithinAt_cgf_zero hXm hb hXi
    rw [hmean] at this
    have e : insertionPressure d s c β ρ N x = cgf (Xp d s c (β / N) x) P0 := by
      funext t; exact insertionPressure_eq hd hs0 hsd β ρ N x t
    rw [e]; exact this
  · rw [insertionDefect_eq' hd hs0 hsd]
    exact sub_nonneg.2 (EF.ef_cgf_ge hXm hb hXi)
  · rw [insertionDefect_eq' hd hs0 hsd, taylor_identity hXm hb hXi]
    refine setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have hν : MemLp (Xp d s c (β / N) x) 2 (P0.tilted fun ω => t * Xp d s c (β / N) x ω) :=
      memLp_tilted_mul (EF.Ioi_subset_interior (P := P0) hXm hb ht.1) 2
    have hS : MemLp (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i)) 2
        (P0.tilted fun ω => t * Xp d s c (β / N) x ω) := by
      have := hν.const_mul (-(β / N)⁻¹)
      refine this.ae_eq (Eventually.of_forall fun Y => ?_)
      simp only [Xp]
      field_simp
    have hev : evariance (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i))
        (P0.tilted fun ω => t * Xp d s c (β / N) x ω) ≠ ∞ := hS.evariance_lt_top.ne
    rw [← critPole_eq_tilted hd hs0 hsd c β hβ hρ hN x t] at hev ⊢
    have e1 : Var[Xp d s c (β / N) x; critPole d s c β ρ N x t] = (β / N) ^ 2 *
        (evariance (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i))
          (critPole d s c β ρ N x t)).toReal := by
      have hX : Xp d s c (β / N) x (n := N - 1) =
          fun Y : Config d (N - 1) => (-(β / N)) * ∑ i, gPlus d s c (x - Y i) := by
        funext Y; simp [Xp]
      rw [hX, variance_const_mul, neg_sq]
      rfl
    rw [e1]
    have h1t : 0 ≤ 1 - t := by linarith [ht.2]
    calc ENNReal.ofReal ((1 - t) * ((β / N) ^ 2 * (evariance (fun Y : Config d (N - 1) =>
            ∑ i, gPlus d s c (x - Y i)) (critPole d s c β ρ N x t)).toReal))
        = ENNReal.ofReal ((1 - t) * (β / N) ^ 2) * ENNReal.ofReal ((evariance (fun Y : Config d (N - 1) =>
            ∑ i, gPlus d s c (x - Y i)) (critPole d s c β ρ N x t)).toReal) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
      _ = _ := by rw [ENNReal.ofReal_toReal hev]
  · rw [insertionDefect_eq_insDefect hd hs0 hsd c β hβ hρ hN x]
    exact (hC N hN x).2.1

/-! ### Part B: the dual estimate for pole marginals -/

section Abstract2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ} {b : ℝ}

/-- `G(t) = F(t) - 2F(t/2)` is nondecreasing in `t > 0` (`G' = H(t) - H(t/2) ≥ 0`). -/
theorem cgf_diff_mono (hXm : Measurable X) (hb : ∀ ω, X ω ≤ b) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    cgf X P t - 2 * cgf X P (t / 2) ≤ cgf X P 1 - 2 * cgf X P (1 / 2) := by
  set F := cgf X P with hFdef
  set H : ℝ → ℝ := fun u => (P.tilted (fun ω => u * X ω))[X] with hHdef
  have hF : ∀ t, 0 < t → HasDerivAt F (H t) t := fun t ht => EF.hasDerivAt_cgf hXm hb ht
  have hH : ∀ t, 0 < t → HasDerivAt H (Var[X; P.tilted (fun ω => t * X ω)]) t :=
    fun t ht => EF.hasDerivAt_mean hXm hb ht
  have hHmono : MonotoneOn H (Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
    · intro u hu; exact (hH u hu).continuousAt.continuousWithinAt
    · intro u hu; rw [interior_Ioi] at hu; exact (hH u hu).differentiableAt.differentiableWithinAt
    · intro u hu; rw [interior_Ioi] at hu; rw [(hH u hu).deriv]; exact variance_nonneg _ _
  set G : ℝ → ℝ := fun t => F t - 2 * F (t / 2) with hG
  have hGd : ∀ t, 0 < t → HasDerivAt G (H t - H (t / 2)) t := by
    intro t ht
    have h1 := hF t ht
    have h2 : HasDerivAt (fun u => F (u / 2)) (H (t / 2) * (1 / 2)) t := by
      have := (hF (t / 2) (by positivity)).comp t ((hasDerivAt_id t).div_const 2)
      simpa [Function.comp_def] using this
    have := h1.sub (h2.const_mul 2)
    refine this.congr_deriv ?_
    ring
  have hGmono : MonotoneOn G (Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
    · intro u hu; exact (hGd u hu).continuousAt.continuousWithinAt
    · intro u hu; rw [interior_Ioi] at hu; exact (hGd u hu).differentiableAt.differentiableWithinAt
    · intro u hu; rw [interior_Ioi] at hu; rw [(hGd u hu).deriv]
      have hu' : (0 : ℝ) < u := hu
      exact sub_nonneg.2 (hHmono (show u / 2 ∈ Ioi (0 : ℝ) from by simp only [mem_Ioi]; linarith) hu
        (by linarith))
  have := hGmono ht0 (show (1 : ℝ) ∈ Ioi 0 by simp) ht1
  simpa [hG] using this

end Abstract2

/-- `n⁻¹ ∑_j f(y_j)`. -/
def fracF {n : ℕ} (f : Torus d → ℝ) (Y : Config d n) : ℝ := (1 / (n : ℝ)) * ∑ j, f (Y j)

theorem measurable_fracF {n : ℕ} {f : Torus d → ℝ} (hf : Measurable f) :
    Measurable (fracF (n := n) f) :=
  (Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)).const_mul _

theorem abs_fracF_le {n : ℕ} (hn : 0 < n) {f : Torus d → ℝ} {K : ℝ} (hf : ∀ y, |f y| ≤ K)
    (Y : Config d n) : |fracF f Y| ≤ K := by
  unfold fracF
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_mul, abs_of_pos (by positivity)]
  have : |∑ j, f (Y j)| ≤ n * K := by
    calc _ ≤ ∑ j, |f (Y j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, K := Finset.sum_le_sum fun j _ => hf _
      _ = n * K := by simp
  calc 1 / (n : ℝ) * |∑ j, f (Y j)| ≤ 1 / (n : ℝ) * (n * K) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = K := by field_simp

theorem integral_fracF {n : ℕ} (hn : 0 < n) {f : Torus d → ℝ} (hfm : Measurable f) {K : ℝ}
    (hf : ∀ y, |f y| ≤ K) (Pm : Measure (Config d n)) [IsProbabilityMeasure Pm]
    (hR : Entropy.IsExchangeable Pm) :
    ∫ Y, fracF f Y ∂Pm = ∫ y, f y ∂(firstMarginal Pm) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hfm' : firstMarginal Pm = Pm.map (fun Y : Config d n => Y ⟨0, hn⟩) := by
    unfold firstMarginal; rw [dif_pos hn]
  have hint : ∀ j : Fin n, Integrable (fun Y : Config d n => f (Y j)) Pm := fun j =>
    Integrable.of_bound (hfm.comp (measurable_pi_apply j)).aestronglyMeasurable K
      (Eventually.of_forall fun Y => by simpa [Real.norm_eq_abs] using hf (Y j))
  unfold fracF
  rw [integral_const_mul, integral_finset_sum _ fun j _ => hint j]
  have : ∀ j : Fin n, ∫ Y, f (Y j) ∂Pm = ∫ y, f y ∂(firstMarginal Pm) := by
    intro j
    rw [hfm', ← hR.marginal_eq j ⟨0, hn⟩, integral_map (measurable_pi_apply j).aemeasurable
      hfm.aestronglyMeasurable]
  simp_rw [this]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem var_fracF_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hvar : ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ f : Torus d → ℝ, Measurable f →
        evariance (fun Y : Config d (N - 1) => ∑ i, f (Y i))
            (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤
          ENNReal.ofReal (C₁ * ((N - 1 : ℕ) : ℝ)) *
            ∫⁻ y, ‖f y‖ₑ ^ 2 *
              ENNReal.ofReal (Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y)))
              ∂(withDensityReal ρ))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ z, -B ≤ periodicRiesz d s z) {N : ℕ} (hN : 2 ≤ N) (x : Torus d)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) {f : Torus d → ℝ} (hfm : Measurable f) {K : ℝ}
    (hf : ∀ y, |f y| ≤ K) :
    Var[fracF (n := N - 1) f; poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t] ≤
      C₁ * Real.exp (β * B) * (∫ y, f y ^ 2 ∂(withDensityReal ρ)) / ((N - 1 : ℕ) : ℝ) := by
  have hμ := isProbabilityMeasure_mu hρ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn0 : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N - 1)
  have hlam : 0 ≤ β / N := by positivity
  set n : ℕ := N - 1 with hn
  set lam : ℝ := β / N with hlamdef
  have h1 := hvar N hN x t ht f hfm
  have h2 : Var[fracF (n := n) f; poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t] =
      (1 / (n : ℝ)) ^ 2 * (evariance (fun Y : Config d n => ∑ i, f (Y i))
        (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t)).toReal :=
    variance_const_mul (1 / (n : ℝ)) (fun Y : Config d n => ∑ i, f (Y i)) _
  rw [h2]
  have hf2int : Integrable (fun y => f y ^ 2) (withDensityReal ρ) :=
    Integrable.of_bound (hfm.pow_const 2).aestronglyMeasurable (K ^ 2)
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have := hf y
        have h0 : 0 ≤ K := (abs_nonneg _).trans this
        nlinarith [abs_nonneg (f y), sq_abs (f y)])
  have h3 : ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * lam) * periodicRiesz d s (x - y)))
      ∂(withDensityReal ρ) ≤ ENNReal.ofReal (Real.exp (β * B) * ∫ y, f y ^ 2 ∂(withDensityReal ρ)) := by
    calc _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (β * B)) * ‖f y‖ₑ ^ 2 ∂(withDensityReal ρ) := by
          refine lintegral_mono fun y => ?_
          have e2 : ENNReal.ofReal (Real.exp (-(t * lam) * periodicRiesz d s (x - y))) ≤
              ENNReal.ofReal (Real.exp (β * B)) := by
            refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
            have h4 := hB (x - y)
            have h5 : 0 ≤ t * lam := mul_nonneg ht.1 hlam
            have h6 : t * lam ≤ β := by
              have : lam ≤ β := by
                rw [hlamdef, div_le_iff₀ hN0]
                have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
                nlinarith
              nlinarith [ht.2]
            nlinarith
          rw [mul_comm]
          exact mul_le_mul' e2 le_rfl
      _ = ENNReal.ofReal (Real.exp (β * B)) * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(withDensityReal ρ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = _ := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
          congr 1
          rw [ofReal_integral_eq_lintegral_ofReal hf2int (Eventually.of_forall fun y => sq_nonneg _)]
          refine lintegral_congr fun y => ?_
          rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have h4 : (evariance (fun Y : Config d n => ∑ i, f (Y i))
        (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t)).toReal ≤
      C₁ * n * (Real.exp (β * B) * ∫ y, f y ^ 2 ∂(withDensityReal ρ)) := by
    have h5 := h1.trans (mul_le_mul' le_rfl h3)
    rw [← ENNReal.ofReal_mul (by positivity)] at h5
    have hI0 : 0 ≤ ∫ y, f y ^ 2 ∂(withDensityReal ρ) := integral_nonneg fun y => sq_nonneg _
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h5).trans
      (by rw [ENNReal.toReal_ofReal (by positivity)])
  calc (1 / (n : ℝ)) ^ 2 * (evariance _ _).toReal ≤
        (1 / (n : ℝ)) ^ 2 * (C₁ * n * (Real.exp (β * B) * ∫ y, f y ^ 2 ∂(withDensityReal ρ))) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = C₁ * Real.exp (β * B) * (∫ y, f y ^ 2 ∂(withDensityReal ρ)) / n := by field_simp

theorem pole_dual (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ f : Torus d → ℝ, Measurable f → ∀ K : ℝ, (∀ y, |f y| ≤ K) →
        |∫ y, f y ∂(firstMarginal
              (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)) -
            ∫ y, f y ∂(firstMarginal
              (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β))| ≤
          Cd * Real.sqrt (∫ y, f y ^ 2 ∂(withDensityReal ρ)) * Real.sqrt (deltaN d s N / N) := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨C₁, hC₁, hvar⟩ := PoleCavityAux.pole_variance_clause hd hs0 hsd β hβ ρ hρ
  obtain ⟨Cd, hCd⟩ := insDefect_le hd hs0 hsd hβ hρ
  obtain ⟨B, hB0, hB⟩ := MarginalAux.rieszB hd hs0 hsd
  have hgm := measurable_periodicRiesz hd hs0 hsd
  set K1 : ℝ := C₁ * Real.exp (β * B) with hK1
  set K2 : ℝ := |Cd| * Real.exp |Cd| with hK2
  have hK1p : 0 ≤ K1 := by positivity
  have hK2p : 0 ≤ K2 := by positivity
  refine ⟨2 * Real.sqrt (2 * (K1 * K2)), by positivity, fun N hN x t ht f hfm K hf => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hn1 : 0 < N - 1 := by omega
  have hn0 : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hn1
  have hnN : (N : ℝ) ≤ 2 * ((N - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hln : β / N * ((N - 1 : ℕ) : ℝ) ≤ β := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    have : β / N * ((N : ℝ) - 1) = β - β / N := by field_simp
    rw [this]; linarith
  set n : ℕ := N - 1 with hn
  set lam : ℝ := β / N with hlamdef
  set L : ℝ := ∫ y, f y ^ 2 ∂(withDensityReal ρ) with hL
  have hL0 : 0 ≤ L := integral_nonneg fun y => sq_nonneg _
  haveI hP0 := cavity_isProb hd hs0 hsd β hρ n lam hlam
  set P0 := cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β with hP0def
  have hδ0 : 0 ≤ deltaN d s N := by
    have := inv_le_deltaN (d := d) hs0 N (by omega)
    exact (inv_nonneg.2 hN0.le).trans this
  have hδ1 : deltaN d s N ≤ 1 := deltaN_le_one hs0 hsd (by omega) N (by omega)
  have hRHS : 0 ≤ 2 * Real.sqrt (2 * (K1 * K2)) * Real.sqrt L * Real.sqrt (deltaN d s N / N) := by
    positivity
  rcases eq_or_lt_of_le ht.1 with h0 | htpos
  · rw [← h0, poleLaw_zero_eq hd hs0 hsd β hρ n lam hlam x, ← hP0def, sub_self, abs_zero]
    exact hRHS
  have hXm' : Measurable fun Y : Config d n => t * Xx (periodicRiesz d s) lam x Y :=
    (measurable_Xx hgm lam x).const_mul t
  have hbX := Xx_le hd hs0 hsd hlam hln hB0 hB x
  have hb' : ∀ Y : Config d n, t * Xx (periodicRiesz d s) lam x Y ≤ β * B := by
    intro Y
    have h1 := hbX Y
    have h2 : 0 ≤ β * B := by positivity
    nlinarith [ht.2]
  have hφm := measurable_fracF (n := n) hfm
  have htv := EF.ef_tv (P := P0) hXm' hb' hφm (abs_fracF_le hn1 hf)
  have e1 : P0.tilted (fun Y => t * Xx (periodicRiesz d s) lam x Y) =
      poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t :=
    (poleLaw_eq_tilted_cavity hd hs0 hsd β hρ n lam hlam x t).symm
  have e0 : P0 = poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x 0 :=
    (poleLaw_zero_eq hd hs0 hsd β hρ n lam hlam x).symm
  haveI hPt := pole_isProb hd hs0 hsd β hρ n lam hlam x t ht.1
  have hint1 : ∫ Y, fracF f Y ∂(P0.tilted (fun Y => t * Xx (periodicRiesz d s) lam x Y)) =
      ∫ y, f y ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t)) := by
    rw [e1]
    exact integral_fracF hn1 hfm hf _ (poleLaw_exchangeable hd hs0 hsd β hρ n lam hlam x t)
  have hint0 : ∫ Y, fracF f Y ∂P0 = ∫ y, f y ∂(firstMarginal P0) :=
    integral_fracF hn1 hfm hf P0 (cavityLaw_exchangeable hd hs0 hsd β hρ n lam)
  have hV0 : Var[fracF (n := n) f; P0] ≤ (K1 * L) / (n : ℝ) := by
    rw [e0]
    have := var_fracF_le hd hs0 hsd hβ hρ hC₁ hvar hB0 hB (N := N) hN x (t := 0) ⟨le_rfl, zero_le_one⟩
      hfm hf
    rw [hK1, hL]; simpa [mul_assoc] using this
  have hV1 : Var[fracF (n := n) f; P0.tilted (fun Y => t * Xx (periodicRiesz d s) lam x Y)] ≤
      (K1 * L) / (n : ℝ) := by
    rw [e1]
    have := var_fracF_le hd hs0 hsd hβ hρ hC₁ hvar hB0 hB (N := N) hN x ht hfm hf
    rw [hK1, hL]; simpa [mul_assoc] using this
  -- the second difference of the cumulant generating function
  obtain ⟨-, -, hΔ1⟩ := hCd N hN x
  have hXmx := measurable_Xx hgm lam x (n := n)
  have hmono := cgf_diff_mono (P := P0) hXmx hbX htpos ht.2
  have hc1 : cgf (fun Y => t * Xx (periodicRiesz d s) lam x Y) P0 1 =
      cgf (Xx (periodicRiesz d s) lam x) P0 t := by
    unfold cgf mgf; congr 2; funext Y; congr 1; ring
  have hc2 : cgf (fun Y => t * Xx (periodicRiesz d s) lam x Y) P0 (1 / 2) =
      cgf (Xx (periodicRiesz d s) lam x) P0 (t / 2) := by
    unfold cgf mgf; congr 2; funext Y; congr 1; ring
  have hΔ' : cgf (fun Y => t * Xx (periodicRiesz d s) lam x Y) P0 1 -
      2 * cgf (fun Y => t * Xx (periodicRiesz d s) lam x Y) P0 (1 / 2) ≤
      |Cd| * deltaN d s N := by
    rw [hc1, hc2]
    exact (hmono.trans hΔ1).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hδ0)
  have hee := exp_sub_one_le _ |Cd| (deltaN d s N) hδ0 hδ1 (abs_nonneg _) hΔ'
  rw [hint1, hint0] at htv
  refine htv.trans ?_
  have hch := sqrt_chain (n := (n : ℝ)) (N := (N : ℝ)) hn0 hN0 hnN (mul_nonneg hK1p hL0) hK2p hδ0
    hV0 hV1 hee
  refine hch.trans (le_of_eq ?_)
  rw [show 2 * (K1 * L * K2) = (2 * (K1 * K2)) * L by ring, Real.sqrt_mul (by positivity)]
  ring

/-! ### Duality for densities and the mixture step -/

theorem mixture_dual {π ν : Measure (Torus d)} [IsProbabilityMeasure π] [IsProbabilityMeasure ν]
    (νx : Torus d → Measure (Torus d)) [∀ x, IsProbabilityMeasure (νx x)]
    (hmeas : ∀ A : Set (Torus d), MeasurableSet A → Measurable fun x => νx x A)
    (hmix : ∀ A : Set (Torus d), MeasurableSet A → π A = ∫⁻ x, νx x A ∂π)
    {f : Torus d → ℝ} (hfm : Measurable f) (hf0 : ∀ y, 0 ≤ f y) {M : ℝ} (hfM : ∀ y, f y ≤ M)
    {Bd : ℝ} (hbd : ∀ x, |∫ y, f y ∂(νx x) - ∫ y, f y ∂ν| ≤ Bd) :
    |∫ y, f y ∂π - ∫ y, f y ∂ν| ≤ Bd := by
  have hνm : Measurable νx := Measure.measurable_of_measurable_coe _ hmeas
  have hbind : π = Measure.bind π νx := by
    ext A hA
    rw [Measure.bind_apply hA hνm.aemeasurable, hmix A hA]
  have hfM0 : ∀ y, ‖f y‖ ≤ M := fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 y)]; exact hfM y
  have hfint : ∀ (m : Measure (Torus d)) [IsProbabilityMeasure m], Integrable f m := fun m _ =>
    Integrable.of_bound hfm.aestronglyMeasurable M (Eventually.of_forall hfM0)
  have hlf : Measurable fun y => ENNReal.ofReal (f y) := ENNReal.measurable_ofReal.comp hfm
  have hI : ∀ x, ∫ y, f y ∂(νx x) = (∫⁻ y, ENNReal.ofReal (f y) ∂(νx x)).toReal := fun x => by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfm.aestronglyMeasurable]
  have hmx : Measurable fun x => ∫⁻ y, ENNReal.ofReal (f y) ∂(νx x) :=
    (Measure.measurable_lintegral hlf).comp hνm
  have hfin : ∀ x, ∫⁻ y, ENNReal.ofReal (f y) ∂(νx x) ≠ ∞ := fun x => by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := M)) ?_
    calc ∫⁻ y, ENNReal.ofReal (f y) ∂(νx x) ≤ ∫⁻ _y, ENNReal.ofReal M ∂(νx x) :=
          lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hfM y)
      _ = ENNReal.ofReal M := by simp
  have hπ : ∫ y, f y ∂π = ∫ x, ∫ y, f y ∂(νx x) ∂π := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfm.aestronglyMeasurable]
    conv_lhs => rw [hbind]
    rw [Measure.lintegral_bind hνm.aemeasurable hlf.aemeasurable]
    simp_rw [hI]
    rw [integral_toReal hmx.aemeasurable (Eventually.of_forall fun x => (hfin x).lt_top)]
  have hint : Integrable (fun x => ∫ y, f y ∂(νx x)) π := by
    refine Integrable.of_bound (C := M) ?_ (Eventually.of_forall fun x => ?_)
    · simp_rw [hI]; exact hmx.ennreal_toReal.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg hf0)]
      calc ∫ y, f y ∂(νx x) ≤ ∫ _y, M ∂(νx x) :=
            integral_mono (hfint _) (integrable_const _) hfM
        _ = M := by simp
  rw [hπ]
  have : ∫ x, ∫ y, f y ∂(νx x) ∂π - ∫ y, f y ∂ν = ∫ x, (∫ y, f y ∂(νx x) - ∫ y, f y ∂ν) ∂π := by
    rw [integral_sub hint (integrable_const _)]
    simp
  rw [this, ← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := π)
    (f := fun x => ∫ y, f y ∂(νx x) - ∫ y, f y ∂ν) (C := Bd)
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hbd x)
  simpa using this

theorem l2_of_dual {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {p q : Torus d → ℝ}
    (hpm : Measurable p) (hqm : Measurable q) (hp0 : ∀ y, 0 ≤ p y) (hq0 : ∀ y, 0 ≤ q y)
    {M : ℝ} (hpM : ∀ y, p y ≤ M) (hqM : ∀ y, q y ≤ M) {Bd : ℝ} (hBd : 0 ≤ Bd)
    (hdual : ∀ f : Torus d → ℝ, Measurable f → (∀ y, 0 ≤ f y) → (∀ y, f y ≤ M) →
      |∫ y, f y * p y ∂μ - ∫ y, f y * q y ∂μ| ≤ Bd * Real.sqrt (∫ y, f y ^ 2 ∂μ)) :
    Real.sqrt (∫ y, (p y - q y) ^ 2 ∂μ) ≤ Real.sqrt 2 * Bd := by
  have hM0 : 0 ≤ M := (hp0 (Classical.arbitrary _)).trans (hpM _)
  have hbdd : ∀ (g : Torus d → ℝ), Measurable g → (∀ y, |g y| ≤ M) → Integrable g μ :=
    fun g hg hgb => Integrable.of_bound hg.aestronglyMeasurable M
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hgb y)
  set u : Torus d → ℝ := fun y => p y - q y with hu
  have hum : Measurable u := hpm.sub hqm
  have hub : ∀ y, |u y| ≤ M := fun y => by
    rw [abs_le]; constructor <;> linarith [hp0 y, hq0 y, hpM y, hqM y]
  set fp : Torus d → ℝ := fun y => max (u y) 0 with hfp
  set fn : Torus d → ℝ := fun y => max (-u y) 0 with hfn
  have hfpm : Measurable fp := hum.max measurable_const
  have hfnm : Measurable fn := hum.neg.max measurable_const
  have hfpM : ∀ y, fp y ≤ M := fun y => max_le (by linarith [(abs_le.1 (hub y)).2]) hM0
  have hfnM : ∀ y, fn y ≤ M := fun y => max_le (by linarith [(abs_le.1 (hub y)).1]) hM0
  have hfp0 : ∀ y, 0 ≤ fp y := fun y => le_max_right _ _
  have hfn0 : ∀ y, 0 ≤ fn y := fun y => le_max_right _ _
  have hfpb : ∀ y, |fp y| ≤ M := fun y => by rw [abs_of_nonneg (hfp0 y)]; exact hfpM y
  have hfnb : ∀ y, |fn y| ≤ M := fun y => by rw [abs_of_nonneg (hfn0 y)]; exact hfnM y
  have hpb : ∀ y, |p y| ≤ M := fun y => by rw [abs_of_nonneg (hp0 y)]; exact hpM y
  have hqb : ∀ y, |q y| ≤ M := fun y => by rw [abs_of_nonneg (hq0 y)]; exact hqM y
  have hsq : ∀ y, u y ^ 2 = fp y ^ 2 + fn y ^ 2 := by
    intro y
    simp only [hfp, hfn]
    rcases le_total (u y) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have hsq2 : ∀ y, u y ^ 2 = fp y * u y + fn y * (-u y) := by
    intro y
    simp only [hfp, hfn]
    rcases le_total (u y) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have hint2 : ∀ g : Torus d → ℝ, Measurable g → (∀ y, |g y| ≤ M) → Integrable (fun y => g y ^ 2) μ :=
    fun g hg hgb => Integrable.of_bound (hg.pow_const 2).aestronglyMeasurable (M ^ 2)
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have := hgb y
        nlinarith [abs_nonneg (g y), sq_abs (g y)])
  have hdp := hdual fp hfpm hfp0 hfpM
  have hdn := hdual fn hfnm hfn0 hfnM
  have e1 : ∫ y, u y ^ 2 ∂μ = (∫ y, fp y * p y ∂μ - ∫ y, fp y * q y ∂μ) +
      (∫ y, fn y * q y ∂μ - ∫ y, fn y * p y ∂μ) := by
    have hi : ∀ g w : Torus d → ℝ, Measurable g → (∀ y, |g y| ≤ M) → Measurable w →
        (∀ y, |w y| ≤ M) → Integrable (fun y => g y * w y) μ := by
      intro g w hg hgb hw hwb
      refine Integrable.of_bound (hg.mul hw).aestronglyMeasurable (M * M) (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hgb y) (hwb y) (abs_nonneg _) hM0
    have h1 := hi _ _ hfpm hfpb hpm hpb
    have h2 := hi _ _ hfpm hfpb hqm hqb
    have h3 := hi _ _ hfnm hfnb hqm hqb
    have h4 := hi _ _ hfnm hfnb hpm hpb
    rw [← integral_sub h1 h2, ← integral_sub h3 h4]
    have h5 := integral_add (h1.sub h2) (h3.sub h4)
    have h6 : ∫ y, u y ^ 2 ∂μ = ∫ y, ((fp y * p y - fp y * q y) + (fn y * q y - fn y * p y)) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun y => by
        have := hsq2 y
        simp only [hu] at this ⊢
        linarith [this])
    rw [h6]
    exact h5
  have hIp : ∫ y, fp y ^ 2 ∂μ + ∫ y, fn y ^ 2 ∂μ = ∫ y, u y ^ 2 ∂μ := by
    rw [← integral_add (hint2 _ hfpm hfpb) (hint2 _ hfnm hfnb)]
    exact integral_congr_ae (Eventually.of_forall fun y => (hsq y).symm)
  set I : ℝ := ∫ y, u y ^ 2 ∂μ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun y => sq_nonneg _
  have hP0 : 0 ≤ ∫ y, fp y ^ 2 ∂μ := integral_nonneg fun y => sq_nonneg _
  have hN0 : 0 ≤ ∫ y, fn y ^ 2 ∂μ := integral_nonneg fun y => sq_nonneg _
  set a := Real.sqrt (∫ y, fp y ^ 2 ∂μ) with ha
  set b := Real.sqrt (∫ y, fn y ^ 2 ∂μ) with hb
  have hab : a ^ 2 + b ^ 2 = I := by
    rw [ha, hb, Real.sq_sqrt hP0, Real.sq_sqrt hN0, hIp]
  have hIle : I ≤ Bd * (a + b) := by
    rw [e1]
    have := (le_abs_self _).trans hdp
    have := (le_abs_self _).trans hdn
    rw [abs_sub_comm] at hdn
    linarith [(le_abs_self _).trans hdn, (le_abs_self _).trans hdp]
  have hab2 : (a + b) ^ 2 ≤ 2 * I := by nlinarith [sq_nonneg (a - b)]
  have hsI : Real.sqrt I ≤ Real.sqrt 2 * Bd := by
    by_cases hI00 : I = 0
    · rw [hI00]; simp; positivity
    · have hIp' : 0 < I := lt_of_le_of_ne hI0 (Ne.symm hI00)
      have hsp : 0 < Real.sqrt I := Real.sqrt_pos.2 hIp'
      have h1 : a + b ≤ Real.sqrt 2 * Real.sqrt I := by
        rw [← Real.sqrt_mul (by norm_num)]
        exact Real.le_sqrt_of_sq_le hab2
      have h2 : I ≤ Bd * (Real.sqrt 2 * Real.sqrt I) :=
        hIle.trans (mul_le_mul_of_nonneg_left h1 hBd)
      have h3 : Real.sqrt I * Real.sqrt I = I := Real.mul_self_sqrt hI0
      nlinarith [Real.sqrt_nonneg 2]
  exact hsI

theorem integral_withDensity_real {μ : Measure (Torus d)} {ψ : Torus d → ℝ} (hψm : Measurable ψ)
    (hψ0 : ∀ y, 0 ≤ ψ y) (f : Torus d → ℝ) :
    ∫ y, f y ∂(μ.withDensity fun y => ENNReal.ofReal (ψ y)) = ∫ y, ψ y * f y ∂μ := by
  have h := integral_withDensity_eq_integral_toReal_smul (μ := μ) (f := ENNReal.ofReal ∘ ψ)
    (ENNReal.measurable_ofReal.comp hψm) (Eventually.of_forall fun y => ENNReal.ofReal_lt_top) f
  refine h.trans ?_
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [ENNReal.toReal_ofReal (hψ0 y)]

theorem isProb_firstMarginal {n : ℕ} (hn : 0 < n) (P : Measure (Config d n)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (firstMarginal P) := by
  unfold firstMarginal; rw [dif_pos hn]; infer_instance

section CavL2

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ)

include hd hs0 hsd hβ hρ

theorem cavity_L2 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ lam : ℝ, lam = β / ((n + 1 : ℕ) : ℝ) →
      Real.sqrt (∫ y, (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y -
          qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y) ^ 2 ∂(withDensityReal ρ)) ≤
        C * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Mp, hMp1, hMp⟩ := pDens_bounds hd hs0 hsd hβ hρ
  obtain ⟨Mq, hMq0, hMq⟩ := qDens_bound hd hs0 hsd hβ hρ
  obtain ⟨Cd, hCd0, hCd⟩ := pole_dual hd hs0 hsd hβ hρ
  refine ⟨Real.sqrt 2 * Cd, by positivity, fun n hn lam hlamdef => ?_⟩
  obtain ⟨hlam, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hN : 2 ≤ n + 1 := by omega
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
  have hqm := qDens_measurable hd hs0 hsd hβ hρ hn hlamdef
  have hacq := hMq (n + 1) hN
  have hlam' : lam = β / ((n + 1 : ℕ) : ℝ) := hlamdef
  have hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪
      withDensityReal ρ := by
    subst hlam'; exact hacq.1
  have hqb : ∀ᵐ y ∂(withDensityReal ρ), qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mq := by
    subst hlam'; exact hacq.2
  have hpb : ∀ y, pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mp := by
    subst hlam'; exact fun y => (hMp (n + 1) hN y).2
  set p := pDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hp
  set q := qDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hq
  set μ := withDensityReal ρ with hμdef
  have hp0 : ∀ y, 0 ≤ p y := fun y => (pDens_pos hd hs0 hsd hρ hlam hln y).le
  have hq0 : ∀ y, 0 ≤ q y := fun y => ENNReal.toReal_nonneg
  set qb : Torus d → ℝ := fun y => min (q y) Mq with hqbdef
  have hqbm : Measurable qb := hqm.min measurable_const
  have hqbq : q =ᵐ[μ] qb := hqb.mono fun y hy => by simp only [hqbdef, min_eq_left hy]
  have hqb0 : ∀ y, 0 ≤ qb y := fun y => le_min (hq0 y) hMq0.le
  have hqbM : ∀ y, qb y ≤ Mq := fun y => min_le_right _ _
  set M : ℝ := Mp + Mq with hM
  have hMp0 : 0 ≤ Mp := (hp0 (Classical.arbitrary _)).trans (hpb _)
  have hpM : ∀ y, p y ≤ M := fun y => by linarith [hpb y]
  have hqM : ∀ y, qb y ≤ M := fun y => by linarith [hqbM y]
  set Bd : ℝ := Cd * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) with hBd
  have hBd0 : 0 ≤ Bd := by positivity
  -- the measures
  have hπeq := firstMarginal_eq_withDensity hd hs0 hsd hρ hlam hln
  have hνeq := nu_eq_withDensity hd hs0 hsd hβ hρ hn hlamdef hac
  haveI hP0 := cavity_isProb hd hs0 hsd β hρ n lam hlam
  haveI hQ := cavity_isProb hd hs0 hsd β hρ (n + 1) lam hlam
  haveI hπp := isProb_firstMarginal (Nat.succ_pos n) (cavityLaw (periodicRiesz d s) μ (n + 1) lam β)
  haveI hνp := isProb_firstMarginal hn (cavityLaw (periodicRiesz d s) μ n lam β)
  haveI hνx : ∀ x : Torus d, IsProbabilityMeasure
      (firstMarginal (poleLaw (periodicRiesz d s) μ n lam β x 1)) := fun x => by
    haveI := pole_isProb hd hs0 hsd β hρ n lam hlam x 1 zero_le_one
    exact isProb_firstMarginal hn _
  have hdual : ∀ f : Torus d → ℝ, Measurable f → (∀ y, 0 ≤ f y) → (∀ y, f y ≤ M) →
      |∫ y, f y * p y ∂μ - ∫ y, f y * qb y ∂μ| ≤ Bd * Real.sqrt (∫ y, f y ^ 2 ∂μ) := by
    intro f hfm hf0 hfM
    have hmixd := mixture_dual (π := firstMarginal (cavityLaw (periodicRiesz d s) μ (n + 1) lam β))
      (ν := firstMarginal (cavityLaw (periodicRiesz d s) μ n lam β))
      (fun x => firstMarginal (poleLaw (periodicRiesz d s) μ n lam β x 1))
      (fun A hA => by
        have hA' : MeasurableSet {Y : Config d n | Y ⟨0, hn⟩ ∈ A} := (measurable_pi_apply _) hA
        have := measurable_poleLaw_set hd hs0 hsd hρ hlam hln hA'
        convert this using 2 with x
        unfold firstMarginal; rw [dif_pos hn, Measure.map_apply (measurable_pi_apply (⟨0, hn⟩ : Fin n)) hA]; rfl)
      (fun A hA => by
        rw [firstMarginal_disint hd hs0 hsd hρ hlam hln hn hA]
        refine lintegral_congr fun x => ?_
        unfold firstMarginal; rw [dif_pos hn, Measure.map_apply (measurable_pi_apply (⟨0, hn⟩ : Fin n)) hA]; rfl)
      hfm hf0 hfM (Bd := Bd * Real.sqrt (∫ y, f y ^ 2 ∂μ)) (fun x => by
        have := hCd (n + 1) hN x 1 ⟨zero_le_one, le_rfl⟩ f hfm M (fun y => by
          rw [abs_of_nonneg (hf0 y)]; exact hfM y)
        have e : β / ((n + 1 : ℕ) : ℝ) = lam := hlamdef.symm
        rw [e] at this
        exact this.trans (le_of_eq (by simp only [hBd]; ring)))
    rw [hπeq, hνeq, integral_withDensity_real hpm hp0, integral_withDensity_real hqm hq0] at hmixd
    have e2 : ∫ y, q y * f y ∂μ = ∫ y, qb y * f y ∂μ :=
      integral_congr_ae (hqbq.mono fun y hy => by simp only [← hy])
    rw [e2] at hmixd
    simp_rw [mul_comm (p _) (f _), mul_comm (qb _) (f _)] at hmixd
    simpa [mul_comm] using hmixd
  have hl2 := l2_of_dual hpm hqbm hp0 hqb0 hpM hqM hBd0 hdual
  have e3 : ∫ y, (p y - q y) ^ 2 ∂μ = ∫ y, (p y - qb y) ^ 2 ∂μ :=
    integral_congr_ae (hqbq.mono fun y hy => by simp only [← hy])
  rw [e3]
  refine hl2.trans (le_of_eq ?_)
  simp only [hBd]; ring

end CavL2

/-! ### Quantitative `L^∞` closeness of the first marginal to `μ` -/

section SupRate

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)

include hd hcrit hβ hρ hc

theorem Kt_sup_rate (M : ℝ) :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ h : Torus d → ℝ, Measurable h → (∀ y, |h y| ≤ M) →
      ∫ y, h y ∂(withDensityReal ρ) = 0 → ∀ e : ℝ, 0 ≤ e → e ≤ 1 →
      ∫ y, |h y| ∂(withDensityReal ρ) ≤ e → ∀ x : Torus d,
        |ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ) h x| ≤ CM * Real.sqrt e := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Cc, -, -, -, h4, -, -⟩ := critical_integrals hd hcrit β hβ ρ hρ c hc
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_density_bound hρ
  obtain ⟨B, Cck, hB0, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
  have hρm : Measurable ρ := hρ.density.measurable
  have hgpm := measurable_gPlus hd hs0 hsd c
  obtain ⟨CM, hCM⟩ := h4 (Λ * M)
  refine ⟨|CM|, abs_nonneg _, fun h hm hb hint0 e he0 he1 hl x => ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hb (Classical.arbitrary _))
  set w : Torus d → ℝ := fun y => ρ y * h y with hw
  have hwm : Measurable w := hρm.mul hm
  have hwb : ∀ y, |w y| ≤ Λ * M := by
    intro y
    have h2 : |ρ y| ≤ Λ := by rw [abs_of_pos (hρ.pos y)]; exact hΛ y
    rw [hw]; simp only [abs_mul]
    exact mul_le_mul h2 (hb y) (abs_nonneg _) hΛ0.le
  have hhi : Integrable h (withDensityReal ρ) :=
    Integrable.of_bound (C := M) hm.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hb y)
  have hl1 : ∫⁻ y, ‖w y‖ₑ ≤ ENNReal.ofReal e := by
    have e1 : ∀ y, ‖w y‖ₑ = ENNReal.ofReal (ρ y) * ‖h y‖ₑ := by
      intro y
      simp only [hw, enorm_mul, Real.enorm_of_nonneg (hρ.density.nonneg y)]
    simp_rw [e1]
    have hmρ : Measurable fun y => ENNReal.ofReal (ρ y) := ENNReal.measurable_ofReal.comp hρm
    have e2 : ∫⁻ y, ENNReal.ofReal (ρ y) * ‖h y‖ₑ = ∫⁻ y, ‖h y‖ₑ ∂(withDensityReal ρ) := by
      show _ = ∫⁻ y, ‖h y‖ₑ ∂(volume.withDensity fun x => ENNReal.ofReal (ρ x))
      rw [lintegral_withDensity_eq_lintegral_mul _ hmρ hm.enorm]
      rfl
    rw [e2]
    have e3 : ∫⁻ y, ‖h y‖ₑ ∂(withDensityReal ρ) = ENNReal.ofReal (∫ y, |h y| ∂(withDensityReal ρ)) := by
      rw [ofReal_integral_eq_lintegral_ofReal hhi.abs (Eventually.of_forall fun y => abs_nonneg _)]
      refine lintegral_congr fun y => ?_
      rw [Real.enorm_eq_ofReal_abs]
    rw [e3]
    exact ENNReal.ofReal_le_ofReal hl
  have h1 := hCM w e hwm hwb he1 hl1 x
  -- `Kt g μ h = Kt g_+ μ h` since `∫ h dμ = 0`
  have hgi := hK.int x
  have hgh : Integrable (fun y => periodicRiesz d s (x - y) * h y) (withDensityReal ρ) :=
    hgi.mul_bdd hm.aestronglyMeasurable (c := M) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hb y)
  have hKt : ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ) h x =
      ∫ y, gPlus d s c (x - y) * w y := by
    have e1 : ∫ y, gPlus d s c (x - y) * w y = ResponseAux.Kt (gPlus d s c) (withDensityReal ρ) h x := by
      rw [ResponseAux.Kt_eq_cv hρ.density]; rfl
    rw [e1]
    unfold ResponseAux.Kt
    have : ∀ y, gPlus d s c (x - y) * h y = periodicRiesz d s (x - y) * h y + c * h y := fun y => by
      unfold gPlus; ring
    simp_rw [this]
    rw [integral_add hgh (hhi.const_mul c), integral_const_mul, hint0]
    simp
  rw [hKt]
  have h2 : ‖∫ y, gPlus d s c (x - y) * w y‖ₑ ≤ ENNReal.ofReal (|CM| * Real.sqrt e) := by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine le_trans (le_of_eq ?_) (h1.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _))))
    refine lintegral_congr fun y => ?_
    have hg0 : 0 ≤ gPlus d s c (x - y) := hc _
    rw [enorm_mul, Real.enorm_of_nonneg hg0]
  rw [Real.enorm_eq_ofReal_abs] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

end SupRate

theorem l1_le_sqrt {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {h : Torus d → ℝ}
    (hm : Measurable h) {M : ℝ} (hb : ∀ y, |h y| ≤ M) :
    ∫ y, |h y| ∂μ ≤ Real.sqrt (∫ y, h y ^ 2 ∂μ) := by
  have hmem : MemLp (fun y => |h y|) 2 μ :=
    MemLp.of_bound hm.abs.aestronglyMeasurable M (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_abs]; exact hb y)
  have h1 : MemLp (fun _ : Torus d => (1 : ℝ)) 2 μ := memLp_const _
  have := EF.cs_integral hmem h1
  simp only [mul_one, one_pow, integral_const, probReal_univ, one_smul, sq_abs] at this
  exact Real.le_sqrt_of_sq_le this

section SupRate2

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)

include hd hcrit hβ hρ hc

theorem sup_dev_rate :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ lam : ℝ, lam = β / ((n + 1 : ℕ) : ℝ) → ∀ x : Torus d,
      |pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1| ≤
        C * Real.sqrt (deltaN d s (n + 1)) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Mp, hMp1, hMp⟩ := pDens_bounds hd hs0 hsd hβ hρ
  obtain ⟨Mq, hMq0, hMq⟩ := qDens_bound hd hs0 hsd hβ hρ
  obtain ⟨Kg, hKg0, hKg⟩ := convAbs_bound hd hs0 hsd hρ
  obtain ⟨Cd, hCd⟩ := insDefect_le hd hs0 hsd hβ hρ
  obtain ⟨C2, hC20, hC2⟩ := L2_all hd hs0 hsd hβ hρ
  obtain ⟨CL, hCL0, hCL⟩ := cavity_L2 hd hs0 hsd hβ hρ
  obtain ⟨CM, hCM0, hCM⟩ := Kt_sup_rate hd hcrit hβ hρ c hc (1 + Mq)
  set Ce : ℝ := C2 + CL with hCe
  have hCe0 : 0 ≤ Ce := by positivity
  set C3 : ℝ := β * CM * Real.sqrt Ce + β * (Kg * Mq) + |Cd| with hC3
  have hC30 : 0 ≤ C3 := by positivity
  refine ⟨max (2 * C3 * Real.exp (2 * C3)) ((Mp + 1) * Real.sqrt Ce), by positivity, ?_⟩
  intro n hn lam hlamdef x
  obtain ⟨hlam, hln, hlam1⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hN : 2 ≤ n + 1 := by omega
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlam' : lam = β / ((n + 1 : ℕ) : ℝ) := hlamdef
  have hδ0 : 0 ≤ deltaN d s (n + 1) := by
    have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
    exact (inv_nonneg.2 hN0.le).trans this
  have hδ1 : deltaN d s (n + 1) ≤ 1 := deltaN_le_one hs0 hsd (by omega) (n + 1) (by omega)
  have hδinv : ((n + 1 : ℕ) : ℝ)⁻¹ ≤ deltaN d s (n + 1) := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
  have hsδ : Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) ≤ deltaN d s (n + 1) := by
    rw [Real.sqrt_le_left hδ0]
    have : deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ) ≤ deltaN d s (n + 1) ^ 2 := by
      rw [div_eq_mul_inv, sq]
      exact mul_le_mul_of_nonneg_left hδinv hδ0
    exact this
  have hacq := hMq (n + 1) hN
  have hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪
      withDensityReal ρ := by
    subst hlam'; exact hacq.1
  have hqb : ∀ᵐ y ∂(withDensityReal ρ), qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mq := by
    subst hlam'; exact hacq.2
  have hpb : ∀ y, pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mp := by
    subst hlam'; exact fun y => (hMp (n + 1) hN y).2
  have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
  have hqm := qDens_measurable hd hs0 hsd hβ hρ hn hlamdef
  have hp0 : ∀ y, 0 < pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y :=
    pDens_pos hd hs0 hsd hρ hlam hln
  set p := pDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hp
  set q := qDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hq
  set μ := withDensityReal ρ with hμdef
  have hq0 : ∀ y, 0 ≤ q y := fun y => ENNReal.toReal_nonneg
  -- the case split
  by_cases hbig : Ce * deltaN d s (n + 1) ≤ 1
  · -- `L¹` bound on `1 - q`
    set qb : Torus d → ℝ := fun y => min (q y) Mq with hqbdef
    have hqbm : Measurable qb := hqm.min measurable_const
    have hqbq : q =ᵐ[μ] qb := hqb.mono fun y hy => by simp only [hqbdef, min_eq_left hy]
    have hqb0 : ∀ y, 0 ≤ qb y := fun y => le_min (hq0 y) hMq0.le
    have hqbM : ∀ y, qb y ≤ Mq := fun y => min_le_right _ _
    obtain ⟨hqi, hq1⟩ := integral_qDens hd hs0 hsd hβ hρ hn hlamdef hac
    have hh0 : ∫ y, (1 - qb y) ∂μ = 0 := by
      have e : ∫ y, (1 - qb y) ∂μ = ∫ y, (1 - q y) ∂μ :=
        integral_congr_ae (hqbq.mono fun y hy => by simp only [← hy])
      rw [e, integral_sub (integrable_const _) hqi, hq1]; simp
    -- `L²` bounds
    have hp2 : Real.sqrt (∫ y, (p y - 1) ^ 2 ∂μ) ≤ C2 * deltaN d s (n + 1) :=
      Real.sqrt_le_iff.2 ⟨by positivity, hC2 n hn lam hlamdef⟩
    have hpq2 : Real.sqrt (∫ y, (p y - q y) ^ 2 ∂μ) ≤ CL * deltaN d s (n + 1) := by
      have := hCL n hn lam hlamdef
      exact this.trans (mul_le_mul_of_nonneg_left hsδ hCL0)
    have hpb' : ∀ y, |p y - 1| ≤ Mp + 1 := fun y => by
      rw [abs_le]; constructor <;> linarith [hp0 y, hpb y]
    have hpqb : ∀ y, |p y - qb y| ≤ Mp + Mq := fun y => by
      rw [abs_le]; constructor <;> linarith [hp0 y, hpb y, hqb0 y, hqbM y]
    have hl1a : ∫ y, |p y - 1| ∂μ ≤ C2 * deltaN d s (n + 1) :=
      (l1_le_sqrt (h := fun y => p y - 1) (hpm.sub measurable_const) hpb').trans hp2
    have hl1b : ∫ y, |p y - qb y| ∂μ ≤ CL * deltaN d s (n + 1) := by
      have e : ∫ y, (p y - qb y) ^ 2 ∂μ = ∫ y, (p y - q y) ^ 2 ∂μ :=
        integral_congr_ae (hqbq.mono fun y hy => by simp only [← hy])
      refine (l1_le_sqrt (h := fun y => p y - qb y) (hpm.sub hqbm) hpqb).trans ?_
      rw [e]; exact hpq2
    have hpi : Integrable p μ := Integrable.of_bound (C := Mp) hpm.aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_pos (hp0 y)]; exact hpb y)
    have hqbi : Integrable qb μ := Integrable.of_bound (C := Mq) hqbm.aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hqb0 y)]; exact hqbM y)
    have hl1 : ∫ y, |1 - qb y| ∂μ ≤ Ce * deltaN d s (n + 1) := by
      have h1 : Integrable (fun y => |p y - 1|) μ := (hpi.sub (integrable_const _)).abs
      have h2 : Integrable (fun y => |p y - qb y|) μ := (hpi.sub hqbi).abs
      have h3 : Integrable (fun y => |1 - qb y|) μ := ((integrable_const (1 : ℝ)).sub hqbi).abs
      have hle : ∫ y, |1 - qb y| ∂μ ≤ ∫ y, (|p y - 1| + |p y - qb y|) ∂μ := by
        refine integral_mono h3 (h1.add h2) fun y => ?_
        have := abs_add_le (1 - p y) (p y - qb y)
        rw [show (1 - p y) + (p y - qb y) = 1 - qb y by ring, abs_sub_comm 1 (p y)] at this
        exact this
      rw [integral_add h1 h2] at hle
      rw [hCe]; nlinarith
    have hbb : ∀ y, |1 - qb y| ≤ 1 + Mq := fun y => by
      rw [abs_le]; constructor <;> linarith [hqb0 y, hqbM y]
    have hKt := hCM (fun y => 1 - qb y) (measurable_const.sub hqbm) hbb hh0
      (Ce * deltaN d s (n + 1)) (by positivity) hbig hl1
    have hKt' : ∀ x, |ResponseAux.Kt (periodicRiesz d s) μ (fun y => 1 - q y) x| ≤
        CM * Real.sqrt (Ce * deltaN d s (n + 1)) := by
      intro x
      have hae : (fun y => 1 - q y) =ᵐ[μ] fun y => 1 - qb y :=
        hqbq.mono fun y hy => by simp only [← hy]
      rw [ResponseAux.Kt_congr _ hae]
      exact hKt x
    have hu : ∀ y, |uIns (periodicRiesz d s) μ n lam β y| ≤
        β * |ResponseAux.Kt (periodicRiesz d s) μ (fun y => 1 - q y) y| + lam * (Kg * Mq) +
          |insDefect (periodicRiesz d s) μ n lam β y| := fun y =>
      uIns_le_aux hd hs0 hsd hβ hρ hn hlamdef hac hMq0.le hqb (fun x => hKg x) y
    have hlamδ : lam ≤ β * deltaN d s (n + 1) := by
      rw [hlam', div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hδinv hβ.le
    have hsq : Real.sqrt (Ce * deltaN d s (n + 1)) = Real.sqrt Ce * Real.sqrt (deltaN d s (n + 1)) :=
      Real.sqrt_mul hCe0 _
    have hδs : deltaN d s (n + 1) ≤ Real.sqrt (deltaN d s (n + 1)) := by
      have h0 := Real.sqrt_nonneg (deltaN d s (n + 1))
      have h1 := Real.sq_sqrt hδ0
      have h2 : Real.sqrt (deltaN d s (n + 1)) ≤ 1 := by
        rw [Real.sqrt_le_one]; exact hδ1
      nlinarith
    have hsδ1 : Real.sqrt (deltaN d s (n + 1)) ≤ 1 := by rw [Real.sqrt_le_one]; exact hδ1
    have hu_le : ∀ y, |uIns (periodicRiesz d s) μ n lam β y| ≤ C3 * Real.sqrt (deltaN d s (n + 1)) := by
      intro y
      refine (hu y).trans ?_
      have hD : 0 ≤ insDefect (periodicRiesz d s) μ n lam β y ∧
          insDefect (periodicRiesz d s) μ n lam β y ≤ Cd * deltaN d s (n + 1) := by
        have := hCd (n + 1) hN y
        rw [← hlam'] at this
        exact ⟨this.1, this.2.1⟩
      have hD1 : |insDefect (periodicRiesz d s) μ n lam β y| ≤ |Cd| * deltaN d s (n + 1) := by
        rw [abs_of_nonneg hD.1]
        exact hD.2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hδ0)
      have h1 : β * |ResponseAux.Kt (periodicRiesz d s) μ (fun y => 1 - q y) y| ≤
          β * (CM * (Real.sqrt Ce * Real.sqrt (deltaN d s (n + 1)))) := by
        rw [← hsq]; exact mul_le_mul_of_nonneg_left (hKt' y) hβ.le
      have h2 : lam * (Kg * Mq) ≤ β * (Kg * Mq) * Real.sqrt (deltaN d s (n + 1)) := by
        calc lam * (Kg * Mq) ≤ (β * deltaN d s (n + 1)) * (Kg * Mq) :=
              mul_le_mul_of_nonneg_right hlamδ (by positivity)
          _ ≤ (β * Real.sqrt (deltaN d s (n + 1))) * (Kg * Mq) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδs hβ.le) (by positivity)
          _ = _ := by ring
      have h3 : |Cd| * deltaN d s (n + 1) ≤ |Cd| * Real.sqrt (deltaN d s (n + 1)) :=
        mul_le_mul_of_nonneg_left hδs (abs_nonneg _)
      have e : C3 * Real.sqrt (deltaN d s (n + 1)) = β * (CM * (Real.sqrt Ce * Real.sqrt (deltaN d s (n + 1)))) +
          β * (Kg * Mq) * Real.sqrt (deltaN d s (n + 1)) + |Cd| * Real.sqrt (deltaN d s (n + 1)) := by
        simp only [hC3]; ring
      linarith [h1, h2, h3, hD1, e]
    have hη : 0 ≤ C3 * Real.sqrt (deltaN d s (n + 1)) := mul_nonneg hC30 (Real.sqrt_nonneg _)
    have hdev := pDens_dev hd hs0 hsd hρ hlam hln hη hu_le x
    refine hdev.trans ?_
    have hexp : Real.exp (2 * (C3 * Real.sqrt (deltaN d s (n + 1)))) - 1 ≤
        2 * (C3 * Real.sqrt (deltaN d s (n + 1))) *
          Real.exp (2 * (C3 * Real.sqrt (deltaN d s (n + 1)))) := by
      have h := Real.add_one_le_exp (-(2 * (C3 * Real.sqrt (deltaN d s (n + 1)))))
      have h3 : Real.exp (-(2 * (C3 * Real.sqrt (deltaN d s (n + 1))))) *
          Real.exp (2 * (C3 * Real.sqrt (deltaN d s (n + 1)))) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (2 * (C3 * Real.sqrt (deltaN d s (n + 1))))]
    refine hexp.trans ?_
    have hE : Real.exp (2 * (C3 * Real.sqrt (deltaN d s (n + 1)))) ≤ Real.exp (2 * C3) :=
      Real.exp_le_exp.2 (by
        have := mul_le_mul_of_nonneg_left hsδ1 hC30
        linarith)
    calc 2 * (C3 * Real.sqrt (deltaN d s (n + 1))) *
          Real.exp (2 * (C3 * Real.sqrt (deltaN d s (n + 1))))
        ≤ 2 * (C3 * Real.sqrt (deltaN d s (n + 1))) * Real.exp (2 * C3) :=
          mul_le_mul_of_nonneg_left hE (mul_nonneg (by norm_num) hη)
      _ = (2 * C3 * Real.exp (2 * C3)) * Real.sqrt (deltaN d s (n + 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  · push Not at hbig
    have hpx : |p x - 1| ≤ Mp + 1 := by
      rw [abs_le]; constructor <;> linarith [hp0 x, hpb x]
    refine hpx.trans ?_
    have h1 : 1 ≤ Real.sqrt Ce * Real.sqrt (deltaN d s (n + 1)) := by
      rw [← Real.sqrt_mul hCe0]
      exact Real.one_le_sqrt.2 hbig.le
    calc Mp + 1 ≤ (Mp + 1) * (Real.sqrt Ce * Real.sqrt (deltaN d s (n + 1))) :=
          le_mul_of_one_le_right (by linarith) h1
      _ = ((Mp + 1) * Real.sqrt Ce) * Real.sqrt (deltaN d s (n + 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)

end SupRate2

/-! ### `L²(μ)` boundedness of the operator with kernel `g` -/

section KtL2

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)

include hd hcrit hβ hρ hc

theorem Kt_L2 :
    ∃ CS : ℝ, 0 ≤ CS ∧ ∀ f : Torus d → ℝ, Measurable f →
      ∫⁻ x, ENNReal.ofReal ((ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ) f x) ^ 2)
          ∂(withDensityReal ρ) ≤
        ENNReal.ofReal CS * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(withDensityReal ρ) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Cc, -, -, h3, -, -, -⟩ := critical_integrals hd hcrit β hβ ρ hρ c hc
  have hgm := measurable_periodicRiesz hd hs0 hsd
  have hgpm := measurable_gPlus hd hs0 hsd c
  refine ⟨2 * |Cc| + 2 * c ^ 2, by positivity, fun f hfm => ?_⟩
  set μ := withDensityReal ρ with hμdef
  have hfe : Measurable fun y => ‖f y‖ₑ := hfm.enorm
  set A : Torus d → ℝ≥0∞ := fun x => ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) * ‖f y‖ₑ ∂μ with hA
  set I1 : ℝ≥0∞ := ∫⁻ y, ‖f y‖ₑ ∂μ with hI1
  set K : ℝ≥0∞ := ENNReal.ofReal |c| * I1 with hK
  have hpt : ∀ x, ENNReal.ofReal ((ResponseAux.Kt (periodicRiesz d s) μ f x) ^ 2) ≤
      2 * (A x) ^ 2 + 2 * K ^ 2 := by
    intro x
    have h1 : ENNReal.ofReal ((ResponseAux.Kt (periodicRiesz d s) μ f x) ^ 2) =
        ‖ResponseAux.Kt (periodicRiesz d s) μ f x‖ₑ ^ 2 := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    rw [h1]
    have h2 : ‖ResponseAux.Kt (periodicRiesz d s) μ f x‖ₑ ≤ A x + K := by
      unfold ResponseAux.Kt
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      have h3' : ∀ y, ‖periodicRiesz d s (x - y) * f y‖ₑ ≤
          ENNReal.ofReal (gPlus d s c (x - y)) * ‖f y‖ₑ + ENNReal.ofReal |c| * ‖f y‖ₑ := by
        intro y
        rw [enorm_mul, ← add_mul]
        refine mul_le_mul' ?_ le_rfl
        have hg0 : 0 ≤ gPlus d s c (x - y) := hc _
        rw [← ENNReal.ofReal_add hg0 (abs_nonneg c), Real.enorm_eq_ofReal_abs]
        refine ENNReal.ofReal_le_ofReal ?_
        have hg0' : 0 ≤ periodicRiesz d s (x - y) + c := hc _
        unfold gPlus
        rw [abs_le]; constructor <;> cases abs_cases c <;> cases abs_cases (periodicRiesz d s (x - y)) <;> linarith
      have hmeasA : Measurable fun y => ENNReal.ofReal (gPlus d s c (x - y)) * ‖f y‖ₑ :=
        (ENNReal.measurable_ofReal.comp (hgpm.comp (measurable_const.sub measurable_id))).mul hfe
      calc ∫⁻ y, ‖periodicRiesz d s (x - y) * f y‖ₑ ∂μ ≤
            ∫⁻ y, (ENNReal.ofReal (gPlus d s c (x - y)) * ‖f y‖ₑ + ENNReal.ofReal |c| * ‖f y‖ₑ) ∂μ :=
            lintegral_mono h3'
        _ = A x + K := by
            rw [lintegral_add_left hmeasA, lintegral_const_mul _ hfe]
    calc ‖ResponseAux.Kt (periodicRiesz d s) μ f x‖ₑ ^ 2 ≤ (A x + K) ^ 2 := by gcongr
      _ ≤ 2 * (A x ^ 2 + K ^ 2) := by
          have := ENNReal.rpow_add_le_mul_rpow_add_rpow (A x) K (p := 2) (by norm_num)
          rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_two, ENNReal.rpow_two,
            ENNReal.rpow_two] at this
          exact this
      _ = _ := by ring
  have hmA : Measurable A := by
    refine Measurable.lintegral_prod_right' (f := fun q : Torus d × Torus d =>
      ENNReal.ofReal (gPlus d s c (q.1 - q.2)) * ‖f q.2‖ₑ) ?_
    exact (ENNReal.measurable_ofReal.comp (hgpm.comp (measurable_fst.sub measurable_snd))).mul
      (hfe.comp measurable_snd)
  have hI1sq : I1 ^ 2 ≤ ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ := by
    have := lintegral_mul_sq_le μ (fun y => ‖f y‖ₑ) (fun _ => 1) hfe.aemeasurable aemeasurable_const
    simpa [hI1] using this
  have hK2 : K ^ 2 = ENNReal.ofReal (c ^ 2) * I1 ^ 2 := by
    rw [hK, mul_pow, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  calc ∫⁻ x, ENNReal.ofReal ((ResponseAux.Kt (periodicRiesz d s) μ f x) ^ 2) ∂μ
      ≤ ∫⁻ x, (2 * (A x) ^ 2 + 2 * K ^ 2) ∂μ := lintegral_mono hpt
    _ = 2 * ∫⁻ x, (A x) ^ 2 ∂μ + 2 * K ^ 2 := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ (hmA.pow_const 2)]
        simp
    _ ≤ 2 * (ENNReal.ofReal |Cc| * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ) +
          2 * (ENNReal.ofReal (c ^ 2) * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ) := by
        refine add_le_add (mul_le_mul' le_rfl ?_) (mul_le_mul' le_rfl ?_)
        · exact (h3 f hfm).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_abs_self _)) le_rfl)
        · exact hK2.trans_le (mul_le_mul' le_rfl hI1sq)
    _ = ENNReal.ofReal (2 * |Cc| + 2 * c ^ 2) * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num)]
        simp only [ENNReal.ofReal_ofNat]
        ring

end KtL2

/-! ### The response equation -/

theorem integral_projMean_zero {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {h : Torus d → ℝ}
    (hi : Integrable h μ) : ∫ x, projMean μ h x ∂μ = 0 := by
  unfold projMean pair
  rw [integral_sub hi (integrable_const _)]; simp

theorem sqrt_int_add_le {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {a b : Torus d → ℝ}
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    Real.sqrt (∫ x, (a x + b x) ^ 2 ∂μ) ≤
      Real.sqrt (∫ x, a x ^ 2 ∂μ) + Real.sqrt (∫ x, b x ^ 2 ∂μ) := by
  have hcs := EF.cs_integral ha hb
  have hA : 0 ≤ ∫ x, a x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hB : 0 ≤ ∫ x, b x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hab : ∫ x, a x * b x ∂μ ≤ Real.sqrt (∫ x, a x ^ 2 ∂μ) * Real.sqrt (∫ x, b x ^ 2 ∂μ) := by
    rw [← Real.sqrt_mul hA]
    exact Real.le_sqrt_of_sq_le hcs
  have e : ∫ x, (a x + b x) ^ 2 ∂μ =
      ∫ x, a x ^ 2 ∂μ + 2 * ∫ x, a x * b x ∂μ + ∫ x, b x ^ 2 ∂μ := by
    have h1 : Integrable (fun x => a x ^ 2) μ := ha.integrable_sq
    have h2 : Integrable (fun x => b x ^ 2) μ := hb.integrable_sq
    have h3 : Integrable (fun x => a x * b x) μ := ha.integrable_mul hb
    have : (fun x => (a x + b x) ^ 2) = fun x => (a x ^ 2 + 2 * (a x * b x)) + b x ^ 2 := by
      funext x; ring
    rw [this]
    have h4 : ∫ x, ((a x ^ 2 + 2 * (a x * b x)) + b x ^ 2) ∂μ =
        ∫ x, (a x ^ 2 + 2 * (a x * b x)) ∂μ + ∫ x, b x ^ 2 ∂μ :=
      integral_add (h1.add (h3.const_mul 2)) h2
    have h5 : ∫ x, (a x ^ 2 + 2 * (a x * b x)) ∂μ =
        ∫ x, a x ^ 2 ∂μ + ∫ x, 2 * (a x * b x) ∂μ := integral_add h1 (h3.const_mul 2)
    rw [h4, h5, integral_const_mul]
  rw [e]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt hA
  have h2 := Real.sq_sqrt hB
  nlinarith [Real.sqrt_nonneg (∫ x, a x ^ 2 ∂μ), Real.sqrt_nonneg (∫ x, b x ^ 2 ∂μ)]

theorem log_sub_bound {p Mp : ℝ} (hp : Real.exp (-Mp) ≤ p) :
    0 ≤ (p - 1) - Real.log p ∧ (p - 1) - Real.log p ≤ Real.exp Mp * (p - 1) ^ 2 := by
  have hp0 : 0 < p := lt_of_lt_of_le (Real.exp_pos _) hp
  refine ⟨by linarith [Real.log_le_sub_one_of_pos hp0], ?_⟩
  have h1 := Real.one_sub_inv_le_log_of_pos hp0
  have h2 : p⁻¹ ≤ Real.exp Mp := by
    have : p⁻¹ ≤ (Real.exp (-Mp))⁻¹ := inv_anti₀ (Real.exp_pos _) hp
    rwa [← Real.exp_neg, neg_neg] at this
  have h3 : (p - 1) - (1 - p⁻¹) = p⁻¹ * (p - 1) ^ 2 := by field_simp
  calc (p - 1) - Real.log p ≤ (p - 1) - (1 - p⁻¹) := by linarith
    _ = p⁻¹ * (p - 1) ^ 2 := h3
    _ ≤ Real.exp Mp * (p - 1) ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

theorem Kt_bdd {μ : Measure (Torus d)} {g : Torus d → ℝ} {f : Torus d → ℝ} {M Kg : ℝ}
    (hgi : ∀ x, Integrable (fun y => g (x - y)) μ) (hKg : ∀ x : Torus d, ∫ y, |g (x - y)| ∂μ ≤ Kg)
    (hf : ∀ y, |f y| ≤ M) (hfm : Measurable f) (x : Torus d) :
    |ResponseAux.Kt g μ f x| ≤ M * Kg := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hf (Classical.arbitrary _))
  unfold ResponseAux.Kt
  refine (abs_integral_le_integral_abs).trans ?_
  have hint : Integrable (fun y => g (x - y) * f y) μ :=
    (hgi x).mul_bdd hfm.aestronglyMeasurable (c := M) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hf y)
  calc ∫ y, |g (x - y) * f y| ∂μ ≤ ∫ y, M * |g (x - y)| ∂μ := by
        refine integral_mono hint.abs (((hgi x).abs).const_mul _) fun y => ?_
        show |g (x - y) * f y| ≤ M * |g (x - y)|
        rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hf y) (abs_nonneg _)
    _ = M * ∫ y, |g (x - y)| ∂μ := integral_const_mul _ _
    _ ≤ M * Kg := mul_le_mul_of_nonneg_left (hKg x) hM0

section Resp

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)

include hd hcrit hβ hρ hc

theorem Kt_L2_real :
    ∃ CS : ℝ, 0 ≤ CS ∧ ∀ f : Torus d → ℝ, Measurable f → ∀ M : ℝ, (∀ y, |f y| ≤ M) →
      Integrable (fun x => (ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ) f x) ^ 2)
          (withDensityReal ρ) ∧
        ∫ x, (ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ) f x) ^ 2 ∂(withDensityReal ρ) ≤
          CS * ∫ y, f y ^ 2 ∂(withDensityReal ρ) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨CS, hCS0, hCS⟩ := Kt_L2 hd hcrit hβ hρ c hc
  refine ⟨CS, hCS0, fun f hfm M hfM => ?_⟩
  have hfi : Integrable (fun y => f y ^ 2) (withDensityReal ρ) :=
    Integrable.of_bound (hfm.pow_const 2).aestronglyMeasurable (M ^ 2) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have := hfM y
      nlinarith [abs_nonneg (f y), sq_abs (f y)])
  have hI0 : 0 ≤ ∫ y, f y ^ 2 ∂(withDensityReal ρ) := integral_nonneg fun y => sq_nonneg _
  have h1 : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(withDensityReal ρ) = ENNReal.ofReal (∫ y, f y ^ 2 ∂(withDensityReal ρ)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall fun y => sq_nonneg _)]
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have h2 := hCS f hfm
  rw [h1, ← ENNReal.ofReal_mul hCS0] at h2
  exact integral_sq_le_of_lintegral (measurable_Kt hd hs0 hsd hβ hρ hfm) (by positivity) h2

end Resp

section Resp2

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)

include hd hcrit hβ hρ hc

set_option maxHeartbeats 1600000 in
theorem response_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ lam : ℝ, lam = β / ((n + 1 : ℕ) : ℝ) →
      MemLp (fun x => (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1) +
          β * Kop (periodicRiesz d s) (withDensityReal ρ)
            (fun y => pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y - 1) x -
          projMean (withDensityReal ρ)
            (insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β) x) 2 (withDensityReal ρ) ∧
      Real.sqrt (∫ x, ((pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1) +
          β * Kop (periodicRiesz d s) (withDensityReal ρ)
            (fun y => pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y - 1) x -
          projMean (withDensityReal ρ)
            (insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β) x) ^ 2
          ∂(withDensityReal ρ)) ≤
        C * (deltaN d s (n + 1) * Real.sqrt (deltaN d s (n + 1)) +
          Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) + 1 / ((n + 1 : ℕ) : ℝ)) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Mp, hMp1, hMp⟩ := pDens_bounds hd hs0 hsd hβ hρ
  obtain ⟨Mq, hMq0, hMq⟩ := qDens_bound hd hs0 hsd hβ hρ
  obtain ⟨Kg, hKg0, hKg⟩ := convAbs_bound hd hs0 hsd hρ
  obtain ⟨C2, hC20, hC2⟩ := L2_all hd hs0 hsd hβ hρ
  obtain ⟨CL, hCL0, hCL⟩ := cavity_L2 hd hs0 hsd hβ hρ
  obtain ⟨CS, hCS0, hCS⟩ := Kt_L2_real hd hcrit hβ hρ c hc
  obtain ⟨Rr, hRr0, hRr⟩ := sup_dev_rate hd hcrit hβ hρ c hc
  obtain ⟨Cd, hCd⟩ := insDefect_le hd hs0 hsd hβ hρ
  obtain ⟨B, Cck, hB0, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
  have hgm := measurable_periodicRiesz hd hs0 hsd
  refine ⟨Real.exp Mp * Rr * C2 + β * Real.sqrt CS * CL + β * (Kg * Mq), by positivity, ?_⟩
  intro n hn lam hlamdef
  obtain ⟨hlam, hln, hlam1⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hN : 2 ≤ n + 1 := by omega
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlam' : lam = β / ((n + 1 : ℕ) : ℝ) := hlamdef
  have hδ0 : 0 ≤ deltaN d s (n + 1) := by
    have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
    exact (inv_nonneg.2 hN0.le).trans this
  have hacq := hMq (n + 1) hN
  have hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪
      withDensityReal ρ := by
    subst hlam'; exact hacq.1
  have hqb : ∀ᵐ y ∂(withDensityReal ρ), qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mq := by
    subst hlam'; exact hacq.2
  have hpb : ∀ y, pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mp := by
    subst hlam'; exact fun y => (hMp (n + 1) hN y).2
  have hplow : ∀ y, Real.exp (-Mp) ≤ pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y := by
    subst hlam'; exact fun y => (hMp (n + 1) hN y).1
  have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
  have hqm := qDens_measurable hd hs0 hsd hβ hρ hn hlamdef
  have hp1 := integral_pDens hd hs0 hsd hρ hlam hln
  have hcav := fun x => cavity_eq_z hd hs0 hsd hβ hρ hn hlamdef hac hpb hqb x
  set p := pDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hp
  set q := qDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hq
  set μ := withDensityReal ρ with hμdef
  set D := insDefect (periodicRiesz d s) μ n lam β with hD
  set Z0 : ℝ := ∫ y, Real.exp (uIns (periodicRiesz d s) μ n lam β y) ∂μ with hZ0
  have hp0 : ∀ y, 0 < p y := pDens_pos hd hs0 hsd hρ hlam hln
  have hq0 : ∀ y, 0 ≤ q y := fun y => ENNReal.toReal_nonneg
  set qb : Torus d → ℝ := fun y => min (q y) Mq with hqbdef
  have hqbm : Measurable qb := hqm.min measurable_const
  have hqbq : q =ᵐ[μ] qb := hqb.mono fun y hy => by simp only [hqbdef, min_eq_left hy]
  have hqb0 : ∀ y, 0 ≤ qb y := fun y => le_min (hq0 y) hMq0.le
  have hqbM : ∀ y, qb y ≤ Mq := fun y => min_le_right _ _
  set z : Torus d → ℝ := fun y => p y - 1 with hz
  have hzm : Measurable z := hpm.sub measurable_const
  have hzb : ∀ y, |z y| ≤ Mp := fun y => by
    rw [abs_le]; constructor <;> linarith [hp0 y, hpb y]
  have hRsup : ∀ y, |z y| ≤ Rr * Real.sqrt (deltaN d s (n + 1)) := fun y => hRr n hn lam hlamdef y
  have hgi := hK.int
  have hKgabs : ∀ x : Torus d, ∫ y, |periodicRiesz d s (x - y)| ∂μ ≤ Kg := hKg
  -- the three convolutions
  set Kz : Torus d → ℝ := ResponseAux.Kt (periodicRiesz d s) μ z with hKz
  set Kpq : Torus d → ℝ := ResponseAux.Kt (periodicRiesz d s) μ (fun y => p y - qb y) with hKpq
  set Kq : Torus d → ℝ := ResponseAux.Kt (periodicRiesz d s) μ qb with hKq
  have hKzm : Measurable Kz := measurable_Kt hd hs0 hsd hβ hρ hzm
  have hKpqm : Measurable Kpq := measurable_Kt hd hs0 hsd hβ hρ (hpm.sub hqbm)
  have hKqm : Measurable Kq := measurable_Kt hd hs0 hsd hβ hρ hqbm
  have hpqb : ∀ y, |p y - qb y| ≤ Mp + Mq := fun y => by
    rw [abs_le]; constructor <;> linarith [hp0 y, hpb y, hqb0 y, hqbM y]
  have hqbb : ∀ y, |qb y| ≤ Mq := fun y => by rw [abs_of_nonneg (hqb0 y)]; exact hqbM y
  have hKzb : ∀ x, |Kz x| ≤ Mp * Kg := fun x => Kt_bdd hgi hKgabs hzb hzm x
  have hKpqb : ∀ x, |Kpq x| ≤ (Mp + Mq) * Kg := fun x => Kt_bdd hgi hKgabs hpqb (hpm.sub hqbm) x
  have hKqb : ∀ x, |Kq x| ≤ Mq * Kg := fun x => Kt_bdd hgi hKgabs hqbb hqbm x
  have hKpq_eq : ResponseAux.Kt (periodicRiesz d s) μ (fun y => p y - q y) = Kpq :=
    ResponseAux.Kt_congr _ (hqbq.mono fun y hy => by simp only [← hy])
  have hKq_eq : ResponseAux.Kt (periodicRiesz d s) μ q = Kq :=
    ResponseAux.Kt_congr _ hqbq
  -- the cavity equation rewritten
  have hDeq : ∀ x, D x = Real.log (1 + z x) + β * Kz x - (β * Kpq x + lam * Kq x) + Real.log Z0 := by
    intro x
    have h := hcav x
    rw [hKpq_eq, hKq_eq] at h
    simp only [hz, hKz] at h ⊢
    linarith [h]
  have hbi : ∀ f : Torus d → ℝ, Measurable f → ∀ M : ℝ, (∀ x, |f x| ≤ M) → Integrable f μ :=
    fun f hf M hb => Integrable.of_bound hf.aestronglyMeasurable M
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)
  have hbm : ∀ f : Torus d → ℝ, Measurable f → ∀ M : ℝ, (∀ x, |f x| ≤ M) → MemLp f 2 μ :=
    fun f hf M hb => MemLp.of_bound hf.aestronglyMeasurable M
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)
  have hDm : Measurable D := by
    have : D = fun x => Real.log (1 + z x) + β * Kz x - (β * Kpq x + lam * Kq x) + Real.log Z0 :=
      funext hDeq
    rw [this]
    exact (((Real.measurable_log.comp (measurable_const.add hzm)).add (hKzm.const_mul β)).sub
      ((hKpqm.const_mul β).add (hKqm.const_mul lam))).add measurable_const
  have hDb : ∀ x, |D x| ≤ |Cd| * deltaN d s (n + 1) := by
    intro x
    have hD' : 0 ≤ D x ∧ D x ≤ Cd * deltaN d s (n + 1) := by
      have := hCd (n + 1) hN x
      rw [← hlam'] at this
      exact ⟨this.1, this.2.1⟩
    rw [abs_of_nonneg hD'.1]
    exact hD'.2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hδ0)
  -- the pieces `ΔL = z - log (1 + z)` and `eF`
  set ΔL : Torus d → ℝ := fun x => z x - Real.log (1 + z x) with hΔL
  set eF : Torus d → ℝ := fun x => β * Kpq x + lam * Kq x with heF
  have h1z : ∀ x, 1 + z x = p x := fun x => by simp only [hz]; ring
  have hΔLm : Measurable ΔL := hzm.sub (Real.measurable_log.comp (measurable_const.add hzm))
  have hΔLb : ∀ x, 0 ≤ ΔL x ∧ ΔL x ≤ Real.exp Mp * z x ^ 2 := by
    intro x
    have := log_sub_bound (p := p x) (Mp := Mp) (hplow x)
    simp only [hΔL, h1z]
    simpa [hz] using this
  have hΔLbb : ∀ x, |ΔL x| ≤ Real.exp Mp * Mp ^ 2 := by
    intro x
    rw [abs_of_nonneg (hΔLb x).1]
    refine (hΔLb x).2.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
    have := hzb x
    nlinarith [abs_nonneg (z x), sq_abs (z x)]
  have heFm : Measurable eF := (hKpqm.const_mul β).add (hKqm.const_mul lam)
  have heFb : ∀ x, |eF x| ≤ |β| * ((Mp + Mq) * Kg) + |lam| * (Mq * Kg) := by
    intro x
    simp only [heF]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hKpqb x) (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hKqb x) (abs_nonneg _)
  set G : Torus d → ℝ := fun x => ΔL x + eF x with hG
  have hGm : Measurable G := hΔLm.add heFm
  have hGb : ∀ x, |G x| ≤ Real.exp Mp * Mp ^ 2 + (|β| * ((Mp + Mq) * Kg) + |lam| * (Mq * Kg)) :=
    fun x => (abs_add_le _ _).trans (add_le_add (hΔLbb x) (heFb x))
  have hGi : Integrable G μ := hbi G hGm _ hGb
  have hGmem : MemLp G 2 μ := hbm G hGm _ hGb
  -- the function `F` of the statement
  set m : ℝ := Real.log Z0 + β * ∫ x, Kz x ∂μ - ∫ x, D x ∂μ with hm
  have hKzi : Integrable Kz μ := hbi Kz hKzm _ hKzb
  have hDi : Integrable D μ := hbi D hDm _ hDb
  set F : Torus d → ℝ := fun x => z x + β * Kop (periodicRiesz d s) μ z x - projMean μ D x with hF
  have hFeq : ∀ x, F x = G x - m := by
    intro x
    have hKop : Kop (periodicRiesz d s) μ z x = Kz x - ∫ x', Kz x' ∂μ := rfl
    have hpm' : projMean μ D x = D x - ∫ x', D x' ∂μ := rfl
    simp only [hF, hKop, hpm', hG, hΔL, heF, hm]
    have := hDeq x
    linarith [this]
  have hzint : ∫ x, z x ∂μ = 0 := by
    have hpi : Integrable p μ := hbi p hpm (Mp) (fun x => by rw [abs_of_pos (hp0 x)]; exact hpb x)
    show ∫ x, (p x - 1) ∂μ = 0
    rw [integral_sub hpi (integrable_const _), hp1]; simp
  have hF0 : ∫ x, F x ∂μ = 0 := by
    have hzi : Integrable z μ := hbi z hzm Mp hzb
    have h1 : ∫ x, Kop (periodicRiesz d s) μ z x ∂μ = 0 := integral_projMean_zero hKzi
    have h2 : ∫ x, projMean μ D x ∂μ = 0 := integral_projMean_zero hDi
    have hKopi : Integrable (fun x => Kop (periodicRiesz d s) μ z x) μ := hKzi.sub (integrable_const _)
    have hpDi : Integrable (fun x => projMean μ D x) μ := hDi.sub (integrable_const _)
    simp only [hF]
    have e1 : ∫ x, (z x + β * Kop (periodicRiesz d s) μ z x - projMean μ D x) ∂μ =
        ∫ x, (z x + β * Kop (periodicRiesz d s) μ z x) ∂μ - ∫ x, projMean μ D x ∂μ :=
      integral_sub (hzi.add (hKopi.const_mul β)) hpDi
    have e2 : ∫ x, (z x + β * Kop (periodicRiesz d s) μ z x) ∂μ =
        ∫ x, z x ∂μ + ∫ x, β * Kop (periodicRiesz d s) μ z x ∂μ :=
      integral_add hzi (hKopi.const_mul β)
    rw [e1, e2, integral_const_mul, h1, h2, hzint]
    simp
  have hGint : ∫ x, G x ∂μ = m := by
    have : ∫ x, F x ∂μ = ∫ x, G x ∂μ - m := by
      have e : (fun x => F x) = fun x => G x - m := funext hFeq
      rw [e, integral_sub hGi (integrable_const _)]; simp
    linarith [hF0, this]
  have hF2 : ∫ x, F x ^ 2 ∂μ ≤ ∫ x, G x ^ 2 ∂μ := by
    have hG2i : Integrable (fun x => G x ^ 2) μ := hGmem.integrable_sq
    have e : ∫ x, F x ^ 2 ∂μ = ∫ x, G x ^ 2 ∂μ - m ^ 2 := by
      have e1 : (fun x => F x ^ 2) = fun x => G x ^ 2 + (-(2 * m) * G x + m ^ 2) := by
        funext x; rw [hFeq]; ring
      have e2 : ∫ x, (G x ^ 2 + (-(2 * m) * G x + m ^ 2)) ∂μ =
          ∫ x, G x ^ 2 ∂μ + ∫ x, (-(2 * m) * G x + m ^ 2) ∂μ :=
        integral_add hG2i ((hGi.const_mul _).add (integrable_const _))
      have e3 : ∫ x, (-(2 * m) * G x + m ^ 2) ∂μ =
          ∫ x, -(2 * m) * G x ∂μ + ∫ x, m ^ 2 ∂μ :=
        integral_add (hGi.const_mul _) (integrable_const _)
      rw [e1, e2, e3, integral_const_mul, hGint]
      simp; ring
    rw [e]; nlinarith [sq_nonneg m]
  -- the `L²` estimates
  set δ := deltaN d s (n + 1) with hδ
  have hz2 : ∫ x, z x ^ 2 ∂μ ≤ (C2 * δ) ^ 2 := hC2 n hn lam hlamdef
  have hzmem : MemLp z 2 μ := hbm z hzm Mp hzb
  have hΔmem : MemLp ΔL 2 μ := hbm ΔL hΔLm _ hΔLbb
  have heFmem : MemLp eF 2 μ := hbm eF heFm _ heFb
  have hΔ2 : ∫ x, ΔL x ^ 2 ∂μ ≤ (Real.exp Mp * (Rr * Real.sqrt δ) * (C2 * δ)) ^ 2 := by
    have hpt : ∀ x, ΔL x ^ 2 ≤ (Real.exp Mp * (Rr * Real.sqrt δ)) ^ 2 * z x ^ 2 := by
      intro x
      have h1 := hΔLb x
      have h2 : ΔL x ^ 2 ≤ (Real.exp Mp * z x ^ 2) ^ 2 := pow_le_pow_left₀ h1.1 h1.2 2
      have h3 : z x ^ 2 ≤ (Rr * Real.sqrt δ) ^ 2 := by
        have := hRsup x
        nlinarith [abs_nonneg (z x), sq_abs (z x)]
      calc ΔL x ^ 2 ≤ (Real.exp Mp * z x ^ 2) ^ 2 := h2
        _ = (Real.exp Mp) ^ 2 * z x ^ 2 * z x ^ 2 := by ring
        _ ≤ (Real.exp Mp) ^ 2 * (Rr * Real.sqrt δ) ^ 2 * z x ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
        _ = _ := by ring
    calc ∫ x, ΔL x ^ 2 ∂μ ≤ ∫ x, (Real.exp Mp * (Rr * Real.sqrt δ)) ^ 2 * z x ^ 2 ∂μ :=
          integral_mono hΔmem.integrable_sq (hzmem.integrable_sq.const_mul _) hpt
      _ = (Real.exp Mp * (Rr * Real.sqrt δ)) ^ 2 * ∫ x, z x ^ 2 ∂μ := integral_const_mul _ _
      _ ≤ (Real.exp Mp * (Rr * Real.sqrt δ)) ^ 2 * (C2 * δ) ^ 2 :=
          mul_le_mul_of_nonneg_left hz2 (sq_nonneg _)
      _ = _ := by ring
  have hT1 : Real.sqrt (∫ x, ΔL x ^ 2 ∂μ) ≤ Real.exp Mp * Rr * C2 * (δ * Real.sqrt δ) := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    refine hΔ2.trans (le_of_eq ?_)
    ring
  -- the forcing term
  have hpq2 : ∫ x, (p x - qb x) ^ 2 ∂μ ≤ (CL * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ))) ^ 2 := by
    have e : ∫ x, (p x - qb x) ^ 2 ∂μ = ∫ x, (p x - q x) ^ 2 ∂μ :=
      integral_congr_ae (hqbq.mono fun y hy => by simp only [← hy])
    rw [e]
    exact (Real.sqrt_le_iff.1 (hCL n hn lam hlamdef)).2
  obtain ⟨-, hKpq2⟩ := hCS (fun y => p y - qb y) (hpm.sub hqbm) (Mp + Mq) hpqb
  have hKpq2' : ∫ x, Kpq x ^ 2 ∂μ ≤ CS * (CL * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ))) ^ 2 :=
    hKpq2.trans (mul_le_mul_of_nonneg_left hpq2 hCS0)
  have hKpqmem : MemLp (fun x => β * Kpq x) 2 μ := hbm _ (hKpqm.const_mul β) _ (fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hKpqb x) (abs_nonneg _))
  have hKqmem : MemLp (fun x => lam * Kq x) 2 μ := hbm _ (hKqm.const_mul lam) _ (fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hKqb x) (abs_nonneg _))
  have hTa : Real.sqrt (∫ x, (β * Kpq x) ^ 2 ∂μ) ≤
      β * Real.sqrt CS * CL * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    calc ∫ x, (β * Kpq x) ^ 2 ∂μ = β ^ 2 * ∫ x, Kpq x ^ 2 ∂μ := by
          rw [← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall fun x => by ring)
      _ ≤ β ^ 2 * (CS * (CL * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ))) ^ 2) :=
          mul_le_mul_of_nonneg_left hKpq2' (sq_nonneg _)
      _ = (β * Real.sqrt CS * CL * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ))) ^ 2 := by
          have := Real.sq_sqrt hCS0
          calc _ = β ^ 2 * (Real.sqrt CS) ^ 2 * (CL * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ))) ^ 2 := by
                rw [this]; ring
            _ = _ := by ring
  have hTb : Real.sqrt (∫ x, (lam * Kq x) ^ 2 ∂μ) ≤ lam * (Mq * Kg) := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    calc ∫ x, (lam * Kq x) ^ 2 ∂μ ≤ ∫ _x, (lam * (Mq * Kg)) ^ 2 ∂μ := by
          refine integral_mono (hKqmem.integrable_sq) (integrable_const _) fun x => ?_
          have : |lam * Kq x| ≤ lam * (Mq * Kg) := by
            rw [abs_mul, abs_of_nonneg hlam]; exact mul_le_mul_of_nonneg_left (hKqb x) hlam
          nlinarith [abs_nonneg (lam * Kq x), sq_abs (lam * Kq x)]
      _ = _ := by simp
  have hT2 : Real.sqrt (∫ x, eF x ^ 2 ∂μ) ≤
      β * Real.sqrt CS * CL * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) + lam * (Mq * Kg) := by
    have := sqrt_int_add_le hKpqmem hKqmem
    exact this.trans (add_le_add hTa hTb)
  have hTG : Real.sqrt (∫ x, G x ^ 2 ∂μ) ≤ Real.sqrt (∫ x, ΔL x ^ 2 ∂μ) + Real.sqrt (∫ x, eF x ^ 2 ∂μ) :=
    sqrt_int_add_le hΔmem heFmem
  have hfin : Real.sqrt (∫ x, F x ^ 2 ∂μ) ≤ Real.sqrt (∫ x, G x ^ 2 ∂μ) := Real.sqrt_le_sqrt hF2
  have hFmem : MemLp F 2 μ := by
    have : F = fun x => G x - m := funext hFeq
    rw [this]; exact hGmem.sub (memLp_const m)
  refine ⟨hFmem, hfin.trans (hTG.trans ?_)⟩
  have hlamE : lam * (Mq * Kg) = β * (Kg * Mq) * (1 / ((n + 1 : ℕ) : ℝ)) := by
    rw [hlam']; field_simp
  have hAB : 0 ≤ δ * Real.sqrt δ := by positivity
  have hBB : 0 ≤ Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) := Real.sqrt_nonneg _
  have hEE : 0 ≤ 1 / ((n + 1 : ℕ) : ℝ) := by positivity
  set c1 := Real.exp Mp * Rr * C2 with hc1
  set c2 := β * Real.sqrt CS * CL with hc2
  set c3 := β * (Kg * Mq) with hc3
  have hc10 : 0 ≤ c1 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  have hc30 : 0 ≤ c3 := by positivity
  have hexp : (c1 + c2 + c3) * (δ * Real.sqrt δ + Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) + 1 / ((n + 1 : ℕ) : ℝ)) -
      (c1 * (δ * Real.sqrt δ) + c2 * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) + c3 * (1 / ((n + 1 : ℕ) : ℝ))) =
      c1 * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) + c1 * (1 / ((n + 1 : ℕ) : ℝ)) + c2 * (δ * Real.sqrt δ) +
      c2 * (1 / ((n + 1 : ℕ) : ℝ)) + c3 * (δ * Real.sqrt δ) + c3 * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) := by
    ring
  have hnn : 0 ≤ c1 * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) + c1 * (1 / ((n + 1 : ℕ) : ℝ)) + c2 * (δ * Real.sqrt δ) +
      c2 * (1 / ((n + 1 : ℕ) : ℝ)) + c3 * (δ * Real.sqrt δ) + c3 * Real.sqrt (δ / ((n + 1 : ℕ) : ℝ)) := by
    positivity
  rw [hlamE] at hT2
  nlinarith [hT1, hT2, hexp, hnn]

end Resp2

end CavResp

end HRS

end
