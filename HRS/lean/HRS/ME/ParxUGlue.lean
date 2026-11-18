import HRS.ME.ParxU
import HRS.Equilibrium.Parametrix.PXSAuxCoef
import HRS.Equilibrium.Parametrix.PXSAuxJpair
import HRS.PDE.MeanFieldPairInverse

/-!
# Packet P5: uniform glue constants (`aCoef_bound`, `ak_bound`, `jpair_smooth`)

Uniform versions of `HRS.Parx.pxS_aCoef_bound` (PXSAuxCoef:60), `HRS.Parx.pxS_ak_bound`
(PXSAuxJpair:321), `HRS.Parx.pxS_jpair_smooth` (PXSAuxJpair:412), and of the glue-level
`HRS.Parx.aCoef_bound`, `HRS.Parx.jpair_smooth` (Glue.lean).

Each statement is the original with the `ParxHyp d s V β ρ` hypothesis replaced by
`ParxU d s N νm νp c₀ Λ₀ β V ρ` and the existential constant moved in front of `∀ β V ρ`.
The only supremum of an expression of `ρ` in the proofs is `Λ = sup ρ`, replaced by `|Λ₀|`
(`ParxU.abs_rho_le`), and the compactness constant `C` of `abs_Lop_le` (sup of `∑ⱼ|∂ⱼρ/ρ|`),
replaced by `∑ⱼ Aⱼ` with `Aⱼ` from `ParxU.partial_div_cbNorm_bound`.
Hypotheses that are not about `ρ` (`2 ≤ d`, `0 ≤ s`, `s < d`, `1 ≤ N`) are arguments of the
statements that need them, because they are needed before `∀ β V ρ`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-! ### Extractors on `ρ` (no new hypotheses) -/

/-- Positivity `0 < ρ`, from `c₀ > 0` and `c₀ ≤ ρ`. -/
theorem ParxU.rho_pos {β : ℝ} {V ρ : Torus d → ℝ} (U : ParxU d s N νm νp c₀ Λ₀ β V ρ) (x : Torus d) :
    0 < ρ x :=
  lt_of_lt_of_le U.F.hc₀ (U.rho_ge x)

/-- `|ρ| ≤ |Λ₀|` pointwise: the uniform replacement of `Λ = sup |ρ|`. -/
theorem ParxU.abs_rho_le {β : ℝ} {V ρ : Torus d → ℝ} (U : ParxU d s N νm νp c₀ Λ₀ β V ρ)
    (x : Torus d) : |ρ x| ≤ |Λ₀| := by
  rw [abs_of_pos (U.rho_pos x)]
  exact (U.rho_le x).trans (le_abs_self _)

/-! ### The first-order coefficient `Lop` with a uniform constant -/

/-- `|L_β f| ≤ K |f|_{C²}` with `K = d + ∑ⱼ Aⱼ`, where `Aⱼ` bounds `|∂ⱼρ/ρ|` uniformly
(`ParxU.partial_div_cbNorm_bound` at `k = 0`); the uniform form of `PDE.MFPair.abs_Lop_le`. -/
theorem abs_Lop_le_unif (hN : 1 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ f : Torus d → ℝ, Torus.IsCk 2 f → ∀ x, |HRS.Lop ρ f x| ≤ K * Torus.cbNorm 2 f := by
  choose A hA0 hA using fun j : Fin d =>
    ParxU.partial_div_cbNorm_bound (d := d) (s := s) (N := N) (νm := νm) (νp := νp) (c₀ := c₀)
      (Λ₀ := Λ₀) j 0 (by omega)
  refine ⟨d + ∑ j, A j, add_nonneg (Nat.cast_nonneg d) (Finset.sum_nonneg fun j _ => hA0 j),
    fun β V ρ U f hf x => ?_⟩
  have hρ2 : Torus.IsCk 2 ρ := PDE.MFPair.isCk_of_smooth_ps U.H.rho_smooth.smooth 2
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps U.H.rho_smooth.smooth 1
  have hρc : Continuous ρ := PDE.MFAux.continuous_of_isCk hρ1
  have hpos : ∀ y, 0 < ρ y := U.rho_pos
  have hbd : ∀ j : Fin d, ∀ y, |Torus.partialDeriv j ρ y / ρ y| ≤ A j := by
    intro j y
    have hdj : Torus.IsCk 1 (Torus.partialDeriv j ρ) := PDE.isCk_one_partialDeriv j ρ hρ2
    have hcont : Continuous fun z => Torus.partialDeriv j ρ z / ρ z :=
      (PDE.MFAux.continuous_of_isCk hdj).div hρc fun z => (hpos z).ne'
    have h := HRS.PDE.norm_le_cbNorm_zero (fun z => Torus.partialDeriv j ρ z / ρ z) hcont y
    rw [Real.norm_eq_abs] at h
    exact h.trans (hA j β V ρ U)
  rw [PDE.MFPair.Lop_eq hρ1 hpos hf x]
  have h1 := PDE.MFPair.abs_laplacian_le (L := 2) le_rfl hf x
  have hcb := PDE.MFPair.cbNorm_nonneg_ps 2 f
  have hCx : ∑ j, |Torus.partialDeriv j ρ x / ρ x| ≤ ∑ j, A j :=
    Finset.sum_le_sum fun j _ => hbd j x
  have h2 : |∑ j, (Torus.partialDeriv j ρ x / ρ x) * Torus.partialDeriv j f x| ≤
      (∑ j, A j) * Torus.cbNorm 2 f := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |(Torus.partialDeriv j ρ x / ρ x) * Torus.partialDeriv j f x|
        ≤ ∑ j, |Torus.partialDeriv j ρ x / ρ x| * Torus.cbNorm 2 f := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (PDE.MFPair.abs_partialDeriv_le (L := 2) (by norm_num) hf j x)
            (abs_nonneg _)
      _ = (∑ j, |Torus.partialDeriv j ρ x / ρ x|) * Torus.cbNorm 2 f := by rw [Finset.sum_mul]
      _ ≤ (∑ j, A j) * Torus.cbNorm 2 f := mul_le_mul_of_nonneg_right hCx hcb
  calc |-(Torus.laplacian f x) - ∑ j, (Torus.partialDeriv j ρ x / ρ x) * Torus.partialDeriv j f x|
      ≤ |-(Torus.laplacian f x)| + |∑ j, (Torus.partialDeriv j ρ x / ρ x) * Torus.partialDeriv j f x| :=
        abs_sub _ _
    _ ≤ d * Torus.cbNorm 2 f + (∑ j, A j) * Torus.cbNorm 2 f := by
        rw [abs_neg]; exact add_le_add h1 h2
    _ = _ := by ring

/-! ### `aCoef_bound` (PXSAuxCoef:60) -/

/-- Uniform form of `pxS_aCoef_bound`: the constant `Ca = (1/2) d max(Cg,0) Λ₀' ∫φ` with
`Λ₀' = |Λ₀|` and `Cg` from `periodicRieszGrad_bound_tdist` (depends on `d, s` only). -/
theorem pxS_aCoef_bound_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ f : Torus d → ℝ, Torus.IsSmooth f →
        AEStronglyMeasurable (aCoef d s ρ f) (withDensityReal ρ) ∧
        ∀ x, |aCoef d s ρ f x| ≤ Ca * posSeminorm 2 f := by
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  obtain ⟨Cg, hCg⟩ := PDE.periodicRieszGrad_bound_tdist hd hs0 hsd
  set φ : Torus d → ℝ := fun z => KernelGrad.tdist z 0 ^ (-s) + KernelGrad.tdist z 0 with hφ
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => by
    have := Real.rpow_nonneg (KernelGrad.tdist_nonneg z 0) (-s)
    have := KernelGrad.tdist_nonneg z 0
    simp only [hφ]; positivity
  have hφm : Measurable φ :=
    (((CoercAux.continuous_tdist_zero.measurable).pow_const _).add
      CoercAux.continuous_tdist_zero.measurable)
  have hφi : Integrable φ :=
    (Commutator.SliceAux.integrable_tdist_rpow hd0 hs0 hsd).add
      (CoercAux.continuous_tdist_zero.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hI0 : 0 ≤ ∫ z, φ z := integral_nonneg hφ0
  refine ⟨(1 / 2) * d * max Cg 0 * |Λ₀| * ∫ z, φ z, by positivity,
    fun β V ρ U f hf => ?_⟩
  have hρ := U.H.rho_smooth
  have hρc : Continuous ρ :=
    PDE.MFAux.continuous_of_isCk (PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1)
  have hΛ' : ∀ x, ρ x ≤ |Λ₀| := fun x => (U.rho_le x).trans (le_abs_self _)
  have hΛ0 : 0 ≤ |Λ₀| := abs_nonneg _
  have hf2 : Torus.IsCk 2 f :=
    ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) from hf)
      (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top)
  have hP0 : 0 ≤ posSeminorm 2 f :=
    Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  -- pointwise bound of the transport kernel
  have hpt : ∀ x y : Torus d, ‖hTransport d s f x y‖ ≤
      d * posSeminorm 2 f * max Cg 0 * φ (x - y) := by
    intro x y
    unfold hTransport
    by_cases hxy : x = y
    · subst hxy
      simp only [sub_self, norm_zero, inner_zero_left]
      have := hφ0 (x - x)
      exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hP0) (le_max_right _ _)) (hφ0 _)
    · have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
      have ht : 0 < KernelGrad.tdist (x - y) 0 := by
        rw [KernelGrad.tdist_zero_right]
        refine norm_pos_iff.mpr fun h => hz ?_
        rw [← KernelGrad.mk_centeredRep (x - y), h]
        funext i; simp [Torus.mk]
      set t := KernelGrad.tdist (x - y) 0 with htdef
      have h1 := pxS_grad_lip f hf x y
      rw [KernelGrad.tdist_eq_sub_zero x y] at h1
      have h2 := hCg (x - y) hz
      have h2' : ‖periodicRieszGrad d s (x - y)‖ ≤ max Cg 0 * (t ^ (-s - 1) + 1) :=
        h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      have e : t * (t ^ (-s - 1) + 1) = t ^ (-s) + t := by
        have : t ^ (-s) = t ^ (-s - 1) * t := by
          rw [← Real.rpow_add_one ht.ne']; ring_nf
        rw [this]; ring
      calc ‖inner ℝ (Torus.grad f x - Torus.grad f y) (periodicRieszGrad d s (x - y))‖
          ≤ ‖Torus.grad f x - Torus.grad f y‖ * ‖periodicRieszGrad d s (x - y)‖ :=
            norm_inner_le_norm _ _
        _ ≤ (d * posSeminorm 2 f * t) * (max Cg 0 * (t ^ (-s - 1) + 1)) :=
            mul_le_mul h1 h2' (norm_nonneg _) (by positivity)
        _ = d * posSeminorm 2 f * max Cg 0 * (t * (t ^ (-s - 1) + 1)) := by ring
        _ = d * posSeminorm 2 f * max Cg 0 * φ (x - y) := by rw [e]
  have hgm : Measurable (periodicRieszGrad d s) := KernelGrad.measurable_periodicRieszGrad hsd
  have hgradc : Continuous (Torus.grad f) := Duality.grad_continuous hf2
  have hmeas : Measurable (fun p : Torus d × Torus d => hTransport d s f p.1 p.2) := by
    unfold hTransport
    refine Measurable.inner ?_ (hgm.comp (measurable_fst.sub measurable_snd))
    exact ((hgradc.measurable.comp measurable_fst).sub (hgradc.measurable.comp measurable_snd))
  refine ⟨?_, fun x => ?_⟩
  · have : StronglyMeasurable (fun x => ∫ y, hTransport d s f x y ∂(withDensityReal ρ)) := by
      have h1 : StronglyMeasurable (Function.uncurry fun x y => hTransport d s f x y) :=
        hmeas.stronglyMeasurable
      exact h1.integral_prod_right
    exact (this.const_mul (1 / 2)).aestronglyMeasurable
  · have hgi : Integrable (fun y => d * posSeminorm 2 f * max Cg 0 * φ (x - y)) (withDensityReal ρ) :=
      (CoercAux.integrable_conv_density hΛ' hφm hφi x).const_mul _
    have h1 : ‖∫ y, hTransport d s f x y ∂(withDensityReal ρ)‖ ≤
        ∫ y, d * posSeminorm 2 f * max Cg 0 * φ (x - y) ∂(withDensityReal ρ) :=
      norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall fun y => hpt x y)
    have h2 := CoercAux.integral_conv_density_le hΛ0 hΛ' hφ0 hφm hφi x
    have h3 : ∫ y, d * posSeminorm 2 f * max Cg 0 * φ (x - y) ∂(withDensityReal ρ) ≤
        d * posSeminorm 2 f * max Cg 0 * (|Λ₀| * ∫ z, φ z) := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left h2 (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hP0) (le_max_right _ _))
    unfold aCoef
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), ← Real.norm_eq_abs]
    calc 1 / 2 * ‖∫ y, hTransport d s f x y ∂(withDensityReal ρ)‖
        ≤ 1 / 2 * (d * posSeminorm 2 f * max Cg 0 * (|Λ₀| * ∫ z, φ z)) :=
          mul_le_mul_of_nonneg_left (h1.trans h3) (by norm_num)
      _ = _ := by ring

/-! ### `ak_bound` (PXSAuxJpair:321) -/

/-- Uniform form of `pxS_ak_bound`: `CJ0 = 2 G1 |Λ₀| (K 3)`... more precisely
`CJ0 = G1 * (|Λ₀| * (K * 3)) * 2` with `G1 = ∫|periodicRiesz|` and `K` from `abs_Lop_le_unif`. -/
theorem pxS_ak_bound_unif (hN : 1 ≤ N) :
    ∃ CJ0 : ℝ, 0 ≤ CJ0 ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (Ψ : Torus d → Torus d → ℝ) (B : ℝ), PDE.IsCk2 2 Ψ → 0 ≤ B →
        (∀ i ≤ 2, ∀ p, ‖iteratedFDeriv ℝ i (PDE.lift2 Ψ) p‖ ≤ B) →
          ∀ x y, |pxS_ak d s ρ Ψ x y| ≤ CJ0 * B := by
  obtain ⟨K, hK0, hL⟩ := abs_Lop_le_unif (d := d) (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hN
  set G1 := ∫ y, |periodicRiesz d s y| with hG1
  have hG10 : 0 ≤ G1 := integral_nonneg fun _ => abs_nonneg _
  refine ⟨2 * (G1 * (|Λ₀| * (K * 3))), by positivity,
    fun β V ρ U Ψ B hΨ hB0 hb x y => ?_⟩
  have H := U.H
  have hρ := H.rho_smooth
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1
  have hρc : Continuous ρ := PDE.MFAux.continuous_of_isCk hρ1
  have hd1 : 1 ≤ d := le_trans (by norm_num) H.two_le
  have hg := PDE.MFOneLe.integrable_periodicRiesz hd1 s H.s_nonneg H.s_lt
  set M : ℝ := G1 * (|Λ₀| * (K * (3 * B))) with hM
  have hM0 : 0 ≤ M := by positivity
  have hW : ∀ y' u : Torus d, |pxS_W ρ Ψ (u, y')| ≤ |Λ₀| * (K * (3 * B)) := by
    intro y' u
    unfold pxS_W
    rw [abs_neg, abs_mul]
    have h1 := hL β V ρ U (fun x' => Ψ x' y') (PDE.MFPair.isCk_slice 2 Ψ hΨ y') u
    have h2 := pxS_slice_cbNorm hΨ hb y'
    have h3 : |HRS.Lop ρ (fun x' => Ψ x' y') u| ≤ K * (3 * B) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 hK0)
    exact mul_le_mul (U.abs_rho_le u) h3 (abs_nonneg _) (abs_nonneg _)
  have hΦ : ∀ z, |Jop d s ρ (fun w => Ψ w y) z| ≤ M := by
    intro z
    rw [pxS_Jop_slice H hΨ y z]
    exact PDE.MFThermalExist.convFun_bound_of_le hg (hW y) z
  rw [pxS_ak_eq H Ψ x y]
  have h2 : |∫ z, ρ z * Jop d s ρ (fun w => Ψ w y) z| ≤ M := by
    rw [← Real.norm_eq_abs]
    have hi : Integrable (fun z => ρ z * M) :=
      (PDE.MFAdjoint.integrable_of_cont hρc).mul_const _
    calc ‖∫ z, ρ z * Jop d s ρ (fun w => Ψ w y) z‖ ≤ ∫ z, ρ z * M := by
          refine norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall fun z => ?_)
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.density.nonneg z)]
          exact mul_le_mul_of_nonneg_left (hΦ z) (hρ.density.nonneg z)
      _ = M := by rw [integral_mul_const, hρ.density.integral_one, one_mul]
  calc |Jop d s ρ (fun w => Ψ w y) x - ∫ z, ρ z * Jop d s ρ (fun w => Ψ w y) z|
      ≤ |Jop d s ρ (fun w => Ψ w y) x| + |∫ z, ρ z * Jop d s ρ (fun w => Ψ w y) z| := abs_sub _ _
    _ ≤ M + M := add_le_add (hΦ x) h2
    _ = 2 * (G1 * (|Λ₀| * (K * 3))) * B := by rw [hM]; ring

/-! ### `jpair_smooth` (PXSAuxJpair:412) -/

/-- Uniform form of `pxS_jpair_smooth`, with the constant `2 * CJ0` of `pxS_ak_bound_unif`. -/
theorem pxS_jpair_smooth_unif (hN : 1 ≤ N) :
    ∃ CJ : ℝ, 0 ≤ CJ ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ Ψ : Torus d → Torus d → ℝ, PDE.IsCk2 2 Ψ →
        PDE.DoublyCentered (withDensityReal ρ) Ψ →
          IsCanonicalPair (withDensityReal ρ) (Jpair d s ρ Ψ) ∧
          ∀ x y, |Jpair d s ρ Ψ x y| ≤ CJ * PDE.cbNorm2 2 Ψ := by
  obtain ⟨CJ0, hCJ0, hCJ⟩ := pxS_ak_bound_unif (d := d) (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hN
  refine ⟨2 * CJ0, by positivity, fun β V ρ U Ψ hΨ hdc => ?_⟩
  have H := U.H
  have hρ := H.rho_smooth
  have : IsProbabilityMeasure (withDensityReal ρ) :=
    PDE.MFSemigroup.isProb_withDensityReal hρ.density
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · have hΨT := pxS_isCk2_swap 2 hΨ
    have c1 := pxS_ak_continuous H hΨ
    have c2 := pxS_ak_continuous H hΨT
    have h1 : Continuous (fun y : Torus d => pxS_ak d s ρ Ψ x y) :=
      (c1.comp (continuous_const.prodMk continuous_id)).congr fun y => rfl
    have h2 : Continuous (fun y : Torus d => pxS_ak d s ρ (fun a b => Ψ b a) y x) :=
      (c2.comp (continuous_id.prodMk continuous_const)).congr fun y => rfl
    have hJ : (Jpair d s ρ Ψ x) = fun y => pxS_ak d s ρ Ψ x y +
        pxS_ak d s ρ (fun a b => Ψ b a) y x := rfl
    rw [hJ]
    have hi1 := h1.integrable_of_hasCompactSupport (μ := withDensityReal ρ) (HasCompactSupport.of_compactSpace _)
    have hi2 := h2.integrable_of_hasCompactSupport (μ := withDensityReal ρ) (HasCompactSupport.of_compactSpace _)
    refine ⟨hi1.add hi2, ?_⟩
    rw [integral_add hi1 hi2, pxS_ak_mean H hΨ hdc.2 x, pxS_ak_swap_mean H hΨ x, add_zero]
  · have hB0 := PDE.MFPair.cbNorm2_nonneg 2 Ψ
    have hΨT := pxS_isCk2_swap 2 hΨ
    have hb1 : ∀ i ≤ 2, ∀ p, ‖iteratedFDeriv ℝ i (PDE.lift2 Ψ) p‖ ≤ PDE.cbNorm2 2 Ψ :=
      fun i hi p => PDE.MFPair.norm_iteratedFDeriv_le_cbNorm2 hΨ hi p
    have hb2 : ∀ i ≤ 2, ∀ p, ‖iteratedFDeriv ℝ i (PDE.lift2 (fun a b => Ψ b a)) p‖ ≤
        PDE.cbNorm2 2 Ψ := by
      intro i hi p
      have e : PDE.lift2 (fun a b => Ψ b a) = PDE.lift2 Ψ ∘ ⇑(LinearIsometryEquiv.prodComm ℝ (Euc d) (Euc d)) :=
        rfl
      rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_right]
      exact hb1 i hi _
    have a1 := hCJ β V ρ U Ψ _ hΨ hB0 hb1 x y
    have a2 := hCJ β V ρ U (fun a b => Ψ b a) _ hΨT hB0 hb2 y x
    have hJ : Jpair d s ρ Ψ x y = pxS_ak d s ρ Ψ x y + pxS_ak d s ρ (fun a b => Ψ b a) y x := rfl
    rw [hJ]
    calc |pxS_ak d s ρ Ψ x y + pxS_ak d s ρ (fun a b => Ψ b a) y x|
        ≤ |pxS_ak d s ρ Ψ x y| + |pxS_ak d s ρ (fun a b => Ψ b a) y x| := abs_add_le _ _
      _ ≤ CJ0 * PDE.cbNorm2 2 Ψ + CJ0 * PDE.cbNorm2 2 Ψ := add_le_add a1 a2
      _ = 2 * CJ0 * PDE.cbNorm2 2 Ψ := by ring

/-! ### Glue-level statements (Glue.lean:140-150, in terms of `ParxU`) -/

/-- Glue-level `aCoef_bound` (Glue.lean) with the uniform bundle. -/
theorem aCoef_bound_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ f : Torus d → ℝ, Torus.IsSmooth f →
        AEStronglyMeasurable (aCoef d s ρ f) (withDensityReal ρ) ∧
        ∀ x, |aCoef d s ρ f x| ≤ Ca * posSeminorm 2 f :=
  pxS_aCoef_bound_unif hd hs0 hsd

/-- Glue-level `jpair_smooth` (Glue.lean) with the uniform bundle. -/
theorem jpair_smooth_unif (hN : 1 ≤ N) :
    ∃ CJ : ℝ, 0 ≤ CJ ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ Ψ : Torus d → Torus d → ℝ, PDE.IsCk2 2 Ψ →
        PDE.DoublyCentered (withDensityReal ρ) Ψ →
          IsCanonicalPair (withDensityReal ρ) (Jpair d s ρ Ψ) ∧
          ∀ x y, |Jpair d s ρ Ψ x y| ≤ CJ * PDE.cbNorm2 2 Ψ :=
  pxS_jpair_smooth_unif hN

end HRS.ME.ParxU

end
