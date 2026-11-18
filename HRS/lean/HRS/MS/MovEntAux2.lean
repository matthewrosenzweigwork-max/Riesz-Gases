import HRS.MS.MovEntAux1

/-!
# S6.6, packet P3: the entropy split `H(f|Q) = H(f|μ^{⊗N}) + βN∫F f + log K` on `ℝ^d`

Namespace `HRS.MS.MovEnt`, helper prefix `s66_`.  Infrastructure for `mov_entropy`; not a manuscript row.

* `s66_kl_tilted`: generic `klDiv ν (P.tilted f)` for `f` with `exp f` `P`-integrable and `f` `ν`-integrable (torus `movf_kl_tilted`
  without the upper bound: the integrability of `f` under `ν` replaces it).
* `s66_gibbs_data`: `GibbsWellDefined` and `|log K| ≤ C N δ_N` for the Euclidean modulated Gibbs law (S3.1 at `θ = 0`, `h = 0`).
* `s66_modGibbs_tilted`: `Whole.modulatedGibbs = π.tilted (-bN F)`.
* `s66_split`: finiteness equivalence and the identity of the split (with `F` integrable from the pair entropy inequality).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MovEnt

open HRS.Whole

local notation "wd" => Whole.withDensityReal

variable {d N : ℕ}

theorem s66_kl_tilted {α : Type*} [MeasurableSpace α] (P ν : Measure α) [IsProbabilityMeasure P]
    [IsProbabilityMeasure ν] {f : α → ℝ} (hexp : Integrable (fun x => Real.exp (f x)) P)
    (hfν : Integrable f ν) :
    (klDiv ν (P.tilted f) ≠ ⊤ ↔ klDiv ν P ≠ ⊤) ∧
    (klDiv ν P ≠ ⊤ →
      (klDiv ν (P.tilted f)).toReal =
        (klDiv ν P).toReal - ∫ x, f x ∂ν + Real.log (∫ x, Real.exp (f x) ∂P)) := by
  haveI : IsProbabilityMeasure (P.tilted f) := isProbabilityMeasure_tilted hexp
  have hPQ : P ≪ P.tilted f := absolutelyContinuous_tilted hexp
  have hQP : P.tilted f ≪ P := tilted_absolutelyContinuous P f
  refine ⟨⟨fun h => ?_, fun h1 => ?_⟩, fun h1 => ?_⟩
  · obtain ⟨hνQ, hint⟩ := klDiv_ne_top_iff.1 h
    have hνP : ν ≪ P := hνQ.trans hQP
    have e := llr_tilted_right hνP hexp
    have hllr : Integrable (llr ν P) ν := by
      have : Integrable (fun x => llr ν (P.tilted f) x + f x -
          Real.log (∫ z, Real.exp (f z) ∂P)) ν :=
        (hint.add hfν).sub (integrable_const _)
      refine this.congr ?_
      filter_upwards [e] with x hx
      rw [hx]; ring
    exact klDiv_ne_top hνP hllr
  · obtain ⟨hνP, hint⟩ := klDiv_ne_top_iff.1 h1
    exact klDiv_ne_top (hνP.trans hPQ) (integrable_llr_tilted_right hνP hfν hint hexp)
  · obtain ⟨hνP, hint⟩ := klDiv_ne_top_iff.1 h1
    rw [toReal_klDiv (hνP.trans hPQ) (integrable_llr_tilted_right hνP hfν hint hexp),
      toReal_klDiv hνP hint, integral_llr_tilted_right hνP hfν hexp hint]
    simp [probReal_univ]

/-- `GibbsWellDefined` and the pressure bound for the Euclidean modulated Gibbs law of a density of the S3.1 class. -/
theorem s66_gibbs_data (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M L bm bp : ℝ)
    (hbm : 0 < bm) (hb : bm < bp) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (s = 0 → HasLogMoment (wd ρ) L) → ∀ N : ℕ, 2 ≤ N → ∀ b ∈ Set.Icc bm bp,
        GibbsWellDefined (fun x y => rieszKernel d s (x - y)) N b (wd ρ) ∧
        |Real.log (pairNormalizer (fun x y => rieszKernel d s (x - y)) N b (wd ρ))| ≤
          C * N * deltaN d s N := by
  obtain ⟨θ₀, hθ₀, C, hC⟩ := HRS.MS.Wr.euclidean_pressure_proof hd hs0 hsd M L bm bp 0 hbm hb
  refine ⟨C, fun ρ hρ hM hL N hN b hb' => ?_⟩
  have hk : IsBoundedPairKernel s 0 (fun _ _ : Euc d => (0 : ℝ)) :=
    ⟨measurable_const, fun _ _ => rfl, fun x y _ => by simp⟩
  have := hC ρ hρ hM hL (fun _ _ => 0) hk N hN b hb' 0 (by simp [hθ₀.le])
  simpa using this

/-- The modulated Gibbs law is the tilt of `μ^{⊗N}` by `-bN F`. -/
theorem s66_modGibbs_tilted {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {b : ℝ} {s : ℝ}
    (hW : GibbsWellDefined (fun x y => rieszKernel d s (x - y)) N b μ) :
    Whole.modulatedGibbs (rieszKernel d s) N b μ =
      (Measure.pi fun _ : Fin N => μ).tilted
        (fun X => -b * N * pairEnergy (fun x y => rieszKernel d s (x - y)) X μ) := by
  set P := Measure.pi fun _ : Fin N => μ with hP
  set f : EucConfig d N → ℝ := fun X => -b * N * pairEnergy (fun x y => rieszKernel d s (x - y)) X μ
    with hf
  have hexp : Integrable (fun x => Real.exp (f x)) P := hW.weight_integrable
  have hK : 0 < ∫ x, Real.exp (f x) ∂P := hW.normalizer_pos
  unfold Whole.modulatedGibbs Measure.tilted
  have hKdef : Whole.gibbsNormalizer (rieszKernel d s) N b μ = ∫ x, Real.exp (f x) ∂P := rfl
  rw [hKdef]
  have e : (fun x => ENNReal.ofReal (Real.exp (f x) / ∫ x, Real.exp (f x) ∂P)) =
      (ENNReal.ofReal (∫ x, Real.exp (f x) ∂P))⁻¹ • fun x => ENNReal.ofReal (Real.exp (f x)) := by
    funext x
    rw [ENNReal.ofReal_div_of_pos hK]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.div_eq_inv_mul]
  rw [e, withDensity_smul' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hK).ne')]
  rfl

/-- **The entropy split** for a density `ρ` of the S3.1 class and every probability law `f` on configurations:
`H(f|Q_{N,β}(μ)) < ∞ ↔ 𝖬𝖥𝖤_N(f,μ) < ∞`, and then
`H(f|Q) = H(f|μ^{⊗N}) + βN ∫ F_N f + log K`. -/
theorem s66_split (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M L β : ℝ) (hβ : 0 < β)
    {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) (hM : ∀ x, ρ x ≤ M)
    (hL : s = 0 → HasLogMoment (wd ρ) L) {N : ℕ} (hN : 2 ≤ N)
    (f : Measure (EucConfig d N)) [IsProbabilityMeasure f] :
    (relEntropy f (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ)) ≠ ⊤ ↔
        MFEFiniteW d s f (wd ρ)) ∧
      (MFEFiniteW d s f (wd ρ) →
        (relEntropy f (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ))).toReal =
          (relEntropy f (Measure.pi fun _ : Fin N => wd ρ)).toReal +
            β * N * ∫ X, rieszModulatedEnergy d s X (wd ρ) ∂f +
            Real.log (Whole.gibbsNormalizer (rieszKernel d s) N β (wd ρ))) := by
  haveI : IsProbabilityMeasure (wd ρ) := HRS.MS.Thm.cb_withDensityReal_isProb hρ
  obtain ⟨C, hC⟩ := s66_gibbs_data hd hs0 hsd M L (β / 2) (2 * β) (by positivity) (by linarith)
  have hW := (hC ρ hρ hM hL N hN β ⟨by linarith, by linarith⟩).1
  have hGm := HRS.MS.Wr.wr9_rieszKernel_pair_meas (d := d) s
  have hFm : Measurable (fun X : EucConfig d N =>
      pairEnergy (fun x y => rieszKernel d s (x - y)) X (wd ρ)) :=
    HRS.MS.Wr.wr9_measurable_pairEnergy hGm
  have hQ := s66_modGibbs_tilted (N := N) (s := s) (b := β) hW
  obtain ⟨c, hc, C2, hent⟩ := HRS.MS.Wr.euclidean_pair_entropy_self_proof hd hs0 hsd M L (β / 2) (2 * β)
    (by positivity) (by linarith)
  have hent' := (hent ρ hρ hM hL N hN β ⟨by linarith, by linarith⟩).2
  have hfm : Measurable (fun X : EucConfig d N =>
      -β * N * pairEnergy (fun x y => rieszKernel d s (x - y)) X (wd ρ)) := measurable_const.mul hFm
  have hint_iff : ∀ ν : Measure (EucConfig d N), Integrable (fun X : EucConfig d N =>
      -β * N * pairEnergy (fun x y => rieszKernel d s (x - y)) X (wd ρ)) ν ↔
      Integrable (fun X => rieszModulatedEnergy d s X (wd ρ)) ν := by
    intro ν
    have hne : -β * (N : ℝ) ≠ 0 := by
      have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      have := mul_pos hβ this
      intro h; linarith
    exact integrable_const_mul_iff (isUnit_iff_ne_zero.2 hne) _
  unfold MFEFiniteW relEntropy
  rw [hQ]
  refine ⟨⟨fun h => ?_, fun ⟨h1, h2⟩ => ?_⟩, fun ⟨h1, h2⟩ => ?_⟩
  · -- finite entropy w.r.t. Q gives integrability of F
    have hQe : relEntropy f (Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ)) < ⊤ := by
      unfold relEntropy; rw [hQ]; exact lt_top_iff_ne_top.2 h
    obtain ⟨hi, -⟩ := hent' f inferInstance hQe
    have hi' : Integrable (fun X : EucConfig d N => rieszModulatedEnergy d s X (wd ρ)) f := by
      have hne : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      have h1 : Integrable (fun X : EucConfig d N =>
          |pairEnergy (fun x y => rieszKernel d s (x - y)) X (wd ρ)|) f :=
        (integrable_const_mul_iff (isUnit_iff_ne_zero.2 hne) _).1 hi
      exact (integrable_norm_iff hFm.aestronglyMeasurable).1 (by simpa [Real.norm_eq_abs] using h1)
    have hfi := (hint_iff f).2 hi'
    exact ⟨((s66_kl_tilted _ f hW.weight_integrable hfi).1).1 h, hi'⟩
  · exact ((s66_kl_tilted _ f hW.weight_integrable ((hint_iff f).2 h2)).1).2 h1
  · have hfi := (hint_iff f).2 h2
    rw [(s66_kl_tilted _ f hW.weight_integrable hfi).2 h1, integral_const_mul]
    have hK : Whole.gibbsNormalizer (rieszKernel d s) N β (wd ρ) = ∫ x, Real.exp (-β * N *
        pairEnergy (fun x y => rieszKernel d s (x - y)) x (wd ρ)) ∂(Measure.pi fun _ : Fin N => wd ρ) := rfl
    rw [hK]
    have : ∫ X, rieszModulatedEnergy d s X (wd ρ) ∂f =
        ∫ X, pairEnergy (fun x y => rieszKernel d s (x - y)) X (wd ρ) ∂f := rfl
    rw [this]
    ring

end HRS.MS.MovEnt

end
