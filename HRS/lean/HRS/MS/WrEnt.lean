import HRS.MS.WrEntAux2

/-!
# HRS.MS.WrEnt -- the pair-entropy consequences of Proposition S3.1 (WR-9)

Packet WR-9 of `docs/SUPP_FOUND_PACKETS.md` (Track D), namespace `HRS.MS.Wr`.

* `wr9_shape_final`: for a law `Q` with `∫ e^{±cNF^H} dQ ≤ e^{2C₀ N δ}` the two displays of
  `euclidean_pair_entropy` in the exact shape of the frozen statement (via `wr9_moments`).
* `wr9_pair_inst`: the tilt identity `E_Q[e^{±cNF^h}] = K^{g ∓ (c/b)h}/K^g` and the two-sided pressure
  bounds give `∫ e^{±cNF^h} dQ ≤ e^{2C₀ N δ}`.
* `wr9_self_inst`: for `h = g` the tilt is `K_{b ∓ c}/K_b`, with `b ∓ c` in an enlarged `β` interval.
* `euclidean_pair_entropy_proof : type_of% @HRS.Whole.euclidean_pair_entropy`: `c = b₋θ₀`, with `θ₀, C₀` of
  `euclidean_pressure_proof`.
* `euclidean_pair_entropy_self_proof : type_of% @HRS.Whole.euclidean_pair_entropy_self`: the pressure bound
  at `θ = 0` with the kernel `h = 0` (`B = 0`) and the enlarged interval `[b₋/2, b₊ + b₋/2]`, `c = b₋/2`.

Statement adjustments: none.  Helper lemmas carry the prefix `wr9_`.  Ties in `HRS/MS/WrEntTie.lean`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

open HRS.Whole

variable {d N : ℕ}

/-! ### Shape of the conclusion -/

theorem wr9_shape_final {μ : Measure (Euc d)} [SFinite μ] (Q : Measure (EucConfig d N))
    [IsProbabilityMeasure Q] (H : Euc d → Euc d → ℝ) (hHm : Measurable (Function.uncurry H))
    {c C0 δ C : ℝ} (hc : 0 < c) (hC0 : 0 ≤ C0) (hT : 1 ≤ (N : ℝ) * δ)
    (hC : (2 * C0 + 1) * (1 + c⁻¹) ≤ C)
    (hp : ∫⁻ X, ENNReal.ofReal (Real.exp (c * ((N : ℝ) * pairEnergy H X μ))) ∂Q ≤
      ENNReal.ofReal (Real.exp (2 * C0 * ((N : ℝ) * δ))))
    (hm : ∫⁻ X, ENNReal.ofReal (Real.exp (-(c * ((N : ℝ) * pairEnergy H X μ)))) ∂Q ≤
      ENNReal.ofReal (Real.exp (2 * C0 * ((N : ℝ) * δ)))) :
    (Integrable (fun X : EucConfig d N => Real.exp (c * N * |pairEnergy H X μ|)) Q ∧
        Real.log (∫ X : EucConfig d N, Real.exp (c * N * |pairEnergy H X μ|) ∂Q) ≤ C * N * δ) ∧
      ∀ f : Measure (EucConfig d N), IsProbabilityMeasure f → relEntropy f Q < ⊤ →
        Integrable (fun X : EucConfig d N => N * |pairEnergy H X μ|) f ∧
          ∫ X, N * |pairEnergy H X μ| ∂f ≤ C * ((relEntropy f Q).toReal + N * δ) := by
  have hΨ : Measurable (fun X : EucConfig d N => (N : ℝ) * pairEnergy H X μ) :=
    measurable_const.mul (wr9_measurable_pairEnergy hHm)
  obtain ⟨⟨hi, hl⟩, hent⟩ := wr9_moments Q hΨ hc hC0 hT hp hm
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hshape : ∀ X : EucConfig d N, c * N * |pairEnergy H X μ| =
      c * |(N : ℝ) * pairEnergy H X μ| := by
    intro X; rw [abs_mul, abs_of_nonneg hN0]; ring
  have e1 : (fun X : EucConfig d N => Real.exp (c * N * |pairEnergy H X μ|)) =
      fun X => Real.exp (c * |(N : ℝ) * pairEnergy H X μ|) := funext fun X => by rw [hshape]
  have e2 : (fun X : EucConfig d N => (N : ℝ) * |pairEnergy H X μ|) =
      fun X => |(N : ℝ) * pairEnergy H X μ| := funext fun X => by rw [abs_mul, abs_of_nonneg hN0]
  have hTnn : 0 ≤ (N : ℝ) * δ := by linarith
  have hA : 0 ≤ 2 * C0 + 1 := by linarith
  have hcinv : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
  have hCa : 2 * C0 + 1 ≤ C := by
    refine le_trans ?_ hC
    nlinarith
  have hCb : c⁻¹ * (2 * C0 + 1) ≤ C := by
    refine le_trans ?_ hC
    nlinarith
  refine ⟨⟨?_, ?_⟩, fun f hf hKL => ?_⟩
  · rw [e1]; exact hi
  · rw [e1]
    refine hl.trans ?_
    calc (2 * C0 + 1) * ((N : ℝ) * δ) ≤ C * ((N : ℝ) * δ) := mul_le_mul_of_nonneg_right hCa hTnn
      _ = C * N * δ := by ring
  · rw [e2]
    obtain ⟨hi2, hb2⟩ := hent f hf hKL.ne
    refine ⟨hi2, hb2.trans ?_⟩
    have hH : 0 ≤ (relEntropy f Q).toReal + (N : ℝ) * δ := by
      have := ENNReal.toReal_nonneg (a := relEntropy f Q); linarith
    exact mul_le_mul_of_nonneg_right hCb hH

/-! ### The tilted exponential moments -/

theorem wr9_nonneg_of_abs_le {C0 T : ℝ} {x : ℝ} (h : |x| ≤ C0 * T) (hT : 1 ≤ T) : 0 ≤ C0 := by
  by_contra hneg
  push Not at hneg
  have h1 : 0 ≤ C0 * T := (abs_nonneg _).trans h
  nlinarith

/-- `E_Q[e^{±cNF^h}] = K^{g ∓ (c/b)h}/K^g ≤ e^{2 C₀ T}` for `Q = Q^g_{N,b}`. -/
theorem wr9_pair_inst {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {G H : Euc d → Euc d → ℝ}
    (hGm : Measurable (Function.uncurry G)) (hHm : Measurable (Function.uncurry H)) {b c C0 T : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hGW : GibbsWellDefined G N b μ)
    (h0 : |Real.log (pairNormalizer G N b μ)| ≤ C0 * T)
    (hGp : GibbsWellDefined (fun x y => G x y - (c / b) * H x y) N b μ)
    (hp : |Real.log (pairNormalizer (fun x y => G x y - (c / b) * H x y) N b μ)| ≤ C0 * T)
    (hGn : GibbsWellDefined (fun x y => G x y - (-(c / b)) * H x y) N b μ)
    (hn : |Real.log (pairNormalizer (fun x y => G x y - (-(c / b)) * H x y) N b μ)| ≤ C0 * T) :
    ∫⁻ X, ENNReal.ofReal (Real.exp (c * ((N : ℝ) * pairEnergy H X μ))) ∂(pairGibbs G N b μ) ≤
        ENNReal.ofReal (Real.exp (2 * C0 * T)) ∧
      ∫⁻ X, ENNReal.ofReal (Real.exp (-(c * ((N : ℝ) * pairEnergy H X μ)))) ∂(pairGibbs G N b μ) ≤
        ENNReal.ofReal (Real.exp (2 * C0 * T)) := by
  have hGok : Wr8Ok μ G := wr9_ok_of_gwd hGm hGW
  have hHok : Wr8Ok μ H := wr9_ok_of_sub hGok hHm (div_ne_zero hc.ne' hb.ne') hGp
  have hHm' : Measurable (fun X : EucConfig d N => pairEnergy H X μ) := wr9_measurable_pairEnergy hHm
  have hbc : b * (c / b) = c := by field_simp
  have e2 : 2 * (C0 * T) = 2 * C0 * T := by ring
  constructor
  · have e : ∫⁻ X : EucConfig d N, ENNReal.ofReal (Real.exp (c * ((N : ℝ) * pairEnergy H X μ)))
        ∂(pairGibbs G N b μ) = (ENNReal.ofReal (pairNormalizer G N b μ))⁻¹ *
        ∫⁻ X : EucConfig d N, ENNReal.ofReal (Real.exp (-b * N *
          pairEnergy (fun x y => G x y - (c / b) * H x y) X μ)) ∂(Measure.pi fun _ : Fin N => μ) := by
      refine wr9_tilt hGm (Ψ := fun X => c * ((N : ℝ) * pairEnergy H X μ))
        (W2 := fun X => -b * N * pairEnergy (fun x y => G x y - (c / b) * H x y) X μ)
        (measurable_const.mul (measurable_const.mul hHm')) (fun X => ?_)
      rw [wr9_pairEnergy_sub hGok hHok]
      linear_combination (-(1 : ℝ)) * (N : ℝ) * (pairEnergy H X μ) * hbc
    rw [e, wr9_partition hGp]
    refine (wr9_ratio_bound hGW.normalizer_pos hGp.normalizer_pos h0 hp).trans (le_of_eq ?_)
    rw [e2]
  · have e : ∫⁻ X : EucConfig d N, ENNReal.ofReal (Real.exp (-(c * ((N : ℝ) * pairEnergy H X μ))))
        ∂(pairGibbs G N b μ) = (ENNReal.ofReal (pairNormalizer G N b μ))⁻¹ *
        ∫⁻ X : EucConfig d N, ENNReal.ofReal (Real.exp (-b * N *
          pairEnergy (fun x y => G x y - (-(c / b)) * H x y) X μ)) ∂(Measure.pi fun _ : Fin N => μ) := by
      refine wr9_tilt hGm (Ψ := fun X => -(c * ((N : ℝ) * pairEnergy H X μ)))
        (W2 := fun X => -b * N * pairEnergy (fun x y => G x y - (-(c / b)) * H x y) X μ)
        (measurable_const.mul (measurable_const.mul hHm')).neg (fun X => ?_)
      rw [wr9_pairEnergy_sub hGok hHok]
      linear_combination ((1 : ℝ)) * (N : ℝ) * (pairEnergy H X μ) * hbc
    rw [e, wr9_partition hGn]
    refine (wr9_ratio_bound hGW.normalizer_pos hGn.normalizer_pos h0 hn).trans (le_of_eq ?_)
    rw [e2]

/-- `h = g`: `E_Q[e^{±cNF^g}] = K_{b ∓ c}/K_b ≤ e^{2 C₀ T}`. -/
theorem wr9_self_inst {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {G : Euc d → Euc d → ℝ}
    (hGm : Measurable (Function.uncurry G)) {b c C0 T : ℝ} (hGW : GibbsWellDefined G N b μ)
    (h0 : |Real.log (pairNormalizer G N b μ)| ≤ C0 * T)
    (hGp : GibbsWellDefined G N (b - c) μ) (hp : |Real.log (pairNormalizer G N (b - c) μ)| ≤ C0 * T)
    (hGn : GibbsWellDefined G N (b + c) μ) (hn : |Real.log (pairNormalizer G N (b + c) μ)| ≤ C0 * T) :
    ∫⁻ X, ENNReal.ofReal (Real.exp (c * ((N : ℝ) * pairEnergy G X μ))) ∂(pairGibbs G N b μ) ≤
        ENNReal.ofReal (Real.exp (2 * C0 * T)) ∧
      ∫⁻ X, ENNReal.ofReal (Real.exp (-(c * ((N : ℝ) * pairEnergy G X μ)))) ∂(pairGibbs G N b μ) ≤
        ENNReal.ofReal (Real.exp (2 * C0 * T)) := by
  have hGm' : Measurable (fun X : EucConfig d N => pairEnergy G X μ) := wr9_measurable_pairEnergy hGm
  have e2 : 2 * (C0 * T) = 2 * C0 * T := by ring
  constructor
  · have e : ∫⁻ X : EucConfig d N, ENNReal.ofReal (Real.exp (c * ((N : ℝ) * pairEnergy G X μ)))
        ∂(pairGibbs G N b μ) = (ENNReal.ofReal (pairNormalizer G N b μ))⁻¹ *
        ∫⁻ X : EucConfig d N, ENNReal.ofReal (Real.exp (-(b - c) * N * pairEnergy G X μ))
          ∂(Measure.pi fun _ : Fin N => μ) := by
      refine wr9_tilt hGm (Ψ := fun X => c * ((N : ℝ) * pairEnergy G X μ))
        (W2 := fun X => -(b - c) * N * pairEnergy G X μ)
        (measurable_const.mul (measurable_const.mul hGm')) (fun X => ?_)
      ring
    rw [e, wr9_partition hGp]
    refine (wr9_ratio_bound hGW.normalizer_pos hGp.normalizer_pos h0 hp).trans (le_of_eq ?_)
    rw [e2]
  · have e : ∫⁻ X : EucConfig d N, ENNReal.ofReal (Real.exp (-(c * ((N : ℝ) * pairEnergy G X μ))))
        ∂(pairGibbs G N b μ) = (ENNReal.ofReal (pairNormalizer G N b μ))⁻¹ *
        ∫⁻ X : EucConfig d N, ENNReal.ofReal (Real.exp (-(b + c) * N * pairEnergy G X μ))
          ∂(Measure.pi fun _ : Fin N => μ) := by
      refine wr9_tilt hGm (Ψ := fun X => -(c * ((N : ℝ) * pairEnergy G X μ)))
        (W2 := fun X => -(b + c) * N * pairEnergy G X μ)
        (measurable_const.mul (measurable_const.mul hGm')).neg (fun X => ?_)
      ring
    rw [e, wr9_partition hGn]
    refine (wr9_ratio_bound hGW.normalizer_pos hGn.normalizer_pos h0 hn).trans (le_of_eq ?_)
    rw [e2]

/-! ### The two statements -/

/-- **Proposition S3.1, pair-entropy consequences** (`HRS.Whole.euclidean_pair_entropy`): `c = b₋ θ₀`,
`E_Q[e^{±cNF^h}] = K^{g ∓ (c/b)h}/K^g ≤ e^{2 C₀ N δ_N}`, `e^{|x|} ≤ e^x + e^{-x}` and the
Donsker--Varadhan inequality. -/
theorem euclidean_pair_entropy_proof : type_of% @HRS.Whole.euclidean_pair_entropy := by
  intro d s hd hs0 hsd M L bm bp B hbm hb
  obtain ⟨θ0, hθ0, C0, hP⟩ := euclidean_pressure_proof hd hs0 hsd M L bm bp B hbm hb
  have hc : 0 < bm * θ0 := mul_pos hbm hθ0
  refine ⟨bm * θ0, hc, (2 * max C0 0 + 1) * (1 + (bm * θ0)⁻¹), ?_⟩
  intro ρ hρ hρM hlog h hh N hN b hb'
  have hμprob : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := Q34.isProbabilityMeasure_nu hρ
  have hb0 : 0 < b := hbm.trans_le hb'.1
  have hθ : |bm * θ0 / b| ≤ θ0 := by
    rw [abs_of_pos (div_pos hc hb0), div_le_iff₀ hb0]
    nlinarith [hb'.1]
  have hT : 1 ≤ (N : ℝ) * deltaN d s N := wr8_one_le_mul_deltaN hs0 N (by omega)
  obtain ⟨hW0, hb0'⟩ := hP ρ hρ hρM hlog h hh N hN b hb' 0 (by rw [abs_zero]; exact hθ0.le)
  obtain ⟨hWp, hbp⟩ := hP ρ hρ hρM hlog h hh N hN b hb' (bm * θ0 / b) hθ
  obtain ⟨hWn, hbn⟩ := hP ρ hρ hρM hlog h hh N hN b hb' (-(bm * θ0 / b)) (by rwa [abs_neg])
  simp only [zero_mul, sub_zero] at hW0 hb0'
  have hb0'' : |Real.log (pairNormalizer (fun x y => rieszKernel d s (x - y)) N b (HRS.Whole.withDensityReal ρ))| ≤
      C0 * ((N : ℝ) * deltaN d s N) := by simpa only [mul_assoc] using hb0'
  have hbp' : |Real.log (pairNormalizer (fun x y => rieszKernel d s (x - y) - (bm * θ0 / b) * h x y) N b
      (HRS.Whole.withDensityReal ρ))| ≤ C0 * ((N : ℝ) * deltaN d s N) := by simpa only [mul_assoc] using hbp
  have hbn' : |Real.log (pairNormalizer (fun x y => rieszKernel d s (x - y) - (-(bm * θ0 / b)) * h x y) N b
      (HRS.Whole.withDensityReal ρ))| ≤ C0 * ((N : ℝ) * deltaN d s N) := by simpa only [mul_assoc] using hbn
  have hC0 : 0 ≤ C0 := wr9_nonneg_of_abs_le hb0'' hT
  obtain ⟨hpl, hmi⟩ := wr9_pair_inst (G := fun x y => rieszKernel d s (x - y)) (H := h)
    (wr9_rieszKernel_pair_meas s) hh.measurable hb0 hc hW0 hb0'' hWp hbp' hWn hbn'
  have := wr9_gibbs_prob hW0
  have key := wr9_shape_final (μ := HRS.Whole.withDensityReal ρ)
    (pairGibbs (fun x y => rieszKernel d s (x - y)) N b (HRS.Whole.withDensityReal ρ)) h hh.measurable hc hC0 hT
    (C := (2 * max C0 0 + 1) * (1 + (bm * θ0)⁻¹))
    (le_of_eq (by rw [max_eq_left hC0])) hpl hmi
  have hQ : HRS.Whole.modulatedGibbs (rieszKernel d s) N b (HRS.Whole.withDensityReal ρ) =
      pairGibbs (fun x y => rieszKernel d s (x - y)) N b (HRS.Whole.withDensityReal ρ) := rfl
  rw [hQ]
  exact key

/-- **Proposition S3.1, last sentence** (`HRS.Whole.euclidean_pair_entropy_self`): `h = g`; the tilt is
`K_{b ∓ c}/K_b` and the pressure bound is applied at `θ = 0`, `h = 0` on the enlarged interval
`[b₋/2, b₊ + b₋/2]` with `c = b₋/2`. -/
theorem euclidean_pair_entropy_self_proof : type_of% @HRS.Whole.euclidean_pair_entropy_self := by
  intro d s hd hs0 hsd M L bm bp hbm hb
  have hbm2 : 0 < bm / 2 := by positivity
  have hb2 : bm / 2 < bp + bm / 2 := by linarith
  obtain ⟨θ0, hθ0, C0, hP⟩ := euclidean_pressure_proof hd hs0 hsd M L (bm / 2) (bp + bm / 2) 0 hbm2 hb2
  refine ⟨bm / 2, hbm2, (2 * max C0 0 + 1) * (1 + (bm / 2)⁻¹), ?_⟩
  intro ρ hρ hρM hlog N hN b hb'
  have hμprob : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := Q34.isProbabilityMeasure_nu hρ
  have hT : 1 ≤ (N : ℝ) * deltaN d s N := wr8_one_le_mul_deltaN hs0 N (by omega)
  have hhz : IsBoundedPairKernel s 0 (fun _ _ : Euc d => (0 : ℝ)) :=
    ⟨measurable_const, fun _ _ => rfl, fun x y _ => by simp⟩
  have key : ∀ b' ∈ Set.Icc (bm / 2) (bp + bm / 2),
      GibbsWellDefined (fun x y => rieszKernel d s (x - y)) N b' (HRS.Whole.withDensityReal ρ) ∧
      |Real.log (pairNormalizer (fun x y => rieszKernel d s (x - y)) N b' (HRS.Whole.withDensityReal ρ))| ≤
        C0 * ((N : ℝ) * deltaN d s N) := by
    intro b' hb''
    obtain ⟨hW, hbd⟩ := hP ρ hρ hρM hlog (fun _ _ => 0) hhz N hN b' hb'' 0
      (by rw [abs_zero]; exact hθ0.le)
    simp only [zero_mul, sub_zero] at hW hbd
    exact ⟨hW, by simpa only [mul_assoc] using hbd⟩
  have hbmem : b ∈ Set.Icc (bm / 2) (bp + bm / 2) := ⟨by linarith [hb'.1], by linarith [hb'.2]⟩
  have hmmem : b - bm / 2 ∈ Set.Icc (bm / 2) (bp + bm / 2) := ⟨by linarith [hb'.1], by linarith [hb'.2]⟩
  have hpmem : b + bm / 2 ∈ Set.Icc (bm / 2) (bp + bm / 2) := ⟨by linarith [hb'.1], by linarith [hb'.2]⟩
  obtain ⟨hW0, hb0''⟩ := key b hbmem
  obtain ⟨hWm, hbm''⟩ := key _ hmmem
  obtain ⟨hWp, hbp''⟩ := key _ hpmem
  have hC0 : 0 ≤ C0 := wr9_nonneg_of_abs_le hb0'' hT
  obtain ⟨hpl, hmi⟩ := wr9_self_inst (G := fun x y => rieszKernel d s (x - y))
    (wr9_rieszKernel_pair_meas s) hW0 hb0'' hWm hbm'' hWp hbp''
  have := wr9_gibbs_prob hW0
  have key2 := wr9_shape_final (μ := HRS.Whole.withDensityReal ρ)
    (pairGibbs (fun x y => rieszKernel d s (x - y)) N b (HRS.Whole.withDensityReal ρ))
    (fun x y => rieszKernel d s (x - y)) (wr9_rieszKernel_pair_meas s) hbm2 hC0 hT
    (C := (2 * max C0 0 + 1) * (1 + (bm / 2)⁻¹))
    (le_of_eq (by rw [max_eq_left hC0])) hpl hmi
  have hQ : HRS.Whole.modulatedGibbs (rieszKernel d s) N b (HRS.Whole.withDensityReal ρ) =
      pairGibbs (fun x y => rieszKernel d s (x - y)) N b (HRS.Whole.withDensityReal ρ) := rfl
  rw [hQ]
  exact key2

end HRS.MS.Wr
