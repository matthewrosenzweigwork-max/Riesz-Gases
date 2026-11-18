import HRS.MS.R2ChaosAux64

/-!
# HRS.MS.R2ChaosTie2 -- S9.6 `round2_polynomial_integrated`

Packet S94.  The frozen statement `HRS.Whole.round2_polynomial_integrated` (Corollary 9.6) is proved from the already proved
Proposition 9.4 (`round2_integrated_chaos_proof`) applied to the bounded truncations `h^j = h 1_{max(|x|,|y|) ≤ j}`, the
polynomial moment bounds of Proposition 9.5, and the limit procedure `s94_limit_F`, `s94_part_i_poly`, `s94_part_ii_poly`,
`s94_part_iii_poly` (files `R2ChaosAux52 .. R2ChaosAux64`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole HRS.MS.R2Poly

theorem round2_polynomial_integrated_proof : type_of% @HRS.Whole.round2_polynomial_integrated := by
  intro d hd s hs0 hs M L C₀ c₀ b p K B Pw T hb hp hPw hT ρ hρ hG Ω _ P _ X Ω' _ P' _ ξ hset h hmeas hker
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  have hB : 0 ≤ B := s94_polyB_nonneg hd (hker 0 ⟨le_rfl, hT.le⟩)
  have hmeasj : ∀ j : ℕ, Measurable fun q : ℝ × Euc d × Euc d => (fun t x y => s95_part (h t) j x y) q.1 q.2.1 q.2.2 :=
    fun j => s94_trunc_family_meas hmeas j
  have hkerj : ∀ j : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      IsBoundedPairKernel s (B * 2 ^ Pw * (1 + (j : ℝ)) ^ Pw) ((fun t x y => s95_part (h t) j x y) t) :=
    fun j t ht => s94_trunc_bdd hd hPw (hker t ht) j
  choose Fj hFjm hFj2 hFjW hFjC using fun j : ℕ =>
    @round2_integrated_chaos_proof d hd s hs0 hs M L b p K (B * 2 ^ Pw * (1 + (j : ℝ)) ^ Pw) T hb hp hT ρ hρ
      Ω _ P _ X Ω' _ P' _ ξ hset (fun t x y => s95_part (h t) j x y) (hmeasj j) (hkerj j)
  have hkok : ∀ j : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T, S94KOK (Whole.withDensityReal ρ) (s95_part (h t) j) :=
    fun j t ht => s94_kok_poly hd hs0 hs hρ hG hPw hB (s94_trunc_poly (hker t ht) j)
  have hk0ok : ∀ t ∈ Set.Icc (0 : ℝ) T, S94KOK (Whole.withDensityReal ρ) (h t) :=
    fun t ht => s94_kok_poly hd hs0 hs hρ hG hPw hB (hker t ht)
  have hconv : ∀ t ∈ Set.Icc (0 : ℝ) T, Tendsto (fun j : ℕ => eLpNorm
      (fun q : Euc d × Euc d => s95_part (h t) j q.1 q.2 - h t q.1 q.2) 2
      ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ))) atTop (𝓝 0) := by
    intro t ht
    have := s94_trunc_lq hd hs0 hs hρ hG hPw (hker t ht) (q := 2) (by norm_num) (by linarith)
    have e2 : ENNReal.ofReal 2 = 2 := by norm_num
    rwa [e2] at this
  have hκ : ∃ κ : ℝ, ∀ j : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T, eLpNorm (fun q : Euc d × Euc d => s95_part (h t) j q.1 q.2) 2
      ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ)) ≤ ENNReal.ofReal κ := by
    obtain ⟨κ, -, hκ⟩ := s94_poly_L2_bound hd hs0 hs hρ hG hPw hB
    exact ⟨κ, fun j t ht => hκ (s94_trunc_poly (hker t ht) j)⟩
  obtain ⟨F, hFm, hF2, hWick, η, hη0, hη, hFη⟩ :=
    s94_limit_F hd hρ hset hT (kk := fun j t => s95_part (h t) j) (k0 := h) hkok hk0ok hconv hκ
      (Φ := Fj) hFjm hFjW
  refine ⟨F, hFm, hF2, hWick, ?_⟩
  intro k aa haa
  have hi := s94_part_i_poly hd hs0 hs hb hp hρ hG hPw hset hT hmeas hker hFjm hFj2
    (fun j k aa haa => (hFjC j k aa haa).1) hFm hF2 hη0 hη hFη haa
  refine ⟨hi, ?_, s94_part_iii_poly hd hs0 hs hb hp hρ hG hPw hset hT hB hmeas hker hF2 haa hi⟩
  exact s94_part_ii_poly hT hF2 (fun N hN => s94_pquad_ae_memLp hd hs0 hs hb hp hρ hG hPw hset hB hmeas hker hN)
    (fun N => s94_measurable_r2L2Path T _ (s94_quad_measurable (N := N) hmeas (X N) (hset.measX N)))
    (fun N => s94_measurable_r2IntPath T hT.le _ (s94_quad_measurable (N := N) hmeas (X N) (hset.measX N)))
    (fun N => (hset.conv k aa haa).forall_aemeasurable N) hi

end HRS.MS.R2Chaos
