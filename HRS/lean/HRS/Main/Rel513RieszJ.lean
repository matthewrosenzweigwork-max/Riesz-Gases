import HRS.Main.Rel513RieszI

/-!
# HRS.Main.Rel513RieszJ -- packet rel513, part 10: `stationary_remainder_L2_proof`

Part (a) of the last sentence of Proposition 5.13.  `P_{N,β} = Q_{N,β}(μ_β)`
(`canonicalGibbs_eq_modulatedGibbs`); the remainder is `√N (μ_N(f) - m_N(f)) - √N (F^h - E F^h)`, whose two
pieces are bounded in `L²` by `rel513_linear_eLpNorm` and `rel513_quad_eLpNorm`, with
`B = C_env d cbNorm 2 φ` from `rel513_envelope` and `rel513_gradLip`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Main

variable {d : ℕ}

theorem stationary_remainder_L2_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (β : ℝ) (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρ : SmoothPosDensity ρβ) (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      eLpNorm (stationaryRemainder d s β V ρβ N φ) 2 (canonicalGibbs (periodicRiesz d s) V N β) ≤
        ENNReal.ofReal (C * Real.sqrt (deltaN d s N) * Torus.cbNorm 2 φ) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := HRS.PoleCavityAux.exists_density_bound hρ
  have hP : ∀ N : ℕ, canonicalGibbs (periodicRiesz d s) V N β =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρβ) := fun N =>
    canonicalGibbs_eq_modulatedGibbs (periodicRiesz d s) V β ρβ hρβ
      (fun x => periodicRiesz_neg x)
      (fun x => (CoercAux.J_bounds (by omega : 1 ≤ d) hs0 hsd one_pos hρ.density hΛ0.le hΛ x).1)
  obtain ⟨Klin, hKlin0, hKlin⟩ := rel513_linear_eLpNorm hd hs0 hsd hβ hρ
  obtain ⟨Kq, hKq0, hKq⟩ := rel513_quad_eLpNorm hd hs0 hsd hβ hρ
  obtain ⟨Cenv, hCenv0, hCenv⟩ := rel513_envelope (d := d) (s := s) hd hs0 hsd
  refine ⟨(Klin + Kq) * Cenv * d, by positivity, fun N hN φ hφ => ?_⟩
  have hN0 : 0 < N := by omega
  set μ := withDensityReal ρβ with hμdef
  haveI : SFinite μ := rel513_sfinite_mu ρβ
  set Q := modulatedGibbs (periodicRiesz d s) N β μ with hQdef
  haveI hQ : IsProbabilityMeasure Q := rel513_modulatedGibbs_isProb hd hs0 hsd hβ hρ hN0
  set m := firstMarginal Q with hmdef
  haveI : IsFiniteMeasure m := rel513_firstMarginal_finite Q
  set L : ℝ := Torus.cbNorm 2 φ * d with hLdef
  have hcb0 : 0 ≤ Torus.cbNorm 2 φ := rel513_cbNorm_nonneg 2 φ
  have hL0 : 0 ≤ L := by positivity
  set B : ℝ := Cenv * L with hBdef
  have hB0 : 0 ≤ B := by positivity
  set h := commKernel (periodicRieszGrad d s) (Torus.grad φ) with hhdef
  have hhm : Measurable (Function.uncurry h) :=
    rel513_measurable_comm hsd (rel513_grad_continuous hφ)
  have hsym : ∀ x y, h x y = h y x := fun x y => rel513_symm_comm hsd _ x y
  have hhh : ∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y) :=
    fun x y hxy => hCenv L (Torus.grad φ) hL0 (rel513_gradLip hφ) x y hxy
  have hlin := hKlin N hN B hB0 h hhm hhh
  have hquad := hKq N hN B hB0 h hhm hsym hhh
  have hfm : Measurable (fun y => Quad.Hc h μ y - Quad.Hc h m y) :=
    (Quad.measurable_Hc hhm μ).sub (Quad.measurable_Hc hhm m)
  have hfun : stationaryRemainder d s β V ρβ N φ = fun X : Config d N =>
      Real.sqrt N * ((∫ y, (Quad.Hc h μ y - Quad.Hc h m y) ∂(empirical X))
          - ∫ y, (Quad.Hc h μ y - Quad.Hc h m y) ∂m)
      - Real.sqrt N * (modulatedEnergy h X m - ∫ X', modulatedEnergy h X' m ∂Q) := by
    funext X
    simp only [stationaryRemainder, hP N]
    rfl
  rw [hfun, hP N]
  have hmin := eLpNorm_sub_le (p := 2) (μ := Q)
    (f := fun X : Config d N => Real.sqrt N * ((∫ y, (Quad.Hc h μ y - Quad.Hc h m y) ∂(empirical X))
          - ∫ y, (Quad.Hc h μ y - Quad.Hc h m y) ∂m))
    (g := fun X : Config d N => Real.sqrt N * (modulatedEnergy h X m - ∫ X', modulatedEnergy h X' m ∂Q))
    (by norm_num)
  refine le_trans hmin ?_
  have hδ0 : 0 ≤ deltaN d s N := (Quad.deltaN_pos hd hs0 hsd (by omega : 1 ≤ N)).le
  have hδ1 : deltaN d s N ≤ 1 := MarginalAux.deltaN_le_one hs0 hsd (by omega) N (by omega)
  have hsq0 := Real.sqrt_nonneg (deltaN d s N)
  have hsq1 : Real.sqrt (deltaN d s N) ≤ 1 := Real.sqrt_le_one.2 hδ1  
  have hle : deltaN d s N ≤ Real.sqrt (deltaN d s N) := by
    nlinarith [Real.sq_sqrt hδ0]
  calc eLpNorm (fun X : Config d N => Real.sqrt N * ((∫ y, (Quad.Hc h μ y - Quad.Hc h m y) ∂(empirical X))
          - ∫ y, (Quad.Hc h μ y - Quad.Hc h m y) ∂m)) 2 Q +
        eLpNorm (fun X : Config d N => Real.sqrt N * (modulatedEnergy h X m - ∫ X', modulatedEnergy h X' m ∂Q)) 2 Q
      ≤ ENNReal.ofReal (Klin * B * deltaN d s N) + ENNReal.ofReal (Kq * B * Real.sqrt (deltaN d s N)) :=
        add_le_add hlin hquad
    _ ≤ ENNReal.ofReal (Klin * B * Real.sqrt (deltaN d s N)) +
          ENNReal.ofReal (Kq * B * Real.sqrt (deltaN d s N)) := by
        gcongr
    _ = ENNReal.ofReal ((Klin + Kq) * B * Real.sqrt (deltaN d s N)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
    _ = _ := by
        congr 1
        simp only [hBdef, hLdef]
        ring

example := (@stationary_remainder_L2_proof : type_of% @stationary_remainder_L2)

end HRS.Main

end
