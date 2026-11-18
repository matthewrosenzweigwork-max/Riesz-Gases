import HRS.MS.SuppU11
import HRS.MS.CovMeasAux1
import HRS.MS.S81pAssemble

/-!
# S8.1 (worker S81P): the return map as a bounded linear map `ℓ² → 𝒳_T`

Namespace `HRS.Whole.S81P`, prefix `s81p_`.

`s81p_return_clm`: for the spectral data of S8.7 (`IsSpectralData`, `L⁴` gradient bound) the return map `z ↦ (t ↦ returnMapW … z t)` of S8.8
(`return_map_bounded`, proved in `SuppU11`) is the evaluation of a genuine continuous linear map `SeqL2 →L[ℝ] OscPath d m T` (Pro R01).
The old and initial Gaussian blocks of the burn-in coupling are images of Gaussian `ℓ²` vectors under this map; `s81p_L2_clm` transfers
an `L²` cost through it (Pro R06).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.SuppU11

namespace HRS.Whole.S81P

variable {d : ℕ}

theorem s81p_return_clm (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (ρβ : Euc d → ℝ)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ)
    (hdata : IsSpectralData d β ρβ e om) (t₀ : ℝ) (ht₀ : 0 < t₀) (C4 : ℝ)
    (hL4 : ∀ l, eLpNorm (fun x => ‖gradient (e l) x‖) 4 (withDensityReal ρβ) ≤
      ENNReal.ofReal (C4 * Real.exp (t₀ * om l)))
    (τ : ℝ) (hτ : 4 * t₀ < τ) (b : ℝ) (hb : τ / 2 + 1 < b) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (T : ℝ) (hT : 0 < T) :
    ∃ R : SeqL2 →L[ℝ] OscPath d m T, ∀ (z : SeqL2) (t : Set.Icc (0 : ℝ) T),
      OscPath.at' (R z) t = returnMapW d β ρβ e om m τ b z t := by
  classical
  obtain ⟨C, hC⟩ := return_map_bounded_proof hd a β ha hβ ρβ hρ e om hdata t₀ ht₀ C4 hL4 τ hτ b hb m
    hm T hT
  set coef : MultiIndex d → ℕ → ℝ := fun α l =>
    β * l2Inner (withDensityReal ρβ) (projMean (withDensityReal ρβ) (oscTestFun m α))
      (responseInverse (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρβ) β (e l)) with hcoef
  have hmem : ∀ (z : SeqL2) (t : ℝ), t ∈ Icc (0 : ℝ) T →
      (∀ α, Summable fun l => coef α l * Real.exp (-(b + t - τ / 2) * om l) * SeqL2.coord z l) ∧
      Memℓp (fun α => ∑' l, coef α l * Real.exp (-(b + t - τ / 2) * om l) * SeqL2.coord z l) 2 :=
    fun z t ht => (hC z).1 t ht
  have hcont : ∀ z : SeqL2, Continuous fun t : Icc (0 : ℝ) T => returnMapW d β ρβ e om m τ b z t :=
    fun z => continuousOn_iff_continuous_restrict.1 (hC z).2.1
  let Rf : SeqL2 →ₗ[ℝ] OscPath d m T :=
    { toFun := fun z => (⟨fun t : Icc (0 : ℝ) T => returnMapW d β ρβ e om m τ b z t, hcont z⟩ :
        C(Icc (0 : ℝ) T, OscDual d m))
      map_add' := fun z z' => by
        refine ContinuousMap.ext fun t => ?_
        obtain ⟨hs, hl⟩ := hmem z t t.2
        obtain ⟨hs', hl'⟩ := hmem z' t t.2
        show returnMapW d β ρβ e om m τ b (z + z') t = returnMapW d β ρβ e om m τ b z t +
          returnMapW d β ρβ e om m τ b z' t
        unfold returnMapW
        rw [← HRS.MS.CovMeas.s101_ellVec_add hl hl']
        congr 1
        funext α
        rw [← (hs α).tsum_add (hs' α)]
        refine tsum_congr fun l => ?_
        have hc : SeqL2.coord (z + z') l = SeqL2.coord z l + SeqL2.coord z' l := rfl
        rw [hc]
        ring
      map_smul' := fun r z => by
        refine ContinuousMap.ext fun t => ?_
        obtain ⟨hs, hl⟩ := hmem z t t.2
        show returnMapW d β ρβ e om m τ b (r • z) t = r • returnMapW d β ρβ e om m τ b z t
        unfold returnMapW
        rw [← HRS.MS.CovMeas.s101_ellVec_smul r hl]
        congr 1
        funext α
        rw [← tsum_mul_left]
        refine tsum_congr fun l => ?_
        have hc : SeqL2.coord (r • z) l = r * SeqL2.coord z l := rfl
        rw [hc]
        ring }
  refine ⟨LinearMap.mkContinuous Rf (max C 0) fun z => ?_, fun z t => rfl⟩
  show ‖(⟨fun t : Icc (0 : ℝ) T => returnMapW d β ρβ e om m τ b z t, hcont z⟩ :
    C(Icc (0 : ℝ) T, OscDual d m))‖ ≤ max C 0 * ‖z‖
  refine (ContinuousMap.norm_le _ (mul_nonneg (le_max_right C 0) (norm_nonneg z))).2 fun t => ?_
  exact ((hC z).2.2 t t.2).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg z))

/-- `L²` cost through a bounded linear map (Pro R06). -/
theorem s81p_L2_clm {Ω E F : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (P : Measure Ω) (L : E →L[ℝ] F) (A B : Ω → E) :
    s81p_L2 P (fun z => L (A z) - L (B z)) ≤ ENNReal.ofReal ‖L‖ * s81p_L2 P (fun z => A z - B z) := by
  rw [s81p_L2_eq, s81p_L2_eq]
  have h : ∀ z, ‖L (A z) - L (B z)‖ₑ ≤ ENNReal.ofReal ‖L‖ * ‖A z - B z‖ₑ := by
    intro z
    rw [← map_sub]
    calc ‖L (A z - B z)‖ₑ ≤ ‖L‖ₑ * ‖A z - B z‖ₑ := L.le_opENorm _
      _ = ENNReal.ofReal ‖L‖ * ‖A z - B z‖ₑ := by rw [ofReal_norm]
  calc (∫⁻ z, ‖L (A z) - L (B z)‖ₑ ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))
      ≤ (∫⁻ z, (ENNReal.ofReal ‖L‖ * ‖A z - B z‖ₑ) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow (lintegral_mono fun z => ENNReal.rpow_le_rpow (h z) (by norm_num))
          (by norm_num)
    _ = ENNReal.ofReal ‖L‖ * (∫⁻ z, ‖A z - B z‖ₑ ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
        rw [lintegral_const_mul' _ _ (by simp), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ← ENNReal.rpow_mul]
        norm_num

end HRS.Whole.S81P
