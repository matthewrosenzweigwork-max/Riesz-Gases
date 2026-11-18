import HRS.MS.R2InterpAux123

/-!
# S10.2 (worker S10S), part 124 (packet M1e): the quadratic field at a fixed time is an admissible functional with an explicit envelope bound
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ}

theorem s102_Z_quad {s : ℝ} {Pw : ℝ} (r : ℕ) (hr : (d : ℝ) / 2 + 2 < r) {c1 : ℝ} (hc1 : 0 ≤ c1)
    (hker : ∀ f : Euc d → ℝ, ContDiff ℝ r f → weightedSobolevE r Pw f < ⊤ →
      IsR2PolyPairKernel s Pw (c1 * (weightedSobolevE r Pw f).toReal) (commutatorKernel d s (fun z => gradient f z)) ∧
      ∀ x y, |commutatorKernel d s (fun z => gradient f z) x y| ≤
        (c1 * (weightedSobolevE r Pw f).toReal) * s102_gk s Pw x y)
    {μ : Measure (Euc d)} [SFinite μ] (hgi : ∀ x, Integrable (s102_gk s Pw x) μ)
    (hgH : Integrable (fun x => ∫ y, s102_gk s Pw x y ∂μ) μ) {N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → EucConfig d N) (hY : Measurable Y)
    (hEi : Integrable (fun ζ => s102_Env (s102_gk s Pw) (Y ζ) μ) P) (ζ : Ω) :
    S102Z r Pw (fun φ => s102_fld P μ Y (commutatorKernel d s (fun x => gradient φ x)) ζ) ∧
      ∀ f : Euc d → ℝ, IsR2WeightedTest r Pw f →
        |s102_fld P μ Y (commutatorKernel d s (fun x => gradient f x)) ζ| ≤
          (c1 * N * (s102_Env (s102_gk s Pw) (Y ζ) μ + ∫ ζ', s102_Env (s102_gk s Pw) (Y ζ') μ ∂P)) *
            (weightedSobolevE r Pw f).toReal := by
  have hr1 : 1 ≤ r := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    have h2 : (2 : ℝ) < r := by linarith
    have h3 : 2 < r := by exact_mod_cast h2
    omega
  have hdiff : ∀ f : Euc d → ℝ, ContDiff ℝ r f → Differentiable ℝ f := fun f hf =>
    hf.differentiable (by exact_mod_cast (by omega : r ≠ 0))
  -- row conditions and integrability of the pair energies for a test `f`
  have hall : ∀ f : Euc d → ℝ, IsR2WeightedTest r Pw f →
      S102RowOK μ (commutatorKernel d s (fun x => gradient f x)) ∧
      Integrable (fun ζ => pairEnergy (commutatorKernel d s (fun x => gradient f x)) (Y ζ) μ) P ∧
      ∀ ζ, |s102_fld P μ Y (commutatorKernel d s (fun x => gradient f x)) ζ| ≤
        N * (c1 * (weightedSobolevE r Pw f).toReal) *
          (s102_Env (s102_gk s Pw) (Y ζ) μ + ∫ ζ', s102_Env (s102_gk s Pw) (Y ζ') μ ∂P) := by
    intro f hf
    obtain ⟨hpoly, hbd⟩ := hker f hf.1 hf.2
    have hB : 0 ≤ c1 * (weightedSobolevE r Pw f).toReal := mul_nonneg hc1 ENNReal.toReal_nonneg
    refine ⟨s102_rowOK_of_bound hpoly.measurable hgi hgH hbd, ?_⟩
    obtain ⟨h1, -, h3⟩ := s102_fld_bound P Y hY hB (s102_gk_meas s Pw) (s102_gk_nonneg s Pw) hgi hgH
      hpoly.measurable hbd hEi
    exact ⟨h1, h3⟩
  refine ⟨⟨?_, ?_, ?_⟩, fun f hf => ?_⟩
  · intro f g hf hg
    have hk : (fun x y => commutatorKernel d s (fun z => gradient (f + g) z) x y) =
        fun x y => commutatorKernel d s (fun z => gradient f z) x y +
          commutatorKernel d s (fun z => gradient g z) x y := by
      funext x y; exact s102_comm_add (hdiff f hf.1) (hdiff g hg.1) s x y
    obtain ⟨H1, I1, -⟩ := hall f hf
    obtain ⟨H2, I2, -⟩ := hall g hg
    show s102_fld P μ Y (commutatorKernel d s (fun x => gradient (f + g) x)) ζ = _
    have : commutatorKernel d s (fun x => gradient (f + g) x) =
        fun x y => commutatorKernel d s (fun z => gradient f z) x y +
          commutatorKernel d s (fun z => gradient g z) x y := hk
    rw [this]
    exact s102_fld_add P μ Y H1 H2 I1 I2 ζ
  · intro c f hf
    show s102_fld P μ Y (commutatorKernel d s (fun x => gradient (c • f) x)) ζ = _
    have : commutatorKernel d s (fun x => gradient (c • f) x) =
        fun x y => c * commutatorKernel d s (fun z => gradient f z) x y := by
      funext x y; exact s102_comm_smul c (hdiff f hf.1) s x y
    rw [this]
    exact s102_fld_smul P μ Y c _ ζ
  · refine ⟨c1 * N * (s102_Env (s102_gk s Pw) (Y ζ) μ + ∫ ζ', s102_Env (s102_gk s Pw) (Y ζ') μ ∂P), fun f hf => ?_⟩
    have := (hall f hf).2.2 ζ
    calc _ ≤ _ := this
      _ = _ := by ring
  · have := (hall f hf).2.2 ζ
    calc _ ≤ _ := this
      _ = _ := by ring

end HRS.MS.R2Interp

end
