import HRS.MS.R2InterpAux96

/-!
# S10.2 (worker S10R), part 97 (packet F5l): the initial observation `obs(𝖨ζ_N^0)` is `ℱ_0`-measurable and equals `ζ_N^0(U^{0,τ_i}φ_i)`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}

theorem s102_obs_y0 (hs : S102Std C m T r c) (hP : (d : ℝ) < 2 * Pw) (hlin : S102Lin C m T) (hT : 0 < T)
    (hd : 1 ≤ d) (hP0 : 0 ≤ Pw) (hr : (d : ℝ) / 2 < r) {N : ℕ} (hN : 0 < N) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N)
    (hmom : Integrable (fun x : Euc d => jbracket x ^ Pw) (HRS.Whole.meanEmpirical (P.map (X 0)))) (L : ℕ) (ζ : Ω)
    (i : Fin (s102_q d L)) :
    s102_obs (s102_tauk hT L) (s102_alk L) (s102_y0 C m T P X ζ) i = s102_zf P X ζ 0 (s102_orb C m hT L i 0) := by
  have hz : S102Z r Pw (s102_zf P X ζ 0) := s102_Z_zf hd hP0 hr hN P X 0 (by simpa using hmom) ζ
  have hy : s102_y0 C m T P X ζ = r2InitProp C m T (s102_zf P X ζ 0) := by
    unfold s102_y0 s102_zf
    simp only [Real.toNNReal_zero]
  rw [hy, s102_obs_apply, ← s102_r2PathAt_of_mem _ (s102_tauk hT L i).2,
    s102_initProp_at hP hs.hD hlin hz hT.le (s102_tauk hT L i).2]
  exact s102_Vprop_coord hP hs.hD hz hlin ⟨le_rfl, hT.le⟩ ⟨(s102_tauk hT L i).2.1, (s102_tauk hT L i).2.2⟩ _

end HRS.MS.R2Interp

end
