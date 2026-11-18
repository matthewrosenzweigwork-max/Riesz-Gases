import HRS.MS.WadAux9
import HRS.MS.WadAux2

/-!
# S8.3, packet D1 (frozen vocabulary): the Mehler semigroup on `C_M`

Statements in the vocabulary of the frozen row `HRS.Whole.weighted_adjoint_decay`
(`MemCM`, `weightedSupE 0 (-M)`):

* `s83_P_memCM`: `f ∈ C_M ⇒ P_t f ∈ C_M` for `t ≥ 0`, `a > 0`, `ν ≥ 0`, `M ≥ 0`.
* `s83_P_wsup0`: `‖P_t f‖_{C_M} ≤ K_M ‖f‖_{C_M}` with `K_M = 2^M mom` independent of `t`.
* `s83_P_add_memCM`: `P_{t+s} f = P_t P_s f` for `f ∈ C_M`.
* `s83_P_tail_wsup`: `⟨x⟩^{-M}|P_t f(x)| ≤ (e^{-aMt} + ε) ‖f‖_{C_M}` for `‖x‖ ≥ R`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s83_P_memCM {M : ℝ} (hM : 0 ≤ M) {f : Euc d → ℝ} (hf : MemCM M f) {a ν t : ℝ} (ha : 0 < a)
    (hν : 0 ≤ ν) (ht : 0 ≤ t) : MemCM M (s83_P a ν t f) :=
  (s83_memCM_iff M _).2 (s83_P_cm ((s83_memCM_iff M f).1 hf) hM ha hν ht)

theorem s83_wsup0_ne_top {M : ℝ} {f : Euc d → ℝ} (hf : MemCM M f) :
    weightedSupE 0 (-M) f ≠ ⊤ := by
  obtain ⟨C, hC⟩ := s83_cm_wt ((s83_memCM_iff M f).1 hf)
  have hC0 := hC.nonneg
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((s83_wsup0_le_iff hC0 f).2 hC)

theorem s83_wt_of_memCM {M : ℝ} {f : Euc d → ℝ} (hf : MemCM M f) :
    Wt M (weightedSupE 0 (-M) f).toReal f :=
  s83_wt_of_wsup_ne_top (s83_wsup0_ne_top hf)

theorem s83_P_wsup0 {M : ℝ} (hM : 0 ≤ M) {f : Euc d → ℝ} (hf : MemCM M f) {a ν t : ℝ} (ha : 0 < a)
    (hν : 0 ≤ ν) (ht : 0 ≤ t) :
    weightedSupE 0 (-M) (s83_P a ν t f) ≤
      ENNReal.ofReal (2 ^ M * mom d M (Real.sqrt (ν / a))) * weightedSupE 0 (-M) f := by
  have hW := s83_wsup0_ne_top hf
  have hw := s83_wt_of_memCM hf
  have hK := s83_P_wt ((s83_memCM_iff M f).1 hf).1 hM hw ha hν ht
  have hnn := hK.nonneg
  have hle := (s83_wsup0_le_iff hnn _).2 hK
  refine hle.trans (le_of_eq ?_)
  have hKnn : 0 ≤ 2 ^ M * mom d M (Real.sqrt (ν / a)) :=
    mul_nonneg (by positivity) (s83_mom_nonneg _ _ (Real.sqrt_nonneg _))
  have e : (weightedSupE 0 (-M) f).toReal * 2 ^ M * mom d M (Real.sqrt (ν / a)) =
      (2 ^ M * mom d M (Real.sqrt (ν / a))) * (weightedSupE 0 (-M) f).toReal := by ring
  rw [e, ENNReal.ofReal_mul hKnn, ENNReal.ofReal_toReal hW]

theorem s83_P_add_memCM {M : ℝ} (hM : 0 ≤ M) {f : Euc d → ℝ} (hf : MemCM M f) {a ν t s : ℝ}
    (ha : 0 < a) (hν : 0 ≤ ν) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    s83_P a ν (t + s) f = s83_P a ν t (s83_P a ν s f) :=
  s83_P_add ((s83_memCM_iff M f).1 hf).1 hM (s83_wt_of_memCM hf) ha hν ht hs

/-- Far-field bound in the frozen vocabulary. -/
theorem s83_P_tail_wsup {M : ℝ} (hM : 0 ≤ M) {a ν t : ℝ} (ha : 0 < a) (hν : 0 ≤ ν) (ht : 0 ≤ t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ x : Euc d, R ≤ ‖x‖ → ∀ f : Euc d → ℝ, MemCM M f →
      |s83_P a ν t f x| ≤ (weightedSupE 0 (-M) f).toReal * (Real.exp (-a * M * t) + ε) *
        jbracket x ^ M := by
  obtain ⟨R, hR⟩ := s83_P_tail_bound (d := d) (E := ℝ) hM ha hν ht hε
  refine ⟨R, fun x hx f hf => ?_⟩
  have := hR x hx f _ ((s83_memCM_iff M f).1 hf).1 (s83_wt_of_memCM hf)
  rwa [Real.norm_eq_abs] at this

end HRS.MS.Wad
