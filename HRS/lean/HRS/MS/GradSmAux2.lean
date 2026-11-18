import HRS.MS.GradSmAux1
import HRS.Whole.Orbits

/-!
# S6.7 packet S67B: gradient smoothing (`W:r2mov:gradient-smoothing`), part 2: the usable form

Part 1 (`GradSmAux1.s67b_gs_smooth`) assumes `F ∈ C^m` with `m` the regularity of the drift.  Here:

* `s67b_gs_close`: only `F ∈ C^{k+1}` with bounds `M i` for `i ≤ k+1` (drift regularity `m ≥ max 2 (k+1)` free); `sg t F ∈ C^{k+1}`
  and `‖D^j P_t F‖ ≤ C (1 + t^{-1/2}) e^{-c0 t} ∑_{i ≤ k} M i`, `1 ≤ j ≤ k+1`, `t > 0`.  (Closing in the data: mollification
  `pois_moll_data`, `pois_moll_close_data`.)  The bound `M_{k+1}` is qualitative (it does not enter).
* `s67b_gs_cb`: the form of S6.7, `‖∇ P_t F‖_{C_b^k}` as `cbNormVecE k (gradient (P_t F))` (in `ℝ≥0∞`), and
  `∇ P_t F ∈ C^k`.

Normalisation of `sg`: `Δ - q x·∇ + B·∇` (`ν = 1`), see `GradSmAux1`.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Interval RealInnerProductSpace ContDiff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg
  HRS.MS.PoisMarkov HRS.MS.PoisKolm HRS.MS.PoisGrad HRS.MS.PoisMax HRS.MS.PoisMoll
  HRS.MS.PoisHigh

noncomputable section

universe u

namespace HRS.MS.GradSm

variable {d : ℕ}

/-- **Gradient smoothing, data in `C^{k+1}`.** -/
theorem s67b_gs_close (q Mb : ℝ) (hq : 0 < q) (hMb : 0 ≤ Mb) (m : ℕ) (hm : 2 ≤ m) (k : ℕ)
    (hk : k + 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ),
      IsBrownianFiltration P ℱ W → ∀ B : Euc d → Euc d, HasCbBound m Mb B →
      ∀ F : Euc d → ℝ, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) F → ∀ M : ℕ → ℝ,
      (∀ i ≤ k + 1, ∀ y, ‖iteratedFDeriv ℝ i F y‖ ≤ M i) → ∀ t : ℝ, 0 < t →
      ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (sg P W q B t F) ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ k + 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (sg P W q B t F) x‖ ≤
        C * (1 + (Real.sqrt t)⁻¹) * Real.exp (-(pm_c0 q Mb) * t) *
          ∑ i ∈ Finset.range (k + 1), M i := by
  obtain ⟨C, hC0, hC⟩ := s67b_gs_smooth (d := d) q Mb hq hMb m hm k hk
  refine ⟨C, hC0, fun {Ω} {mΩ} P _ ℱ W hW B hBm F hF M hM t ht0 => ?_⟩
  have hWs := sgNoise_of_brownian hW
  set kk : ℕ := k + 1 with hkk
  have hM0 : ∀ i ≤ kk, 0 ≤ M i := fun i hi => (norm_nonneg _).trans (hM i hi 0)
  set M' : ℝ := ∑ i ∈ Finset.range (kk + 1), |M i| with hM'def
  have hMM' : ∀ i ≤ kk, M i ≤ M' := fun i hi =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |M i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega)))
  obtain ⟨Csg, -, hCsg⟩ := sg_contDiff (d := d) q Mb hq m hm t ht0.le kk hk
  refine ⟨(hCsg P W hWs B hBm F hF M' (fun i hi y => (hM i hi y).trans (hMM' i hi)) t
    ⟨ht0.le, le_rfl⟩).1, fun j hj1 hjk x => ?_⟩
  obtain ⟨hn, hnc, hnM, hnb, hn0, hnlim⟩ := pois_moll_data (k := kk) hF (M := M) hM
  choose Cn hCn using hnb
  set K : ℝ := ∑ i ∈ Finset.range (k + 1), M i with hK
  set Bd : ℝ := C * (1 + (Real.sqrt t)⁻¹) * Real.exp (-(pm_c0 q Mb) * t) * K with hBd
  have key := pois_moll_close_data (P := P) q Mb hq m hm kk hk kk le_rfl hBm W hWs
    (hn := hn) (fun n => (hnc n).of_le (by exact_mod_cast le_top))
    (fun n => ⟨M', fun i hi y => (hnM n i hi y).trans (hMM' i hi)⟩) hF (M := M')
    (fun i hi y => (hM i hi y).trans (hMM' i hi)) hnlim (M0 := M 0) hn0 ht0.le
    (C := fun i => if i = 0 then M 0 else Bd) (fun n i hi y => ?_) j hjk x
  · have : j ≠ 0 := by omega
    simpa [this] using key
  · by_cases hi0 : i = 0
    · subst hi0
      rw [norm_iteratedFDeriv_zero]
      simpa using gs_sg_abs_le (P := P) (W := W) (q := q) (B := B) (hn0 n) t y
    · simp only [hi0, ite_false]
      have hb := hC P ℱ W hW B hBm (hn n) ((hnc n).of_le (by exact_mod_cast le_top))
        (fun i => if i ≤ kk then M i else Cn n i) (fun i hi z => ?_) t ht0 i (by omega) hi y
      · refine hb.trans (le_of_eq ?_)
        rw [hBd, hK]
        congr 1
        refine Finset.sum_congr rfl (fun l hl => ?_)
        have := Finset.mem_range.1 hl
        simp only [show l ≤ kk by omega, ite_true]
      · by_cases hik : i ≤ kk
        · simp only [hik, ite_true]; exact hnM n i hik z
        · simp only [hik, ite_false]; exact hCn n i z

theorem s67b_norm_iter_grad {u : Euc d → ℝ} {i : ℕ} (hu : ContDiff ℝ ((i + 1 : ℕ) : WithTop ℕ∞) u)
    (x : Euc d) :
    ‖iteratedFDeriv ℝ i (fun y => gradient u y) x‖ = ‖iteratedFDeriv ℝ (i + 1) u x‖ := by
  have e : (fun y => gradient u y) = (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ u := by
    funext y; rfl
  rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, norm_iteratedFDeriv_fderiv]

theorem s67b_contDiff_gradient {u : Euc d → ℝ} {k : ℕ}
    (hu : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) u) :
    ContDiff ℝ (k : WithTop ℕ∞) (fun y => gradient u y) := by
  have e : (fun y => gradient u y) = (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ u := by
    funext y; rfl
  rw [e]
  refine (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp ?_
  exact hu.fderiv_right (by push_cast; exact le_rfl)


/-- **Gradient smoothing in the `C_b^k` norm of the gradient** (the form consumed by S6.7):
for `F ∈ C^{k+1}` with `‖D^i F‖ ≤ M i` (`i ≤ k+1`), `t > 0`:
`∇ P_t F ∈ C^k` and `‖∇ P_t F‖_{C_b^k} ≤ C (1 + t^{-1/2}) e^{-c0 t} ∑_{i ≤ k} M i`
(`cbNormVecE`, the sum over `j ≤ k` of `sup_x ‖D^j ∇P_tF‖`, in `ℝ≥0∞`). -/
theorem s67b_gs_cb (q Mb : ℝ) (hq : 0 < q) (hMb : 0 ≤ Mb) (m : ℕ) (hm : 2 ≤ m) (k : ℕ)
    (hk : k + 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ),
      IsBrownianFiltration P ℱ W → ∀ B : Euc d → Euc d, HasCbBound m Mb B →
      ∀ F : Euc d → ℝ, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) F → ∀ M : ℕ → ℝ,
      (∀ i ≤ k + 1, ∀ y, ‖iteratedFDeriv ℝ i F y‖ ≤ M i) → ∀ t : ℝ, 0 < t →
      ContDiff ℝ (k : WithTop ℕ∞) (fun x => gradient (sg P W q B t F) x) ∧
      cbNormVecE k (fun x => gradient (sg P W q B t F) x) ≤
        ENNReal.ofReal (C * (1 + (Real.sqrt t)⁻¹) * Real.exp (-(pm_c0 q Mb) * t) *
          ∑ i ∈ Finset.range (k + 1), M i) := by
  obtain ⟨C, hC0, hC⟩ := s67b_gs_close (d := d) q Mb hq hMb m hm k hk
  refine ⟨((k : ℝ) + 1) * C, by positivity, fun {Ω} {mΩ} P _ ℱ W hW B hBm F hF M hM t ht0 => ?_⟩
  obtain ⟨hcd, hb⟩ := hC P ℱ W hW B hBm F hF M hM t ht0
  refine ⟨s67b_contDiff_gradient hcd, ?_⟩
  set Bd : ℝ := C * (1 + (Real.sqrt t)⁻¹) * Real.exp (-(pm_c0 q Mb) * t) *
    ∑ i ∈ Finset.range (k + 1), M i with hBd
  unfold cbNormVecE
  have h1 : ∀ j ∈ Finset.range (k + 1), (⨆ x : Euc d,
      ENNReal.ofReal ‖iteratedFDeriv ℝ j (fun y => gradient (sg P W q B t F) y) x‖) ≤
      ENNReal.ofReal Bd := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    refine iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
    rw [s67b_norm_iter_grad (hcd.of_le (by exact_mod_cast hj')) x]
    exact hb (j + 1) (by omega) (by omega) x
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hBd0 : 0 ≤ Bd := by
    have hM0 : ∀ i ≤ k + 1, 0 ≤ M i := fun i hi => (norm_nonneg _).trans (hM i hi 0)
    have : 0 ≤ ∑ i ∈ Finset.range (k + 1), M i := Finset.sum_nonneg fun i hi => hM0 i (by
      have := Finset.mem_range.1 hi; omega)
    rw [hBd]; positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine le_of_eq (congrArg _ ?_)
  rw [hBd]; push_cast; ring

end HRS.MS.GradSm
