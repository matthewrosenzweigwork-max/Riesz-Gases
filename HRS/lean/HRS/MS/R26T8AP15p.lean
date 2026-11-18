import HRS.MS.R26T8AP15o

/-!
# S8.2 T8A P15p: conormal bounds for the local operator `Lop` applied in the first variable
* `r26t8a_cd2_of_conormal`, `_slice_x`, `_slice_y`: a `Conormal (k+2)` pair function is `C²` (also in each slice) off the diagonal;
* `r26t8a_Kx_conormal`: `Q` conormal `(k+2) b M s A` implies `(x,y) ↦ Lop Q(.,y)(x)` is `Conormal k b (M+1) (s+2) (c A)`;
* `r26t8a_Lop_onevar_x/_y`: for `r ∈ C^{k+2}` with jets `≤ B jb^M`, the pair functions `Lop r (x)` and `Lop r (y)` are conormal of every order.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_cd2_of_conormal {k b : ℕ} {M s A : ℝ} {Q : Euc d → Euc d → ℝ} (hQ : Conormal (k + 2) b M s A Q)
    {x y : Euc d} (hxy : x ≠ y) : ContDiffAt ℝ 2 (fun q : Euc d × Euc d => Q q.1 q.2) (x, y) := by
  have hopen : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  exact (hQ.1.contDiffAt (hopen.mem_nhds hxy)).of_le (by exact_mod_cast (by omega : 2 ≤ k + 2))

theorem r26t8a_slice_x {k b : ℕ} {M s A : ℝ} {Q : Euc d → Euc d → ℝ} (hQ : Conormal (k + 2) b M s A Q)
    {x y : Euc d} (hxy : x ≠ y) : ContDiffAt ℝ 2 (fun w => Q w y) x :=
  (r26t8a_cd2_of_conormal hQ hxy).comp x (contDiffAt_id.prodMk contDiffAt_const)

theorem r26t8a_slice_y {k b : ℕ} {M s A : ℝ} {Q : Euc d → Euc d → ℝ} (hQ : Conormal (k + 2) b M s A Q)
    {x y : Euc d} (hxy : x ≠ y) : ContDiffAt ℝ 2 (fun w => Q x w) y :=
  (r26t8a_cd2_of_conormal hQ hxy).comp y (contDiffAt_const.prodMk contDiffAt_id)

theorem r26t8a_Kx_conormal {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (C : WholeCoeff d) (α : Fin d → Euc d → ℝ)
    (hb : ∀ i x, C.drift 0 x i = α i x) (k b : ℕ) (M s B : ℝ) (hB : 0 ≤ B)
    (hα : ∀ i, ContDiff ℝ (k : WithTop ℕ∞) (α i))
    (hαb : ∀ i, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (α i) x‖ ≤ B * jbracket x) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (Q : Euc d → Euc d → ℝ) (A : ℝ), 0 ≤ A → Conormal (k + 2) b M s A Q →
      Conormal k b (M + 1) (s + 2) (c * A) (fun x y => r26t8a_Lop C (fun w => Q w y) x) := by
  obtain ⟨c, hc, h⟩ := r26t8a_LxP_conormal hchi k b M s C.ν B hB α hα hαb
  refine ⟨c, hc, fun Q A hA hQ => ?_⟩
  refine r26t8a_conormal_congr (fun x y hxy => ?_) (h Q A hA hQ)
  exact (r26t8a_LxP_eq C α hb Q x y (r26t8a_slice_x hQ hxy)).symm

theorem r26t8a_Lop_onevar_x {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (C : WholeCoeff d) (α : Fin d → Euc d → ℝ)
    (hb : ∀ i x, C.drift 0 x i = α i x) (k : ℕ) (M B σ : ℝ) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hα : ∀ i, ContDiff ℝ (k : WithTop ℕ∞) (α i))
    (hαb : ∀ i, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (α i) x‖ ≤ B * jbracket x) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (r : Euc d → ℝ) (Br : ℝ), 0 ≤ Br → ContDiff ℝ ((k + 2 : ℕ) : WithTop ℕ∞) r →
      (∀ j ≤ k + 2, ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ Br * jbracket x ^ M) →
      Conormal k 1 (M + 1) σ (c * Br) (fun x _ => r26t8a_Lop C r x) := by
  obtain ⟨c, hc, h⟩ := r26t8a_Kx_conormal hchi C α hb k 1 M (σ - 2) B hB hα hαb
  refine ⟨c * 2 ^ (k + 2), by positivity, fun r Br hBr hr hj => ?_⟩
  have h1 : Conormal (k + 2) 1 M (σ - 2) (2 ^ (k + 2) * Br) (fun x _ => r x) :=
    r26t8a_f24_conormal_swap hchi (r26t8a_conormal_of_snd hM hBr hr hj)
  have h2 := h (fun x _ => r x) _ (by positivity) h1
  refine r26t8a_conormal_mono_sA (by positivity) (le_of_eq (by ring)) (le_of_eq (by ring)) h2

theorem r26t8a_Lop_onevar_y {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (C : WholeCoeff d) (α : Fin d → Euc d → ℝ)
    (hb : ∀ i x, C.drift 0 x i = α i x) (k : ℕ) (M B σ : ℝ) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hα : ∀ i, ContDiff ℝ (k : WithTop ℕ∞) (α i))
    (hαb : ∀ i, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (α i) x‖ ≤ B * jbracket x) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (r : Euc d → ℝ) (Br : ℝ), 0 ≤ Br → ContDiff ℝ ((k + 2 : ℕ) : WithTop ℕ∞) r →
      (∀ j ≤ k + 2, ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ Br * jbracket x ^ M) →
      Conormal k 1 (M + 1) σ (c * Br) (fun _ y => r26t8a_Lop C r y) := by
  obtain ⟨c, hc, h⟩ := r26t8a_Lop_onevar_x hchi C α hb k M B σ hB hM hα hαb
  exact ⟨c, hc, fun r Br hBr hr hj => r26t8a_f24_conormal_swap hchi (h r Br hBr hr hj)⟩

end HRS.MS.R26T8A
