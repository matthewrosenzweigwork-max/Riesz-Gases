import HRS.MS.R26T8AP06u
import HRS.MS.R26T8AP06w
import HRS.MS.R26T8AP06d10

/-!
# S8.2 Taylor split (T), step B2c: the polynomial part `Pfull` and its centre-derivative words
`r26t8a_Pfull m c Y w = Σ_{ℓ ≤ m} (1/ℓ!) c ℓ Y (w,…,w)`; jointly `C^n` if the `c ℓ` are, and
`D^p_Y Pfull (X,w) u = Σ_ℓ (1/ℓ!) (D^p c ℓ (X) u)(w,…,w)`.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS

variable {d : ℕ}

def r26t8a_Pfull (m : ℕ) (c : (ℓ : ℕ) → Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => Euc d) ℝ)
    (Y w : Euc d) : ℝ :=
  ∑ ℓ ∈ Finset.range (m + 1), (1 / (ℓ.factorial : ℝ)) * c ℓ Y (fun _ => w)

theorem r26t8a_Pfull_contDiff (m : ℕ) (c : (ℓ : ℕ) → Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => Euc d) ℝ)
    {n : WithTop ℕ∞} (hc : ∀ ℓ ≤ m, ContDiff ℝ n (c ℓ)) :
    ContDiff ℝ n (fun Yw : Euc d × Euc d => r26t8a_Pfull m c Yw.1 Yw.2) := by
  refine ContDiff.sum fun ℓ hℓ => contDiff_const.mul ?_
  exact r26t8a_cmm_diag_contDiff ℓ (fun Yw : Euc d × Euc d => c ℓ Yw.1) (fun Yw => Yw.2)
    ((hc ℓ (by rw [Finset.mem_range] at hℓ; omega)).comp contDiff_fst) contDiff_snd

theorem r26t8a_Pfull_word (m : ℕ) (c : (ℓ : ℕ) → Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => Euc d) ℝ)
    {p : ℕ} (hc : ∀ ℓ ≤ m, ContDiff ℝ (p : WithTop ℕ∞) (c ℓ)) (X w : Euc d) (u : Fin p → Euc d) :
    iteratedFDeriv ℝ p (fun Y => r26t8a_Pfull m c Y w) X u =
      ∑ ℓ ∈ Finset.range (m + 1), (1 / (ℓ.factorial : ℝ)) * iteratedFDeriv ℝ p (c ℓ) X u (fun _ => w) := by
  have hterm : ∀ ℓ ∈ Finset.range (m + 1), ∀ Y : Euc d,
      (1 / (ℓ.factorial : ℝ)) * c ℓ Y (fun _ => w) =
        (((1 / (ℓ.factorial : ℝ)) • ContinuousMultilinearMap.apply ℝ (fun _ : Fin ℓ => Euc d) ℝ (fun _ => w)) :
          ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => Euc d) ℝ →L[ℝ] ℝ) (c ℓ Y) := fun ℓ _ Y => by
    simp
  unfold r26t8a_Pfull
  rw [iteratedFDeriv_fun_sum_apply (fun ℓ hℓ => ?_)]
  swap
  · refine ContDiffAt.mul contDiffAt_const ?_
    exact (r26t8a_cmm_diag_contDiff ℓ (fun Y : Euc d => c ℓ Y) (fun _ => w)
      (hc ℓ (by rw [Finset.mem_range] at hℓ; omega)) contDiff_const).contDiffAt
  rw [ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have hfun : (fun Y : Euc d => (1 / (ℓ.factorial : ℝ)) * c ℓ Y (fun _ => w)) =
      (((1 / (ℓ.factorial : ℝ)) • ContinuousMultilinearMap.apply ℝ (fun _ : Fin ℓ => Euc d) ℝ (fun _ => w)) :
          ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => Euc d) ℝ →L[ℝ] ℝ) ∘ c ℓ := by
    funext Y; exact hterm ℓ hℓ Y
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_left _
    ((hc ℓ (by rw [Finset.mem_range] at hℓ; omega)).contDiffAt) le_rfl]
  simp

end HRS.MS.R26T8A
