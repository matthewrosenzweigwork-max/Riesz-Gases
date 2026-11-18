import HRS.PDE.MovAAux18

/-!
# MOVA Aux19: the mean-field equation `∂_tρ = pdeRHS(ρ)` holds pointwise on `[0,T]`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

set_option maxHeartbeats 1600000 in
theorem mova_pde_pointwise (D : DynData d) (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ))
    (hV : Torus.IsCk 2 D.V) {T : ℝ} (hT : 0 < T) {ρ ρt : ℝ → Torus d → ℝ}
    (hmf : IsMeanFieldSolution D T ρ) (hρt : IsC12Test T ρ ρt) :
    ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, ρt r x = mova_pdeRHS D (ρ r) x := by
  have hcP := mova_cont_pde D hρt hV
  have hIoo : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x, ρt t x = mova_pdeRHS D (ρ t) x := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
    have hct : Continuous (ρt t) := mova_cont_ρt_slice hρt htI
    have hcp : Continuous (mova_pdeRHS D (ρ t)) :=
      hcP.comp (continuous_const.prodMk continuous_id :
        Continuous fun x : Torus d => ((⟨t, htI⟩ : Set.Icc (0 : ℝ) T), x))
    have hz := mova_eq_zero_of_integral_zero (f := fun x => ρt t x - mova_pdeRHS D (ρ t) x)
      (hct.sub hcp) (fun ψ hψ => by
        have hψc := mova_continuous_of_isCk hψ
        have e : (fun x => ψ x * (ρt t x - mova_pdeRHS D (ρ t) x)) =
            fun x => ψ x * ρt t x - ψ x * mova_pdeRHS D (ρ t) x := funext fun x => by ring
        have i1 : Integrable (fun x => ψ x * ρt t x) := mova_int_cont (hψc.mul hct)
        have i2 : Integrable (fun x => ψ x * mova_pdeRHS D (ρ t) x) := mova_int_cont (hψc.mul hcp)
        rw [e, integral_sub i1 i2, mova_pde_Ioo D hM hV hT hmf hρt ht ψ hψ, sub_self])
    intro x
    have := hz x
    linarith
  intro r hr x
  -- extension by continuity in `r`
  have hu : Continuous fun q : Set.Icc (0 : ℝ) T => ρt q x :=
    hρt.cont_time_deriv.comp (continuous_id.prodMk continuous_const :
      Continuous fun q : Set.Icc (0 : ℝ) T => (q, x))
  have hv : Continuous fun q : Set.Icc (0 : ℝ) T => mova_pdeRHS D (ρ q) x :=
    hcP.comp (continuous_id.prodMk continuous_const :
      Continuous fun q : Set.Icc (0 : ℝ) T => (q, x))
  let u : ℝ → ℝ := fun s => ρt s x
  let v : ℝ → ℝ := fun s => mova_pdeRHS D (ρ s) x
  have hu' : ContinuousOn u (Set.Icc (0 : ℝ) T) := by
    rw [continuousOn_iff_continuous_restrict]; exact hu
  have hv' : ContinuousOn v (Set.Icc (0 : ℝ) T) := by
    rw [continuousOn_iff_continuous_restrict]; exact hv
  have heq : Set.EqOn u v (Set.Icc (0 : ℝ) T) :=
    Set.EqOn.of_subset_closure (s := Set.Ioo 0 T) (fun t ht => hIoo t ht x) hu' hv'
      Set.Ioo_subset_Icc_self (by rw [closure_Ioo hT.ne])
  exact heq hr

end HRS
