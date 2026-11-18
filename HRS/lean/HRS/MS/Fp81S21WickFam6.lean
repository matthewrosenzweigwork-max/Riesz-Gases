import HRS.MS.Fp81S21WickFam4
import HRS.MS.Fp81S21WickFam5
import HRS.MS.Fp81S21GaussModification

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111

/-- Uniformly bounded extensions of the supplied Gaussian coordinates are
continuous in time on every reference L² input. -/
theorem fp81s21_wickFam_linear_family_continuous (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ G : GaussianRealization R,
          ∀ (T : ℝ → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ] Lp ℝ 2 G.P)
            (K : ℝ),
            (∀ u : ℝ, 0 ≤ u → ‖T u‖ ≤ K) →
            (∀ (u : ℝ), 0 ≤ u → ∀ α : MultiIndex p.d,
              ∀ hα : MemLp (oscTestFun (wholeSpaceIndex p.d : ℝ) α) 2
                  (HRS.Whole.withDensityReal R.ρβ),
              (fun ω : G.Ω => (T u (hα.toLp _)) ω) =ᵐ[G.P]
                fun ω => OscDual.eval (G.Z u ω)
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) →
            ∀ f, ContinuousOn (fun u => T u f) (Ici (0 : ℝ)) := by
  obtain ⟨δ0, hδ0, hδhalf, hcoord⟩ :=
    fp81s21_wickFam_oscillator_coordinate_continuous p
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R G T K hbound hagree f
  obtain ⟨_, _, hthermal⟩ := sol13_uniform_thermal_sup_bound p
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hρeq : R.ρβ = HRS.Whole.thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal
  have hρmeas : Measurable R.ρβ := by
    obtain ⟨-, ψ, hψ⟩ := HRS.MS.S21.s21_schwartz_thermal p.hd p.hs0 hsd p.ha p.hβ
    rw [hρeq, ← hψ]
    exact ψ.continuous.measurable
  let S := HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ)
  have hS : ∀ φ ∈ S, MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ) := by
    intro φ hφ
    exact HRS.MS.S111X1.x1_osc_memLp hρmeas
      (fun x => (HRS.Whole.u4_thermal_pos R.thermal x).le)
      (hthermal δ R) hφ
  let basis := fp81s21_wickFam_coordinate_class p R hS
  let D : Submodule ℝ (Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ)) :=
    Submodule.span ℝ (Set.range basis)
  have hdense : Dense (D : Set (Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ))) := fp81s21_wickFam_coordinate_dense p R hS
  apply fp81s21_contOn_Ici_of_nat
  intro n
  by_cases hn : n = 0
  · subst n
    simpa using (continuousOn_singleton : ContinuousOn (fun u : ℝ => T u f) {0})
  have hH : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hbase : ∀ α, ContinuousOn (fun u => T u (basis α)) (Icc (0 : ℝ) (n : ℝ)) := by
    intro α
    apply hcoord δ hδ hδle R (n : ℝ) hH G (fun u => T u (basis α)) α
    intro u hu
    exact hagree u hu α (hS _ (initialTestBasis (wholeSpaceIndex p.d : ℝ) α).2)
  have hD : ∀ v ∈ (D : Set (Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ))), ContinuousOn (fun u => T u v) (Icc (0 : ℝ) (n : ℝ)) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨α, rfl⟩ := hv
      exact hbase α
    | zero => simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : Lp ℝ 2 G.P)) (Icc 0 (n : ℝ)))
    | add x y hx hy ihx ihy =>
      convert ihx.add ihy using 1
      ext u
      simp
    | smul c x hx ihx =>
      convert ihx.const_smul c using 1
      ext u
      simp
  exact fp81s21_wickFam_continuous_of_dense (Icc 0 (n : ℝ)) T K
    (fun u hu => hbound u hu.1) (D : Set (Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ))) hdense hD f

#print axioms fp81s21_wickFam_linear_family_continuous
end HRS.Fp81.S21
end
