import HRS.MS.R26T8AO03b13

/-!
# S8.2 T8A O03b (part 14): `f ↦ D f X` is linear on test functions, at collision-free `X`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U HRS.MS.S82W HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_o03b_D_lin (N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta M C : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) :
    r26t8a_o03b_Lin d (fun f : Euc d → ℝ => r26t8a_correctedD (N := N) a beta rho Psi f X) := by
  refine ⟨fun A B f g hf hg => ?_, fun A c f hf => ?_⟩
  · have hfg := r26t8a_o03b_tb_add hf hg
    have := r26t8a_o03b_D_lincomb N hd hN a beta M C ha hbeta hM hC rho hrho Psi hPsi hfg hf hg 1 1
      (by rw [r26t8a_o03b_Q_add N hd hN a beta M C ha hbeta hM hC rho hrho Psi hPsi hf hg]; simp)
      (fun x y => by rw [r26t8a_o03b_hs_add hf.1 hg.1 x y]; ring)
      (fun x => by
        have e : hSource (f + g) x = fun y => hSource f x y + hSource g x y :=
          funext fun y => r26t8a_o03b_hs_add hf.1 hg.1 x y
        rw [e, integral_add (r26t8a_o03b_hs_int hd ha hbeta hrho hf x) (r26t8a_o03b_hs_int hd ha hbeta hrho hg x)]
        ring) hX
    simpa using this
  · have hcf := r26t8a_o03b_tb_smul c hf
    have := r26t8a_o03b_D_lincomb N hd hN a beta M C ha hbeta hM hC rho hrho Psi hPsi hcf hf hf c 0
      (by rw [r26t8a_o03b_Q_smul N a beta M C rho Psi hPsi hf c]; simp)
      (fun x y => by rw [r26t8a_o03b_hs_smul c hf.1 x y]; ring)
      (fun x => by
        have e : hSource (c • f) x = fun y => c * hSource f x y :=
          funext fun y => r26t8a_o03b_hs_smul c hf.1 x y
        rw [e, integral_const_mul]
        ring) hX
    simpa using this

end HRS.MS.R26T8A
