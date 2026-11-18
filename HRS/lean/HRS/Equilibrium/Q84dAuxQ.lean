/-
# HRS.Equilibrium.Q84dAuxQ — packet Q84d: gradient and Laplacian of `F_N(ψ)` in one particle
-/
import HRS.Equilibrium.Q84dAuxP

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q84d_sum_sum_erase_split (i : Fin N) (f : Fin N → Fin N → ℝ) :
    ∑ a, ∑ b ∈ Finset.univ.erase a, f a b
      = ∑ b ∈ Finset.univ.erase i, f i b + ∑ a ∈ Finset.univ.erase i, f a i
        + ∑ a ∈ Finset.univ.erase i, ∑ b ∈ (Finset.univ.erase i).erase a, f a b := by
  have h1 : ∑ a, ∑ b ∈ Finset.univ.erase a, f a b
      = ∑ b ∈ Finset.univ.erase i, f i b + ∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase a, f a b :=
    (Finset.add_sum_erase Finset.univ (fun a => ∑ b ∈ Finset.univ.erase a, f a b) (Finset.mem_univ i)).symm
  have h2 : ∀ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase a, f a b
      = f a i + ∑ b ∈ (Finset.univ.erase i).erase a, f a b := by
    intro a ha
    have hai : a ≠ i := Finset.ne_of_mem_erase ha
    have hmem : i ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨hai.symm, Finset.mem_univ i⟩
    rw [← Finset.add_sum_erase (Finset.univ.erase a) (fun b => f a b) hmem, Finset.erase_right_comm]
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib]
  ring

/-- The part of the ordered pair sum not involving the index `i`. -/
def pairRestQ (b : Torus d → Torus d → ℝ) (i : Fin N) (Y : Config d N) : ℝ :=
  ∑ a ∈ Finset.univ.erase i, ∑ c ∈ (Finset.univ.erase i).erase a, b (Y a) (Y c)

theorem q84d_pairRest_update (b : Torus d → Torus d → ℝ) (i : Fin N) (Y : Config d N)
    (z : Torus d) : pairRestQ b i (Function.update Y i z) = pairRestQ b i Y := by
  unfold pairRestQ
  have h1 : ∀ a ∈ Finset.univ.erase i, Function.update Y i z a = Y a := fun a ha =>
    Function.update_of_ne (Finset.ne_of_mem_erase ha) _ _
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun c hc => ?_
  rw [h1 a ha, h1 c (Finset.mem_of_mem_erase hc)]

theorem q84d_pairSum_update (b : Torus d → Torus d → ℝ) (hsym : ∀ x y, b x y = b y x)
    (i : Fin N) (Y : Config d N) (z : Torus d) :
    pairSumOrdered b (Function.update Y i z) =
      2 * ∑ j ∈ Finset.univ.erase i, b z (Y j) + pairRestQ b i Y := by
  unfold pairSumOrdered
  rw [q84d_sum_sum_erase_split i (fun a c => b (Function.update Y i z a) (Function.update Y i z c))]
  have h1 : ∀ a ∈ Finset.univ.erase i, Function.update Y i z a = Y a := fun a ha =>
    Function.update_of_ne (Finset.ne_of_mem_erase ha) _ _
  have e1 : ∑ c ∈ Finset.univ.erase i, b (Function.update Y i z i) (Function.update Y i z c)
      = ∑ j ∈ Finset.univ.erase i, b z (Y j) := by
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [h1 c hc, Function.update_self]
  have e2 : ∑ a ∈ Finset.univ.erase i, b (Function.update Y i z a) (Function.update Y i z i)
      = ∑ j ∈ Finset.univ.erase i, b z (Y j) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [h1 a ha, Function.update_self, hsym]
  have e3 : ∑ a ∈ Finset.univ.erase i, ∑ c ∈ (Finset.univ.erase i).erase a,
      b (Function.update Y i z a) (Function.update Y i z c) = pairRestQ b i Y := by
    rw [← q84d_pairRest_update b i Y z]
    rfl
  rw [e1, e2, e3]; ring

/-- `∂_{ik}F_N(ψ)` (explicit form). -/
def Aik (d : ℕ) (ψ : Torus d → Torus d → ℝ) {N : ℕ} (i : Fin N) (k : Fin d) (Y : Config d N) : ℝ :=
  2 * (N : ℝ) ^ (-(3 / 2 : ℝ)) * ∑ j ∈ Finset.univ.erase i, gK ψ k (Y i) (Y j)

/-- `∂²_{ik}F_N(ψ)` (explicit form). -/
def Cik (d : ℕ) (ψ : Torus d → Torus d → ℝ) {N : ℕ} (i : Fin N) (k : Fin d) (Y : Config d N) : ℝ :=
  2 * (N : ℝ) ^ (-(3 / 2 : ℝ)) * ∑ j ∈ Finset.univ.erase i, hK ψ k (Y i) (Y j)

theorem q84d_slice_contDiffAt {ψ : Torus d → Torus d → ℝ}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) {x y : Torus d}
    (hxy : x ≠ y) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : Euc d => ψ (x + Torus.mk u) y) 0 := by
  have hcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (Torus.rep x, Torus.rep y) :=
    q84d_contDiffAt_lift2 hsm (q84d_mem_offDiag hxy)
  have e : (fun u : Euc d => ψ (x + Torus.mk u) y) = fun u => lift2 ψ (Torus.rep x + u, Torus.rep y) := by
    funext u
    simp [lift2, Q84a.q84a_mk_add, Torus.mk_rep]
  rw [e]
  have hg' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ)
      ((fun u : Euc d => (Torus.rep x + u, Torus.rep y)) 0) := by simpa using hcd
  exact ContDiffAt.comp (0 : Euc d) hg' ((contDiffAt_const.add contDiffAt_id).prodMk contDiffAt_const)

theorem q84d_gK_line_deriv {ψ : Torus d → Torus d → ℝ}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) {x y : Torus d}
    (hxy : x ≠ y) (k : Fin d) :
    HasDerivAt (fun τ : ℝ => gK ψ k (x + Torus.mk (τ • ek k)) y) (hK ψ k x y) 0 := by
  set G : Euc d × Euc d → ℝ := fun p => fderiv ℝ (lift2 ψ) p (EuclideanSpace.single k 1, 0) with hG
  have hcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (Torus.rep x, Torus.rep y) :=
    q84d_contDiffAt_lift2 hsm (q84d_mem_offDiag hxy)
  have hGd : DifferentiableAt ℝ G (Torus.rep x, Torus.rep y) := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ (lift2 ψ)) (Torus.rep x, Torus.rep y) :=
      hcd.fderiv_right (m := 1) (by norm_num)
    exact (h1.clm_apply contDiffAt_const).differentiableAt (by simp)
  have e : (fun τ : ℝ => gK ψ k (x + Torus.mk (τ • ek k)) y) =
      fun τ => G (Torus.rep x + τ • ek k, Torus.rep y) := by
    funext τ
    unfold gK
    rw [hG]
    simp only
    congr 1
    refine Q84a.q84a_fderiv_lift2_congr ψ ?_ (Torus.rep y)
    rw [Torus.mk_rep, Q84a.q84a_mk_add, Torus.mk_rep]
  rw [e]
  have hline : HasDerivAt (fun τ : ℝ => ((Torus.rep x + τ • ek k, Torus.rep y) : Euc d × Euc d))
      (ek k, (0 : Euc d)) 0 := by
    have h1 : HasDerivAt (fun τ : ℝ => τ • ek k) (ek k) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (ek k)
    exact (h1.const_add (Torus.rep x)).prodMk (hasDerivAt_const _ _)
  have hF : HasFDerivAt G (fderiv ℝ G (Torus.rep x, Torus.rep y))
      ((fun τ : ℝ => ((Torus.rep x + τ • ek k, Torus.rep y) : Euc d × Euc d)) 0) := by
    simpa using hGd.hasFDerivAt
  have := hF.comp_hasDerivAt (0 : ℝ) hline
  exact this

end HRS.Q84d

end
