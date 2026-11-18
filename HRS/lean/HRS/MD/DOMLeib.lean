/-
# HRS.MD.DOMLeib — packet DOM-LEIB

For `Fe ε = χ_ε (F - c)`: the product rule for `configGrad`, `configLap` and `particleGen` at collision-free
configurations, smoothness of the lift on the covering space, and compact support off collisions.
-/
import HRS.MD.DOMCut2
import HRS.Stochastic.SelectedFlow

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.MD.DOMProof

open HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

/-- The approximant `χ_ε · (F - c)`. -/
def Fe (ε c : ℝ) (F : Config d N → ℝ) (X : Config d N) : ℝ := chi ε X * (F X - c)

theorem domp_update_zero (X : Config d N) (i : Fin N) :
    Function.update X i (X i + Torus.mk (0 : Euc d)) = X := by
  rw [q84d_mk_zero, add_zero, Function.update_eq_self]

theorem domp_gradient_sub_const (f : Euc d → ℝ) (c : ℝ) (x : Euc d) :
    gradient (fun z => f z - c) x = gradient f x := by
  apply (InnerProductSpace.toDual ℝ (Euc d)).injective
  rw [toDual_gradient, toDual_gradient, fderiv_sub_const]

theorem domp_dk_sub_const (f : Euc d → ℝ) (c : ℝ) (k : Fin d) (x : Euc d) :
    dk (fun z => f z - c) k x = dk f k x := by
  unfold dk; rw [fderiv_sub_const]

theorem domp_lap_sub_const {f : Euc d → ℝ} {x : Euc d} (hf : ContDiffAt ℝ 2 f x) (c : ℝ) :
    Laplacian.laplacian (fun z => f z - c) x = Laplacian.laplacian f x := by
  have hg : ContDiffAt ℝ 2 (fun z => f z - c) x := hf.sub contDiffAt_const
  rw [domp_lap_eq_sum_ddk hg, domp_lap_eq_sum_ddk hf]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold ddk
  have : dk (fun z => f z - c) k = dk f k := funext fun z => domp_dk_sub_const f c k z
  rw [this]

section Leibniz

variable {F : Config d N → ℝ} {ε c : ℝ} {X : Config d N} {i : Fin N}

theorem domp_configGrad_Fe
    (hF : ContDiffAt ℝ 2 (fun u : Euc d => F (Function.update X i (X i + Torus.mk u))) 0)
    (hχ : ContDiffAt ℝ 2 (fun u : Euc d => chi ε (Function.update X i (X i + Torus.mk u))) 0) :
    configGrad (Fe ε c F) X i =
      chi ε X • configGrad F X i + (F X - c) • configGrad (chi ε) X i := by
  have hg : ContDiffAt ℝ 2 (fun u : Euc d => F (Function.update X i (X i + Torus.mk u)) - c) 0 :=
    hF.sub contDiffAt_const
  have h := domp_gradient_mul (hχ.differentiableAt (by simp)) (hg.differentiableAt (by simp))
  unfold configGrad Fe
  rw [h, domp_gradient_sub_const, domp_update_zero]

theorem domp_configLap_Fe
    (hF : ContDiffAt ℝ 2 (fun u : Euc d => F (Function.update X i (X i + Torus.mk u))) 0)
    (hχ : ContDiffAt ℝ 2 (fun u : Euc d => chi ε (Function.update X i (X i + Torus.mk u))) 0) :
    configLap (Fe ε c F) X i =
      chi ε X * configLap F X i +
        2 * inner ℝ (configGrad (chi ε) X i) (configGrad F X i) + (F X - c) * configLap (chi ε) X i := by
  have hg : ContDiffAt ℝ 2 (fun u : Euc d => F (Function.update X i (X i + Torus.mk u)) - c) 0 :=
    hF.sub contDiffAt_const
  have h := domp_lap_mul hχ hg
  unfold configLap configGrad Fe
  rw [h, domp_lap_sub_const hF, domp_gradient_sub_const]
  simp only [domp_update_zero]

end Leibniz

section Slices

variable {ψ : Torus d → Torus d → ℝ}

/-- `F_N(ψ)` is `C^∞` along the displacement of particle `i` at collision-free configurations. -/
theorem domp_Fstat_slice (hsymm : IsSymmPair ψ)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) (X : Config d N)
    (hX : ∀ a b : Fin N, a ≠ b → X a ≠ X b) (i : Fin N) :
    ContDiffAt ℝ 2 (fun u : Euc d => Fstat ψ (Function.update X i (X i + Torus.mk u))) 0 := by
  have hφ : (fun u : Euc d => Fstat ψ (Function.update X i (X i + Torus.mk u))) =
      fun u => (N : ℝ) ^ (-(3 / 2 : ℝ)) * (2 * ∑ j ∈ Finset.univ.erase i, ψ (X i + Torus.mk u) (X j) +
        pairRestQ ψ i X) := by
    funext u
    unfold Fstat
    rw [q84d_pairSum_update ψ hsymm i X (X i + Torus.mk u)]
  rw [hφ]
  have hcd : ∀ j ∈ Finset.univ.erase i,
      ContDiffAt ℝ 2 (fun u : Euc d => ψ (X i + Torus.mk u) (X j)) 0 := fun j hj =>
    (q84d_slice_contDiffAt hsm (hX i j (Finset.ne_of_mem_erase hj).symm)).of_le (by norm_cast)
  exact contDiffAt_const.mul ((contDiffAt_const.mul (ContDiffAt.sum hcd)).add contDiffAt_const)

end Slices

/-- The product rule for the generator. -/
theorem domp_particleGen_Fe {V : Torus d → ℝ} {β : ℝ} {F : Config d N → ℝ} {ε c : ℝ}
    {X : Config d N}
    (hF : ∀ i, ContDiffAt ℝ 2 (fun u : Euc d => F (Function.update X i (X i + Torus.mk u))) 0)
    (hχ : ∀ i, ContDiffAt ℝ 2 (fun u : Euc d => chi ε (Function.update X i (X i + Torus.mk u))) 0) :
    particleGen d s V β (Fe ε c F) X =
      chi ε X * particleGen d s V β F X +
        ∑ i, (β⁻¹ * (2 * inner ℝ (configGrad (chi ε) X i) (configGrad F X i) +
            (F X - c) * configLap (chi ε) X i) -
          (F X - c) * inner ℝ (Torus.grad V (X i) + (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
            periodicRieszGrad d s (X i - X j)) (configGrad (chi ε) X i)) := by
  unfold particleGen
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [domp_configGrad_Fe (hF i) (hχ i), domp_configLap_Fe (hF i) (hχ i), inner_add_right,
    inner_smul_right, inner_smul_right]
  ring

/-! ### Smoothness of the lift and compact support -/

section Smooth

variable {ψ : Torus d → Torus d → ℝ}

theorem domp_Fstat_lift (Y : Fin N → Euc d) :
    Fstat ψ (fun i => Torus.mk (Y i)) =
      (N : ℝ) ^ (-(3 / 2 : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i, lift2 ψ (Y i, Y j) := by
  unfold Fstat pairSumOrdered lift2
  rfl

theorem domp_contDiffAt_Fstat_lift (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d))
    (Y : Fin N → Euc d) (hY : ∀ a b : Fin N, a ≠ b → Torus.mk (Y a) ≠ Torus.mk (Y b)) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun Z : Fin N → Euc d => Fstat ψ (fun i => Torus.mk (Z i))) Y := by
  have e : (fun Z : Fin N → Euc d => Fstat ψ (fun i => Torus.mk (Z i))) =
      fun Z => (N : ℝ) ^ (-(3 / 2 : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i, lift2 ψ (Z i, Z j) :=
    funext domp_Fstat_lift
  rw [e]
  refine contDiffAt_const.mul (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j hj => ?_)
  have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (Y i, Y j) :=
    q84d_contDiffAt_lift2 hsm (show (Y i, Y j) ∈ offDiag d from hY i j hij)
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Z : Fin N → Euc d => (Z i, Z j)) :=
    (contDiff_apply ℝ (Euc d) i).prodMk (contDiff_apply ℝ (Euc d) j)
  exact ContDiffAt.comp Y h1 h2.contDiffAt

theorem domp_contDiff_Fe_lift (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d))
    {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (configLift (fun _ => Fe ε c (Fstat (N := N) ψ)) 0) := by
  have e : configLift (fun _ => Fe ε c (Fstat (N := N) ψ)) 0 =
      fun Y : Fin N → Euc d => (∏ p ∈ pairsN N, Th ε (Y p.1 - Y p.2)) *
        (Fstat ψ (fun i => Torus.mk (Y i)) - c) := by
    funext Y
    unfold configLift Fe
    show chi ε (fun i => Torus.mk (Y i)) * _ = _
    rw [domp_chi_lift]
  rw [e, contDiff_iff_contDiffAt]
  intro Y
  by_cases hY : ∀ a b : Fin N, a ≠ b → Torus.mk (Y a) ≠ Torus.mk (Y b)
  · exact ((domp_contDiff_chi_lift ε).contDiffAt).mul
      ((domp_contDiffAt_Fstat_lift hsm Y hY).sub contDiffAt_const)
  · push Not at hY
    obtain ⟨a, b, hab, hmk⟩ := hY
    have hs0 : sE (Y a - Y b) < ε := by
      have : sE (Y a - Y b) = 0 := by
        rw [← domp_sT_mk, Q84a.q84a_mk_sub, hmk, sub_self, domp_sT_zero]
      rw [this]; exact hε
    have hz := domp_chi_lift_eventually_zero hε hab hs0
    refine contDiffAt_const.congr_of_eventuallyEq (f := fun _ => (0 : ℝ)) ?_
    filter_upwards [hz] with Z hZ
    simp [hZ]

/-- The compact set `{∀ a ≠ b, ε ≤ sT(x_a - x_b)}`. -/
def Kset (ε : ℝ) (d N : ℕ) : Set (Config d N) := {X | ∀ a b : Fin N, a ≠ b → ε ≤ sT (X a - X b)}

theorem domp_isCompact_Kset (ε : ℝ) : IsCompact (Kset ε d N) := by
  have hc : IsClosed (Kset ε d N) := by
    have : Kset ε d N = ⋂ a : Fin N, ⋂ b : Fin N, ⋂ (_ : a ≠ b), {X | ε ≤ sT (X a - X b)} := by
      ext X; simp [Kset]
    rw [this]
    refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ => ?_
    exact isClosed_le continuous_const
      (domp_continuous_sT.comp ((continuous_apply a).sub (continuous_apply b)))
  exact hc.isCompact

theorem domp_Kset_disjoint {ε : ℝ} (hε : 0 < ε) : Disjoint (Kset ε d N) (collisionSet d N) := by
  rw [Set.disjoint_left]
  rintro X hK ⟨a, b, hab, hX⟩
  have := hK a b hab
  rw [hX, sub_self, domp_sT_zero] at this
  linarith

theorem domp_Fe_zero_outside {ε : ℝ} (hε : 0 < ε) (c : ℝ) (F : Config d N → ℝ) (X : Config d N)
    (hX : X ∉ Kset ε d N) : Fe ε c F X = 0 := by
  unfold Kset at hX
  simp only [Set.mem_setOf_eq, not_forall, not_le] at hX
  obtain ⟨a, b, hab, h⟩ := hX
  unfold Fe
  rw [domp_chi_eq_zero hε hab h.le, zero_mul]

end Smooth

end HRS.MD.DOMProof

end
