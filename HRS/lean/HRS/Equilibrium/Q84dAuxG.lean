/-
# HRS.Equilibrium.Q84dAuxG — packet Q84d: a.e. measurability of `∇ψ`, `B_ψ`, `T_ψ`, `G_ψ` on `Config`
-/
import HRS.Equilibrium.Q84dAuxF
import HRS.Equilibrium.Q84aEstimates

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q84d_aesm_swap {F : Torus d → Torus d → ℝ}
    (hF : AEStronglyMeasurable (fun p : Torus d × Torus d => F p.1 p.2) volume) :
    AEStronglyMeasurable (fun p : Torus d × Torus d => F p.2 p.1) volume := by
  have h : MeasurePreserving (Prod.swap : Torus d × Torus d → Torus d × Torus d) volume volume := by
    rw [Measure.volume_eq_prod]
    exact Measure.measurePreserving_swap
  exact hF.comp_quasiMeasurePreserving h.quasiMeasurePreserving

theorem q84d_aesm_of_ae_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hg : Measurable g) (h : ∀ᵐ a ∂μ, f a = g a) : AEStronglyMeasurable f μ :=
  hg.aestronglyMeasurable.congr (h.mono fun _ h => h.symm)

/-- `∂_{x_m}ψ(x,y)` is a.e. jointly measurable. -/
theorem q84d_aesm_gradFst {ψ : Torus d → Torus d → ℝ}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) (hd : 1 ≤ d) (m : Fin d) :
    AEStronglyMeasurable (fun p : Torus d × Torus d => (gradFst ψ p.1 p.2) m) volume := by
  refine q84d_aesm_of_ae_eq (q84d_measurable_gK ψ m) ?_
  filter_upwards [q84d_ae_ne_diag hd] with p hp
  exact q84d_grad_comp hsm hp m

theorem q84d_aesm_gradSnd {ψ : Torus d → Torus d → ℝ} (hsymm : IsSymmPair ψ)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) (hd : 1 ≤ d) (m : Fin d) :
    AEStronglyMeasurable (fun p : Torus d × Torus d => (gradSnd ψ p.1 p.2) m) volume := by
  have h := q84d_aesm_swap (F := fun x y => (gradFst ψ x y) m) (q84d_aesm_gradFst hsm hd m)
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Q84a.q84a_gradSnd_eq hsymm]

theorem q84d_aesm_inner {α : Type*} [MeasurableSpace α] {μ : Measure α} {u v : α → Euc d}
    (hu : ∀ m, AEStronglyMeasurable (fun a => u a m) μ)
    (hv : ∀ m, AEStronglyMeasurable (fun a => v a m) μ) :
    AEStronglyMeasurable (fun a => inner ℝ (u a) (v a)) μ := by
  simp only [PiLp.inner_apply]
  refine Finset.aestronglyMeasurable_fun_sum _ fun m _ => ?_
  have e : (fun a => inner ℝ (u a m) (v a m)) = fun a => (v a m) * (u a m) := by
    funext a; simp
  rw [e]
  exact (hv m).mul (hu m)

theorem q84d_measurable_centeredForce (hsd : s < d) (ρ : Torus d → ℝ) (m : Fin d) :
    Measurable (fun p : Torus d × Torus d => (centeredForce d s ρ p.1 p.2) m) := by
  have h1 : Measurable (fun p : Torus d × Torus d => periodicRieszGrad d s (p.1 - p.2)) :=
    (KernelGrad.measurable_periodicRieszGrad hsd).comp (measurable_fst.sub measurable_snd)
  have h2 : Measurable (fun p : Torus d × Torus d => forceField d s ρ p.1) :=
    (q84d_measurable_grad _).comp measurable_fst
  have h3 : Measurable (fun p : Torus d × Torus d => periodicRieszGrad d s (p.1 - p.2) - forceField d s ρ p.1) :=
    h1.sub h2
  exact (EuclideanSpace.proj m).continuous.measurable.comp h3

/-- `B_ψ` is a.e. jointly measurable. -/
theorem q84d_aesm_Bpsi (hsd : s < d) {ρ : Torus d → ℝ} {ψ : Torus d → Torus d → ℝ}
    (hsymm : IsSymmPair ψ) (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d))
    (hd : 1 ≤ d) :
    AEStronglyMeasurable (fun p : Torus d × Torus d => Bpsi d s ρ ψ p.1 p.2) volume := by
  have hg1 := q84d_aesm_gradFst hsm hd
  have hg2 := q84d_aesm_gradSnd hsymm hsm hd
  have hgrav : ∀ m, AEStronglyMeasurable
      (fun p : Torus d × Torus d => (periodicRieszGrad d s (p.1 - p.2)) m) volume := fun m =>
    ((EuclideanSpace.proj m).continuous.measurable.comp
      ((KernelGrad.measurable_periodicRieszGrad hsd).comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable
  have hF1 : ∀ m, AEStronglyMeasurable (fun p : Torus d × Torus d => (forceField d s ρ p.1) m) volume :=
    fun m => ((EuclideanSpace.proj m).continuous.measurable.comp
      ((q84d_measurable_grad _).comp measurable_fst)).aestronglyMeasurable
  have hF2 : ∀ m, AEStronglyMeasurable (fun p : Torus d × Torus d => (forceField d s ρ p.2) m) volume :=
    fun m => ((EuclideanSpace.proj m).continuous.measurable.comp
      ((q84d_measurable_grad _).comp measurable_snd)).aestronglyMeasurable
  unfold Bpsi Vpsi
  refine AEStronglyMeasurable.sub ?_ (AEStronglyMeasurable.const_mul (AEStronglyMeasurable.add ?_ ?_) 2)
  · exact q84d_aesm_inner hgrav fun m => (hg1 m).sub (hg2 m)
  · exact q84d_aesm_inner hF1 hg1
  · exact q84d_aesm_inner hF2 hg2

section Cfg

variable {ρ : Torus d → ℝ} {ψ : Torus d → Torus d → ℝ}

theorem q84d_aesm_Tpsi (hsd : s < d) (hsymm : IsSymmPair ψ)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) (hd : 1 ≤ d)
    {a b c : Fin N} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    AEStronglyMeasurable (fun X : Config d N => Tpsi d s ρ ψ (X a) (X b) (X c)) volume := by
  have hK : ∀ m (u v : Fin N), u ≠ v → AEStronglyMeasurable
      (fun X : Config d N => (centeredForce d s ρ (X u) (X v)) m) volume := fun m u v huv =>
    q84d_aesm_pair (b := fun x z => (centeredForce d s ρ x z) m)
      (q84d_measurable_centeredForce hsd ρ m).aestronglyMeasurable huv
  have hG1 : ∀ m (u v : Fin N), u ≠ v → AEStronglyMeasurable
      (fun X : Config d N => (gradFst ψ (X u) (X v)) m) volume := fun m u v huv =>
    q84d_aesm_pair (b := fun x y => (gradFst ψ x y) m) (q84d_aesm_gradFst hsm hd m) huv
  have hG2 : ∀ m (u v : Fin N), u ≠ v → AEStronglyMeasurable
      (fun X : Config d N => (gradSnd ψ (X u) (X v)) m) volume := fun m u v huv =>
    q84d_aesm_pair (b := fun x y => (gradSnd ψ x y) m) (q84d_aesm_gradSnd hsymm hsm hd m) huv
  unfold Tpsi
  refine AEStronglyMeasurable.sub (AEStronglyMeasurable.neg ?_) ?_
  · exact q84d_aesm_inner (fun m => hK m a c hac) (fun m => hG1 m a b hab)
  · exact q84d_aesm_inner (fun m => hK m b c hbc) (fun m => hG2 m a b hab)

theorem q84d_aesm_Gpsi (hd : 1 ≤ d) (hsd : s < d) (hsymm : IsSymmPair ψ)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d))
    (hJ : AEStronglyMeasurable (fun p : Torus d × Torus d => Jpair d s ρ ψ p.1 p.2) volume)
    {i j k : Fin N} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    AEStronglyMeasurable (fun X : Config d N => Gpsi d s ρ ψ (X i) (X j) (X k)) volume := by
  have T1 := q84d_aesm_Tpsi (N := N) (ρ := ρ) hsd hsymm hsm hd hij hik hjk
  have T2 := q84d_aesm_Tpsi (N := N) (ρ := ρ) hsd hsymm hsm hd hik hij hjk.symm
  have T3 := q84d_aesm_Tpsi (N := N) (ρ := ρ) hsd hsymm hsm hd hjk hij.symm hik.symm
  have J1 := q84d_aesm_pair (N := N) hJ hij
  have J2 := q84d_aesm_pair (N := N) hJ hik
  have J3 := q84d_aesm_pair (N := N) hJ hjk
  unfold Gpsi
  exact ((T1.add T2).add T3).const_mul (1 / 3) |>.sub (((J1.add J2).add J3).const_mul (1 / 3))

end Cfg

end HRS.Q84d

end
