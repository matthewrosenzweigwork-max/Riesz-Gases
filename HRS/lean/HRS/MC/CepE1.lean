import HRS.MC.CepE1Aux5
import HRS.Appendix.CepaFlow

/-!
# Packet CEPE1: the drift in chamber coordinates (`cep_E1_chamber_drift`)

`HRS.MC.CepE1.cep_E1_chamber_drift_proof` has the statement of `HRS.MC.Cepa.cep_E1_chamber_drift`
(the duplicated vocabulary `Ch`, `cep_IsC11`, `cep_StrictlyOrdered`, `cep_chamberPot`, `cep_toCh`, `cep_rank`
unfolds to the same bodies).  `Ψ(z) = (a/N) ∑_{k<l} r(z_l - z_k) + ∑_k V(z_k)` where `r' = ρ` is the primitive of the
smooth remainder of K1, normalised so that `g(u) = -log(2 sin πu) + r(u)` on `(0,1)`.
-/

open Set
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE1

open HRS HRS.MC.CepK1


variable {N : ℕ}

theorem cepe1_inner_single (k : Fin N) (z : Ch N) :
    inner ℝ (EuclideanSpace.single k (1 : ℝ)) z = z k := by
  simp [EuclideanSpace.inner_single_left]

/-- The pair potential with profile `(a/N) r` plus the one-body potential. -/
def cepe1_Psi (a : ℝ) (N : ℕ) (r Vt : ℝ → ℝ) (z : Ch N) : ℝ :=
  cepe1_pair (fun u => (a / N) * r u) z + ∑ k, Vt (z k)

/-- Its gradient. -/
def cepe1_PsiGrad (a : ℝ) (N : ℕ) (Vt' : ℝ → ℝ) (z : Ch N) : Ch N :=
  cepe1_pairGrad (cepe1_h2 a N) z + ∑ k, Vt' (z k) • EuclideanSpace.single k (1 : ℝ)

theorem cepe1_Psi_hasGradient {a : ℝ} {r Vt Vt' : ℝ → ℝ} (hr : ∀ u, HasDerivAt r (cepk1_ρ u) u)
    (hV : ∀ u, HasDerivAt Vt (Vt' u) u) (z : Ch N) :
    HasGradientAt (cepe1_Psi a N r Vt) (cepe1_PsiGrad a N Vt' z) z := by
  refine cepe1_hasGradientAt_add (cepe1_hasGradientAt_pair (h := fun u => (a / N) * r u)
    (h' := cepe1_h2 a N) (z := z) fun k l _ => (hr _).const_mul _) ?_
  refine cepe1_hasGradientAt_sum Finset.univ fun k _ => ?_
  have := cepe1_hasGradientAt_term (h := Vt) (c := Vt' (z k)) (EuclideanSpace.single k (1 : ℝ)) z
    (by rw [cepe1_inner_single]; exact hV _)
  simpa only [cepe1_inner_single] using this

theorem cepe1_Psi_lip {a : ℝ} {Vt' : ℝ → ℝ} {Lρ LV : ℝ≥0} (hρ : LipschitzWith Lρ cepk1_ρ)
    (hV : LipschitzWith LV Vt') : ∃ K : ℝ≥0, LipschitzWith K (cepe1_PsiGrad a N Vt') := by
  obtain ⟨K1, hK1⟩ := cepe1_lip_pairGrad (N := N) (cepe1_lip_const_mul hρ (a / N))
  refine ⟨K1 + ∑ k : Fin N, LV * ‖EuclideanSpace.single k (1 : ℝ)‖₊ * ‖EuclideanSpace.single k (1 : ℝ)‖₊, ?_⟩
  have h2 : LipschitzWith (∑ k : Fin N, LV * ‖EuclideanSpace.single k (1 : ℝ)‖₊ *
      ‖EuclideanSpace.single k (1 : ℝ)‖₊)
      (fun z : Ch N => ∑ k, Vt' (z k) • EuclideanSpace.single k (1 : ℝ)) := by
    refine cepe1_lip_sum Finset.univ _ _ fun k _ => ?_
    have := cepe1_lip_term hV (EuclideanSpace.single k (1 : ℝ))
    simpa only [cepe1_inner_single] using this
  exact hK1.add h2

theorem cepe1_Psi_contDiff {a : ℝ} {r Vt : ℝ → ℝ} (hr : ContDiff ℝ 1 r) (hV : ContDiff ℝ 1 Vt) :
    ContDiff ℝ 1 (cepe1_Psi a N r Vt) := by
  unfold cepe1_Psi
  refine (cepe1_contDiff_pair (contDiff_const.mul hr)).add ?_
  exact ContDiff.sum fun k _ => hV.comp (EuclideanSpace.proj k : Ch N →L[ℝ] ℝ).contDiff

theorem cepe1_Psi_periodic {a : ℝ} {r Vt : ℝ → ℝ} (hV : ∀ u, Vt (u + 1) = Vt u) (z : Ch N) :
    cepe1_Psi a N r Vt (z + WithLp.toLp 2 fun _ : Fin N => (1 : ℝ)) = cepe1_Psi a N r Vt z := by
  unfold cepe1_Psi cepe1_pair
  simp [hV]

theorem cepe1_chamberPot_eq (a : ℝ) (N : ℕ) :
    cep_chamberPot a N = cepe1_pair (fun u => (a / N) * (-Real.log (2 * Real.sin (Real.pi * u)))) := by
  funext z
  unfold cep_chamberPot cepe1_pair
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

theorem cepe1_Phi_hasGradient {a : ℝ} {N : ℕ} {z : Ch N}
    (hz : ∀ k l : Fin N, k < l → 0 < z l - z k ∧ z l - z k < 1) :
    HasGradientAt (cep_chamberPot a N) (cepe1_pairGrad (cepe1_h1 a N) z) z := by
  rw [cepe1_chamberPot_eq]
  refine cepe1_hasGradientAt_pair fun k l hkl => ?_
  exact (cepe1_hasDerivAt_neglog (hz k l hkl)).const_mul _

theorem cepe1_potential {D : DynData 1} (hs : D.s = 0) {r : ℝ → ℝ}
    (hrker : ∀ u ∈ Ioo (0 : ℝ) 1,
      periodicRiesz 1 0 (Torus.mk (cepk1_ι u)) = -Real.log (2 * Real.sin (Real.pi * u)) + r u)
    {π : Equiv.Perm (Fin N)} {y : Fin N → Euc 1} (hso : cep_StrictlyOrdered π y) :
    totalPotential D (fun i => Torus.mk (y i)) = cep_chamberPot 1 N (cep_toCh π y) +
      cepe1_Psi 1 N r (fun u => Torus.lift D.V (cepk1_ι u)) (cep_toCh π y) := by
  set z : Fin N → ℝ := fun l => y (π l) 0 with hz
  set P : Fin N → Fin N → ℝ := fun k l =>
    periodicRiesz 1 0 (Torus.mk (y (π k)) - Torus.mk (y (π l))) with hP
  have hι : ∀ l, cepk1_ι (z l) = y (π l) := fun l => by
    ext j
    have : j = 0 := Subsingleton.elim _ _
    subst this
    simp [cepk1_ι, hz]
  have hPsymm : ∀ k l, P k l = P l k := fun k l => by
    simp only [hP]
    rw [← periodicRiesz_neg, neg_sub]
  have hPval : ∀ k l, k < l → P k l = -Real.log (2 * Real.sin (Real.pi * (z l - z k))) + r (z l - z k) := by
    intro k l hkl
    rw [hPsymm]
    simp only [hP]
    have := hrker (z l - z k) (cepe1_diff hso hkl)
    rw [← this, cepe1_sub_mk]
    congr 2
    rw [← hι l, ← hι k]
    ext j
    have : j = 0 := Subsingleton.elim _ _
    subst this
    simp [cepk1_ι]
  have hF : ∑ i, ∑ j ∈ Finset.univ.erase i, periodicRiesz 1 D.s (Torus.mk (y i) - Torus.mk (y j)) =
      ∑ k, ∑ l ∈ Finset.univ.erase k, P k l := by
    rw [← Equiv.sum_comp π]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hs]
    exact (Finset.sum_equiv π (by simp) fun l _ => rfl).symm
  have hsplit : ∑ k, ∑ l ∈ Finset.univ.erase k, P k l =
      2 * ∑ k, ∑ l, if k < l then P k l else 0 := by
    simp only [cepe1_sum_erase_split, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun k l => if l < k then P k l else 0)]
    have : ∑ y_1, ∑ x, (if y_1 < x then P x y_1 else 0) = ∑ k, ∑ l, if k < l then P k l else 0 := by
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      by_cases h : k < l
      · simp [h, hPsymm k l]
      · simp [h]
    rw [this]
    ring
  have hV : ∑ i, D.V (Torus.mk (y i)) = ∑ k, Torus.lift D.V (cepk1_ι (z k)) := by
    rw [← Equiv.sum_comp π]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hι]
    rfl
  have hq : ∑ k, ∑ l, (if k < l then P k l else 0) =
      ∑ k, ∑ l, (if k < l then -Real.log (2 * Real.sin (Real.pi * (z l - z k))) else 0) +
      ∑ k, ∑ l, (if k < l then r (z l - z k) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h : k < l
    · simp [h, hPval k l h]
    · simp [h]
  have hch : cep_chamberPot 1 N (cep_toCh π y) = (1 / (N : ℝ)) *
      ∑ k, ∑ l, (if k < l then -Real.log (2 * Real.sin (Real.pi * (z l - z k))) else 0) := rfl
  have hps : cepe1_Psi 1 N r (fun u => Torus.lift D.V (cepk1_ι u)) (cep_toCh π y) =
      (1 / (N : ℝ)) * ∑ k, ∑ l, (if k < l then r (z l - z k) else 0) +
        ∑ k, Torus.lift D.V (cepk1_ι (z k)) := by
    unfold cepe1_Psi cepe1_pair
    rw [Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h : k < l
    · simp only [h, ite_true]; rfl
    · simp [h]
  unfold totalPotential
  rw [hF, hsplit, hV, hq, hch, hps]
  ring

theorem cep_E1_chamber_drift_proof {D : DynData 1} (hs : D.s = 0) {a : ℝ} (ha : 0 ≤ a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hV : cep_IsC11 D.V) (N : ℕ) :
    ∃ (Ψ : Ch N → ℝ) (L : ℝ≥0), ContDiff ℝ 1 Ψ ∧ LipschitzWith L (gradient Ψ) ∧
      (∀ z, Ψ (z + WithLp.toLp 2 fun _ : Fin N => (1 : ℝ)) = Ψ z) ∧
      (∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y → ∀ k : Fin N,
        liftedDrift D y (π k) 0 =
          -(gradient (cep_chamberPot a N) (cep_toCh π y)) k - (gradient Ψ (cep_toCh π y)) k) ∧
      (a = 1 → ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y →
        totalPotential D (fun i => Torus.mk (y i)) = cep_chamberPot 1 N (cep_toCh π y) + Ψ (cep_toCh π y)) := by
  classical
  obtain ⟨r, hrc, hrd, hrker⟩ := cepe1_kernel
  obtain ⟨Lρ, hρ⟩ := cepe1_ρ_lip
  obtain ⟨h1, LV, hLV⟩ := hV
  obtain ⟨hVc, hVd, hVl⟩ := cepe1_V h1 hLV
  have hVper : ∀ u : ℝ, Torus.lift D.V (cepk1_ι (u + 1)) = Torus.lift D.V (cepk1_ι u) := fun u => by
    simp only [Torus.lift, Function.comp]
    rw [cepk1_mk_add_one]
  obtain ⟨K, hK⟩ := cepe1_Psi_lip (a := a) (N := N) hρ hVl
  have hgrad : ∀ z, gradient (cepe1_Psi a N r (fun u => Torus.lift D.V (cepk1_ι u))) z =
      cepe1_PsiGrad a N (fun u => (gradient (Torus.lift D.V) (cepk1_ι u)) 0) z :=
    fun z => (cepe1_Psi_hasGradient hrd hVd z).gradient
  refine ⟨cepe1_Psi a N r (fun u => Torus.lift D.V (cepk1_ι u)), K, cepe1_Psi_contDiff hrc hVc, ?_,
    fun z => cepe1_Psi_periodic hVper z, ?_, ?_⟩
  · have : gradient (cepe1_Psi a N r (fun u => Torus.lift D.V (cepk1_ι u))) =
        cepe1_PsiGrad a N (fun u => (gradient (Torus.lift D.V) (cepk1_ι u)) 0) := funext hgrad
    rw [this]; exact hK
  · intro π y hso k
    have hz : ∀ k l : Fin N, k < l →
        0 < (cep_toCh π y) l - (cep_toCh π y) k ∧ (cep_toCh π y) l - (cep_toCh π y) k < 1 :=
      fun k l hkl => cepe1_diff hso hkl
    rw [(cepe1_Phi_hasGradient hz).gradient, hgrad, cepe1_drift_core hs hM hso k]
    simp only [cepe1_PsiGrad, WithLp.ofLp_add, Pi.add_apply, WithLp.ofLp_sum, Finset.sum_apply,
      WithLp.ofLp_smul, Pi.smul_apply, EuclideanSpace.single_apply, smul_eq_mul]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  · intro ha1 π y hso
    subst ha1
    exact cepe1_potential hs hrker hso

end HRS.MC.CepE1
