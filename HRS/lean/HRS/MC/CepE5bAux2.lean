import HRS.MC.CepE5bAux1

/-!
# Packet CEPE5B, auxiliary 2: the resolvent is `C¹` (inverse function theorem)

For the Yosida family `J`, `n > 0`: `Ψ_n(y) = y + n⁻¹ ∇Φ(y)` is `C¹` on the open alcove with invertible
derivative `1 + n⁻¹ H_y` and injective, `J_n = Ψ_n⁻¹`.  Hence `J_n` is `C¹`.
-/

open Set Filter Topology
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE5b

open HRS.MC.Cepa
open HRS.MC.CepE1 (cepe1_h1 cepe1_pairGrad cepe1_vec cepe1_inner_vec)

variable {N : ℕ} {a : ℝ} {J : ℝ → Ch N → Ch N}

/-- The principal force on the alcove. -/
abbrev e5b_pg (a : ℝ) (N : ℕ) : Ch N → Ch N := cepe1_pairGrad (cepe1_h1 a N)

theorem e5b_hasGradient_Phi (a : ℝ) {y : Ch N} (hy : y ∈ cep_Alcove N) :
    HasGradientAt (cep_chamberPot a N) (e5b_pg a N y) y :=
  HRS.MC.CepE4.e4_Phi_hasGradient fun k l hkl => ⟨(e5b_gap hy hkl).1, (e5b_gap hy hkl).2⟩

theorem e5b_force (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) (z : Ch N) :
    n • (z - J n z) = e5b_pg a N (J n z) := by
  rw [hJ.force n z hn]
  exact (e5b_hasGradient_Phi a (hJ.mem n z hn)).gradient

theorem e5b_monotone (ha : 0 ≤ a) {y y' : Ch N} (hy : y ∈ cep_Alcove N) (hy' : y' ∈ cep_Alcove N) :
    0 ≤ inner ℝ (e5b_pg a N y - e5b_pg a N y') (y - y') :=
  HRS.MC.CepE2.cepe2_monotone ha hy hy'

/-- The map whose inverse is the resolvent. -/
def e5b_Psi (a : ℝ) (N : ℕ) (n : ℝ) (y : Ch N) : Ch N := y + n⁻¹ • e5b_pg a N y

theorem e5b_Psi_J (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) (z : Ch N) :
    e5b_Psi a N n (J n z) = z := by
  unfold e5b_Psi
  rw [← e5b_force hJ hn z, smul_smul, inv_mul_cancel₀ hn.ne', one_smul]
  abel

theorem e5b_Psi_inj (ha : 0 ≤ a) {n : ℝ} (hn : 0 < n) {y y' : Ch N} (hy : y ∈ cep_Alcove N)
    (hy' : y' ∈ cep_Alcove N) (h : e5b_Psi a N n y = e5b_Psi a N n y') : y = y' := by
  have hm := e5b_monotone ha hy hy'
  have h1 : y - y' = -(n⁻¹ • (e5b_pg a N y - e5b_pg a N y')) := by
    unfold e5b_Psi at h
    have h2 : (y + n⁻¹ • e5b_pg a N y) - (y' + n⁻¹ • e5b_pg a N y') = 0 := sub_eq_zero.2 h
    calc y - y' = ((y + n⁻¹ • e5b_pg a N y) - (y' + n⁻¹ • e5b_pg a N y')) -
          n⁻¹ • (e5b_pg a N y - e5b_pg a N y') := by module
      _ = _ := by rw [h2]; simp
  have h3 : ‖y - y'‖ ^ 2 ≤ 0 := by
    have h4 : inner ℝ (y - y') (y - y') = -(n⁻¹ * inner ℝ (e5b_pg a N y - e5b_pg a N y') (y - y')) := by
      have := congrArg (fun x => inner ℝ x (y - y')) h1
      simpa [inner_neg_left, real_inner_smul_left] using this
    have : 0 ≤ n⁻¹ * inner ℝ (e5b_pg a N y - e5b_pg a N y') (y - y') :=
      mul_nonneg (inv_nonneg.2 hn.le) hm
    rw [← real_inner_self_eq_norm_sq, h4]
    linarith
  have : ‖y - y'‖ = 0 := by nlinarith [norm_nonneg (y - y')]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

theorem e5b_hasFDerivAt_Psi (a : ℝ) (n : ℝ) {y : Ch N} (hy : y ∈ cep_Alcove N) :
    HasFDerivAt (e5b_Psi a N n) (ContinuousLinearMap.id ℝ (Ch N) + n⁻¹ • e5b_Hop a N y) y :=
  (hasFDerivAt_id y).add ((e5b_hasFDerivAt_pg a hy).const_smul n⁻¹)

theorem e5b_A_apply (a : ℝ) (n : ℝ) (y u : Ch N) :
    (ContinuousLinearMap.id ℝ (Ch N) + n⁻¹ • e5b_Hop a N y) u = u + n⁻¹ • e5b_Hop a N y u := rfl

theorem e5b_A_inj (ha : 0 ≤ a) {n : ℝ} (hn : 0 < n) (y : Ch N) :
    Function.Injective (ContinuousLinearMap.id ℝ (Ch N) + n⁻¹ • e5b_Hop a N y) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  rw [e5b_A_apply] at hu
  have h1 : inner ℝ (u + n⁻¹ • e5b_Hop a N y u) u = 0 := by rw [hu]; simp
  rw [inner_add_left, real_inner_smul_left, e5b_inner_Hop, real_inner_self_eq_norm_sq] at h1
  have h2 := e5b_hq_nonneg ha y u
  have h3 : 0 ≤ n⁻¹ * e5b_hq a N y u u := mul_nonneg (inv_nonneg.2 hn.le) h2
  have : ‖u‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖u‖]
  exact norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 this)

theorem e5b_contDiffAt_J (ha : 0 < a) (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) (z : Ch N) :
    ContDiffAt ℝ 1 (J n) z := by
  set y0 := J n z with hy0def
  have hy0 : y0 ∈ cep_Alcove N := hJ.mem n z hn
  have hΨ : ContDiffAt ℝ 1 (e5b_Psi a N n) y0 :=
    contDiffAt_id.add ((e5b_contDiffAt_pg a hy0).const_smul n⁻¹)
  set A : Ch N →L[ℝ] Ch N := ContinuousLinearMap.id ℝ (Ch N) + n⁻¹ • e5b_Hop a N y0 with hA
  have hinj := e5b_A_inj ha.le hn y0
  let e : Ch N ≃L[ℝ] Ch N :=
    LinearEquiv.toContinuousLinearEquiv (LinearEquiv.ofInjectiveEndo (A : Ch N →ₗ[ℝ] Ch N) hinj)
  have he : (e : Ch N →L[ℝ] Ch N) = A := by
    ext u
    rfl
  have hf' : HasFDerivAt (e5b_Psi a N n) (e : Ch N →L[ℝ] Ch N) y0 := by
    rw [he]; exact e5b_hasFDerivAt_Psi a n hy0
  have hn1 : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  have hstrict := hΨ.hasStrictFDerivAt' hf' hn1
  have hΨz : e5b_Psi a N n y0 = z := e5b_Psi_J hJ hn z
  have hL : ContDiffAt ℝ 1 (hΨ.localInverse hf' hn1) z := by
    have := hΨ.to_localInverse hf' hn1
    rwa [hΨz] at this
  have hLz : hΨ.localInverse hf' hn1 z = y0 := by
    have := hΨ.localInverse_apply_image hf' hn1
    rwa [hΨz] at this
  have hright : ∀ᶠ z' in 𝓝 z, e5b_Psi a N n (hΨ.localInverse hf' hn1 z') = z' := by
    have := hstrict.eventually_right_inverse
    rwa [hΨz] at this
  have hmem : ∀ᶠ z' in 𝓝 z, hΨ.localInverse hf' hn1 z' ∈ cep_Alcove N :=
    hL.continuousAt.eventually (HRS.MC.CepE2.cepe2_isOpen_alcove.mem_nhds (by rw [hLz]; exact hy0))
  refine hL.congr_of_eventuallyEq ?_
  filter_upwards [hright, hmem] with z' h1 h2
  refine (e5b_Psi_inj ha.le hn (hJ.mem n z' hn) h2 ?_)
  rw [e5b_Psi_J hJ hn z', h1]

theorem e5b_contDiff_J (ha : 0 < a) (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) :
    ContDiff ℝ 1 (J n) :=
  contDiff_iff_contDiffAt.2 fun z => e5b_contDiffAt_J ha hJ hn z

end HRS.MC.CepE5b
