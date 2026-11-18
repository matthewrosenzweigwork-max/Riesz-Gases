import HRS.MC.SEdgeVocab
import HRS.MC.SEdgeB9sym
import HRS.PDE.MeanFieldPairInverse

/-!
# Packet B11a: the covariance matrix `C_ab = mu(phi_a r_b)` is positive semidefinite
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B11a

open HRS.Sec7 HRS.MC.SEdge HRS.MC.SEdge.B9sym

variable {d : ℕ} {s : ℝ}

theorem b11_sd (hd : 2 ≤ d) (hs : s < (d : ℝ) / 2) : s < d := by
  have : (0 : ℝ) ≤ d := by positivity
  linarith

theorem b11_resp_ae (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {r : Torus d → ℝ}
    (hr : IsResponse (periodicRiesz d s) (withDensityReal ρ) β φ r) :
    responseInverse (periodicRiesz d s) (withDensityReal ρ) β φ =ᵐ[withDensityReal ρ] r := by
  have hsd := b11_sd hd hs
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨Λ, hΛ⟩ := Q66.q66_bound_of_smooth hρ.smooth
  have hφc : Continuous φ := Q66.q66_cont_of_smooth hφ
  have hφL2 : MemLp φ 2 (withDensityReal ρ) :=
    hφc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨h, hh, huniq⟩ := exists_unique_response hd hs0 hsd ρ hρ.density Λ
    (fun x => (le_abs_self _).trans (hΛ x)) β hβ φ hφL2
  have hex : ∃ h, IsResponse (periodicRiesz d s) (withDensityReal ρ) β φ h := ⟨h, hh⟩
  have h1 : IsResponse (periodicRiesz d s) (withDensityReal ρ) β φ
      (responseInverse (periodicRiesz d s) (withDensityReal ρ) β φ) := by
    unfold responseInverse
    rw [dif_pos hex]
    exact hex.choose_spec
  exact (huniq _ h1).trans (huniq _ hr).symm

/-- Additivity of `Kop` on continuous functions. -/
theorem b11_kop_add (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {f g : Torus d → ℝ} (hf : Continuous f)
    (hg : Continuous g) (x : Torus d) :
    Kop (periodicRiesz d s) (withDensityReal ρ) (fun y => f y + g y) x =
      Kop (periodicRiesz d s) (withDensityReal ρ) f x +
        Kop (periodicRiesz d s) (withDensityReal ρ) g x := by
  have hsd := b11_sd hd hs
  have hρc : Continuous ρ := Q66.q66_cont_of_smooth hρ.smooth
  have hgi := HRS.PDE.MFOneLe.integrable_periodicRiesz (by omega) s hs0 hsd
  have e : (fun y => f y + g y) = fun y => f y - (-1 * g y) := by funext y; ring
  have hng : Continuous fun y => -1 * g y := continuous_const.mul hg
  rw [e, HRS.PDE.MFPair.Kop_sub_fun hgi hρ.density hρc hf hng,
    HRS.PDE.MFPair.Kop_smul_fun hρ.density g (-1)]
  ring

theorem b11_kop_sum (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {ι : Type*} (S : Finset ι) (c : ι → ℝ)
    (f : ι → Torus d → ℝ) (hf : ∀ i, Continuous (f i)) (x : Torus d) :
    Kop (periodicRiesz d s) (withDensityReal ρ) (fun y => ∑ i ∈ S, c i * f i y) x =
      ∑ i ∈ S, c i * Kop (periodicRiesz d s) (withDensityReal ρ) (f i) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have := HRS.PDE.MFPair.Kop_smul_fun (s := s) hρ.density (fun _ => (0 : ℝ)) 0 x
    simpa using this
  | insert a S ha ih =>
    have e : (fun y => ∑ i ∈ insert a S, c i * f i y) =
        fun y => c a * f a y + ∑ i ∈ S, c i * f i y := by
      funext y; rw [Finset.sum_insert ha]
    have hc1 : Continuous fun y => c a * f a y := continuous_const.mul (hf a)
    have hc2 : Continuous fun y => ∑ i ∈ S, c i * f i y :=
      continuous_finsetSum _ fun i _ => continuous_const.mul (hf i)
    rw [e, b11_kop_add hd hs0 hs hρ hc1 hc2, ih, Finset.sum_insert ha,
      HRS.PDE.MFPair.Kop_smul_fun hρ.density (f a) (c a)]

theorem b11_l2_sum {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {n : ℕ} (x : Fin n → ℝ)
    (f g : Fin n → Torus d → ℝ) (hf : ∀ i, Continuous (f i)) (hg : ∀ i, Continuous (g i)) :
    l2Inner (withDensityReal ρ) (fun y => ∑ i, x i * f i y) (fun y => ∑ j, x j * g j y) =
      ∑ i, ∑ j, x i * x j * l2Inner (withDensityReal ρ) (f i) (g j) := by
  have hρc : Continuous ρ := Q66.q66_cont_of_smooth hρ.smooth
  have hm := HRS.PDE.MFAdjoint.l2Inner_mu hρ.density
  rw [hm]
  have e : ∀ y, ρ y * ((∑ i, x i * f i y) * ∑ j, x j * g j y) =
      ∑ i, ∑ j, x i * x j * (ρ y * (f i y * g j y)) := fun y => by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [e]
  have ci : ∀ i j, Continuous fun y => x i * x j * (ρ y * (f i y * g j y)) := fun i j =>
    continuous_const.mul (hρc.mul ((hf i).mul (hg j)))
  rw [integral_finsetSum _ (fun i _ => HRS.PDE.MFAdjoint.integrable_of_cont
    (continuous_finsetSum _ fun j _ => ci i j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => HRS.PDE.MFAdjoint.integrable_of_cont (ci i j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, hm]

theorem sed_B11a_cov_psd_proof (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ}
    (hβ : 0 ≤ β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {p : ℕ} {φ : Fin p → Torus d → ℝ}
    (hφ : ∀ a, Torus.IsSmooth (φ a)) : (sed_Cmat d s β ρ φ).PosSemidef := by
  have hsd := b11_sd hd hs
  have hρc : Continuous ρ := Q66.q66_cont_of_smooth hρ.smooth
  choose r hrs hrR hreq using fun a =>
    Q66.q66_response_regular hd hs0 hs β hβ hρ (hφ a)
  have hrc : ∀ a, Continuous (r a) := fun a => Q66.q66_cont_of_smooth (hrs a)
  have hφc : ∀ a, Continuous (φ a) := fun a => Q66.q66_cont_of_smooth (hφ a)
  have hr0 : ∀ a, pair (withDensityReal ρ) (r a) = 0 := fun a =>
    b9s_pair_resp hd hs0 hs hρ (hφc a) (hrc a) (hreq a)
  -- identification of the entries
  have hC : ∀ a b, sed_Cmat d s β ρ φ a b = l2Inner (withDensityReal ρ) (φ a) (r b) := by
    intro a b
    have hae := b11_resp_ae hd hs0 hs hβ hρ (hφ b) (hrR b)
    show ∫ x, φ a x * responseInverse (periodicRiesz d s) (withDensityReal ρ) β (φ b) x
      ∂(withDensityReal ρ) = _
    exact integral_congr_ae (hae.mono fun x hx => by simp only [hx])
  have hCs : ∀ a b, sed_Cmat d s β ρ φ a b = l2Inner (withDensityReal ρ) (r a) (r b) +
      β * l2Inner (withDensityReal ρ) (Kop (periodicRiesz d s) (withDensityReal ρ) (r a))
        (r b) := by
    intro a b
    rw [hC, ← b9s_l2_proj hρ (hφc a) (hrc b) (hr0 b)]
    exact b9s_l2_resp hd hs0 hs hρ (hrc a) (hrc b) (hreq a)
  refine ⟨?_, ?_⟩
  · refine Matrix.ext fun a b => ?_
    simp only [Matrix.conjTranspose_apply, star_trivial]
    rw [hC, hC]
    exact (b9s_part2 hd hs0 hs hρ (hφ b) (hφ a) (hrs b) (hrs a) (hreq b) (hreq a)).symm
  · intro x
    have hq : x.sum (fun i xi => x.sum fun j xj => star xi * sed_Cmat d s β ρ φ i j * xj) =
        ∑ i, ∑ j, x i * sed_Cmat d s β ρ φ i j * x j := by
      simp [Finsupp.sum_fintype]
    rw [hq]
    set R : Torus d → ℝ := fun y => ∑ i, x i * r i y with hR
    have hRc : Continuous R := continuous_finsetSum _ fun i _ => continuous_const.mul (hrc i)
    have hR0 : pair (withDensityReal ρ) R = 0 := by
      rw [HRS.PDE.MFAdjoint.pair_mu hρ.density]
      have ci : ∀ i, Continuous fun y => ρ y * (x i * r i y) := fun i =>
        hρc.mul (continuous_const.mul (hrc i))
      have : ∀ y, ρ y * R y = ∑ i, x i * (ρ y * r i y) := fun y => by
        simp only [hR]; rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      simp_rw [this]
      rw [integral_finsetSum (Finset.univ : Finset (Fin p))
        (f := fun i y => x i * (ρ y * r i y)) (fun i _ => HRS.PDE.MFAdjoint.integrable_of_cont
        (continuous_const.mul (hρc.mul (hrc i))))]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [integral_const_mul, ← HRS.PDE.MFAdjoint.pair_mu hρ.density, hr0 i, mul_zero]
    have hKR : ∀ y, Kop (periodicRiesz d s) (withDensityReal ρ) R y =
        ∑ i, x i * Kop (periodicRiesz d s) (withDensityReal ρ) (r i) y := fun y =>
      b11_kop_sum hd hs0 hs hρ Finset.univ x r hrc y
    have hKc : ∀ i, Continuous (Kop (periodicRiesz d s) (withDensityReal ρ) (r i)) := fun i =>
      b9s_cont_kop hd hs0 hs hρ (hrc i)
    have T1 := b11_l2_sum hρ x r r hrc hrc
    have T2 := b11_l2_sum hρ x (fun i => Kop (periodicRiesz d s) (withDensityReal ρ) (r i)) r hKc hrc
    have hKfun : (fun y => ∑ i, x i * Kop (periodicRiesz d s) (withDensityReal ρ) (r i) y) =
        Kop (periodicRiesz d s) (withDensityReal ρ) R := (funext hKR).symm
    rw [hKfun] at T2
    have P1 : 0 ≤ l2Inner (withDensityReal ρ) R R := by
      rw [HRS.PDE.MFAdjoint.l2Inner_mu hρ.density]
      exact integral_nonneg fun y => mul_nonneg (hρ.pos y).le (mul_self_nonneg _)
    have P2 := HRS.PDE.MFAdjoint.l2Inner_kop_nonneg' (by omega) s hs0 hsd ρ hρ.density hρc R hRc hR0
    have key : ∑ i, ∑ j, x i * sed_Cmat d s β ρ φ i j * x j =
        l2Inner (withDensityReal ρ) R R +
          β * l2Inner (withDensityReal ρ) (Kop (periodicRiesz d s) (withDensityReal ρ) R) R := by
      rw [show l2Inner (withDensityReal ρ) R R = _ from T1, T2, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hCs i j]; ring
    rw [key]
    exact add_nonneg P1 (mul_nonneg hβ P2)

end HRS.MC.SEdge.B11a


end
