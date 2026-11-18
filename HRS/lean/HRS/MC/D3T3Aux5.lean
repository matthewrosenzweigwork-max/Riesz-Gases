import HRS.MC.D3T3Aux4

/-!
# Packet D3T3, auxiliary facts: `g_λ = H_λ - const` on the torus.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform

namespace HRS.MC.D3T3

open HRS HRS.MC.FDLE HRS.MC.Per HRS.MC.D3T1

variable {d : ℕ}

lemma d3f_int_kap {s : ℝ} (hsd : s < d) (b : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    ∫ t in Ioc 0 lam, kap d s b t = b * (lam ^ ((d : ℝ) - s) / ((d : ℝ) - s)) := by
  have hr1 : (d : ℝ) - s - 1 + 1 = (d : ℝ) - s := by ring
  have hcongr : ∫ t in Ioc 0 lam, kap d s b t = ∫ t in Ioc 0 lam, b * t ^ ((d : ℝ) - s - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    simp only [kap]
    rw [Real.rpow_sub_one ht.1.ne']
  rw [hcongr, ← intervalIntegral.integral_of_le hlam.le, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith)), hr1,
    Real.zero_rpow (by linarith), sub_zero]

lemma d3f_rep_ne (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {lam : ℝ} (hlam : 0 < lam)
    {x : Torus d} (hx : x ≠ 0) :
    periodicRiesz d s x - fdlWT ψ s b lam x =
      Hs ψ s b lam x - b * (∫ y, fdlPhi ψ y) * (lam ^ ((d : ℝ) - s) / ((d : ℝ) - s)) := by
  have hb0 : 0 < b := hb.1
  set c : ℝ := ∫ y, fdlPhi ψ y with hc
  obtain ⟨hTint, hg⟩ := hb.2.2.2 x hx
  set T : ℝ → ℝ := fun t => t ^ ((d : ℝ) - s) * (fdlPer (fdlPhiScale ψ t) x - c) / t with hT
  set F : ℝ → ℝ := fun t => t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) x / t with hF
  have hFint : IntegrableOn F (Ioc 0 lam) := d3t_F_integrable hsd hb hx hlam
  have hkint : IntegrableOn (kap d s 1) (Ioc 0 lam) := d3f_kap_integrableOn hsd 1 hlam
  have hsplit : ∫ t in Ioi (0 : ℝ), T t = (∫ t in Ioc 0 lam, T t) + ∫ t in Ioi lam, T t := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hTint.mono_set (fun t ht => ht.1)) (hTint.mono_set (fun t ht => lt_trans hlam ht))]
    rw [Ioc_union_Ioi_eq_Ioi hlam.le]
  have hTF : ∀ t ∈ Ioc 0 lam, T t = F t - c * kap d s 1 t := by
    intro t ht
    simp only [hT, hF, kap]
    ring
  have hIoc : ∫ t in Ioc 0 lam, T t = (∫ t in Ioc 0 lam, F t) - c * (lam ^ ((d : ℝ) - s) / ((d : ℝ) - s)) := by
    rw [setIntegral_congr_fun measurableSet_Ioc hTF, integral_sub hFint (hkint.const_mul c),
      integral_const_mul, d3f_int_kap hsd 1 hlam, one_mul]
  have hHs : Hs ψ s b lam x = b * ∫ t in Ioi lam, T t := by
    unfold Hs
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := lt_trans hlam ht
    simp only [hT, kap]
    rw [d3f_perJ_eq hψ ht0]
    ring
  have hW : fdlWT ψ s b lam x = b * ∫ t in Ioc 0 lam, F t := rfl
  rw [hg, hsplit, hIoc, hHs, hW]
  ring


lemma d3f_truncT_eq (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {lam : ℝ} (hlam : 0 < lam) :
    fdlTruncT ψ s b lam =
      fun x => Hs ψ s b lam x - b * (∫ y, fdlPhi ψ y) * (lam ^ ((d : ℝ) - s) / ((d : ℝ) - s)) := by
  funext x
  by_cases hx : x = 0
  · subst hx
    have hcont : Continuous (fun x : Torus d =>
        Hs ψ s b lam x - b * (∫ y, fdlPhi ψ y) * (lam ^ ((d : ℝ) - s) / ((d : ℝ) - s))) :=
      (d3f_Hs_continuous hd hs0 hψ hb.1 hlam).sub continuous_const
    haveI := d3f_nebot hd
    unfold fdlTruncT
    rw [if_pos rfl]
    have hev : (fun x' : Torus d => periodicRiesz d s x' - fdlWT ψ s b lam x') =ᶠ[𝓝[≠] (0 : Torus d)]
        fun x => Hs ψ s b lam x - b * (∫ y, fdlPhi ψ y) * (lam ^ ((d : ℝ) - s) / ((d : ℝ) - s)) := by
      filter_upwards [self_mem_nhdsWithin] with x' hx'
      exact d3f_rep_ne hd hs0 hsd hψ hb hlam hx'
    have ht : Tendsto (fun x' : Torus d => periodicRiesz d s x' - fdlWT ψ s b lam x')
        (𝓝[≠] (0 : Torus d)) (𝓝 (Hs ψ s b lam 0 - b * (∫ y, fdlPhi ψ y) *
          (lam ^ ((d : ℝ) - s) / ((d : ℝ) - s)))) :=
      ((hcont.tendsto 0).mono_left nhdsWithin_le_nhds).congr' hev.symm
    exact ht.limUnder_eq
  · unfold fdlTruncT
    rw [if_neg hx]
    exact d3f_rep_ne hd hs0 hsd hψ hb hlam hx

lemma d3f_fcoef_Hs (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {lam : ℝ} (hlam : 0 < lam)
    (k : Lattice d) :
    Torus.fcoef (Hs ψ s b lam) k = if k = 0 then 0 else ((fdlGhat ψ s b lam k : ℝ) : ℂ) := by
  have hb0 : 0 < b := hb.1
  have h1 := d3f_fubini (ψ := ψ) k (S := Ioi lam) (kap d s b) (∫ y, fdlPhi ψ y)
    (d3f_int_b hd hs0 hψ k hb0 hlam)
  have hH : Hs ψ s b lam = fun x => ∫ t in Ioi lam, kap d s b t * (perJ ψ (x, t) - ∫ y, fdlPhi ψ y) :=
    rfl
  rw [hH, h1]
  have hco : ∀ t ∈ Ioi lam, ((kap d s b t : ℝ) : ℂ) *
      Torus.fcoef (fun x => perJ ψ (x, t) - ∫ y, fdlPhi ψ y) k =
      ((kap d s b t : ℝ) : ℂ) * (if k = 0 then 0 else
        ((fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 : ℝ) : ℂ)) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hlam ht
    have hf : (fun x : Torus d => perJ ψ (x, t) - ∫ y, fdlPhi ψ y) = perQ ψ t :=
      funext fun x => by rw [d3f_perJ_eq hψ ht0]; rfl
    rw [hf, per_fcoef_Q hd hψ ht0 k]
  rw [setIntegral_congr_fun measurableSet_Ioi hco]
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, if_false]
    have hint := d3f_int_psi hψ hs0 hlam hk
    have key : ∀ f : ℝ → ℝ, ((∫ t in Ioi lam, f t : ℝ) : ℂ) = ∫ t in Ioi lam, (f t : ℂ) :=
      fun f => integral_ofReal.symm
    unfold fdlGhat
    rw [← integral_const_mul, key]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [kap]
    push_cast
    ring


lemma d3f_fcoef_trunc (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {lam : ℝ} (hlam : 0 < lam)
    {k : Lattice d} (hk : k ≠ 0) :
    Torus.fcoef (fdlTruncT ψ s b lam) k = ((fdlGhat ψ s b lam k : ℝ) : ℂ) := by
  rw [d3f_truncT_eq hd hs0 hsd hψ hb hlam]
  have hcont := d3f_Hs_continuous hd hs0 hψ hb.1 hlam
  rw [HRS.MC.Per.per_fcoef_sub_const hcont, d3f_fcoef_Hs hd hs0 hsd hψ hb hlam k]
  simp [hk]

end HRS.MC.D3T3
