import HRS.MS.S11Q3B1
import HRS.MS.S11Q2B1

/-!
# S11.3 / S11.4 (worker S11Q3), B2: the weak QREG core from a regular density family

`s11q3_QReg_of_Reg`: for a regular family `ρ_t` of probability densities (`s11q3_Reg`), `N ≥ 2`, `T > 0` and a compact collision-free `K`,
there are `q̃` of class `C^{1,2}` on `ℝ × ℝ^{Nd}` (`s113q_C12`), positive for `t ∈ [0,T+1]`, and an open `G' ⊇ J⁻¹K` with
`q̃(t,z) = q_N^t(Jz)` on `G'` for `t ∈ [0,T+1]` (`HRS.MS.S11Q2.s11q2_QReg`).
Construction: `q_N^t(Jz) = K̂(t)⁻¹ exp(-βN θ F0(Jz) + ∑_a (β Γ_t(x_a) + log ρ_t(x_a)))` on `θ = 1`, reflected past `t = 0`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S11Q3

open HRS HRS.Whole HRS.MS.MovForce HRS.MS.S113BD
open HRS.MC.CepP3 (Jc)
open HRS.MS.S113X2 HRS.MS.S113X2B HRS.MS.S113X2C

variable {d N : ℕ} {s : ℝ}

theorem s11q3_QReg_of_Reg (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ D : ℝ → Euc d → ℝ} {c B : ℝ} (R : s11q3_Reg d ρ D c B)
    (hprob : ∀ t, 0 ≤ t → HRS.Whole.IsProbDensity (ρ t)) (hN : 2 ≤ N) (T : ℝ)
    (K : Set (EucConfig d N)) (hK : IsCompact K) (hfree : ∀ x ∈ K, x ∉ eucCollisionSet d N) :
    ∃ (qt : ℝ → s113b_E (N * d) → ℝ) (G' : Set (s113b_E (N * d))),
      HRS.MS.S11Q2.s11q2_QReg d N s β ρ T K qt G' := by
  have hd1 : 1 ≤ d := by omega
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hKpos, hKc, hKc', hKd, -⟩ := s11q3_Khat_facts hd1 hs0 hsd R hβ hN1
  -- the cut-off
  set U : Set (s113b_E (N * d)) := {z | Jc d N z ∉ eucCollisionSet d N} with hU
  have hUo : IsOpen U := (s113a_isOpen_free d N).preimage (Jc d N).continuous
  set KE : Set (s113b_E (N * d)) := Jc d N ⁻¹' K with hKE
  have hKEc : IsCompact KE := ((Jc d N).toHomeomorph.isCompact_preimage).2 hK
  have hKEU : KE ⊆ U := fun z hz => hfree _ hz
  obtain ⟨θ, G, hθ, -, hθs, -, hGo, hKG, hθ1⟩ := s113c_cutoff hKEc hUo hKEU
  have hF0c := s11q3_F0c_contDiff (d := d) (s := s) (N := N) hθ hθs
  obtain ⟨G0, hG0⟩ : ∃ G0 : s113b_E (N * d) → ℝ, ∀ z, G0 z = (-β * N) * (θ z * s11q3_F0 d s N (Jc d N z)) :=
    ⟨_, fun _ => rfl⟩
  have hG0c : ContDiff ℝ 2 G0 := by
    have : G0 = fun z => (-β * N) * (θ z * s11q3_F0 d s N (Jc d N z)) := funext hG0
    rw [this]
    exact contDiff_const.mul hF0c
  obtain ⟨π, hπ⟩ : ∃ π : Fin N → s113b_E (N * d) →L[ℝ] Euc d, ∀ a z, π a z = Jc d N z a :=
    ⟨fun a => (ContinuousLinearMap.proj a : (Fin N → Euc d) →L[ℝ] Euc d).comp
      (Jc d N : s113b_E (N * d) →L[ℝ] (Fin N → Euc d)), fun a z => rfl⟩
  -- jets of the clamped family
  have jΓ := s11q3_Gam_jet hd1 hs0 hsd R
  have jρ := s11q3_rho_jet R
  have jlog := jρ.log (fun t x => R.pos _ (le_max_right t 0) x)
  have jA := (jΓ.smulT (κ := fun _ => β) continuous_const).add jlog
  have jS := (s11q3_Jet2.static hG0c).add (s11q3_Jet2.sum Finset.univ (fun a _ => jA.comp_clm (π a)))
  have hκ : Continuous fun t : ℝ => (s11q3_Khat d s β N ρ (max t 0))⁻¹ :=
    ((hKc.comp_continuous (continuous_id.max continuous_const)
      (fun t => Set.mem_Ici.2 (le_max_right t 0))).inv₀ (fun t => (hKpos _ (le_max_right t 0)).ne'))
  have jQ := (jS.exp).smulT hκ
  obtain ⟨Qb, hQb⟩ : ∃ Qb : ℝ → s113b_E (N * d) → ℝ, ∀ t z, Qb t z = (s11q3_Khat d s β N ρ (max t 0))⁻¹ *
      Real.exp (G0 z + ∑ a, (β * s11q3_Gam d s (ρ (max t 0)) (π a z) + Real.log (ρ (max t 0) (π a z)))) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨a1, a2, hJ⟩ : ∃ a1 a2, s11q3_Jet2 Qb a1 a2 := by
    have hQfun : Qb = fun t z => (s11q3_Khat d s β N ρ (max t 0))⁻¹ *
      Real.exp (G0 z + ∑ a, (β * s11q3_Gam d s (ρ (max t 0)) (π a z) + Real.log (ρ (max t 0) (π a z)))) :=
      funext fun t => funext (hQb t)
    rw [hQfun]
    exact ⟨_, _, jQ⟩
  -- the time derivative
  obtain ⟨Sx, hSx⟩ : ∃ Sx : ℝ → s113b_E (N * d) → ℝ, ∀ t z, Sx t z =
      G0 z + ∑ a, (β * s11q3_Gam d s (ρ t) (π a z) + Real.log (ρ t (π a z))) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨d1, hd1def⟩ : ∃ d1 : ℝ → s113b_E (N * d) → ℝ, ∀ t z, d1 t z =
      (-(s11q3_Khat' d s β N ρ D t) / (s11q3_Khat d s β N ρ t) ^ 2) * Real.exp (Sx t z) +
      (s11q3_Khat d s β N ρ t)⁻¹ * (Real.exp (Sx t z) *
        ∑ a, (β * s11q3_Gam d s (D t) (π a z) + D t (π a z) / ρ t (π a z))) := ⟨_, fun _ _ => rfl⟩
  have hA1 : ∀ t, 0 < t → ∀ z, HasDerivAt (fun σ => Qb σ z) (d1 t z) t := by
    intro t ht z
    have hG : ∀ a ∈ (Finset.univ : Finset (Fin N)),
        HasDerivAt (fun σ => β * s11q3_Gam d s (ρ σ) (π a z) + Real.log (ρ σ (π a z)))
          (β * s11q3_Gam d s (D t) (π a z) + D t (π a z) / ρ t (π a z)) t := fun a _ =>
      ((s11q3_Gam_dt hd1 hs0 hsd R ht (π a z)).const_mul β).add
        ((R.dA t ht (π a z)).log (R.pos t ht.le _).ne')
    have hS : HasDerivAt (fun σ => Sx σ z) (∑ a, (β * s11q3_Gam d s (D t) (π a z) + D t (π a z) / ρ t (π a z))) t := by
      have hfun : (fun σ => Sx σ z) = fun σ => G0 z + ∑ a, (β * s11q3_Gam d s (ρ σ) (π a z) + Real.log (ρ σ (π a z))) :=
        funext fun σ => hSx σ z
      rw [hfun]
      exact (HasDerivAt.fun_sum hG).const_add (G0 z)
    have hK : HasDerivAt (fun σ => (s11q3_Khat d s β N ρ σ)⁻¹)
        (-(s11q3_Khat' d s β N ρ D t) / (s11q3_Khat d s β N ρ t) ^ 2) t :=
      (hKd t ht).inv (hKpos t ht.le).ne'
    have hprod := hK.mul hS.exp
    have hev : (fun σ => Qb σ z) =ᶠ[𝓝 t] fun σ => (s11q3_Khat d s β N ρ σ)⁻¹ * Real.exp (Sx σ z) := by
      filter_upwards [Ioi_mem_nhds ht] with σ hσ
      rw [hQb, hSx, max_eq_left (le_of_lt (Set.mem_Ioi.1 hσ))]
    refine (hprod.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [hd1def]
  -- continuity of `d1`
  have hSset : ∀ p : ℝ × s113b_E (N * d), p ∈ Ici (0 : ℝ) ×ˢ (univ : Set (s113b_E (N * d))) → p.1 ∈ Ici (0 : ℝ) :=
    fun p hp => hp.1
  have hproj : ∀ a, Continuous fun p : ℝ × s113b_E (N * d) => (p.1, π a p.2) := fun a =>
    continuous_fst.prodMk ((π a).continuous.comp continuous_snd)
  have hmapS : ∀ a, MapsTo (fun p : ℝ × s113b_E (N * d) => (p.1, π a p.2)) (Ici (0 : ℝ) ×ˢ univ)
      (Ici (0 : ℝ) ×ˢ (univ : Set (Euc d))) := fun a p hp => ⟨hp.1, mem_univ _⟩
  have cΓ : ∀ a, ContinuousOn (fun p : ℝ × s113b_E (N * d) => s11q3_Gam d s (ρ p.1) (π a p.2))
      (Ici (0 : ℝ) ×ˢ univ) := fun a => (s11q3_Gam_cont0 hd1 hs0 hsd R).comp (hproj a).continuousOn (hmapS a)
  have cΓD : ∀ a, ContinuousOn (fun p : ℝ × s113b_E (N * d) => s11q3_Gam d s (D p.1) (π a p.2))
      (Ici (0 : ℝ) ×ˢ univ) := fun a => (s11q3_GamD_cont hd1 hs0 hsd R).comp (hproj a).continuousOn (hmapS a)
  have cρ : ∀ a, ContinuousOn (fun p : ℝ × s113b_E (N * d) => ρ p.1 (π a p.2)) (Ici (0 : ℝ) ×ˢ univ) := fun a =>
    R.j0.comp (hproj a).continuousOn (hmapS a)
  have cD : ∀ a, ContinuousOn (fun p : ℝ × s113b_E (N * d) => D p.1 (π a p.2)) (Ici (0 : ℝ) ×ˢ univ) := fun a =>
    R.jD.comp (hproj a).continuousOn (hmapS a)
  have clog : ∀ a, ContinuousOn (fun p : ℝ × s113b_E (N * d) => Real.log (ρ p.1 (π a p.2)))
      (Ici (0 : ℝ) ×ˢ univ) := fun a => (cρ a).log (fun p hp => (R.pos p.1 hp.1 _).ne')
  have cK : ContinuousOn (fun p : ℝ × s113b_E (N * d) => s11q3_Khat d s β N ρ p.1) (Ici (0 : ℝ) ×ˢ univ) :=
    hKc.comp continuous_fst.continuousOn hSset
  have cK' : ContinuousOn (fun p : ℝ × s113b_E (N * d) => s11q3_Khat' d s β N ρ D p.1) (Ici (0 : ℝ) ×ˢ univ) :=
    hKc'.comp continuous_fst.continuousOn hSset
  have hK0 : ∀ p ∈ Ici (0 : ℝ) ×ˢ (univ : Set (s113b_E (N * d))), s11q3_Khat d s β N ρ p.1 ≠ 0 :=
    fun p hp => (hKpos p.1 hp.1).ne'
  have cS : ContinuousOn (fun p : ℝ × s113b_E (N * d) => Sx p.1 p.2) (Ici (0 : ℝ) ×ˢ univ) := by
    have hfun : (fun p : ℝ × s113b_E (N * d) => Sx p.1 p.2) = fun p =>
        G0 p.2 + ∑ a, (β * s11q3_Gam d s (ρ p.1) (π a p.2) + Real.log (ρ p.1 (π a p.2))) :=
      funext fun p => hSx p.1 p.2
    rw [hfun]
    exact (hG0c.continuous.comp continuous_snd).continuousOn.add
      (continuousOn_finsetSum _ fun a _ => (continuousOn_const.mul (cΓ a)).add (clog a))
  have cexp : ContinuousOn (fun p : ℝ × s113b_E (N * d) => Real.exp (Sx p.1 p.2)) (Ici (0 : ℝ) ×ˢ univ) :=
    Real.continuous_exp.comp_continuousOn cS
  have cSum : ContinuousOn (fun p : ℝ × s113b_E (N * d) =>
      ∑ a, (β * s11q3_Gam d s (D p.1) (π a p.2) + D p.1 (π a p.2) / ρ p.1 (π a p.2))) (Ici (0 : ℝ) ×ˢ univ) :=
    continuousOn_finsetSum _ fun a _ => (continuousOn_const.mul (cΓD a)).add
      ((cD a).div (cρ a) (fun p hp => (R.pos p.1 hp.1 _).ne'))
  have cd1 : ContinuousOn (fun p : ℝ × s113b_E (N * d) => d1 p.1 p.2) (Ici (0 : ℝ) ×ˢ univ) := by
    have hfun : (fun p : ℝ × s113b_E (N * d) => d1 p.1 p.2) = fun p =>
        (-(s11q3_Khat' d s β N ρ D p.1) / (s11q3_Khat d s β N ρ p.1) ^ 2) * Real.exp (Sx p.1 p.2) +
        (s11q3_Khat d s β N ρ p.1)⁻¹ * (Real.exp (Sx p.1 p.2) *
          ∑ a, (β * s11q3_Gam d s (D p.1) (π a p.2) + D p.1 (π a p.2) / ρ p.1 (π a p.2))) :=
      funext fun p => hd1def p.1 p.2
    rw [hfun]
    exact (((cK'.neg).div (cK.pow 2) (fun p hp => pow_ne_zero 2 (hK0 p hp))).mul cexp).add
      ((cK.inv₀ hK0).mul (cexp.mul cSum))
  -- the half-line datum
  have hHalf : s11q3_Half Qb d1 (fun t z => a1 t z) (fun t z => a2 t z) := by
    refine ⟨hJ.c0, cd1, hJ.c1, hJ.c2, ?_, hA1, hJ.h1, hJ.h2, ?_⟩
    · intro t ht z
      have hcz : ContinuousOn (fun σ : ℝ => Qb σ z) (Ici 0) :=
        (hJ.c0.comp (continuous_id.prodMk continuous_const)).continuousOn
      have hcd : ContinuousOn (fun σ : ℝ => d1 σ z) (Ici 0) :=
        cd1.comp (continuous_id.prodMk continuous_const).continuousOn fun σ hσ => ⟨hσ, mem_univ _⟩
      exact s11q3_rightDeriv hcz (fun t ht => hA1 t ht z) hcd t ht
    · intro t ht
      funext z
      have h1 : max t 0 = 0 := max_eq_right ht
      rw [hQb, hQb, h1, max_self]
  obtain ⟨Qr, hQr, hQrEq⟩ := hHalf.reflect
  refine ⟨fun t z => Qr (t, z), G, ⟨hGo, fun z hz => hKG hz, hQr, fun t ht z => ?_, fun t ht z hz => ?_⟩⟩
  · rw [hQrEq t ht.1 z, hQb]
    exact mul_pos (inv_pos.2 (hKpos _ (le_max_right t 0))) (Real.exp_pos _)
  · rw [hQrEq t ht.1 z, s11q3_movQ_eq hd1 hs0 hsd R hN1 ht.1 (hprob t ht.1)]
    rw [hQb, max_eq_left ht.1]
    congr 1
    have hθz : θ z = 1 := hθ1 z hz
    have h1 : Real.exp (∑ a, Real.log (ρ t (π a z))) = ∏ a, ρ t (π a z) := by
      rw [Real.exp_sum]
      exact Finset.prod_congr rfl fun a _ => Real.exp_log (R.pos t ht.1 _)
    have h2 : G0 z + ∑ a, (β * s11q3_Gam d s (ρ t) (π a z) + Real.log (ρ t (π a z))) =
        (-β * N * s11q3_F0 d s N (Jc d N z) + β * ∑ a, s11q3_Gam d s (ρ t) (π a z)) +
          ∑ a, Real.log (ρ t (π a z)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hG0, hθz]
      ring
    rw [h2, Real.exp_add, h1]
    simp only [s11q3_W, s11q3_E, s11q3_P, hπ]

end HRS.MS.S11Q3

end
