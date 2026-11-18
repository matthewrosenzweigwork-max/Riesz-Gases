import HRS.MS.SA12CompB4
import HRS.MS.SA12CompB2
import HRS.MS.AdjRdWeakTerm
import HRS.MS.AdjRdNorms
import HRS.MS.FcauTie

/-!
# S.A.12 B5: a regular representative of a weak forward solution is a classical adjoint solution

The weak equation tested against `C_c^∞` functions, the slice identity `fcau_slice` and Fubini turn the weak
forward equation into the pointwise Duhamel identity `u(τ,x) = φ(x) + ∫₀^τ 𝓛_{t-σ}u(σ)(x) dσ`; the integrand is
jointly continuous with linear growth by B4, and the fundamental theorem of calculus gives the time derivative.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Companions

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.Fcau HRS.MH.DualityRd

variable {d : ℕ}

/-- `forwardPairing` only sees its first argument almost everywhere. -/
theorem sa12z_forwardPairing_congr_ae (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) (t σ : ℝ)
    {z z' : Euc d → ℝ} (ψ : Euc d → ℝ) (h : z =ᵐ[volume] z') :
    forwardPairing D ρ t σ z ψ = forwardPairing D ρ t σ z' ψ := by
  have key : ∀ f : Euc d → ℝ, ∫ x, z x * f x = ∫ x, z' x * f x := fun f =>
    integral_congr_ae (by filter_upwards [h] with x hx; rw [hx])
  unfold forwardPairing
  simp_rw [key]

-- BEGIN SA12.B5
theorem classical_of_regular_representative (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (m : ℕ) (hm : 1 ≤ m) (MB Λ ΛV G₀ νbar T : ℝ)
    (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ)
    (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) T) (φ : Euc d → ℝ) (hφ : ContDiff ℝ 2 φ)
    (F u : ℝ → Euc d → ℝ) (hF : IsForwardSolutionRd (D.coeff μ) t φ F)
    (hae : ∀ τ ∈ Icc (0 : ℝ) t, u τ =ᵐ[volume] F τ)
    (hc2 : ∀ τ ∈ Icc (0 : ℝ) t, ContDiff ℝ 2 (u τ))
    (hb : ∃ B : ℝ, ∀ j ≤ 2, ∀ τ ∈ Icc (0 : ℝ) t, ∀ x,
      ‖iteratedFDeriv ℝ j (u τ) x‖ ≤ B)
    (hcont : ∀ j ≤ 2, ContinuousOn
      (fun q : ℝ × Euc d => iteratedFDeriv ℝ j (u q.1) q.2)
      (Icc (0 : ℝ) t ×ˢ univ)) :
    IsClassicalAdjointW (D.coeff μ) t φ (fun r => u (t - r)) := by
  obtain ⟨hDs, -, -⟩ := hD.hs
  have hs0' : 0 ≤ D.s := by rw [hDs]; exact hs0
  have hsd' : D.s < d := by rw [hDs]; exact hsd
  have ht0 : 0 ≤ t := ht.1.le
  obtain ⟨B, hB⟩ := hb
  have hrev : ∀ r ∈ Icc (0 : ℝ) t, t - r ∈ Icc (0 : ℝ) t := fun r hr =>
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hMem : ∀ τ ∈ Icc (0 : ℝ) t, MemCb 2 (u τ) := fun τ hτ =>
    ⟨hc2 τ hτ, fun j hj => ⟨B, by rintro _ ⟨x, rfl⟩; exact hB j hj τ hτ x⟩⟩
  obtain ⟨hGc, BG, hBG⟩ := generator_on_continuous_c2_path hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T D μ hD
    t ht u hc2 ⟨B, hB⟩ hcont
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → Euc d → ℝ,
      G = fun σ x => generatorW (D.coeff μ) (t - σ) (u σ) x := ⟨_, rfl⟩
  have hGval : ∀ σ x, G σ x = generatorW (D.coeff μ) (t - σ) (u σ) x := fun σ x => by rw [hGdef]
  have hGc' : ContinuousOn (fun q : ℝ × Euc d => G q.1 q.2) (Icc (0 : ℝ) t ×ˢ univ) := by
    rw [hGdef]; exact hGc
  have hBG' : ∀ τ ∈ Icc (0 : ℝ) t, ∀ x, |G τ x| ≤ BG * (1 + ‖x‖) := fun τ hτ x => by
    rw [hGval]; exact hBG τ hτ x
  have hft : Continuous fun q : Set.Icc (0 : ℝ) t × Euc d => G q.1.1 q.2 :=
    hGc'.comp_continuous (f := fun q : Set.Icc (0 : ℝ) t × Euc d => (q.1.1, q.2))
      (by fun_prop) (fun q => ⟨q.1.2, mem_univ _⟩)
  have hGcl : Continuous (fun q : ℝ × Euc d => G (max 0 (min q.1 t)) q.2) := db3_Phi_cont ht0 hft
  have hS := fcau_slices_of_hyp hd hs0 hsd m hm MB Λ ΛV G₀ hDs hD.hM hD.hV hD.hμ
    (show t ∈ Icc (0 : ℝ) T from ⟨ht0, ht.2⟩)
  obtain ⟨χ, hχ⟩ := fcau_exists_cutoff (d := d)
  obtain ⟨Cχ, hCχ0, hCχ⟩ := fcau_ul_bound hχ
  have hulf : ∀ σ ∈ Icc (0 : ℝ) t, ulocNormE 0 χ (F σ) < ⊤ := by
    intro σ hσ
    have h1 : ulocNormE 1 χ (u σ) ≤ ENNReal.ofReal (Cχ * B) :=
      hCχ (u σ) B ((hc2 σ hσ).of_le (by norm_num))
        (fun x => by
          have := hB 0 (by norm_num) σ hσ x
          rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this)
        (fun x => by
          have := hB 1 (by norm_num) σ hσ x
          rwa [norm_iteratedFDeriv_one] at this)
    have h2 := (HRS.MS.SA12BD.sa12_uloc_mono d 1 0 (by norm_num) χ (u σ)).trans h1
    rw [(norm_congr_ae 0 χ (u σ) (F σ) (hae σ hσ)).1] at h2
    exact lt_of_le_of_lt h2 ENNReal.ofReal_lt_top
  -- the weak term is the pairing with the generator
  have hweak : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ σ ∈ Icc (0 : ℝ) t,
      forwardWeakTerm (D.coeff μ) t F ψ σ = ∫ x, ψ x * G σ x := by
    intro ψ hψ σ hσ
    rw [HRS.MS.SA12BD.sa12_weak_term_bridge d hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T χ hχ D μ hD t ht
      ψ hψ F σ hσ (hulf σ hσ)]
    rw [← sa12z_forwardPairing_congr_ae D μ t σ ψ (hae σ hσ)]
    have := (fcau_slice hd D hs0' hsd' μ t σ (hS (t - σ) (hrev σ hσ)).1 (hS (t - σ) (hrev σ hσ)).2
      (hMem σ hσ) hψ.1 hψ.2).symm
    simp_rw [hGval]
    exact this
  -- the Duhamel identity
  have hK : ∀ τ ∈ Icc (0 : ℝ) t, ∀ x, u τ x = φ x + ∫ σ in (0 : ℝ)..τ, G σ x := by
    intro τ hτ
    have hGeq : ∀ x, ∫ σ in (0 : ℝ)..τ, G σ x = ∫ σ in (0 : ℝ)..τ, G (max 0 (min σ t)) x := by
      intro x
      refine intervalIntegral.integral_congr (fun σ hσ => ?_)
      rw [Set.uIcc_of_le hτ.1] at hσ
      show G σ x = G (max 0 (min σ t)) x
      rw [db3_clamp_eq (show σ ∈ Icc (0 : ℝ) t from ⟨hσ.1, hσ.2.trans hτ.2⟩)]
    set I : Euc d → ℝ := fun x => ∫ σ in (0 : ℝ)..τ, G σ x with hI
    have hIc : Continuous I := by
      have := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := volume) (f := fun (x : Euc d) (σ : ℝ) => G (max 0 (min σ t)) x)
        (by
          have : Continuous (fun p : Euc d × ℝ => G (max 0 (min p.2 t)) p.1) :=
            hGcl.comp (continuous_snd.prodMk continuous_fst)
          exact this) 0 τ
      exact this.congr (fun x => (hGeq x).symm)
    have hRc : Continuous (fun x => u τ x - φ x - I x) :=
      (((hc2 τ hτ).continuous).sub hφ.continuous).sub hIc
    have hzero : ∀ᵐ x ∂(volume : Measure (Euc d)), u τ x - φ x - I x = 0 := by
      refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hRc.locallyIntegrable (fun ψ hψ hψc => ?_)
      have hψI : IsCcInfty ψ := ⟨hψ, hψc⟩
      have hψcont : Continuous ψ := hψ.continuous
      have hint : ∀ f : Euc d → ℝ, Continuous f → Integrable (fun x => ψ x * f x) := fun f hf =>
        (hψcont.mul hf).integrable_of_hasCompactSupport hψc.mul_right
      have h1 := hF.eq ψ hψI τ hτ
      have h2 : ∫ x, F τ x * ψ x = ∫ x, ψ x * u τ x := by
        refine integral_congr_ae ?_
        filter_upwards [hae τ hτ] with x hx
        rw [← hx]; ring
      have h3 : ∫ σ in Icc (0 : ℝ) τ, forwardWeakTerm (D.coeff μ) t F ψ σ = ∫ x, ψ x * I x := by
        rw [setIntegral_congr_fun measurableSet_Icc (fun σ hσ =>
          hweak ψ hψI σ ⟨hσ.1, hσ.2.trans hτ.2⟩), integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le hτ.1]
        exact (fcau_fubini ht0 hft hBG' hψcont hψc le_rfl hτ.1 hτ.2).symm
      have e : (fun x => ψ x • (u τ x - φ x - I x)) =
          fun x => ψ x * u τ x - ψ x * φ x - ψ x * I x := by
        funext x; simp only [smul_eq_mul]; ring
      have i1 := hint _ (hc2 τ hτ).continuous
      have i2 := hint _ hφ.continuous
      have i3 := hint _ hIc
      have i12 : Integrable (fun x => ψ x * u τ x - ψ x * φ x) := i1.sub i2
      rw [e, integral_sub i12 i3, integral_sub i1 i2]
      have h4 : ∫ x, φ x * ψ x = ∫ x, ψ x * φ x := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_); ring
      linarith
    have hz : (fun x => u τ x - φ x - I x) =ᵐ[volume] fun _ => 0 := hzero
    have hz' := (Continuous.ae_eq_iff_eq volume hRc continuous_const).1 hz
    intro x
    have h0 : u τ x - φ x - I x = 0 := congrFun hz' x
    have hIx : I x = ∫ σ in (0 : ℝ)..τ, G σ x := rfl
    linarith
  -- the pointwise time derivative of `u`
  have hder : ∀ x, ∀ τ ∈ Ioo (0 : ℝ) t, HasDerivAt (fun τ' => u τ' x) (G τ x) τ := by
    intro x τ hτ
    have hcl : Continuous fun σ : ℝ => G (max 0 (min σ t)) x :=
      hGcl.comp (continuous_id.prodMk continuous_const)
    have h1 := hcl.integral_hasStrictDerivAt 0 τ
    have hτ' : τ ∈ Icc (0 : ℝ) t := ⟨hτ.1.le, hτ.2.le⟩
    have h2 : G (max 0 (min τ t)) x = G τ x := by rw [db3_clamp_eq hτ']
    rw [h2] at h1
    have h3 := (h1.hasDerivAt.const_add (φ x))
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with τ' hτ'
    have hτ'' : τ' ∈ Icc (0 : ℝ) t := ⟨hτ'.1.le, hτ'.2.le⟩
    rw [hK τ' hτ'' x]
    congr 1
    refine intervalIntegral.integral_congr (fun σ hσ => ?_)
    rw [Set.uIcc_of_le hτ'.1.le] at hσ
    show G σ x = G (max 0 (min σ t)) x
    rw [db3_clamp_eq (show σ ∈ Icc (0 : ℝ) t from ⟨hσ.1, hσ.2.trans hτ'.2.le⟩)]
  have hGsym : ∀ r ∈ Icc (0 : ℝ) t, ∀ x, G (t - r) x =
      generatorW (D.coeff μ) r (u (t - r)) x := by
    intro r hr x
    rw [hGval, sub_sub_cancel]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    exact hc2 (t - r) (hrev r hr)
  · intro j hj
    exact ⟨B, fun r hr x => hB j hj (t - r) (hrev r hr) x⟩
  · intro j hj
    exact (hcont j hj).comp_continuous (f := fun p : Set.Icc (0 : ℝ) t × Euc d => (t - p.1.1, p.2))
      (by fun_prop) (fun p => ⟨hrev p.1.1 p.1.2, mem_univ _⟩)
  · funext x
    show u (t - t) x = φ x
    rw [sub_self]
    have := hK 0 ⟨le_rfl, ht0⟩ x
    simpa using this
  · intro x r hr
    have hd := hder x (t - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have hc : HasDerivAt (fun r' : ℝ => t - r') (-1) r := by
      simpa using (hasDerivAt_id r).const_sub t
    have := hd.scomp r hc
    rw [hGsym r ⟨hr.1.le, hr.2.le⟩ x] at this
    have h6 : HasDerivAt (fun r' : ℝ => u (t - r') x)
        ((-1 : ℝ) • generatorW (D.coeff μ) r (u (t - r)) x) r := this
    have e6 : (-1 : ℝ) • generatorW (D.coeff μ) r (u (t - r)) x =
        -(generatorW (D.coeff μ) r (u (t - r)) x) := by simp
    rw [e6] at h6
    exact h6
  · have h := hft.comp (g := fun q : Set.Icc (0 : ℝ) t × Euc d => G q.1.1 q.2)
      (f := fun p : Set.Icc (0 : ℝ) t × Euc d => ((⟨t - p.1.1, hrev p.1.1 p.1.2⟩ : Set.Icc (0 : ℝ) t), p.2))
      (by fun_prop)
    refine h.congr (fun p => ?_)
    exact hGsym p.1.1 p.1.2 p.2
  · refine ⟨BG, fun r hr x => ?_⟩
    rw [← hGsym r hr x]
    exact hBG' (t - r) (hrev r hr) x
-- END SA12.B5

end HRS.MH.AdjointRd.Phase2SA12Companions
