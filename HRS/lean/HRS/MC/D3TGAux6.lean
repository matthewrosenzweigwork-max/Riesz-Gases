import HRS.MC.D3TGAux5

/-!
# Packet D3TG, helper 6: the truncated kernel `g_λ = H_λ - c_λ` on the torus
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.MC.D3TG

open HRS HRS.MC.D3EW HRS.MC.Per HRS.MC.D3T1 HRS.MC.FDLE

variable {d : ℕ}

/-- The constant `c_λ = b (∫ φ) λ^{d-s} / (d-s)`. -/
def d3tgc (ψ : Euc d → ℝ) (s b lam : ℝ) : ℝ :=
  b * (∫ x, fdlPhi ψ x) * lam ^ ((d : ℝ) - s) / ((d : ℝ) - s)

lemma d3tgH_per (ψ : Euc d → ℝ) (s b lam : ℝ) (y : Euc d) (n : Lattice d) :
    d3tgH ψ s b lam (y + Lattice.toEuc n) = d3tgH ψ s b lam y := by
  unfold d3tgH d3tgK
  simp_rw [d3t_mk_add]

lemma d3tg_neBot (hd : 1 ≤ d) : (𝓝[≠] (0 : Torus d)).NeBot := by
  set i0 : Fin d := ⟨0, hd⟩ with hi0
  set f : ℝ → Torus d := fun r => Torus.mk (r • EuclideanSpace.single i0 (1 : ℝ)) with hf
  have hfc : Continuous f := Torus.continuous_mk.comp (continuous_id.smul continuous_const)
  have hf0 : f 0 = 0 := by
    funext i
    simp [hf, Torus.mk]
  have hlim : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (hfc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      rwa [hf0] at this
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
      intro h0
      have h1 : f r i0 = 0 := by rw [h0]; rfl
      have h2 : ((r : ℝ) : UnitAddCircle) = 0 := by
        simpa [hf, Torus.mk] using h1
      rw [AddCircle.coe_eq_zero_iff] at h2
      obtain ⟨n, hn⟩ := h2
      simp only [zsmul_eq_mul, mul_one] at hn
      have h3 : (0 : ℝ) < n := by rw [hn]; exact hr.1
      have h4 : (n : ℝ) < 1 := by rw [hn]; exact hr.2
      have h5 : (0 : ℤ) < n := by exact_mod_cast h3
      have h6 : n < (1 : ℤ) := by exact_mod_cast h4
      omega
  haveI : (Filter.map f (𝓝[>] (0 : ℝ))).NeBot := Filter.map_neBot
  exact Filter.NeBot.mono this hlim

theorem d3tg_rep_ne (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {lam : ℝ} (hl0 : 0 < lam)
    (y : Euc d) (hy : Torus.mk y ≠ 0) :
    fdlTruncT ψ s b lam (Torus.mk y) = d3tgH ψ s b lam y - d3tgc ψ s b lam := by
  obtain ⟨hint, hrep⟩ := hb.2.2.2 (Torus.mk y) hy
  set I : ℝ := ∫ x, fdlPhi ψ x with hI
  set f : ℝ → ℝ := fun t => t ^ ((d : ℝ) - s) *
    (fdlPer (fdlPhiScale ψ t) (Torus.mk y) - I) / t with hf
  have hds : 0 < (d : ℝ) - s := by linarith
  have hH : d3tgH ψ s b lam y = b * ∫ t in Ioi lam, f t := by
    unfold d3tgH
    rw [← integral_const_mul]
    rfl
  have hsplit : ∫ t in Ioi 0, f t = (∫ t in Ioc 0 lam, f t) + ∫ t in Ioi lam, f t := by
    have h := setIntegral_union (μ := volume) (f := f) (Set.Ioc_disjoint_Ioi (le_refl lam))
      measurableSet_Ioi (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hl0.le))
    rwa [Ioc_union_Ioi_eq_Ioi hl0.le] at h
  have hrpow : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s - 1)) (Ioc 0 lam) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := lam) (by linarith)).1
  have hint2 : ∫ t in Ioc 0 lam, t ^ ((d : ℝ) - s - 1) = lam ^ ((d : ℝ) - s) / ((d : ℝ) - s) := by
    rw [← intervalIntegral.integral_of_le hl0.le, integral_rpow (Or.inl (by linarith))]
    rw [Real.zero_rpow (by linarith), sub_zero, show (d : ℝ) - s - 1 + 1 = (d : ℝ) - s by ring]
  have hW : ∫ t in Ioc 0 lam, t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) (Torus.mk y) / t
      = (∫ t in Ioc 0 lam, f t) + I * (lam ^ ((d : ℝ) - s) / ((d : ℝ) - s)) := by
    have hcongr : ∀ t ∈ Ioc 0 lam, t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) (Torus.mk y) / t
        = f t + I * t ^ ((d : ℝ) - s - 1) := by
      intro t ht
      simp only [hf]
      rw [Real.rpow_sub_one ht.1.ne']
      field_simp
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr,
      integral_add (hint.mono_set Ioc_subset_Ioi_self) (hrpow.const_mul I), integral_const_mul, hint2]
  unfold fdlTruncT
  rw [if_neg hy, hrep, hsplit, hH]
  unfold fdlWT
  rw [hW]
  unfold d3tgc
  ring

lemma d3tg_G_cont (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (b : ℝ)
    {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) :
    Continuous (fun x : Torus d => d3tgH ψ s b lam (Torus.rep x) - d3tgc ψ s b lam) := by
  refine Torus.continuous_of_continuous_lift ?_
  have : Torus.lift (fun x : Torus d => d3tgH ψ s b lam (Torus.rep x) - d3tgc ψ s b lam)
      = fun y => d3tgH ψ s b lam y - d3tgc ψ s b lam := by
    funext y
    obtain ⟨m, hm⟩ := Torus.rep_mk y
    show d3tgH ψ s b lam (Torus.rep (Torus.mk y)) - d3tgc ψ s b lam = _
    rw [hm, d3tgH_per]
  rw [this]
  exact ((d3tgH_contDiff hd hψ hs0 b hl0 hl1).continuous).sub continuous_const

theorem d3tg_trunc_eq (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {lam : ℝ} (hl0 : 0 < lam)
    (hl1 : lam < 1) (x : Torus d) :
    fdlTruncT ψ s b lam x = d3tgH ψ s b lam (Torus.rep x) - d3tgc ψ s b lam := by
  by_cases hx : x = 0
  · subst hx
    have hG := d3tg_G_cont hd hs0 hψ b hl0 hl1
    have hlim : Tendsto (fun x' : Torus d => periodicRiesz d s x' - fdlWT ψ s b lam x')
        (𝓝[≠] (0 : Torus d))
        (𝓝 (d3tgH ψ s b lam (Torus.rep (0 : Torus d)) - d3tgc ψ s b lam)) := by
      refine Tendsto.congr' ?_ ((hG.tendsto 0).mono_left nhdsWithin_le_nhds)
      filter_upwards [self_mem_nhdsWithin] with x' hx'
      have hx'' : x' ≠ 0 := hx'
      have := d3tg_rep_ne hd hs0 hsd hψ hb hl0 (Torus.rep x') (by rwa [Torus.mk_rep])
      rw [Torus.mk_rep] at this
      rw [← this]
      unfold fdlTruncT
      rw [if_neg hx'']
    haveI := d3tg_neBot hd
    unfold fdlTruncT
    rw [if_pos rfl]
    exact hlim.limUnder_eq
  · have := d3tg_rep_ne hd hs0 hsd hψ hb hl0 (Torus.rep x) (by rwa [Torus.mk_rep])
    rwa [Torus.mk_rep] at this

theorem d3tg_lift_eq (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {lam : ℝ} (hl0 : 0 < lam)
    (hl1 : lam < 1) (y : Euc d) :
    Torus.lift (fdlTruncT ψ s b lam) y = d3tgH ψ s b lam y - d3tgc ψ s b lam := by
  show fdlTruncT ψ s b lam (Torus.mk y) = _
  rw [d3tg_trunc_eq hd hs0 hsd hψ hb hl0 hl1]
  obtain ⟨m, hm⟩ := Torus.rep_mk y
  rw [hm, d3tgH_per]

end HRS.MC.D3TG
