import HRS.MC.CepN5Aux6

/-!
# Packet N5, helper 8: pathwise facts

(a) behaviour of `H` before/at the exit time `τe` from `(δ, ε)`;
(b) on a path in `A₁`, the increments of `Z` are `∫ β` with `0 ≤ β ≤ κ/H + C ≤ M₀` up to `τR`, so that the
drift recovery lemma `n5_Q` applies.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal

namespace HRS.MC.CepN5

open HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section Exit

variable {G : ℝ → Ω → ℝ} {t₁ : ℝ≥0} {δ ε : ℝ} {ω : Ω}

theorem n5_exit_lt {u : ℝ} (hu : 0 ≤ u) (h : (u : WithTop ℝ) < n5_tauE G t₁ δ ε ω) :
    δ < n5_H G t₁ u ω ∧ n5_H G t₁ u ω < ε := by
  have := notMem_of_lt_hittingAfter (u := n5_H G t₁) (s := Iic δ ∪ Ici ε) (n := 0) (ω := ω) h hu
  simp only [mem_union, mem_Iic, mem_Ici, not_or, not_le] at this
  exact ⟨this.1, this.2⟩

theorem n5_exit_mem (hG : Continuous fun t => G t ω) {a : ℝ}
    (h : n5_tauE G t₁ δ ε ω = (a : WithTop ℝ)) :
    0 ≤ a ∧ (n5_H G t₁ a ω ≤ δ ∨ ε ≤ n5_H G t₁ a ω) := by
  refine ⟨?_, ?_⟩
  · have := le_hittingAfter (u := n5_H G t₁) (s := Iic δ ∪ Ici ε) (n := (0 : ℝ)) ω
    change (0 : WithTop ℝ) ≤ n5_tauE G t₁ δ ε ω at this
    rw [h] at this
    exact_mod_cast this
  · have := mem_of_hittingAfter_eq_of_isClosed (n5_H G t₁) ω (n5_H_cont (fun _ => hG) t₁ ω)
      (isClosed_Iic.union isClosed_Ici : IsClosed (Iic δ ∪ Ici ε)) 0 a h
    simpa [mem_union] using this

theorem n5_exit_le (hG : Continuous fun t => G t ω) (hε : 0 < ε) (h0 : δ < G t₁ ω)
    (h0' : G t₁ ω ≤ ε / 2) {u : ℝ} (hu : 0 ≤ u) (h : (u : WithTop ℝ) ≤ n5_tauE G t₁ δ ε ω) :
    δ ≤ n5_H G t₁ u ω ∧ n5_H G t₁ u ω ≤ ε := by
  rcases h.lt_or_eq with hlt | heq
  · exact ⟨(n5_exit_lt hu hlt).1.le, (n5_exit_lt hu hlt).2.le⟩
  · rcases hu.lt_or_eq with hpos | hzero
    · have hcont : Continuous fun s => n5_H G t₁ s ω := n5_H_cont (fun _ => hG) t₁ ω
      have ht : Tendsto (fun s => n5_H G t₁ s ω) (𝓝[<] u) (𝓝 (n5_H G t₁ u ω)) :=
        (hcont.tendsto u).mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ v in 𝓝[<] u, 0 < v ∧ v < u := by
        filter_upwards [Ioo_mem_nhdsLT hpos] with v hv using hv
      have h1 : ∀ᶠ v in 𝓝[<] u, δ < n5_H G t₁ v ω ∧ n5_H G t₁ v ω < ε := by
        filter_upwards [hev] with v hv
        refine n5_exit_lt hv.1.le ?_
        rw [← heq]; exact_mod_cast hv.2
      exact ⟨ge_of_tendsto ht (h1.mono fun v hv => hv.1.le), le_of_tendsto ht (h1.mono fun v hv => hv.2.le)⟩
    · rw [← hzero, n5_H_zero]
      exact ⟨h0.le, h0'.trans (by linarith)⟩

end Exit

section Pathwise

variable {G c : ℝ → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ρ : Ω → WithTop ℝ} {t₁ : ℝ≥0} {κ σ C δ ε dur : ℝ}
  {A : Set Ω} {ω : Ω}

theorem n5_toNNReal_add (t₁ : ℝ≥0) {t : ℝ} (ht : 0 ≤ t) : ((t₁ : ℝ) + t).toNNReal = t₁ + t.toNNReal := by
  rw [Real.toNNReal_add (NNReal.coe_nonneg t₁) ht, Real.toNNReal_coe]

theorem n5_pathwise (hκ : 0 < κ) (hC : 0 ≤ C) (hδ : 0 < δ) (hε : 0 < ε) (hεC : C * ε ≤ κ)
    (hdur : 0 < dur) (hω : ω ∈ n5_A1 G ρ t₁ δ A) (hA0 : G t₁ ω ≤ ε / 2)
    (hGc : Continuous fun t => G t ω) (hc : ∀ u, |c u ω| ≤ C)
    (hdyn : ∀ s t : ℝ, (t₁ : ℝ) ≤ s → s ≤ t → t ≤ t₁ + dur → ((t : ℝ) : WithTop ℝ) ≤ ρ ω →
      G t ω - G s ω = (∫ u in s..t, (κ / G u ω + c u ω)) +
        σ * (B (Real.toNNReal t) ω - B (Real.toNNReal s) ω)) :
    (∀ s ∈ Icc 0 (n5_tauR G ρ t₁ δ ε dur A ω), n5_Zp G B t₁ σ s ω =
      ∫ u in Icc 0 s, n5_bcl (κ / δ + C) (n5_dq (fun u => n5_Zp G B t₁ σ u ω) u)) ∧
    (∀ᵐ u, u ∈ Icc 0 (n5_tauR G ρ t₁ δ ε dur A ω) →
      n5_bcl (κ / δ + C) (n5_dq (fun u => n5_Zp G B t₁ σ u ω) u) ≤ κ / n5_H G t₁ u ω + C) := by
  obtain ⟨⟨hAω, hρω⟩, hGδ⟩ := hω
  set T₀ := n5_tauR G ρ t₁ δ ε dur A ω with hT₀def
  have hT₀0 : 0 ≤ T₀ := n5_tauR_nonneg hdur.le ω
  have hT₀d : T₀ ≤ dur := n5_tauR_le hdur.le ω
  have hω' : ω ∈ n5_A1 G ρ t₁ δ A := ⟨⟨hAω, hρω⟩, hGδ⟩
  have hT₀tau : ((T₀ : ℝ) : WithTop ℝ) = n5_tau1 G ρ t₁ δ ε dur ω := n5_tauR_of_mem hω'
  have hle_e : ∀ u : ℝ, 0 ≤ u → u ≤ T₀ → (u : WithTop ℝ) ≤ n5_tauE G t₁ δ ε ω := fun u hu huT => by
    have h1 : (u : WithTop ℝ) ≤ (T₀ : WithTop ℝ) := by exact_mod_cast huT
    rw [hT₀tau] at h1
    exact h1.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hle_r : ∀ u : ℝ, u ≤ T₀ → (u : WithTop ℝ) ≤ n5_rhat ρ t₁ ω := fun u huT => by
    have h1 : (u : WithTop ℝ) ≤ (T₀ : WithTop ℝ) := by exact_mod_cast huT
    rw [hT₀tau] at h1
    exact h1.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hρle : ∀ u : ℝ, u ≤ T₀ → (((t₁ : ℝ) + u : ℝ) : WithTop ℝ) ≤ ρ ω := fun u huT => by
    have h1 := hle_r u huT
    unfold n5_rhat at h1
    have hρω' : ((t₁ : ℝ) : WithTop ℝ) ≤ ρ ω := hρω
    cases h : ρ ω with
    | top => exact le_top
    | coe r =>
      rw [h] at h1 hρω'
      simp only [WithTop.map_coe, WithTop.coe_le_coe] at h1 hρω' ⊢
      have := (le_max_left (r - t₁) 0)
      have h2 : r - t₁ ≤ max (r - t₁) 0 := le_max_left _ _
      have h3 : max (r - t₁) 0 = r - t₁ := max_eq_left (by linarith)
      linarith
  have hGin : ∀ u : ℝ, 0 ≤ u → u ≤ T₀ → δ ≤ G (t₁ + u) ω ∧ G (t₁ + u) ω ≤ ε := fun u hu huT => by
    have := n5_exit_le hGc hε hGδ hA0 hu (hle_e u hu huT)
    simpa [n5_H, max_eq_left hu] using this
  have hM₀ : 0 ≤ κ / δ + C := by positivity
  have hQ := n5_Q (Z := fun u => n5_Zp G B t₁ σ u ω)
    (β := fun u => κ / G (t₁ + u) ω + c (t₁ + u) ω) (hi := fun u => κ / n5_H G t₁ u ω + C)
    (T₀ := T₀) (M₀ := κ / δ + C) hT₀0 hM₀ (n5_Zp_neg G B t₁ σ le_rfl ω)
    (fun u hu => n5_Zp_neg G B t₁ σ hu ω) ?_ ?_ ?_
  · exact hQ
  · intro s t hs hst htT
    have hs0 : 0 ≤ s := hs
    have ht0 : 0 ≤ t := hs0.trans hst
    have h1 := hdyn ((t₁ : ℝ) + s) ((t₁ : ℝ) + t) (by linarith) (by linarith)
      (by linarith [htT, hT₀d]) (hρle t htT)
    rw [n5_toNNReal_add t₁ ht0, n5_toNNReal_add t₁ hs0,
      ← intervalIntegral.integral_comp_add_left (fun u => κ / G u ω + c u ω)] at h1
    simp only [n5_Zp, n5_H, max_eq_left hs0, max_eq_left ht0, Real.toNNReal_of_nonneg, Real.coe_toNNReal _ hs0,
      Real.coe_toNNReal _ ht0]
    linarith
  · intro u hu
    have hH : n5_H G t₁ u ω = G (t₁ + u) ω := by simp [n5_H, max_eq_left hu.1]
    obtain ⟨hl, hr⟩ := hGin u hu.1 hu.2
    have hpos : 0 < G (t₁ + u) ω := lt_of_lt_of_le hδ hl
    have h1 : C ≤ κ / G (t₁ + u) ω := by
      rw [le_div_iff₀ hpos]
      nlinarith [hεC, hr, hC]
    have hcu := abs_le.1 (hc (t₁ + u))
    refine ⟨by linarith [hcu.1], ?_⟩
    rw [hH]
    linarith [hcu.2]
  · intro u hu
    have hH : n5_H G t₁ u ω = G (t₁ + u) ω := by simp [n5_H, max_eq_left hu.1]
    obtain ⟨hl, hr⟩ := hGin u hu.1 hu.2
    show κ / n5_H G t₁ u ω + C ≤ κ / δ + C
    rw [hH]
    have : κ / G (t₁ + u) ω ≤ κ / δ := div_le_div_of_nonneg_left hκ.le hδ hl
    linarith

end Pathwise

end HRS.MC.CepN5
