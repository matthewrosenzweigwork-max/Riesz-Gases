import HRS.MC.WinJSpecDefs
import HRS.MC.WinJP1

/-!
# WJ4: P4 `p4_polyMix_bounds` (the difference polygon path)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.WinJ

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan HRS.MC.Sec7.PID HRS.MC.E213U3

section P4Helpers

variable {d : ℕ}

/-- evaluation of a difference of paths -/
lemma p_wj4_pathAt_sub {m T : ℝ} (w w' : PathSpace d m T) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    pathAt (w - w') t = pathAt w t - pathAt w' t := by
  unfold pathAt
  rw [dif_pos ht, dif_pos ht, dif_pos ht]
  rfl

/-- sup-norm bound from pointwise bounds on `[0,T]` -/
lemma p_wj4_norm_le {m T : ℝ} (w : PathSpace d m T) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖pathAt w t‖ ≤ K) : ‖w‖ ≤ K := by
  show ‖(w : C(Set.Icc (0 : ℝ) T, NegSobolev d m))‖ ≤ K
  refine (ContinuousMap.norm_le _ hK).2 ?_
  intro x
  have := h x.1 x.2
  unfold pathAt at this
  rw [dif_pos x.2] at this
  exact this

/-- `polyAt` is linear in the node family -/
lemma p_wj4_polyAt_sub {m : ℝ} (c c' : ℝ) (n : ℕ) (v v' : ℕ → NegSobolev d m) (t : ℝ) :
    polyAt c c' n (fun i => v i - v' i) t = polyAt c c' n v t - polyAt c c' n v' t := by
  unfold polyAt
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_sub]

end P4Helpers

section Packets

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}

theorem p4_polyMix_bounds (sd : StatDatum S β₀ m hE) (G : ℝ) (hG : 0 < G) :
    ∃ C₁ Cw κ : ℝ, 1 ≤ C₁ ∧ 0 ≤ Cw ∧ 0 < κ ∧ ∀ (b : ℝ) (hb : 0 ≤ b) (c c' : ℝ), 0 ≤ c → c < c' → c' ≤ G →
      ∀ (n : ℕ) (v v' : ℕ → NegSobolev d m) (b₁ b₂ : ℝ),
        (∀ i ≤ 2 ^ n, ‖v i - v' i‖ ≤ b₁) → (∀ i ≤ 2 ^ n, ‖v' i‖ ≤ b₂) →
        ‖polyPathMix (Rp sd b hb).D (Rs sd b hb).D (Rp sd b hb).ρ (Rs sd b hb).ρ m G c c' n v v'‖ ≤
          C₁ * b₁ + Cw * Real.exp (-κ * (b + c')) * b₂ ∧
        ∀ B : ℝ, (∀ k < 2 ^ (n + 1), ‖(v (k + 1) - v' (k + 1)) - (v k - v' k)‖ ≤ B) →
          ‖polyPathMix (Rp sd b hb).D (Rs sd b hb).D (Rp sd b hb).ρ (Rs sd b hb).ρ m G c c' (n + 1) v v' -
              polyPathMix (Rp sd b hb).D (Rs sd b hb).D (Rp sd b hb).ρ (Rs sd b hb).ρ m G c c' n
                (fun i => v (2 * i)) (fun i => v' (2 * i))‖ ≤ B := by
  have hm : 3 * (d : ℝ) + 8 < m := hE.m_gt
  obtain ⟨C, c0, κ, hC, hc0, hκ, hP1⟩ := p1_vprop_compare_op sd m (rLvl_le hE)
  obtain ⟨Cp, hCp1, hpolyP⟩ := HRS.MC.E213J.e213j_poly (regime S β₀ hE) m hm G hG
  obtain ⟨Cs, hCs1, hpolyS⟩ := HRS.MC.E213J.e213j_poly (regime sd.Ss S.β sd.hEs) m hm G hG
  obtain ⟨k0, hk1, hk2, hk3, hkst, -⟩ := HRS.MC.Sec7.S7PIDV.S7PIDV_hyp (regime S β₀ hE) m hm 1 one_pos
  obtain ⟨L, Ac, Am, Cb, hL, hAc, hAm1, hCb, hU⟩ :=
    HRS.MC.E213I.e213i_V_unif_shift (regime S β₀ hE) k0 hk1 hkst m hk2 hk3 G hG
  obtain ⟨Rg, MB, Λ, VB, ν₀, hbundle⟩ := HRS.MC.E213F.adjointData_uniform (regime S β₀ hE) (k0 + 3)
  have hd1 : 1 ≤ d := by have := (regime S β₀ hE).hd; omega
  have hn₀ : 1 ≤ k0 + 2 := by omega
  have hJ : k0 + 2 + 1 ≤ k0 + 3 := le_rfl
  have hm0 : ((k0 + 2 : ℕ) : ℝ) < m := by push_cast; exact hk2
  have hm1 : m ≤ ((k0 + 2 : ℕ) : ℝ) + 1 := by push_cast; linarith
  refine ⟨max 1 Cb, C, κ, le_max_left _ _, hC.le, hκ, ?_⟩
  intro b hb c c' hc hcc hc'G n v v' b₁ b₂ h1 h2
  have hc'0 : 0 ≤ c' := hc.trans hcc.le
  have H : HRS.MC.Sec7.PIE.PIEHyp (k0 + 3) (Rp sd b hb).D (Rp sd b hb).ρ G :=
    ⟨hd1, by omega, Rg, MB, Λ, VB, ν₀, hbundle G hG b hb⟩
  obtain ⟨hpa, -, -⟩ := hpolyP b hb c c' hc hcc.le hc'G n v
  obtain ⟨hsa, -, -⟩ := hpolyS b hb c c' hc hcc.le hc'G n v'
  have hb₁ : 0 ≤ b₁ := (norm_nonneg _).trans (h1 0 (Nat.zero_le _))
  have hb₂ : 0 ≤ b₂ := (norm_nonneg _).trans (h2 0 (Nat.zero_le _))
  have hCb1 : (0 : ℝ) ≤ max 1 Cb := zero_le_one.trans (le_max_left _ _)
  refine ⟨?_, ?_⟩
  · have hK0 : 0 ≤ max 1 Cb * b₁ + C * Real.exp (-κ * (b + c')) * b₂ := by positivity
    refine p_wj4_norm_le _ _ hK0 ?_
    intro t ht
    unfold polyPathMix
    rw [p_wj4_pathAt_sub _ _ t ht, hpa hcc t ht, hsa hcc t ht]
    by_cases hle : t ≤ c'
    · simp only [if_pos hle]
      rw [← p_wj4_polyAt_sub]
      have h3 := HRS.MC.Sec7.S7PIDP.S7PIDP_polyAt_norm c c' t hc hcc.le n (fun i => v i - v' i) b₁ hb₁ h1
      have h4 : b₁ ≤ max 1 Cb * b₁ := le_mul_of_one_le_left hb₁ (le_max_left _ _)
      have h5 : 0 ≤ C * Real.exp (-κ * (b + c')) * b₂ := by positivity
      linarith
    · simp only [if_neg hle]
      have hlt : c' ≤ t := (not_le.1 hle).le
      have hV : ‖Vprop (Rp sd b hb).D (Rp sd b hb).ρ m t c' (v (2 ^ n) - v' (2 ^ n))‖ ≤
          Cb * ‖v (2 ^ n) - v' (2 ^ n)‖ := (hU b hb c' c' t hc'0 le_rfl hlt ht.2).2.1 _
      have hW := hP1 b hb c' t hc'0 hlt (v' (2 ^ n))
      have e : Vprop (Rp sd b hb).D (Rp sd b hb).ρ m t c' (v (2 ^ n)) -
            Vprop (Rs sd b hb).D (Rs sd b hb).ρ m t c' (v' (2 ^ n)) =
          Vprop (Rp sd b hb).D (Rp sd b hb).ρ m t c' (v (2 ^ n) - v' (2 ^ n)) +
          (Vprop (Rp sd b hb).D (Rp sd b hb).ρ m t c' (v' (2 ^ n)) -
            Vprop (Rs sd b hb).D (Rs sd b hb).ρ m t c' (v' (2 ^ n))) := by
        rw [HRS.MC.Sec7.S7PIDN.S7PIDN_Vprop_sub H m (k0 + 2) hn₀ hJ hm0 hm1 t ⟨by linarith, ht.2⟩ c'
          ⟨hc'0, hlt⟩]
        abel
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · calc _ ≤ Cb * ‖v (2 ^ n) - v' (2 ^ n)‖ := hV
          _ ≤ Cb * b₁ := mul_le_mul_of_nonneg_left (h1 _ le_rfl) hCb
          _ ≤ max 1 Cb * b₁ := mul_le_mul_of_nonneg_right (le_max_right _ _) hb₁
      · have hex : Real.exp (-c0 * (t - c')) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith
        have hex2 : 0 ≤ Real.exp (-κ * (b + c')) := (Real.exp_pos _).le
        calc _ ≤ C * Real.exp (-c0 * (t - c')) * Real.exp (-κ * (b + c')) * ‖v' (2 ^ n)‖ := hW
          _ ≤ C * 1 * Real.exp (-κ * (b + c')) * b₂ := by
            gcongr
            · exact h2 _ le_rfl
          _ = _ := by ring
  · intro B hB
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (pow_pos (by norm_num) _))
    refine p_wj4_norm_le _ _ hB0 ?_
    intro t ht
    obtain ⟨hpa1, -, -⟩ := hpolyP b hb c c' hc hcc.le hc'G (n + 1) v
    obtain ⟨hsa1, -, -⟩ := hpolyS b hb c c' hc hcc.le hc'G (n + 1) v'
    obtain ⟨hpa0, -, -⟩ := hpolyP b hb c c' hc hcc.le hc'G n (fun i => v (2 * i))
    obtain ⟨hsa0, -, -⟩ := hpolyS b hb c c' hc hcc.le hc'G n (fun i => v' (2 * i))
    unfold polyPathMix
    rw [p_wj4_pathAt_sub _ _ t ht, p_wj4_pathAt_sub _ _ t ht, p_wj4_pathAt_sub _ _ t ht,
      hpa1 hcc t ht, hsa1 hcc t ht, hpa0 hcc t ht, hsa0 hcc t ht]
    by_cases hle : t ≤ c'
    · simp only [if_pos hle]
      have h3 := HRS.MC.Sec7.S7PIDP.S7PIDP_polyAt_refine c c' hc hcc n (fun i => v i - v' i) t B hB0 hB
      have e : polyAt c c' (n + 1) v t - polyAt c c' (n + 1) v' t -
          (polyAt c c' n (fun i => v (2 * i)) t - polyAt c c' n (fun i => v' (2 * i)) t) =
          polyAt c c' (n + 1) (fun i => v i - v' i) t -
            polyAt c c' n (fun i => (fun j => v j - v' j) (2 * i)) t := by
        rw [p_wj4_polyAt_sub, show (fun i => (fun j => v j - v' j) (2 * i)) =
          (fun i => v (2 * i) - v' (2 * i)) from rfl, p_wj4_polyAt_sub]
      rw [e]
      exact h3
    · simp only [if_neg hle]
      show ‖Vprop (Rp sd b hb).D (Rp sd b hb).ρ m t c' (v (2 ^ (n + 1))) -
          Vprop (Rs sd b hb).D (Rs sd b hb).ρ m t c' (v' (2 ^ (n + 1))) -
          (Vprop (Rp sd b hb).D (Rp sd b hb).ρ m t c' (v (2 * 2 ^ n)) -
          Vprop (Rs sd b hb).D (Rs sd b hb).ρ m t c' (v' (2 * 2 ^ n)))‖ ≤ B
      rw [show 2 * 2 ^ n = 2 ^ (n + 1) by ring, sub_self, norm_zero]
      exact hB0

end Packets

end HRS.MC.WinJ

end
