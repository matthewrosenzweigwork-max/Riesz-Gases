import HRS.MC.E213U10O

/-!
# Packet e213u10, part P: almost-sure identification of the Gaussian integrals with the pair-space functionals

For `gd : GaussData`, `0 ≤ b ≤ a`, `a + T ≤ b + L`:

* `u10_gauss_A`: a.s. `rsA(Z^{a+T}; near_b ℬ) = FD(η^{b,L}, ℬ^{b,L})`;
* `u10_gauss_J`: a.s. `rsJ(Z^{a+T}; near_b η) = FJ(η^{b,L}, η^{b,L})`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U10

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ}

theorem u10_pathAt_epath (hE : EdgeworthHyp S β₀ m) (T : ℝ) (p : PathSpace d (rLvl d) T) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    pathAt (HRS.MD.EQInterp.epath (rLvl_le hE) T p) t = NegSobolev.embed m (pathAt p t) := by
  rw [u10_pathAt_eq _ ⟨t, ht⟩, u10_pathAt_eq _ ⟨t, ht⟩]
  exact HRS.MD.EQInterp.epath_at' (rLvl_le hE) T p ⟨t, ht⟩

theorem u10_cont_shift {Ω : Type} {r : ℝ} (η : ℝ → Ω → NegSobolev d r) (ω : Ω) (c T H : ℝ) (hc0 : 0 ≤ c)
    (hH : c + T ≤ H) (hc : ContinuousOn (fun t => η t ω) (Set.Icc 0 H)) :
    Continuous fun t : Set.Icc (0 : ℝ) T => η (c + (t : ℝ)) ω := by
  have h1 : ContinuousOn (fun t : ℝ => η (c + t) ω) (Set.Icc 0 T) := by
    refine hc.comp (continuous_const.add continuous_id).continuousOn ?_
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact continuousOn_iff_continuous_restrict.1 h1

theorem u10_gauss_hW (hE : EdgeworthHyp S β₀ m) (gd : GaussData S β₀ hE) (T a b L : ℝ) (hb : 0 ≤ b) (hL : 0 ≤ L)
    (hH : a + T ≤ b + L) (ω : gd.Ω₀) (hc : ContinuousOn (fun t => gd.η t ω) (Set.Icc 0 (b + L))) :
    ∀ t ∈ Set.Icc b (a + T), pathAt (gd.Zwin (a + T) 0 ω) t =
      pathAt (u10_liftW hE b L (a + T) hL hH (procWin (rLvl d) L b gd.η ω)) t := by
  intro t ht
  have ht0 : t ∈ Set.Icc (0 : ℝ) (a + T) := ⟨hb.trans ht.1, ht.2⟩
  have htb : t - b ∈ Set.Icc (0 : ℝ) L := ⟨sub_nonneg.2 ht.1, by linarith [ht.2]⟩
  rw [u10_liftW_pathAt hE b L (a + T) hL hH _ ht0 ht.1]
  have e1 : pathAt (gd.Zwin (a + T) 0 ω) t = NegSobolev.embed m (gd.η (0 + t) ω) := by
    show pathAt (HRS.MD.EQInterp.epath (rLvl_le hE) (a + T) (procWin (rLvl d) (a + T) 0 gd.η ω)) t = _
    rw [u10_pathAt_epath hE (a + T) _ ht0]
    have e0 : pathAt (procWin (rLvl d) (a + T) 0 gd.η ω) t = gd.η (0 + t) ω := by
      show pathAt (toPath (rLvl d) (a + T) (fun t ω => gd.η (0 + t) ω) ω) t = _
      exact u10_pathAt_toPath (rLvl d) (a + T) (fun t ω => gd.η (0 + t) ω) ω
        (u10_cont_shift gd.η ω 0 (a + T) (b + L) le_rfl (by linarith) hc) ht0
    rw [e0]
  have e2 : pathAt (procWin (rLvl d) L b gd.η ω) (t - b) = gd.η (b + (t - b)) ω := by
    show pathAt (toPath (rLvl d) L (fun t ω => gd.η (b + t) ω) ω) (t - b) = _
    exact u10_pathAt_toPath (rLvl d) L (fun t ω => gd.η (b + t) ω) ω
      (u10_cont_shift gd.η ω b L (b + L) hb le_rfl hc) htb
  rw [e1, e2]
  have : (0 : ℝ) + t = b + (t - b) := by ring
  rw [this]

theorem u10_gauss_A (hE : EdgeworthHyp S β₀ m) (gd : GaussData S β₀ hE) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (b L : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (hL : 0 < L)
    (hH : a + T ≤ b + L) :
    ∀ᵐ ω ∂gd.P₀, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (nearCoef b (fun v => NegSobolev.embed m (gd.B v ω))) =
      u10_FD hE T a ha Φ b L hL.le hH (pairLim (rLvl d) L b gd.η gd.B ω) := by
  obtain ⟨Y₀, -, hsol⟩ := gd.limit
  have hcont := (hsol (b + L)).cont
  have hB := gd.B_L2 L hL b hb
  filter_upwards [hcont, hB] with ω hc hBω
  have hW0 := u10_gauss_hW hE gd T a b L hb hL.le hH ω hc
  exact u10_rsA_eq_FD hE T hT a ha Φ hΦ b L hb hba hL.le hH _ _ hW0 _ _
    (u10_cD_ae_eq hE T a b L hH (fun v => gd.B v ω) hBω _ (fun v => rfl))

theorem u10_gauss_J (hE : EdgeworthHyp S β₀ m) (gd : GaussData S β₀ hE) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (b L : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (hL : 0 < L)
    (hH : a + T ≤ b + L) :
    ∀ᵐ ω ∂gd.P₀, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (nearCoef b (fun v => NegSobolev.embed m (gd.η v ω))) =
      u10_GJ hE T a ha Φ b L hL.le hH 0 (pairLim (rLvl d) L b gd.η gd.B ω) := by
  obtain ⟨Y₀, -, hsol⟩ := gd.limit
  have hcont := (hsol (b + L)).cont
  filter_upwards [hcont] with ω hc
  have hW0 := u10_gauss_hW hE gd T a b L hb hL.le hH ω hc
  have key := u10_rsJ_eq_FJ hE T hT a ha Φ hΦ b L hb hba hL.le hH _ (procWin (rLvl d) L b gd.η ω) hW0 (nearCoef b (fun v => NegSobolev.embed m (gd.η v ω)))
    (procWin (rLvl d) L b gd.η ω) (by
      intro v hv0 hva
      unfold nearCoef u10_cJ nearCoef
      by_cases hbv : b ≤ v
      · simp only [if_pos hbv]
        have hvb : v - b ∈ Set.Icc (0 : ℝ) L := ⟨sub_nonneg.2 hbv, by linarith⟩
        congr 1
        unfold u10_zq
        have e : pathAt (procWin (rLvl d) L b gd.η ω) (v - b) = gd.η (b + (v - b)) ω := by
          show pathAt (toPath (rLvl d) L (fun t ω => gd.η (b + t) ω) ω) (v - b) = _
          exact u10_pathAt_toPath (rLvl d) L (fun t ω => gd.η (b + t) ω) ω
            (u10_cont_shift gd.η ω b L (b + L) hb le_rfl hc) hvb
        rw [e]
        have e2 : b + (v - b) = v := by ring
        rw [e2]
      · simp only [if_neg hbv])
  rw [key]
  show u10_FJ hE T a ha Φ b L hL.le hH (procWin (rLvl d) L b gd.η ω, procWin (rLvl d) L b gd.η ω) =
    u10_FJ hE T a ha Φ b L hL.le hH (procWin (rLvl d) L b gd.η ω, procWin (rLvl d) L b gd.η ω + 0)
  rw [add_zero]

end HRS.MC.E213U10

end
