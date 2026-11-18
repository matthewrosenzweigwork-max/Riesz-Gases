import HRS.Equilibrium.Parametrix.PX4aAuxH

/-!
# Packet PX4a auxiliaries I: periodized cutoffs and the smooth part `Λ` of the Riesz kernel

`perCut r v = ζ_r(centeredRep (mk v))` is the periodization of the radial cutoff;
`Lam = (1 - perCut_{1/128}) g` is a smooth periodic function with bounded derivatives, and
`g(z - w) = rieszK(z - w) + Lam(z - w)` for `|z_i| ≤ 1/2 + 1/64`, `‖w‖ < 1/32`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The periodized cutoff `ζ_r ∘ centeredRep ∘ mk`. -/
def perCut (d : ℕ) (r : ℝ) (v : Euc d) : ℝ := px3a_zeta d r (Torus.centeredRep (Torus.mk v))

lemma mk_sub_isLat (v n : Euc d) (hn : IsLat n) : Torus.mk (v - n) = Torus.mk v := by
  rw [mk_sub_eq, mk_isLat hn, sub_zero]

lemma perCut_eq_of_small (r : ℝ) (v n : Euc d) (hn : IsLat n) (h : ∀ i, |(v - n) i| < 1 / 2) :
    perCut d r v = px3a_zeta d r (v - n) := by
  unfold perCut
  rw [← mk_sub_isLat v n hn, cR_mk_of_small _ h]

lemma perCut_contDiff {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 4) (N : ℕ∞) : ContDiff ℝ N (perCut d r) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  obtain ⟨n, hn, hc⟩ := cR_exists_lat v
  by_cases hcn : ‖v - n‖ < 1 / 2
  · set δ : ℝ := (1 / 2 - ‖v - n‖) / 2 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    have hev : perCut d r =ᶠ[𝓝 v] fun v' => px3a_zeta d r (v' - n) := by
      filter_upwards [Metric.ball_mem_nhds v hδ0] with v' hv'
      have h1 : ‖v' - n‖ < 1 / 2 := by
        have := norm_sub_le_norm_sub_add_norm_sub v' v n
        rw [mem_ball_iff_norm] at hv'
        linarith
      exact perCut_eq_of_small r v' n hn (fun i => lt_of_le_of_lt (by
        have := PiLp.norm_apply_le (v' - n) i
        simpa [Real.norm_eq_abs] using this) h1)
    exact ((px3a_zeta_contDiff (d := d) r N).comp (contDiff_id.sub contDiff_const)).contDiffAt.congr_of_eventuallyEq hev
  · have hcn' : 1 / 2 ≤ ‖v - n‖ := not_lt.mp hcn
    have hev : perCut d r =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds v (by norm_num : (0 : ℝ) < 1 / 8)] with v' hv'
      by_contra hne
      have hz : px3a_zeta d r (Torus.centeredRep (Torus.mk v')) ≠ 0 := hne
      have hlt : ‖Torus.centeredRep (Torus.mk v')‖ < r := by
        by_contra hge
        exact hz (px3a_zeta_eq_zero hr (not_lt.mp hge))
      obtain ⟨n', hn', hc'⟩ := cR_exists_lat v'
      rw [hc'] at hlt
      have h1 := norm_cR_le v n' hn'
      rw [hc] at h1
      have h2 : ‖v - n'‖ ≤ ‖v - v'‖ + ‖v' - n'‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub v v' n'
        exact this
      rw [mem_ball_iff_norm, norm_sub_rev] at hv'
      have h3 : ‖v - n‖ ≤ ‖v - n'‖ := by
        have := norm_cR_le v n' hn'
        rwa [hc] at this
      linarith
    exact contDiffAt_const.congr_of_eventuallyEq hev

lemma perCut_eq_zeta (z w : Euc d) (hz : ∀ i, |z i| ≤ 1 / 2 + 1 / 64) (hw : ‖w‖ < 1 / 32) :
    perCut d (1 / 128) (z - w) = px3a_zeta d (1 / 128) (z - w) := by
  have hwi : ∀ i, |w i| < 1 / 32 := fun i => lt_of_le_of_lt (by
    have := PiLp.norm_apply_le w i
    simpa [Real.norm_eq_abs] using this) hw
  have hvi : ∀ i, |(z - w) i| ≤ 1 / 2 + 3 / 64 := fun i => by
    have h1 := hz i
    have h2 := hwi i
    simp only [PiLp.sub_apply]
    calc |z i - w i| ≤ |z i| + |w i| := abs_sub _ _
      _ ≤ _ := by linarith
  by_cases hv : ‖z - w‖ < 1 / 128
  · have hs : ∀ i, |(z - w) i| < 1 / 2 := fun i => lt_of_le_of_lt (by
      have := PiLp.norm_apply_le (z - w) i
      simpa [Real.norm_eq_abs] using this) (by linarith)
    unfold perCut
    rw [cR_mk_of_small _ hs]
  · have hv' : 1 / 128 ≤ ‖z - w‖ := not_lt.mp hv
    rw [px3a_zeta_eq_zero (by norm_num) hv']
    unfold perCut
    obtain ⟨n, hn, hc⟩ := cR_exists_lat (z - w)
    rw [hc]
    by_contra hne
    have hlt : ‖z - w - n‖ < 1 / 128 := by
      by_contra hge
      exact hne (px3a_zeta_eq_zero (by norm_num) (not_lt.mp hge))
    have hn0 : n = 0 := by
      ext i
      obtain ⟨k, hk⟩ := hn i
      have h1 : |(z - w - n) i| < 1 / 128 := lt_of_le_of_lt (by
        have := PiLp.norm_apply_le (z - w - n) i
        simpa [Real.norm_eq_abs] using this) hlt
      have h2 : |(k : ℝ)| < 1 := by
        rw [← hk]
        have h3 := hvi i
        have : n i = (z - w) i - (z - w - n) i := by simp
        rw [this]
        calc |(z - w) i - (z - w - n) i| ≤ |(z - w) i| + |(z - w - n) i| := abs_sub _ _
          _ < 1 := by linarith
      have h4 : k = 0 := by
        have : |k| < 1 := by exact_mod_cast h2
        exact abs_lt.mp this |> fun h => by omega
      simp [hk, h4]
    rw [hn0, sub_zero] at hlt
    exact hv hlt

/-- The smooth part `(1 - perCut_{1/128}) g` of the Riesz kernel (periodic). -/
def Lam (d : ℕ) (s : ℝ) (v : Euc d) : ℝ :=
  (1 - perCut d (1 / 128) v) * periodicRiesz d s (Torus.mk v)

lemma ghat_split {s : ℝ} (z w : Euc d) (hz : ∀ i, |z i| ≤ 1 / 2 + 1 / 64) (hw : ‖w‖ < 1 / 32) :
    periodicRiesz d s (Torus.mk (z - w)) = rieszK d s (z - w) + Lam d s (z - w) := by
  unfold rieszK Lam
  rw [perCut_eq_zeta z w hz hw]
  ring

lemma Lam_contDiff (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (N : ℕ∞) :
    ContDiff ℝ N (Lam d s) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hm : Torus.mk v = 0
  · have hl : IsLat v := mk_eq_zero_imp hm
    have hev : Lam d s =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds v (by norm_num : (0 : ℝ) < 1 / 256)] with v' hv'
      have h1 : ‖v' - v‖ < 1 / 256 := by rwa [mem_ball_iff_norm] at hv'
      have hs : ∀ i, |(v' - v) i| < 1 / 2 := fun i => lt_of_le_of_lt (by
        have := PiLp.norm_apply_le (v' - v) i
        simpa [Real.norm_eq_abs] using this) (by linarith)
      have : perCut d (1 / 128) v' = 1 := by
        rw [perCut_eq_of_small _ v' v hl hs]
        exact px3a_zeta_eq_one (by norm_num) (by linarith)
      show (1 - perCut d (1 / 128) v') * periodicRiesz d s (Torus.mk v') = 0
      rw [this]; ring
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hg : ContDiffAt ℝ (N : WithTop ℕ∞) (Torus.lift (periodicRiesz d s)) v :=
      ((KernelGrad.contDiffOn_periodicRiesz hd hs0 hsd).contDiffAt
        (isOpen_mk_ne_zero'.mem_nhds hm)).of_le (by exact_mod_cast le_top)
    exact (contDiffAt_const.sub (perCut_contDiff (by norm_num) (by norm_num) N).contDiffAt).mul hg

lemma Lam_periodic {s : ℝ} (v : Euc d) (n : Euc d) (hn : IsLat n) : Lam d s (v + n) = Lam d s v := by
  unfold Lam perCut
  have : Torus.mk (v + n) = Torus.mk v := by rw [mk_add_eq, mk_isLat hn, add_zero]
  rw [this]

lemma Lam_bdd (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : Euc d, ‖iteratedFDeriv ℝ n (Lam d s) y‖ ≤ M := by
  have : Lam d s = Torus.lift (fun x : Torus d => (1 - px3a_zeta d (1 / 128) (Torus.centeredRep x)) *
      periodicRiesz d s x) := rfl
  rw [this]
  exact bdd_iteratedFDeriv_lift _ n (by
    rw [← this]; exact_mod_cast Lam_contDiff hd hs0 hsd (n : ℕ∞))

end HRS.Parx

end
