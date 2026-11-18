import HRS.Equilibrium.Parametrix.PX4aAuxI
import HRS.Energy.Coercivity

/-!
# Packet PX4a auxiliaries J: left-chart sources, integrability and linearity of `kPot`
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The first-variable derivative kernel `ρ(x) ∂_{x_i} Ψ(x, y)`. -/
def Psii (ρ : Torus d → ℝ) (Ψ : Torus d → Torus d → ℝ) (i : Fin d) : Torus d → Torus d → ℝ :=
  fun x y => ρ x * Torus.partialDeriv i (fun z => Ψ z y) x

/-- The left chart `(Y, w) ↦ F(Y + w, Y)` of a kernel. -/
def leftCh (F : Torus d → Torus d → ℝ) : Euc d × Euc d → ℝ :=
  fun p => F (Torus.mk (p.1 + p.2)) (Torus.mk p.1)

/-- The near source: cutoff at `‖w‖ < 1/32`. -/
def Gsrc (F : Torus d → Torus d → ℝ) : Euc d × Euc d → ℝ :=
  fun p => px3a_zeta d (1 / 32) p.2 * leftCh F p

/-- The far source: the periodized complementary cutoff. -/
def Fsrc (F : Torus d → Torus d → ℝ) : Euc d × Euc d → ℝ :=
  fun p => (1 - perCut d (1 / 32) p.2) * leftCh F p

lemma leftCh_eq_shear (F : Torus d → Torus d → ℝ) (p : Euc d × Euc d) :
    leftCh F p = toChart F (shearCLM d (1 / 2 : ℝ) p) := by
  simp only [leftCh, toChart, shearCLM_apply]
  congr 2
  · module
  · module

lemma Gsrc_eq_shear (F : Torus d → Torus d → ℝ) :
    Gsrc F = fun p => (fun q : Euc d × Euc d => px3a_zeta d (1 / 32) q.2 * toChart F q)
      (shearCLM d (1 / 2 : ℝ) p) := by
  funext p
  simp only [Gsrc, leftCh_eq_shear, shearCLM_apply]

lemma toChart_periodic (F : Torus d → Torus d → ℝ) (X z n : Euc d) (hn : IsLat n) :
    toChart F (X + n, z) = toChart F (X, z) := by
  simp only [toChart]
  have h1 : X + n + (1 / 2 : ℝ) • z = (X + (1 / 2 : ℝ) • z) + n := by abel
  have h2 : X + n - (1 / 2 : ℝ) • z = (X - (1 / 2 : ℝ) • z) + n := by abel
  rw [h1, h2]
  simp only [mk_add_eq, mk_isLat hn, add_zero]

lemma leftCh_periodic (F : Torus d → Torus d → ℝ) (Y w n : Euc d) (hn : IsLat n) :
    leftCh F (Y + n, w) = leftCh F (Y, w) := by
  simp only [leftCh]
  have h1 : Y + n + w = (Y + w) + n := by abel
  rw [h1]
  simp only [mk_add_eq, mk_isLat hn, add_zero]

lemma Gsrc_periodic (F : Torus d → Torus d → ℝ) (Y w n : Euc d) (hn : IsLat n) :
    Gsrc F (Y + n, w) = Gsrc F (Y, w) := by
  simp only [Gsrc, leftCh_periodic F Y w n hn]

lemma leftCh_periodic_w (F : Torus d → Torus d → ℝ) (Y w n : Euc d) (hn : IsLat n) :
    leftCh F (Y, w + n) = leftCh F (Y, w) := by
  simp only [leftCh]
  have h1 : Y + (w + n) = (Y + w) + n := by abel
  rw [h1]
  simp only [mk_add_eq, mk_isLat hn, add_zero]

lemma perCut_periodic (r : ℝ) (v n : Euc d) (hn : IsLat n) : perCut d r (v + n) = perCut d r v := by
  unfold perCut
  rw [mk_add_eq, mk_isLat hn, add_zero]

lemma Fsrc_periodic_w (F : Torus d → Torus d → ℝ) (Y w n : Euc d) (hn : IsLat n) :
    Fsrc F (Y, w + n) = Fsrc F (Y, w) := by
  simp only [Fsrc, leftCh_periodic_w F Y w n hn, perCut_periodic _ w n hn]

lemma Fsrc_periodic (F : Torus d → Torus d → ℝ) (Y w n : Euc d) (hn : IsLat n) :
    Fsrc F (Y + n, w) = Fsrc F (Y, w) := by
  simp only [Fsrc, leftCh_periodic F Y w n hn]

/-- On the closed cube the periodized cutoff is the plain cutoff. -/
lemma perCut_eq_on_cube {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 4) (w : Euc d)
    (hw : ∀ i, |w i| ≤ 1 / 2) : perCut d r w = px3a_zeta d r w := by
  by_cases hs : ∀ i, |w i| < 1 / 2
  · unfold perCut
    rw [cR_mk_of_small _ hs]
  · push_neg at hs
    obtain ⟨i, hi⟩ := hs
    have hw1 : |w i| = 1 / 2 := le_antisymm (hw i) hi
    have hn : r ≤ ‖w‖ := by
      have := PiLp.norm_apply_le w i
      simp only [Real.norm_eq_abs] at this
      linarith
    rw [px3a_zeta_eq_zero hr hn]
    unfold perCut
    obtain ⟨n, hn', hc⟩ := cR_exists_lat w
    rw [hc]
    -- the `i`-th coordinate of `w - n` has absolute value `1/2`
    obtain ⟨k, hk⟩ := hn' i
    have hci : |(w - n) i| ≤ 1 / 2 := by
      have := px3a_abs_cR_le (Torus.mk w) i
      rwa [hc] at this
    have h2 : |(w - n) i| = 1 / 2 := by
      have e : (w - n) i = w i - k := by simp [hk]
      rw [e] at hci ⊢
      have hwi : w i = 1 / 2 ∨ w i = -(1 / 2) := by
        rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.mp hw1 with h | h
        · exact Or.inl h
        · exact Or.inr h
      rcases hwi with h | h
      · rw [h] at hci ⊢
        have hk1 : (k : ℝ) = 0 ∨ (k : ℝ) = 1 := by
          have h3 := abs_le.mp hci
          have : (0 : ℝ) ≤ k := by linarith [h3.1]
          have h5 : (k : ℝ) ≤ 1 := by linarith [h3.2]
          have h6 : 0 ≤ k := by exact_mod_cast this
          have h7 : k ≤ 1 := by exact_mod_cast h5
          interval_cases k <;> simp
        rcases hk1 with h0 | h0 <;> rw [h0] <;> norm_num
      · rw [h] at hci ⊢
        have hk1 : (k : ℝ) = 0 ∨ (k : ℝ) = -1 := by
          have h3 := abs_le.mp hci
          have h5 : (-1 : ℝ) ≤ k := by linarith [h3.2]
          have h6 : (k : ℝ) ≤ 0 := by linarith [h3.1]
          have h7 : -1 ≤ k := by exact_mod_cast h5
          have h8 : k ≤ 0 := by exact_mod_cast h6
          interval_cases k <;> simp
        rcases hk1 with h0 | h0 <;> rw [h0] <;> norm_num
    have : r ≤ ‖w - n‖ := by
      have := PiLp.norm_apply_le (w - n) i
      simp only [Real.norm_eq_abs] at this
      linarith
    exact px3a_zeta_eq_zero hr this

section Pot

variable {s : ℝ} {k : Euc d → ℝ}

lemma kernel_mul_src_zero (hk : LocKer d s k) {g : Euc d × Euc d → ℝ}
    (hz : ∀ X w : Euc d, 1 / 32 < ‖w‖ → g (X, w) = 0) (Y z : Euc d) (hzn : 1 / 16 ≤ ‖z‖) (w : Euc d) :
    k (z - w) * g (Y, w) = 0 := by
  by_cases hw : 1 / 32 < ‖w‖
  · simp [hz Y w hw]
  · have : 1 / 64 ≤ ‖z - w‖ := by
      have := norm_sub_norm_le z w
      linarith [not_lt.mp hw]
    simp [hk.supp _ this]

lemma kPot_integrable (hd : 1 ≤ d) (hk : LocKer d s k) {σ : ℝ} (hσ : σ < d) {b m : ℕ} {A : ℝ}
    (hA : 0 ≤ A) {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g)
    (hz : ∀ X w : Euc d, 1 / 32 < ‖w‖ → g (X, w) = 0) (Y z : Euc d) (hz0 : z ≠ 0) :
    Integrable (fun w => k (z - w) * g (Y, w)) := by
  by_cases hzr : ‖z‖ < 1 / 8
  · have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    obtain ⟨hn, hf, -⟩ := kPot_split hd hk hσ hA h hr hzr (z0 := z) rfl (p := (Y, z))
      (by simp; positivity)
    have hρ : 0 < ‖z‖ / 8 := by positivity
    have hn' : Integrable (fun w => kN k (‖z‖ / 8) (z - w) * g (Y, w)) := by
      have := hn.comp_sub_left z
      refine this.congr (Eventually.of_forall fun w => ?_)
      simp
    refine (hn'.add hf).congr (Eventually.of_forall fun w => ?_)
    show kN k (‖z‖ / 8) (z - w) * g (Y, w) + kF k (‖z‖ / 8) (z - w) * g (Y, w) = k (z - w) * g (Y, w)
    rw [← add_mul, kN_add_kF]
  · have : ∀ w, k (z - w) * g (Y, w) = 0 := fun w =>
      kernel_mul_src_zero hk hz Y z (by linarith [not_lt.mp hzr]) w
    simp only [this]
    exact integrable_zero _ _ _

lemma kPot_sum {ι : Type*} (hd : 1 ≤ d) (hk : LocKer d s k) {σ : ℝ} (hσ : σ < d) {b m : ℕ}
    (t : Finset ι) (A : ι → ℝ) (g : ι → Euc d × Euc d → ℝ) (hA : ∀ i ∈ t, 0 ≤ A i)
    (h : ∀ i ∈ t, SrcCls d σ b m (A i) (g i))
    (hz : ∀ i ∈ t, ∀ X w : Euc d, 1 / 32 < ‖w‖ → g i (X, w) = 0) (Y z : Euc d) (hz0 : z ≠ 0) :
    kPot d k (fun p => ∑ i ∈ t, g i p) (Y, z) = ∑ i ∈ t, kPot d k (g i) (Y, z) := by
  unfold kPot
  simp only [Finset.mul_sum]
  rw [integral_finset_sum]
  intro i hi
  exact kPot_integrable hd hk hσ (hA i hi) (h i hi) (hz i hi) Y z hz0

end Pot

end HRS.Parx

end
