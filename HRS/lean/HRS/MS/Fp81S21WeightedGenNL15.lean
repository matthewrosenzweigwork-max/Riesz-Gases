import HRS.MS.Fp81S21WeightedGenNL14
import HRS.MS.Fp81S21WeightedGenNL6

/-! Classical output jets for weighted tests via compact cutoffs. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.Ul HRS.MS.ProClosureS111

local notation "J" => iteratedFDeriv ℝ

/-- The compact-source convolution limits identify the output's classical jets. -/
theorem fp81s21_b3_output_jets_of_cutoff_source_energy {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) (u : ℝ) (f : Euc p.d → ℝ) (K : ℝ)
    (h : ℕ → Euc p.d → ℝ) {B c : ℝ}
    (hB0 : 0 ≤ B) (hc : 0 < c)
    (hdata : fp81s21_b3_Data R B c) (hu : 0 ≤ u)
    (hf : IsR2WeightedTest ((fp81s21_b3_q p) + 2) (fp81s21_b3_P p) f) (hK : 0 ≤ K)
    (hreg : ∀ n, IsR2WeightedTest ((fp81s21_b3_q p) + 2) (fp81s21_b3_P p) (h n) ∧ HasCompactSupport (h n))
    (hb : ∀ n x, ‖weightedJets ((fp81s21_b3_q p) + 2) (fp81s21_b3_P p) (h n) x‖ ≤ K * ‖weightedJets ((fp81s21_b3_q p) + 2) (fp81s21_b3_P p) f x‖)
    (heq : ∀ x, ∀ᶠ n in atTop, ∀ (j : Fin p.d) (m : ℕ),
      J m (fp81s21_b3_source R u (h n) j) x = J m (fp81s21_b3_source R u f j) x)
    (hA : ∀ {fn : ℕ → Euc p.d → ℝ} {g : Euc p.d → ℝ}
      {T : ∀ m : ℕ, Euc p.d → (Euc p.d [×m]→L[ℝ] ℝ)},
      (∀ n, ContDiff ℝ (fp81s21_b3_q p) (fn n)) →
      (∀ m ≤ (fp81s21_b3_q p), TendstoLocallyUniformly (fun n => J m (fn n)) (T m) atTop) →
      (∀ x, Tendsto (fun n => fn n x) atTop (𝓝 (g x))) →
      ContDiff ℝ (fp81s21_b3_q p) g ∧ ∀ m ≤ (fp81s21_b3_q p), J m g = T m)
    (hconv : ∀ j : Fin p.d, ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      {gn : ℕ → Euc p.d → F} {g : Euc p.d → F},
      (∀ n, Continuous (gn n)) → Continuous g → (∀ n, Integrable (gn n)) → Integrable g →
      TendstoLocallyUniformly gn g atTop →
      Tendsto (fun n => eLpNorm (gn n - g) 1 volume) atTop (𝓝 0) →
      TendstoLocallyUniformly (fun n => ultK (u2_kap p.d p.s j) (gn n))
        (ultK (u2_kap p.d p.s j) g) atTop)
    (hD : ∀ {gn : ℕ → Euc p.d → ℝ} {g : Euc p.d → ℝ} {H : Euc p.d → ℝ},
      (∀ n, ContDiff ℝ ((fp81s21_b3_q p) + 1) (gn n)) → ContDiff ℝ ((fp81s21_b3_q p) + 1) g →
      Continuous H → Integrable H → (∀ x, 0 ≤ H x) →
      (∀ n m, m ≤ (fp81s21_b3_q p) + 1 → ∀ x, ‖J m (gn n) x‖ ≤ H x) →
      (∀ m, m ≤ (fp81s21_b3_q p) + 1 → ∀ x, ‖J m g x‖ ≤ H x) →
      (∀ x, ∀ᶠ n in atTop, ∀ m ≤ (fp81s21_b3_q p), J m (gn n) x = J m g x) →
      ∀ m ≤ (fp81s21_b3_q p), TendstoLocallyUniformly (fun n => J m (gn n)) (J m g) atTop ∧
        Tendsto (fun n => eLpNorm (J m (gn n) - J m g) 1 volume) atTop (𝓝 0)) :
    ContDiff ℝ (fp81s21_b3_q p) (fp81s21_g4N p R u f) ∧
    ∀ x, Tendsto (fun n => weightedJets (fp81s21_b3_q p) (fp81s21_b3_P p) (fp81s21_g4N p R u (h n)) x) atTop
      (𝓝 (weightedJets (fp81s21_b3_q p) (fp81s21_b3_P p) (fp81s21_g4N p R u f) x)) := by
  let S := fp81s21_b3_source R u
  let V : (Euc p.d → ℝ) → Fin p.d → Euc p.d → ℝ := fun z j => ultK (u2_kap p.d p.s j) (S z j)
  have hd : 1 ≤ p.d := by have := p.hd; omega
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hL : (p.d : ℝ) < (p.d : ℝ) + 1 := by linarith
  have hs1 : p.s + 1 < (p.d : ℝ) := by
    have hd2 : (2 : ℝ) ≤ p.d := by exact_mod_cast p.hd
    linarith [p.hs]
  have hN : ∀ z, IsR2WeightedTest ((fp81s21_b3_q p) + 2) (fp81s21_b3_P p) z → fp81s21_g4N p R u z = fun x => ∑ j, V z j x := by
    intro z hz
    choose A hA' hdec using fp81s21_b3_all_test_source_decay p R u hu z hz
    funext x
    unfold fp81s21_g4N
    exact Finset.sum_congr rfl fun j _ => (ult_conv_comp hd p.hs0 hsd hL (hA' j) (hdec j) x).2 j
  have hsmooth : ∀ z, ContDiff ℝ ((fp81s21_b3_q p) + 2) z → ∀ j, ContDiff ℝ ((fp81s21_b3_q p) + 1) (S z j) := by
    intro z hz j
    obtain ⟨_, _, hρ, _⟩ := hdata u hu
    have hv : ContDiff ℝ ((fp81s21_b3_q p) + 1) (fun y => fderiv ℝ z y (ul1w (r26t3_coeff R).M j)) :=
      (hz.fderiv_right (by exact_mod_cast (show (fp81s21_b3_q p) + 2 ≤ (fp81s21_b3_q p) + 1 + 1 by omega))).clm_apply contDiff_const
    have he : S z j = fun y => R.ρ u y * fderiv ℝ z y (ul1w (r26t3_coeff R).M j) := by
      funext y
      simp only [S, fp81s21_b3_source, ul1_matVec]
    rw [he]
    exact (hρ.of_le (by exact_mod_cast (show (fp81s21_b3_q p) + 1 ≤ (fp81s21_b3_q p) + 2 by omega))).mul hv
  obtain ⟨H, hHc, hHi, hH2, hH0, hbound, hboundn⟩ :=
    fp81s21_b3_source_jet_envelope R u f K h hB0 hc hdata hu hf hK hreg hb
  have hsource : ∀ j m, m ≤ (fp81s21_b3_q p) → Integrable (J m (S f j)) := by
    intro j m hm
    exact hHi.mono' ((hsmooth f hf.1 j).continuous_iteratedFDeriv (by exact_mod_cast (show m ≤ (fp81s21_b3_q p) + 1 by omega))).aestronglyMeasurable
      (Filter.Eventually.of_forall (hbound j m (by omega)))
  have hlimit : ∀ j, ContDiff ℝ (fp81s21_b3_q p) (V f j) ∧ ∀ m ≤ (fp81s21_b3_q p),
      TendstoLocallyUniformly (fun n => J m (V (h n) j)) (J m (V f j)) atTop := by
    intro j
    have hdec : ∀ n, ∃ L A : ℝ, (p.d : ℝ) < L ∧ 0 ≤ A ∧ U2Dec ((fp81s21_b3_q p) + 1) L A (S (h n) j) := by
      intro n
      obtain ⟨A, hA', hh⟩ := fp81s21_b3_compact_source_decay p R B c hB0 hc hdata u hu (h n)
        (hreg n).1.1 (hreg n).2 (p.d + 1)
      exact ⟨p.d + 1, A, by push_cast; linarith, hA', by simpa only [Nat.cast_add, Nat.cast_one, S] using hh j⟩
    have ht := hD (fun n => hsmooth (h n) (hreg n).1.1 j) (hsmooth f hf.1 j) hHc hHi hH0
      (fun n m hm => hboundn n j m hm) (fun m hm => hbound j m hm)
      (fun x => (heq x).mono (fun n hn m hm => hn j m))
    obtain ⟨hcd, hl⟩ := fp81s21_b3_ultK_iter_limit hd (ult_ker_kap p.hs0 hsd j) hs1
      hA (hconv j) hdec ((hsmooth f hf.1 j).of_le (by exact_mod_cast (show (fp81s21_b3_q p) ≤ (fp81s21_b3_q p) + 1 by omega)))
      (hsource j) ht
    exact ⟨hcd, fun m hm => (hl m hm).2⟩
  have hncd : ∀ n j, ContDiff ℝ (fp81s21_b3_q p) (V (h n) j) := by
    intro n j
    obtain ⟨A, hA', hh⟩ := fp81s21_b3_compact_source_decay p R B c hB0 hc hdata u hu (h n)
      (hreg n).1.1 (hreg n).2 (p.d + 1)
    exact (ult_K_iter hd (ult_ker_kap p.hs0 hsd j) (by push_cast; linarith) hA' (hh j)).2
  have hcd : ContDiff ℝ (fp81s21_b3_q p) (fp81s21_g4N p R u f) := by
    rw [hN f hf]
    exact ContDiff.sum fun j _ => (hlimit j).1
  refine ⟨hcd, fp81s21_weightedJets_tendsto_of_iterated ?_⟩
  intro m hm x
  have hsum := tendsto_finset_sum (Finset.univ : Finset (Fin p.d)) (fun j _ =>
    ((hlimit j).2 m hm).tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ x))
  have hderiv : ∀ z, (∀ j, ContDiff ℝ (fp81s21_b3_q p) (V z j)) →
      J m (fun x => ∑ j, V z j x) x = ∑ j, J m (V z j) x := by
    intro z hz
    ext v
    rw [iteratedFDeriv_fun_sum_apply (fun j _ => ((hz j).of_le (by exact_mod_cast hm)).contDiffAt)]
  simpa only [hN f hf, hN (h _) (hreg _).1, hderiv f (fun j => (hlimit j).1),
    hderiv (h _) (hncd _)] using hsum

#print axioms HRS.Fp81.S21.fp81s21_b3_output_jets_of_cutoff_source_energy
end HRS.Fp81.S21
