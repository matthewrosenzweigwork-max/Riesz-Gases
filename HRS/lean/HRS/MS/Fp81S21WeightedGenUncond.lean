import HRS.MS.Fp81S21WeightedGenA
import HRS.MS.Fp81S21WeightedGenB
import HRS.MS.Fp81S21WeightedGenD
import HRS.MS.Fp81S21WeightedGenNL16

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.Ul HRS.MS.ProClosureS111

local notation "J" => iteratedFDeriv ℝ

/-- The B3 local-limit hypotheses needed by U4 follow from the dimension-generic
jet, convolution, and source-jet limit theorems. -/
theorem fp81s21_b3_nonlocal_all_tests_unconditional (p : Parameters) :
    ∀ B c : ℝ, 0 ≤ B → 0 < c →
      fp81s21_b3_nonlocal_all_tests_contract p B c := by
  intro B c hB hc
  have hd : 1 ≤ p.d := le_trans (by decide) p.hd
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hs1 : p.s + 1 < (p.d : ℝ) := by
    have hd2 : (2 : ℝ) ≤ p.d := by exact_mod_cast p.hd
    linarith [p.hs]
  have hA : ∀ {fn : ℕ → Euc p.d → ℝ} {g : Euc p.d → ℝ}
      {T : ∀ m : ℕ, Euc p.d → (Euc p.d [×m]→L[ℝ] ℝ)},
      (∀ n, ContDiff ℝ (fp81s21_b3_q p) (fn n)) →
      (∀ m ≤ fp81s21_b3_q p,
        TendstoLocallyUniformly (fun n => J m (fn n)) (T m) atTop) →
      (∀ x, Tendsto (fun n => fn n x) atTop (𝓝 (g x))) →
      ContDiff ℝ (fp81s21_b3_q p) g ∧
        ∀ m ≤ fp81s21_b3_q p, J m g = T m := by
    intro fn g T hC hlim hf
    exact fp81s21_b3_jets_limit_local (d := p.d) (k := fp81s21_b3_q p)
      hC hlim hf
  have hconv : ∀ j : Fin p.d, ∀ {F : Type}
      [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      {gn : ℕ → Euc p.d → F} {g : Euc p.d → F},
      (∀ n, Continuous (gn n)) → Continuous g →
      (∀ n, Integrable (gn n)) → Integrable g →
      TendstoLocallyUniformly gn g atTop →
      Tendsto (fun n => eLpNorm (gn n - g) 1 volume) atTop (𝓝 0) →
      TendstoLocallyUniformly
        (fun n => ultK (u2_kap p.d p.s j) (gn n))
        (ultK (u2_kap p.d p.s j) g) atTop := by
    intro j
    exact fp81s21_b3_ultK_tendsto_local hd
      (ult_ker_kap p.hs0 hsd j) hs1
  have hD : ∀ {gn : ℕ → Euc p.d → ℝ} {g : Euc p.d → ℝ}
      {H : Euc p.d → ℝ},
      (∀ n, ContDiff ℝ (fp81s21_b3_q p + 1) (gn n)) →
      ContDiff ℝ (fp81s21_b3_q p + 1) g →
      Continuous H → Integrable H → (∀ x, 0 ≤ H x) →
      (∀ n m, m ≤ fp81s21_b3_q p + 1 → ∀ x,
        ‖J m (gn n) x‖ ≤ H x) →
      (∀ m, m ≤ fp81s21_b3_q p + 1 → ∀ x, ‖J m g x‖ ≤ H x) →
      (∀ x, ∀ᶠ n in atTop, ∀ m ≤ fp81s21_b3_q p,
        J m (gn n) x = J m g x) →
      ∀ m ≤ fp81s21_b3_q p,
        TendstoLocallyUniformly (fun n => J m (gn n)) (J m g) atTop ∧
        Tendsto (fun n => eLpNorm (J m (gn n) - J m g) 1 volume)
          atTop (𝓝 0) := by
    intro gn g H hcn hc hHc hHi hH0 hbn hb heq
    exact fp81s21_b3_source_jet_limits (d := p.d) (k := fp81s21_b3_q p)
      hcn hc hHc hHi hH0 hbn hb heq
  exact fp81s21_b3_nonlocal_all_tests p B c hB hc hA hconv hD

#print axioms HRS.Fp81.S21.fp81s21_b3_nonlocal_all_tests_unconditional

end HRS.Fp81.S21
