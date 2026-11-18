import HRS.MS.Fp81S21BlockValue12

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas HRS.MS.GenPath

/-- Exact shifted evaluation on finite-combination observations. -/
theorem fp81s21_blockValue_eval_combo
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + H →
      ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ,
        IsR2DualCombo m φ → IsR2DualCombo m ψ →
        propagatorW C u t (φ + c • ψ) = propagatorW C u t φ + c • propagatorW C u t ψ)
    {I : Set ℝ} (hI : MeasurableSet I) (k : ℕ)
    {ta tb : ℝ} (hta : ta ∈ Icc (0 : ℝ) H) (htb : tb ∈ Icc (0 : ℝ) H)
    (Sa Sb : Finset (MultiIndex d)) (ca cb : MultiIndex d → ℝ)
    (l₁ l₂ : StrongDual ℝ (OscPath d m H))
    (h₁ : ∀ w, l₁ w = OscDual.eval (r2PathAt w ta)
      (fun x => ∑ α ∈ Sa, ca α * oscTestFun m α x))
    (h₂ : ∀ w, l₂ w = OscDual.eval (r2PathAt w tb)
      (fun x => ∑ α ∈ Sb, cb α * oscTestFun m α x)) :
    ((fp81s21_blockValue D I k : projTensor (OscPath d m H) 2) :
      TensorDual (OscPath d m H) 2)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l₁, l₂]) =
    2 * C.ν * ∫ v in (Icc (k : ℝ) ((k : ℝ) + 1) ∩ I) ∩
        Icc (0 : ℝ) (min (a + ta) (a + tb)),
      z v (fun x => inner ℝ
        (gradient (propagatorW C v (a + ta) (fun y => ∑ α ∈ Sa, ca α * oscTestFun m α y)) x)
        (gradient (propagatorW C v (a + tb) (fun y => ∑ α ∈ Sb, cb α * oscTestFun m α y)) x)) := by
  let L := fun s => fp81s21_windowLocalD I k C m H a z D.fp81s21_ha (le_of_lt D.fp81s21_hH) s
  let Pa := s101Pc m H ta Sa ca
  let Qa := s101Qc m H Sa ca
  let Pb := s101Pc m H tb Sb cb
  let Qb := s101Qc m H Sb cb
  let θa := fp81s21_blockClock a k ⟨ta, hta⟩
  let θb := fp81s21_blockClock a k ⟨tb, htb⟩
  let F := fun v => 2 * C.ν * z v (fun x => inner ℝ
    (gradient (propagatorW C v (a + ta) (fun y => ∑ α ∈ Sa, ca α * oscTestFun m α y)) x)
    (gradient (propagatorW C v (a + tb) (fun y => ∑ α ∈ Sb, cb α * oscTestFun m α y)) x))
  let S := (I ∩ Icc (0 : ℝ) (a + H)) ∩ Iic (a + ta) ∩ Iic (a + tb)
  have hS : MeasurableSet S := ((hI.inter measurableSet_Icc).inter measurableSet_Iic).inter measurableSet_Iic
  have hset : Icc (k : ℝ) ((k : ℝ) + 1) ∩ S =
      (Icc (k : ℝ) ((k : ℝ) + 1) ∩ I) ∩ Icc (0 : ℝ) (min (a + ta) (a + tb)) := by
    ext v
    simp only [S, mem_inter_iff, mem_Icc, mem_Iic, le_min_iff]
    constructor
    · rintro ⟨hB, ⟨⟨⟨hI, ⟨h0, hH⟩⟩, ha⟩, hb⟩⟩
      exact ⟨⟨hB, hI⟩, h0, ha, hb⟩
    · rintro ⟨⟨hB, hI⟩, h0, ha, hb⟩
      have hvH : v ≤ a + H := by linarith [hta.2]
      exact ⟨hB, ⟨⟨⟨hI, h0, hvH⟩, ha⟩, hb⟩⟩
  have hp : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) 1)), s ∈ Ioc (0 : ℝ) 1 := by
    rw [← Measure.restrict_congr_set (Ioc_ae_eq_Icc : Ioc (0 : ℝ) 1 =ᵐ[volume] Icc 0 1)]
    exact ae_restrict_mem measurableSet_Ioc
  rw [fp81s21_blockValue_obs_four D hI k hta htb Sa Sb ca cb l₁ l₂ h₁ h₂]
  change (∫ s in Icc (0 : ℝ) 1, L s Pa Pb) +
    (∫ s in Icc (0 : ℝ) (θb : ℝ), L s Pa Qb) +
    (∫ s in Icc (0 : ℝ) (θa : ℝ), L s Qa Pb) +
    (∫ s in Icc (0 : ℝ) (min (θa : ℝ) (θb : ℝ)), L s Qa Qb) = _
  rw [fp81s21_blockValue_four_sum L Pa Qa Pb Qb θa θb
    (fp81s21_windowLocal_entry_integrable D hI k Pa Pb)
    (fp81s21_windowLocal_entry_integrable D hI k Pa Qb)
    (fp81s21_windowLocal_entry_integrable D hI k Qa Pb)
    (fp81s21_windowLocal_entry_integrable D hI k Qa Qb)]
  calc
    _ = ∫ s in Icc (0 : ℝ) 1, S.indicator F ((k : ℝ) + s) := by
      apply integral_congr_ae
      filter_upwards [hp, fp81s21_windowLocal_cutoff_gradient_ae D hlin (I := I) k hta htb Sa Sb ca cb] with s hs hcut
      have ha' := fp81s21_blockClock_cutoff_iff (a := a) k hta hs
      have hb' := fp81s21_blockClock_cutoff_iff (a := a) k htb hs
      simp only [θa, θb, ← ha', ← hb']
      simpa [L, Pa, Qa, Pb, Qb, S, F, Set.indicator, and_assoc] using hcut
    _ = ∫ v in Icc (k : ℝ) ((k : ℝ) + 1) ∩ S, F v := fp81s21_blockValue_integral_shift F S hS k
    _ = _ := by rw [hset, integral_const_mul]

#print axioms fp81s21_blockValue_eval_combo
end HRS.Fp81.S21
end
