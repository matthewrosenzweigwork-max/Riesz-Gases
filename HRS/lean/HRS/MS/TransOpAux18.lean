import HRS.MS.TransOpAux17

/-!
# S611 packet P4d: propagator and noise covariance under translation (continued)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- Uniqueness of classical adjoint solutions for the stationary coefficients (the hypothesis of the propagator conjugation). -/
def s611_Uniq (d : ℕ) (s q β : ℝ) (ρβ : Euc d → ℝ) (T : ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ),
    IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) t φ f →
    ∀ r ∈ Set.Icc (0 : ℝ) t,
      propagatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) r t φ = f r

theorem s611_adjoint_from_tr' (s q β : ℝ) (ρβ : Euc d → ℝ) (b : Euc d) {t : ℝ} {φ : Euc d → ℝ}
    {g : ℝ → Euc d → ℝ}
    (h : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff (movTranslatedDensity q b ρβ)) t
      (fun x => φ (x - movShift q b t)) g) :
    IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) t φ
      (fun r x => g r (x - -movShift q b r)) := by
  have h1 := s611_adjoint_from_tr s q β ρβ b h
  convert h1 using 2
  all_goals simp

theorem s611_propagator_shift (s q β : ℝ) (ρβ : Euc d → ℝ) (b : Euc d) (T : ℝ)
    (huniq : s611_Uniq d s q β ρβ T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (φ : Euc d → ℝ)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) :
    propagatorW ((quadraticGradientDyn d s q β).coeff (movTranslatedDensity q b ρβ)) r t
        (fun x => φ (x - movShift q b t)) =
      fun x => propagatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) r t φ
        (x - movShift q b r) := by
  by_cases hex : ∃ f, IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) t φ f
  · obtain ⟨f, hf⟩ := hex
    have hfc := s611_adjoint_to_tr s q β ρβ b hf
    have hexT : ∃ g, IsClassicalAdjointW
        ((quadraticGradientDyn d s q β).coeff (movTranslatedDensity q b ρβ)) t
        (fun x => φ (x - movShift q b t)) g := ⟨_, hfc⟩
    have hP : propagatorW ((quadraticGradientDyn d s q β).coeff (movTranslatedDensity q b ρβ)) r t
        (fun x => φ (x - movShift q b t)) = hexT.choose r := by
      unfold propagatorW
      rw [dif_pos hexT]
    rw [hP]
    have hg := hexT.choose_spec
    have hg' := s611_adjoint_from_tr' s q β ρβ b hg
    have := huniq t ht φ _ hg' r hr
    funext x
    rw [this]
    simp
  · have hnex : ¬ ∃ g, IsClassicalAdjointW
        ((quadraticGradientDyn d s q β).coeff (movTranslatedDensity q b ρβ)) t
        (fun x => φ (x - movShift q b t)) g := by
      rintro ⟨g, hg⟩
      exact hex ⟨_, s611_adjoint_from_tr' s q β ρβ b hg⟩
    have e1 : propagatorW ((quadraticGradientDyn d s q β).coeff (movTranslatedDensity q b ρβ)) r t
        (fun x => φ (x - movShift q b t)) = 0 := by
      unfold propagatorW
      rw [dif_neg hnex]
    have e2 : propagatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) r t φ = 0 := by
      unfold propagatorW
      rw [dif_neg hex]
    rw [e1, e2]
    funext x
    rfl

theorem s611_gradient_sub (P : Euc d → ℝ) (c x : Euc d) :
    gradient (fun y => P (y - c)) x = gradient P (x - c) := by
  have := HRS.MS.A0.a0_gradient_comp_add P (-c) x
  simpa [sub_eq_add_neg] using this

theorem s611_noiseCov_shift (s q β : ℝ) (ρβ : Euc d → ℝ) (b : Euc d) (T : ℝ)
    (huniq : s611_Uniq d s q β ρβ T) (q' : ℝ) {t t' : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (ht' : t' ∈ Set.Icc (0 : ℝ) T) (φ φ' : Euc d → ℝ) :
    noiseCovW ((quadraticGradientDyn d s q β).coeff (movTranslatedDensity q b ρβ)) q' t t'
        (fun x => φ (x - movShift q b t)) (fun x => φ' (x - movShift q b t')) =
      noiseCovW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) q' t t' φ φ' := by
  unfold noiseCovW
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc (fun r hr => ?_)
  have hr1 : r ∈ Set.Icc (0 : ℝ) t := ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
  have hr2 : r ∈ Set.Icc (0 : ℝ) t' := ⟨hr.1, hr.2.trans (min_le_right _ _)⟩
  rw [s611_propagator_shift s q β ρβ b T huniq ht φ hr1, s611_propagator_shift s q β ρβ b T huniq ht' φ' hr2]
  simp only [s611_gradient_sub]
  exact integral_sub_right_eq_self (fun y => inner ℝ
    (gradient (propagatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) r t φ) y)
    (gradient (propagatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) r t' φ') y) * ρβ y)
    (movShift q b r)

end HRS.MS.TransOp

end
