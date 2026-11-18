import HRS.MS.FixEqP3Aux16

/-!
# S5.7 `fixed_equation` (worker S57P), part 29: norm, Lipschitz bound and pairing of the initial part
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ} {θ : Euc d → ℝ} {T : ℝ} {n : ℕ} {K : ℝ} {s : ℝ} {M Q : Matrix (Fin d) (Fin d) ℝ} {ν : ℝ}
  {c : ℝ → Euc d → Euc d} {ρ : ℝ → Euc d → ℝ} {A Λc νbar : ℝ} {m : ℝ} {J : ℕ} {Ca Cd : ℝ}
  {P : ℝ} {η : (Euc d → ℝ) → ℝ}

/-- the constant `‖η‖ C` -/
def s57pD (d n : ℕ) (P : ℝ) (η : (Euc d → ℝ) → ℝ) : ℝ := (dualNormE n P η).toReal * s57pC d n P

theorem s57pD_nonneg (d n : ℕ) (P : ℝ) (η : (Euc d → ℝ) → ℝ) : 0 ≤ s57pD d n P η :=
  mul_nonneg ENNReal.toReal_nonneg (s57pC_nonneg d n P)

theorem s57p_init_coord (hP : (d : ℝ) < 2 * P) (hη : IsBoundedLinearOnE n P η) (hdual : dualNormE n P η < ⊤)
    (hbd : S57pOrbBd (fixedEqCoeff s M Q ν c ρ) T n m J Ca Cd) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (α : MultiIndex d) :
    |η (propagatorW (fixedEqCoeff s M Q ν c ρ) 0 t (oscTestFun m α))| ≤
      s57pD d n P η * (Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) := by
  obtain ⟨hcl, hb⟩ := (hbd α).1 t ht
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht.1⟩
  have hc0 : ContDiff ℝ (n : WithTop ℕ∞) (propagatorW (fixedEqCoeff s M Q ν c ρ) 0 t (oscTestFun m α)) :=
    (hb 0 h0).1.of_le (by exact_mod_cast Nat.le_succ n)
  have := s57p_eta_bound hP hη hdual hc0
    (B := Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) (fun j hj x => (hb 0 h0).2 j (by omega) x)
  simpa [s57pD, mul_assoc] using this

theorem s57p_init_coord_lip (hP : (d : ℝ) < 2 * P) (hη : IsBoundedLinearOnE n P η) (hdual : dualNormE n P η < ⊤)
    (hbd : S57pOrbBd (fixedEqCoeff s M Q ν c ρ) T n m J Ca Cd) {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂)
    (h2T : t₂ ≤ T) (α : MultiIndex d) :
    |η (propagatorW (fixedEqCoeff s M Q ν c ρ) 0 t₂ (oscTestFun m α)) -
        η (propagatorW (fixedEqCoeff s M Q ν c ρ) 0 t₁ (oscTestFun m α))| ≤
      s57pD d n P η * (Cd * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) * (t₂ - t₁)) := by
  have ht1 : t₁ ∈ Set.Icc (0 : ℝ) T := ⟨h0, h12.trans h2T⟩
  have ht2 : t₂ ∈ Set.Icc (0 : ℝ) T := ⟨h0.trans h12, h2T⟩
  obtain ⟨-, hb1⟩ := (hbd α).1 t₁ ht1
  obtain ⟨-, hb2⟩ := (hbd α).1 t₂ ht2
  have h01 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t₁ := ⟨le_rfl, h0⟩
  have h02 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t₂ := ⟨le_rfl, h0.trans h12⟩
  have hc1 : ContDiff ℝ (n : WithTop ℕ∞) (propagatorW (fixedEqCoeff s M Q ν c ρ) 0 t₁ (oscTestFun m α)) :=
    (hb1 0 h01).1.of_le (by exact_mod_cast Nat.le_succ n)
  have hc2 : ContDiff ℝ (n : WithTop ℕ∞) (propagatorW (fixedEqCoeff s M Q ν c ρ) 0 t₂ (oscTestFun m α)) :=
    (hb2 0 h02).1.of_le (by exact_mod_cast Nat.le_succ n)
  have hB1 : ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (propagatorW (fixedEqCoeff s M Q ν c ρ) 0 t₁ (oscTestFun m α)) x‖ ≤
      Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := fun j hj x => (hb1 0 h01).2 j (by omega) x
  have hB2 : ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (propagatorW (fixedEqCoeff s M Q ν c ρ) 0 t₂ (oscTestFun m α)) x‖ ≤
      Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := fun j hj x => (hb2 0 h02).2 j (by omega) x
  rw [← s57p_eta_sub hP hη hc2 hc1 hB2 hB1]
  have := s57p_eta_bound hP hη hdual (hc2.sub hc1) (B := Cd * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) * (t₂ - t₁))
    (fun j hj x => (hbd α).2 t₁ t₂ h0 h12 h2T 0 h01 j hj x)
  simpa [s57pD, mul_assoc] using this

theorem s57p_init_lip (hP : (d : ℝ) < 2 * P) (hη : IsBoundedLinearOnE n P η) (hdual : dualNormE n P η < ⊤)
    (hbd : S57pOrbBd (fixedEqCoeff s M Q ν c ρ) T n m J Ca Cd) (hCa : 0 ≤ Ca) (hCd : 0 ≤ Cd) (a : ℝ)
    (hsum : Summable fun α : MultiIndex d => oscEigenvalue d α ^ ((J : ℝ) - m)) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, Memℓp (fun α => a * η (propagatorW (fixedEqCoeff s M Q ν c ρ) 0 t (oscTestFun m α))) 2 ∧
      ‖s57pI (fixedEqCoeff s M Q ν c ρ) m a η t‖ ^ 2 ≤
        (|a| * s57pD d n P η * Ca) ^ 2 * ∑' α : MultiIndex d, oscEigenvalue d α ^ ((J : ℝ) - m)) ∧
    ∀ t₁ ∈ Set.Icc (0 : ℝ) T, ∀ t₂ ∈ Set.Icc (0 : ℝ) T,
      ‖s57pI (fixedEqCoeff s M Q ν c ρ) m a η t₂ - s57pI (fixedEqCoeff s M Q ν c ρ) m a η t₁‖ ≤
        (|a| * s57pD d n P η * Cd * Real.sqrt (∑' α : MultiIndex d, oscEigenvalue d α ^ ((J : ℝ) - m))) * |t₂ - t₁| := by
  have hD := s57pD_nonneg d n P η
  have hsq : ∀ (C0 : ℝ) (α : MultiIndex d), (C0 * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) ^ 2 =
      C0 ^ 2 * oscEigenvalue d α ^ ((J : ℝ) - m) := by
    intro C0 α; rw [mul_pow, rpow_half_sq _ _ (oscEv_pos α)]
  have hS0 : 0 ≤ ∑' α : MultiIndex d, oscEigenvalue d α ^ ((J : ℝ) - m) :=
    tsum_nonneg fun α => (Real.rpow_pos_of_pos (oscEv_pos α) _).le
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) T, Memℓp (fun α => a * η (propagatorW (fixedEqCoeff s M Q ν c ρ) 0 t (oscTestFun m α))) 2 ∧
      ‖s57pI (fixedEqCoeff s M Q ν c ρ) m a η t‖ ^ 2 ≤
        (|a| * s57pD d n P η * Ca) ^ 2 * ∑' α : MultiIndex d, oscEigenvalue d α ^ ((J : ℝ) - m) := by
    intro t ht
    have key := s57p_ellVec_norm_sq (m := m) (v := fun α => a * η (propagatorW (fixedEqCoeff s M Q ν c ρ) 0 t (oscTestFun m α)))
      (g := fun α => (|a| * s57pD d n P η * Ca) ^ 2 * oscEigenvalue d α ^ ((J : ℝ) - m)) (hsum.mul_left _) (fun α => by
        have h1 := s57p_init_coord hP hη hdual hbd ht α
        have h2 : |a * η (propagatorW (fixedEqCoeff s M Q ν c ρ) 0 t (oscTestFun m α))| ≤
            |a| * (s57pD d n P η * (Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2))) := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        have h3 := pow_le_pow_left₀ (abs_nonneg _) h2 2
        rw [sq_abs] at h3
        refine h3.trans (le_of_eq ?_)
        calc (|a| * (s57pD d n P η * (Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)))) ^ 2
            = (|a| * s57pD d n P η * Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) ^ 2 := by ring
          _ = _ := by rw [hsq])
    refine ⟨key.1, ?_⟩
    unfold s57pI
    refine key.2.trans (le_of_eq ?_)
    rw [tsum_mul_left]
  refine ⟨hmem, fun t₁ ht₁ t₂ ht₂ => ?_⟩
  have hlip : ∀ s₀ t₀ : ℝ, s₀ ∈ Set.Icc (0 : ℝ) T → t₀ ∈ Set.Icc (0 : ℝ) T → s₀ ≤ t₀ →
      ‖s57pI (fixedEqCoeff s M Q ν c ρ) m a η t₀ - s57pI (fixedEqCoeff s M Q ν c ρ) m a η s₀‖ ≤
        (|a| * s57pD d n P η * Cd * Real.sqrt (∑' α : MultiIndex d, oscEigenvalue d α ^ ((J : ℝ) - m))) * |t₀ - s₀| := by
    intro s' t' hs' ht' hst
    unfold s57pI
    rw [s57p_ellVec_sub (hmem t' ht').1 (hmem s' hs').1]
    have key := s57p_ellVec_norm_sq (m := m)
      (v := fun α => a * η (propagatorW (fixedEqCoeff s M Q ν c ρ) 0 t' (oscTestFun m α)) -
        a * η (propagatorW (fixedEqCoeff s M Q ν c ρ) 0 s' (oscTestFun m α)))
      (g := fun α => (|a| * s57pD d n P η * Cd * (t' - s')) ^ 2 * oscEigenvalue d α ^ ((J : ℝ) - m)) (hsum.mul_left _) (fun α => by
        have h1 := s57p_init_coord_lip hP hη hdual hbd hs'.1 hst ht'.2 (m := m) α
        have h2 : |a * η (propagatorW (fixedEqCoeff s M Q ν c ρ) 0 t' (oscTestFun m α)) -
            a * η (propagatorW (fixedEqCoeff s M Q ν c ρ) 0 s' (oscTestFun m α))| ≤
            |a| * (s57pD d n P η * (Cd * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) * (t' - s'))) := by
          rw [← mul_sub, abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        have h3 := pow_le_pow_left₀ (abs_nonneg _) h2 2
        rw [sq_abs] at h3
        refine h3.trans (le_of_eq ?_)
        calc (|a| * (s57pD d n P η * (Cd * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) * (t' - s')))) ^ 2
            = (|a| * s57pD d n P η * Cd * (t' - s') * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) ^ 2 := by ring
          _ = _ := by rw [hsq])
    rw [tsum_mul_left] at key
    refine le_of_sq_le_sq ?_ (by positivity)
    refine key.2.trans (le_of_eq ?_)
    rw [abs_of_nonneg (sub_nonneg.2 hst)]
    have h := Real.sq_sqrt hS0
    calc (|a| * s57pD d n P η * Cd * (t' - s')) ^ 2 * ∑' α : MultiIndex d, oscEigenvalue d α ^ ((J : ℝ) - m)
        = (|a| * s57pD d n P η * Cd * (t' - s')) ^ 2 *
          (Real.sqrt (∑' α : MultiIndex d, oscEigenvalue d α ^ ((J : ℝ) - m))) ^ 2 := by rw [h]
      _ = _ := by ring
  rcases le_total t₁ t₂ with h | h
  · exact hlip t₁ t₂ ht₁ ht₂ h
  · rw [← norm_neg, neg_sub, abs_sub_comm]; exact hlip t₂ t₁ ht₂ ht₁ h

theorem s57p_osc_orbit (hθ : IsUlCutoff θ) (hd : 1 ≤ d) (Fx : S57pFx θ T n K s M Q ν c ρ A Λc νbar) {Cj : ℝ} (hCj : 0 ≤ Cj)
    (hjets : ∀ α : MultiIndex d, ContDiff ℝ ∞ (oscTestFun m α) ∧ ∀ l ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x,
      ‖iteratedFDeriv ℝ l (oscTestFun m α) x‖ ≤ Cj * oscEigenvalue d α ^ (((J : ℝ) - m) / 2))
    (hm : (J : ℝ) + d < m) {φ : Euc d → ℝ} (hφ : IsOscTest m φ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ (n + 1) (propagatorW (fixedEqCoeff s M Q ν c ρ) r t φ) ∧
      ∀ i ≤ n + 1, ∀ x, ‖iteratedFDeriv ℝ i (propagatorW (fixedEqCoeff s M Q ν c ρ) r t φ) x‖ ≤ B := by
  obtain ⟨hsum, hexp, htail⟩ := s57p_hermite_series hd hm hCj hjets hφ
  obtain ⟨hCu0, hCu⟩ := s57pCu_spec hθ (n + 1)
  set g : MultiIndex d → ℝ := fun α => |s57pb d m φ α| * (Cj * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) with hg
  have hg0 : ∀ α, 0 ≤ g α := fun α => mul_nonneg (abs_nonneg _) (mul_nonneg hCj (Real.rpow_nonneg (oscEv_pos α).le _))
  have hφR : ContDiff ℝ ((n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) φ := hφ.1.of_le (by exact_mod_cast le_top)
  have hBφ : ∀ l ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x, ‖iteratedFDeriv ℝ l φ x‖ ≤ ∑' α, g α := by
    intro l hl x
    have := htail ∅ l hl x
    have e : (fun y => φ y - s57pP d m φ ∅ y) = φ := by funext y; simp [s57pP]
    rw [e] at this
    refine this.trans (le_of_eq ?_)
    refine tsum_congr fun α => ?_
    simp [hg]
  obtain ⟨-, hO⟩ := hCu Fx.fam.adj (tsum_nonneg hg0) hφR hBφ t ht
  exact ⟨|K| * (s57pCu θ hθ (n + 1) * ∑' α, g α), mul_nonneg (abs_nonneg _) (mul_nonneg hCu0 (tsum_nonneg hg0)),
    fun r hr => ⟨(hO r hr).1, (hO r hr).2⟩⟩

theorem s57p_init_eval (hθ : IsUlCutoff θ) (hd : 1 ≤ d) (hP : (d : ℝ) < 2 * P) (hη : IsBoundedLinearOnE n P η)
    (hdual : dualNormE n P η < ⊤) (Fx : S57pFx θ T n K s M Q ν c ρ A Λc νbar)
    (hbd : S57pOrbBd (fixedEqCoeff s M Q ν c ρ) T n m J Ca Cd) (hCa : 0 ≤ Ca) (hCd : 0 ≤ Cd) {Cj : ℝ} (hCj : 0 ≤ Cj)
    (hjets : ∀ α : MultiIndex d, ContDiff ℝ ∞ (oscTestFun m α) ∧ ∀ l ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x,
      ‖iteratedFDeriv ℝ l (oscTestFun m α) x‖ ≤ Cj * oscEigenvalue d α ^ (((J : ℝ) - m) / 2))
    (hJ : 3 * (n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊) + 9 ≤ J) (hm : (J : ℝ) + d < m) (a : ℝ) {φ : Euc d → ℝ}
    (hφ : IsOscTest m φ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    OscDual.eval (s57pI (fixedEqCoeff s M Q ν c ρ) m a η t) φ = a * η (propagatorW (fixedEqCoeff s M Q ν c ρ) 0 t φ) := by
  set C := fixedEqCoeff s M Q ν c ρ with hC
  have hsumJ := s57p_summable_J hd hm
  obtain ⟨hmem, -⟩ := (s57p_init_lip hP hη hdual hbd hCa hCd a hsumJ).1 t ht
  have hcoord : ∀ α, OscDual.coord (s57pI C m a η t) α = a * η (propagatorW C 0 t (oscTestFun m α)) := fun α =>
    s57p_coord_ellVec hmem α
  have hD := s57pD_nonneg d n P η
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht.1⟩
  set f : MultiIndex d → Euc d → ℝ := fun α => propagatorW C 0 t (oscTestFun m α) with hf
  have hfc : ∀ α, ContDiff ℝ n (f α) := fun α => (((hbd α).1 t ht).2 0 h0).1.of_le (by exact_mod_cast Nat.le_succ n)
  have hfb : ∀ α, ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (f α) x‖ ≤ Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) :=
    fun α j hj x => (((hbd α).1 t ht).2 0 h0).2 j (by omega) x
  -- summability
  have hsb := s57p_b_summable hd hm hφ
  have hw : Summable fun α : MultiIndex d => s57pb d m φ α * η (f α) := by
    refine Summable.of_norm_bounded (hsb.mul_left (s57pD d n P η * Ca)) fun α => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have := s57p_init_coord hP hη hdual hbd ht α
    calc |s57pb d m φ α| * |η (f α)| ≤ |s57pb d m φ α| * (s57pD d n P η * (Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2))) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = _ := by ring
  -- the limit of the partial sums
  have hlim : Tendsto (fun F : Finset (MultiIndex d) => ∑ α ∈ F, s57pb d m φ α * η (f α)) atTop
      (𝓝 (η (propagatorW C 0 t φ))) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    set ε' : ℝ := ε / (2 * (s57pD d n P η + 1)) with hε'
    have hε'0 : 0 < ε' := by positivity
    obtain ⟨F₀, hF₀⟩ := s57p_prop_expand hθ hd Fx.fam (m := m) (J := J) hJ hm hφ hε'0
    obtain ⟨Bφ, hBφ0, hBφ⟩ := s57p_osc_orbit hθ hd Fx hCj hjets hm hφ ht
    refine ⟨F₀, fun F hF => ?_⟩
    obtain ⟨hS1, hS2, hS3⟩ := s57p_eta_finsum hP hη F f (s57pb d m φ) (fun α => Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) hfc hfb
    have hBF0 : 0 ≤ ∑ α ∈ F, |s57pb d m φ α| * (Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) :=
      Finset.sum_nonneg fun α _ => mul_nonneg (abs_nonneg _) (mul_nonneg hCa (Real.rpow_nonneg (oscEv_pos α).le _))
    have hf0c : ContDiff ℝ n (propagatorW C 0 t φ) := ((hBφ 0 h0).1).of_le (by exact_mod_cast Nat.le_succ n)
    have hsub := s57p_eta_sub hP hη hf0c hS1 (B := max Bφ (∑ α ∈ F, |s57pb d m φ α| * (Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2))))
      (fun j hj x => ((hBφ 0 h0).2 j (by omega) x).trans (le_max_left _ _))
      (fun j hj x => (hS2 j hj x).trans (le_max_right _ _))
    have hgc : ContDiff ℝ n (fun y => propagatorW C 0 t φ y - ∑ α ∈ F, s57pb d m φ α * f α y) := hf0c.sub hS1
    have hb := s57p_eta_bound hP hη hdual hgc (B := ε') (fun j hj x => hF₀ F hF t ht 0 h0 j (by omega) x)
    rw [hsub, hS3] at hb
    rw [Real.dist_eq, abs_sub_comm]
    refine lt_of_le_of_lt hb ?_
    have hD' : 0 ≤ s57pD d n P η := hD
    calc (dualNormE n P η).toReal * (s57pC d n P * ε') = s57pD d n P η * ε' := by simp [s57pD]; ring
      _ < ε := by
        rw [hε']
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  have hev : OscDual.eval (s57pI C m a η t) φ = ∑' α, a * (s57pb d m φ α * η (f α)) := by
    rw [s57p_eval_tsum]
    refine tsum_congr fun α => ?_
    rw [hcoord α]; ring
  rw [hev, tsum_mul_left]
  congr 1
  exact tendsto_nhds_unique hw.hasSum hlim

end HRS.MS.FixEq
