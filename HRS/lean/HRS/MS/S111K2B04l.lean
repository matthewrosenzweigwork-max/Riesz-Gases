import HRS.MS.S111K2B04g
import HRS.MS.S111K2B04k

/-!
# S11.1 continuation, B04: `window_drift_BV`

The drift interval map `D(a,b)(t) = ∫_{(a,b] ∩ [0,u+t]} z^v(U(v,u+t) ·) dv`, as a continuous path in `B_m`, with the bound
`‖D(a,b)‖ ≤ K ∫_{(a,b]} age_u(v) ‖z^v‖_{F_{r,P}} dv`, interval additivity, continuity and variation of the cumulative path.
Zero mass of `z^v` and `P > d/2 + 1` are what make the linear growth of `U(v,t)φ_α` integrable against the weight `⟨x⟩^{-2P}`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K2

open HRS HRS.Whole HRS.MS.Go HRS.MS.CovMeas HRS.MS.R2WinErr HRS.MS.FixEq

variable {d : ℕ} {C : WholeCoeff d} {m c0 : ℝ} {r : ℕ} {b : MultiIndex d → ℝ} {S T u Pw : ℝ}
  {z : ℝ → (Euc d → ℝ) → ℝ}

lemma s111k2_enorm_path_le {w : OscPath d m T} {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (h : ∀ τ : Set.Icc (0 : ℝ) T, ‖OscPath.at' w τ‖ₑ ≤ B) : ‖w‖ₑ ≤ B := by
  rw [← ofReal_norm_eq_enorm]
  have h1 : ‖(show C(Set.Icc (0 : ℝ) T, OscDual d m) from w)‖ ≤ B.toReal := by
    refine (ContinuousMap.norm_le _ ENNReal.toReal_nonneg).2 fun τ => ?_
    refine (ENNReal.ofReal_le_iff_le_toReal hB).1 ?_
    rw [ofReal_norm_eq_enorm]
    exact h τ
  calc ENNReal.ofReal ‖w‖ ≤ ENNReal.ofReal B.toReal := ENNReal.ofReal_le_ofReal h1
    _ = B := ENNReal.ofReal_toReal hB

/-- The bundled continuous path `τ ↦ ∫_{(a,b]} W(v,τ) dv` (for `0 ≤ a ≤ b ≤ u + T`). -/
def s111k2_DpathAux (h : S111k2Drift C m c0 r b S T u Pw z) (a b' : ℝ)
    (hg : 0 ≤ a ∧ a ≤ b' ∧ b' ≤ u + T) : OscPath d m T :=
  (⟨fun τ => s111k2_Dfun C m z u a b' τ, s111k2_Dfun_cont h hg.1 hg.2.1 hg.2.2⟩ :
    C(Set.Icc (0 : ℝ) T, OscDual d m))

open Classical in
/-- The drift path `D(a,b)` (`0` outside `0 ≤ a ≤ b ≤ u + T`). -/
def s111k2_Dpath (h : S111k2Drift C m c0 r b S T u Pw z) (a b' : ℝ) : OscPath d m T :=
  if hg : 0 ≤ a ∧ a ≤ b' ∧ b' ≤ u + T then s111k2_DpathAux h a b' hg else 0

lemma s111k2_Dpath_at (h : S111k2Drift C m c0 r b S T u Pw z) {a b' : ℝ} (ha : 0 ≤ a) (hab : a ≤ b')
    (hb : b' ≤ u + T) (τ : Set.Icc (0 : ℝ) T) :
    OscPath.at' (s111k2_Dpath h a b') τ = s111k2_Dfun C m z u a b' τ := by
  unfold s111k2_Dpath
  rw [dif_pos ⟨ha, hab, hb⟩]
  rfl

theorem s111k2_window_drift_BV (d r : ℕ) (hd : 2 ≤ d) (m T Pw S c0 : ℝ) (hT : 0 < T)
    (hPw : (d : ℝ) / 2 + 1 < Pw) (hS : 0 ≤ S) (hc0 : 0 < c0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ C : WholeCoeff d,
      ∀ b : MultiIndex d → ℝ, Summable (fun alpha => b alpha ^ 2) →
      (∑' alpha, b alpha ^ 2) ≤ S → S111k2WindowOrbitInput C m c0 r b →
      ∀ u : ℝ, 0 ≤ u →
      ∀ z : ℝ → (Euc d → ℝ) → ℝ, IsR2L1F r Pw (u + T) z →
      S111k2DriftIntegrandMeas C m T u z →
      (∀ v ∈ Set.Icc 0 (u + T), z v (fun _ => 1) = 0) →
        ∃ D : ℝ → ℝ → OscPath d m T,
          (∀ a, D a a = 0) ∧
          (∀ a b c, 0 ≤ a → a ≤ b → b ≤ c → c ≤ u + T →
            D a c = D a b + D b c) ∧
          ContinuousOn (fun v => D 0 v) (Set.Icc 0 (u + T)) ∧
          eVariationOn (fun v => D 0 v) (Set.Icc 0 (u + T)) ≤
            ENNReal.ofReal K * ∫⁻ v in Set.Icc 0 (u + T),
              ENNReal.ofReal (s111k2_age c0 u v) * dualNormE r Pw (z v) ∧
          ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ u + T →
            (‖D a b‖ₑ ≤ ENNReal.ofReal K * ∫⁻ v in Set.Ioc a b,
              ENNReal.ofReal (s111k2_age c0 u v) * dualNormE r Pw (z v)) ∧
            ∀ t : Set.Icc (0 : ℝ) T, ∀ phi, IsR2DualCombo m phi →
              OscDual.eval (OscPath.at' (D a b) t) phi =
                ∫ v in Set.Ioc a b ∩ Set.Icc 0 (u + t),
                  z v (propagatorW C v (u + t) phi) := by
  refine ⟨s111k2_Kdrift d r Pw S, (s111k2_Kdrift_pos d r Pw S).le, ?_⟩
  intro C b hbs hbS hW u hu z hz hmeas hone
  have h : S111k2Drift C m c0 r b S T u Pw z :=
    ⟨hW, hc0, hT, hu, hbs, hbS, by linarith, hz, hmeas, hone⟩
  have hbd : ∀ a b', 0 ≤ a → a ≤ b' → b' ≤ u + T →
      ‖s111k2_Dpath h a b'‖ₑ ≤ ENNReal.ofReal (s111k2_Kdrift d r Pw S) *
        ∫⁻ v in Set.Ioc a b', s111k2_Phi c0 u r Pw z v := by
    intro a b' ha hab hb
    have hsub : Set.Ioc a b' ⊆ Set.Icc (0 : ℝ) (u + T) := fun v hv => ⟨ha.trans hv.1.le, hv.2.trans hb⟩
    refine s111k2_enorm_path_le (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top (s111k2_Phi_fin h) (lintegral_mono_set hsub))) fun τ => ?_
    rw [s111k2_Dpath_at h ha hab hb]
    exact s111k2_Dfun_bound h τ.2 ha hab hb
  have hadd : ∀ a b' c', 0 ≤ a → a ≤ b' → b' ≤ c' → c' ≤ u + T →
      s111k2_Dpath h a c' = s111k2_Dpath h a b' + s111k2_Dpath h b' c' := by
    intro a b' c' ha hab hbc hc
    refine ContinuousMap.ext fun τ => ?_
    have e1 := s111k2_Dpath_at h ha (hab.trans hbc) hc τ
    have e2 := s111k2_Dpath_at h ha hab (hbc.trans hc) τ
    have e3 := s111k2_Dpath_at h (ha.trans hab) hbc hc τ
    show OscPath.at' (s111k2_Dpath h a c') τ = OscPath.at' (s111k2_Dpath h a b') τ + OscPath.at' (s111k2_Dpath h b' c') τ
    rw [e1, e2, e3]
    exact s111k2_Dfun_add h τ.2 ha hab hbc hc
  have hfin : ∫⁻ v in Set.Icc (0 : ℝ) (u + T), ENNReal.ofReal (s111k2_Kdrift d r Pw S) * s111k2_Phi c0 u r Pw z v ≠ ⊤ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (s111k2_Phi_fin h)
  obtain ⟨hcont, hvar⟩ := s111k2_interval_bv (s111k2_Dpath h) (H := u + T)
    (fun v => ENNReal.ofReal (s111k2_Kdrift d r Pw S) * s111k2_Phi c0 u r Pw z v) hfin
    hadd (fun a b' ha hab hb => by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact hbd a b' ha hab hb)
  refine ⟨s111k2_Dpath h, ?_, hadd, hcont, ?_, ?_⟩
  · intro a
    unfold s111k2_Dpath
    by_cases hg : 0 ≤ a ∧ a ≤ a ∧ a ≤ u + T
    · rw [dif_pos hg]
      refine ContinuousMap.ext fun τ => ?_
      exact s111k2_Dfun_self C m z u a τ
    · rw [dif_neg hg]
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hvar
    exact hvar
  · intro a b' ha hab hb
    refine ⟨hbd a b' ha hab hb, fun t φ hφ => ?_⟩
    rw [s111k2_Dpath_at h ha hab hb]
    exact s111k2_Dfun_eval h t.2 ha hab hb hφ

end HRS.MS.S111K2
