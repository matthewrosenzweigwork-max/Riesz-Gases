import HRS.MS.Fp81S21BlockValue14
import HRS.MS.Fp81S21WindowFeature15

/-!
# S2.1(iii), packet 15-close: moving weighted covariance block API

This exports the physical moving-window block value with its uniform weighted
bound and shifted observation specification. The block reconstruction factor
and the squared orbit-decay weight are displayed in the contract field.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas
open HRS.MS.GenPath HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL
open HRS.MS.FixEq

/-- The non-decaying amplitude in the packet-15 positive feature bound.
It is fixed before the observation start, block, localization, and field. -/
noncomputable def fp81s21_windowCovBlockAmp
    (d r : ℕ) (H Cmix : ℝ) : ℝ :=
  (2 + (d : ℝ) ^ (r + 1) *
      ((volume.restrict (Icc (0 : ℝ) H)) Set.univ).toReal ^ (1 / 2 : ℝ)) *
    Cmix * Real.sqrt (∑' α : MultiIndex d, (s104_b d α) ^ 2)

private lemma fp81s21_window_feature_Bpos_sq_explicit
    (d r : ℕ) (H Cmix cdec a v : ℝ) :
    (fp81s21_window_feature_Bpos d r H Cmix cdec a v) ^ 2 =
      (fp81s21_windowCovBlockAmp d r H Cmix) ^ 2 *
        Real.exp (-2 * cdec * max (a - v) 0) := by
  have hexp : (Real.exp (-cdec * max (a - v) 0)) ^ 2 =
      Real.exp (-2 * cdec * max (a - v) 0) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  dsimp [fp81s21_window_feature_Bpos, fp81s21_window_Bpos,
    fp81s21_windowCovBlockAmp]
  calc
    _ = ((2 + (d : ℝ) ^ (r + 1) *
          ((volume.restrict (Icc (0 : ℝ) H)) Set.univ).toReal ^ (1 / 2 : ℝ)) *
        Cmix * Real.sqrt (∑' α : MultiIndex d, (s104_b d α) ^ 2)) ^ 2 *
        (Real.exp (-cdec * max (a - v) 0)) ^ 2 := by ring
    _ = _ := by rw [hexp]

/-- The individual moving block value, with its weighted variation estimate
and all shifted observation coordinates. The value in the coordinate field
is the projective tensor supplied by `fp81s21_blockValue`; the coordinate
predicate itself includes its projective-membership clause. -/
structure fp81s21_WindowCovarianceBlockContract
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + H →
      ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ,
        IsR2DualCombo m φ → IsR2DualCombo m ψ →
        propagatorW C u t (φ + c • ψ) =
          propagatorW C u t φ + c • propagatorW C u t ψ)
    (I : Set ℝ) (k : ℕ) : Prop where
  weighted_bound :
    ‖fp81s21_blockValue D I k‖ₑ ≤
      ENNReal.ofReal ((3 + Real.sqrt H) ^ 2 * fp81s21_blockC0) *
        (∫⁻ v in fp81s21_windowLocalBlock a H k ∩ I,
          ENNReal.ofReal |2 * C.ν| * dualNormE r P (z v) *
            ENNReal.ofReal (s57pC d r P *
              ((d : ℝ) * 2 ^ r *
                ((fp81s21_windowCovBlockAmp d r H Cmix) ^ 2 *
                  Real.exp (-2 * cdec * max (a - v) 0)))))
  coordinate_spec :
    fp81s21_IsWindowJValue C m H a z (Icc (k : ℝ) ((k : ℝ) + 1) ∩ I)
      ((fp81s21_blockValue D I k : projTensor (OscPath d m H) 2) :
        TensorDual (OscPath d m H) 2)

/-- The packet-15 individual block contract for the physical moving
trajectory. The trajectory radius and decay constants precede the observation
start and all block/localization/field data. The input `D` retains the exact
localized-domain hypotheses, including orbit admissibility,
`IsR2L1F`, and `R2JIntegrandMeas`. The weighted field displays the block
reconstruction factor `(3 + sqrt H)^2` and squared decay weight.

`coordinate_spec` supplies projective-tensor membership and the coordinate
specification on every observation function. Block-level linearity and
set-additivity are not claimed here; they are packet 16a.
-/
theorem fp81s21_window_covariance_block (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ _hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁,
      ∃ Cs0 cdec Cmix : ℝ,
        0 ≤ Cs0 ∧ 0 < cdec ∧ Summable (s104_b p.d) ∧
        0 ≤ Cmix ∧ Cs0 ≤ Cmix ∧
        ∀ a : ℝ, 0 ≤ a → ∀ (P : ℝ)
          (z : ℝ → (Euc p.d → ℝ) → ℝ),
          ∀ (D : fp81s21_WindowLocalInput (r26t3_coeff R)
              (wholeSpaceIndex p.d : ℝ) p.T a (2 * p.d + 8) P z Cmix cdec),
          (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + p.T →
            ∀ φ ψ : Euc p.d → ℝ, ∀ c : ℝ,
              IsR2DualCombo (wholeSpaceIndex p.d : ℝ) φ →
              IsR2DualCombo (wholeSpaceIndex p.d : ℝ) ψ →
              propagatorW (r26t3_coeff R) u t (φ + c • ψ) =
                propagatorW (r26t3_coeff R) u t φ +
                  c • propagatorW (r26t3_coeff R) u t ψ) →
          ∀ (I : Set ℝ), MeasurableSet I → ∀ k : ℕ,
          fp81s21_WindowCovarianceBlockContract D hlin I k := by
  obtain ⟨δ0, hδ0, hδ0half, hfeature⟩ :=
    fp81s21_window_feature_trace_bound_pos_from_wR33 p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R hterm
  obtain ⟨Cs0, cdec, Cmix, hCs0, hcdec, hsumb, hCmix, hCs0Cmix, _htrace⟩ :=
    hfeature δ hδ hδle R hterm
  refine ⟨Cs0, cdec, Cmix, hCs0, hcdec, hsumb, hCmix, hCs0Cmix, ?_⟩
  intro a ha P z D hlin I hI k
  constructor
  · have hnorm := fp81s21_blockValue_norm_le D hI k
    have hweighted := fp81s21_windowLocal_lintegral_bound_weighted D hI k
    have hprofile : ∀ v : ℝ,
        (fp81s21_window_feature_Bpos p.d (2 * p.d + 8) p.T
          Cmix cdec a v) ^ 2 =
          (fp81s21_windowCovBlockAmp p.d (2 * p.d + 8) p.T Cmix) ^ 2 *
            Real.exp (-2 * cdec * max (a - v) 0) := by
      intro v
      exact fp81s21_window_feature_Bpos_sq_explicit p.d
        (2 * p.d + 8) p.T Cmix cdec a v
    have hintegral :
        (∫⁻ v in fp81s21_windowLocalBlock a p.T k ∩ I,
          ENNReal.ofReal |2 * (r26t3_coeff R).ν| *
            dualNormE (2 * p.d + 8) P (z v) *
            ENNReal.ofReal (s57pC p.d (2 * p.d + 8) P *
              ((p.d : ℝ) * 2 ^ (2 * p.d + 8) *
                (fp81s21_window_feature_Bpos p.d (2 * p.d + 8)
                  p.T Cmix cdec a v) ^ 2))) =
        ∫⁻ v in fp81s21_windowLocalBlock a p.T k ∩ I,
          ENNReal.ofReal |2 * (r26t3_coeff R).ν| *
            dualNormE (2 * p.d + 8) P (z v) *
            ENNReal.ofReal (s57pC p.d (2 * p.d + 8) P *
              ((p.d : ℝ) * 2 ^ (2 * p.d + 8) *
                ((fp81s21_windowCovBlockAmp p.d (2 * p.d + 8)
                    p.T Cmix) ^ 2 *
                  Real.exp (-2 * cdec * max (a - v) 0)))) := by
      refine lintegral_congr fun v => ?_
      rw [hprofile v]
    have hrawWeighted :
        (∫⁻ v in fp81s21_windowLocalBlock a p.T k ∩ I,
          ENNReal.ofReal (HRS.traceNormForm
            (fp81s21_windowDm (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
              p.T a z D.fp81s21_ha (le_of_lt D.fp81s21_hH) v))) ≤
        (∫⁻ v in fp81s21_windowLocalBlock a p.T k ∩ I,
          ENNReal.ofReal |2 * (r26t3_coeff R).ν| *
            dualNormE (2 * p.d + 8) P (z v) *
            ENNReal.ofReal (s57pC p.d (2 * p.d + 8) P *
              ((p.d : ℝ) * 2 ^ (2 * p.d + 8) *
                (fp81s21_window_feature_Bpos p.d (2 * p.d + 8)
                  p.T Cmix cdec a v) ^ 2))) := by
      rw [← fp81s21_blockValue_traceIntegral_eq D hI k]
      exact hweighted
    calc
      ‖fp81s21_blockValue D I k‖ₑ ≤
          ENNReal.ofReal ((3 + Real.sqrt p.T) ^ 2 * fp81s21_blockC0) *
            (∫⁻ v in fp81s21_windowLocalBlock a p.T k ∩ I,
              ENNReal.ofReal (HRS.traceNormForm
                (fp81s21_windowDm (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                  p.T a z D.fp81s21_ha (le_of_lt D.fp81s21_hH) v))) := hnorm
      _ ≤ ENNReal.ofReal ((3 + Real.sqrt p.T) ^ 2 * fp81s21_blockC0) *
          (∫⁻ v in fp81s21_windowLocalBlock a p.T k ∩ I,
            ENNReal.ofReal |2 * (r26t3_coeff R).ν| *
              dualNormE (2 * p.d + 8) P (z v) *
              ENNReal.ofReal (s57pC p.d (2 * p.d + 8) P *
                ((p.d : ℝ) * 2 ^ (2 * p.d + 8) *
                  (fp81s21_window_feature_Bpos p.d (2 * p.d + 8)
                    p.T Cmix cdec a v) ^ 2))) :=
          mul_le_mul' le_rfl hrawWeighted
      _ = ENNReal.ofReal ((3 + Real.sqrt p.T) ^ 2 * fp81s21_blockC0) *
          (∫⁻ v in fp81s21_windowLocalBlock a p.T k ∩ I,
            ENNReal.ofReal |2 * (r26t3_coeff R).ν| *
              dualNormE (2 * p.d + 8) P (z v) *
              ENNReal.ofReal (s57pC p.d (2 * p.d + 8) P *
                ((p.d : ℝ) * 2 ^ (2 * p.d + 8) *
                  ((fp81s21_windowCovBlockAmp p.d (2 * p.d + 8)
                      p.T Cmix) ^ 2 *
                    Real.exp (-2 * cdec * max (a - v) 0))))) := by
        exact congrArg
          (fun t : ℝ≥0∞ => ENNReal.ofReal ((3 + Real.sqrt p.T) ^ 2 *
            fp81s21_blockC0) * t) hintegral
  · exact fp81s21_blockValue_isWindowJValue D hlin hI k

#print axioms fp81s21_window_feature_Bpos_sq_explicit
#print axioms fp81s21_window_covariance_block

end HRS.Fp81.S21

end
