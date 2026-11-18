import HRS.PDE.MovAAux13

/-!
# MOVA Aux14: the centred identity `S^M + βN(C^M - E_Q C^M) = ∑ k(x_i) - E_Q ∑ k(x_i)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem mova_integrable_of_continuous_config {μ : Measure (Config d N)} [IsFiniteMeasure μ]
    {f : Config d N → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem mova_srcReg_centered (hN : 0 < N) (D : DynData d)
    (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ)) (M : ℝ) {ρ ρt : ℝ → Torus d → ℝ} {r : ℝ}
    (hρ : Torus.IsCk 2 (ρ r)) (hdens : IsProbDensity (ρ r)) (hpos : ∀ x, 0 < ρ r x)
    (hV : Torus.IsCk 2 D.V) (hκ : 0 < D.invβ) (hρtc : Continuous (ρt r))
    [IsProbabilityMeasure (movT_Q (b15c_gReg d D.s M) D N ρ r)] (X : Config d N) :
    movT_srcReg D N M ρ ρt r X - (-(D.invβ⁻¹ * N) * (movT_commReg D N M (ρ r) X -
        ∫ Y, movT_commReg D N M (ρ r) Y ∂(movT_Q (b15c_gReg d D.s M) D N ρ r))) =
      ∑ i, mova_k D M ρ ρt r (X i) -
        ∫ Y, ∑ i, mova_k D M ρ ρt r (Y i) ∂(movT_Q (b15c_gReg d D.s M) D N ρ r) := by
  set Q := movT_Q (b15c_gReg d D.s M) D N ρ r with hQ
  have hφ2 := mova_phi_isCk_two D M hρ hpos hV
  have hCc := mova_continuous_commReg D N M hρ hdens hpos hV
  have hKc : Continuous fun Y : Config d N => ∑ i, mova_k D M ρ ρt r (Y i) :=
    continuous_finsetSum _ fun i _ =>
      (mova_continuous_k D M hρ hdens hpos hV hκ hρtc).comp (continuous_apply i)
  have hPc : Continuous (movT_psit D M ρ ρt r : Config d N → ℝ) := by
    unfold movT_psit
    exact continuous_finsetSum _ fun i _ =>
      (mova_continuous_phit D M hρ hpos hρtc).comp (continuous_apply i)
  have hALG := fun Y => mova_srcReg_alg hN D hM M hρ hpos hV hκ (ρt := ρt) Y
  have hSc : Continuous (movT_srcReg D N M ρ ρt r : Config d N → ℝ) := by
    have : (movT_srcReg D N M ρ ρt r : Config d N → ℝ) = fun Y =>
        -(D.invβ⁻¹ * N) * movT_commReg D N M (ρ r) Y + ∑ i, mova_k D M ρ ρt r (Y i) +
          mova_const D N M ρ ρt r := funext hALG
    rw [this]
    exact ((continuous_const.mul hCc).add hKc).add continuous_const
  -- `E_Q S = 0`
  have hA0 := mova_EQ_A0 hN D hM hV hκ M hρ hdens hpos hφ2 (fun x => mova_phi_apply D M ρ r x)
  have hiP : Integrable (movT_psit D M ρ ρt r : Config d N → ℝ) Q := mova_integrable_of_continuous_config hPc
  have hiS : Integrable (movT_srcReg D N M ρ ρt r : Config d N → ℝ) Q := mova_integrable_of_continuous_config hSc
  have hS' : ∀ Y : Config d N, movT_srcReg D N M ρ ρt r Y =
      (d1_configGen D.invβ (b15d_configDriftReg D M) (fun X => ∑ i, movT_phi D M ρ r (X i)) Y +
        D.invβ * ∑ i, ‖Torus.grad (movT_phi D M ρ r) (Y i)‖ ^ 2) - movT_psit D M ρ ρt r Y +
        ∫ Z, movT_psit D M ρ ρt r Z ∂Q := fun Y => rfl
  have hiA : Integrable (fun Y : Config d N => d1_configGen D.invβ (b15d_configDriftReg D M)
      (fun X => ∑ i, movT_phi D M ρ r (X i)) Y +
        D.invβ * ∑ i, ‖Torus.grad (movT_phi D M ρ r) (Y i)‖ ^ 2) Q := by
    have : (fun Y : Config d N => d1_configGen D.invβ (b15d_configDriftReg D M)
        (fun X => ∑ i, movT_phi D M ρ r (X i)) Y +
          D.invβ * ∑ i, ‖Torus.grad (movT_phi D M ρ r) (Y i)‖ ^ 2) = fun Y =>
        (movT_srcReg D N M ρ ρt r Y + movT_psit D M ρ ρt r Y) - ∫ Z, movT_psit D M ρ ρt r Z ∂Q := by
      funext Y; rw [hS' Y]; ring
    rw [this]
    exact (hiS.add hiP).sub (integrable_const _)
  have hES : ∫ Y, movT_srcReg D N M ρ ρt r Y ∂Q = 0 := by
    have e : (fun Y : Config d N => movT_srcReg D N M ρ ρt r Y) = fun Y =>
        ((d1_configGen D.invβ (b15d_configDriftReg D M) (fun X => ∑ i, movT_phi D M ρ r (X i)) Y +
          D.invβ * ∑ i, ‖Torus.grad (movT_phi D M ρ r) (Y i)‖ ^ 2) - movT_psit D M ρ ρt r Y) +
          ∫ Z, movT_psit D M ρ ρt r Z ∂Q := funext hS'
    have i1 : Integrable (fun Y : Config d N => (d1_configGen D.invβ (b15d_configDriftReg D M)
        (fun X => ∑ i, movT_phi D M ρ r (X i)) Y +
          D.invβ * ∑ i, ‖Torus.grad (movT_phi D M ρ r) (Y i)‖ ^ 2) - movT_psit D M ρ ρt r Y) Q :=
      hiA.sub hiP
    rw [e, integral_add i1 (integrable_const _), integral_sub hiA hiP]
    have h0 : ∫ Y : Config d N, (d1_configGen D.invβ (b15d_configDriftReg D M)
        (fun X => ∑ i, movT_phi D M ρ r (X i)) Y +
          D.invβ * ∑ i, ‖Torus.grad (movT_phi D M ρ r) (Y i)‖ ^ 2) ∂Q = 0 := hA0
    rw [h0]
    simp
  -- integrate the algebraic identity
  have hiC : Integrable (movT_commReg D N M (ρ r) : Config d N → ℝ) Q := mova_integrable_of_continuous_config hCc
  have hiK : Integrable (fun Y : Config d N => ∑ i, mova_k D M ρ ρt r (Y i)) Q :=
    mova_integrable_of_continuous_config hKc
  have hES2 : ∫ Y, movT_srcReg D N M ρ ρt r Y ∂Q =
      -(D.invβ⁻¹ * N) * ∫ Y, movT_commReg D N M (ρ r) Y ∂Q +
        ∫ Y, ∑ i, mova_k D M ρ ρt r (Y i) ∂Q + mova_const D N M ρ ρt r := by
    have e : (fun Y : Config d N => movT_srcReg D N M ρ ρt r Y) = fun Y =>
        -(D.invβ⁻¹ * N) * movT_commReg D N M (ρ r) Y + ∑ i, mova_k D M ρ ρt r (Y i) +
          mova_const D N M ρ ρt r := funext hALG
    have i1 : Integrable (fun Y : Config d N => -(D.invβ⁻¹ * N) * movT_commReg D N M (ρ r) Y +
        ∑ i, mova_k D M ρ ρt r (Y i)) Q := (hiC.const_mul _).add hiK
    have i2 : Integrable (fun Y : Config d N => -(D.invβ⁻¹ * N) * movT_commReg D N M (ρ r) Y) Q :=
      hiC.const_mul _
    rw [e, integral_add i1 (integrable_const _), integral_add i2 hiK, integral_const_mul]
    simp
  rw [hALG X]
  linarith

end HRS
