import HRS.MC.S7E0a
import HRS.MC.QRPWickAux1
import HRS.Equilibrium.QuadraticLimit.ChaosAuxA

/-!
# Packet `s7_W1_isserlis`: Isserlis / Wick pairing for the correlated Gaussian data

The law of `(G_0, ..., G_{n-1})` is `multivariateGaussian 0 C_n` with `C_n` positive semidefinite
(`s7e_cov_psd`).  The linear forms of a centred multivariate Gaussian form a Gaussian linear space
(`QrpwG4`), so the Wick pairing `qrpw_wick4` applies on `EuclideanSpace`; transfer by `integral_map`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace Matrix

noncomputable section

namespace HRS.MC.Sec7.W1

open HRS HRS.Sec7 HRS.Q08 HRS.MC.QRSpec.Wick

variable {n : ℕ}

/-- the linear map `w |-> (z |-> sum_i w_i z_i)` -/
def w1Lin (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) → ℝ) where
  toFun := q08c_ch_lin
  map_add' := fun u v => by funext z; exact q08c_ch_lin_add u v z
  map_smul' := fun c w => by
    funext z; simp [q08c_ch_lin, Finset.mul_sum, mul_assoc]

theorem w1Lin_apply (w : Fin n → ℝ) : w1Lin n w = q08c_ch_lin w := rfl

theorem w1_coord (a : Fin n) (z : EuclideanSpace ℝ (Fin n)) :
    q08c_ch_lin (Pi.single a 1) z = z a := by
  simp [q08c_ch_lin, Pi.single_apply]

theorem w1_memLp4 {C : Matrix (Fin n) (Fin n) ℝ} (w : Fin n → ℝ) :
    MemLp (q08c_ch_lin w) 4 (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C) := by
  have h1 := (innerSL ℝ (WithLp.toLp 2 w)).comp_memLp'
    (IsGaussian.memLp_id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C) 4 (by norm_num))
  convert h1 using 1
  rw [q08c_ch_lin_eq]; ext z; simp

theorem w1_G4 {C : Matrix (Fin n) (Fin n) ℝ} (hS : C.PosSemidef) :
    QrpwG4 (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C) (LinearMap.range (w1Lin n)) := by
  rintro W ⟨w, rfl⟩
  refine ⟨w1_memLp4 w, ?_⟩
  simp only [w1Lin_apply]
  rw [q08c_ch_fourth hS, q08c_ch_second hS]

theorem w1_mean {C : Matrix (Fin n) (Fin n) ℝ} (hS : C.PosSemidef) (a : Fin n) :
    ∫ z, z a ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C) = 0 := by
  have := q08c_ch_lin_int_pow hS (Pi.single a 1) 1
  simp only [w1_coord, pow_one] at this
  rw [this]; simp

theorem w1_second {C : Matrix (Fin n) (Fin n) ℝ} (hS : C.PosSemidef) (a b : Fin n) :
    ∫ z, z a * z b ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C) = C a b := by
  have := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin n))) hS a b
  unfold covariance at this
  simpa [w1_mean hS] using this


theorem w1_coord_mem {n : ℕ} (a : Fin n) :
    (fun z : EuclideanSpace ℝ (Fin n) => z a) ∈ LinearMap.range (w1Lin n) :=
  ⟨Pi.single a 1, funext fun z => w1_coord a z⟩

theorem w1_wick {C : Matrix (Fin n) (Fin n) ℝ} (hS : C.PosSemidef) (a b c d : Fin n) :
    ∫ z, (z a * z b - C a b) * (z c * z d - C c d)
      ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C) = C a c * C b d + C a d * C b c := by
  have hG := w1_G4 hS
  have hA := w1_coord_mem a
  have hB := w1_coord_mem b
  have hC := w1_coord_mem c
  have hD := w1_coord_mem d
  have h4 := qrpw_wick4 hG hA hB hC hD
  have mA := (hG _ hA).1
  have mB := (hG _ hB).1
  have mC := (hG _ hC).1
  have mD := (hG _ hD).1
  have iab := qrpw_int_mul mA mB
  have icd := qrpw_int_mul mC mD
  have i4 := qrpw_int_mul4 mA mB mC mD
  have e : (fun z : EuclideanSpace ℝ (Fin n) => (z a * z b - C a b) * (z c * z d - C c d)) =
      fun z => (z a * z b * (z c * z d) - C c d * (z a * z b)) - (C a b * (z c * z d) - C a b * C c d) := by
    funext z; ring
  have j1 : Integrable (fun z : EuclideanSpace ℝ (Fin n) => C c d * (z a * z b))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C) := iab.const_mul (C c d)
  have j2 : Integrable (fun z : EuclideanSpace ℝ (Fin n) => C a b * (z c * z d))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C) := icd.const_mul (C a b)
  have j3 : Integrable (fun _ : EuclideanSpace ℝ (Fin n) => C a b * C c d)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C) := integrable_const _
  have k1 : ∫ z : EuclideanSpace ℝ (Fin n), C c d * (z a * z b)
      ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C) = C c d * C a b := by
    rw [integral_const_mul, w1_second hS]
  have k2 : ∫ z : EuclideanSpace ℝ (Fin n), C a b * (z c * z d)
      ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C) = C a b * C c d := by
    rw [integral_const_mul, w1_second hS]
  have k3 : ∫ _z : EuclideanSpace ℝ (Fin n), C a b * C c d
      ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) C) = C a b * C c d := by
    simp
  have k4 := h4
  rw [w1_second hS, w1_second hS, w1_second hS, w1_second hS, w1_second hS, w1_second hS] at k4
  have s1 := integral_sub (i4.sub j1) (j2.sub j3)
  have s2 := integral_sub i4 j1
  have s3 := integral_sub j2 j3
  rw [e]
  simp only [Pi.sub_apply] at s1 s2 s3 ⊢
  rw [s1, s2, s3, k1, k2, k3, k4]
  ring

/-! ### The packet -/

theorem s7_W1_isserlis_proof (d : ℕ) (s β : ℝ) (ρ : Torus d → ℝ) (e : ℕ → Torus d → ℝ) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (G : ℕ → Ω → ℝ)
    (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) (hρ : SmoothPosDensity ρ)
    (he : IsONBL2Zero (withDensityReal ρ) e)
    (hG : s7_GaussData d s β ρ e P G) (i j k l : ℕ) :
    let C := fun a b => susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e a) (e b)
    ∫ ω, (G i ω * G j ω - C i j) * (G k ω * G l ω - C k l) ∂P = C i k * C j l + C i l * C j k := by
  intro C
  obtain ⟨hmeas, hlaw⟩ := hG
  set N := max (max i j) (max k l) + 1 with hN
  have hS := E0a.s7e_cov_psd hd hs0 hsd hβ hρ he N
  have hV : Measurable (fun ω => (WithLp.toLp 2 fun a : Fin N => G a ω : EuclideanSpace ℝ (Fin N))) :=
    (MeasurableEquiv.toLp 2 (Fin N → ℝ)).measurable.comp (Measurable.of_eval fun a => hmeas a)
  have hi : i < N := by omega
  have hj : j < N := by omega
  have hk : k < N := by omega
  have hl : l < N := by omega
  have key := w1_wick hS ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ ⟨l, hl⟩
  rw [← hlaw N] at key
  unfold law at key
  rw [integral_map hV.aemeasurable (by fun_prop)] at key
  simpa [C] using key

end HRS.MC.Sec7.W1
