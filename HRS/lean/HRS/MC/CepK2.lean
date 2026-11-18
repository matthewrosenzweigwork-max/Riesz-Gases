import HRS.MC.CepK1
import HRS.MC.CepK2Aux2

/-!
# Packet K2: dissipativity of the ordered drift
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepK2

open HRS

/-- `V` is `C¹` with Lipschitz gradient on the covering line.  Same body as
`HRS.MC.Cepa.cep_IsC11` (`HRS/MC/CepaSpec.lean`); duplicated so that this packet does not import the spec. -/
def cep_IsC11 {d : ℕ} (V : Torus d → ℝ) : Prop :=
  Torus.IsCk 1 V ∧ ∃ L : ℝ≥0, LipschitzWith L (gradient (Torus.lift V))

lemma cepk2_drift_coord {N : ℕ} {D : DynData 1} (hs : D.s = 0) {a : ℝ}
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) {ρ : ℝ → ℝ}
    (hρ : ∀ y : Euc 1, (∀ n : ℤ, y 0 ≠ n) → (periodicRieszGrad 1 0 (Torus.mk y)) 0 =
      -(Real.pi * (Real.cos (Real.pi * y 0) / Real.sin (Real.pi * y 0))) + ρ (y 0))
    {y : Fin N → Euc 1} (hfree : (fun i => Torus.mk (y i)) ∉ collisionSet 1 N) (i : Fin N) :
    liftedDrift D y i 0 = (a / N) * ∑ j ∈ Finset.univ.erase i,
        (cepk2_c (y i 0 - y j 0) - ρ (y i 0 - y j 0)) - (gradient (Torus.lift D.V) (y i)) 0 := by
  unfold liftedDrift particleDrift
  rw [PiLp.sub_apply, PiLp.smul_apply, cepk2_grad_eq]
  have hsum : (∑ j ∈ Finset.univ.erase i,
      Torus.matVec D.M (periodicRieszGrad 1 D.s (Torus.mk (y i) - Torus.mk (y j)))) 0 =
      ∑ j ∈ Finset.univ.erase i, (-a) * (periodicRieszGrad 1 0 (Torus.mk (y i - y j))) 0 := by
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← cepk2_mk_sub, hs, hM]
    show (WithLp.toLp 2 ((-(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))).mulVec
      (periodicRieszGrad 1 0 (Torus.mk (y i - y j))).ofLp) : Euc 1) 0 = _
    simp [Matrix.mulVec, dotProduct]
  rw [hsum, smul_eq_mul]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≠ i := (Finset.mem_erase.mp hj).1
  rw [hρ (y i - y j) (fun n hn => cepk2_free hfree i j hj'.symm n (by simpa using hn))]
  unfold cepk2_c
  simp only [PiLp.sub_apply]
  ring

lemma cepk2_norm_sq (v : Euc 1) : ‖v‖ ^ 2 = (v 0) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp

lemma cepk2_inner (v w : Euc 1) : inner ℝ v w = w 0 * v 0 := by
  simp [PiLp.inner_apply]

/-- **K2 (dissipativity of the ordered drift)**. -/
theorem cep_K2_drift_dissipative_proof {N : ℕ} {D : DynData 1} (hs : D.s = 0) {a : ℝ} (ha : 0 ≤ a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hV : cep_IsC11 D.V) :
    ∃ Λ : ℝ, ∀ (π : Equiv.Perm (Fin N)) (y y' : Fin N → Euc 1),
      CyclicallyOrdered π y → CyclicallyOrdered π y' →
      (fun i => Torus.mk (y i)) ∉ collisionSet 1 N → (fun i => Torus.mk (y' i)) ∉ collisionSet 1 N →
      ∑ i, inner ℝ (y i - y' i) (liftedDrift D y i - liftedDrift D y' i) ≤ Λ * ∑ i, ‖y i - y' i‖ ^ 2 := by
  obtain ⟨ρ, hρs, hρper, -, hρ⟩ := HRS.MC.CepK1.cep_K1_force_decomp_proof
  obtain ⟨Lρ, hLρ0, hLρ⟩ := cepk2_lip_of_periodic hρs hρper
  obtain ⟨-, LV, hLV⟩ := hV
  refine ⟨(LV : ℝ) + 2 * a * Lρ, ?_⟩
  intro π y y' hord hord' hfree hfree'
  by_cases hN : N = 0
  · subst hN; simp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  obtain ⟨δ, hδ⟩ : ∃ δ : Fin N → ℝ, ∀ i, δ i = y i 0 - y' i 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨fc, hfc⟩ : ∃ fc : Fin N → Fin N → ℝ, ∀ i j,
      fc i j = cepk2_c (y i 0 - y j 0) - cepk2_c (y' i 0 - y' j 0) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨fr, hfr⟩ : ∃ fr : Fin N → Fin N → ℝ, ∀ i j,
      fr i j = ρ (y i 0 - y j 0) - ρ (y' i 0 - y' j 0) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨gg, hgg⟩ : ∃ gg : Fin N → ℝ, ∀ i,
      gg i = gradient (Torus.lift D.V) (y i) 0 - gradient (Torus.lift D.V) (y' i) 0 :=
    ⟨_, fun _ => rfl⟩
  have hcoord : ∀ i, liftedDrift D y i 0 - liftedDrift D y' i 0 =
      (a / N) * (∑ j, fc i j) - (a / N) * (∑ j, fr i j) - gg i := by
    intro i
    rw [cepk2_drift_coord hs hM hρ hfree i, cepk2_drift_coord hs hM hρ hfree' i, hgg]
    have h1 : ∑ j ∈ Finset.univ.erase i, (cepk2_c (y i 0 - y j 0) - ρ (y i 0 - y j 0)) -
        ∑ j ∈ Finset.univ.erase i, (cepk2_c (y' i 0 - y' j 0) - ρ (y' i 0 - y' j 0)) =
        ∑ j, (fc i j - fr i j) := by
      have h0 : fc i i - fr i i = 0 := by rw [hfc, hfr]; simp
      rw [← Finset.sum_sub_distrib,
        ← Finset.sum_erase (Finset.univ : Finset (Fin N)) (f := fun j => fc i j - fr i j) h0]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hfc, hfr]; ring
    have h1' : ∑ j, (fc i j - fr i j) = ∑ j, fc i j - ∑ j, fr i j := by
      rw [Finset.sum_sub_distrib]
    rw [h1'] at h1
    have h2 : (a / N) * (∑ j ∈ Finset.univ.erase i,
        (cepk2_c (y i 0 - y j 0) - ρ (y i 0 - y j 0))) -
        (a / N) * (∑ j ∈ Finset.univ.erase i,
        (cepk2_c (y' i 0 - y' j 0) - ρ (y' i 0 - y' j 0))) =
        (a / N) * (∑ j, fc i j) - (a / N) * (∑ j, fr i j) := by
      rw [← mul_sub, h1, mul_sub]
    linarith
  have hpair : ∀ i j, (δ i - δ j) * fc i j ≤ 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp
    · have h := cepk2_c_pair (cepk2_pair_case hord hord' hfree hfree' hij)
      rw [hfc, hδ, hδ]
      have e : y i 0 - y' i 0 - (y j 0 - y' j 0) = (y i 0 - y j 0) - (y' i 0 - y' j 0) := by ring
      rw [e]; exact h
  have hanti : ∀ i j, fc j i = - fc i j := by
    intro i j
    rw [hfc, hfc, show y j 0 - y i 0 = -(y i 0 - y j 0) by ring,
      show y' j 0 - y' i 0 = -(y' i 0 - y' j 0) by ring, cepk2_c_neg, cepk2_c_neg]
    ring
  have hAc := cepk2_sum_antisym δ fc hanti hpair
  have hfrb : ∀ i j, |-(fr i j)| ≤ Lρ * (|δ i| + |δ j|) := by
    intro i j
    rw [abs_neg, hfr]
    refine (hLρ _ _).trans ?_
    have e : y i 0 - y j 0 - (y' i 0 - y' j 0) = δ i - δ j := by rw [hδ, hδ]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (abs_sub _ _) hLρ0
  have hAr := cepk2_sum_lip δ (fun i j => -(fr i j)) hLρ0 hfrb
  simp only [mul_neg, Finset.sum_neg_distrib] at hAr
  have hg : ∀ i, -(δ i * gg i) ≤ (LV : ℝ) * δ i ^ 2 := by
    intro i
    have h1 := hLV.dist_le_mul (y i) (y' i)
    rw [dist_eq_norm, dist_eq_norm] at h1
    have h2 : |gg i| ≤ (LV : ℝ) * |δ i| := by
      have h3 : |gg i| ≤ ‖gradient (Torus.lift D.V) (y i) - gradient (Torus.lift D.V) (y' i)‖ := by
        rw [hgg]
        have := PiLp.norm_apply_le (gradient (Torus.lift D.V) (y i) - gradient (Torus.lift D.V) (y' i)) 0
        simpa using this
      have h4 : ‖y i - y' i‖ = |δ i| := by
        rw [hδ]
        have := cepk2_norm_sq (y i - y' i)
        have h5 : ‖y i - y' i‖ = |(y i - y' i) 0| := by
          rw [← Real.sqrt_sq (norm_nonneg _), this, Real.sqrt_sq_eq_abs]
        simpa using h5
      rw [h4] at h1
      exact h3.trans h1
    calc -(δ i * gg i) ≤ |δ i| * |gg i| := by
          rw [← abs_mul]; exact neg_le_abs _
      _ ≤ |δ i| * ((LV : ℝ) * |δ i|) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = (LV : ℝ) * δ i ^ 2 := by rw [← sq_abs (δ i)]; ring
  have hnorm : ∀ i, ‖y i - y' i‖ ^ 2 = δ i ^ 2 := by
    intro i; rw [cepk2_norm_sq, hδ]; simp
  have hterm : ∀ i, inner ℝ (y i - y' i) (liftedDrift D y i - liftedDrift D y' i) =
      (a / N) * (∑ j, δ i * fc i j) - (a / N) * (∑ j, δ i * fr i j) - δ i * gg i := by
    intro i
    rw [cepk2_inner, PiLp.sub_apply, hcoord, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [PiLp.sub_apply, ← hδ]
    ring
  simp only [hterm, hnorm]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hG : -(∑ i, δ i * gg i) ≤ (LV : ℝ) * ∑ i, δ i ^ 2 := by
    rw [← Finset.sum_neg_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hg i
  have hc1 : (a / N) * ∑ i, ∑ j, δ i * fc i j ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (div_nonneg ha hNpos.le) hAc
  have hc2 : -((a / N) * ∑ i, ∑ j, δ i * fr i j) ≤ 2 * a * Lρ * ∑ i, δ i ^ 2 := by
    have := mul_le_mul_of_nonneg_left hAr (div_nonneg ha hNpos.le)
    have e : a / N * (2 * N * Lρ * ∑ i, δ i ^ 2) = 2 * a * Lρ * ∑ i, δ i ^ 2 := by
      field_simp
    rw [e] at this
    linarith
  nlinarith

end HRS.MC.CepK2
