import Mathlib
import HRS.MC.CepN3Aux1
import HRS.MC.CepN2

/-!
# Packet CEPN3, auxiliary 2: the steering path

The convex combination `c(t) = y₀ + θ(t)(y* - y₀)` of two strictly `σ`-ordered configurations is strictly
ordered, hence collision free; the noise path `v(t) = c(t) - c(0) - ∫₀ᵗ b(c)` is continuous.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepN3

open HRS HRS.MC.CepN4

variable {N : ℕ}

lemma cepn3_circle_ne {a b : ℝ} (hab : a < b) (hba : b < a + 1) :
    ((a : ℝ) : UnitAddCircle) ≠ ((b : ℝ) : UnitAddCircle) := by
  intro h
  have h' := (QuotientAddGroup.eq).1 h
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 h'
  simp only [zsmul_eq_mul, mul_one] at hk
  have h1 : (0 : ℝ) < k := by rw [hk]; linarith
  have h2 : (k : ℝ) < 1 := by rw [hk]; linarith
  have h1' : (0 : ℤ) < k := by exact_mod_cast h1
  have h2' : k < (1 : ℤ) := by exact_mod_cast h2
  omega

lemma cepn3_free_of_ordered {σ : Equiv.Perm (Fin N)} {y : Fin N → Euc 1}
    (hy : cep_StrictlyOrdered σ y) : y ∈ liftedFree 1 N := by
  rintro ⟨i, j, hij, h⟩
  have h0 : ((y i 0 : ℝ) : UnitAddCircle) = ((y j 0 : ℝ) : UnitAddCircle) := congr_fun h 0
  obtain ⟨k, rfl⟩ : ∃ k, σ k = i := ⟨σ.symm i, by simp⟩
  obtain ⟨k', rfl⟩ : ∃ k, σ k = j := ⟨σ.symm j, by simp⟩
  have hkk : k ≠ k' := fun e => hij (by rw [e])
  rcases lt_or_gt_of_ne hkk with hlt | hgt
  · exact cepn3_circle_ne (hy.1 k k' hlt) (hy.2 k k') h0
  · exact cepn3_circle_ne (hy.1 k' k hgt) (hy.2 k' k) h0.symm

/-- The clamped parameter. -/
def cepn3_theta (T' t : ℝ) : ℝ := max 0 (min 1 (t / T'))

lemma cepn3_theta_nonneg (T' t : ℝ) : 0 ≤ cepn3_theta T' t := le_max_left _ _

lemma cepn3_theta_le (T' t : ℝ) : cepn3_theta T' t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma cepn3_theta_cont (T' : ℝ) : Continuous (cepn3_theta T') := by
  unfold cepn3_theta; fun_prop

lemma cepn3_theta_zero (T' : ℝ) : cepn3_theta T' 0 = 0 := by
  simp [cepn3_theta]

lemma cepn3_theta_T {T' : ℝ} (hT' : 0 < T') : cepn3_theta T' T' = 1 := by
  simp [cepn3_theta, div_self hT'.ne']

/-- The straight-line path. -/
def cepn3_c (y₀ ys : Fin N → Euc 1) (T' t : ℝ) : Fin N → Euc 1 :=
  y₀ + cepn3_theta T' t • (ys - y₀)

lemma cepn3_c_cont (y₀ ys : Fin N → Euc 1) (T' : ℝ) : Continuous (cepn3_c y₀ ys T') := by
  unfold cepn3_c
  exact continuous_const.add ((cepn3_theta_cont T').smul continuous_const)

lemma cepn3_c_zero (y₀ ys : Fin N → Euc 1) (T' : ℝ) : cepn3_c y₀ ys T' 0 = y₀ := by
  simp [cepn3_c, cepn3_theta_zero]

lemma cepn3_c_T (y₀ ys : Fin N → Euc 1) {T' : ℝ} (hT' : 0 < T') : cepn3_c y₀ ys T' T' = ys := by
  simp [cepn3_c, cepn3_theta_T hT']

lemma cepn3_c_ordered {σ : Equiv.Perm (Fin N)} {y₀ ys : Fin N → Euc 1}
    (h0 : cep_StrictlyOrdered σ y₀) (h1 : cep_StrictlyOrdered σ ys) (T' t : ℝ) :
    cep_StrictlyOrdered σ (cepn3_c y₀ ys T' t) := by
  have hθ0 := cepn3_theta_nonneg T' t
  have hθ1 := cepn3_theta_le T' t
  set θ := cepn3_theta T' t
  have hc : ∀ i, cepn3_c y₀ ys T' t i 0 = (1 - θ) * y₀ i 0 + θ * ys i 0 := fun i => by
    simp [cepn3_c, θ]; ring
  refine ⟨fun k k' hkk => ?_, fun k k' => ?_⟩
  · rw [hc, hc]
    have a := h0.1 k k' hkk
    have b := h1.1 k k' hkk
    nlinarith [mul_nonneg (sub_nonneg.2 hθ1) (sub_nonneg.2 a.le), mul_nonneg hθ0 (sub_nonneg.2 b.le),
      mul_pos_iff.2 (Or.inl ⟨(by linarith : (0:ℝ) < 1), sub_pos.2 a⟩)]
  · rw [hc, hc]
    have a := h0.2 k k'
    have b := h1.2 k k'
    nlinarith [mul_nonneg (sub_nonneg.2 hθ1) (sub_nonneg.2 a.le), mul_nonneg hθ0 (sub_nonneg.2 b.le)]

lemma cepn3_c_free {σ : Equiv.Perm (Fin N)} {y₀ ys : Fin N → Euc 1}
    (h0 : cep_StrictlyOrdered σ y₀) (h1 : cep_StrictlyOrdered σ ys) (T' t : ℝ) :
    cepn3_c y₀ ys T' t ∈ liftedFree 1 N :=
  cepn3_free_of_ordered (cepn3_c_ordered h0 h1 T' t)

/-- The drift is continuous on the free region. -/
lemma cepn3_continuousOn_drift {D : DynData 1} (hs : D.s = 0) (hV : HRS.MC.CepC0.cep_IsC11 D.V) :
    ContinuousOn (liftedDrift (N := N) D) (liftedFree 1 N) := by
  have hK : Torus.IsSmoothOffZero (periodicRieszGrad 1 D.s) :=
    (kernelLocal_d1 (by rw [hs]) (by rw [hs]; norm_num)).smoothOffZero
  have hloc : IsLocLipschitzDrift (liftedFree 1 N) (fun _ Z => liftedDrift (N := N) D Z) :=
    HRS.MC.CepC0.cep_C0_locLipschitz_proof (d := 1) (N := N) D hK hV
  have hg : ContinuousOn (fun z : Fin N → Euc 1 => ((0 : ℝ), z)) (liftedFree 1 N) :=
    continuousOn_const.prodMk continuousOn_id
  have hmap : Set.MapsTo (fun z : Fin N → Euc 1 => ((0 : ℝ), z)) (liftedFree 1 N)
      (Set.Ici (0 : ℝ) ×ˢ liftedFree 1 N) := fun z hz => Set.mk_mem_prod (Set.mem_Ici.2 le_rfl) hz
  have h := ContinuousOn.comp (g := Function.uncurry fun (_ : ℝ) (Z : Fin N → Euc 1) => liftedDrift D Z)
    hloc.cont hg hmap
  refine h.congr fun z _ => ?_
  simp only [Function.comp_apply, Function.uncurry_apply_pair]

/-- Deterministic steering path with its noise path. -/
theorem cepn3_det {D : DynData 1} (hs : D.s = 0) (hV : HRS.MC.CepC0.cep_IsC11 D.V) {T' : ℝ} (hT' : 0 < T')
    {σ : Equiv.Perm (Fin N)} {y₀ ys : Fin N → Euc 1} (h0 : cep_StrictlyOrdered σ y₀)
    (h1 : cep_StrictlyOrdered σ ys) :
    ∃ c v : ℝ → Fin N → Euc 1, Continuous c ∧ Continuous v ∧ v 0 = 0 ∧ c 0 = y₀ ∧ c T' = ys ∧
      (∀ t, c t ∈ liftedFree 1 N) ∧
      ∀ t, c t = c 0 + (∫ u in (0 : ℝ)..t, liftedDrift D (c u)) + v t := by
  have hc := cepn3_c_cont y₀ ys T'
  have hb : Continuous fun u => liftedDrift (N := N) D (cepn3_c y₀ ys T' u) :=
    (cepn3_continuousOn_drift hs hV).comp_continuous hc (cepn3_c_free h0 h1 T')
  refine ⟨cepn3_c y₀ ys T', fun t => cepn3_c y₀ ys T' t - cepn3_c y₀ ys T' 0 -
    ∫ u in (0 : ℝ)..t, liftedDrift D (cepn3_c y₀ ys T' u), hc, ?_, by simp, cepn3_c_zero _ _ _,
    cepn3_c_T _ _ hT', cepn3_c_free h0 h1 T', fun t => by module⟩
  exact (hc.sub continuous_const).sub
    (intervalIntegral.continuous_primitive (fun a b => hb.intervalIntegrable a b) 0)

end HRS.MC.CepN3
