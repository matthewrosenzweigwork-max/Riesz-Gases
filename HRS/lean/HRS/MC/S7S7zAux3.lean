import HRS.MC.S7S7zAux2
import HRS.Energy.StaticLimitJoint

/-!
# Packet `s7_S7z_product_case`, helper 3: the probability space `((N -> T^d) x E_r, Pinf mu (x) G)`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.Sec7.S7z

open HRS HRS.Sec7 HRS.StaticLimitAux

variable {d : ℕ} {r : ℝ}

/-- The product probability space. -/
abbrev s7zP (μ : Measure (Torus d)) (G : Measure (NegSobolev d r)) :
    Measure ((ℕ → Torus d) × NegSobolev d r) :=
  (Pinf μ).prod G

section Space

variable (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (G : Measure (NegSobolev d r))
  [IsProbabilityMeasure G] {Y : Torus d → NegSobolev d r} (hY : Measurable Y)

theorem s7z_map_fst : (s7zP μ G).map Prod.fst = Pinf μ := by
  simp [s7zP]

theorem s7z_map_snd : (s7zP μ G).map Prod.snd = G := by
  simp [s7zP]

include hY in
theorem s7z_law_X (i : ℕ) :
    HRS.law (s7zP μ G) (fun ω => Y (ω.1 i)) = μ.map Y := by
  have h : (fun ω : (ℕ → Torus d) × NegSobolev d r => Y (ω.1 i)) = Xi Y i ∘ Prod.fst := rfl
  unfold HRS.law
  rw [h, ← Measure.map_map (measurable_Xi hY i) measurable_fst, s7z_map_fst]
  exact law_Xi μ hY i

include hY in
theorem s7z_iid : HRS.IsIIDCopies (s7zP μ G) (fun (i : ℕ) (ω : (ℕ → Torus d) × NegSobolev d r) => Y (ω.1 i)) := by
  refine ⟨?_, fun i j => by rw [s7z_law_X μ G hY i, s7z_law_X μ G hY j]⟩
  have h := (iid_Xi μ hY (H := NegSobolev d r)).1
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S sets hsets
  have e1 : (⋂ i ∈ S, (fun ω : (ℕ → Torus d) × NegSobolev d r => Y (ω.1 i)) ⁻¹' sets i) =
      Prod.fst ⁻¹' (⋂ i ∈ S, Xi Y i ⁻¹' sets i) := by
    ext ω; simp [Xi]
  have e2 : ∀ i, (fun ω : (ℕ → Torus d) × NegSobolev d r => Y (ω.1 i)) ⁻¹' sets i =
      Prod.fst ⁻¹' (Xi Y i ⁻¹' sets i) := fun i => rfl
  have hm1 : MeasurableSet (⋂ i ∈ S, Xi Y i ⁻¹' sets i) :=
    MeasurableSet.biInter S.countable_toSet fun i hi => measurable_Xi hY i (hsets i hi)
  rw [e1, ← Measure.map_apply measurable_fst hm1, s7z_map_fst]
  simp_rw [e2]
  rw [Finset.prod_congr rfl fun i hi => by
    rw [← Measure.map_apply measurable_fst (measurable_Xi hY i (hsets i hi)), s7z_map_fst]]
  exact h S hsets

include hY in
theorem s7z_integral_sum (Φ : NegSobolev d r → ℝ) (hΦ : Continuous Φ) (N : ℕ) :
    ∫ ω, Φ ((Real.sqrt N)⁻¹ • ∑ i : Fin N, Y (ω.1 i)) ∂(s7zP μ G) =
      ∫ z, Φ (Ssum Y N z) ∂(Measure.pi fun _ : Fin N => μ) := by
  have hr : Measurable (fun (ω : ℕ → Torus d) (j : Fin N) => ω j) :=
    Measurable.of_eval fun j => measurable_pi_apply _
  have hT : Measurable (fun (ω : (ℕ → Torus d) × NegSobolev d r) (j : Fin N) => ω.1 j) :=
    hr.comp measurable_fst
  have hmap : (s7zP μ G).map (fun (ω : (ℕ → Torus d) × NegSobolev d r) (j : Fin N) => ω.1 j) =
      Measure.pi fun _ : Fin N => μ := by
    rw [show (fun (ω : (ℕ → Torus d) × NegSobolev d r) (j : Fin N) => ω.1 j) =
      (fun (ω : ℕ → Torus d) (j : Fin N) => ω j) ∘ Prod.fst from rfl,
      ← Measure.map_map hr measurable_fst, s7z_map_fst]
    exact map_restrict_eq μ N
  rw [← hmap]
  exact (integral_map hT.aemeasurable
    ((hΦ.measurable.comp (measurable_Ssum' hY N)).aestronglyMeasurable)).symm

theorem s7z_integral_snd (Φ : NegSobolev d r → ℝ) (hΦ : Continuous Φ) :
    ∫ ω, Φ ω.2 ∂(s7zP μ G) = ∫ F, Φ F ∂G := by
  rw [← s7z_map_snd μ G, integral_map measurable_snd.aemeasurable hΦ.aestronglyMeasurable]
  rw [s7z_map_snd]

theorem s7z_third (hYc : Continuous Y) {C : ℝ} (hC : ∀ x, ‖Y x‖ ≤ C) {Φ : NegSobolev d r → ℝ}
    (hΦ : Φ ∈ CbUnitBall (NegSobolev d r) 3) :
    thirdMomentPairing (s7zP μ G) Φ (fun ω => ω.2) (fun ω => Y (ω.1 0)) =
      ∫ F, ∫ x, iteratedFDeriv ℝ 3 Φ F ![Y x, Y x, Y x] ∂μ ∂G := by
  set f : NegSobolev d r × Torus d → ℝ := fun q => iteratedFDeriv ℝ 3 Φ q.1 ![Y q.2, Y q.2, Y q.2]
    with hf
  have hcont : Continuous f := by
    have h1 : Continuous fun q : NegSobolev d r × Torus d => iteratedFDeriv ℝ 3 Φ q.1 :=
      (hΦ.1.continuous_iteratedFDeriv (by norm_num)).comp continuous_fst
    have hv : Continuous fun q : NegSobolev d r × Torus d =>
        (![Y q.2, Y q.2, Y q.2] : Fin 3 → NegSobolev d r) := by
      refine continuous_pi fun i => ?_
      fin_cases i <;> exact hYc.comp continuous_snd
    exact h1.eval hv
  have hb : ∀ q, ‖f q‖ ≤ C ^ 3 := fun q => by
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    have h1 := iteratedFDeriv_norm_le_of_mem hΦ (le_refl 3) q.1
    have h2 : ∏ i, ‖(![Y q.2, Y q.2, Y q.2] : Fin 3 → NegSobolev d r) i‖ ≤ C ^ 3 := by
      simp only [Fin.prod_univ_three]
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC q.2)
      have := hC q.2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      calc ‖Y q.2‖ * ‖Y q.2‖ * ‖Y q.2‖ ≤ C * C * C := by gcongr
        _ = C ^ 3 := by ring
    calc _ ≤ 1 * C ^ 3 := mul_le_mul h1 h2 (Finset.prod_nonneg fun i _ => norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hint : Integrable f (G.prod μ) :=
    Integrable.of_bound hcont.aestronglyMeasurable (C ^ 3) (Filter.Eventually.of_forall hb)
  have hev : Measurable (fun ω : (ℕ → Torus d) × NegSobolev d r => ω.1 0) :=
    (measurable_pi_apply 0).comp measurable_fst
  have hT : Measurable (Prod.map (Prod.snd : (ℕ → Torus d) × NegSobolev d r → NegSobolev d r)
      (fun ω : (ℕ → Torus d) × NegSobolev d r => ω.1 0)) := measurable_snd.prodMap hev
  have hmap : ((s7zP μ G).prod (s7zP μ G)).map
      (Prod.map (Prod.snd : (ℕ → Torus d) × NegSobolev d r → NegSobolev d r)
        (fun ω : (ℕ → Torus d) × NegSobolev d r => ω.1 0)) = G.prod μ := by
    rw [← Measure.map_prod_map _ _ measurable_snd hev, s7z_map_snd]
    congr 1
    rw [show (fun ω : (ℕ → Torus d) × NegSobolev d r => ω.1 0) = (fun ω : ℕ → Torus d => ω 0) ∘ Prod.fst
      from rfl, ← Measure.map_map (measurable_pi_apply 0) measurable_fst, s7z_map_fst]
    exact Measure.infinitePi_map_eval (μ := fun _ : ℕ => μ) 0
  unfold thirdMomentPairing
  change ∫ p, f (Prod.map Prod.snd (fun ω : (ℕ → Torus d) × NegSobolev d r => ω.1 0) p) ∂_ = _
  rw [← integral_map hT.aemeasurable hcont.aestronglyMeasurable, hmap, integral_prod _ hint]

end Space

end HRS.MC.Sec7.S7z
