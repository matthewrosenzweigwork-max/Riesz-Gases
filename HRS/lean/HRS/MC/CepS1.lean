import HRS.Stochastic.ParticleLog
import HRS.MC.CepS1Aux3
import HRS.MC.CepC3

/-!
# Packet CEPS1: the logarithmic noncollision barrier chain under a `C^{1,1}` potential

`HRS.particle_no_collision_d1_log` (`HRS/Stochastic/ParticleLog.lean`) with `cep_IsC11 D.V` in place of
`Torus.IsCk 2 D.V`; the pair barrier and the descending induction are copied, and the cluster barrier chain
comes from `HRS.MC.CepS1Aux1`-`Aux3`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepS1

open HRS HRS.ClusterBarrier HRS.MC.CepC0

variable {N : ℕ}
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}

theorem d1_pair_barrier_log [IsProbabilityMeasure P] (D : DynData 1) (hK : KernelLocal 1 D.s)
    (hV : cep_IsC11 D.V) (hs : D.s = 0) {a : ℝ} (ha : 0 < a) (hM : D.M 0 0 = -a)
    (hthr : (N : ℝ) * D.invβ ≤ a)
    (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → (Fin N → Euc 1)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc 1)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) (i j : Fin N) (hij : i ≠ j)
    (hind : ∀ J : Finset (Fin N), ({i, j} : Finset (Fin N)) ⊂ J → J.card = 3 →
      ∀ T : ℝ, P {ω | ClusterCollapse J T τ Y ω} = 0)
    (T : ℝ) : P {ω | ClusterCollapse ({i, j} : Finset (Fin N)) T τ Y ω} = 0 := by
  have hI : 2 ≤ ({i, j} : Finset (Fin N)).card := by rw [Finset.card_pair hij]
  have hMa : D.M 0 0 ≤ 0 := by rw [hM]; linarith
  refine cluster_barrier_of_hit D hsol ({i, j} : Finset (Fin N)) hI ?_ ?_ T
  · intro δ hδ q₁ hq₁ T'
    obtain ⟨q, C₀, hq, hqr, hC₀, hrem⟩ := clusterRemainder_bound D hK hV _ hI δ hδ
    obtain ⟨q₂, hq₂, -, hint⟩ := d1_internal_ge_log D hs ha hM hthr hij
    obtain ⟨C', hC'0, hC'⟩ := barrier_generator_bound_of_internal D (symNonpos_of_d1 D.M hMa) _ hI
      (q := min q q₂)
      (lt_min hq hq₂) (lt_of_le_of_lt (min_le_left _ _) hqr) hC₀
      {Z | ∀ j', j' ∉ ({i, j} : Finset (Fin N)) → δ ≤ clusterDispersionLift (insert j' {i, j}) Z}
      (fun Y hYS hYf hYq => hrem Y hYf (lt_of_lt_of_le hYq (min_le_left _ _)) hYS)
      (fun Y _ hYf hYq => by
        have hpos := clusterDispersionLift_pos hI hYf
        have h2 := hint Y hpos (by linarith [min_le_right q q₂])
        rw [Finset.card_pair hij]
        norm_num
        linarith)
    exact cluster_hitting_of_gen D hK hV hW' hsol _ hI (lt_min hq hq₂) hC'0 δ
      (fun Z hZS hZf => hC' Z hZS hZf) q₁ hq₁ T'
  · intro J hJ hJc T'
    exact hind J hJ (by rw [hJc, Finset.card_pair hij]) T'

theorem particle_no_collision_d1_log [IsProbabilityMeasure P] (D : DynData 1) (hs : D.s = 0)
    {a : ℝ} (ha : 0 < a) (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ)))
    (hthr : (N : ℝ) * D.invβ ≤ a) (hV : cep_IsC11 D.V)
    (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → (Fin N → Euc 1)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc 1)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) :
    ∀ᵐ ω ∂P, τ ω = ⊤ := by
  have hMa : D.M 0 0 = -a := by rw [hM]; simp
  have hM' : Torus.SymNonpos D.M := symNonpos_of_d1 D.M (by rw [hMa]; linarith)
  classical
  have hs1 : D.s < 1 := by simpa using D.hsd
  have hK : KernelLocal 1 D.s := kernelLocal_d1 D.hs0 hs1
  have key : ∀ m : ℕ, ∀ I : Finset (Fin N), 2 ≤ I.card → N - I.card = m →
      ∀ T : ℝ, P {ω | ClusterCollapse I T τ Y ω} = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro I hI hm T
      have hIN : I.card ≤ N := by simpa using Finset.card_le_univ I
      have hind : ∀ J : Finset (Fin N), I ⊂ J → J.card = I.card + 1 →
          ∀ T : ℝ, P {ω | ClusterCollapse J T τ Y ω} = 0 := by
        intro J _ hJc T'
        have hJN : J.card ≤ N := by simpa using Finset.card_le_univ J
        exact ih (N - J.card) (by omega) J (by omega) rfl T'
      by_cases h3 : 3 ≤ I.card
      · refine cluster_barrier D hK hM' hV hW' hsol I hI ?_ hind T
        have : 2 ≤ I.card - 1 := by omega
        simpa using this
      · have h2 : I.card = 2 := by omega
        obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 h2
        have hind' : ∀ J : Finset (Fin N), ({i, j} : Finset (Fin N)) ⊂ J → J.card = 3 →
            ∀ T : ℝ, P {ω | ClusterCollapse J T τ Y ω} = 0 :=
          fun J hJ hJc T' => hind J hJ (by rw [hJc, h2]) T'
        exact d1_pair_barrier_log D hK hV hs ha hMa hthr hW' hsol i j hij hind' T
  have h1 : ∀ I : Finset (Fin N), 2 ≤ I.card → ∀ T : ℝ, P {ω | ClusterCollapse I T τ Y ω} = 0 :=
    fun I hI T => key _ I hI rfl T
  have hcol := HRS.MC.CepC3.cep_C3_collision_alternative_proof D hK hV hW' hsol
  have hnull : P (⋃ T : ℕ, ⋃ i : Fin N, ⋃ j : Fin N, ⋃ (_ : i ≠ j),
      {ω | ClusterCollapse ({i, j} : Finset (Fin N)) (T : ℝ) τ Y ω}) = 0 := by
    refine measure_iUnion_null fun T => measure_iUnion_null fun i => measure_iUnion_null fun j =>
      measure_iUnion_null fun hij => h1 _ ?_ _
    rw [Finset.card_pair hij]
  have hn2 := measure_eq_zero_iff_ae_notMem.1 hnull
  filter_upwards [hcol, hn2] with ω hω hnot
  by_contra hne
  have hlt : τ ω < ⊤ := lt_top_iff_ne_top.2 hne
  obtain ⟨τ₀, hτ₀⟩ := WithTop.ne_top_iff_exists.1 hne
  obtain ⟨T, hT⟩ := exists_nat_gt τ₀
  have hτT : ∀ t : ℝ, (t : WithTop ℝ) < τ ω → t < (T : ℝ) := by
    intro t ht
    rw [← hτ₀] at ht
    have : t < τ₀ := by exact_mod_cast ht
    linarith
  apply hnot
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  by_contra hno
  push_neg at hno
  have hpair : ∀ p : Fin N × Fin N, ∃ ε : ℝ, 0 < ε ∧ (p.1 ≠ p.2 → ∀ t : ℝ, 0 ≤ t → t < T →
      (t : WithTop ℝ) < τ ω → ε ≤ clusterDispersionLift ({p.1, p.2} : Finset (Fin N)) (Y t ω)) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨1, one_pos, fun h => absurd hp h⟩
    · have := hno T p.1 p.2 hp
      unfold ClusterCollapse at this
      push_neg at this
      obtain ⟨ε, hε, h⟩ := this
      exact ⟨ε, hε, fun _ t h0 h1 h2 => h t h0 h1 h2⟩
  choose ε hε0 hε using hpair
  obtain ⟨e, he0, hele⟩ := exists_pos_le_fintype ε hε0
  obtain ⟨t, ht1, htτ, i, j, hij, hdist⟩ := hω hlt (min (1 / 8) (16 * e)) (lt_min (by norm_num)
    (by linarith)) 0 le_rfl (by simpa using hsol.pos ω)
  have hr8 : Torus.tdist (Torus.mk (Y t ω i)) (Torus.mk (Y t ω j)) < 1 / 8 :=
    lt_of_lt_of_le hdist (min_le_left _ _)
  have hr16 : Torus.tdist (Torus.mk (Y t ω i)) (Torus.mk (Y t ω j)) < 16 * e :=
    lt_of_lt_of_le hdist (min_le_right _ _)
  have hQ := clusterDispersionLift_pair hij (Y t ω) hr8
  have hnn : 0 ≤ Torus.tdist (Torus.mk (Y t ω i)) (Torus.mk (Y t ω j)) := norm_nonneg _
  have hlow := hε (i, j) hij t ht1.le (hτT t htτ) htτ
  have := hele (i, j)
  set r := Torus.tdist (Torus.mk (Y t ω i)) (Torus.mk (Y t ω j))
  simp only at hlow
  rw [hQ] at hlow
  nlinarith

/-- **S1 (barrier chain under `C^{1,1}`)**.  Statement verbatim from `HRS.MC.Cepa.cep_S1_no_explosion_log`
(with the duplicated predicate `cep_IsC11`). -/
theorem cep_S1_no_explosion_log_proof {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (D : DynData 1) (hs : D.s = 0) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hthr : (N : ℝ) * D.invβ ≤ a)
    (hV : cep_IsC11 D.V) (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → (Fin N → Euc 1)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc 1)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) : ∀ᵐ ω ∂P, τ ω = ⊤ :=
  particle_no_collision_d1_log D hs ha hM hthr hV hW' hsol

end HRS.MC.CepS1
