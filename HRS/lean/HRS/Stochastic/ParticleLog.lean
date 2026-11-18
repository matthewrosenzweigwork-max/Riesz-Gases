import HRS.Stochastic.Particle

/-!
# The one-dimensional logarithmic noncollision threshold (Remark `B:rem:d1-threshold-sharp`)

Source: `HRS_periodic_main_20261008T010000Z.tex`, Remark B.13 (L11977-11985).
Sufficiency half: for `d = 1`, `s = 0` (periodic logarithmic kernel), `M = -a` with `a > 0`
and positive (or zero) temperature, the threshold `a β_N ≥ N`, i.e. `N * D.invβ ≤ a`, gives a.s.
noncollision and global collision-free strong well-posedness.  The argument is the barrier
argument of `d1_pair_barrier` / `particle_no_collision_d1` of `Particle.lean`, with the `s = 0`
internal term, which is the constant `2a/N` instead of the Riesz blow-up `Q^{-s/2-1}`.  Clusters
of size `≥ 3` are untouched (`cluster_barrier`); only the pair step changes, and for a pair the
hypothesis of `barrier_generator_bound_of_internal`, `4 invβ ≤ 2 invβ + 2a/N`, is exactly
`N invβ ≤ a`.

The necessity half (collisions occur with positive probability below the threshold) is not
formalised here: it needs the external input that the gap process is comparable to a Bessel
process of dimension `δ = 1 + aβ/N < 2`, which hits `0` almost surely (Cépa–Lépingle 1997/2001,
Theorem 3.1), and the notion of Cépa–Lépingle flow (`IsCepaLepingleFlow`), which is not yet
defined in this branch.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

open ClusterBarrier

variable {N : ℕ}

/-! ### The `s = 0` internal term -/

open Matrix in
/-- Logarithmic force term: for `s = 0`, `z ⬝ M ∇g_E(z) = -M₀₀` for every `z ≠ 0`
(`∇g_E(z) = -|z|⁻² z`). -/
theorem d1_force_term_log (D : DynData 1) (hs : D.s = 0) (z : Euc 1) (hz : z ≠ 0) :
    inner ℝ z (Torus.matVec D.M (eucRieszGrad D.s z)) = -(D.M 0 0) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have e : Torus.matVec D.M (eucRieszGrad D.s z) = -(rieszRadial D.s z) • Torus.matVec D.M z := by
    unfold eucRieszGrad Torus.matVec; exact map_smul _ _ _
  rw [e, real_inner_smul_right, inner_matVec_eq]
  have h1 : z.ofLp ⬝ᵥ (D.M *ᵥ z.ofLp) = D.M 0 0 * ‖z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Matrix.mulVec, dotProduct]
    ring
  rw [h1]
  have h2 : rieszRadial D.s z = ‖z‖ ^ (-2 : ℝ) := by
    unfold rieszRadial; simp [hs]
  rw [h2]
  have h3 : ‖z‖ ^ (-2 : ℝ) * ‖z‖ ^ 2 = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn]; norm_num
  calc -(‖z‖ ^ (-2 : ℝ)) * (D.M 0 0 * ‖z‖ ^ 2)
      = -(D.M 0 0) * (‖z‖ ^ (-2 : ℝ) * ‖z‖ ^ 2) := by ring
    _ = _ := by rw [h3]; ring

/-- For `s = 0` the internal term of a pair is the constant `2(-M₀₀)/N` (`= 2a/N` for `M = -a`). -/
theorem d1_clusterInternal_pair_log (D : DynData 1) (hs : D.s = 0) {i j : Fin N} (hij : i ≠ j)
    (Y : Fin N → Euc 1) (hr : ‖geoRep (Y i - Y j)‖ < 1 / 8) (hr0 : geoRep (Y i - Y j) ≠ 0) :
    clusterInternal D ({i, j} : Finset (Fin N)) Y = (2 / (N : ℝ)) * (-(D.M 0 0)) := by
  have hanti := geoRep_antisymm Y i j hr
  unfold clusterInternal
  rw [Finset.sum_pair hij, Finset.sum_pair hij, Finset.sum_pair hij]
  have h0 : ∀ k : Fin N, geoRep (Y k - Y k) = 0 := fun k => by rw [sub_self]; exact geoRep_zero
  rw [h0, h0, hanti, d1_force_term_log D hs _ hr0, d1_force_term_log D hs _ (neg_ne_zero.2 hr0)]
  simp [eucRieszGrad, Torus.matVec]
  ring

/-- Log-kernel analogue of `d1_internal_ge`: for `s = 0`, `M = -a` and `N * invβ ≤ a`, the
pair internal term dominates `2 invβ` on `{0 < Q < q₂}`. -/
theorem d1_internal_ge_log (D : DynData 1) (hs : D.s = 0) {a : ℝ} (ha : 0 < a)
    (hM : D.M 0 0 = -a) (hthr : (N : ℝ) * D.invβ ≤ a) {i j : Fin N} (hij : i ≠ j) :
    ∃ q₂ : ℝ, 0 < q₂ ∧ q₂ ≤ clusterRadius ({i, j} : Finset (Fin N)) ∧
      ∀ Y : Fin N → Euc 1, 0 < clusterDispersionLift ({i, j} : Finset (Fin N)) Y →
        clusterDispersionLift ({i, j} : Finset (Fin N)) Y < q₂ →
        2 * D.invβ ≤ clusterInternal D ({i, j} : Finset (Fin N)) Y := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos i
  have hrad : clusterRadius ({i, j} : Finset (Fin N)) = 1 / 256 := by
    unfold clusterRadius; rw [Finset.card_pair hij]; norm_num
  refine ⟨1 / 256, by norm_num, hrad.symm.le, fun Y hQ0 hQ => ?_⟩
  have hQrad : clusterDispersionLift ({i, j} : Finset (Fin N)) Y <
      clusterRadius ({i, j} : Finset (Fin N)) := by
    rw [hrad]; exact hQ
  have hr8 : ‖geoRep (Y i - Y j)‖ < 1 / 8 :=
    (clusterDispersionLift_eq_euclid _ Y hQrad).1 i (by simp) j (by simp)
  have hQeq := clusterDispersionLift_pair hij Y (by simpa [Torus.tdist, geoRep, mk_sub'] using hr8)
  have he3 : Torus.tdist (Torus.mk (Y i)) (Torus.mk (Y j)) = ‖geoRep (Y i - Y j)‖ := by
    simp [Torus.tdist, geoRep, mk_sub']
  rw [he3] at hQeq
  have hrpos : 0 < ‖geoRep (Y i - Y j)‖ := by
    by_contra h
    have : ‖geoRep (Y i - Y j)‖ = 0 := le_antisymm (not_lt.1 h) (norm_nonneg _)
    rw [hQeq, this] at hQ0; simp at hQ0
  have hz : geoRep (Y i - Y j) ≠ 0 := fun h => by rw [h] at hrpos; simp at hrpos
  rw [d1_clusterInternal_pair_log D hs hij Y hr8 hz, hM]
  have h1 : D.invβ ≤ a / N := by rw [le_div_iff₀ hN]; linarith
  calc 2 * D.invβ ≤ 2 * (a / N) := by linarith
    _ = (2 / (N : ℝ)) * (-(-a)) := by ring

/-! ### The pair barrier, the noncollision theorem and well-posedness -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}

/-- Lemma `B:lem:d1-pair-barrier` for the logarithmic kernel (`s = 0`), at the threshold
`N β⁻¹ ≤ a` (Remark `B:rem:d1-threshold-sharp`, sufficiency): if no three-point enlargement of
the pair collapses before `T ∧ τ`, then the pair does not.  Same proof as `d1_pair_barrier`,
with `d1_internal_ge_log` in place of `d1_internal_ge`. -/
theorem d1_pair_barrier_log [IsProbabilityMeasure P] (D : DynData 1) (hK : KernelLocal 1 D.s)
    (hV : Torus.IsCk 2 D.V) (hs : D.s = 0) {a : ℝ} (ha : 0 < a) (hM : D.M 0 0 = -a)
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

/-- Proposition `B:prop:particle-no-collision-d1` for the logarithmic kernel at the threshold
(Remark `B:rem:d1-threshold-sharp`, sufficiency): `d = 1`, `s = 0`, `M = -a` with `a > 0`, and
`N β⁻¹ ≤ a` (that is, `a β_N ≥ N`); then `τ_⋆ = ∞` a.s.  Proof as `particle_no_collision_d1`:
descending induction on the cluster size, clusters of size `≥ 3` by `cluster_barrier`, pairs by
`d1_pair_barrier_log`, then the collision alternative. -/
theorem particle_no_collision_d1_log [IsProbabilityMeasure P] (D : DynData 1) (hs : D.s = 0)
    {a : ℝ} (ha : 0 < a) (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ)))
    (hthr : (N : ℝ) * D.invβ ≤ a) (hV : Torus.IsCk 2 D.V)
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
  have hcol := IsMaximalParticleSolution.collision_alternative D hK hV hW' hsol
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

/-- Proposition `B:thm:particle-wp` in the logarithmic `d = 1` regime above the threshold
(Remark `B:rem:d1-threshold-sharp`, sufficiency; the spec's `particle_wellposed_d1_log`): `d = 1`,
`s = 0`, `M = -a` with `a > 0`, `N β⁻¹ ≤ a`, `N ≥ 2`, `V ∈ C²`; the particle system has a
collision-free strong solution on `[0,T]` and is pathwise unique there.  Existence:
`exists_isStrongSolution_of_maximal` with `particle_no_collision_d1_log`; uniqueness:
`pathwiseUnique_of_locLipschitz` with `liftedDrift_locLipschitz` (`kernelLocal_d1` covers `s = 0`). -/
theorem particle_wellposed_d1_log {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : DynData 1) (hN : 2 ≤ N) (hs : D.s = 0) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hthr : (N : ℝ) * D.invβ ≤ a)
    (hV : Torus.IsCk 2 D.V)
    (X₀ : Ω → Config 1 N) (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    (W : ℝ≥0 → Ω → (Fin N → Euc 1)) (hW : IsVectorBrownian P W)
    (hind : ProbabilityTheory.IndepFun X₀ (fun ω => fun t => W t ω) P) (T : ℝ) (hT : 0 < T) :
    (∃ X, IsStrongSolution P D T X₀ W X) ∧ PathwiseUnique P D T X₀ W := by
  have hs1 : D.s < 1 := by simpa using D.hsd
  have hK : KernelLocal 1 D.s := kernelLocal_d1 D.hs0 hs1
  have hb : IsLocLipschitzDrift (liftedFree 1 N) (fun _ Z => liftedDrift D Z) :=
    liftedDrift_locLipschitz D hK.smoothOffZero hV
  refine ⟨?_, pathwiseUnique_of_locLipschitz P D hb T X₀ W hW⟩
  refine exists_isStrongSolution_of_maximal P D hb X₀ hX₀ hdist W hW hind ?_ T
  intro ℱ W' hW' _ Y₀ τ Y hsol _
  exact particle_no_collision_d1_log D hs ha hM hthr hV hW' hsol

end HRS
