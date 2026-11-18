import HRS.MC.CepH3Pf
import HRS.MC.CepH2C11
import HRS.MC.CepE2Props

/-!
# Packet CEPH4CORE: proof of `cep_H4_core` (entropy inequality for the limit flow)

Combine H3 (parts (a), (b), (c)) with the cylinder entropy dissipation H2 for the `C^{1,1}` potentials
`U_n = Φ_n + Ψ`, `n ≥ ⌈L⌉ + 1`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH4Core

open HRS HRS.MC.Cepa

lemma ch4c_ennreal_sub_ne_bot (x : ℝ≥0∞) (r : ℝ) :
    ((x : ℝ≥0∞) : EReal) - (r : EReal) ≠ ⊥ := by
  rw [sub_eq_add_neg, EReal.add_ne_bot_iff]
  refine ⟨?_, ?_⟩
  · simp
  · rw [← EReal.coe_neg]; simp

lemma ch4c_add_le {x y : ℕ → EReal} {a e : EReal} {r : ℝ} (hy : ∀ n, 0 ≤ y n)
    (hxa : a ≤ liminf x atTop) (hye : e ≤ liminf y atTop)
    (h : ∀ᶠ n in atTop, x n + y n ≤ (r : EReal)) : a + e ≤ (r : EReal) := by
  by_cases hab : a = ⊥
  · rw [hab, EReal.bot_add]; exact bot_le
  have hat : a ≠ ⊤ := by
    intro hat
    rw [hat] at hxa
    have h1 : ((r : ℝ) : EReal) < liminf x atTop := lt_of_lt_of_le (EReal.coe_lt_top r) hxa
    have h2 := eventually_lt_of_lt_liminf h1
    obtain ⟨n, hn1, hn2⟩ := (h2.and h).exists
    have h3 : x n ≤ x n + y n := by simpa using add_le_add_right (hy n) (x n)
    exact absurd (lt_of_lt_of_le hn1 (h3.trans hn2)) (lt_irrefl _)
  obtain ⟨a₀, rfl⟩ : ∃ a₀ : ℝ, (a₀ : EReal) = a := ⟨a.toReal, EReal.coe_toReal hat hab⟩
  have he : e ≤ ((r - a₀ : ℝ) : EReal) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨s, hs1, hs2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
    have hs : r - a₀ < s := by exact_mod_cast hs1
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (s - (r - a₀)) / 2 := ⟨_, rfl⟩
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    have h1 : ((a₀ - δ : ℝ) : EReal) < liminf x atTop :=
      lt_of_lt_of_le (by exact_mod_cast (by linarith : a₀ - δ < a₀)) hxa
    have h2 : (s : EReal) < liminf y atTop := lt_of_lt_of_le hs2 hye
    obtain ⟨n, hn1, hn2, hn3⟩ :=
      ((eventually_lt_of_lt_liminf h1).and ((eventually_lt_of_lt_liminf h2).and h)).exists
    have h5 := EReal.add_lt_add hn1 hn2
    rw [← EReal.coe_add] at h5
    have h4 := h5.trans_le hn3
    have h6 : a₀ - δ + s < r := by exact_mod_cast h4
    linarith
  calc (a₀ : EReal) + e ≤ (a₀ : EReal) + ((r - a₀ : ℝ) : EReal) := add_le_add_right he _
    _ = (r : EReal) := by rw [← EReal.coe_add]; congr 1; ring

lemma ch4c_hasGradient_add {N : ℕ} {f g : Ch N → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (x : Ch N) :
    HasGradientAt (fun w => f w + g w) (gradient f x + gradient g x) x := by
  rw [hasGradientAt_iff_hasFDerivAt, map_add, toDual_gradient, toDual_gradient]
  exact (hf x).hasFDerivAt.add (hg x).hasFDerivAt

lemma ch4c_gradient_add {N : ℕ} {f g : Ch N → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) :
    gradient (fun w => f w + g w) = fun x => gradient f x + gradient g x :=
  funext fun x => (ch4c_hasGradient_add hf hg x).gradient

section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem cep_H4_core_proof [IsProbabilityMeasure P] [NeZero N] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ) (hM : D.M = -(1 : Matrix (Fin 1) (Fin 1) ℝ))
    (hV : cep_IsC11 D.V) (σ₀ : Equiv.Perm (Fin N))
    {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida 1 N J) {Φn : ℝ → Ch N → ℝ}
    (hΦ : ∀ n z, 0 < n → HasGradientAt (Φn n) (n • (z - J n z)) z)
    (hΦle : ∀ n z, 0 < n → z ∈ cep_Alcove N → Φn n z ≤ cep_chamberPot 1 N z)
    (hΦlim : ∀ z, z ∈ cep_Alcove N → Filter.Tendsto (fun n : ℕ => Φn n z) Filter.atTop (𝓝 (cep_chamberPot 1 N z)))
    (hΦper : ∀ n z, 0 < n → Φn n (z + cep_diag N) = Φn n z)
    (hΦC : ∀ n, 0 < n → ContDiff ℝ 1 (Φn n) ∧ LipschitzWith (Real.toNNReal n) (gradient (Φn n)))
    (hΦlow : ∃ C : ℝ, ∀ n z, 0 < n → n / 2 * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ Φn n z)
    {Ψ : Ch N → ℝ} {L : ℝ≥0} (hΨ : ContDiff ℝ 1 Ψ) (hΨL : LipschitzWith L (gradient Ψ))
    (hΨper : ∀ z, Ψ (z + cep_diag N) = Ψ z)
    (hΨtot : ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y →
      totalPotential D (fun i => Torus.mk (y i)) = cep_chamberPot 1 N (cep_toCh π y) + Ψ (cep_toCh π y))
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) (hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' (fun _ => σ₀) (Real.sqrt (2 * D.invβ))
      (fun z => -(gradient (fun w => Φn n w + Ψ w) z)) z₀ (Z n))
    {Zl : ℝ → Ω → Ch N}
    (hZl : ∀ T : ℝ, ∀ ε : ℝ, 0 < ε → Filter.Tendsto (fun n : ℕ =>
        P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z n t ω - Zl t ω‖}) Filter.atTop (𝓝 0))
    (hZlc : ∀ ω, Continuous fun t => Zl t ω)
    (hZlA : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → Zl t ω ∈ closure (cep_Alcove N))
    (hZlnull : ∀ᵐ ω ∂P, ∀ T : ℝ, volume {s : ℝ | s ∈ Set.Icc 0 T ∧ Zl s ω ∉ cep_Alcove N} = 0)
    (hH0 : gibbsEntropy D (selectedLaw P (fun s ω => fun i => Torus.mk (cep_unrank σ₀ (Zl (s : ℝ) ω) i)) 0) < ⊤) :
    ∀ t : ℝ, 0 ≤ t →
      gibbsEntropy D (selectedLaw P (fun s ω => fun i => Torus.mk (cep_unrank σ₀ (Zl (s : ℝ) ω) i)) t)
        + ((ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N
            (selectedLaw P (fun s ω => fun i => Torus.mk (cep_unrank σ₀ (Zl (s : ℝ) ω) i)) r) : ℝ≥0∞) : EReal)
        ≤ gibbsEntropy D (selectedLaw P (fun s ω => fun i => Torus.mk (cep_unrank σ₀ (Zl (s : ℝ) ω) i)) 0) := by
  intro t ht
  obtain ⟨hA, hB, hC⟩ := HRS.MC.CepH3.cep_H3_limit_semicontinuity_proof hW' hs hβ hM hV σ₀ hJ hΦ hΦle
    hΦlim hΨ hΨL hΨtot hz₀ hz₀A hZ hZl hZlc hZlA hZlnull t ht
  obtain ⟨Clow, hClow⟩ := hΦlow
  -- eventual finiteness of the initial entropies
  have hlim := lt_of_le_of_lt hC hH0
  have hfinev := eventually_lt_of_limsup_lt hlim
  -- the entropy inequality for large `n`
  have hev : ∀ᶠ n : ℕ in atTop,
      cep_cylEntropy D.invβ (fun w => Φn n w + Ψ w) (P.map fun ω => cep_reduce (Z n t ω))
        + ((ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t,
            cep_cylFisher D.invβ (fun w => Φn n w + Ψ w)
              (P.map fun ω => cep_reduce (Z n r ω)) : ℝ≥0∞) : EReal)
        ≤ cep_cylEntropy D.invβ (fun w => Φn n w + Ψ w) (P.map fun ω => cep_reduce (z₀ ω)) := by
    filter_upwards [eventually_ge_atTop (⌈(L : ℝ)⌉₊ + 1), hfinev] with n hn hfin
    have hn1 : 1 ≤ n := by omega
    have hnR : (L : ℝ) + 1 ≤ (n : ℝ) := by
      have h1 : (L : ℝ) ≤ (⌈(L : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈(L : ℝ)⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      push_cast at h2
      linarith
    have hn0 : (0 : ℝ) < n := by linarith [L.coe_nonneg]
    obtain ⟨hΦ1, hΦL⟩ := hΦC (n : ℝ) hn0
    have hdΦ : Differentiable ℝ (Φn n) := hΦ1.differentiable one_ne_zero
    have hdΨ : Differentiable ℝ Ψ := hΨ.differentiable one_ne_zero
    have hU : ContDiff ℝ 1 (fun w => Φn n w + Ψ w) := hΦ1.add hΨ
    have hK : LipschitzWith (Real.toNNReal (n : ℝ) + L) (gradient (fun w => Φn n w + Ψ w)) := by
      rw [ch4c_gradient_add hdΦ hdΨ]
      exact hΦL.add hΨL
    have hUper : ∀ z, (fun w => Φn n w + Ψ w) (z + cep_diag N) = (fun w => Φn n w + Ψ w) z := by
      intro z
      simp only [hΦper n z hn0, hΨper z]
    have hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤
        (fun w => Φn n w + Ψ w) z := by
      obtain ⟨c, C', hc, hcC⟩ := HRS.MC.CepE2Props.cep_H4_potential_conf_proof hΨ hΨL hΨper
        (fun n z hn => hClow n z hn) (n : ℝ) hnR
      exact ⟨c, C', hc, hcC⟩
    have hπ : ∀ σ, MeasurableSet[ℱ 0] {ω : Ω | (fun _ : Ω => σ₀) ω = σ} := by
      intro σ
      by_cases h : σ₀ = σ
      · simp [h]
      · simp [h]
    exact HRS.MC.CepH2C11.cep_H2_c11_cylinder_entropy_proof hW' hπ hU hK hUper hconf hβ hz₀
      (hZ n hn1) hfin t ht
  -- assemble
  have hc_ne : gibbsEntropy D (selectedLaw P (fun s ω => fun i => Torus.mk (cep_unrank σ₀ (Zl (s : ℝ) ω) i)) 0) ≠ ⊥ := by
    unfold gibbsEntropy
    exact ch4c_ennreal_sub_ne_bot _ _
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, (c₀ : EReal) = gibbsEntropy D (selectedLaw P
      (fun s ω => fun i => Torus.mk (cep_unrank σ₀ (Zl (s : ℝ) ω) i)) 0) :=
    ⟨_, EReal.coe_toReal hH0.ne hc_ne⟩
  -- the Fisher information term
  have hbf : ENNReal.ofReal D.invβ * (∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N
      (selectedLaw P (fun s ω => fun i => Torus.mk (cep_unrank σ₀ (Zl (s : ℝ) ω) i)) r)) ≤
      Filter.liminf (fun n : ℕ => ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t,
        cep_cylFisher D.invβ (fun w => Φn n w + Ψ w) (P.map fun ω => cep_reduce (Z n r ω))) atTop := by
    rw [ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top]
    exact mul_le_mul_right hB _
  have hbf' : ((ENNReal.ofReal D.invβ * (∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N
      (selectedLaw P (fun s ω => fun i => Torus.mk (cep_unrank σ₀ (Zl (s : ℝ) ω) i)) r)) : ℝ≥0∞) : EReal) ≤
      Filter.liminf (fun n : ℕ => ((ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t,
        cep_cylFisher D.invβ (fun w => Φn n w + Ψ w) (P.map fun ω => cep_reduce (Z n r ω)) : ℝ≥0∞) : EReal))
        atTop := by
    have hm := Monotone.map_liminf_of_continuousAt (F := atTop)
      (f := ((↑) : ℝ≥0∞ → EReal)) EReal.coe_ennreal_strictMono.monotone
      (fun n : ℕ => ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t,
        cep_cylFisher D.invβ (fun w => Φn n w + Ψ w) (P.map fun ω => cep_reduce (Z n r ω)))
      continuous_coe_ennreal_ereal.continuousAt
    exact (EReal.coe_ennreal_le_coe_ennreal_iff.2 hbf).trans_eq hm
  refine le_of_not_gt fun hcon => ?_
  rw [← hc₀] at hcon
  obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  have hq : c₀ < q := by exact_mod_cast hq1
  have hlq : Filter.limsup (fun n : ℕ => cep_cylEntropy D.invβ (fun w => Φn n w + Ψ w)
      (P.map fun ω => cep_reduce (z₀ ω))) Filter.atTop < ((q : ℝ) : EReal) :=
    lt_of_le_of_lt hC (by rw [← hc₀]; exact_mod_cast hq)
  have hmain := ch4c_add_le (r := q) (fun n => EReal.coe_ennreal_nonneg _) hA hbf' (by
    filter_upwards [hev, eventually_lt_of_limsup_lt hlq] with n h1 h2
    exact h1.trans h2.le)
  exact absurd hmain (not_le.2 hq2)

end Main

end HRS.MC.CepH4Core
