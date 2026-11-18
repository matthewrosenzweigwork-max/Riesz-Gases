import HRS.MC.CepN6Aux5

/-!
# Packet CEPN6 (aux 6): the pathwise exit lemma

For a path `y` in the closed good set up to time `x`, for which the gap equation of N4 holds on every
subinterval where its hypotheses hold, `y` is in the open good set at time `x` (no exit before `t₁ + dur`).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace HRS.MC.CepN6

open HRS HRS.MC.CepN4

variable {N : ℕ}

theorem n6_closure_path {p0 p1 : Fin N} {r2 gcap : ℝ} {y : ℝ → Fin N → Euc 1} {t₁ x : ℝ}
    (hlt : t₁ < x) (hcont : ContinuousOn y (Set.Icc t₁ x))
    (hU : ∀ v ∈ Set.Ico t₁ x, y v ∈ n6_Uo p0 p1 r2 gcap) :
    ∀ v ∈ Set.Icc t₁ x, y v ∈ n6_Kc p0 p1 r2 gcap := by
  intro v hv
  rcases eq_or_lt_of_le hv.2 with rfl | hvx
  · have h1 : v ∈ closure (Set.Ico t₁ v) := by
      rw [closure_Ico hlt.ne]; exact ⟨hlt.le, le_rfl⟩
    have h2 : ContinuousWithinAt y (Set.Ico t₁ v) v :=
      (hcont v ⟨hlt.le, le_rfl⟩).mono Set.Ico_subset_Icc_self
    have h3 := h2.mem_closure_image h1
    have h4 : closure (y '' Set.Ico t₁ v) ⊆ closure (n6_Uo p0 p1 r2 gcap) :=
      closure_mono (by rintro _ ⟨w, hw, rfl⟩; exact hU w hw)
    exact n6_closure_Uo_subset p0 p1 r2 gcap (h4 h3)
  · exact n6_Uo_subset_Kc _ _ _ _ (hU v ⟨hv.1, hvx⟩)

theorem n6_rise_of_eq {G c : ℝ → ℝ} {κ C L s t : ℝ} (hst : s ≤ t) (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (hL : 0 < L) (hc : ∀ u, |c u| ≤ C) (hGL : ∀ u ∈ Set.Ioc s t, L ≤ G u) :
    (∫ u in s..t, (κ / G u + c u)) ≤ (κ / L + C) * (t - s) := by
  by_cases hint : IntervalIntegrable (fun u => κ / G u + c u) volume s t
  · rw [intervalIntegral.integral_of_le hst]
    have hint' : IntegrableOn (fun u => κ / G u + c u) (Set.Ioc s t) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).1 hint
    calc ∫ u in Set.Ioc s t, (κ / G u + c u) ≤ ∫ u in Set.Ioc s t, (κ / L + C) := by
          refine setIntegral_mono_on hint' (integrableOn_const (by simp)) measurableSet_Ioc ?_
          intro u hu
          have h1 : κ / G u ≤ κ / L :=
            div_le_div_of_nonneg_left hκ hL (hGL u hu)
          have h2 : c u ≤ C := (abs_le.1 (hc u)).2
          linarith
      _ = (κ / L + C) * (t - s) := by
          rw [setIntegral_const, Real.volume_real_Ioc_of_le hst]
          simp [smul_eq_mul, mul_comm]
  · rw [intervalIntegral.integral_undef hint]
    have : 0 ≤ t - s := sub_nonneg.2 hst
    positivity

theorem n6_noise_eq {b X : ℝ} (hb : 0 ≤ b) :
    2 * Real.sqrt b * (X / Real.sqrt 2) = Real.sqrt (2 * b) * X := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsq : Real.sqrt (2 * b) = Real.sqrt 2 * Real.sqrt b := Real.sqrt_mul (by norm_num) _
  have hs2ne : Real.sqrt 2 ≠ 0 := by positivity
  rw [hsq]
  calc 2 * Real.sqrt b * (X / Real.sqrt 2)
      = (Real.sqrt 2 * Real.sqrt 2) * Real.sqrt b * (X / Real.sqrt 2) := by rw [hs2]
    _ = Real.sqrt 2 * Real.sqrt b * X := by field_simp

theorem n6_exit {D : DynData 1} (hN : 2 ≤ N) (σ : Equiv.Perm (Fin N))
    {a Bd C r r2 η L ε T t₁ dur : ℝ}
    (ha : 0 < a) (hβ : 0 < D.invβ) (hη : 0 ≤ η) (hBd0 : 0 ≤ Bd) (hC : 0 ≤ C)
    (ht₁ : 0 ≤ t₁) (hdur : 0 < dur) (hT : t₁ + dur ≤ T)
    (hBd1 : ∀ z ∈ liftedFree 1 N, ∀ k : Fin N, (∀ j, j ≠ k → r2 ≤ n6_dc (z k 0 - z j 0)) →
      |(liftedDrift D z k) 0| ≤ Bd)
    (hBd2 : ∀ z ∈ liftedFree 1 N,
      (∀ j, j ≠ σ (cep_i0 hN) → j ≠ σ (cep_i1 hN) →
        r2 ≤ n6_dc (z (σ (cep_i0 hN)) 0 - z j 0) ∧ r2 ≤ n6_dc (z (σ (cep_i1 hN)) 0 - z j 0)) →
      |(liftedDrift D z (σ (cep_i0 hN))) 0 + (liftedDrift D z (σ (cep_i1 hN))) 0| ≤ Bd)
    {y : ℝ → Fin N → Euc 1} {c : ℝ → ℝ} {w : ℝ → Fin N → ℝ}
    (hc : ∀ u, |c u| ≤ C)
    (hfree : ∀ v ∈ Set.Icc (0 : ℝ) T, y v ∈ liftedFree 1 N)
    (hcont : ContinuousOn y (Set.Icc 0 T))
    (hord : ∀ v ∈ Set.Icc (0 : ℝ) T, cep_StrictlyOrdered σ (y v))
    (hcoord : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → ∀ k : Fin N,
      IntervalIntegrable (fun u => (liftedDrift D (y u) k) 0) volume s t ∧
      y t k 0 - y s k 0 = (∫ u in s..t, (liftedDrift D (y u) k) 0) +
        Real.sqrt (2 * D.invβ) * (w t k - w s k))
    (hN4 : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
      (∀ u ∈ Set.Icc s t, cep_StrictlyOrdered σ (y u) ∧ cep_PairIsolated hN σ (y u) r2 ∧
        0 < y u (σ (cep_i1 hN)) 0 - y u (σ (cep_i0 hN)) 0 ∧
        y u (σ (cep_i1 hN)) 0 - y u (σ (cep_i0 hN)) 0 < 1 / 4) →
      (y t (σ (cep_i1 hN)) 0 - y t (σ (cep_i0 hN)) 0) - (y s (σ (cep_i1 hN)) 0 - y s (σ (cep_i0 hN)) 0) =
        (∫ u in s..t, ((2 * a / N) / (y u (σ (cep_i1 hN)) 0 - y u (σ (cep_i0 hN)) 0) + c u)) +
          2 * Real.sqrt D.invβ *
            (((w t (σ (cep_i1 hN)) - w t (σ (cep_i0 hN))) - (w s (σ (cep_i1 hN)) - w s (σ (cep_i0 hN)))) /
              Real.sqrt 2))
    (hw : ∀ k, ∀ v ∈ Set.Icc t₁ (t₁ + dur), |w v k - w t₁ k| ≤ η)
    (hinit : ∀ k l, n6_rel (σ (cep_i0 hN)) (σ (cep_i1 hN)) k l → r ≤ n6_dc (y t₁ k 0 - y t₁ l 0))
    (hG0 : y t₁ (σ (cep_i1 hN)) 0 - y t₁ (σ (cep_i0 hN)) 0 ≤ ε / 2)
    (hεL : ε / 2 ≤ L) (h2L : 2 * L ≤ 1 / 8)
    (hM : r2 + 2 * (Bd * dur + 2 * Real.sqrt (2 * D.invβ) * η + L) < r)
    (hcond : ((2 * a / N) / L + C) * dur + 4 * Real.sqrt (2 * D.invβ) * η < L) :
    ∀ x : ℝ, t₁ ≤ x → x ≤ t₁ + dur →
      (∀ v ∈ Set.Ico t₁ x, y v ∈ n6_Uo (σ (cep_i0 hN)) (σ (cep_i1 hN)) r2 (1 / 8)) →
      y x ∈ n6_Uo (σ (cep_i0 hN)) (σ (cep_i1 hN)) r2 (1 / 8) := by
  intro x hx1 hx2 hU
  set p0 := σ (cep_i0 hN) with hp0
  set p1 := σ (cep_i1 hN) with hp1
  have hpne : p0 ≠ p1 := σ.injective.ne (cepn4_i0_ne_i1 hN)
  set ν := Real.sqrt (2 * D.invβ) with hνdef
  have hν : 0 ≤ ν := Real.sqrt_nonneg _
  have hlt01 : cep_i0 hN < cep_i1 hN := by
    show (⟨0, _⟩ : Fin N) < ⟨1, _⟩
    exact Fin.mk_lt_mk.2 one_pos
  have hgap : ∀ v ∈ Set.Icc (0 : ℝ) T, 0 < y v p1 0 - y v p0 0 := fun v hv => by
    have := (hord v hv).1 _ _ hlt01
    linarith
  have ht₁T : t₁ ∈ Set.Icc (0 : ℝ) T := ⟨ht₁, by linarith⟩
  have hL0 : 0 < L := lt_of_lt_of_le (hgap t₁ ht₁T) (hG0.trans hεL)
  have hNr : (0 : ℝ) ≤ 2 * a / N := by positivity
  have hxT : x ≤ T := hx2.trans hT
  have hKnn : 0 ≤ (2 * a / N) / L + C := by positivity
  have hbr : 0 ≤ Bd * dur + 2 * ν * η + L := by positivity
  by_cases hxt : x = t₁
  · -- the initial point is in the good set
    rw [hxt]
    have hr2r : r2 < r := by linarith
    refine ⟨by linarith, fun k l hkl => ?_⟩
    have := hinit k l hkl
    linarith
  · have hlt : t₁ < x := lt_of_le_of_ne hx1 (Ne.symm hxt)
    have hcx : ContinuousOn y (Set.Icc t₁ x) :=
      hcont.mono (Set.Icc_subset_Icc ht₁ hxT)
    have hKc := n6_closure_path hlt hcx hU
    have hrise : ∀ s t, t₁ ≤ s → s ≤ t → t ≤ x → (∀ v ∈ Set.Ioc s t, L ≤ y v p1 0 - y v p0 0) →
        (y t p1 0 - y t p0 0) - (y s p1 0 - y s p0 0) ≤
          ((2 * a / N) / L + C) * (t - s) + 4 * ν * η := by
      intro s t hs hst htx hGL
      have hs0 : 0 ≤ s := ht₁.trans hs
      have htT : t ≤ T := htx.trans hxT
      have hcondN4 : ∀ u ∈ Set.Icc s t, cep_StrictlyOrdered σ (y u) ∧
          cep_PairIsolated hN σ (y u) r2 ∧ 0 < y u p1 0 - y u p0 0 ∧
          y u p1 0 - y u p0 0 < 1 / 4 := by
        intro u hu
        have huK := hKc u ⟨hs.trans hu.1, hu.2.trans htx⟩
        have huT : u ∈ Set.Icc (0 : ℝ) T := ⟨hs0.trans hu.1, hu.2.trans htT⟩
        refine ⟨hord u huT, ?_, hgap u huT, ?_⟩
        · intro k hk0 hk1 m
          have r0 : n6_rel p0 p1 k p0 := ⟨hk0, fun h => by
            rcases h with ⟨h | h, _⟩
            · exact hk0 h
            · exact hk1 h⟩
          have r1 : n6_rel p0 p1 k p1 := ⟨hk1, fun h => by
            rcases h with ⟨h | h, _⟩
            · exact hk0 h
            · exact hk1 h⟩
          exact ⟨le_trans (huK.2 k p0 r0) (n6_dc_le _ m), le_trans (huK.2 k p1 r1) (n6_dc_le _ m)⟩
        · have := huK.1
          linarith
      have hid := hN4 s t hs0 hst htT hcondN4
      rw [hid]
      have h1 := n6_rise_of_eq (G := fun u => y u p1 0 - y u p0 0) (c := c) (κ := 2 * a / N)
        (C := C) (L := L) (s := s) (t := t) hst hNr hC hL0 hc hGL
      have h2 : 2 * Real.sqrt D.invβ *
          (((w t p1 - w t p0) - (w s p1 - w s p0)) / Real.sqrt 2) ≤ 4 * ν * η := by
        rw [n6_noise_eq hβ.le]
        have e1 := hw p1 t ⟨hs.trans' le_rfl |>.trans hst, htx.trans hx2⟩
        have e2 := hw p0 t ⟨hs.trans hst, htx.trans hx2⟩
        have e3 := hw p1 s ⟨hs, (hst.trans htx).trans hx2⟩
        have e4 := hw p0 s ⟨hs, (hst.trans htx).trans hx2⟩
        obtain ⟨a1, a2⟩ := abs_le.1 e1
        obtain ⟨b1, b2⟩ := abs_le.1 e2
        obtain ⟨c1, c2⟩ := abs_le.1 e3
        obtain ⟨d1, d2⟩ := abs_le.1 e4
        rw [← hνdef]
        nlinarith [mul_nonneg hν hη]
      linarith
    refine n6_boot (D := D) (p0 := p0) (p1 := p1) hpne (y := y) (w := w) (t₁ := t₁) (u := x) hx1
      hν hη hBd0 hBd1 hBd2 (fun v hv => hfree v ⟨ht₁.trans hv.1, hv.2.trans hxT⟩) hKc
      (fun k => (hcoord t₁ x ht₁ hx1 hxT k).1)
      (fun k v hv => (hcoord t₁ v ht₁ hv.1 (hv.2.trans hxT) k).2)
      (fun k v hv => hw k v ⟨hv.1, hv.2.trans hx2⟩) hcx hinit (hG0.trans hεL)
      (fun v hv => hgap v ⟨ht₁.trans hv.1, hv.2.trans hxT⟩) hKnn hrise ?_ ?_ h2L
    · have : ((2 * a / N) / L + C) * (x - t₁) ≤ ((2 * a / N) / L + C) * dur :=
        mul_le_mul_of_nonneg_left (by linarith) hKnn
      linarith
    · have : Bd * (x - t₁) ≤ Bd * dur := mul_le_mul_of_nonneg_left (by linarith) hBd0
      linarith

end HRS.MC.CepN6
