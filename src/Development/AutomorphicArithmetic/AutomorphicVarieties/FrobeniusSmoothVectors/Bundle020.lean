module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle066
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem zcases (j : ZMod 2) : j = 0 ∨ j = 1 := by
  revert j; decide

private theorem sg0 (K : Type) [CommRing K] : sg K 0 = 1 := by simp [sg]

private theorem sg1 (K : Type) [CommRing K] : sg K 1 = -1 := by
  show (-1 : K) ^ ((1 : ZMod 2).val) = -1
  rw [show (1 : ZMod 2).val = 1 from rfl]
  simp

private theorem sg_add (K : Type) [CommRing K] (i j : ZMod 2) : sg K (i + j) = sg K i * sg K j := by
  rcases zcases i with rfl | rfl <;> rcases zcases j with rfl | rfl
  · simp [sg0]
  · simp [sg0]
  · simp [sg0]
  · rw [show (1 : ZMod 2) + 1 = 0 from rfl, sg0, sg1]
    ring

private theorem sg_nsmul (K : Type) [CommRing K] (m : ℕ) (i : ZMod 2) : sg K (m • i) = sg K i ^ m := by
  induction m with
  | zero => simp [sg0]
  | succ k ih => rw [succ_nsmul, sg_add, ih, pow_succ]

private theorem sg_weight (K : Type) [CommRing K] {ι : Type} (wt : ι → ZMod 2) (n : ι →₀ ℕ) :
    (n.prod fun s m => sg K (wt s) ^ m) = sg K (Finsupp.weight wt n) := by
  classical
  rw [Finsupp.weight_apply]
  simp only [Finsupp.prod, Finsupp.sum, ← sg_nsmul]
  generalize n.support = t
  refine Finset.induction_on t ?_ ?_
  · simp [sg0]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, sg_add]

private theorem coeff_sg (O : Type) [CommRing O] {ι : Type} (j : ZMod 2) (y : MvPowerSeries ι O) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (sg _ j * y) = sg O j * MvPowerSeries.coeff n y := by
  rcases zcases j with rfl | rfl <;> simp [sg0, sg1]

theorem UpperTheory.V.Fr.ep_ps :
    ∀ (O : Type) [CommRing O], IsUnit (2 : O) → ∀ (ι : Type) [Finite ι] (wt : ι → ZMod 2), ∃ τ : MvPowerSeries ι O →ₐ[O] MvPowerSeries ι O, (∀ y, τ (τ y) = y) ∧ (∀ j, evp τ j = wtPart O wt j) ∧ ∀ j y, (2 : MvPowerSeries ι O) * wcomp O wt j y = y + sg _ j * τ y := by
  classical
  intro O _ h2 ι _ wt
  have hsq : ∀ i : ZMod 2, sg O i * sg O i = 1 := by
    intro i
    rw [← sg_add]
    rcases zcases i with rfl | rfl
    · exact sg0 O
    · rw [show (1 : ZMod 2) + 1 = 0 from rfl]
      exact sg0 O
  have hne : ∀ i j : ZMod 2, i ≠ j → sg O i = - sg O j := by
    intro i j hij
    rcases zcases i with rfl | rfl <;> rcases zcases j with rfl | rfl
    · exact absurd rfl hij
    · simp [sg0, sg1]
    · simp [sg0, sg1]
    · exact absurd rfl hij
  let a : ι → O := fun s => sg O (wt s)
  have hcoef : ∀ y n, MvPowerSeries.coeff n (MvPowerSeries.rescale a y)
      = sg O (Finsupp.weight wt n) * MvPowerSeries.coeff n y := by
    intro y n
    rw [MvPowerSeries.coeff_rescale, sg_weight]
  let τ : MvPowerSeries ι O →ₐ[O] MvPowerSeries ι O :=
    AlgHom.mk (MvPowerSeries.rescale a) (fun r => by
      ext n
      show MvPowerSeries.coeff n (MvPowerSeries.rescale a (algebraMap O _ r)) = _
      rw [hcoef]
      by_cases hn : n = 0
      · subst hn
        simp [sg0]
      · classical
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          MvPowerSeries.coeff_C, if_neg hn, mul_zero])
  have hτ : ∀ y n, MvPowerSeries.coeff n (τ y)
      = sg O (Finsupp.weight wt n) * MvPowerSeries.coeff n y := hcoef
  refine ⟨τ, ?_, ?_, ?_⟩
  · intro y
    ext n
    rw [hτ, hτ, ← mul_assoc, hsq, one_mul]
  · intro j
    ext y
    show τ y = sg _ j * y ↔ ∀ n, Finsupp.weight wt n ≠ j → MvPowerSeries.coeff n y = 0
    constructor
    · intro h n hn
      have := congrArg (MvPowerSeries.coeff n) h
      rw [hτ, coeff_sg, hne _ _ hn] at this
      have h' : 2 * MvPowerSeries.coeff n y = 0 := by
        linear_combination (-sg O j) * this - (2 * MvPowerSeries.coeff n y) * hsq j
      exact (h2.mul_right_eq_zero).mp h'
    · intro h
      ext n
      rw [hτ, coeff_sg]
      by_cases hn : Finsupp.weight wt n = j
      · rw [hn]
      · rw [h n hn, mul_zero, mul_zero]
  · intro j y
    ext n
    rw [two_mul, map_add (f := _), coeff_wcomp, map_add (f := _), coeff_sg, hτ]
    split_ifs with hn
    · rw [hn]
      linear_combination (-MvPowerSeries.coeff n y) * hsq j
    · rw [hne _ _ hn]
      linear_combination MvPowerSeries.coeff n y * hsq j
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem par_equiv {ι : Type} [Fintype ι] (v : ι → ZMod 2) :
    ∃ (a g : ℕ) (e : Fin a ⊕ Fin g ≃ ι), ∀ s, v (e s) = Space.Loc.par a g s := by
  classical
  refine ⟨_, _, (Equiv.sumCongr (Fintype.equivFin {i // v i = 0}).symm
    (Fintype.equivFin {i // ¬ v i = 0}).symm).trans (Equiv.sumCompl fun i => v i = 0), ?_⟩
  have h2 : ∀ j : ZMod 2, ¬ j = 0 → j = 1 := by decide
  rintro (s | s)
  · exact ((Fintype.equivFin {i // v i = 0}).symm s).2
  · exact h2 _ ((Fintype.equivFin {i // ¬ v i = 0}).symm s).2

theorem UpperTheory.V.Fr.ep_basis :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∀ J N : Ideal R, (∀ y ∈ J, σ y ∈ J) → (∀ y ∈ N, σ y ∈ N) → maximalIdeal R * J ≤ N → ∃ (a g : ℕ) (z : Fin a ⊕ Fin g → R), (∀ s, z s ∈ J ∧ z s ∈ evp σ (Space.Loc.par a g s)) ∧ J ≤ Ideal.span (Set.range z) ⊔ N ∧ ∀ c : Fin a ⊕ Fin g → O, ∑ s, c s • z s ∈ N → ∀ s, c s ∈ maximalIdeal O := by
  classical
  intro O _ _ _ _ h2 R _ _ _ σ hσ J N hJ hN hmJ
  haveI : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian J : J.FG)
  obtain ⟨u, hu2, hucomm⟩ : ∃ u : R, u * 2 = 1 ∧ ∀ x, σ (u * x) = u * σ x :=
    ⟨algebraMap O R ↑h2.unit⁻¹, by
      rw [← map_ofNat (algebraMap O R) 2, ← map_mul, h2.val_inv_mul, map_one],
      fun x => by rw [map_mul, AlgHom.commutes]⟩
  have hsg : ∀ p : ZMod 2, sg R p * sg R p = 1 := by
    intro p
    simp only [sg, ← pow_add, ← two_mul, pow_mul]
    simp
  have hsgσ : ∀ p : ZMod 2, σ (sg R p) = sg R p := by
    intro p
    simp [sg]
  have s0 : sg R 0 = 1 := by simp [sg]
  have s1 : sg R 1 = -1 := by
    show (-1 : R) ^ ((1 : ZMod 2).val) = -1
    rw [show (1 : ZMod 2).val = 1 from rfl]
    simp
  let w : T × ZMod 2 → R := fun j => u * (j.1.1 + sg R j.2 * σ j.1.1)
  have hwJ : ∀ j, w j ∈ J := by
    intro j
    have ht : (j.1 : R) ∈ J := hT ▸ Submodule.subset_span j.1.2
    exact J.mul_mem_left _ (J.add_mem ht (J.mul_mem_left _ (hJ _ ht)))
  have hwev : ∀ j, w j ∈ evp σ j.2 := by
    intro j
    show σ (w j) = sg R j.2 * w j
    simp only [w, hucomm, map_add (f := _), map_mul, hσ, hsgσ]
    linear_combination (-(u * σ j.1.1)) * hsg j.2
  have hmemN : ∀ c ∈ maximalIdeal O, ∀ y ∈ J, c • y ∈ N := by
    intro c hc y hy
    rw [Algebra.smul_def]
    exact hmJ (Ideal.mul_mem_mul (map_nonunit (algebraMap O R) c hc) hy)
  let Indep : Finset (T × ZMod 2) → Prop := fun S =>
    ∀ c : T × ZMod 2 → O, ∑ s ∈ S, c s • w s ∈ N → ∀ s ∈ S, c s ∈ maximalIdeal O
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image
    (Finset.univ.powerset.filter Indep) Finset.card
    ⟨∅, Finset.mem_filter.mpr ⟨by simp, fun c _ s hs => absurd hs (Finset.notMem_empty s)⟩⟩
  have hS' : Indep S := (Finset.mem_filter.mp hS).2
  obtain ⟨a, g, e, he⟩ := par_equiv (ι := S) (fun i => i.1.2)
  refine ⟨a, g, fun s => w (e s).1, ?_, ?_, ?_⟩
  · intro s
    refine ⟨hwJ _, ?_⟩
    rw [← he s]
    exact hwev _
  · have hspan : ∀ j, w j ∈ Ideal.span (Set.range fun s => w (e s).1) ⊔ N := by
      intro j
      by_cases hj : j ∈ S
      · exact Ideal.mem_sup_left (Ideal.subset_span ⟨e.symm ⟨j, hj⟩, by simp⟩)
      · have hnot : ¬ Indep (insert j S) := by
          intro hI
          have := hmax (insert j S) (Finset.mem_filter.mpr ⟨by simp, hI⟩)
          rw [Finset.card_insert_of_notMem hj] at this
          omega
        simp only [Indep, not_forall] at hnot
        obtain ⟨c, hc, s, hs, hcs⟩ := hnot
        rw [Finset.sum_insert hj] at hc
        have hcj : c j ∉ maximalIdeal O := by
          intro hcj
          have h1 : c j • w j ∈ N := hmemN _ hcj _ (hwJ j)
          have h2' : ∑ s ∈ S, c s • w s ∈ N := by
            have := N.sub_mem hc h1
            simpa using this
          rcases Finset.mem_insert.mp hs with rfl | hs
          · exact hcs hcj
          · exact hcs (hS' c h2' s hs)
        have hunit : IsUnit (c j) := by
          by_contra h
          exact hcj ((IsLocalRing.mem_maximalIdeal _).mpr h)
        have hsumS : ∑ s ∈ S, c s • w s ∈ Ideal.span (Set.range fun s => w (e s).1) := by
          refine Ideal.sum_mem _ fun s hs => ?_
          rw [Algebra.smul_def]
          exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨e.symm ⟨s, hs⟩, by simp⟩)
        have hcw : c j • w j ∈ Ideal.span (Set.range fun s => w (e s).1) ⊔ N := by
          have : c j • w j = (c j • w j + ∑ s ∈ S, c s • w s) - ∑ s ∈ S, c s • w s := by
            abel
          rw [this]
          exact Submodule.sub_mem _ (Ideal.mem_sup_right hc) (Ideal.mem_sup_left hsumS)
        obtain ⟨d, hd⟩ := hunit.exists_left_inv
        have : w j = d • (c j • w j) := by rw [smul_smul, hd, one_smul]
        rw [this, Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ hcw
    rw [← hT]
    show Submodule.span R (T : Set R) ≤ _
    rw [Submodule.span_le]
    intro t ht
    have : t = w (⟨t, ht⟩, 0) + w (⟨t, ht⟩, 1) := by
      simp only [w, s0, s1]
      linear_combination (-t) * hu2
    rw [this]
    exact Submodule.add_mem _ (hspan _) (hspan _)
  · intro c hc s
    let c' : T × ZMod 2 → O := fun j => if h : j ∈ S then c (e.symm ⟨j, h⟩) else 0
    have hsum : ∑ j ∈ S, c' j • w j = ∑ s, c s • w (e s).1 := by
      rw [← Finset.sum_coe_sort S, ← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp [c']
    have := hS' c' (hsum ▸ hc) (e s).1 (e s).2
    simpa [c'] using this
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem sg_zero (R : Type) [CommRing R] : sg R 0 = 1 := by simp [sg]

private theorem sg_one (R : Type) [CommRing R] : sg R 1 = -1 := by
  show (-1 : R) ^ (1 : ZMod 2).val = -1
  rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]

theorem UpperTheory.V.Fr.ep_ee :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, ∀ (x : Ideal S.A) (L : S.Loc x), S.u.ee ≤ x → ∀ σ, L.IsInv σ → L.ρ.ee = Ideal.span (evp σ 1 : Set L.R) := by
  intro l _ O _ _ _ _ F C₀ hF S x L hx σ hσ
  have hl : l ≠ 2 := hF.l_odd
  have h2O : IsUnit (2 : L.O') := by
    by_contra h
    have hm : (2 : L.O') ∈ maximalIdeal L.O' := (mem_maximalIdeal _).mpr h
    have hr : residue L.O' 2 = 0 := (residue_eq_zero_iff _).mpr hm
    rw [map_ofNat] at hr
    have hd : l ∣ 2 := (CharP.cast_eq_zero_iff (ResidueField L.O') l 2).mp (by exact_mod_cast hr)
    have hp : l.Prime := Fact.out
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
    · exact hp.one_lt.ne' h1
    · exact hl h1
  have h2 : IsUnit (2 : L.R) := by
    have := h2O.map (algebraMap L.O' L.R)
    rw [map_ofNat] at this
    exact this
  have hpw : ∀ a b : Fin 3, Odd (w 3 a - w 3 b) → pw a b = 1 := by
    intro a b h
    obtain ⟨k, hk⟩ := h
    show ((w 3 a - w 3 b : ℤ) : ZMod 2) = 1
    rw [hk, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_ofNat,
      show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
  have hpw0 : ∀ a b : Fin 3, Even (w 3 a - w 3 b) → pw a b = 0 := by
    intro a b h
    obtain ⟨k, hk⟩ := h
    show ((w 3 a - w 3 b : ℤ) : ZMod 2) = 0
    rw [hk, ← two_mul, Int.cast_mul, Int.cast_ofNat, show (2 : ZMod 2) = 0 from rfl, zero_mul]
  apply le_antisymm
  · unfold NRep.ee
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨g, i, j, hodd, rfl⟩
    apply Ideal.subset_span
    have he := hσ.ent g i j
    rw [hpw i j hodd] at he
    exact he
  · refine Ideal.span_le.mpr ?_
    intro y hy
    have hy' : σ y = sg L.R 1 * y := hy
    rw [sg_one] at hy'
    have hIm : L.ρ.ee ≤ maximalIdeal L.R := by
      unfold NRep.ee
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨g, i, j, hodd, rfl⟩
      have hmem : S.u.r g i j ∈ S.u.ee := Ideal.subset_span ⟨g, i, j, hodd, rfl⟩
      have hxm := hx hmem
      rw [← L.lies] at hxm
      exact Ideal.mem_comap.mp hxm
    haveI : Nontrivial (L.R ⧸ L.ρ.ee) :=
      Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal L.R).ne_top hIm)
    haveI : IsCO L.O' (L.R ⧸ L.ρ.ee) :=
      co_quot L.O' L.R _ (Ideal.Quotient.mkₐ L.O' L.ρ.ee) (Ideal.Quotient.mkₐ_surjective _ _)
    have key' : ∀ z (hz : z ∈ Algebra.adjoin O ((S.B : Set S.R) ∪ {x | ∃ g i j, x = S.ρ.r g i j})),
        Ideal.Quotient.mk L.ρ.ee (σ (L.ι ⟨z, hz⟩)) = Ideal.Quotient.mk L.ρ.ee (L.ι ⟨z, hz⟩) := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem z hz =>
        rcases hz with hB | ⟨g, i, j, rfl⟩
        · have hb' : σ (L.b ⟨z, hB⟩) = sg L.R 0 * L.b ⟨z, hB⟩ := hσ.base ⟨z, hB⟩
          rw [sg_zero, one_mul] at hb'
          show Ideal.Quotient.mk _ (σ (L.b ⟨z, hB⟩)) = Ideal.Quotient.mk _ (L.b ⟨z, hB⟩)
          rw [hb']
        · have he' : σ (L.ρ.r g i j) = sg L.R (pw i j) * L.ρ.r g i j := hσ.ent g i j
          show Ideal.Quotient.mk _ (σ (L.ρ.r g i j)) = Ideal.Quotient.mk _ (L.ρ.r g i j)
          rcases Int.even_or_odd (w 3 i - w 3 j) with h | h
          · rw [hpw0 i j h, sg_zero, one_mul] at he'
            rw [he']
          · rw [hpw i j h, sg_one] at he'
            have hm : L.ρ.r g i j ∈ L.ρ.ee := Ideal.subset_span ⟨g, i, j, h, rfl⟩
            rw [he', Ideal.Quotient.eq]
            have hc : -1 * L.ρ.r g i j - L.ρ.r g i j = (-2) * L.ρ.r g i j := by ring
            rw [hc]
            exact Ideal.mul_mem_left _ _ hm
      | algebraMap r =>
        show Ideal.Quotient.mk _ (σ (L.ι (algebraMap O S.A r))) = Ideal.Quotient.mk _ (L.ι (algebraMap O S.A r))
        rw [L.ι.commutes]
        have hc := (σ.restrictScalars O).commutes r
        rw [AlgHom.restrictScalars_apply] at hc
        rw [hc]
      | add a b ha hb iha ihb =>
        show Ideal.Quotient.mk _ (σ (L.ι (⟨a, ha⟩ + ⟨b, hb⟩))) = Ideal.Quotient.mk _ (L.ι (⟨a, ha⟩ + ⟨b, hb⟩))
        simp only [map_add (f := _), iha, ihb]
      | mul a b ha hb iha ihb =>
        show Ideal.Quotient.mk _ (σ (L.ι (⟨a, ha⟩ * ⟨b, hb⟩))) = Ideal.Quotient.mk _ (L.ι (⟨a, ha⟩ * ⟨b, hb⟩))
        simp only [map_mul, iha, ihb]
    have huniq := L.univ (L.R ⧸ L.ρ.ee) ((Ideal.Quotient.mkₐ O L.ρ.ee).comp L.ι) (fun a => by
      show res L.O' _ (Ideal.Quotient.mkₐ L.O' L.ρ.ee (L.ι a)) = _
      exact res_map _ _)
    have h1 : ∀ a : S.A, ((Ideal.Quotient.mkₐ L.O' L.ρ.ee).comp σ) (L.ι a) =
        ((Ideal.Quotient.mkₐ O L.ρ.ee).comp L.ι) a := by
      rintro ⟨z, hz⟩
      exact key' z hz
    have h2' : ∀ a : S.A, (Ideal.Quotient.mkₐ L.O' L.ρ.ee) (L.ι a) =
        ((Ideal.Quotient.mkₐ O L.ρ.ee).comp L.ι) a := fun a => rfl
    have heq := huniq.unique h1 h2'
    have hyq := AlgHom.congr_fun heq y
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hy'] at hyq
    have hd := Ideal.Quotient.eq.mp hyq
    have h2y : 2 * y ∈ L.ρ.ee := by
      have hc : 2 * y = -((-1 * y) - y) := by ring
      rw [hc]
      exact neg_mem hd
    obtain ⟨u, hu⟩ := h2
    have hc : y = (↑u⁻¹ : L.R) * (2 * y) := by rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    show y ∈ L.ρ.ee
    rw [hc]
    exact Ideal.mul_mem_left _ _ h2y
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section
open MvPowerSeries
private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X f hf
end

private theorem der_zero {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    {σ : R →ₐ[O] R} (P : GPres O σ) (D : R →ₗ[O] ResidueField O) (hD : D ∈ PtDer (res O R) (ResidueField O))
    (h : ∀ s, D (P.p (MvPowerSeries.X s)) = 0) : D = 0 := by
  have hm : ∀ f g, D (f * g) = res O R f • D g + res O R g • D f := hD
  have h1 : D 1 = 0 := by
    have := hm 1 1
    simp only [mul_one, map_one, one_smul] at this
    exact left_eq_add.1 this
  have hs : ∀ g ∈ Ideal.span (Set.range (MvPowerSeries.X : _ → MvPowerSeries (Fin P.a ⊕ Fin P.g) O)),
      res O R (P.p g) = 0 ∧ D (P.p g) = 0 := fun g hg => by
    refine Submodule.span_induction (p := fun g _ => res O R (P.p g) = 0 ∧ D (P.p g) = 0) ?_ (by simp) ?_ ?_ hg
    · rintro _ ⟨s, rfl⟩
      exact ⟨(res_eq_zero_iff O R _).2 (P.var s), h s⟩
    · rintro x y - - ⟨a, b⟩ ⟨c, d⟩
      simp [a, b, c, d]
    · rintro x y - ⟨a, b⟩
      rw [smul_eq_mul, map_mul, map_mul, hm, a, b]
      simp
  ext x
  obtain ⟨f, rfl⟩ := P.surj x
  have e : f = (f - algebraMap O _ (MvPowerSeries.constantCoeff f)) + (MvPowerSeries.constantCoeff f) • 1 := by
    rw [Algebra.algebraMap_eq_smul_one, sub_add_cancel]
  have h2 := (hs _ (mem_span_X (f - algebraMap O _ (MvPowerSeries.constantCoeff f))
    (by simp [MvPowerSeries.algebraMap_apply]))).2
  rw [e, map_add (f := _), map_add (f := _), h2, map_smul, map_smul, map_one, h1]
  simp

private theorem der_off {O : Type} [CommRing O] [IsLocalRing O] (h2 : IsUnit (2 : O)) {R : Type} [CommRing R]
    [Algebra O R] [IsCO O R] {σ : R →ₐ[O] R} (P : GPres O σ) (j : ZMod 2) (D : R →ₗ[O] ResidueField O)
    (hD : D ∈ derp O σ j) (s : Fin P.a ⊕ Fin P.g) (hs : Space.Loc.par P.a P.g s ≠ j) :
    D (P.p (MvPowerSeries.X s)) = 0 := by
  have h1 : P.p (MvPowerSeries.X s) ∈ evp σ (Space.Loc.par P.a P.g s) := by
    rw [← P.part]
    exact ⟨_, X_mem_wtPart O _ s, rfl⟩
  have h3 : σ (P.p (MvPowerSeries.X s)) = sg R (Space.Loc.par P.a P.g s) * P.p (MvPowerSeries.X s) := h1
  have h4 : D (σ (P.p (MvPowerSeries.X s))) = sg (ResidueField O) j * D (P.p (MvPowerSeries.X s)) := hD.2 _
  have h5 : (2 : ResidueField O) ≠ 0 := by
    have := (h2.map (residue O)).ne_zero
    rwa [map_ofNat] at this
  rw [h3] at h4
  generalize Space.Loc.par P.a P.g s = i at hs h4
  generalize P.p (MvPowerSeries.X s) = y at h4
  have v1 : (1 : ZMod 2).val = 1 := rfl
  have hc : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
  apply (mul_eq_zero.1 (show 2 * D y = 0 from ?_)).resolve_left h5
  rcases hc i with rfl | rfl <;> rcases hc j with rfl | rfl
  · exact absurd rfl hs
  · simp only [sg, ZMod.val_zero, v1, pow_zero, pow_one, one_mul, neg_mul] at h4
    linear_combination h4
  · simp only [sg, ZMod.val_zero, v1, pow_zero, pow_one, one_mul, neg_mul, map_neg] at h4
    linear_combination -h4
  · exact absurd rfl hs

private theorem der_bound {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R]
    [Algebra O R] (N : Submodule (ResidueField O) (R →ₗ[O] ResidueField O)) {ι : Type} [Fintype ι] (y : ι → R)
    (h : ∀ D ∈ N, (∀ i, D (y i) = 0) → D = 0) :
    Module.Finite (ResidueField O) N ∧ Module.finrank (ResidueField O) N ≤ Fintype.card ι := by
  let φ : N →ₗ[ResidueField O] (ι → ResidueField O) :=
    { toFun := fun D i => D.1 (y i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := (injective_iff_map_eq_zero φ).2 fun D hD =>
    Subtype.ext (h D.1 D.2 fun i => congrFun hD i)
  exact ⟨Module.Finite.of_injective φ hφ, by
    simpa using LinearMap.finrank_le_finrank_of_injective hφ⟩

theorem UpperTheory.V.Fr.ep_der :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R) (P : GPres O σ), (∀ j, Module.Finite (ResidueField O) (derp O σ j)) ∧ Module.finrank (ResidueField O) (derp O σ 0) ≤ P.a ∧ Module.finrank (ResidueField O) (derp O σ 1) ≤ P.g := by
  intro O _ _ _ _ h2 R _ _ _ σ P
  refine ⟨fun j => (der_bound (derp O σ j) (fun s => P.p (MvPowerSeries.X s))
    fun D hD h => der_zero P D hD.1 h).1, ?_, ?_⟩
  · have := (der_bound (derp O σ 0) (fun i : Fin P.a => P.p (MvPowerSeries.X (.inl i)))
      fun D hD h => der_zero P D hD.1 fun s => by
        rcases s with i | i
        · exact h i
        · exact der_off h2 P 0 D hD _ (show (1 : ZMod 2) ≠ 0 by decide)).2
    simpa using this
  · have := (der_bound (derp O σ 1) (fun i : Fin P.g => P.p (MvPowerSeries.X (.inr i)))
      fun D hD h => der_zero P D hD.1 fun s => by
        rcases s with i | i
        · exact der_off h2 P 1 D hD _ (show (0 : ZMod 2) ≠ 1 by decide)
        · exact h i).2
    simpa using this
end
