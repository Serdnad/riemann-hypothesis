module

public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle004
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushTestB
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace SheetDecomposition

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal intNum mixedDiff diffStep)

theorem intNum_perm {K : Type} [DecidableEq K] {ι : K → Type} {F : Type} [Field F] (I : Ideal (MvPolynomial (Σ k, ι k) F))
    {n m : ℕ} (a : Fin n → K → ℤ) (b : Fin m → K → ℤ) (h : (List.ofFn a).Perm (List.ofFn b)) : intNum F I a = intNum F I b := by
  have : LeftCommutative (diffStep (K := K)) := ⟨fun x y g => by
    funext z
    simp only [diffStep, sub_right_comm z x y]
    ring⟩
  unfold intNum mixedDiff
  rw [h.foldr_eq]

theorem monoLines_perm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} (l : J → HermLine ι) {d : ℕ}
    (w : Fin d → J) :
    (List.ofFn fun k => (monoLines l (∑ j, Finsupp.single (w j) 1) d k).a).Perm (List.ofFn fun j => (l (w j)).a) := by
  have h1 : Finsupp.toMultiset (∑ j, Finsupp.single (w j) 1 : J →₀ ℕ) = (List.ofFn w : Multiset J) := by

    rw [map_sum, ← Fin.univ_val_map, Finset.sum_eq_multiset_sum]
    simp only [Finsupp.toMultiset_single, one_smul]
    conv_rhs => rw [← Multiset.sum_map_singleton (Multiset.map w Finset.univ.val), Multiset.map_map]
    rfl
  have h2 : (Finsupp.toMultiset (∑ j, Finsupp.single (w j) 1 : J →₀ ℕ)).toList.Perm (List.ofFn w) := by
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, h1]
  have h4 : (List.ofFn fun k => (monoLines l (∑ j, Finsupp.single (w j) 1) d k).a) =
      ((Finsupp.toMultiset (∑ j, Finsupp.single (w j) 1 : J →₀ ℕ)).toList).map fun x => (l x).a := by
    refine List.ext_getElem (by simp) fun i h h' => ?_
    have hi : i < (Finsupp.toMultiset (∑ j, Finsupp.single (w j) 1 : J →₀ ℕ)).toList.length := by simpa using h'
    simp only [List.getElem_ofFn, List.getElem_map, monoLines, dif_pos hi, List.get_eq_getElem]
  rw [h4]
  have h5 := h2.map fun x => (l x).a
  rwa [List.map_ofFn] at h5

theorem monoLines_smooth {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} (l : J → HermLine ι)
    (hl : ∀ j, IsSmoothHerm (l j)) (m : J →₀ ℕ) (d : ℕ) (k : Fin d) : IsSmoothHerm (monoLines l m d k) := by
  unfold monoLines
  split_ifs
  · exact hl _
  · exact contDiffOn_const

variable {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N)

open Classical in
theorem geoFun_word (hI : PB.Inputs) (w : Fin (dimFl Ψ N) → Ψ × Fin N) :
    M.geoFun (toA (∏ j, X (w j))) * M.δ =
      (intNum ℚ (M.P.map (MvPolynomial.map (Int.castRingHom ℚ))) fun j => M.xdeg (w j) : ℤ) := by
  have h1 : toA (∏ j, X (w j) : RP Ψ N) = basisMonomials (Option (Ψ × Fin N)) ℝ (∑ j, Finsupp.single (some (w j)) 1) := by
    simp only [toA, map_prod, rename_X, coe_basisMonomials]
    rw [monomial_sum_one]
    rfl
  have h2 : (∑ j, Finsupp.single (some (w j)) 1 : Option (Ψ × Fin N) →₀ ℕ).degree = dimFl Ψ N := by

    simp [map_sum]
  have h3 : (∑ j, Finsupp.single (some (w j)) 1 : Option (Ψ × Fin N) →₀ ℕ) none = 0 := by
    simp [Finsupp.finsetSum_apply]
  have hs : ∀ j, IsSmoothHerm (M.line 1 j) := fun j => by
    cases j
    · exact M.A_smooth
    · exact M.x_smooth _ _
  have h4 := GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree hI.degree M.K M.ι M.P (dimFl Ψ N)
    (monoLines (M.line 1) (∑ j, Finsupp.single (some (w j)) 1) (dimFl Ψ N)) M.arith (monoLines_smooth _ hs _ _)
  have hδ : (M.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 M.δ_pos.ne'
  rw [h1, RootModel.geoFun, Module.Basis.constr_basis, RootModel.geoMono, if_pos h2, h3, pow_zero, mul_one, div_mul_cancel₀ _ hδ]
  refine h4.trans (congrArg _ ?_)
  refine (intNum_perm _ _ _ (monoLines_perm (M.line 1) fun j => some (w j))).trans ?_
  simp only [RootModel.line, M.x_deg]

open Classical in
theorem geoFun_prod (hI : PB.Inputs) (c : Fin (dimFl Ψ N) → Ψ × Fin N → ℤ) :
    M.geoFun (toA (∏ j, ∑ x, c j x • X x)) * M.δ =
      (intNum ℚ (M.P.map (MvPolynomial.map (Int.castRingHom ℚ))) fun j => ∑ x, c j x • M.xdeg x : ℤ) := by
  obtain ⟨F, hF⟩ := exists_multilinear_gen (P := M.P) M.arith

  rw [← hF, F.map_sum, Fintype.prod_sum]
  have h1 : ∀ w : Fin (dimFl Ψ N) → Ψ × Fin N, toA (∏ j, c j (w j) • X (w j) : RP Ψ N) =
      ((∏ j, c j (w j) : ℤ) : ℝ) • toA (∏ j, X (w j)) := fun w => by
    rw [Finset.prod_smul, Int.cast_smul_eq_zsmul, toA, toA, map_zsmul]
  have h2 : toA (∑ w : Fin (dimFl Ψ N) → Ψ × Fin N, ∏ j, c j (w j) • X (w j) : RP Ψ N) =
      ∑ w : Fin (dimFl Ψ N) → Ψ × Fin N, toA (∏ j, c j (w j) • X (w j)) := map_sum (rename some) _ _

  rw [h2, map_sum, Finset.sum_mul, Int.cast_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [h1, map_smul, F.map_smul_univ, smul_eq_mul, smul_eq_mul, mul_assoc, geoFun_word M hI, hF, Int.cast_mul]
  rfl

theorem test_pointIdeal_rat {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [h : Algebra ℚ Ω]
    (y : (Σ k, ι k) → Ω) : pointIdeal ℚ y = (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) := by
  have : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : h = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalNef.genIdeal_eq y).symm

theorem geoTest : GeoTest := by
  intro hI Ψ _ _ p q M _ n r e hq hn
  have hc : n + r = dimFl Ψ (p + q) := by
    rw [hn, ← count_pairs, ← Fintype.card_congr e, Fintype.card_fin]
  refine ⟨hc, ?_⟩
  have key : ∀ (d : ℕ) (_ : d = dimFl Ψ (p + q)) (c : Fin d → Ψ × Fin (p + q) → ℤ),
      M.geoFun (toA (∏ j, ∑ x, c j x • X x)) * M.δ = inum ℚ M.y fun j => ∑ x, c j x • M.xdeg x := by
    rintro _ rfl c
    rw [inum, test_pointIdeal_rat]
    convert geoFun_prod M hI c
    rfl
  rw [test_factor e hq hn, key _ hc]
  congr 2
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [Fin.append_left, sum_muCoef, muDeg]
  · simp only [Fin.append_right, sum_fibCoef, fibDeg]

end SheetDecomposition
end
end

section

noncomputable section

namespace SheetDecomposition

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ b, Fintype (ι' b)]

theorem inum_eq_zero_of_valEq_zero (h3 : UnitZero) {z : (Σ b, ι b) → Ω} {d : ℕ} (hz : IsPt k z d) (ht : fnField k z = ⊤)
    (a : Fin d → K → ℤ) (i : Fin d) (h : ValEq k z (a i) z 0) : inum k z a = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have := i.pos; omega⟩
  have key : inum k z a = inum k z (a ∘ Equiv.swap i (Fin.last n)) := by
    unfold inum NumbersDVR.intNum
    rw [FieldNumbers.mixedDiff_comp_perm]
  rw [key, ← Fin.snoc_init_self (a ∘ Equiv.swap i (Fin.last n))]
  apply h3 k Ω K ι z n _ _ hz ht
  show ValEq k z (a (Equiv.swap i (Fin.last n) (Fin.last n))) z 0
  rw [Equiv.swap_apply_right]
  exact h

theorem inum_update (h1 : PtDim) (h3 : UnitZero) {z : (Σ b, ι b) → Ω} {d : ℕ} (hz : IsPt k z d) (ht : fnField k z = ⊤)
    (a : Fin d → K → ℤ) (i : Fin d) (b : K → ℤ) (h : ValEq k z b z (a i)) : inum k z (Function.update a i b) = inum k z a := by
  classical
  obtain ⟨hprime, hdim, -⟩ := h1 k Ω K ι z d hz
  have hadd := FieldNumbers.IntNumAdd.full k K ι (NumbersDVR.pointIdeal k z) hprime.multiHomog hprime.relevant d hdim
    a i (b - a i) (a i)
  rw [sub_add_cancel, Function.update_eq_self] at hadd
  have hz0 : inum k z (Function.update a i (b - a i)) = 0 := by
    apply inum_eq_zero_of_valEq_zero h3 hz ht _ i
    rw [Function.update_self]
    obtain ⟨ρ, hρ, hO⟩ := h
    refine ⟨ρ, hρ, fun O hk => ?_⟩
    have e := hO O hk
    have hne : ∀ c : K, (Finset.univ.sup fun j : ι c => O.valuation (z ⟨c, j⟩)) ≠ 0 := by
      intro c h0
      obtain ⟨j, hj⟩ := hz.1 c
      have hle : O.valuation (z ⟨c, j⟩) ≤ 0 :=
        h0 ▸ Finset.le_sup (f := fun j : ι c => O.valuation (z ⟨c, j⟩)) (Finset.mem_univ j)
      exact hj ((Valuation.zero_iff _).mp (le_antisymm hle zero_le'))
    have hv : vdeg O z (b - a i) * vdeg O z (a i) = vdeg O z b := by
      unfold vdeg
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [Pi.sub_apply, ← zpow_add₀ (hne c), sub_add_cancel]
    have hne' : vdeg O z (a i) ≠ 0 := by
      unfold vdeg
      exact Finset.prod_ne_zero_iff.mpr fun c _ => zpow_ne_zero _ (hne c)
    have h0 : vdeg O z (0 : K → ℤ) = 1 := by
      unfold vdeg
      simp
    rw [h0, mul_one]
    apply mul_right_cancel₀ hne'
    rw [hv, e]
  unfold inum at hz0 ⊢
  convert hadd using 1
  rw [hz0, zero_add]

theorem inum_congr (h1 : PtDim) (h3 : UnitZero) {z : (Σ b, ι b) → Ω} {d : ℕ} (hz : IsPt k z d) (ht : fnField k z = ⊤)
    (a a' : Fin d → K → ℤ) (h : ∀ j, ValEq k z (a j) z (a' j)) : inum k z a = inum k z a' := by
  classical
  have key : ∀ s : Finset (Fin d), inum k z (fun j => if j ∈ s then a' j else a j) = inum k z a := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro i s hi ih
      rw [← ih]
      have e : (fun j => if j ∈ insert i s then a' j else a j) =
          Function.update (fun j => if j ∈ s then a' j else a j) i (a' i) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp
        · simp [hj]
      rw [e]
      apply inum_update h1 h3 hz ht
      simpa [hi] using (h i).symm
  simpa using (key Finset.univ).symm

theorem fnField_le_join_inl (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) : fnField k y ≤ fnField k (joinPt y y') := by
  unfold fnField
  rw [IntermediateField.adjoin_le_iff]
  rintro t ⟨p, q, hpq, rfl⟩
  apply IntermediateField.subset_adjoin
  exact ⟨⟨Sum.inl p.1, p.2⟩, ⟨Sum.inl q.1, q.2⟩, congrArg Sum.inl hpq, rfl⟩

theorem finite_of_le {F F' : IntermediateField k Ω} (h : F ≤ F') [FiniteDimensional F Ω] : FiniteDimensional F' Ω := by
  letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower F F' Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite F F' Ω

theorem IsPt.join_inl {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω} {d : ℕ} (h : IsPt k y d) (h' : ∀ b, ∃ i, y' ⟨b, i⟩ ≠ 0) :
    IsPt k (joinPt y y') d := by
  obtain ⟨h0, hf, ht⟩ := h
  refine ⟨?_, ?_, ht⟩
  · rintro (b | b)
    · exact h0 b
    · exact h' b
  · haveI := hf
    exact finite_of_le (fnField_le_join_inl (k := k) y y')

theorem num_join_inl (h2 : NumPull) {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω} {d : ℕ} (h : IsPt k y d)
    (h' : ∀ b, ∃ i, y' ⟨b, i⟩ ≠ 0) (a : Fin d → K → ℤ) : num k (joinPt y y') (fun j => Sum.elim (a j) 0) = num k y a := by
  have hv : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap (Sum.inl : K → K ⊕ K')
      (fun p : (Σ b, ι b) => (⟨Sum.inl p.1, p.2⟩ : Σ b, Sum.elim ι ι' b)) := by
    refine ⟨Sum.inl_injective, ?_, fun _ => rfl, ?_⟩
    · intro p q hpq
      obtain ⟨b, i⟩ := p
      obtain ⟨b', i'⟩ := q
      cases hpq
      rfl
    · rintro ⟨b, i⟩ ⟨c, rfl⟩
      exact ⟨⟨c, i⟩, rfl⟩
  have hp : ∀ j, ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg (Sum.inl : K → K ⊕ K') (a j) = Sum.elim (a j) (0 : K' → ℤ) := by
    intro j
    funext x
    cases x with
    | inl c => exact Sum.inl_injective.extend_apply (a j) 0 c
    | inr c =>
      show Function.extend Sum.inl (a j) 0 (Sum.inr c) = 0
      rw [Function.extend_apply' _ _ _ (by rintro ⟨c', hc⟩; cases hc)]
      rfl
  have := h2 k Ω K ι (K ⊕ K') (Sum.elim ι ι') Sum.inl _ (joinPt y y') d a hv (h.join_inl h') h
  simp only [hp] at this
  exact this

theorem num_join_inr (h2 : NumPull) {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω} {d : ℕ} (h : IsPt k y d) (h' : IsPt k y' d)
    (a : Fin d → K' → ℤ) : num k (joinPt y y') (fun j => Sum.elim 0 (a j)) = num k y' a := by
  have hv : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap (Sum.inr : K' → K ⊕ K')
      (fun p : (Σ b, ι' b) => (⟨Sum.inr p.1, p.2⟩ : Σ b, Sum.elim ι ι' b)) := by
    refine ⟨Sum.inr_injective, ?_, fun _ => rfl, ?_⟩
    · intro p q hpq
      obtain ⟨b, i⟩ := p
      obtain ⟨b', i'⟩ := q
      cases hpq
      rfl
    · rintro ⟨b, i⟩ ⟨c, rfl⟩
      exact ⟨⟨c, i⟩, rfl⟩
  have hp : ∀ j, ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg (Sum.inr : K' → K ⊕ K') (a j) = Sum.elim (0 : K → ℤ) (a j) := by
    intro j
    funext x
    cases x with
    | inr c => exact Sum.inr_injective.extend_apply (a j) 0 c
    | inl c =>
      show Function.extend Sum.inr (a j) 0 (Sum.inl c) = 0
      rw [Function.extend_apply' _ _ _ (by rintro ⟨c', hc⟩; cases hc)]
      rfl
  have := h2 k Ω K' ι' (K ⊕ K') (Sum.elim ι ι') Sum.inr _ (joinPt y y') d a hv (h.join_inl h'.1) h'
  simp only [hp] at this
  exact this

theorem exists_top (y : (Σ b, ι b) → Ω) [FiniteDimensional (fnField k y) Ω] :
    ∃ (m : ℕ) (w : (Σ _ : Unit, Option (Fin m)) → Ω), (∀ b, ∃ i, w ⟨b, i⟩ ≠ 0) ∧ fnField k (joinPt y w) = ⊤ := by
  let B := Module.finBasis (fnField k y) Ω
  refine ⟨_, fun x => x.2.elim 1 B, fun _ => ⟨none, one_ne_zero⟩, eq_top_iff.2 fun t _ => ?_⟩
  rw [← B.sum_repr t]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def]
  refine mul_mem (fnField_le_join_inl y _ (B.repr t i).2) (IntermediateField.subset_adjoin _ _ ?_)
  exact ⟨⟨.inr (), some i⟩, ⟨.inr (), none⟩, rfl, (div_one _).symm⟩

theorem numEq : PtDim → NumPull → UnitZero → NumEq := by
  intro h1 h2 h3 k _ Ω _ _ K _ ι _ K' _ ι' _ y y' d a a' hy hy' h
  have hj := hy.join_inl hy'.1
  haveI := hj.2.1
  obtain ⟨m, w, hw, ht⟩ := exists_top (k := k) (joinPt y y')
  rw [← num_join_inl h2 hy hy'.1, ← num_join_inr h2 hy hy', ← num_join_inl h2 hj hw, ← num_join_inl h2 hj hw]
  unfold num
  congr 1
  refine inum_congr h1 h3 (hj.join_inl hw) ht _ _ fun j => ?_
  exact ((ValEq.join_inl _ w _).trans (ValEq.join_inl y y' _)).trans
    ((h j).trans ((ValEq.join_inl _ w _).trans (ValEq.join_inr y y' _)).symm)

end SheetDecomposition
end
end
