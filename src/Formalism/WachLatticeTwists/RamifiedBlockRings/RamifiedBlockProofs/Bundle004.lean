module

public import Formalism.WachLatticeTwists.RamifiedBlockRings.Bundle001
public import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.Bundle003
public import Formalism.WachLatticeTwists.RamifiedBlockRings.LemmaFiveThreeAnyResidueField
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.WachLatticeTwists.CoprimeLiftBounds.Statement

@[expose] public section

section

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.BR

section

variable {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O']
  [IsDiscreteValuationRing O'] [Algebra O O'] {X d G : Type} [Fintype d] [DecidableEq d] [Group G] {t : ℕ}
  {bl : d → Fin (t + 1)} {T : Subalgebra O (X → O)} {r : G →* (X → Matrix d d O)} {π : X}
  {χ₁ ε : G →* Oˣ} {g₀ : G} {eB e₁ s : X → Matrix d d O} {D : RingData O X d G t bl}
  {D' : RingData O' X d G t bl}

private theorem blockPoly_map_lemma {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {d : Type*}
    [Fintype d] [DecidableEq d] (e a : Matrix d d A) :
    blockPoly (e.map f) (a.map f) = (blockPoly e a).map f := by
  unfold blockPoly
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

theorem blockPoly_bc (x : X) :
    blockPoly ((bcM O' eB x).map (algebraMap O' (FractionRing O')))
      ((bcM O' eB x * bcR O' r g₀ x * bcM O' eB x + bcM O' s x).map (algebraMap O' (FractionRing O'))) =
    ((blockPoly (eB x) (eB x * r g₀ x * eB x + s x)).map (algebraMap O O')).map
      (algebraMap O' (FractionRing O')) := by
  have h1 : bcM O' eB x = (eB x).map (algebraMap O O') := rfl
  have h3 : bcR O' r g₀ x = (r g₀ x).map (algebraMap O O') := rfl
  have hs : bcM O' s x = (s x).map (algebraMap O O') := rfl
  have h2 : bcM O' eB x * bcR O' r g₀ x * bcM O' eB x + bcM O' s x =
      (eB x * r g₀ x * eB x + s x).map (algebraMap O O') := by
    rw [h1, h3, hs]
    ext i j

    simp [Matrix.mul_apply, Matrix.add_apply, map_sum, map_mul, map_add (f := _)]
  rw [h2, h1, blockPoly_map_lemma, blockPoly_map_lemma]

theorem exists_sigma (hj : Function.Injective (algebraMap O O')) (hX : DistinctEigenvalueCornerPerturbation O T r π t g₀ eB s)
    (hD : RingDef O T r π χ₁ ε g₀ eB e₁ s D)
    (hD' : RingDef O' (bcT O' T) (bcR O' r) π (bcChar O' χ₁) (bcChar O' ε) g₀ (bcM O' eB) (bcM O' e₁)
      (bcM O' s) D') :
    ∃ σ : D'.X' → D.X', (∀ y', D.p (σ y') = D'.p y') ∧
      (∀ y' i, i < t → algebraMap O O' ((D.rr i : D.X' → O) (σ y')) = (D'.rr i : D'.X' → O') y') ∧
      σ D'.π' = D.π' := by
  classical
  have hι'inj : Function.Injective (algebraMap O' (FractionRing O')) :=
    IsFractionRing.injective O' (FractionRing O')
  have hD0 := hD
  have hD'0 := hD'
  dsimp only [RingDef] at hD0 hD'0
  obtain ⟨-, huniq, -, -, hpπ, hrrπ, -⟩ := hD0
  obtain ⟨hfac', -, -, -, hpπ', hrrπ', -⟩ := hD'0
  unfold DistinctEigenvalueCornerPerturbation at hX
  obtain ⟨-, -, -, -, hαX⟩ := hX
  have key : ∀ y' : D'.X', ∃! x' : D.X', D.p x' = D'.p y' ∧
      ∀ i, i < t → algebraMap O O' ((D.rr i : D.X' → O) x') = (D'.rr i : D'.X' → O') y' := by
    intro y'
    have h1 : ((blockPoly (eB (D'.p y')) (eB (D'.p y') * r g₀ (D'.p y') * eB (D'.p y') + s (D'.p y'))).map
        (algebraMap O O')).map (algebraMap O' (FractionRing O')) =
        ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C
          (algebraMap O' (FractionRing O') ((D'.rr i : D'.X' → O') y'))) := by
      rw [← blockPoly_bc]
      exact hfac' y'
    obtain ⟨α, -, hα⟩ := hαX (D'.p y')
    rw [blockPoly_map_lemma] at hα
    obtain ⟨β, -, hβ⟩ := rootsInt O _ t α hα
    have hroot : ∀ i, i < t → ∃ b : O, algebraMap O O' b = (D'.rr i : D'.X' → O') y' := by
      intro i hi
      have h2 := congrArg (Polynomial.eval
        (algebraMap O' (FractionRing O') ((D'.rr i : D'.X' → O') y'))) h1
      rw [hβ] at h2
      simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h2
      have h3 : ∏ k ∈ Finset.range t, (algebraMap O' (FractionRing O') ((D'.rr i : D'.X' → O') y') -
          algebraMap O' (FractionRing O') ((D'.rr k : D'.X' → O') y')) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.2 hi) (sub_self _)
      rw [h3, Finset.prod_eq_zero_iff] at h2
      obtain ⟨j, -, hj0⟩ := h2
      exact ⟨β j, hι'inj (sub_eq_zero.1 hj0).symm⟩
    choose b hb using hroot
    let α' : ℕ → O := fun i => if h : i < t then b i h else 0
    have hα' : ∀ i, i < t → algebraMap O O' (α' i) = (D'.rr i : D'.X' → O') y' := by
      intro i hi
      simp only [α', dif_pos hi]
      exact hb i hi
    have hPinj : Function.Injective
        (Polynomial.map ((algebraMap O' (FractionRing O')).comp (algebraMap O O'))) :=
      Polynomial.map_injective _ (hι'inj.comp hj)
    have hP2 : blockPoly (eB (D'.p y')) (eB (D'.p y') * r g₀ (D'.p y') * eB (D'.p y') + s (D'.p y')) =
        ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (α' i)) := by
      apply hPinj
      rw [← Polynomial.map_map, h1]
      simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        RingHom.comp_apply]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [hα' i (Finset.mem_range.1 hi)]
    have hfacO : blockPoly ((eB (D'.p y')).map (algebraMap O (FractionRing O)))
        ((eB (D'.p y') * r g₀ (D'.p y') * eB (D'.p y') + s (D'.p y')).map (algebraMap O (FractionRing O))) =
        ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (algebraMap O (FractionRing O) (α' i))) := by
      rw [blockPoly_map_lemma, hP2]
      simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    obtain ⟨x', ⟨hx'1, hx'2⟩, hx'u⟩ := huniq (D'.p y') α' hfacO
    refine ⟨x', ⟨hx'1, fun i hi => by rw [hx'2 i hi, hα' i hi]⟩, ?_⟩
    rintro z ⟨hz1, hz2⟩
    refine hx'u z ⟨hz1, fun i hi => hj ?_⟩
    rw [hz2 i hi, hα' i hi]
  choose σ hσ using fun y' => (key y').exists
  refine ⟨σ, fun y' => (hσ y').1, fun y' i hi => (hσ y').2 i hi, ?_⟩
  refine (key D'.π').unique (hσ D'.π') ⟨by rw [hpπ, hpπ'], fun i hi => ?_⟩
  rw [hrrπ i hi, hrrπ' i hi]
  simp [bcChar]

theorem bcT'_mem (hD : RingDef O T r π χ₁ ε g₀ eB e₁ s D)
    (hD' : RingDef O' (bcT O' T) (bcR O' r) π (bcChar O' χ₁) (bcChar O' ε) g₀ (bcM O' eB) (bcM O' e₁)
      (bcM O' s) D') (σ : D'.X' → D.X') (hσ1 : ∀ y', D.p (σ y') = D'.p y')
    (hσ2 : ∀ y' i, i < t →
      algebraMap O O' ((D.rr i : D.X' → O) (σ y')) = (D'.rr i : D'.X' → O') y')
    {f : D.X' → O} (hf : f ∈ D.T') : (fun y' => algebraMap O O' (f (σ y'))) ∈ D'.T' := by
  dsimp only [RingDef] at hD hD'
  obtain ⟨-, -, hT, -⟩ := hD
  obtain ⟨-, -, hT', -⟩ := hD'
  rw [hT] at hf
  rw [hT']
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
    apply Algebra.subset_adjoin
    rcases hx with ⟨g, hg, rfl⟩ | ⟨i, hi, rfl⟩
    · refine Or.inl ⟨algebraMap O O' ∘ g, Algebra.subset_adjoin ⟨g, hg, rfl⟩, ?_⟩
      funext y'
      simp [hσ1 y']
    · exact Or.inr ⟨i, hi, funext fun y' => hσ2 y' i hi⟩
  | algebraMap c =>
    convert Subalgebra.algebraMap_mem (Algebra.adjoin O' _) (algebraMap O O' c) using 1
    funext y'
    simp
  | add x y _ _ ihx ihy =>
    convert Subalgebra.add_mem _ ihx ihy using 1
    funext y'
    simp
  | mul x y _ _ ihx ihy =>
    convert Subalgebra.mul_mem _ ihx ihy using 1
    funext y'
    simp

theorem bcR'_mem (hD : RingDef O T r π χ₁ ε g₀ eB e₁ s D)
    (hD' : RingDef O' (bcT O' T) (bcR O' r) π (bcChar O' χ₁) (bcChar O' ε) g₀ (bcM O' eB) (bcM O' e₁)
      (bcM O' s) D') (σ : D'.X' → D.X') (hσ1 : ∀ y', D.p (σ y') = D'.p y')
    (hσ2 : ∀ y' i, i < t →
      algebraMap O O' ((D.rr i : D.X' → O) (σ y')) = (D'.rr i : D'.X' → O') y')
    (κ : FractionRing O →+* FractionRing O')
    (hκ : ∀ y, κ (algebraMap O (FractionRing O) y) = algebraMap O' (FractionRing O') (algebraMap O O' y))
    {a : D.X' → Matrix d d (FractionRing O)} (ha : a ∈ D.R') :
    (fun y' => (a (σ y')).map κ) ∈ D'.R' := by
  have hmem : ∀ f ∈ D.T', (fun y' => algebraMap O O' (f (σ y'))) ∈ D'.T' :=
    fun f hf => bcT'_mem hD hD' σ hσ1 hσ2 hf
  dsimp only [RingDef] at hD hD'
  obtain ⟨-, -, -, -, -, -, hr, hR, -⟩ := hD
  obtain ⟨-, -, -, -, -, -, hr', hR', -⟩ := hD'
  have ha2 := (hR a).1 ha
  refine (hR' _).2 ?_
  simp only [tSpan, Set.mem_setOf_eq] at ha2 ⊢
  obtain ⟨s0, c, hc, rfl⟩ := ha2
  refine ⟨s0, fun g y' => algebraMap O O' (c g (σ y')),
    fun g => hmem _ (hc g), ?_⟩
  funext y'
  ext i j

  simp [Finset.sum_apply, Matrix.sum_apply, map_sum, hr, hr', hσ1, hκ, bcR, bcM]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, hκ, hκ, ← IsScalarTower.algebraMap_apply O O' (FractionRing O')]

end

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

section

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem relMap_mul {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M] {l m n : Type*} [Fintype l]
    [Fintype m] [Fintype n] (C : Matrix l m O) (B : Matrix m n O) (v : n → M) :
    relMap O M (C * B) v = relMap O M C (relMap O M B v) := by
  ext i
  simp only [relMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, Finset.sum_smul,
    Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem ker_eq_of_factor {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M] {m n : Type*}
    [Fintype m] [Fintype n] (A : Matrix m n O) (B : Matrix n n O) (C : Matrix m n O)
    (C' : Matrix n m O) (h1 : A = C * B) (h2 : B = C' * A) :
    LinearMap.ker (relMap O M A) = LinearMap.ker (relMap O M B) := by
  ext v
  simp only [LinearMap.mem_ker]
  constructor
  · intro hv
    rw [h2, relMap_mul, hv, map_zero]
  · intro hv
    rw [h1, relMap_mul, hv, map_zero]

private theorem sum_extend_embedding_zero_eq_sum {α β M : Type*} [Fintype α] [Fintype β] [AddCommMonoid M]
    (f : α ↪ β) (φ : α → M) : ∑ l, Function.extend f φ 0 l = ∑ j, φ j := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map f)), Finset.sum_map]
  · simp only [Function.Embedding.coeFn_mk, f.injective.extend_apply]
  · intro l _ hl
    rw [Function.extend_apply']
    · rfl
    · rintro ⟨j, rfl⟩
      exact hl (Finset.mem_map_of_mem _ (Finset.mem_univ j))

theorem exists_square {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {m n : Type}
    [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n O) :
    ∃ (B : Matrix n n O) (C : Matrix m n O) (C' : Matrix n m O), A = C * B ∧ B = C' * A := by
  classical
  obtain ⟨k, b⟩ := Submodule.basisOfPid (Pi.basisFun O n) (Submodule.span O (Set.range A))
  have hk : Fintype.card (Fin k) ≤ Fintype.card n := by
    have h := Submodule.finrank_le (Submodule.span O (Set.range A))
    rw [Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card] at h
    exact h
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hk
  have hA : ∀ i, A i ∈ Submodule.span O (Set.range A) := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hb : ∀ j, ∃ w : m → O, ∑ i, w i • A i = (b j : n → O) := fun j =>
    (Submodule.mem_span_range_iff_exists_fun O).1 (b j).2
  choose w hw using hb
  refine ⟨Function.extend f (fun j => (b j : n → O)) 0,
    fun i => Function.extend f (fun j => b.repr ⟨A i, hA i⟩ j) 0,
    Function.extend f w 0, ?_, ?_⟩
  · ext i c
    erw [Matrix.mul_apply]
    have hterm : ∀ l, Function.extend f (fun j => b.repr ⟨A i, hA i⟩ j) 0 l *
        Function.extend f (fun j => (b j : n → O)) 0 l c =
        Function.extend f (fun j => b.repr ⟨A i, hA i⟩ j * (b j : n → O) c) 0 l := by
      intro l
      by_cases hl : ∃ j, f j = l
      · obtain ⟨j, rfl⟩ := hl
        simp only [f.injective.extend_apply]
      · simp only [Function.extend_apply' _ _ _ hl, Pi.zero_apply, zero_mul]
    simp_rw [hterm]
    rw [sum_extend_embedding_zero_eq_sum]
    have h := congrArg (fun x : Submodule.span O (Set.range A) => (x : n → O) c)
      (b.sum_repr ⟨A i, hA i⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h
    exact h.symm
  · ext l c
    erw [Matrix.mul_apply]
    by_cases hl : ∃ j, f j = l
    · obtain ⟨j, rfl⟩ := hl
      simp only [f.injective.extend_apply]
      have h := congrFun (hw j) c
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
      exact h.symm
    · simp [Function.extend_apply' _ _ _ hl]

theorem kerBc : StatKerBc := by
  intro O O' _ _ _ _ _ _ _ e he m n _ _ _ A
  obtain ⟨B, C, C', h1, h2⟩ := exists_square A
  let j : O →+* O' := algebraMap O O'
  have h1' : A.map j = C.map j * B.map j := by rw [← Matrix.map_mul, ← h1]
  have h2' : B.map j = C'.map j * A.map j := by rw [← Matrix.map_mul, ← h2]
  rw [ker_eq_of_factor A B C C' h1 h2, ker_eq_of_factor (A.map j) (B.map j) (C.map j) (C'.map j) h1' h2']
  have e1 := lenKer O n B
  have e2 := lenKer O' n (B.map j)
  unfold matQ at e1 e2
  rw [e1, e2, ← he]
  congr 1
  exact (RingHom.map_det j B).symm

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end
