module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle191
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1024
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleSpreadFromLocalScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1025
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenFinite

theorem finiteDimensional_of_trdeg_eq (F A B K L : Type) [Field F] [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Field K] [Field L] [Algebra F A] [Algebra A B] [Algebra F B]
    [IsScalarTower F A B] [Algebra A K] [Algebra B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L]
    [Algebra.FiniteType A B] (n : ℕ) (hA : Algebra.trdeg F A = n) (hB : Algebra.trdeg F B = n) :
    FiniteDimensional K L := by
  letI : Algebra F K := ((algebraMap A K).comp (algebraMap F A)).toAlgebra
  letI : Algebra F L := ((algebraMap B L).comp (algebraMap F B)).toAlgebra
  haveI : IsScalarTower F A K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower F B L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower F K L := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    change algebraMap B L (algebraMap F B x) = algebraMap K L (algebraMap A K (algebraMap F A x))
    rw [← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
      ← IsScalarTower.algebraMap_apply F A B]
  haveI : FaithfulSMul F A := (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F A).injective
  haveI : FaithfulSMul F B := (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F B).injective
  haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective A K)
  haveI : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective B L)
  haveI : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  haveI : Algebra.IsAlgebraic B L := IsLocalization.isAlgebraic L (nonZeroDivisors B)
  have hK : Algebra.trdeg F K = n := (trdeg_eq_of_isAlgebraic_top F A K).trans hA
  have hL : Algebra.trdeg F L = n := (trdeg_eq_of_isAlgebraic_top F B L).trans hB
  have h0 : Algebra.trdeg K L = 0 := by
    have e := trdeg_add_eq F K (A := L)
    rw [hK, hL] at e
    rcases (Cardinal.add_eq_left_iff).1 e with h | h
    · exact absurd (le_trans (le_max_left _ _) h) (not_le.2 (Cardinal.natCast_lt_aleph0))
    · exact h
  haveI : Algebra.IsAlgebraic K L := trdeg_eq_zero_iff.1 h0
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType A B).out
  let g : B →ₐ[A] L := IsScalarTower.toAlgHom A B L
  let T : IntermediateField K L := IntermediateField.adjoin K (g '' (s : Set B))
  have hfin : FiniteDimensional K T :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hrange : ∀ b : B, algebraMap B L b ∈ T := by
    intro b
    have hb : b ∈ Algebra.adjoin A (s : Set B) := hs ▸ Algebra.mem_top
    have : g b ∈ (Algebra.adjoin A (s : Set B)).map g := Subalgebra.mem_map.2 ⟨b, hb, rfl⟩
    rw [AlgHom.map_adjoin] at this
    have hle : Algebra.adjoin A (g '' (s : Set B)) ≤ T.toSubalgebra.restrictScalars A :=
      Algebra.adjoin_le (IntermediateField.subset_adjoin K _)
    exact hle this
  have htop : T = ⊤ := by
    refine eq_top_iff.2 fun l _ => ?_
    obtain ⟨x, y, _, rfl⟩ := IsFractionRing.div_surjective (A := B) l
    exact T.div_mem (hrange x) (hrange y)
  rw [htop] at hfin
  exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv

end GlobalTheory.GenFinite

namespace GlobalTheory.GenFinite

theorem trdeg_affineOpen_eq (F : Type) [Field F] {Y : Scheme.{0}} [IsIntegral Y]
    (q : Y ⟶ Sp F) [LocallyOfFiniteType q] {U : Y.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set Y).Nonempty) [Algebra F Γ(Y, U)] [Algebra.FiniteType F Γ(Y, U)] (n : ℕ)
    (hn : topologicalKrullDim Y = n) : Algebra.trdeg F Γ(Y, U) = n := by
  haveI : Nonempty U := ⟨⟨hne.some, hne.some_mem⟩⟩
  obtain ⟨d, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq F Γ(Y, U)
  have e : topologicalKrullDim (U : Set Y) = d := by
    rw [← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
      hU.range_fromSpec
  rw [GlobalTheory.OpenDim.topologicalKrullDim_open F q U hne, hn] at e
  have hd : d = n := by exact_mod_cast e.symm
  rw [h₂, hd]

theorem residueDegree_genericPoint_ne_zero : ∀ (F : Type) [Field F] (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp F) (f : M ⟶ W) (n : ℕ), LocallyOfFiniteType p → LocallyOfFiniteType f → Surjective f → topologicalKrullDim M = n → topologicalKrullDim W = n → f.residueDegree (genericPoint M) ≠ 0 := by
  intro F _ M W _ _ p f n hp hf hs hM hW
  have hη : f (genericPoint M) = genericPoint W := by
    have := (genericPoint_spec M).image f.continuous
    rw [Set.image_univ, f.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec W)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint W)) isOpen_univ
  have hV : IsAffineOpen V := hV
  have hx : f (genericPoint M) ∈ V := hη ▸ hxV
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, hUV⟩ := M.isBasis_affineOpens.exists_subset_of_mem_open
    (show genericPoint M ∈ f ⁻¹ᵁ V from hx) (f ⁻¹ᵁ V).isOpen
  have hU : IsAffineOpen U := hU
  haveI : Nonempty V := ⟨⟨_, hx⟩⟩
  haveI : Nonempty U := ⟨⟨_, hy⟩⟩
  have e : U ≤ f ⁻¹ᵁ V := hUV
  let φ := Spec.preimage (hV.fromSpec ≫ p)
  have hφ : Spec.map φ = hV.fromSpec ≫ p := Spec.map_preimage _
  letI : Algebra F Γ(W, V) := φ.hom.toAlgebra
  have hftA : Algebra.FiniteType F Γ(W, V) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  letI : Algebra Γ(W, V) Γ(M, U) := (f.appLE V U e).hom.toAlgebra
  have hftB : Algebra.FiniteType Γ(W, V) Γ(M, U) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f hf ⟨V, hV⟩ ⟨U, hU⟩ e
  letI : Algebra F Γ(M, U) := (φ ≫ f.appLE V U e).hom.toAlgebra
  haveI : IsScalarTower F Γ(W, V) Γ(M, U) := IsScalarTower.of_algebraMap_eq' rfl
  have hftC : Algebra.FiniteType F Γ(M, U) := Algebra.FiniteType.trans hftA hftB
  have hA : Algebra.trdeg F Γ(W, V) = n := trdeg_affineOpen_eq F p hV ⟨_, hx⟩ n hW
  have hB : Algebra.trdeg F Γ(M, U) = n := trdeg_affineOpen_eq F (f ≫ p) hU ⟨_, hy⟩ n hM
  letI := (W.evaluation V _ hx).hom.toAlgebra
  letI := (M.evaluation U _ hy).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint M)).hom.toAlgebra
  letI : Algebra Γ(W, V) (M.residueField (genericPoint M)) :=
    (f.appLE V U e ≫ M.evaluation U _ hy).hom.toAlgebra
  haveI : IsScalarTower Γ(W, V) Γ(M, U) (M.residueField (genericPoint M)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have nat : f.appLE V U e ≫ M.evaluation U _ hy =
      W.evaluation V _ hx ≫ f.residueFieldMap (genericPoint M) := by
    rw [Scheme.evaluation_naturality f _ hx, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp only [Scheme.evaluation]
    rw [← Category.assoc, TopCat.Presheaf.germ_res]
  haveI : IsScalarTower Γ(W, V) (W.residueField (f (genericPoint M)))
      (M.residueField (genericPoint M)) :=
    IsScalarTower.of_algebraMap_eq' congr($(nat).hom)
  haveI := GenFiniteEtale.isFractionRing_eval W hV hη hx
  haveI := GenFiniteEtale.isFractionRing_eval M hU rfl hy
  have := finiteDimensional_of_trdeg_eq F Γ(W, V) Γ(M, U) (W.residueField (f (genericPoint M)))
    (M.residueField (genericPoint M)) n hA hB
  change Module.finrank (W.residueField (f (genericPoint M))) (M.residueField (genericPoint M)) ≠ 0
  exact Module.finrank_pos.ne'

end GlobalTheory.GenFinite
end
end

section

open scoped nonZeroDivisors

namespace GlobalTheory.ReducedNormalisation

theorem exists_mem_others_not_mem {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → Ideal R) (hp : ∀ i, (p i).IsPrime) (hmin : ∀ i j, p i ≤ p j → i = j) (i : ι) :
    ∃ a : R, a ∉ p i ∧ ∀ j, j ≠ i → a ∈ p j := by
  by_contra h
  push_neg at h
  have hle : (Finset.univ.erase i).inf p ≤ p i := by
    intro a ha
    by_contra hai
    obtain ⟨j, hj, hja⟩ := h a hai
    exact hja ((Finset.inf_le (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩) : _ ≤ p j) ha)
  obtain ⟨j, hj, hji⟩ := ((hp i).inf_le').1 hle
  exact (Finset.mem_erase.1 hj).1 (hmin j i hji)

theorem exists_conductor_elem {R : Type} [CommRing R] (p : Ideal R) [hp : p.IsPrime] (J : Ideal R)
    (e : R) (he : e ∈ J) (hep : e ∉ p)
    [Module.Finite (R ⧸ p) (integralClosure (R ⧸ p) (FractionRing (R ⧸ p)))] :
    ∃ c : R, c ∉ p ∧ c ∈ J ∧ ∀ d : integralClosure (R ⧸ p) (FractionRing (R ⧸ p)),
      ∃ y ∈ J, algebraMap R (FractionRing (R ⧸ p)) y =
        algebraMap R (FractionRing (R ⧸ p)) c * (d : FractionRing (R ⧸ p)) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R ⧸ p)
    (M := integralClosure (R ⧸ p) (FractionRing (R ⧸ p)))
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (R ⧸ p)⁰
    (S := FractionRing (R ⧸ p)) (s.image Subtype.val)
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (b : R ⧸ p)
  have htp : t ∉ p := by
    intro h
    have h0 : (b : R ⧸ p) = 0 := by rw [← ht]; exact Ideal.Quotient.eq_zero_iff_mem.2 h
    exact nonZeroDivisors.coe_ne_zero b h0
  refine ⟨e * t, fun h => (hp.mem_or_mem h).elim hep htp, J.mul_mem_right t he, fun d => ?_⟩
  have key : ∀ d ∈ Submodule.span (R ⧸ p)
      (s : Set (integralClosure (R ⧸ p) (FractionRing (R ⧸ p)))),
      ∃ y ∈ J, algebraMap R (FractionRing (R ⧸ p)) y =
        algebraMap R (FractionRing (R ⧸ p)) (e * t) * (d : FractionRing (R ⧸ p)) := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨x, hx⟩ := hb (g : FractionRing (R ⧸ p)) (Finset.mem_image_of_mem Subtype.val hg)
      obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨e * x', J.mul_mem_right x' he, ?_⟩
      have h1 : algebraMap R (FractionRing (R ⧸ p)) x' =
          algebraMap R (FractionRing (R ⧸ p)) t * (g : FractionRing (R ⧸ p)) := by
        rw [IsScalarTower.algebraMap_apply R (R ⧸ p) (FractionRing (R ⧸ p)) x',
          IsScalarTower.algebraMap_apply R (R ⧸ p) (FractionRing (R ⧸ p)) t,
          Ideal.Quotient.algebraMap_eq, hx, ht]
        exact Algebra.smul_def _ _
      rw [map_mul, map_mul, h1, mul_assoc]
    | zero => exact ⟨0, J.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨y1, hy1, e1⟩ := hx
      obtain ⟨y2, hy2, e2⟩ := hy
      exact ⟨y1 + y2, J.add_mem hy1 hy2, by
        rw [map_add (f := _), e1, e2, ← mul_add]; rfl⟩
    | smul q x _ hx =>
      obtain ⟨y1, hy1, e1⟩ := hx
      obtain ⟨q', rfl⟩ := Ideal.Quotient.mk_surjective q
      refine ⟨q' * y1, J.mul_mem_left q' hy1, ?_⟩
      rw [map_mul, e1]
      show _ = _ * ((Ideal.Quotient.mk p q') • (x : FractionRing (R ⧸ p)))
      rw [Algebra.smul_def, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      ring
  exact key d (by rw [hs]; trivial)

theorem algebraMap_eq_zero_of_mem {R : Type} [CommRing R] (p : Ideal R) [p.IsPrime] {z : R}
    (hz : z ∈ p) : algebraMap R (FractionRing (R ⧸ p)) z = 0 := by
  rw [IsScalarTower.algebraMap_apply R (R ⧸ p) (FractionRing (R ⧸ p)),
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hz, map_zero]

theorem exists_conductor {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → Ideal R) [hp : ∀ i, (p i).IsPrime] (hmin : ∀ i j, p i ≤ p j → i = j)
    [∀ i, Module.Finite (R ⧸ p i) (integralClosure (R ⧸ p i) (FractionRing (R ⧸ p i)))] :
    ∃ a : R, (∀ i, a ∉ p i) ∧
      ∀ r : (∀ i, integralClosure (R ⧸ p i) (FractionRing (R ⧸ p i))),
        ∃ y : R, algebraMap R _ y = algebraMap R _ a * r := by
  classical
  have hc : ∀ i, ∃ c : R, c ∉ p i ∧ c ∈ (⨅ (j : ι) (_ : j ≠ i), p j) ∧
      ∀ d : integralClosure (R ⧸ p i) (FractionRing (R ⧸ p i)),
        ∃ y ∈ (⨅ (j : ι) (_ : j ≠ i), p j), algebraMap R (FractionRing (R ⧸ p i)) y =
          algebraMap R (FractionRing (R ⧸ p i)) c * (d : FractionRing (R ⧸ p i)) := by
    intro i
    obtain ⟨e, hei, hej⟩ := exists_mem_others_not_mem p hp hmin i
    exact exists_conductor_elem (p i) _ e
      ((Submodule.mem_iInf _).2 fun j => (Submodule.mem_iInf _).2 fun hj => hej j hj) hei
  choose c hcp hcJ hcd using hc
  have hmemJ : ∀ {i k : ι} {z : R}, z ∈ (⨅ (j : ι) (_ : j ≠ i), p j) → i ≠ k → z ∈ p k :=
    fun hz hik => (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hz _) (Ne.symm hik)
  refine ⟨∑ i, c i, fun i h => hcp i ?_, fun r => ?_⟩
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h
    refine (Submodule.add_mem_iff_left _ (Submodule.sum_mem _ fun j hj => ?_)).1 h
    exact hmemJ (hcJ j) (Finset.mem_erase.1 hj).1
  choose y hyJ hy using fun i => hcd i (r i)
  refine ⟨∑ i, y i, funext fun k => Subtype.ext ?_⟩
  change algebraMap R (FractionRing (R ⧸ p k)) (∑ i, y i) =
    algebraMap R (FractionRing (R ⧸ p k)) (∑ i, c i) * (r k : FractionRing (R ⧸ p k))

  rw [map_sum, map_sum, Finset.sum_mul, Finset.sum_eq_single k, Finset.sum_eq_single k, hy k]
  · intro i _ hik
    rw [algebraMap_eq_zero_of_mem (p k) (hmemJ (hcJ i) hik), zero_mul]
  · intro h; exact absurd (Finset.mem_univ k) h
  · intro i _ hik
    exact algebraMap_eq_zero_of_mem (p k) (hmemJ (hyJ i) hik)
  · intro h; exact absurd (Finset.mem_univ k) h

end GlobalTheory.ReducedNormalisation

namespace GlobalTheory.ReducedNormalisation

theorem exists_finiteIndex_prod_normalDomains :
    ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] [IsReduced R] [Nontrivial R],
      ∃ (n : ℕ) (D : Fin n → Type) (_ : ∀ i, CommRing (D i)) (_ : ∀ i, Algebra R (D i)),
        (∀ i, IsDomain (D i) ∧ IsIntegrallyClosed (D i) ∧ Module.Finite R (D i)) ∧
        Function.Injective (algebraMap R (∀ i, D i)) ∧
        ∃ a : R, a ≠ 0 ∧ ∀ r : (∀ i, D i), ∃ y : R,
          algebraMap R (∀ i, D i) y = algebraMap R (∀ i, D i) a * r := by
  intro R _ _ _ _
  classical
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  letI : Fintype (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing R).fintype
  let e := Fintype.equivFin (minimalPrimes R)
  let p : Fin (Fintype.card (minimalPrimes R)) → Ideal R := fun k => (e.symm k).1
  haveI hp : ∀ k, (p k).IsPrime := fun k => Ideal.minimalPrimes_isPrime (e.symm k).2
  have hmin : ∀ k l, p k ≤ p l → k = l := by
    intro k l h
    have h2 : p l ≤ p k := (e.symm l).2.2 ⟨hp k, bot_le⟩ h
    exact e.symm.injective (Subtype.ext (le_antisymm h h2))
  haveI : ∀ k, Module.Finite (R ⧸ p k) (integralClosure (R ⧸ p k) (FractionRing (R ⧸ p k))) :=
    fun k => by
      have h : Algebra.EssFiniteType ℤ (R ⧸ p k) := Algebra.instEssFiniteTypeQuotientIdeal ℤ R (p k)
      refine @GlobalTheory.finite_integralClosure_of_essFiniteType_int (R ⧸ p k) _ _ ?_
      convert h
      first | exact Subsingleton.elim _ _ | exact Algebra.algebra_ext _ _ fun r => (eq_intCast _ r).trans (eq_intCast _ r).symm
  obtain ⟨a, ha, hr⟩ := exists_conductor p hmin
  have hzero : ∀ {x : R} (k), algebraMap R (integralClosure (R ⧸ p k) (FractionRing (R ⧸ p k))) x = 0 →
      x ∈ p k := by
    intro x k hx
    have h1 : algebraMap R (FractionRing (R ⧸ p k)) x = 0 := congrArg Subtype.val hx
    rw [IsScalarTower.algebraMap_apply R (R ⧸ p k) (FractionRing (R ⧸ p k)),
      Ideal.Quotient.algebraMap_eq] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1
      ((map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ p k) (FractionRing (R ⧸ p k)))).1 h1)
  refine ⟨Fintype.card (minimalPrimes R),
    fun k => integralClosure (R ⧸ p k) (FractionRing (R ⧸ p k)), fun k => inferInstance,
    fun k => inferInstance, fun k => ⟨inferInstance,
      integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing (R ⧸ p k)),
      Module.Finite.trans (R ⧸ p k) _⟩, ?_, a, ?_, hr⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have hmem : x ∈ sInf (minimalPrimes R) := Submodule.mem_sInf.2 fun q hq => by
      have := hzero (e ⟨q, hq⟩) (congrFun hx (e ⟨q, hq⟩))
      simpa [p] using this
    rw [minimalPrimes, Ideal.sInf_minimalPrimes] at hmem
    exact IsReduced.eq_zero x (mem_nilradical.mp hmem)
  · intro h0
    obtain ⟨q⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal R)) bot_ne_top
    apply ha (e q)
    rw [h0]
    exact zero_mem _

end GlobalTheory.ReducedNormalisation

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

theorem _root_.GlobalTheory.T.homFixedPullbackRep_of_affineTests : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left), L.IsLB → M.IsLB →
  ∀ (H : Scheme.{0}) (π : H ⟶ S) (AH : Over H) [GrpObj AH] (BH : Over H) [GrpObj BH]
    (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH),
    IsGrpPullback AH A π φA → IsGrpPullback BH B π φB →
    (∀ (R : Type) [CommRing R] (t : Sp R ⟶ S) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : Sp R ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left) →
    ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : T ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left := by
  first | exact @GlobalTheory.EndLoc.HomFixGlue.rep_of_affine | exact GlobalTheory.EndLoc.HomFixGlue.rep_of_affine | (intros; apply GlobalTheory.EndLoc.HomFixGlue.rep_of_affine <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_lineBundle_spread_from_localScheme : ∀ {S Y U YU : Scheme.{0}} [IsLocallyNoetherian S] (f : Y ⟶ S) [QuasiCompact f] [QuasiSeparated f] (j : U ⟶ S) [IsOpenImmersion j] (e : YU ⟶ Y) (fU : YU ⟶ U), IsPullback e fU f j → ∀ (L : LB YU), L.IsLB → ∀ (x : S) (N : LB (pullback f (S.fromSpecStalk x))), N.IsLB → (∀ (T : Scheme.{0}) (a : T ⟶ pullback f (S.fromSpecStalk x)) (b : T ⟶ YU), a ≫ pullback.fst f (S.fromSpecStalk x) = b ≫ e → LBIso (N.pull a) (L.pull b)) → ∃ W : S.Opens, x ∈ W ∧ ∃ N' : LB ↑(f ⁻¹ᵁ W), N'.IsLB ∧ ∀ (T : Scheme.{0}) (a : T ⟶ ↑(f ⁻¹ᵁ W)) (b : T ⟶ YU), a ≫ (f ⁻¹ᵁ W).ι = b ≫ e → LBIso (N'.pull a) (L.pull b) := by
  first | exact @GlobalTheory.SpreadLB.exists_spread | exact GlobalTheory.SpreadLB.exists_spread | (intros; apply GlobalTheory.SpreadLB.exists_spread <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.symmetry_secondDifference_eq_cubical_ratio : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (x y : T ⟶ D.P.A) (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → val D.sym (x * y).left z J * cubV D.cub z J y y⁻¹ x⁻¹ = val D.sym x.left z J * val D.sym y.left z J * cubV D.cub z J x x⁻¹ y := by
  first | exact @GlobalTheory.PolDeg.SymCube.sym_cube | exact GlobalTheory.PolDeg.SymCube.sym_cube | (intros; apply GlobalTheory.PolDeg.SymCube.sym_cube <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.chartAroundUnit (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (s : Sp R) :
    ∃ f : R, s ∈ Set.range (spMap (algebraMap R (Localization.Away f))) ∧ ∃ W : A.left.Opens,
      IsAffineOpen W ∧ ∀ t ∈ Set.range (spMap (algebraMap R (Localization.Away f))),
        ∃ x ∈ W, A.hom x = t := by
  let e : Sp R ⟶ A.left := (η[A]).left
  have he : e ≫ A.hom = 𝟙 (Sp R) := Over.w (η[A])
  have hpt : ∀ t : Sp R, A.hom (e t) = t := by
    intro t
    rw [← Scheme.Hom.comp_apply, he]
    rfl
  obtain ⟨W, hW, hsW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := e s) trivial
  have hrange : ∀ f : R, Set.range (spMap (algebraMap R (Localization.Away f))) =
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
    intro f
    exact PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  have hopen : IsOpen (e ⁻¹' (W : Set A.left)) := W.isOpen.preimage e.continuous
  obtain ⟨_, ⟨f, rfl⟩, hsf, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
      (a := s) hsW hopen
  refine ⟨f, ?_, W, hW, ?_⟩
  · rw [hrange]; exact hsf
  · intro t ht
    rw [hrange] at ht
    exact ⟨e t, hsub ht, hpt t⟩
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem affine_preimage_pullback_meets_fibres {R R' : Type} [CommRing R] [CommRing R'] (a : R →+* R')
    (A : Over (Sp R)) (W : A.left.Opens) : IsAffineOpen W →
    (∀ t ∈ Set.range (spMap a), ∃ x ∈ W, A.hom x = t) →
    ∃ V : ((Over.pullback (spMap a)).obj A).left.Opens, IsAffineOpen V ∧
      ∀ s : Sp R', ∃ x ∈ V, ((Over.pullback (spMap a)).obj A).hom x = s := by
  intro hW hfib
  haveI : IsAffineHom (pullback.fst A.hom (spMap a)) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  refine ⟨(pullback.fst A.hom (spMap a)) ⁻¹ᵁ W, hW.preimage _, ?_⟩
  intro s
  obtain ⟨x, hxW, hx⟩ := hfib (spMap a s) ⟨s, rfl⟩
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := A.hom) (g := spMap a) x s hx
  exact ⟨z, by show (pullback.fst A.hom (spMap a)) z ∈ W; rw [hz1]; exact hxW, hz2⟩

end GlobalTheory
end
