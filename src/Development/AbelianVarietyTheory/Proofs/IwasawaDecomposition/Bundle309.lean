module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle295
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Henselian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle256
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Formalism.TameInertiaTowers.CentralOrderTwo.OddEqOneOfSubOneMem
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle300
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle299
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
namespace GlobalTheory.CycLayers

theorem layer_of_clauses {F : Type*} [NormedField F] (A R : Subring F) (h : A ≤ R) (l m : ℕ)
    (hlnorm : ‖(l : F)‖ < 1) (hl0 : (l : F) ≠ 0) (hm : 0 < m)
    (hdiv : ∀ x ∈ R, ∀ y ∈ R, ‖x‖ ≤ ‖y‖ → x / y ∈ R)
    (T : Finset F) (hT : ∀ x, x ∈ R ↔ x ∈ Submodule.span A (T : Set F))
    (ζ : F) (hzmem : ζ ∈ R) (hζ : IsPrimitiveRoot ζ m)
    (hlast : ∀ x ∈ R, ∃ (p : Polynomial A) (d : A), d ≠ 0 ∧ x * (d : F) = Polynomial.aeval ζ p) :
    letI := (Subring.inclusion h).toAlgebra;
    Module.Finite A R ∧ ∃ z : Rˣ, IsPrimitiveRoot (z : R) m ∧ ∀ x : FractionRing R, ∃ p : Polynomial A, ∃ d : A, d ≠ 0 ∧
      x * algebraMap _ (FractionRing R) (algebraMap _ R d) = algebraMap _ (FractionRing R) (Polynomial.aeval (z : R) p) := by
  let _ := (Subring.inclusion h).toAlgebra
  refine ⟨?_, ?_⟩
  · let f : R →ₗ[A] F :=
      { toFun := Subtype.val, map_add' := fun _ _ => rfl,
        map_smul' := fun a y => by rw [RingHom.id_apply, Algebra.smul_def, Subring.smul_def]; rfl }
    let S : Set R := Subtype.val ⁻¹' (T : Set F)
    have hS : S.Finite := T.finite_toSet.preimage Subtype.val_injective.injOn
    have himg : f '' S = (T : Set F) := by
      ext c
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hc
        have hcR : c ∈ R := (hT c).2 (Submodule.subset_span hc)
        exact ⟨⟨c, hcR⟩, hc, rfl⟩
    have key : ∀ y : R, y ∈ Submodule.span A S := by
      intro y
      have h1 : (y : F) ∈ Submodule.span A (T : Set F) := (hT y).1 y.2
      rw [← himg, ← Submodule.map_span] at h1
      obtain ⟨y', hy', hyy⟩ := h1
      have : y' = y := Subtype.ext hyy
      rw [← this]; exact hy'
    exact ⟨⟨hS.toFinset, by rw [Set.Finite.coe_toFinset]; exact eq_top_iff.2 fun y _ => key y⟩⟩
  · have hprim : IsPrimitiveRoot (⟨ζ, hzmem⟩ : R) m :=
      IsPrimitiveRoot.coe_submonoidClass_iff.1 hζ
    refine ⟨(hprim.isUnit hm.ne').unit, by simpa using hprim, ?_⟩
    intro x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
    set b : R := (s : R) with hbdef
    have hb : b ∈ nonZeroDivisors R := s.2
    have hb0 : (b : F) ≠ 0 := by
      intro h0
      have : b = 0 := Subtype.ext h0
      exact nonZeroDivisors.ne_zero hb this
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hb0) hlnorm
    have hlR : (l : F) ^ N ∈ R := pow_mem (natCast_mem R l) N
    have hlNA : (l : F) ^ N ∈ A := pow_mem (natCast_mem A l) N
    have hq : (l : F) ^ N / b ∈ R := by
      refine hdiv _ hlR _ b.2 ?_
      rw [norm_pow]; exact hN.le
    obtain ⟨p, d', hd', hpd⟩ := hlast _ (mul_mem a.2 hq)
    refine ⟨p, ⟨(l : F) ^ N, hlNA⟩ * d', ?_, ?_⟩
    · refine mul_ne_zero ?_ hd'
      intro h0
      have h1 : (l : F) ^ N = 0 := congrArg Subtype.val h0
      exact pow_ne_zero N hl0 h1
    · have hev : ((Polynomial.aeval ((hprim.isUnit hm.ne').unit : R) p : R) : F) = Polynomial.aeval ζ p := by
        rw [Polynomial.aeval_def, Polynomial.aeval_def, IsUnit.unit_spec]
        rw [show ((Polynomial.eval₂ (algebraMap A R) (⟨ζ, hzmem⟩ : R) p : R) : F) =
          R.subtype (Polynomial.eval₂ (algebraMap A R) (⟨ζ, hzmem⟩ : R) p) from rfl, Polynomial.hom_eval₂]
        rfl
      have hRd : algebraMap A R (⟨(l : F) ^ N, hlNA⟩ * d') =
          b * ⟨(l : F) ^ N / b, hq⟩ * algebraMap A R d' := by
        rw [map_mul]; congr 1
        apply Subtype.ext
        show (l : F) ^ N = (b : F) * ((l : F) ^ N / b)
        field_simp
      have hfin : a * ⟨(l : F) ^ N / b, hq⟩ * algebraMap A R d' =
          Polynomial.aeval ((hprim.isUnit hm.ne').unit : R) p := by
        apply Subtype.ext
        rw [hev, ← hpd]
        rfl
      rw [hRd, ← hfin, map_mul, map_mul, map_mul, map_mul, ← mul_assoc, ← mul_assoc, IsLocalization.mk'_spec]

theorem finite_primitive_root :
    ∀ (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) (k : ℕ) (h : clC l (Kt l K₀ L) ≤ clC l (Kt l K₀ L ⊔ muK l k)), letI := (Subring.inclusion h).toAlgebra; Module.Finite ↥(clC l (Kt l K₀ L)) ↥(clC l (Kt l K₀ L ⊔ muK l k)) ∧ ∃ z : (↥(clC l (Kt l K₀ L ⊔ muK l k)))ˣ, IsPrimitiveRoot (z : ↥(clC l (Kt l K₀ L ⊔ muK l k))) (l ^ k) ∧ ∀ x : FractionRing ↥(clC l (Kt l K₀ L ⊔ muK l k)), ∃ p : Polynomial ↥(clC l (Kt l K₀ L)), ∃ d : ↥(clC l (Kt l K₀ L)), d ≠ 0 ∧ x * algebraMap _ (FractionRing ↥(clC l (Kt l K₀ L ⊔ muK l k))) (algebraMap _ ↥(clC l (Kt l K₀ L ⊔ muK l k)) d) = algebraMap _ (FractionRing ↥(clC l (Kt l K₀ L ⊔ muK l k))) (Polynomial.aeval (z : ↥(clC l (Kt l K₀ L ⊔ muK l k))) p) := by
  intro l _ K₀ L k h
  obtain ⟨-, -, -, -, hdiv, -, ⟨T, hT⟩, ζ, hzmem, hζ, hlast⟩ := GlobalTheory.T.exists_cyclotomic_unramified_completed_integers l K₀ L k
  have hlnorm : ‖(l : ℂ_[l])‖ < 1 := by
    have e : ((l : ℚ_[l]) : ℂ_[l]) = (l : ℂ_[l]) := by simp
    rw [← e, PadicComplex.norm_extends' l (l : ℚ_[l]), Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hl0 : (l : ℂ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  exact layer_of_clauses _ _ h l (l ^ k) hlnorm hl0 (pow_pos (Fact.out : l.Prime).pos k) hdiv T hT ζ hzmem hζ hlast

end GlobalTheory.CycLayers
end

section

open AlgebraicGeometry CategoryTheory Limits MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionRep

theorem exists_finite_free_rep (O : Type) [CommRing O] [HenselianLocalRing O] {Y : Scheme.{0}} (f : Y ⟶ Sp O)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] [Flat f] :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (j : Sp A ⟶ Y), Module.Finite O A ∧ Module.Free O A ∧
      j ≫ f = spMap (algebraMap O A) ∧ ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B]
        (h : Sp B ⟶ Y), h ≫ f = spMap (algebraMap O B) → ∃! φ : A →ₐ[O] B, spMap (φ : A →+* B) ≫ j = h := by
  have : HenselianLocalRing (CommRingCat.of O) := ‹_›
  have hfin : IsFinite ((finitePart f).ι ≫ f) := isFinite_finitePart f
  have : IsAffine (finitePart f).toScheme := isAffine_of_isAffineHom ((finitePart f).ι ≫ f)
  let A : CommRingCat.{0} := Γ((finitePart f).toScheme, ⊤)
  let i : Spec A ≅ (finitePart f).toScheme := (finitePart f).toScheme.isoSpec.symm
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (i.hom ≫ (finitePart f).ι ≫ f)
  have h₁ : ψ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hψ]
    infer_instance
  have h₂ : ψ.hom.Flat := by
    rw [← HasRingHomProperty.Spec_iff (P := @Flat), hψ]
    infer_instance
  let _ : Algebra O A := ψ.hom.toAlgebra
  have h₃ : Module.Finite O A := h₁
  have h₄ : Module.Flat O A := h₂
  have hj : (i.hom ≫ (finitePart f).ι) ≫ f = spMap (algebraMap O A) := by
    rw [Category.assoc, ← hψ]; rfl
  refine ⟨A, inferInstance, inferInstance, i.hom ≫ (finitePart f).ι, h₃,
    Module.free_of_flat_of_isLocalRing, hj, fun B _ _ _ h hh => ?_⟩
  have : IsFinite (spMap (algebraMap O B)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 ‹_›)
  obtain ⟨l, hl, -⟩ := existsUnique_lift_finitePart f _ h hh
  obtain ⟨χ, hχ⟩ := Spec.map_surjective (R := A) (S := .of B) (l ≫ i.inv)
  have hχ' : Spec.map χ ≫ i.hom ≫ (finitePart f).ι = h := by
    rw [hχ, Category.assoc, i.inv_hom_id_assoc, hl]
  have hc : CommRingCat.ofHom (algebraMap O A) ≫ χ = CommRingCat.ofHom (algebraMap O B) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    refine Eq.trans ?_ hh
    rw [← hχ', Category.assoc, hj]
  refine ⟨⟨χ.hom, fun r => congr(($hc).hom r)⟩, hχ', fun φ hφ => ?_⟩
  have h₅ : spMap (φ : A →+* B) = Spec.map χ := by
    rw [← cancel_mono (i.hom ≫ (finitePart f).ι)]
    exact hφ.trans hχ'.symm
  have h₆ := Spec.map_injective h₅
  exact AlgHom.ext fun a => congr(($h₆).hom a)

theorem exists_finite_free_torsion_rep : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (O : Type) [CommRing O] [HenselianLocalRing O] (x : Sp O ⟶ X) (q : ℕ), q ≠ 0 → ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (u : overAt x A ⟶ G), Module.Finite O A ∧ Module.Free O A ∧ u ^ q = 1 ∧ ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B] (g : overAt x B ⟶ G), g ^ q = 1 → ∃! φ : A →ₐ[O] B, homAt x φ ≫ u = g := by
  intro X G _ _ hG O _ _ x q hq
  obtain ⟨hf, hqf⟩ := GlobalTheory.T.pow_flat_locallyQuasiFinite X G hG q hq
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  let m : G ⟶ G := (𝟙 G) ^ q
  have hm : ∀ {T : Over X} (g : T ⟶ G), g ≫ m = g ^ q := fun g => by
    rw [MonObj.comp_pow, Category.comp_id]
  have : Flat m.left := hf
  have : LocallyQuasiFinite m.left := hqf
  have : LocallyOfFiniteType (m.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType m.left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact (m.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact m.left := QuasiCompact.of_comp _ G.hom
  have : IsSeparated (m.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : IsSeparated m.left := IsSeparated.of_comp _ G.hom
  let e : Sp O ⟶ G.left := (1 : Over.mk x ⟶ G).left
  have he : e ≫ G.hom = x := Over.w (1 : Over.mk x ⟶ G)
  have h1 : ∀ (B : Type) [CommRing B] [Algebra O B],
      (1 : overAt x B ⟶ G).left = spMap (algebraMap O B) ≫ e := fun B _ _ => by
    let t : overAt x B ⟶ Over.mk x := Over.homMk (spMap (algebraMap O B)) rfl
    rw [← MonObj.comp_one t]
    rfl
  have : LocallyQuasiFinite (pullback.snd m.left e) :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (IsPullback.of_hasPullback m.left e) hqf
  obtain ⟨A, _, _, j, hA₁, hA₂, hj, H⟩ := exists_finite_free_rep O (pullback.snd m.left e)
  have hu : (j ≫ pullback.fst m.left e) ≫ m.left = spMap (algebraMap O A) ≫ e := by
    rw [Category.assoc, pullback.condition, reassoc_of% hj]
  let u : overAt x A ⟶ G := Over.homMk (j ≫ pullback.fst m.left e) (by
    rw [← Over.w m, ← Category.assoc]
    exact (congrArg (· ≫ G.hom) hu).trans (by rw [Category.assoc, he]; rfl))
  refine ⟨A, inferInstance, inferInstance, u, hA₁, hA₂, ?_, fun B _ _ _ g hg => ?_⟩
  · rw [← hm]
    exact Over.OverMorphism.ext (hu.trans (h1 A).symm)
  have hg' : g.left ≫ m.left = spMap (algebraMap O B) ≫ e := by
    rw [← Over.comp_left, hm, hg, h1]
  obtain ⟨φ, hφ, hφ'⟩ := H B (pullback.lift g.left (spMap (algebraMap O B)) hg') (pullback.lift_snd _ _ _)
  refine ⟨φ, Over.OverMorphism.ext ?_, fun φ' h' => hφ' φ' ?_⟩
  · change spMap (φ : A →+* B) ≫ j ≫ pullback.fst m.left e = g.left
    rw [← Category.assoc, hφ]
    exact pullback.lift_fst _ _ _
  · apply pullback.hom_ext
    · rw [Category.assoc]
      exact (congrArg CommaMorphism.left h').trans (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, hj]
      refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, φ'.comp_algebraMap]

end GlobalTheory.TorsionRep
end

section

noncomputable section

namespace GlobalTheory.MemN.HalfPlaces

open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.Mem.GaloisStage
open scoped Pointwise

theorem exists_transversal_cover {S : Type} [Fintype S] (c : S → S) (hc : ∀ x, c (c x) = x)
    (hne : ∀ x, c x ≠ x) {n : ℕ} (hn : Fintype.card S = 2 * n) :
    ∃ e : Fin n → S, Function.Injective e ∧ (∀ i j, c (e i) ≠ e j) ∧ ∀ x, ∃ i, x = e i ∨ x = c (e i) := by
  classical
  obtain ⟨e, he, he'⟩ := exists_transversal c hc hne hn
  refine ⟨e, he, he', fun x => ?_⟩
  have hinj : Function.Injective (Sum.elim e (fun i => c (e i)) : Fin n ⊕ Fin n → S) := by
    rintro (i | i) (j | j) h
    · exact congrArg _ (he h)
    · exact absurd h.symm (he' j i)
    · exact absurd h (he' i j)
    · have h' : c (e i) = c (e j) := h
      have : e i = e j := by rw [← hc (e i), h', hc]
      exact congrArg _ (he this)
  have hbij := (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, by simp [hn, two_mul]⟩
  obtain ⟨i | i, h⟩ := hbij.2 x
  · exact ⟨i, Or.inl h.symm⟩
  · exact ⟨i, Or.inr h.symm⟩

variable {R : Ranks}

theorem isConjPl_iff (H : Host R) (w w' : PlE H) :
    IsConjPl H w w' ↔ H.conj • w.asIdeal = w'.asIdeal := by
  constructor
  · intro h
    ext y
    have := h (H.conj⁻¹ • y) y (by rw [← Formalism.TwoAdicCyclotomicDecomposition.odd_coe_smul, smul_inv_smul])
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    exact this
  · intro h x y hxy
    have hy : y = H.conj • x := by
      apply Subtype.ext
      exact hxy
    rw [← h, hy, Ideal.smul_mem_pointwise_smul_iff]

theorem exists_places_cover (H : Host R) {p : ℕ} (hp : p.Prime)
    (hs : (placesOver H.E p).ncard = Module.finrank ℚ H.E) :
    ∃ e : Fin R.f → PlE H, (∀ i, e i ∈ placesOver H.E p) ∧ Function.Injective e ∧
      (∀ i j, ¬ IsConjPl H (e i) (e j)) ∧ ∀ w ∈ placesOver H.E p, ∃ v, w = e v ∨ IsConjPl H (e v) w := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hG : IsGalois ℚ H.E := H.galois
  have := Formalism.FrobeniusOrbits.SplitK.span_prime p
  have : IsGaloisGroup (H.E ≃ₐ[ℚ] H.E) ℤ (𝓞 H.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ H.E
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  obtain ⟨⟨P, hP1, hP2⟩⟩ := (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 H.E)))
  have hr : Set.range (fun σ : H.E ≃ₐ[ℚ] H.E => σ • P) = Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 H.E) := by
    ext Q
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨inferInstance, inferInstance⟩
    · rintro ⟨hQ1, hQ2⟩
      exact Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (H.E ≃ₐ[ℚ] H.E)
  have hinj : Function.Injective (fun σ : H.E ≃ₐ[ℚ] H.E => σ • P) := by
    rw [GlobalTheory.HostSplit.ncard_placesOver H.E hp, ← hr, ← IsGalois.card_aut_eq_finrank, ← Set.image_univ,
      ← Set.ncard_univ] at hs
    exact Set.injOn_univ.1 (Set.injOn_of_ncard_image_eq hs)
  have hcard : Fintype.card (H.E ≃ₐ[ℚ] H.E) = 2 * R.f := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      H.finrank_cmField, Ranks.f, Ranks.n]
    ring
  obtain ⟨e, he, he', hcov⟩ := exists_transversal_cover (fun σ => H.conj * σ)
    (fun σ => by rw [← mul_assoc, conj_mul_conj, one_mul])
    (fun σ h => conj_ne_one H (mul_eq_right.1 h)) hcard
  refine ⟨fun i => ⟨e i • P, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 _⟩, fun i => ?_,
    fun i j h => he (hinj (congrArg HeightOneSpectrum.asIdeal h)), fun i j h => he' i j (hinj ?_),
    fun w hw => ?_⟩
  · have h3 : (p : ℤ) ∈ (e i • P).under ℤ := by
      rw [← Ideal.over_def (e i • P) (Ideal.span {(p : ℤ)})]
      exact Ideal.mem_span_singleton_self _
    have h4 : algebraMap ℤ (𝓞 H.E) ((p : ℕ) : ℤ) ∈ e i • P := h3
    rw [map_natCast] at h4
    exact h4
  · show (H.conj * e i) • P = e j • P
    rw [mul_smul]
    have h' := (isConjPl_iff H _ _).1 h
    dsimp only at h'
    exact h'
  · have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    have hwp := w.isPrime
    have hw' : w.asIdeal ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 H.E) := by
      refine ⟨hwp, ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩⟩
      rw [Ideal.span_singleton_le_iff_mem]
      show algebraMap ℤ (𝓞 H.E) ((p : ℕ) : ℤ) ∈ w.asIdeal
      rw [map_natCast]
      exact hw
    rw [← hr] at hw'
    obtain ⟨σ, hσ⟩ := hw'
    have hσ' : σ • P = w.asIdeal := hσ
    obtain ⟨i, h | h⟩ := hcov σ
    · exact ⟨i, Or.inl (HeightOneSpectrum.ext (by rw [← hσ', h]))⟩
    · refine ⟨i, Or.inr ?_⟩
      rw [isConjPl_iff]
      dsimp only
      rw [← hσ', h, mul_smul]

end GlobalTheory.MemN.HalfPlaces

end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem _root_.GlobalTheory.T.exists_multilinearMap_of_commuting_endAlgHom : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Wv : ι → Type) [∀ v, AddCommGroup (Wv v)] [∀ v, Module ℂ (Wv v)] (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : ∀ v, Module.End ℂ (Wv v) →ₐ[ℂ] Module.End ℂ V) (w : ∀ v, Wv v) (ℓ : ∀ v, Module.Dual ℂ (Wv v)) (y : V), (∀ u v, u ≠ v → ∀ A B, Commute (Φ u A) (Φ v B)) → (∀ v, Φ v ((ℓ v).smulRight (w v)) y = y) → ∃ F : (∀ v, Wv v) →ₘₗ[ℂ] V, F w = y ∧ ∀ v (A : Module.End ℂ (Wv v)) (x : ∀ u, Wv u), Φ v A (F x) = F (Function.update x v (A (x v))) := by
  exact @GlobalTheory.exists_multilinear_of_commuting_endAlgHom
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem _root_.GlobalTheory.T.exists_ne_zero_fixed_by_commuting_rankOne_images : ∀ (ι : Type) [Fintype ι] (Wv : ι → Type) [∀ v, AddCommGroup (Wv v)] [∀ v, Module ℂ (Wv v)] [∀ v, FiniteDimensional ℂ (Wv v)] (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : ∀ v, Module.End ℂ (Wv v) →ₐ[ℂ] Module.End ℂ V) (w : ∀ v, Wv v) (ℓ : ∀ v, Module.Dual ℂ (Wv v)), Nontrivial V → (∀ v, ℓ v (w v) = 1) → (∀ u v, u ≠ v → ∀ A B, Commute (Φ u A) (Φ v B)) → ∃ y : V, y ≠ 0 ∧ ∀ v, Φ v ((ℓ v).smulRight (w v)) y = y := by
  first | exact @GlobalTheory.commuting_endAlgebras_common_fixed_vector | exact GlobalTheory.commuting_endAlgebras_common_fixed_vector | (intros; apply GlobalTheory.commuting_endAlgebras_common_fixed_vector <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem _root_.GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor : ∀ (G H V W W' : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G V) (s : H →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H W'), ρ.IsIrreducible → σ.IsIrreducible → σ'.IsIrreducible → (∀ g, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y)) → ∀ f : σ.IntertwiningMap (ρ.comp s), f ≠ 0 → (⨆ f : σ.IntertwiningMap (ρ.comp s), LinearMap.range f.toLinearMap) = ⊤ ∧ ∀ f' : σ'.IntertwiningMap (ρ.comp s), f' ≠ 0 → Nonempty (σ.Equiv σ') := by
  first | exact @GlobalTheory.CuspRep.CompUniq.isotypic | exact GlobalTheory.CuspRep.CompUniq.isotypic | (intros; apply GlobalTheory.CuspRep.CompUniq.isotypic <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem _root_.GlobalTheory.T.exists_algHom_endomorphism_of_span_intertwiners : ∀ (H W V : Type) [Group H] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ H W) (ρ : Representation ℂ H V), σ.IsIrreducible → (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) = ⊤ → ∃ Φ : Module.End ℂ W →ₐ[ℂ] Module.End ℂ V, (∀ h, Φ (σ h) = ρ h) ∧ ∀ T : Module.End ℂ V, (∀ h, Commute T (ρ h)) → ∀ A, Commute T (Φ A) := by
  first | exact @GlobalTheory.FinPart.exists_algHom_end_of_span_intertwiners | exact GlobalTheory.FinPart.exists_algHom_end_of_span_intertwiners | (intros; apply GlobalTheory.FinPart.exists_algHom_end_of_span_intertwiners <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnifMap

theorem unif_to_unif : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 F))
    (w : HeightOneSpectrum (𝓞 E)) (i : v.adicCompletion F ≃+* w.adicCompletion E), Continuous i →
    ∀ ϖ : v.adicCompletion F, Valued.v ϖ = WithZero.exp (-1 : ℤ) → Valued.v (i ϖ) = WithZero.exp (-1 : ℤ) := by
  intro F E _ _ _ _ v w i hi ϖ hϖ
  have hle := GlobalTheory.T.valued_le_one_iff_of_continuous_ringEquiv F E v w i hi
  have key : ∀ x : WithZero (Multiplicative ℤ), x ≠ 0 → x < 1 → x ≤ WithZero.exp (-1 : ℤ) := by
    intro x hx h1
    rw [← WithZero.exp_log hx] at h1 ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    rw [WithZero.exp_le_exp]; omega
  have hlt : ∀ y, Valued.v (i y) < 1 ↔ Valued.v y < 1 := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · have hiy : i y ≠ 0 := by simpa using hy
      have e1 := (Valued.v (R := w.adicCompletion E)).one_lt_val_iff (inv_ne_zero hiy)
      have e2 := (Valued.v (R := v.adicCompletion F)).one_lt_val_iff (inv_ne_zero hy)
      rw [inv_inv] at e1 e2
      rw [← e1, ← e2, ← not_le, ← not_le, ← map_inv₀ i, hle]
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hiϖ0 : i ϖ ≠ 0 := by simpa using hϖ0
  have hϖ1 : Valued.v ϖ < 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hup : Valued.v (i ϖ) < 1 := (hlt ϖ).2 hϖ1
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer E w
  set z : w.adicCompletion E := (π : w.adicCompletion E)
  have hz : Valued.v z = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hπ
  set y := i.symm z
  have hy1 : Valued.v y < 1 := by
    rw [← hlt, RingEquiv.apply_symm_apply, hz, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy1
    have : z = 0 := by simpa [y] using h
    rw [this, map_zero] at hz; exact WithZero.exp_ne_zero hz.symm
  have hdiv : Valued.v (y / ϖ) ≤ 1 := by
    rw [map_div₀, hϖ, div_le_one₀ (by simp)]
    exact key _ (by simpa using hy0) hy1
  have h2 := (hle _).2 hdiv
  rw [map_div₀, map_div₀, RingEquiv.apply_symm_apply, hz] at h2
  have hlow : WithZero.exp (-1 : ℤ) ≤ Valued.v (i ϖ) := by
    rwa [div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hiϖ0))] at h2
  exact le_antisymm (key _ (by simpa using hiϖ0) hup) hlow

end GlobalTheory.UnifMap
end
