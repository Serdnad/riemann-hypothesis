module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle410
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHkIsogEtaleUnique
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle060
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle090
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle432
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle019

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem isAbelianScheme_fib {K : Type} [CommRing K] (x : Sp K ⟶ Xo.X) : IsAbelianScheme (Fib Xo x) :=
  have hA := GlobalTheory.HeckePoint.isAbelianScheme_of_proper Xo.univ.t Xo.univ.proper
  { comm := by have := hA.comm; infer_instance
    smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
    proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
    geomConnected := by have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }

theorem exists_fibPtsEquiv {K : Type} [Field K] (x : Sp K ⟶ Xo.X) :
    ∃ ρ : (𝟙_ (Over (Sp K)) ⟶ Fib Xo x) ≃* (Over.mk x ⟶ Xo.univ.t.G),
      (∀ u, fibPt _ (ρ u) = u.left) ∧
      ∀ (g : Xo.univ.t.G ⟶ Xo.univ.t.G) u, ρ (u ≫ (Over.pullback x).map g) = ρ u ≫ g := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.HeckePoint.exists_ptsEquiv (isGrpPullback_pullback Xo.univ.t.G x) (𝟙_ (Over (Sp K))) x
    (Category.id_comp _)
  refine ⟨ρ, fun u => ?_, fun g u => Over.OverMorphism.ext ?_⟩
  · apply pullback.hom_ext
    · rw [fibPt, pullback.lift_fst, hρ]
    · rw [fibPt, pullback.lift_snd]
      exact (Over.w u).symm
  · have A : ((Over.pullback x).map g).left ≫ pullback.fst _ x = pullback.fst _ x ≫ g.left :=
      pullback.lift_fst _ _ _
    rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, Category.assoc]
    exact congrArg (u.left ≫ ·) A

theorem exists_hkWith_of_hkRelFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) (C : hkKer (Xo := Xo) P p i Ω y) (z : FrPt Xo c Ω), hkRelFr P p i (hkTr Xo c p) Ω y C z → ∃ f f', HkWith p y z f f' := by
  intro E _ _ _ H Dw l Xo c P p i ⟨hP, hco, hp, hpP, hpM⟩ Ω _ _ _ y C z ⟨ψ, ψp, h, hLie, hTr⟩
  obtain ⟨⟨hfin, het, hsur⟩, -⟩ := GlobalTheory.HeckePointLaw.isHkIsog_etale_unique Xo hP hco hp hpP hpM C.2 h
  obtain ⟨-, h0, hf, hact, -, hker, -⟩ := h
  have hL : Out.Laws := abelianSchemeLaws_all.1
  have hA := isAbelianScheme_fib y.x
  have hB := isAbelianScheme_fib z.x
  have := hA.proper
  have := hB.proper
  have := hA.comm
  obtain ⟨ρ, e₁, e₂⟩ := exists_fibPtsEquiv y.x
  obtain ⟨σ, s₁, s₂⟩ := exists_fibPtsEquiv z.x
  let f : Fib Xo y.x ⟶ Fib Xo z.x := Over.homMk ψ h0
  have hψ : ∀ u, σ (u ≫ f) = ψp (ρ u) := fun u => GlobalTheory.HeckePoint.fibPt_injective _ (by
    rw [s₁, ← hf, e₁]; rfl)
  have one : ∀ (G : Over (Sp Ω)) [GrpObj G], (1 : 𝟙_ (Over (Sp Ω)) ⟶ G) = η[G] := fun G _ => by
    rw [Hom.one_def]; simp
  have hom : IsMonHom f := hL.rigidity _ _ _ hA hB f (by
    rw [← one, ← one]
    exact σ.injective (by rw [hψ, map_one, map_one, map_one]))
  have lin : Lin f := fun a => GlobalTheory.HeckePoint.hom_ext_pts hA.smooth fun u => σ.injective (by
    rw [← Category.assoc, ← Category.assoc, hψ, s₂, hψ, e₂, hact])
  have hkill : ∀ u : 𝟙_ (Over (Sp Ω)) ⟶ Fib Xo y.x, u ≫ f = 1 → u ^ p ^ 2 = 1 := fun u hu => by
    have hx : ρ u ∈ C.1 := by rw [← hker, MonoidHom.mem_ker, ← hψ, hu, map_one]
    refine ρ.injective ?_
    rw [map_pow, map_one]
    refine (GlobalTheory.HeckeKerModel.mem_tors_span Xo.univ.t _ (p ^ 2)).1 fun a ha => C.2.2.2.1 hx a ?_
    refine (Ideal.span_singleton_le_iff_mem _).2 ?_ ha
    rw [sq, Nat.cast_mul]
    refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpP
    rwa [map_natCast] at this
  have hpow : ∀ m : ℕ, IsMonHom (𝟙 (Fib Xo y.x) ^ m) := fun m => by
    induction m with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit _ ≫ η[Fib Xo y.x]))
    | succ m ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 (Fib Xo y.x) ^ m) (𝟙 _) ≫ μ[Fib Xo y.x]))
  have := hpow (p ^ 2)
  have : IsFinite f.left := hfin
  have : Etale f.left := het
  have : Surjective f.left := hsur
  obtain ⟨π, hπ⟩ := GlobalTheory.HeckePoint.exists_fac hA.smooth f (𝟙 (Fib Xo y.x) ^ p ^ 2) fun u hu => by
    rw [MonObj.comp_pow, Category.comp_id, hkill u hu]
  have homπ : IsMonHom π := hL.rigidity _ _ _ hB hA π (by
    rw [← IsMonHom.one_hom f, Category.assoc, hπ, IsMonHom.one_hom])
  have : Epi f.left := Flat.epi_of_flat_of_surjective _
  have : Epi f := Over.epi_of_epi_left f
  refine ⟨f, π, ⟨hom, homπ, hπ, ?_, lin, fun a => ?_⟩, hLie, hTr⟩
  · rw [← cancel_epi f, ← Category.assoc, hπ, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  · have := Xo.univ.t.act.hom a
    rw [← cancel_epi f, ← Category.assoc, ← lin a, Category.assoc, hπ, ← Category.assoc, hπ, MonObj.pow_comp,
      MonObj.comp_pow, Category.id_comp, Category.comp_id]

end GlobalTheory.HkIntegral
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

open GlobalTheory.Spread

theorem fibre_transition {G X : Scheme.{0}} (p : G ⟶ X) {K L : Type} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) (x : Sp K ⟶ X)
    (π : pullback p (spMap (algebraMap K L) ≫ x) ⟶ pullback p (spMap (algebraMap K M) ≫ x))
    (h₁ : π ≫ pullback.fst _ _ = pullback.fst _ _)
    (h₂ : π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap M.val.toRingHom) :
    (pullbackLeftPullbackSndIso p x (spMap (algebraMap K L))).hom ≫ π =
      bcMap (pullback.snd p x) M.val ≫ (pullbackLeftPullbackSndIso p x (spMap (algebraMap K M))).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, h₁, Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
      pullbackLeftPullbackSndIso_hom_fst, bcMap_fst_assoc]
  · rw [Category.assoc, h₂, Category.assoc, pullbackLeftPullbackSndIso_hom_snd,
      pullbackLeftPullbackSndIso_hom_snd_assoc, bcMap_snd]

theorem exists_descend_fibre {G X : Scheme.{0}} (p : G ⟶ X) [QuasiCompact p] [QuasiSeparated p]
    [LocallyOfFinitePresentation p] {K L : Type} [Field K] [Field L] [Algebra K L] (x x' : Sp K ⟶ X)
    (g : pullback p (spMap (algebraMap K L) ≫ x) ⟶ pullback p (spMap (algebraMap K L) ≫ x'))
    (hg : g ≫ pullback.snd _ _ = pullback.snd _ _) :
    ∃ s : Finset L, ∀ M : IntermediateField K L, (s : Set L) ⊆ M →
      ∃ f : pullback p (spMap (algebraMap K M) ≫ x) ⟶ pullback p (spMap (algebraMap K M) ≫ x'),
        f ≫ pullback.snd _ _ = pullback.snd _ _ ∧
        ∀ (π : pullback p (spMap (algebraMap K L) ≫ x) ⟶ pullback p (spMap (algebraMap K M) ≫ x))
          (π' : pullback p (spMap (algebraMap K L) ≫ x') ⟶ pullback p (spMap (algebraMap K M) ≫ x')),
          π ≫ pullback.fst _ _ = pullback.fst _ _ →
          π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap M.val.toRingHom →
          π' ≫ pullback.fst _ _ = pullback.fst _ _ →
          π' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap M.val.toRingHom →
          g ≫ π' = π ≫ f := by
  let A : Over (Sp K) := Over.mk (pullback.snd p x)
  let B : Over (Sp K) := Over.mk (pullback.snd p x')
  have : QuasiCompact A.hom := inferInstanceAs (QuasiCompact (pullback.snd p x))
  have : QuasiSeparated A.hom := inferInstanceAs (QuasiSeparated (pullback.snd p x))
  have : LocallyOfFinitePresentation B.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd p x'))
  let g₀ : pullback (pullback.snd p x) (spMap (algebraMap K L)) ⟶
      pullback (pullback.snd p x') (spMap (algebraMap K L)) :=
    (pullbackLeftPullbackSndIso p x (spMap (algebraMap K L))).hom ≫ g ≫
      (pullbackLeftPullbackSndIso p x' (spMap (algebraMap K L))).inv
  have hg₀ : g₀ ≫ pullback.snd _ _ = pullback.snd _ _ := by
    simp only [g₀, Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, hg, pullbackLeftPullbackSndIso_hom_snd]
  obtain ⟨s, hs⟩ := HomPairDescent.exists_descend (Ω := L) A B (Over.homMk g₀ hg₀)
  refine ⟨s, fun M hM => ?_⟩
  obtain ⟨f, hf⟩ := hs M hM
  let f₀ : pullback (pullback.snd p x) (spMap (algebraMap K M)) ⟶
      pullback (pullback.snd p x') (spMap (algebraMap K M)) := f.left
  have hf₀ : f₀ ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
  have hf₁ : bcMap (pullback.snd p x) M.val ≫ f₀ = g₀ ≫ bcMap (pullback.snd p x') M.val := hf
  refine ⟨(pullbackLeftPullbackSndIso p x (spMap (algebraMap K M))).inv ≫ f₀ ≫
      (pullbackLeftPullbackSndIso p x' (spMap (algebraMap K M))).hom, ?_, fun π π' h₁ h₂ h₃ h₄ => ?_⟩
  · simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, hf₀, pullbackLeftPullbackSndIso_hom_snd]
  · have e := fibre_transition p M x π h₁ h₂
    have e' := fibre_transition p M x' π' h₃ h₄
    rw [← cancel_epi (pullbackLeftPullbackSndIso p x (spMap (algebraMap K L))).hom, reassoc_of% e,
      Iso.hom_inv_id_assoc, reassoc_of% hf₁, ← e']
    simp only [g₀, Category.assoc, Iso.inv_hom_id_assoc]

theorem pair_defined_over_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (g : Fib Xo w ⟶ Fib Xo w') (g' : Fib Xo w' ⟶ Fib Xo w), φ.IsIntegral → w = spMap φ ≫ x → w' = spMap φ ≫ x' → IsMonHom g → IsMonHom g' → ∃ (M : Type) (_ : Field M) (i : K →+* M) (j : M →+* L), j.comp i = φ ∧ i.Finite ∧ ∀ v v' : Sp M ⟶ Xo.X, v = spMap i ≫ x → v' = spMap i ≫ x' → ∃ (f : Fib Xo v ⟶ Fib Xo v') (f' : Fib Xo v' ⟶ Fib Xo v), IsBC j f g ∧ IsBC j f' g' := by
  classical
  intro E _ _ _ H Dw l Xo K L _ _ φ x x' w w' g g' hφ hw hw' _ _
  let _ : Algebra K L := φ.toAlgebra
  have hint : Algebra.IsIntegral K L := ⟨hφ⟩
  subst hw hw'
  have hA := ObjDim.isAbelianScheme Xo.univ
  have := hA.proper
  have := hA.smooth
  obtain ⟨s, hs⟩ := exists_descend_fibre Xo.univ.t.G.hom (L := L) x x' g.left (Over.w g)
  obtain ⟨t, ht⟩ := exists_descend_fibre Xo.univ.t.G.hom (L := L) x' x g'.left (Over.w g')
  let M : IntermediateField K L := IntermediateField.adjoin K ((s ∪ t : Finset L) : Set L)
  have hM : ((s ∪ t : Finset L) : Set L) ⊆ M := IntermediateField.subset_adjoin _ _
  obtain ⟨f, hf, hf'⟩ := hs M ((Finset.coe_subset.2 Finset.subset_union_left).trans hM)
  obtain ⟨r, hr, hr'⟩ := ht M ((Finset.coe_subset.2 Finset.subset_union_right).trans hM)
  have hfin : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨M, inferInstance, algebraMap K M, M.val.toRingHom, RingHom.ext fun _ => rfl,
    RingHom.finite_algebraMap.2 hfin, ?_⟩
  rintro v v' rfl rfl
  have e : ∀ y : Sp K ⟶ Xo.X, spMap φ ≫ y = spMap M.val.toRingHom ≫ spMap (algebraMap K M) ≫ y := fun y => by
    rw [← Category.assoc, GlobalTheory.Spread.spMap_algHom_comp]
  exact ⟨Over.homMk f hf, Over.homMk r hr, ⟨e x, e x', hf'⟩, ⟨e x', e x, hr'⟩⟩

end GlobalTheory.HkIntegral
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral.PairBC

section General

variable {S S' : Scheme.{0}} {j : S' ⟶ S}

theorem exists_proj {X : Scheme.{0}} (G : Over X) [GrpObj G] (x : S ⟶ X) (w : S' ⟶ X) (h : w = j ≫ x) :
    ∃ π : pullback G.hom w ⟶ pullback G.hom x, π ≫ pullback.fst _ _ = pullback.fst _ _ ∧
      π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ j ∧
      IsGrpPullback ((Over.pullback w).obj G) ((Over.pullback x).obj G) j π := by
  have e : pullback.fst G.hom w ≫ G.hom = (pullback.snd _ _ ≫ j) ≫ x := by
    rw [Category.assoc, ← h, pullback.condition]
  exact ⟨pullback.lift _ _ e, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, (isGrpPullback_pullback G _).cancel
    ((isGrpPullback_pullback G _).congr h (pullback.lift_fst _ _ e).symm) (pullback.lift_snd _ _ _)⟩

theorem id_pow_left {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {π : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G j π) (N : ℕ) : (𝟙 G' ^ N).left ≫ π = π ≫ (𝟙 G ^ N).left := by
  let U : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk π h.1.w
  have e : pushHom h G' (𝟙 G') = U := Over.OverMorphism.ext (Category.id_comp π)
  have e' : pushHom h G' (𝟙 G' ^ N) = U ≫ 𝟙 G ^ N := by
    rw [map_pow, e, MonObj.comp_pow, Category.comp_id]
  exact congrArg (fun u => u.left) e'

theorem eq_iff [Flat j] [Surjective j] {A B : Over S} {A' B' : Over S'} {α : A'.left ⟶ A.left}
    {β : B'.left ⟶ B.left} (hα : IsPullback α A'.hom A.hom j) (hβ : IsPullback β B'.hom B.hom j)
    {u v : A ⟶ B} {u' v' : A' ⟶ B'} (hu : u'.left ≫ β = α ≫ u.left) (hv : v'.left ≫ β = α ≫ v.left) :
    u = v ↔ u' = v' := by
  have : Flat α := MorphismProperty.of_isPullback (P := @Flat) hα.flip ‹_›
  have : Surjective α := MorphismProperty.of_isPullback (P := @Surjective) hα.flip ‹_›
  have : Epi α := Flat.epi_of_flat_of_surjective α
  constructor
  · rintro rfl
    exact Over.OverMorphism.ext (hβ.hom_ext (hu.trans hv.symm) (by rw [Over.w, Over.w]))
  · rintro rfl
    exact Over.OverMorphism.ext ((cancel_epi α).1 (hu.symm.trans hv))

theorem comp_sq {A B C : Over S} {A' B' C' : Over S'} {α : A'.left ⟶ A.left} {β : B'.left ⟶ B.left}
    {δ : C'.left ⟶ C.left} {u : A ⟶ B} {v : B ⟶ C} {u' : A' ⟶ B'} {v' : B' ⟶ C'}
    (hu : u'.left ≫ β = α ≫ u.left) (hv : v'.left ≫ δ = β ≫ v.left) :
    (u' ≫ v').left ≫ δ = α ≫ (u ≫ v).left := by
  rw [Over.comp_left, Over.comp_left, Category.assoc, hv, reassoc_of% hu]

theorem map_sq {X : Scheme.{0}} {G : Over X} {x : S ⟶ X} {w : S' ⟶ X} (π : pullback G.hom w ⟶ pullback G.hom x)
    (h₁ : π ≫ pullback.fst _ _ = pullback.fst _ _) (h₂ : π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ j) (a : G ⟶ G) :
    ((Over.pullback w).map a).left ≫ π = π ≫ ((Over.pullback x).map a).left := by
  apply pullback.hom_ext <;>
    simp [h₁, h₂, reassoc_of% h₁, pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc]

end General

theorem exists_isBC_and_isPair_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X), (w = spMap φ ≫ x → w' = spMap φ ≫ x' → ∀ f : Fib Xo x ⟶ Fib Xo x', ∃ g : Fib Xo w ⟶ Fib Xo w', IsBC φ f g) ∧ ∀ (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (g : Fib Xo w ⟶ Fib Xo w') (g' : Fib Xo w' ⟶ Fib Xo w) (N : ℕ), IsBC φ f g → IsBC φ f' g' → (IsPair N f f' ↔ IsPair N g g') := by
  intro E _ _ _ H Dw l Xo K L _ _ φ x x' w w'
  refine ⟨fun hw hw' f => ?_, fun f f' g g' N hf hf' => ?_⟩
  · obtain ⟨π, p₁, p₂, hπ⟩ := exists_proj Xo.univ.t.G x w hw
    obtain ⟨π', p₁', p₂', hπ'⟩ := exists_proj Xo.univ.t.G x' w' hw'
    have e : (π ≫ f.left) ≫ (Fib Xo x').hom = (Fib Xo w).hom ≫ spMap φ :=
      (Category.assoc _ _ _).trans ((congrArg (π ≫ ·) (Over.w f)).trans hπ.1.w)
    refine ⟨Over.homMk (hπ'.1.lift _ _ e) (hπ'.1.lift_snd _ _ e), hw, hw', fun ρ ρ' q₁ q₂ q₁' q₂' => ?_⟩
    obtain rfl : ρ = π := pullback.hom_ext (q₁.trans p₁.symm) (q₂.trans p₂.symm)
    obtain rfl : ρ' = π' := pullback.hom_ext (q₁'.trans p₁'.symm) (q₂'.trans p₂'.symm)
    exact hπ'.1.lift_fst _ _ e
  · have := FieldBaseChange.flat_spMap φ
    have := FieldBaseChange.surjective_spMap φ
    obtain ⟨π, p₁, p₂, hπ⟩ := exists_proj Xo.univ.t.G x w hf.1
    obtain ⟨π', p₁', p₂', hπ'⟩ := exists_proj Xo.univ.t.G x' w' hf.2.1
    have e := hf.2.2 π π' p₁ p₂ p₁' p₂'
    have e' := hf'.2.2 π' π p₁' p₂' p₁ p₂
    refine and_congr (FieldBaseChange.isMonHom_iff_of_isGrpPullback hπ hπ' g f e.symm).symm
      (and_congr (FieldBaseChange.isMonHom_iff_of_isGrpPullback hπ' hπ g' f' e'.symm).symm
      (and_congr (eq_iff hπ.1 hπ.1 (comp_sq e e') (id_pow_left hπ N))
      (and_congr (eq_iff hπ'.1 hπ'.1 (comp_sq e' e) (id_pow_left hπ' N))
      (and_congr (forall_congr' fun a => ?_) (forall_congr' fun a => ?_)))))
    · exact eq_iff hπ.1 hπ'.1 (comp_sq (map_sq π p₁ p₂ _) e)
        (comp_sq (u := f) (u' := g) (v := (Over.pullback x').map _) (v' := (Over.pullback w').map _) e
          (map_sq π' p₁' p₂' _))
    · exact eq_iff hπ'.1 hπ.1 (comp_sq (map_sq π' p₁' p₂' _) e')
        (comp_sq (u := f') (u' := g') (v := (Over.pullback x).map _) (v' := (Over.pullback w).map _) e'
          (map_sq π p₁ p₂ _))

end GlobalTheory.HkIntegral.PairBC
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

theorem sabMap_exists_iso_pullback {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {j : S' ⟶ S} (m : SABMap s' s j) :
    ∃ e : s'.G ≅ (Over.pullback j).obj s.G, IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst s.G.hom j = m.φ ∧
      ∀ a, s'.act.act a ≫ e.hom = e.hom ≫ (Over.pullback j).map (s.act.act a) := by
  obtain ⟨e, he, hφ⟩ := grpPullback_iso m.cart (isGrpPullback_pullback s.G _)
  have hφ' : e.hom.left ≫ pullback.fst s.G.hom j = m.φ := hφ
  refine ⟨e, he, hφ', fun a => ?_⟩
  have A : ((Over.pullback j).map (s.act.act a)).left ≫ pullback.fst s.G.hom _ =
        pullback.fst s.G.hom _ ≫ (s.act.act a).left := pullback.lift_fst _ _ _
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, A]
    rw [reassoc_of% hφ', hφ', m.act a]
  · exact (Over.w _).trans (Over.w _).symm

theorem conj_comp_eq_id_pow {S : Scheme.{0}} {A B A' B' : Over S} [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
    (u : A ≅ B) (u' : A' ≅ B') [IsMonHom u.hom] (f : B ⟶ B') (f' : B' ⟶ B) (N : ℕ) (h : f ≫ f' = 𝟙 B ^ N) :
    (u.hom ≫ f ≫ u'.inv) ≫ (u'.hom ≫ f' ≫ u.inv) = 𝟙 A ^ N := by
  have : IsMonHom u.inv := inferInstance
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% h, MonObj.pow_comp, MonObj.comp_pow]
  simp

theorem pullback_map_id_pow {S S' : Scheme.{0}} (j : S' ⟶ S) (A : Over S) [GrpObj A] (N : ℕ) :
    (Over.pullback j).map (𝟙 A ^ N) = 𝟙 ((Over.pullback j).obj A) ^ N := by
  induction N with
  | zero => simpa using Functor.map_one (Over.pullback j)
  | succ n ih => rw [pow_succ, pow_succ, Functor.map_mul, ih]; simp

theorem ext_of_map_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {T : CDVR} {x x' : Sp T.Fr ⟶ Xo.X} {G G' : SAB H (Sp T.V)} {t t' : SAB H (Sp T.Fr)}
    (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr)))
    (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr)))
    (f : Fib Xo x ⟶ Fib Xo x') [IsMonHom f] (F : G.G ⟶ G'.G)
    (d : t.G ≅ Fib Xo x) (d' : t'.G ≅ Fib Xo x') [IsMonHom d.hom] [IsMonHom d'.hom]
    (e : t.G ≅ (Over.pullback (spMap (algebraMap T.V T.Fr))).obj G.G)
    (e' : t'.G ≅ (Over.pullback (spMap (algebraMap T.V T.Fr))).obj G'.G)
    (hd : d.hom.left ≫ pullback.fst _ _ = m₁.φ) (hd' : d'.hom.left ≫ pullback.fst _ _ = n₁.φ)
    (he : e.hom.left ≫ pullback.fst _ _ = m₂.φ) (he' : e'.hom.left ≫ pullback.fst _ _ = n₂.φ)
    (hF : (Over.pullback (spMap (algebraMap T.V T.Fr))).map F = (e.symm ≪≫ d).hom ≫ f ≫ (e'.symm ≪≫ d').inv) :
    Ext m₁ m₂ n₁ n₂ f F := by
  have A : ((Over.pullback (spMap (algebraMap T.V T.Fr))).map F).left ≫ pullback.fst G'.G.hom _ =
        pullback.fst G.G.hom _ ≫ F.left := pullback.lift_fst _ _ _
  have B : (d.hom ≫ f ≫ d'.inv) ≫ e'.hom = e.hom ≫ (Over.pullback (spMap (algebraMap T.V T.Fr))).map F := by
    rw [hF]; simp
  refine ⟨d.hom ≫ f ≫ d'.inv, inferInstance, ?_, fun g g' h1 h2 h3 h4 => ?_⟩
  · rw [← he', ← he, Category.assoc, ← A, ← Category.assoc, ← Category.assoc e.hom.left, ← Over.comp_left,
      ← Over.comp_left, B]
  · obtain rfl : g = d.hom.left := pullback.hom_ext (h1.trans hd.symm) (h2.trans (Over.w d.hom).symm)
    obtain rfl : g' = d'.hom.left := pullback.hom_ext (h3.trans hd'.symm) (h4.trans (Over.w d'.hom).symm)
    have C : d.hom ≫ f = (d.hom ≫ f ≫ d'.inv) ≫ d'.hom := by simp
    exact congrArg (fun k => k.left) C

theorem conj_comm {C : Type*} [Category C] {A B P A' B' P' : C} (e : A ≅ P) (d : A ≅ B) (e' : A' ≅ P') (d' : A' ≅ B')
    (f : B ⟶ B') (a : A ⟶ A) (b : B ⟶ B) (p : P ⟶ P) (a' : A' ⟶ A') (b' : B' ⟶ B') (p' : P' ⟶ P')
    (hd : a ≫ d.hom = d.hom ≫ b) (he : a ≫ e.hom = e.hom ≫ p) (hd' : a' ≫ d'.hom = d'.hom ≫ b')
    (he' : a' ≫ e'.hom = e'.hom ≫ p') (h : b ≫ f = f ≫ b') :
    p ≫ (e.symm ≪≫ d).hom ≫ f ≫ (e'.symm ≪≫ d').inv = ((e.symm ≪≫ d).hom ≫ f ≫ (e'.symm ≪≫ d').inv) ≫ p' := by
  have h1 : p ≫ e.inv = e.inv ≫ a := by rw [Iso.eq_inv_comp, ← reassoc_of% he]; simp
  have h2 : b' ≫ d'.inv = d'.inv ≫ a' := by rw [Iso.eq_inv_comp, ← reassoc_of% hd']; simp
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% hd, reassoc_of% h, reassoc_of% h2, he']

theorem exists_ext_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : CDVR) (x x' : Sp T.Fr ⟶ Xo.X) (G G' : SAB H (Sp T.V)) (t t' : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr))) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x), IsMonHom f → IsMonHom f' → ∃ (F : G.G ⟶ G'.G) (F' : G'.G ⟶ G.G), IsMonHom F ∧ IsMonHom F' ∧ Ext m₁ m₂ n₁ n₂ f F ∧ Ext n₁ n₂ m₁ m₂ f' F' ∧ (∀ N : ℕ, f ≫ f' = 𝟙 _ ^ N → F ≫ F' = 𝟙 _ ^ N) ∧ (∀ N : ℕ, f' ≫ f = 𝟙 _ ^ N → F' ≫ F = 𝟙 _ ^ N) ∧ (Lin f → ∀ a, G.act.act a ≫ F = F ≫ G'.act.act a) ∧ (Lin f' → ∀ a, G'.act.act a ≫ F' = F' ≫ G.act.act a) := by
  intro E _ _ _ H Dw l Xo T x x' G G' t t' m₁ m₂ n₁ n₂ f f' hf hf'
  have hx := semiAbelian_hom_extends_uniquely_dvr T.V T.Fr
  have inj : ∀ (s s' : SAB H (Sp T.V)) (F F' : s.G ⟶ s'.G), IsMonHom F → IsMonHom F' →
      (Over.pullback (spMap (algebraMap T.V T.Fr))).map F = (Over.pullback (spMap (algebraMap T.V T.Fr))).map F' →
        F = F' := by
    intro s s' F F' hF hF' h
    exact (hx s.G s'.G s.semi s'.semi _ inferInstance).unique ⟨hF, rfl⟩ ⟨hF', h.symm⟩
  have hpow : ∀ (s : SAB H (Sp T.V)) (N : ℕ), IsMonHom (𝟙 s.G ^ N) := by
    intro s N
    induction N with
    | zero =>
      rw [pow_zero]
      exact inferInstanceAs (IsMonHom (toUnit s.G ≫ η[s.G]))
    | succ n ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 s.G ^ n) (𝟙 s.G) ≫ μ[s.G]))
  obtain ⟨d, hd, hdφ, hda⟩ := sabMap_exists_iso_pullback m₁
  obtain ⟨e, he, heφ, hea⟩ := sabMap_exists_iso_pullback m₂
  obtain ⟨d', hd', hdφ', hda'⟩ := sabMap_exists_iso_pullback n₁
  obtain ⟨e', he', heφ', hea'⟩ := sabMap_exists_iso_pullback n₂
  obtain ⟨F, ⟨hF, hFf⟩, -⟩ := hx G.G G'.G G.semi G'.semi
    ((e.symm ≪≫ d).hom ≫ f ≫ (e'.symm ≪≫ d').inv) (by dsimp; infer_instance)
  obtain ⟨F', ⟨hF', hFf'⟩, -⟩ := hx G'.G G.G G'.semi G.semi
    ((e'.symm ≪≫ d').hom ≫ f' ≫ (e.symm ≪≫ d).inv) (by dsimp; infer_instance)
  have : IsMonHom (e.symm ≪≫ d).hom := by dsimp; infer_instance
  have : IsMonHom (e'.symm ≪≫ d').hom := by dsimp; infer_instance
  refine ⟨F, F', hF, hF', ext_of_map_eq m₁ m₂ n₁ n₂ f F d d' e e' hdφ hdφ' heφ heφ' hFf,
    ext_of_map_eq n₁ n₂ m₁ m₂ f' F' d' d e' e hdφ' hdφ heφ' heφ hFf', fun N h => ?_, fun N h => ?_,
    fun h a => ?_, fun h a => ?_⟩
  · refine inj _ _ _ _ inferInstance (hpow G N) ?_
    rw [Functor.map_comp, hFf, hFf', pullback_map_id_pow]
    exact conj_comp_eq_id_pow _ _ f f' N h
  · refine inj _ _ _ _ inferInstance (hpow G' N) ?_
    rw [Functor.map_comp, hFf, hFf', pullback_map_id_pow]
    exact conj_comp_eq_id_pow _ _ f' f N h
  · have := G.act.hom a
    have := G'.act.hom a
    refine inj _ _ _ _ inferInstance inferInstance ?_
    rw [Functor.map_comp, Functor.map_comp, hFf]
    exact conj_comm e d e' d' f _ _ _ _ _ _ (hda a) (hea a) (hda' a) (hea' a) (h a)
  · have := G.act.hom a
    have := G'.act.hom a
    refine inj _ _ _ _ inferInstance inferInstance ?_
    rw [Functor.map_comp, Functor.map_comp, hFf']
    exact conj_comm e' d' e d f' _ _ _ _ _ _ (hda' a) (hea' a) (hda a) (hea a) (h a)

end GlobalTheory.HkIntegral
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed

theorem _root_.GlobalTheory.T.hasSum_cuspidalMultiplicity_trace : GlobalTheory.Published.CuspTraceClass → ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ f ∈ CcGA V, (∀ c : UDual (GA D V), mCusp V μ c.rep.π ≠ 0 → IsTraceClass (repOp c.rep.π μ f)) ∧ (Summable fun c : UDual (GA D V) => ‖((mCusp V μ c.rep.π).toNat : ℂ) * repTrace c.rep.π μ f‖) ∧ HasSum (fun c : UDual (GA D V) => ((mCusp V μ c.rep.π).toNat : ℂ) * repTrace c.rep.π μ f) (trace (RcuspOp V μ f)) := by
  first | exact @GlobalTheory.CuspTraceSum.hasSum_mCusp_repTrace | exact GlobalTheory.CuspTraceSum.hasSum_mCusp_repTrace | (intros; apply GlobalTheory.CuspTraceSum.hasSum_mCusp_repTrace <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.rationalForm_coordinates_coeff_mem_coefficientField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (x : A.fam.amb.FR t) (y : FinPt ch.G (.grid 0 D.R.m)) m, AddMonoidAlgebra.coeff (ch.S.formC t (R.jX t x) y).1 m ∈ Set.range D.what₂.embLL := by
  first | exact @GlobalTheory.FormCoef.coeff_formC_mem | exact GlobalTheory.FormCoef.coeff_formC_mem | (intros; apply GlobalTheory.FormCoef.coeff_formC_mem <;> assumption)
end
