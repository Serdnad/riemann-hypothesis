module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.RingTheory.Smooth.Basic
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentImagesLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle135
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2343
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2333
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
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
import Mathlib.GroupTheory.CosetCover
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory

theorem secClosed_closedPoint (K : Type) [Field K] (X : Scheme.{0}) (q : X ⟶ Sp K) (z : Sp K ⟶ X)
    (_hq : IsProjOver q) (hz : z ≫ q = 𝟙 _) :
    IsClosed ({z (IsLocalRing.closedPoint K)} : Set X) := by
  have : IsClosedImmersion z := isClosedImmersion_of_comp_eq_id q z hz
  have hc : IsClosed (Set.range z.base) := z.isClosedEmbedding.isClosed_range
  convert hc using 1
  ext x
  constructor
  · rintro rfl; exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    rw [Set.mem_singleton_iff, Subsingleton.elim y (IsLocalRing.closedPoint K)]

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory

theorem section_eq_of_point_eq : ∀ (K : Type) [Field K] (X : Scheme.{0}) (q : X ⟶ Sp K) (z z' : Sp K ⟶ X), z ≫ q = 𝟙 _ → z' ≫ q = 𝟙 _ → z (IsLocalRing.closedPoint K) = z' (IsLocalRing.closedPoint K) → z = z' := by
  intro K _ X q z z' hz hz' hpt
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective z
  obtain ⟨⟨p', ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective z'
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hz hz' hpt ⊢
  have e : p = p' := by
    have h1 := (Scheme.Hom.comp_apply _ _ _).symm.trans (hpt.trans (Scheme.Hom.comp_apply _ _ _))
    rwa [Scheme.fromSpecResidueField_apply, Scheme.fromSpecResidueField_apply] at h1
  subst e
  obtain ⟨χ, hχ⟩ := Spec.map_surjective (X.fromSpecResidueField p ≫ q)
  rw [Category.assoc, ← hχ, ← Spec.map_comp, ← Spec.map_id, Spec.map_inj] at hz hz'
  have hφ : ∀ c, φ.hom (χ.hom c) = c := fun c => congrArg (fun g => g.hom c) hz
  have hψ : ∀ c, ψ.hom (χ.hom c) = c := fun c => congrArg (fun g => g.hom c) hz'
  have hsurj : Function.Surjective χ.hom := by
    intro y
    refine ⟨φ.hom y, φ.hom.injective ?_⟩
    rw [hφ]
  have : φ = ψ := by
    ext y
    obtain ⟨c, rfl⟩ := hsurj y
    rw [hφ, hψ]
  rw [this]

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

open scoped TensorProduct

namespace GlobalTheory.CoordExt

theorem formallySmooth_of_charZero (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] :
    Algebra.FormallySmooth F K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F K
  haveI := hs.isAlgebraic_field
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  haveI : CharZero (IntermediateField.adjoin F (Set.range ((↑) : s → K))) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  haveI : Algebra.IsSeparable (IntermediateField.adjoin F (Set.range ((↑) : s → K))) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

theorem span_D_algebraMap_eq_top (F A R : Type) [Field F] [CommRing A] [CommRing R]
    [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] (P : Ideal A) [P.IsPrime]
    [IsLocalization.AtPrime R P] :
    Submodule.span R (Set.range fun y : A => KaehlerDifferential.D F R (algebraMap A R y)) = ⊤ := by
  set S := Submodule.span R (Set.range fun y : A => KaehlerDifferential.D F R (algebraMap A R y))
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl r
  have hu : IsUnit (algebraMap A R s) := IsLocalization.map_units R s
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have key : algebraMap A R s • KaehlerDifferential.D F R (IsLocalization.mk' R y s) =
      KaehlerDifferential.D F R (algebraMap A R y) -
        IsLocalization.mk' R y s • KaehlerDifferential.D F R (algebraMap A R s) := by
    rw [eq_sub_iff_add_eq, add_comm, ← Derivation.leibniz, IsLocalization.mk'_spec]
  have hmem : algebraMap A R s • KaehlerDifferential.D F R (IsLocalization.mk' R y s) ∈ S := by
    rw [key]
    exact sub_mem (Submodule.subset_span ⟨y, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩))
  have : KaehlerDifferential.D F R (IsLocalization.mk' R y s) =
      v • (algebraMap A R s • KaehlerDifferential.D F R (IsLocalization.mk' R y s)) := by
    rw [smul_smul, hv, one_smul]
  change _ ∈ S
  rw [this]
  exact Submodule.smul_mem _ _ hmem

theorem span_tmul_eq_top {R M : Type} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    {ι : Type} (f : ι → M) (hf : Submodule.span R (Set.range f) = ⊤) :
    Submodule.span (IsLocalRing.ResidueField R)
      (Set.range fun i => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f i) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.TensorUnitSpanTop.main
  | exact _root_.GlobalTheory.TensorUnitSpanTop.main
  | (apply _root_.GlobalTheory.TensorUnitSpanTop.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.TensorUnitSpanTop.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TensorUnitSpanTop.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TensorUnitSpanTop.main ..)

end GlobalTheory.CoordExt


open GlobalTheory.CoordExt in
theorem GlobalTheory.exists_coords_extending_regularParams : ∀ (F A R : Type) [Field F] [CharZero F] [CommRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (n : ℕ) [Module.Free R Ω[R⁄F]] [Module.Finite R Ω[R⁄F]], Module.finrank R Ω[R⁄F] = n → ∀ (m : ℕ) (a : Fin m → A), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m (fun i => algebraMap A R (a i)) → ∃ (x : Fin n → A) (e : Fin m ↪ Fin n), (∀ j, x (e j) = a j) ∧ ∃ bs : Module.Basis (Fin n) R Ω[R⁄F], ∀ i, bs i = KaehlerDifferential.D F R (algebraMap A R (x i)) := by
  classical
  intro F A R _ _ _ _ _ _ _ _ _ _ _ P _ _ n _ _ hn m a hrsp
  haveI : Algebra.FormallySmooth F (IsLocalRing.ResidueField R) := formallySmooth_of_charZero F _
  set r : Fin m → R := fun i => algebraMap A R (a i) with hr_def
  have hr : ∀ i, r i ∈ IsLocalRing.maximalIdeal R := fun i => hrsp.1 ▸ Ideal.subset_span ⟨i, rfl⟩

  have hcot : LinearIndependent (IsLocalRing.ResidueField R) (fun i =>
      ((IsLocalRing.maximalIdeal R).toCotangent ⟨r i, hr i⟩ : IsLocalRing.CotangentSpace R)) := by
    have hfr : Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = m := by
      have := (IsRegularLocalRing.iff_finrank_cotangentSpace R).1 inferInstance
      rw [← hrsp.2] at this
      exact_mod_cast this
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp [hfr])
    have hsp : Submodule.span R (Set.range fun i => (⟨r i, hr i⟩ : IsLocalRing.maximalIdeal R)) = ⊤ := by
      apply Submodule.map_injective_of_injective (IsLocalRing.maximalIdeal R).injective_subtype
      rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
      exact hrsp.1
    rw [← IsLocalRing.CotangentSpace.span_image_eq_top_iff] at hsp
    rw [← Set.range_comp] at hsp
    exact hsp.ge
  have hw := GlobalTheory.AdaptedFrame.linearIndependent_tmul_D (k := F) r hr hcot
  let φ : A → IsLocalRing.ResidueField R ⊗[R] Ω[R⁄F] :=
    fun y => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] KaehlerDifferential.D F R (algebraMap A R y)
  have hw' : LinearIndependent (IsLocalRing.ResidueField R) (φ ∘ a) := hw
  have ha : Function.Injective a := fun i j h => hw'.injective (by simp only [Function.comp_apply, h])
  have hli : LinearIndepOn (IsLocalRing.ResidueField R) φ (Set.range a) :=
    (linearIndepOn_range_iff ha φ).2 hw'
  obtain ⟨b, -, hab, hbsp, hbli⟩ := exists_linearIndepOn_extension hli (Set.subset_univ _)
  have hVsp : Submodule.span (IsLocalRing.ResidueField R) (Set.range φ) = ⊤ :=
    span_tmul_eq_top _ (span_D_algebraMap_eq_top F A R P)
  have hbtop : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField R) (Set.range fun y : b => φ y) := by
    rw [← Set.image_eq_range, ← hVsp, ← Set.image_univ]
    exact Submodule.span_le.2 hbsp
  let bV := Module.Basis.mk hbli hbtop
  haveI : Finite b := Module.Finite.finite_basis bV
  letI : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = n := by
    rw [← Module.finrank_eq_card_basis bV, Module.finrank_baseChange, hn]
  let σ := Fintype.equivFinOfCardEq hcard
  let e0 : Fin m ↪ b := ⟨fun j => ⟨a j, hab ⟨j, rfl⟩⟩, fun i j h => ha (congrArg Subtype.val h)⟩
  refine ⟨fun i => ((σ.symm i : b) : A), e0.trans σ.toEmbedding, fun j => by
    simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
    rfl, ?_⟩
  let ω : Fin n → Ω[R⁄F] := fun i => KaehlerDifferential.D F R (algebraMap A R (σ.symm i : b))
  have hb' : ∀ i, (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] ω i = bV.reindex σ i := by
    intro i
    rw [Module.Basis.reindex_apply]
    exact (Module.Basis.mk_apply hbli hbtop _).symm
  have hspan := IsLocalRing.span_eq_top_of_tmul_eq_basis ω (bV.reindex σ) hb'
  have hli2 : LinearIndependent R ω :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (by simp [hn])
  exact ⟨Module.Basis.mk hli2 hspan.ge, fun i => by rw [Module.Basis.mk_apply]⟩
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}


open Classical in
def flatFrame {K : Type} [CommRing K] (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) {n n' : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') :
    Matrix (Fin n) (Fin n') K :=
  (Matrix.blockDiagonal' A).submatrix e.symm e'.symm

theorem flatFrame_apply {K : Type} [CommRing K] (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    {n n' : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (τ : E →+* ℂ) (i k : Fin (Dw.mult τ)) : flatFrame A e e' (e ⟨τ, i⟩) (e' ⟨τ, k⟩) = A τ i k := by
  simp [flatFrame, Matrix.blockDiagonal'_apply_eq]

end GlobalTheory.LogKSDiv
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

theorem _root_.GlobalTheory.T.exists_closedPoint_specializes_in_open_of_finiteType : ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k) [LocallyOfFiniteType q] (U : X.Opens) (y : X), y ∈ U → ∃ x : X, IsClosed ({x} : Set X) ∧ y ⤳ x ∧ x ∈ U := by
  first | exact @GlobalTheory.closedPoint_specializing_in_open | exact GlobalTheory.closedPoint_specializing_in_open | (intros; apply GlobalTheory.closedPoint_specializing_in_open <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory


open GlobalTheory.ZeroDimSystem in
theorem exists_sec_nonzero_on_finite_of_generated :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X] (p : X ⟶ Sp k) (L : LB X), L.IsLB → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → ∀ S : Set X, S.Finite → ∃ s : L.Sec, ∀ x ∈ S, x ∈ nonzeroLocus s := by
  intro k _ _ X _ p L _ n u hu S hS
  classical
  letI : Algebra k Γ(X, ⊤) := (p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have hne : ∀ x ∈ hS.toFinset, vanishAt (k := k) u x ≠ ⊤ := fun x _ h => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hu.ge (Set.mem_univ x))
    exact single_notMem_vanishAt (k := k) u hi (h.symm ▸ Submodule.mem_top)
  have h := Subspace.biUnion_ne_univ_of_top_notMem (k := k) (E := Fin n → k)
    (s := hS.toFinset.image (vanishAt (k := k) u)) (by
      rw [Finset.mem_image]
      rintro ⟨x, hx, h⟩
      exact hne x hx h)
  obtain ⟨c, hc⟩ := (Set.ne_univ_iff_exists_notMem _).1 h
  refine ⟨comb u c, fun x hx => ?_⟩
  by_contra hxc
  exact hc (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (hS.mem_toFinset.2 hx)))
    ((mem_vanishAt u x c).2 hxc))

end GlobalTheory
end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.LevDesc (move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.TateTorsion


open NumberField in
theorem _root_.GlobalTheory.TateTorsion.torsion_eq_level_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (T : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso Dw k Q act e) (eta : Dw.La → Q) (I : Ideal (𝓞 E)) (g : ℕ), (∀ a b x, act (a + b) x = act a x * act b x) → (∀ x, act 1 x = x) → (∀ (n : ℕ) x, act (n : 𝓞 E) x = x ^ n) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), eta a = T.ev l.M a) → g.Prime → Ideal.absNorm I = g → (g : 𝓞 E) ∉ I ^ 2 → l.Mb ≤ I → ∃ t : 𝓞 E, (∀ c ∈ I • (⊤ : Submodule (𝓞 E) Dw.La), t • c ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ ∀ x : Q, (∀ a ∈ I, act a x = 1) → ∃ c : Dw.La, x = eta (t • c) := by
  intro E _ _ _ H Dw l k _ Q _ act e T eta I g hadd hone hnat heta hg hI hsq hle
  have hMb : (l.M : 𝓞 E) ∈ l.Mb := by
    have h : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.mem_span_singleton_self _
    rw [← l.prod] at h
    exact Ideal.mul_le_left h
  have hgI : (g : 𝓞 E) ∈ I := hI ▸ Ideal.absNorm_mem I
  have hprime : I.IsPrime := by
    apply Ideal.isPrime_of_irreducible_absNorm
    rw [hI]
    exact (Nat.prime_iff.mp hg).irreducible
  have hne : I ≠ ⊥ := by
    rintro rfl
    simp only [Ideal.absNorm_bot] at hI
    exact hg.ne_zero hI.symm
  have hmax : I.IsMaximal := hprime.isMaximal hne
  obtain ⟨B, hB⟩ : I ∣ Ideal.span {(g : 𝓞 E)} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hgI)
  have hIB : I ⊔ B = ⊤ := by
    by_contra h
    have hBI : B ≤ I := (hmax.eq_of_le h le_sup_left).symm ▸ le_sup_right
    apply hsq
    have hgB : (g : 𝓞 E) ∈ I * B := hB ▸ Ideal.mem_span_singleton_self _
    rw [pow_two]
    exact Ideal.mul_mono_right hBI hgB
  have hIbar : I ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ :=
    eq_top_iff.mpr (l.coprime ▸ sup_le_sup_right hle _)
  have hIK : I ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) * B = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq] at hIB hIbar ⊢
    exact hIbar.mul_right hIB
  obtain ⟨i, hi, u, hu, hiu⟩ :=
    Submodule.mem_sup.mp (hIK ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ I ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) * B)
  have huB : u ∈ B := Ideal.mul_le_right hu
  have huBar : u ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mul_le_left hu
  have hgN : g ∣ l.M := by
    have h := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr (hle hMb))
    have h' : ((l.M : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (l.M : ℤ) := by simp
    rw [hI, Ideal.absNorm_span_singleton, h', Algebra.norm_algebraMap, Int.natAbs_pow,
      Int.natAbs_natCast] at h
    exact hg.dvd_of_dvd_pow h
  obtain ⟨m, hm⟩ := hgN
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; have := l.three_le; omega)
  have key : ∀ j ∈ I, (m : 𝓞 E) * u * j ∈ l.Mb := by
    intro j hj
    have h : u * j ∈ Ideal.span {(g : 𝓞 E)} := hB ▸ (mul_comm j u ▸ Ideal.mul_mem_mul hj huB)
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp h
    have h2 : (m : 𝓞 E) * u * j = r * (l.M : 𝓞 E) := by
      rw [mul_assoc, ← hr, hm]; push_cast; ring
    rw [h2]
    exact Ideal.mul_mem_left _ r hMb
  refine ⟨(m : 𝓞 E) * u, ?_, ?_⟩
  · intro c hc
    refine Submodule.smul_induction_on hc (fun j hj y _ => ?_) (fun y z hy hz => ?_)
    · rw [smul_smul]
      exact Submodule.smul_mem_smul (key j hj) Submodule.mem_top
    · rw [smul_add]
      exact add_mem hy hz
  · intro x hx
    have hxg : x ^ g = 1 := by rw [← hnat]; exact hx _ hgI
    obtain ⟨b, hb⟩ := (T.onto g hg.pos x).mp hxg
    have hpow : ∀ (n j : ℕ) (a : Dw.La), T.ev n (j • a) = T.ev n a ^ j := by
      intro n j a
      induction j with
      | zero =>
        have h := T.add n 0 0
        rw [add_zero] at h
        simpa using h
      | succ j ih => rw [succ_nsmul, T.add, ih, pow_succ]
    have hux : act u x = x := by
      have h := hone x
      rwa [← hiu, hadd, hx i hi, one_mul] at h
    refine ⟨b, ?_⟩
    have hmem : ((m : 𝓞 E) * u) • b ∈
        l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) :=
      Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ huBar) Submodule.mem_top
    rw [heta _ hmem, mul_comm, mul_smul, T.lin, Nat.cast_smul_eq_nsmul, hpow, hm,
      T.tower g m hg.pos hm0, hb, hux]

end GlobalTheory.TateTorsion
end
