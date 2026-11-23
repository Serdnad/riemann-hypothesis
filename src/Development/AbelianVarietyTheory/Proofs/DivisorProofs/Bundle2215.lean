module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle096
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

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

namespace GlobalTheory.FrameSpread

open GlobalTheory.TopForm

theorem exists_basicOpen_isFrame_dOn : ∀ (k : Type) [Field k] (X : Scheme.{0}) (p : X ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n p] (U : X.affineOpens) (x₀ : X) (hx : x₀ ∈ U.1) (x : Fin n → Γ(X, U.1)), (letI := ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1)).toAlgebra; ∃ bs : Module.Basis (Fin n) (X.presheaf.stalk x₀) Ω[X.presheaf.stalk x₀⁄k], ∀ i, bs i = KaehlerDifferential.D k (X.presheaf.stalk x₀) ((X.presheaf.germ U.1 x₀ hx).hom (x i))) → ∃ s : Γ(X, U.1), x₀ ∈ X.basicOpen s ∧ GlobalTheory.TopForm.IsFrame (GlobalTheory.TopForm.dOn p fun i => resG X (X.basicOpen_le s) (x i)) := by
  intro k _ X p n _ U x₀ hx x hbs
  obtain ⟨V, ω, hxV, hω⟩ := TopForm.exists_isFrame p n x₀
  obtain ⟨s, hsV, hxs⟩ := U.2.exists_basicOpen_le ⟨x₀, hxV⟩ hx
  have hWU : X.basicOpen s ≤ U.1 := X.basicOpen_le s
  have hWaff : IsAffineOpen (X.basicOpen s) := U.2.basicOpen s
  have hωW := hω.res hWaff hsV
  set η : FormsOn p n (X.basicOpen s) := TopForm.dOn p (fun i => resG X hWU (x i)) with hη
  set J : Γ(X, X.basicOpen s) := hωW.gen.repr η with hJdef
  have hJ : J • TopForm.resForm hsV ω = η := hωW.gen.repr_smul η
  obtain ⟨bs, hbs⟩ := hbs
  set ρ : Γ(X, X.basicOpen s) →+* X.presheaf.stalk x₀ := (X.presheaf.germ (X.basicOpen s) x₀ hxs).hom with hρ
  have hgerm : ∀ a : Γ(X, U.1), ρ (resG X hWU a) = (X.presheaf.germ U.1 x₀ hx).hom a := fun a => by
    have := TopCat.Presheaf.germ_res X.presheaf (homOfLE hWU) x₀ hxs
    exact congrArg (fun φ => (ConcreteCategory.hom φ) a) this
  have hρα : ρ.comp (algX p (X.basicOpen s)) = (X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1) := by
    rw [← resG_comp_algX p hWU]
    ext a
    exact hgerm _
  have hfe : letI := ρ.toAlgebra; Algebra.FormallyEtale Γ(X, X.basicOpen s) (X.presheaf.stalk x₀) := by
    letI := ρ.toAlgebra
    haveI := hWaff.isLocalization_stalk ⟨x₀, hxs⟩
    exact Algebra.FormallyEtale.of_isLocalization (hWaff.primeIdealOf ⟨x₀, hxs⟩).asIdeal.primeCompl
  have h1 : IsFreeGen (X.presheaf.stalk x₀) (TopForm.formMap n ρ hρα (TopForm.resForm hsV ω)) := by
    letI := (algX p (X.basicOpen s)).toAlgebra
    letI := ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1)).toAlgebra
    letI := ρ.toAlgebra
    haveI : IsScalarTower k Γ(X, X.basicOpen s) (X.presheaf.stalk x₀) :=
      IsScalarTower.of_algebraMap_eq' hρα.symm
    haveI : Algebra.FormallyEtale Γ(X, X.basicOpen s) (X.presheaf.stalk x₀) := hfe
    exact hωW.gen.of_isBaseChange (isBaseChange_exteriorPower
      (KaehlerDifferential.isBaseChange_of_formallyEtale k Γ(X, X.basicOpen s) (X.presheaf.stalk x₀)) n)
  have h2 : IsFreeGen (X.presheaf.stalk x₀)
      (dForm ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1))
        (fun i => (X.presheaf.germ U.1 x₀ hx).hom (x i))) :=
    isFreeGen_dForm _ bs hbs
  have h3 : TopForm.formMap n ρ hρα η = ρ J • TopForm.formMap n ρ hρα (TopForm.resForm hsV ω) := by
    rw [← hJ, map_smulₛₗ]
  have h4 : TopForm.formMap n ρ hρα η = dForm ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1))
      (fun i => (X.presheaf.germ U.1 x₀ hx).hom (x i)) := by
    rw [hη, dOn, formMap_dForm]
    simp only [hgerm]
  have hu : IsUnit (ρ J) := h1.smul_iff.1 (h3 ▸ h4 ▸ h2)
  have hxJ : x₀ ∈ X.basicOpen J := (X.mem_basicOpen J x₀ hxs).2 hu
  obtain ⟨t, htJ, hxt⟩ := U.2.exists_basicOpen_le ⟨x₀, hxJ⟩ hx
  refine ⟨t, hxt, ?_⟩
  have hJW : X.basicOpen J ≤ X.basicOpen s := X.basicOpen_le J
  have hte : X.basicOpen t ≤ X.basicOpen s := htJ.trans hJW
  have hframe := hωW.res (U.2.basicOpen t) hte
  have e : TopForm.dOn p (fun i => resG X (X.basicOpen_le t) (x i)) =
      resG X hte J • TopForm.resForm hte (TopForm.resForm hsV ω) := by
    rw [← resForm_smul, hJ, hη, resForm_dOn]
    simp only [resG_resG]
  rw [e]
  refine ⟨U.2.basicOpen t, hframe.gen.smul_iff.2 ?_⟩
  have hu' : IsUnit (resG X hJW J) := X.toRingedSpace.isUnit_res_basicOpen J
  have := hu'.map (resG X htJ)
  rwa [resG_resG] at this

end GlobalTheory.FrameSpread
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace TopForm

namespace FrameBasis

theorem bijective_of_isFreeGen {k A : Type*} [CommRing k] [CommRing A] (α : k →+* A) {m : ℕ}
    (hA : α.IsStandardSmoothOfRelativeDimension m) (x : Fin m → A)
    (hx : IsFreeGen A (dForm α x)) :
    Function.Bijective (Fintype.linearCombination A fun i => dFun α (x i)) := by
  letI := α.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension m k A := hA
  cases subsingleton_or_nontrivial A with
  | inl _ =>
    haveI := Module.subsingleton A (Omega α)
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  | inr _ =>
    haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth m (R := k) (S := A)
    haveI : Module.Free A (Omega α) := inferInstanceAs (Module.Free A Ω[A⁄k])
    haveI : Module.Finite A (Omega α) := inferInstanceAs (Module.Finite A Ω[A⁄k])
    have hr : Module.finrank A (Omega α) = m := Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := A) m)
    let b := Module.finBasisOfFinrankEq A (Omega α) hr
    let v : Fin m → Omega α := fun i => dFun α (x i)
    obtain ⟨a, ha⟩ := hx.2 (exteriorPower.ιMulti A m b)
    have e := congrArg (exteriorPower.alternatingMapLinearEquiv b.det) ha
    simp only [map_smul, dForm_eq, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      Module.Basis.det_self, smul_eq_mul] at e
    have hu : IsUnit (b.det v) := IsUnit.of_mul_eq_one a (by rw [mul_comm]; exact e)
    obtain ⟨hli, hsp⟩ := (b.is_basis_iff_det).2 hu
    let b' := Module.Basis.mk hli hsp.ge
    have : (Fintype.linearCombination A fun i => dFun α (x i)) = b'.equivFun.symm.toLinearMap := by
      ext c
      simp [Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply, b', v]
    rw [this]
    exact b'.equivFun.symm.bijective

end FrameBasis

end TopForm

end GlobalTheory

namespace GlobalTheory.TopForm.FrameBasis

theorem bijective_of_isLocalization_span {k A : Type*} [CommRing k] [CommRing A] (α : k →+* A)
    {m : ℕ} (x : Fin m → A) (s : Set A) (hs : Ideal.span s = ⊤) (B : s → Type*)
    [∀ t, CommRing (B t)] [∀ t, Algebra A (B t)] [∀ t : s, IsLocalization.Away t.1 (B t)]
    (H : ∀ t : s, Function.Bijective (Fintype.linearCombination (B t)
      fun i => dFun ((algebraMap A (B t)).comp α) (algebraMap A (B t) (x i)))) :
    Function.Bijective (Fintype.linearCombination A fun i => dFun α (x i)) := by
  letI := α.toAlgebra
  letI (t : s) : Algebra k (B t) := ((algebraMap A (B t)).comp α).toAlgebra
  haveI (t : s) : IsScalarTower k A (B t) := IsScalarTower.of_algebraMap_eq' rfl
  haveI (t : s) : Algebra.FormallyEtale A (B t) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t.1)
  let g : ∀ t : s, Ω[A⁄k] →ₗ[A] Ω[B t⁄k] := fun t => KaehlerDifferential.map k k A (B t)
  haveI H₁ (t : s) : IsLocalizedModule.Away t.1 (g t) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers t.1) (B t) (g t)).2
      (KaehlerDifferential.isBaseChange_of_formallyEtale k A (B t))
  let π : ∀ t : s, (Fin m → A) →ₗ[A] (Fin m → B t) := fun t => (Algebra.linearMap A (B t)).compLeft (Fin m)
  haveI H₂ (t : s) : IsLocalizedModule.Away t.1 (π t) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers t.1) (B t) (π t)).2
      (IsBaseChange.finitePow (Fin m) (IsBaseChange.linearMap A (B t)))
  let e : ∀ t : s, (Fin m → B t) ≃ₗ[A] Ω[B t⁄k] := fun t =>
    (LinearEquiv.ofBijective _ (H t)).restrictScalars A
  haveI H₃ (t : s) : IsLocalizedModule.Away t.1 ((e t).toLinearMap ∘ₗ π t) :=
    IsLocalizedModule.of_linearEquiv _ _ _
  have hcomp (t : s) : g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i)) =
      (e t).toLinearMap ∘ₗ π t := by
    ext c
    simp [g, e, π, Fintype.linearCombination_apply, algebraMap_smul]
  haveI H₄ (t : s) : IsLocalizedModule.Away t.1
      (g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i))) := by
    rw [hcomp t]; exact H₃ t
  refine bijective_of_isLocalized_span s hs (fun t => Ω[B t⁄k])
    (fun t => g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i))) (fun t => Ω[B t⁄k]) g
    (Fintype.linearCombination A fun i => dFun α (x i)) fun t => ?_
  have : IsLocalizedModule.map (.powers t.1)
      (g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i))) (g t)
      (Fintype.linearCombination A fun i => dFun α (x i)) = LinearMap.id := by
    refine IsLocalizedModule.linearMap_ext (.powers t.1)
      (g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i))) (g t) ?_
    rw [IsLocalizedModule.map_comp]
    rfl
  rw [this]
  exact Function.bijective_id

end GlobalTheory.TopForm.FrameBasis

namespace GlobalTheory.TopForm.FrameBasis

theorem exists_basis_of_isFrame : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (m : ℕ),
    SmoothOfRelativeDimension m p → ∀ (U : X.Opens) (x : Fin m → Γ(X, U)),
    GlobalTheory.TopForm.IsFrame (GlobalTheory.TopForm.dOn p x) →
    ∃ b : Module.Basis (Fin m) Γ(X, U) (GlobalTheory.TopForm.Omega (algX p U)),
      ∀ i, b i = GlobalTheory.TopForm.dFun (algX p U) (x i) := by
  intro k _ X p m hp U x hx
  have hU := hx.affine
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension m) p hp
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  haveI (t : (s : Set Γ(X, U))) := hU.isLocalization_basicOpen t.1
  have hbij : Function.Bijective
      (Fintype.linearCombination Γ(X, U) fun i => dFun (algX p U) (x i)) := by
    refine bijective_of_isLocalization_span (algX p U) x (s : Set Γ(X, U)) hs
      (fun t => Γ(X, X.basicOpen t.1)) fun t => ?_
    have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
      (h t t.2 Γ(X, X.basicOpen t.1))
    have e : (algebraMap Γ(X, U) Γ(X, X.basicOpen t.1)).comp (algX p U) =
        algX p (X.basicOpen t.1) := resG_comp_algX p (X.basicOpen_le t.1)
    have h₂ : (algX p (X.basicOpen t.1)).IsStandardSmoothOfRelativeDimension m := by
      rw [← resG_comp_algX p (X.basicOpen_le t.1)]
      exact h₁
    have hfr := (hx.res (hU.basicOpen t.1) (X.basicOpen_le t.1)).gen
    rw [resForm_dOn] at hfr
    have := bijective_of_isFreeGen _ h₂ _ hfr
    rw [e]
    exact this
  let eq := LinearEquiv.ofBijective _ hbij
  refine ⟨Module.Basis.ofEquivFun eq.symm, fun i => ?_⟩
  simp [eq, Module.Basis.coe_ofEquivFun, Fintype.linearCombination_apply, Pi.single_apply]

end GlobalTheory.TopForm.FrameBasis
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.AllWt (cuspW latW GoodW rankW)
open GlobalTheory.LevDesc (levDet secRing pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

namespace GlobalTheory

theorem levPh_injective_of_levDet_nonZeroDivisor : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (S : Subgroup (LevelAut Dw l)), 1 ≤ Dw.p + Dw.q → l.A.Coprime l.M → ∀ (χ : S →* (c.F)ˣ) (u : Rul Xo c), u ∈ secRing Xo c → (∀ f ∈ secRing Xo c, levDet Xo c S u * f = 0 → f = 0) → ∀ f ∈ secRing Xo c, (∀ h : S, GlobalTheory.LevDesc.levPh Xo c S χ u f h = 0) → f = 0 := by
  classical
  intro E _ _ _ H Dw l Xo c S hpq hA χ u hu hdet f hf hph
  have hact := GlobalTheory.LevDesc.isRightAct_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA
  have hdet' : (Matrix.of fun h g : S => GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA (h * g) ⟨u, hu⟩).det ∈
      nonZeroDivisors (secRing Xo c) := by
    have h1 := GlobalTheory.LevDesc.coe_det_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA ⟨u, hu⟩
    have hl : ∀ x : secRing Xo c,
        (Matrix.of fun h g : S => GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA (h * g) ⟨u, hu⟩).det * x = 0 → x = 0 := by
      intro x hx
      have h2 := congrArg Subtype.val hx
      simp only [Subalgebra.coe_mul, Subalgebra.coe_zero] at h2
      apply Subtype.ext
      refine hdet x x.2 ?_
      rw [← h1]
      exact h2
    rw [mem_nonZeroDivisors_iff]
    exact ⟨hl, fun x hx => hl x (by rw [mul_comm]; exact hx)⟩
  have key := (GlobalTheory.twistedTrace_equivariant_and_injective_of_groupDet S c.F (secRing Xo c)
    (GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA) hact.1 hact.2 χ ⟨u, hu⟩ hdet').2.1 ⟨f, hf⟩ (fun h => by
      have h3 := GlobalTheory.LevDesc.coe_tr_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA χ
        (⟨f, hf⟩ * GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA h ⟨u, hu⟩)
      rw [GlobalTheory.LevDesc.tr_apply] at h3
      apply Subtype.ext
      rw [h3]
      exact hph h)
  exact congrArg Subtype.val key

end GlobalTheory
end

section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.FlatTw

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

private theorem ideal_smul_map_le_of_mem {K M N : Type} [Field K]
    [AddCommGroup M] [Module K M] [Module (𝓞 K) M] [IsScalarTower (𝓞 K) K M]
    [AddCommGroup N] [Module K N] [Module (𝓞 K) N] [IsScalarTower (𝓞 K) K N]
    (ψ : M →ₗ[K] N) (L : Submodule (𝓞 K) M) (L' : Submodule (𝓞 K) N) (𝔞 : Ideal (𝓞 K))
    (h : ∀ b ∈ 𝔞, b ≠ 0 → ∀ f ∈ L, (b : K) • ψ f ∈ L') :
    𝔞 • L.map (ψ.restrictScalars (𝓞 K)) ≤ L' := by
  rw [Submodule.smul_le]
  rintro b hb _ ⟨f, hf, rfl⟩
  by_cases hb0 : b = 0
  · rw [hb0, zero_smul]
    exact L'.zero_mem
  · exact IsScalarTower.algebraMap_smul K b (ψ f) ▸ h b hb hb0 f hf

theorem degOn_add_rank_mul_degLo_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E) (B : Finset ℕ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → Even G.2 → (∀ p ∈ B, p.Prime) → IntOff B s.lo → GoodOn U x V dict Z G → degOn U x V dict Z G + (rankOn U Z G : ℝ) * (s.degLo - logSum B) ≤ degOn U x V dict Z (G + G₀) := by
  intro E _ _ _ H Dw l Xo c r U x D V dict Z G₀ s G B hU hG hB hInt hGood
  have : IsTotallyComplex c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => CompHt.conj_comp_ne (c := c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  -- Reuse the canonical scalar actions without unfolding the ambient rule space during inference.
  let pts := fun S [CommRing S] [Algebra c.F S] => FrPt Xo c S
  let _ : CommRing (Rul Xo c) := rulesCommRing pts
  let _ : Module c.F (Rul Xo c) := rulesModule pts
  let _ : SMul c.F (Rul Xo c) := rulesSMul pts
  let C := cuspOn U Z G
  let C' := cuspOn U Z (G + G₀)
  let _ : AddCommGroup C := Submodule.addCommGroup C
  let _ : AddCommGroup C' := Submodule.addCommGroup C'
  let fieldModule : Module c.F C := Submodule.module C
  let fieldModule' : Module c.F C' := Submodule.module C'
  let integerModule : Module (𝓞 c.F) C := subRulesModuleInt pts C
  let integerModule' : Module (𝓞 c.F) C' := subRulesModuleInt pts C'
  let _ : SMul c.F C := fieldModule.toSMul
  let _ : SMul c.F C' := fieldModule'.toSMul
  let _ : SMul (𝓞 c.F) C := integerModule.toSMul
  let _ : SMul (𝓞 c.F) C' := integerModule'.toSMul
  have : IsScalarTower (𝓞 c.F) c.F C := subRulesTower pts C
  have : IsScalarTower (𝓞 c.F) c.F C' := subRulesTower pts C'
  obtain ⟨a, 𝔞, ha, h𝔞, hint, hsum⟩ := GlobalTheory.T.exists_ideal_rounding_realExponents_badPrimes c.F B s.lo hB s.finite_lo hInt
  obtain ⟨φ, hφ, -, hlat, -⟩ := GlobalTheory.T.exists_linearEquiv_mul_twistingSection_integral E H Dw l Xo c r U x Z G₀ s G hG
  have ⟨hGood', hrk⟩ :=
    GlobalTheory.T.twistingSection_preserves_hermitianLattices_ranks E H Dw l Xo c r U x D V dict Z G₀ s G hU hG hGood
  have hna : ∀ σ : c.F →+* ℂ, 0 < ‖σ a‖ := fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 ha)
  set t : (c.F →+* ℂ) → ℝ := fun σ => ‖σ a‖ * s.cInf σ with ht
  have ht0 : ∀ σ, 0 < t σ := fun σ => mul_pos (hna σ) (s.cInf_pos σ)
  have htc : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ := fun σ => by
    simp only [ht, RingHom.comp_apply, Complex.norm_conj]
    rw [s.cInf_congr (CompHt.goodOf_conj σ)]
  let ψ : C ≃ₗ[c.F] C' := φ.trans (LinearEquiv.smulOfNeZero c.F C' a ha)
  have hN : ∀ σ f, normOn U x V dict Z (G + G₀) σ (ψ f) ≤ t σ * normOn U x V dict Z G σ f := by
    intro σ f
    have e : (ψ f : Rul Xo c) = a • ((f : Rul Xo c) * s.sig) :=
      congrArg (fun y : Rul Xo c => a • y) (hφ f)
    have hpet : petOn U x V dict Z (G + G₀) σ ((f : Rul Xo c) * s.sig) =
        s.cInf σ * petOn U x V dict Z G σ f :=
      GlobalTheory.T.petersson_norm_mul_twistingSection_eq_const_mul
        E H Dw l Xo c r U x Z G₀ s G hG f f.2.2 σ D (V (goodOf c σ)) (dict (goodOf c σ))
        (muOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z)
    change petOn U x V dict Z (G + G₀) σ (ψ f) ≤
      (‖σ a‖ * s.cInf σ) * petOn U x V dict Z G σ f
    rw [e, petOn_smul, hpet, mul_assoc]
  have hL := ideal_smul_map_le_of_mem ψ.toLinearMap (latOn U Z G) (latOn U Z (G + G₀)) 𝔞
    (fun b hb hb0 f hf => by
      have hb' : (b : c.F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hb0
      refine hlat ((b : c.F) * a) (mul_ne_zero hb' ha) (hint b hb hb0) f hf _ ?_
      exact congrArg (fun y : C' => (y : Rul Xo c))
        (@mul_smul c.F C' _ fieldModule'.toDistribMulAction.toMulAction.toSemigroupAction
          (b : c.F) a (φ f)).symm)
  have key := GlobalTheory.T.deg_add_le_deg_of_ideal_smul_le_alt c.F C C'
    (normOn U x V dict Z G) (normOn U x V dict Z (G + G₀)) ψ.toLinearMap t
    (latOn U Z G) (latOn U Z (G + G₀)) 𝔞 hGood.1 hGood'.1 ψ.injective ht0 htc hN
    hGood.2.1 hGood'.2.1 h𝔞 hL hrk
  have hlog : ∑ σ, Real.log (t σ) = ∑ σ : c.F →+* ℂ, Real.log ‖σ a‖ + ∑ σ, Real.log (s.cInf σ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => Real.log_mul (hna σ).ne' (s.cInf_pos σ).ne'
  have hdeg : s.degLo - logSum B ≤ -((∑ σ, Real.log (t σ)) / (Module.finrank ℚ c.F : ℝ)) -
      Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ c.F : ℝ) := by
    rw [hlog, add_div]
    unfold TwSec.degLo lineDeg logSum
    linarith only [hsum]
  exact le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hdeg (Nat.cast_nonneg _))) key

end GlobalTheory.FlatTw
end
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

theorem _root_.GlobalTheory.T.framed_dictionary_bound : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (x0 : ∀ k, Frame ((U σ).X k).Ψ D.R.r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), (∀ k, IsOrth ((U σ).X k) (x0 k) ∧ IsFundSet ((U σ).X k) (x0 k) (FF k)) → ∑ k, muF ((U σ).X k) (x0 k) (FF k) ≤ ENNReal.ofReal (massLev D.host.E D.R.r l.M) := by
  first | exact @GlobalTheory.LevGeo.MassLev.mass_components_le | exact GlobalTheory.LevGeo.MassLev.mass_components_le | (intros; apply GlobalTheory.LevGeo.MassLev.mass_components_le <;> assumption)
end

section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

theorem _root_.GlobalTheory.T.cuspForm_sup_norm_le_petersson_integral_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (M w : ℝ) (x0 : Frame X.Ψ r) (FF : Set (V (nd X.toData))), 0 < r → P ∈ X.SS la → 0 < M → (∑ τ, X.spread la τ) ≤ w → 0 < w → (∀ γ ∈ X.Γ, ∀ v ∈ X.L', (γ : Matrix (Fin r) (Fin r) E).mulVec v ∈ X.L') → (∀ v ∈ X.L', herm X.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ X.Γ, X.χ la γ = 1 ∧ ∀ τ : X.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.flowMat v τ ((M : ℂ) * τ.1 b)) → IsOrth X.toData x0 → IsFundSet X.toData x0 FF → ∀ y ∈ X.dom, ENNReal.ofReal (X.pnorm la P y ^ 2) ≤ ENNReal.ofReal (locConst E r w (epStar M (fdeg E) w X.k0)) * ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la P (cpt X.toData x0 z) ^ 2) ∂(muF X.toData x0) := by
  first | exact @GlobalTheory.supLoc_component | exact GlobalTheory.supLoc_component | (intros; apply GlobalTheory.supLoc_component <;> assumption)
end

section

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.isotropic_vector_lattice_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * x = 1 → ∀ (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ g : GLoc σ J v, ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ g = q * k ∧ ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1 := by
  intro F E _ _ _ _ _ σ hσ hU n J hJ x y hx hy L hL v hv hSD g
  letI := hL
  exact GlobalTheory.InertIwasawaUnram.main F E σ hσ hU n J hJ x y hx hy L (by first | exact hL | infer_instance) v hv hSD g
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

theorem _root_.GlobalTheory.T.range_adjoint_le_span_jX_image_ZHg : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → R.PGEquiv F → (∀ t, LinearMap.range (LinearMap.adjoint (R.Th t)) ≤ Submodule.span ℂ (R.jX t '' ((A3.A.fam.R t).ZHg A3.A.X : Set (A3.A.fam.R t).S.Forms))) ∧ ∀ i t, LinearMap.range (LinearMap.adjoint (R.thG i t)) ≤ Submodule.span ℂ (R.jV i t '' ((A3.A.fam.L i t).ZHg A3.A.X : Set (A3.A.fam.L i t).S.Forms)) := by
  first | exact @GlobalTheory.AdjBlockSpan.range_adjoint_le_span_good_block | exact GlobalTheory.AdjBlockSpan.range_adjoint_le_span_good_block | (intros; apply GlobalTheory.AdjBlockSpan.range_adjoint_le_span_good_block <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

theorem _root_.GlobalTheory.T.transfer_eigensystem_parts_three_levels_of_mult_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ s : ℕ, A.fam.Ok s → GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → GoodStable A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R → ∀ SF, GlobalTheory.Hk3.IsSF R SF → GlobalTheory.TrCopy.TRLev R F SF := by
  first | exact @GlobalTheory.TrLevMult.trLev_of_multEq | exact GlobalTheory.TrLevMult.trLev_of_multEq | (intros; apply GlobalTheory.TrLevMult.trLev_of_multEq <;> assumption)
end
