module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle194
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveAlgebraic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsDlogFirstChernClass
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Topology.Sheaves.Presheaf
import GroundTheory.AutomorphicForms.GL2.GodementSection
import GroundTheory.AutomorphicForms.GL2.SummableNormIffAndTsumEqCoset2
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.GlobalFields.TateThesis.Bundle001
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle038
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem tensBasis : ∀ {K : Type} [Field K] {J : Type} [DecidableEq J] (V W : J → Type 1) [∀ t, AddCommGroup (V t)] [∀ t, Module K (V t)] [∀ t, AddCommGroup (W t)] [∀ t, Module K (W t)] (B : J → Type 1) [DecidableEq (Σ t, B t)] (b : ∀ t, Module.Basis (B t) K (V t)), ∃ e : (⨁ t, V t ⊗[K] W t) ≃ₗ[K] ⨁ u : (Σ t, B t), W u.1, ∀ (t : J) (β : B t) (x : W t), e (DirectSum.lof K J (fun t => V t ⊗[K] W t) t (b t β ⊗ₜ x)) = DirectSum.lof K (Σ t, B t) (fun u => W u.1) ⟨t, β⟩ x := by
  classical
  intro K _ J _ V W _ _ _ _ B _ b
  let et : ∀ t, (V t ⊗[K] W t) ≃ₗ[K] (Π₀ _ : B t, W t) := fun t =>
    (TensorProduct.congr (b t).repr (LinearEquiv.refl K (W t))) ≪≫ₗ
      (TensorProduct.finsuppScalarLeft K (W t) (B t)) ≪≫ₗ (finsuppLequivDFinsupp K)
  have het : ∀ t (β : B t) (x : W t), et t (b t β ⊗ₜ x) = DFinsupp.single β x := by
    intro t β x
    simp [et, TensorProduct.finsuppScalarLeft_apply_tmul, Module.Basis.repr_self]
  let C : (⨁ u : (Σ t, B t), W u.1) ≃ₗ[K] (Π₀ t, Π₀ _ : B t, W t) :=
    DFinsupp.sigmaCurryLEquiv (R := K) (M := fun t (_ : B t) => W t)
  refine ⟨(DFinsupp.mapRange.linearEquiv et) ≪≫ₗ C.symm, ?_⟩
  intro t β x
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
  have h1 : C (DirectSum.lof K (Σ t, B t) (fun u => W u.1) ⟨t, β⟩ x)
      = DFinsupp.single t (DFinsupp.single β x) := by
    have : DirectSum.lof K (Σ t, B t) (fun u => W u.1) ⟨t, β⟩ x
        = DFinsupp.single (⟨t, β⟩ : Σ t, B t) x := rfl
    rw [this]
    change DFinsupp.sigmaCurry (δ := fun t (_ : B t) => W t) (DFinsupp.single (⟨t, β⟩ : Σ t, B t) x) = _
    convert DFinsupp.sigmaCurry_single (δ := fun t (_ : B t) => W t) (⟨t, β⟩ : Σ t, B t) x
  rw [h1, ← het]
  exact DFinsupp.mapRange_single (hf := fun i => map_zero (et i))

end GlobalTheory.CompanionTheory.KunGlue
end

section

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.GodementSection IdeleGroup

namespace GlobalTheory.CompanionTheory.EisRankOne

theorem weakFEPair_Λ₀_of_smul (P Q : WeakFEPair ℂ) (c : ℂ) (hf : Q.f = c • P.f)
    (hg : Q.g = c • P.g) (hk : Q.k = P.k) (hε : Q.ε = P.ε) (hf₀ : Q.f₀ = c • P.f₀)
    (hg₀ : Q.g₀ = c • P.g₀) : Q.Λ₀ = c • P.Λ₀ := by
  have hmod : Q.f_modif = c • P.f_modif := by
    funext x
    simp only [WeakFEPair.f_modif, Pi.add_apply, Pi.smul_apply, Set.indicator_apply, hf, hf₀, hg₀, hk, hε,
      smul_eq_mul]
    split_ifs <;> ring
  funext s
  simp only [WeakFEPair.Λ₀, hmod, Pi.smul_apply]
  exact mellin_const_smul P.f_modif s c

end GlobalTheory.CompanionTheory.EisRankOne
end

section

open TensorProduct

namespace GlobalTheory.CompanionTheory.TensorCompleteFinite

open GlobalTheory.CompanionTheory.TensorComplete

theorem isAdicComplete_of_linearEquiv_univ {A : Type} [CommRing A] {π : A} {M : Type} {M' : Type 1}
    [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] (e : M ≃ₗ[A] M')
    (h : IsAdicComplete (Ideal.span {π}) M) : IsAdicComplete (Ideal.span {π}) M' := by
  have hM : ∀ (n : ℕ) (x : M), x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule A M) →
      e x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule A M') := by
    intro n x hx
    have h1 : (Ideal.span {π} ^ n • ⊤ : Submodule A M).map (e : M →ₗ[A] M') ≤
        Ideal.span {π} ^ n • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact h1 (Submodule.mem_map_of_mem hx)
  have hM' : ∀ (n : ℕ) (x : M'), x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule A M') →
      e.symm x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule A M) := by
    intro n x hx
    have h1 : (Ideal.span {π} ^ n • ⊤ : Submodule A M').map (e.symm : M' →ₗ[A] M) ≤
        Ideal.span {π} ^ n • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact h1 (Submodule.mem_map_of_mem hx)
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have h0 : e.symm x = 0 := by
      refine h.toIsHausdorff.haus' (e.symm x) (fun n => ?_)
      rw [SModEq.sub_mem, sub_zero]
      have hx' := (SModEq.sub_mem).mp (hx n)
      rw [sub_zero] at hx'
      exact hM' n x hx'
    simpa using congrArg e h0
  · intro f hf
    obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec' (fun n => e.symm (f n)) (fun {m n} hmn => by
      rw [SModEq.sub_mem, ← map_sub]
      exact hM' m _ ((SModEq.sub_mem).mp (hf hmn)))
    refine ⟨e L, fun n => ?_⟩
    rw [SModEq.sub_mem]
    have h2 := hM n _ ((SModEq.sub_mem).mp (hL n))
    rwa [map_sub, LinearEquiv.apply_symm_apply] at h2

theorem isAdicComplete_tensor_finite : ∀ (W : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] (l : ℕ), Irreducible (l : W) →
    ∀ (A : Type) [CommRing A] [Algebra W A] [IsAdicComplete (Ideal.span {(l : A)}) A]
      (L : Type 1) [AddCommGroup L] [Module W L] [Module.Finite W L],
      IsAdicComplete (Ideal.span {(l : A)}) (A ⊗[W] L) := by
  intro W _ _ _ l hl A _ _ hA L _ _ _
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hl.ne_zero Nat.cast_zero
  obtain ⟨p, hpmem, hpu⟩ : ∃ p ∈ l.primeFactorsList, ¬IsUnit (p : W) := by
    by_contra hcon
    push_neg at hcon
    apply hl.1
    rw [← Nat.prod_primeFactorsList hl0, Nat.cast_list_prod]
    refine List.prod_isUnit (fun m hm => ?_)
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact hcon q hq
  have hp : p.Prime := Nat.prime_of_mem_primeFactorsList hpmem
  obtain ⟨m, hm⟩ := Nat.dvd_of_mem_primeFactorsList hpmem
  have hmu : IsUnit (m : W) := by
    have h := hl.isUnit_or_isUnit (show (l : W) = (p : W) * (m : W) by rw [hm, Nat.cast_mul])
    exact h.resolve_left hpu
  have hmA : IsUnit (m : A) := by
    have h := hmu.map (algebraMap W A)
    rwa [map_natCast] at h
  have hI : Ideal.span {(l : A)} = Ideal.span {(p : A)} := by
    rw [hm, Nat.cast_mul, Ideal.span_singleton_mul_right_unit hmA]
  have hp0 : (p : W) ≠ 0 := by
    intro h
    apply hl.ne_zero
    rw [hm, Nat.cast_mul, h, zero_mul]
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hA' : IsAdicComplete (Ideal.span {(p : A)}) A := by
    rw [← hI]
    exact hA
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' W L
  have hN := isAdicComplete_tensor p W A hp0 hpu ((Fin n → W) ⧸ LinearMap.ker f)
  rw [hI]
  exact isAdicComplete_of_linearEquiv_univ
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A)
      (f.quotKerEquivOfSurjective hf)) hN

end GlobalTheory.CompanionTheory.TensorCompleteFinite
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Relevant

theorem exists_coord_ne_zero :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (D : ℕ), IsArithVar (mCoordIdeal y) (D + 1) → ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
  intro K _ ι _ Ω _ _ y D hP k
  obtain ⟨i, hi⟩ := hP.2.1.2.2 k
  exact ⟨i, fun h0 => hi (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.X_mem_of_eq_zero h0)⟩

end GlobalTheory.CompanionTheory.Ar.Relevant
end

section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Axis

theorem exists_abelianScheme_baseChange_ringHom :
    ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ (A' : Over (Sp R')) (_ : GrpObj A') (φ : A'.left ⟶ A.left), IsAbelianScheme A' ∧
      SmoothOfRelativeDimension g A'.hom ∧ IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) := by
  intro R R' _ _ _ A _ g hA hg
  exact ⟨(Over.pullback (spMap (algebraMap R R'))).obj A, Functor.grpObjObj,
    Limits.pullback.fst A.hom (spMap (algebraMap R R')),
    GlobalTheory.AbLaw.CubeGen.isAb_baseChange hA _,
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback _ _) hg,
    IsPullback.of_hasPullback _ _⟩

end GlobalTheory.CompanionTheory.Axis
end
