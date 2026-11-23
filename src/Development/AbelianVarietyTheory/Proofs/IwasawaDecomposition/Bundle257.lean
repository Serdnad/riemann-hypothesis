module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle004
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle191
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.EtaUnitArg

theorem denseRange_atInf_single {L : Type} [Field L] [NumberField L] (w : InfinitePlace L) :
    DenseRange (atInf w : Lˣ → (w.Completion)ˣ) := by
  classical
  have hs : Function.Surjective (fun u : ∀ v : InfinitePlace L, (v.Completion)ˣ => u w) := fun z =>
    ⟨Function.update (1 : ∀ v : InfinitePlace L, (v.Completion)ˣ) w z, by simp⟩
  exact hs.denseRange.comp (GlobalTheory.InfTypeLocal.denseRange_atInf L) (continuous_apply w)

open Classical in
theorem locInf_eq {L : Type} [Field L] [NumberField L] (w : InfinitePlace L) (z : (w.Completion)ˣ) :
    Units.map (Formalism.L2.NC.locInf w) z = infIdele L w z := by
  apply Units.ext
  rfl

theorem etaT_isUnitArg : ∀ {R : Ranks} (H : Host R) (χ : HChar H.E), IsEtaT H χ → ∀ (h : Formalism.L2.NC.HC H.E), h.χ = (χ : Ideles H.E →* ℂˣ) → ∀ (g : R.Psi), h.IsUnitArg (H.emb (g : R.GG)) := by
  intro R H χ hχ h hh g f hf hfE z
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hloc := (GlobalTheory.InfTypeLocal.infType_iff_local H.E (R.Psi) (embPsi H) hcm.bij χ.1 χ.2.1
    (fun _ => 1)).1 (fun k => hχ.inf k) g
  have key : (fun z : ((InfinitePlace.mk (H.emb (g : R.GG))).Completion)ˣ =>
      ((χ.1 (infIdele H.E _ z) : ℂˣ) : ℂ)) =
      fun z : ((InfinitePlace.mk (H.emb (g : R.GG))).Completion)ˣ =>
        f (z : (InfinitePlace.mk (H.emb (g : R.GG))).Completion) /
          ((‖f (z : (InfinitePlace.mk (H.emb (g : R.GG))).Completion)‖ : ℝ) : ℂ) := by
    refine (denseRange_atInf_single _).equalizer ?_ ?_ ?_
    · exact Units.continuous_val.comp (χ.2.1.comp (GlobalTheory.InfTypeLocal.continuous_infIdele _ _))
    · have h1 := hf.comp Units.continuous_val
      have h2 : ∀ u : ((InfinitePlace.mk (H.emb (g : R.GG))).Completion)ˣ,
          f (u : (InfinitePlace.mk (H.emb (g : R.GG))).Completion) ≠ 0 := fun u =>
        (_root_.map_ne_zero _).2 u.ne_zero
      exact h1.div (Complex.continuous_ofReal.comp h1.norm) fun u => by exact_mod_cast norm_ne_zero_iff.2 (h2 u)
    · funext k
      have e : f ((atInf _ k : ((InfinitePlace.mk (H.emb (g : R.GG))).Completion)ˣ) :
          (InfinitePlace.mk (H.emb (g : R.GG))).Completion) = H.emb (g : R.GG) k := by
        change f (algebraMap H.E _ (k : H.E)) = H.emb (g : R.GG) k
        rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
          Algebra.algebraMap_self_apply]
        exact hfE k
      simp only [Function.comp_apply]
      rw [e]
      have := hloc k
      exact this.trans (zpow_one _)
  rw [locInf_eq, hh]
  exact congrFun key z

end GlobalTheory.EtaUnitArg
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ProperCover

theorem isFractionRing_evaluation (X : Scheme.{0}) [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x = genericPoint X) (hxU : x ∈ U) :
    letI := (X.evaluation U x hxU).hom.toAlgebra
    IsFractionRing Γ(X, U) (X.residueField x) := by
  subst hx
  letI := (X.evaluation U _ hxU).hom.toAlgebra
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  let φ : X.functionField →+* X.residueField (genericPoint X) := (X.residue _).hom
  let e : X.functionField ≃ₐ[Γ(X, U)] X.residueField (genericPoint X) :=
    { RingEquiv.ofBijective φ ⟨φ.injective, X.residue_surjective _⟩ with
      commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv _ e

theorem evaluation_genericPoint_injective (X : Scheme.{0}) [IsIntegral X] (V : X.Opens)
    (hV : genericPoint X ∈ V) : Function.Injective (X.evaluation V (genericPoint X) hV) := by
  intro a b h
  apply germ_injective_of_isIntegral X _ hV
  let φ : X.functionField →+* X.residueField (genericPoint X) := (X.residue _).hom
  apply φ.injective
  exact h

theorem dim_le_of_residueDegree_pos {Z' Z : Scheme.{0}} [IsIntegral Z'] [IsIntegral Z]
    [IsLocallyNoetherian Z] (f : Z' ⟶ Z) [LocallyOfFiniteType f]
    (hg : f (genericPoint Z') = genericPoint Z) (hdeg : 0 < f.residueDegree (genericPoint Z')) :
    topologicalKrullDim Z' ≤ topologicalKrullDim Z := by
  have hd : ∀ {X : Scheme.{0}} (U : X.Opens), IsAffineOpen U →
      topologicalKrullDim (U : Set X) = ringKrullDim Γ(X, U) := fun {X} U hU => by
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(X, U))
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens (Opens.mem_top (f x))
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.1 Z'.isBasis_affineOpens (show x ∈ f ⁻¹ᵁ U from hxU)
  refine ⟨V, V.isOpen, hxV, ?_⟩
  refine le_trans ?_ (topologicalKrullDim_subspace_le Z (U : Set Z))
  rw [hd U hU, hd V hV]
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  have : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI := (f.appLE U V hVU).hom.toAlgebra
  have : Algebra.FiniteType Γ(Z, U) Γ(Z', V) := f.finiteType_appLE hU hV hVU
  have hηV : genericPoint Z' ∈ V :=
    ((genericPoint_spec Z').mem_open_set_iff V.isOpen).mpr ⟨x, trivial, hxV⟩
  have hyU : f (genericPoint Z') ∈ U := hVU hηV
  letI := (Z.evaluation U _ hyU).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint Z')).hom.toAlgebra
  letI : Algebra Γ(Z, U) (Z'.residueField (genericPoint Z')) :=
    (Z.evaluation U _ hyU ≫ f.residueFieldMap (genericPoint Z')).hom.toAlgebra
  haveI : IsScalarTower Γ(Z, U) (Z.residueField (f (genericPoint Z')))
      (Z'.residueField (genericPoint Z')) := IsScalarTower.of_algebraMap_eq' rfl
  haveI := isFractionRing_evaluation Z hU hg hyU
  have : Algebra.IsAlgebraic Γ(Z, U) (Z.residueField (f (genericPoint Z'))) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(Z, U))
  have : Module.Finite (Z.residueField (f (genericPoint Z'))) (Z'.residueField (genericPoint Z')) :=
    Module.finite_of_finrank_pos hdeg
  have : Algebra.IsAlgebraic Γ(Z, U) (Z'.residueField (genericPoint Z')) :=
    Algebra.IsAlgebraic.trans Γ(Z, U) (Z.residueField (f (genericPoint Z'))) _
  have hnat : f.appLE U V hVU ≫ Z'.evaluation V _ hηV =
      Z.evaluation U _ hyU ≫ f.residueFieldMap (genericPoint Z') := by
    rw [Scheme.evaluation_naturality, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp [Scheme.evaluation]
  let ψ : Γ(Z', V) →ₐ[Γ(Z, U)] Z'.residueField (genericPoint Z') :=
    { (Z'.evaluation V _ hηV).hom with
      commutes' := fun a => RingHom.congr_fun congr($(hnat).hom) a }
  have hψ : Function.Injective ψ := evaluation_genericPoint_injective Z' V hηV
  have hinj : Function.Injective (algebraMap Γ(Z, U) Γ(Z', V)) := by
    have h1 : Function.Injective (algebraMap Γ(Z, U) (Z'.residueField (genericPoint Z'))) := by
      rw [IsScalarTower.algebraMap_eq Γ(Z, U) (Z.residueField (f (genericPoint Z')))
        (Z'.residueField (genericPoint Z'))]
      exact (f.residueFieldMap (genericPoint Z')).hom.injective.comp (IsFractionRing.injective Γ(Z, U) _)
    intro a b h
    apply h1
    rw [← ψ.commutes, ← ψ.commutes, h]
  have : FaithfulSMul Γ(Z, U) Γ(Z', V) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Algebra.IsAlgebraic Γ(Z, U) Γ(Z', V) := Algebra.IsAlgebraic.of_injective ψ hψ
  exact GlobalTheory.ModelDom.ringKrullDim_le_of_isAlgebraic _ _

end GlobalTheory.ProperCover
end
end
