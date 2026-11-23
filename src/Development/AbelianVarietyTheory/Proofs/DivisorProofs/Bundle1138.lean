module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1102
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1109
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle004
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle029
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan
public import Formalism.QuotientMetricDivisors.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1106
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.RingTheory.Valuation.Integral
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle002
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.squareZeroLiftSystem_filtration_direct_summand : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Good s₀ → RhoBC hI hk s₀ → ∀ S' : Sys I π s₀, S'.Full hI → (∃ N, IsCompl (S'.K hI) N) → ∀ S : Sys I π s₀, (∃ N, IsCompl (S.K hI) N) ∧ S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) := by
  first | exact @GlobalTheory.LiftSys.summand_of_full | exact GlobalTheory.LiftSys.summand_of_full | (intros; apply GlobalTheory.LiftSys.summand_of_full <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_squareZeroLiftSystem_of_summand_reduction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Good s₀ → RhoBC hI hk s₀ → ∀ S' : Sys I π s₀, S'.Full hI → (∃ N, IsCompl (S'.K hI) N) → ∀ K : Submodule R (Cr hI π s₀), (∃ N, IsCompl K N) → K ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) → ∃ S : Sys I π s₀, S.K hI = K := by
  first | exact @GlobalTheory.LiftSys.exists_sys_of_summand | exact GlobalTheory.LiftSys.exists_sys_of_summand | (intros; apply GlobalTheory.LiftSys.exists_sys_of_summand <;> assumption)
end

section

open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

namespace GlobalTheory.PointGroup

theorem isIntegrallyClosedIn_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsIntegrallyClosedIn O C :=
  isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h => hv.exists_of_le_one
    (hv.isIntegral_iff_v_le_one.1 h)⟩

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]

theorem exists_form (hv : v.Integers O) (G : PDivGroup p O) (ζ : (PDivGroup.mu p O).Tate)
    (hζ : Function.Bijective fun a : ℤ_[p] => a • ζ) :
    ∃ B : G.Tate →ₗ[ℤ_[p]] G.dual.Tate →ₗ[ℤ_[p]] ℤ_[p], (∀ s χ, pairing G O s χ = B s χ • ζ) ∧
      Function.Bijective B ∧ Function.Bijective B.flip := by
  haveI := isIntegrallyClosedIn_of_integers hv
  let z := LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ_[p] _ ζ) hζ
  refine ⟨(pairing G O).compr₂ z.symm.toLinearMap, fun s χ => (z.apply_symm_apply _).symm, ?_, ?_⟩
  · exact (LinearEquiv.congrRight (M := G.dual.Tate) z.symm).bijective.comp (G.pairing_bijective C)
  · exact (LinearEquiv.congrRight (M := G.Tate) z.symm).bijective.comp (G.pairing_flip_bijective C)

theorem finite_tate (hv : v.Integers O) (G : PDivGroup p O) : Module.Finite ℤ_[p] G.Tate :=
  haveI := isIntegrallyClosedIn_of_integers hv
  G.finite_tate C

theorem free_tate (hv : v.Integers O) (G : PDivGroup p O) : Module.Free ℤ_[p] G.Tate :=
  haveI := isIntegrallyClosedIn_of_integers hv
  G.free_tate C

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O]
  {ε : PreTilt O p} {hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε}



variable [Algebra ℤ_[p] O]




end GlobalTheory.PointGroup
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

theorem _root_.GlobalTheory.T.nat_mul_integral_mem_cmLattice_prime_to : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (c : Ideal (OF E)) (y : (Af E)ˣ) (R : ℕ), l.Prime → OneOver l y → 0 < R → (R : OF E) ∈ c → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ x : E, IsIntegral ℤ x → ((M * R : ℕ) : E) * x ∈ lattice c y := by
  first | exact @GlobalTheory.HilbFam.LatDen.nat_mul_integral_mem_lattice | exact GlobalTheory.HilbFam.LatDen.nat_mul_integral_mem_lattice | (intros; apply GlobalTheory.HilbFam.LatDen.nat_mul_integral_mem_lattice <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.LatVal.CurveTransport

open GlobalTheory.EllipticCM GlobalTheory.ConjPoint WeierstrassCurve
open GlobalTheory.Idele
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsLatOf IsInvIdealOf)

variable {K : Type} [Field K] [NumberField K]

theorem isLatOf_iff {ι : K →+* ℂ} {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {Λ : PeriodPair} :
    IsLatOf ι 𝔞 Λ ↔ ∀ z, z ∈ Λ.lattice ↔ ∃ x ∈ 𝔞, ι x = z := by
  rw [IsLatOf, Set.ext_iff]
  rfl

theorem isInvIdealOf_inv_smul_one (t : (Af K)ˣ) :
    IsInvIdealOf t (t⁻¹ • (1 : FractionalIdeal (𝓞 K)⁰ K)) := by
  intro x
  rw [← algebraMap_mem_adelicIdeal (GlobalTheory.Idele.smul_ne_zero _ (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0)), ← mem_adelicIdeal_one_iff,
    ← mul_mem_adelicIdeal_smul t⁻¹ 1 ((t : Af K) * algebraMap K _ x), Units.inv_mul_cancel_left]

theorem mulEquiv_inv_mk (t : (Af K)ˣ) {x x' : K}
    (h : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v (((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) v) ≤ 1) :
    mulEquiv t⁻¹ (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0) rfl
      (Submodule.Quotient.mk x) = Submodule.Quotient.mk x' := by
  rw [mulEquiv_mk_eq_mk_iff_adelic]
  have e : ((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) x - algebraMap K (Af K) x' =
      ((t⁻¹ : (Af K)ˣ) : Af K) * -((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) := by
    rw [mul_neg, mul_sub, Units.inv_mul_cancel_left]
    ring
  rw [e, mul_mem_adelicIdeal_smul]
  exact neg_mem (mem_adelicIdeal_one_iff.2 h)

theorem exists_curve_torsTransport : ∀ {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K],
    Module.finrank ℚ K = 2 → ∀ (ι : K →+* ℂ) (Λ₀ : PeriodPair) (Ω₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 1 Λ₀ →
    Ω₀ ≠ 0 → letI : Algebra K ℂ := ι.toAlgebra;
    ∃ (X : WeierstrassCurve ℂ) (_ : X.IsElliptic)
      (ξ : (ℂ ⧸ GlobalTheory.EllipticCM.idealSub (1 : FractionalIdeal (𝓞 K)⁰ K)) ≃+ X.toAffine.Point),
      GlobalTheory.EllipticCM.IsAnalyticIso ξ ∧ ∀ (σ : ℂ ≃ₐ[K] ℂ) (t : (Af K)ˣ),
        GlobalTheory.EllipticCM.Transports σ t one_ne_zero ξ →
        ∃ (Λ₁ : PeriodPair) (Ω₁ : ℂ), TorsTransport ι σ.toRingEquiv t Λ₀ Λ₁ Ω₀ Ω₁ := by
  intro K _ _ _ _ ι Λ₀ Ω₀ hΛ₀ hΩ₀
  letI : Algebra K ℂ := ι.toAlgebra
  have hAlg : ∀ y : K, algebraMap K ℂ y = ι y := fun _ => rfl
  have hsubIff : ∀ {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {Λ : PeriodPair},
      (IsLatOf ι 𝔞 Λ ↔ ∀ z, z ∈ idealSub 𝔞 ↔ z ∈ Λ.lattice) := fun {𝔞 Λ} => by
    rw [isLatOf_iff]
    exact forall_congr' fun z => by rw [mem_idealSub]; exact Iff.comm
  let M := GlobalTheory.scalePeriods Λ₀ Ω₀ hΩ₀
  have hM : GlobalTheory.IsHomothetic Ω₀ Λ₀ M := GlobalTheory.isHomothetic_scalePeriods Λ₀ Ω₀ hΩ₀
  have hsub : ∀ z, z ∈ idealSub (1 : FractionalIdeal (𝓞 K)⁰ K) ↔ Ω₀ * z ∈ M.lattice := fun z => by
    rw [hM z]; exact hsubIff.1 hΛ₀ z
  obtain ⟨ξ, hξ, hξz⟩ := exists_isAnalyticIso (X := latticeCurve M) (C := 1) (one_smul _ _) hΩ₀ hsub
  refine ⟨latticeCurve M, inferInstance, ξ, hξ, fun σ t ht => ?_⟩
  obtain ⟨η, ⟨hη, hηx⟩, -⟩ := ht
  obtain ⟨L', g2, g3⟩ := GlobalTheory.CMRam.exists_conj_lattice σ.toRingEquiv M
  have h' : (1 : _root_.WeierstrassCurve.VariableChange ℂ) • (latticeCurve M).map (σ : ℂ →+* ℂ) = latticeCurve L' := by
    rw [one_smul]
    simp [latticeCurve, WeierstrassCurve.map, g2, g3, map_ofNat]
  obtain ⟨α, hα0, hα, hηα⟩ := hη.exists_mul h'
  let Λ₁ := GlobalTheory.scalePeriods L' α⁻¹ (inv_ne_zero hα0)
  have hΛ₁ : GlobalTheory.IsHomothetic α⁻¹ L' Λ₁ := GlobalTheory.isHomothetic_scalePeriods L' α⁻¹ (inv_ne_zero hα0)
  have hΛ₁' : GlobalTheory.IsHomothetic α Λ₁ L' := fun z => by
    rw [← hΛ₁ (α * z), ← mul_assoc, inv_mul_cancel₀ hα0, one_mul]
  have hlat1 : IsLatOf ι (t⁻¹ • 1) Λ₁ := hsubIff.2 fun z => by rw [hα, hΛ₁' z]
  refine ⟨Λ₁, α, hΩ₀, hα0, fun x => σ.commutes x, hΛ₀, ⟨_, isInvIdealOf_inv_smul_one t, hlat1⟩, ?_, ?_, ?_⟩
  · rw [div_eq_inv_mul, ← hM.g₂_eq, ← g2, hΛ₁'.g₂_eq, div_eq_inv_mul]
  · rw [div_eq_inv_mul, ← hM.g₃_eq, ← g3, hΛ₁'.g₃_eq, div_eq_inv_mul]
  · intro x x' hx hint
    have e := hηx (Submodule.Quotient.mk x)
    rw [mulEquiv_inv_mk t hint, torsionIncl_mk, torsionIncl_mk, hξz, hηα, hAlg, hAlg] at e
    have hxM : Ω₀ * ι x ∉ M.lattice := fun h => hx ((hM _).1 h)
    rw [latticePoint_of_notMem M hxM] at e
    have hx' : α * ι x' ∉ L'.lattice := by
      intro h
      rw [latticePoint_of_mem L' h, map_zero, variableChangePoint_some] at e
      exact _root_.WeierstrassCurve.Affine.Point.some_ne_zero _ e
    rw [latticePoint_of_notMem L' hx', variableChangePoint_some, variableChangePoint_some] at e
    change _root_.WeierstrassCurve.Affine.Point.some _ _ _ = _ at e
    rw [_root_.WeierstrassCurve.Affine.Point.some.injEq] at e
    simp [_root_.WeierstrassCurve.VariableChange.one_def] at e
    obtain ⟨e1, e2⟩ := e
    refine ⟨?_, ?_⟩
    · rw [div_eq_inv_mul, ← hM.weierstrassP_mul, div_eq_inv_mul, ← hΛ₁'.weierstrassP_mul]
      exact e1
    · rw [div_eq_inv_mul, ← hM.derivWeierstrassP_mul, div_eq_inv_mul, ← hΛ₁'.derivWeierstrassP_mul]
      rw [map_ofNat σ 2, div_left_inj' two_ne_zero] at e2
      exact e2

end GlobalTheory.LatVal.CurveTransport
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

set_option backward.isDefEq.respectTransparency false in
theorem exists_baseChange_spAlg_prod (R D : Type) [CommRing R] [CommRing D] [Algebra R D]
    (B : Over (Sp R)) [GrpObj B] (g : ℕ) :
    IsAbelianScheme B → SmoothOfRelativeDimension g B.hom →
      ∃ (B' : Over (Sp D)) (_ : GrpObj B') (π : B'.left ⟶ B.left)
        (q : B'.left ⟶ (SpAlg R D ⊗ B).left),
        IsGrpPullback B' B (spMap (algebraMap R D)) π ∧ IsAbelianScheme B' ∧
          SmoothOfRelativeDimension g B'.hom ∧ IsIso q ∧
          q ≫ (fst (SpAlg R D) B).left = B'.hom ∧ q ≫ (snd (SpAlg R D) B).left = π := by
  intro hA hg
  let f := spMap (algebraMap R D)
  refine ⟨(Over.pullback f).obj B, inferInstance, Limits.pullback.fst B.hom f,
    (Limits.pullbackSymmetry B.hom f).hom,
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback B f,
    GlobalTheory.isAbelianScheme_pullback_obj f B hA,
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (CategoryTheory.IsPullback.of_hasPullback B.hom f) hg,
    inferInstance, Limits.pullbackSymmetry_hom_comp_fst B.hom f,
    Limits.pullbackSymmetry_hom_comp_snd B.hom f⟩

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem archEx_continuous_det {r : ℕ} {Ψ : Finset (E →+* ℂ)} (τ : Ψ) :
    Continuous fun y : Frame Ψ r => (mat y τ).det :=
  Continuous.matrix_det (continuous_apply τ)

theorem archEx_continuousOn_horizGen {r : ℕ} (X : Data E r) (τ : X.Ψ) : ContinuousOn (horizGen τ) X.dom :=
  (archEx_continuous_det τ).continuousOn.inv₀ fun _ hy => (hy τ).1

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem archEx_relab_mem {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (τ : Psi H) (k : U.Comp) :
    relab c σ τ.1 ∈ (U.X k).Ψ := by
  refine ((hU.2.1 k).2 _).2 ?_
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  exact (congrArg σ (Subtype.ext τ.2)).trans hσ0

end SlopeTestRemainingChoices

end GlobalTheory.FlatCore

end
end

section

open NumberField GlobalTheory.AllWt

theorem _root_.GlobalTheory.T.maxSlope_sq_le_of_no_short_vector : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (La : ℝ), HasGram N → (∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x) → L.FG → L ≠ ⊥ → (∀ x ∈ L, x ≠ 0 → -La ≤ (∑ σ : K →+* ℂ, Real.log (N σ x)) / (Module.finrank ℚ K : ℝ)) → slopeMax_sq N L ≤ 2 * La + Real.log (Module.finrank K V : ℝ) + Real.log |(discr K : ℝ)| / (Module.finrank ℚ K : ℝ) := by
  first | exact @GlobalTheory.SlopeMink.slopeMax_sq_le_of_no_short | exact GlobalTheory.SlopeMink.slopeMax_sq_le_of_no_short | (intros; apply GlobalTheory.SlopeMink.slopeMax_sq_le_of_no_short <;> assumption)
end

section

open NumberField GlobalTheory.AllWt Module TensorProduct Matrix GlobalTheory.SlopeExt
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.SlopeGalois

theorem gram_ge {K K' V V' ι κ : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [Field K']
    [NumberField K'] [StarRing K'] [Algebra K K'] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K' V']
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {b : Basis ι K V} {X : InfinitePlace K → Matrix ι ι ℂ}
    {b' : Basis κ K' V'} {X' : InfinitePlace K' → Matrix κ κ ℂ} {N : (K →+* ℂ) → V → ℝ} {N' : (K' →+* ℂ) → V' → ℝ}
    (hG : IsGram b X N) (hG' : IsGram b' X' N') (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    (φ : V →ₛₗ[algebraMap K K'] V') (ht : ∀ σ' x, N' σ' (φ x) = N (σ'.comp (algebraMap K K')) x)
    {j : ℕ} (e : Fin j → V) (w : InfinitePlace K') :
    (Formalism.HN.gramPl b X (w.comap (algebraMap K K')) e).det.re ≤
      (Formalism.HN.gramPl b' X' w fun k => φ (e k)).det.re := by
  set σ := w.embedding.comp (algebraMap K K') with hσ
  have hv : w.comap (algebraMap K K') = InfinitePlace.mk σ := by
    rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  have hd : DenseRange σ := denseRange_of_not_isReal (IsTotallyComplex.complexEmbedding_not_isReal σ)
  have h1 : ∀ x : Fin j → K, N σ (∑ k, x k • e k) =
      1 * Formalism.HermitianLatticesTheory.cnorm (cols b' X' w (fun k => φ (e k)) *ᵥ fun k => σ (x k)) := fun x => by
    have h := ht w.embedding (∑ k, x k • e k)

    rw [← (hG' w).2, map_sum] at h
    simp only [map_smulₛₗ] at h
    rw [normAt_sum] at h
    rw [one_mul]
    exact h.symm
  rw [hv, gramPl_eq, gramPl_eq]
  refine le_of_le_of_eq ?_ (by rw [one_pow, one_mul] : (1 : ℝ) ^ (2 * j) * _ = _)
  rcases InfinitePlace.embedding_mk_eq σ with h | h
  · refine det_le_of_dense σ hd _ _ 1 fun x => (le_of_eq ?_).trans (h1 x).le
    have := normAt_sum b X (InfinitePlace.mk σ) e x
    rw [(hG _).2, h] at this
    rw [this]
  · set B := cols b X (InfinitePlace.mk σ) e with hB
    have h2 : ((B.map (starRingEnd ℂ))ᴴ * B.map (starRingEnd ℂ)).det.re = (Bᴴ * B).det.re := by
      have : (B.map (starRingEnd ℂ))ᴴ * B.map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix (Bᴴ * B) := by
        ext a c
        simp [Matrix.mul_apply]
      rw [this, ← RingHom.map_det, Complex.conj_re]
    rw [← h2]
    refine det_le_of_dense σ hd _ _ 1 fun x => (le_of_eq ?_).trans (h1 x).le
    have := normAt_sum b X (InfinitePlace.mk σ) e x
    rw [(hG _).2, h] at this
    rw [← hc]
    refine (this.trans ?_).symm
    unfold Formalism.HermitianLatticesTheory.cnorm
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.norm_conj]
    simp [Matrix.mulVec, dotProduct, hB]

end GlobalTheory.SlopeGalois
end
end

section

open NumberField

theorem _root_.GlobalTheory.T.covolumePerRank_le_neg_slope_scaled : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ), GlobalTheory.AllWt.HasGram N →
    ∀ (L : Submodule (𝓞 K) V) (d : ℕ), 0 < d → ∀ (b : Fin d → V), LinearIndependent K b →
    (∀ x ∈ L, x ∈ Submodule.span K (Set.range b)) →
    ∀ (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (s : ℝ), 0 < s → s ≤ 1 → (∀ v, IsUnit (X v).det) →
    (∀ v (c : Fin d → K), Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) X v c = s * N v.embedding (∑ k, c k • b k)) →
    Submodule.IsFullLattice K (L.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K))) →
    Formalism.DivisionValues.lcv X (L.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K))) / (d : ℝ) ≤ -GlobalTheory.AllWt.slope_sq N L := by
  first | exact @GlobalTheory.CovolCore.lcv_div_le_neg_slope_sq | exact GlobalTheory.CovolCore.lcv_div_le_neg_slope_sq | (intros; apply GlobalTheory.CovolCore.lcv_div_le_neg_slope_sq <;> first | assumption | exact (show Submodule.IsFullLattice _ _ from by assumption).toIsLattice)
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.TjCount

theorem Tj_complex_ne_zero_iff {L : Type} [Field L] (n : ℕ) (O : Subring L) (ϖ : L) (j : ℕ)
    (g : GL (Fin n) L) : Formalism.UG.Tj ℂ n O ϖ j g ≠ 0 ↔ Formalism.UG.Tj ℤ n O ϖ j g ≠ 0 := by
  unfold Formalism.UG.Tj
  rw [Set.indicator_apply_ne_zero, Set.indicator_apply_ne_zero]
  simp

theorem prod_le_pow (q n j : ℕ) (hq : 2 ≤ q) (hj : j ≤ n) :
    0 < ∏ i ∈ Finset.range j, ((q : ℤ) ^ (n - i) - 1) ∧
    ∏ i ∈ Finset.range j, ((q : ℤ) ^ (n - i) - 1) ≤ (q : ℤ) ^ (n * j) := by
  have hq1 : (1 : ℤ) < q := by exact_mod_cast (by omega : 1 < q)
  have hpos : ∀ i ∈ Finset.range j, (0 : ℤ) < (q : ℤ) ^ (n - i) - 1 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have : (1 : ℤ) < (q : ℤ) ^ (n - i) := one_lt_pow₀ hq1 (by omega)
    linarith
  refine ⟨Finset.prod_pos hpos, ?_⟩
  calc ∏ i ∈ Finset.range j, ((q : ℤ) ^ (n - i) - 1)
      ≤ ∏ _i ∈ Finset.range j, (q : ℤ) ^ n := by
        apply Finset.prod_le_prod₀ (fun i hi => (hpos i hi).le)
        intro i hi
        have : (q : ℤ) ^ (n - i) ≤ (q : ℤ) ^ n := pow_le_pow_right₀ hq1.le (Nat.sub_le n i)
        linarith
    _ = (q : ℤ) ^ (n * j) := by rw [Finset.prod_const, Finset.card_range, ← pow_mul]

theorem one_le_prod (q j : ℕ) (hq : 2 ≤ q) : 1 ≤ ∏ i ∈ Finset.range j, ((q : ℤ) ^ (i + 1) - 1) := by
  have hq1 : (1 : ℤ) < q := by exact_mod_cast (by omega : 1 < q)
  have h1 : ∀ i ∈ Finset.range j, (1 : ℤ) ≤ (q : ℤ) ^ (i + 1) - 1 := by
    intro i _
    have : (q : ℤ) ≤ (q : ℤ) ^ (i + 1) := by
      calc (q : ℤ) = (q : ℤ) ^ 1 := (pow_one _).symm
        _ ≤ (q : ℤ) ^ (i + 1) := pow_le_pow_right₀ hq1.le (by omega)
    linarith
  calc (1 : ℤ) = ∏ _i ∈ Finset.range j, (1 : ℤ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) h1

end GlobalTheory.TjCount


open GlobalTheory.TjCount in
theorem GlobalTheory.TjCount.tj_cosets_finite_card_le : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), Formalism.UG.IsUnifV E w ϖ → ∀ j ≤ n, {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) | Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0}.Finite ∧ Nat.card {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) // Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} ≤ Formalism.UG.qV E w ^ (n * j) := by
  intro E _ _ w n ϖ hϖ j hj
  have h := Formalism.UG.P.Tj_double_coset_decomposition E w n ϖ (GlobalTheory.LFun.mem_Ov_of_isUnifV hϖ) hϖ j hj
  have hq : 2 ≤ Formalism.UG.qV E w := GlobalTheory.LFun.one_lt_absNorm w
  have hcard : Nat.card {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) //
      Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} =
      Nat.card {x : GL (Fin n) (w.adicCompletion E) ⧸ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E w) |
        Formalism.UG.Tj ℤ n (Formalism.UG.Ov E w) ϖ j x.out ≠ 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Tj_complex_ne_zero_iff _ _ _ _ _)
  obtain ⟨hP, hB⟩ := prod_le_pow (Formalism.UG.qV E w) n j hq hj
  have hA := one_le_prod (Formalism.UG.qV E w) j hq
  rw [← hcard] at h
  set C := Nat.card {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) //
      Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} with hC
  have hCpos : 0 < C := by
    rcases Nat.eq_zero_or_pos C with h0 | h0
    · rw [h0] at h; simp at h; linarith
    · exact h0
  have hle : (C : ℤ) ≤ (Formalism.UG.qV E w : ℤ) ^ (n * j) := by
    have : (C : ℤ) ≤ (C : ℤ) * ∏ i ∈ Finset.range j, ((Formalism.UG.qV E w : ℤ) ^ (i + 1) - 1) :=
      le_mul_of_one_le_right (by positivity) hA
    linarith
  refine ⟨?_, by exact_mod_cast hle⟩
  have : Finite {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) //
      Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} := Nat.finite_of_card_ne_zero hCpos.ne'
  exact Set.finite_coe_iff.mp (by exact this)
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

theorem _root_.GlobalTheory.T.lastMapHalf_recNums_of_log_levelPrime_le : ∀ (CY CT : ℝ) (N : NumDatum) (X : Fields) (Pr : Primes X) (W : Wts X Pr.Word N.R) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)), WeightTie N W pl u δ → Sizes Pr W N.sc.a → GlobalTheory.Core.Ht2.SizeRowsS CY N δ → Real.log (Pr.T u : ℝ) ≤ CT * N.R.m * N.sc.L → 1 ≤ Pr.T u → Reads N eJ δ (Pr.T u) R → LastSide R CT (lastLog W u) := by
  first | exact @GlobalTheory.ColRows.LastSideProof.lastSide_of_logT_le | exact GlobalTheory.ColRows.LastSideProof.lastSide_of_logT_le | (intros; apply GlobalTheory.ColRows.LastSideProof.lastSide_of_logT_le <;> assumption)
end
