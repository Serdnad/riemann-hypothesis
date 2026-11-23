module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle293
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle556
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Mathlib.Algebra.Module.StablyFree.Basic
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle014
import Formalism.LocalRingCardinality.DataHost
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle699
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle681
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwChiGal

open GlobalTheory.GalChar (IsGal toQ inQ block)

theorem firstTwistCharacter_eq_ladic_heckeCharacter : ∀ (D : D7) (cf : CharFrame D) (chiD : Formalism.L2.NC.NChiData D), Formalism.L2.NC.NormalizedCharacterCompatibility D chiD → (∀ x, chiD.etaT.χ x = cf.eta.1 x) → (∀ (j : Fin D.R.m) x, (chiD.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x) → (∀ s x, (chiD.del s).χ x = (cf.delAt (D.ntw.l s)).1 x) → ValLL0 D cf → ∀ (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ (i : D.ntw.Tw) (b : Bool) (ρ : GlobalTheory.Triple.Reading D.ntw i b) (j : Fin D.R.m), ∃ n, GlobalTheory.GalChar.IsGal art ρ.κ ρ.ι (GlobalTheory.Triple.blockChar cf (D.ntw.l i) j) n (D.ntw.chi1 i (j.1 + 1) b) := by
  intro D cf chiD T hEta hMu hDel hC art ha i b ρ j
  obtain ⟨χ', n, h'⟩ := GlobalTheory.Triple.exists_blockChar ha hC ρ j
  have hj1 : 1 ≤ j.1 + 1 := Nat.le_add_left 1 j.1
  have hj2 : j.1 + 1 ≤ D.R.m := j.2
  obtain ⟨B1, hB1⟩ := T.chi1 i (j.1 + 1) b hj1 hj2
  have hχ : ∀ x, (chiD.firstHeckeCharacter i (j.1 + 1)).χ x = (cf.mu0 j * cf.delAt (D.ntw.l i) * cf.eta⁻¹).1 x := by
    intro x
    change (chiD.mu0 (j.1 + 1)).χ x * (chiD.del i).χ x * (chiD.etaT.χ x)⁻¹ =
      (cf.mu0 j).1 x * (cf.delAt (D.ntw.l i)).1 x * (cf.eta.1 x)⁻¹
    rw [hMu j x, hDel i x, hEta x]
  set χb := GlobalTheory.Triple.blockChar cf (D.ntw.l i) j with hχb
  have hev : ∀ᶠ P in Filter.cofinite, P ∉ B1 := Filter.eventually_cofinite.2 (by simpa using B1.finite_toSet)
  have hc1 : Continuous (inQ ρ.κ (D.ntw.chi1 i (j.1 + 1) b)) :=
    GlobalTheory.GalChar.continuous_units _ ((GlobalTheory.GalChar.isEmbedding_toQ (D.ntw.twistBaseCoefficientRing_isAdic i) ρ.κ_alg).continuous.comp
      (D.ntw.twistCharacterFamily_continuous i (j.1 + 1) b))
  have e : inQ ρ.κ χ' = inQ ρ.κ (D.ntw.chi1 i (j.1 + 1) b) := by
    refine GlobalTheory.GalChar.eq_of_frob ha (h'.cont (D.ntw.twistBaseCoefficientRing_isAdic i) ρ.κ_alg) hc1 ?_
    filter_upwards [hev, GlobalTheory.GalChar.unr_ae χb,
      GlobalTheory.GalChar.away_ae (E := D.host.E) (D.ntw.l i) (D.ntw.lPrime i).out.ne_zero] with v hv hu hl A hA σ hσ
    refine GlobalTheory.ChiLocGal.frob_any (D.nd.plOm.2 v) hA (fun σ' hσ' => ?_) hσ
    obtain ⟨α, hα, x, hx, hσx⟩ := hB1 v hv
    have hval : ((χb.val v : ℂˣ) : ℂ) = (Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D x)⁻¹ :=
      GlobalTheory.ChiLocGal.val_block (GlobalTheory.ChiLocGal.val_of_at hχ hα) hx
    have e1 := h'.frob ha (Or.inl hl) hu (D.nd.plOm.2 v) hσ'
    rw [hval, inv_inv] at e1
    apply Units.ext
    apply ρ.ι.injective
    show ρ.ι (toQ ρ.κ (χ' σ' : (D.ntw.O0 i)ˣ)) = ρ.ι (toQ ρ.κ (D.ntw.chi1 i (j.1 + 1) b σ' : (D.ntw.O0 i)ˣ))
    rw [e1]
    show Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D x = ρ.ι (ρ.κ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))
      (D.ntw.chi1 i (j.1 + 1) b σ' : (D.ntw.O0 i)ˣ)))
    rw [hσx σ' hσ']
    exact (ρ.read x).symm
  have : χ' = D.ntw.chi1 i (j.1 + 1) b := MonoidHom.ext fun g => GlobalTheory.GalChar.inQ_inj ρ.κ (DFunLike.congr_fun e g)
  exact ⟨n, this ▸ h'⟩

end GlobalTheory.TwChiGal

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TripInhab

open GlobalTheory.Triple GlobalTheory.EigTie
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf GalE)
open GlobalTheory.TwistAbove (twGL)

theorem isInv_twGL_iff {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K)
    (W : Submodule K (Fin a → K)) : IsInv (twGL χ r) W ↔ IsInv r W := by
  constructor
  · intro h g v hv
    have := W.smul_mem (((χ g)⁻¹ : Kˣ) : K) (h g v hv)
    rwa [GlobalTheory.TwistAbove.twGL_val, Matrix.smul_mulVec, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul] at this
  · intro h g v hv
    rw [GlobalTheory.TwistAbove.twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem isSSRep_twGL {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K)
    (h : IsSSRep r) : IsSSRep (twGL χ r) := fun W hW =>
  let ⟨W', h1, h2⟩ := h W ((isInv_twGL_iff χ r W).1 hW)
  ⟨W', (isInv_twGL_iff χ r W').2 h1, h2⟩

variable {D : D7} {C : CharFrame D} {art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om}

end GlobalTheory.TripInhab

namespace GlobalTheory.TripInhab

open GlobalTheory.Triple GlobalTheory.EigTie
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf GalE)
open GlobalTheory.TwistAbove (twGL)

end GlobalTheory.TripInhab

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResidueUnit

theorem card_residueField_coprime {E : Type} [Field E] [NumberField E] (PP : Pl E) (l : ℕ) (hl : l.Prime)
    (hPP : ((l : ℕ) : 𝓞 E) ∉ PP.asIdeal) : Nat.Coprime (Nat.card (kP PP)) l := by
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  letI : Field (kP PP) := Ideal.Quotient.field PP.asIdeal
  haveI : Finite (kP PP) := PP.asIdeal.finiteQuotientOfFreeOfNeBot PP.ne_bot
  letI : Fintype (kP PP) := Fintype.ofFinite _
  obtain ⟨n, hp, hcard⟩ := FiniteField.card (kP PP) (ringChar (kP PP))
  rw [Nat.card_eq_fintype_card, hcard]
  refine Nat.Coprime.pow_left _ ((Nat.coprime_primes hp hl).2 ?_)
  intro hpl
  apply hPP
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h0 : ((ringChar (kP PP) : ℕ) : kP PP) = 0 := ringChar.Nat.cast_ringChar
  rw [hpl] at h0
  simpa using h0

theorem natCast_mem_maximalIdeal_of_finite {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A]
    [IsLocalRing A] [Algebra O A] [Module.Finite O A] (l : ℕ) (hl : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) :
    ((l : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
  haveI : Algebra.IsIntegral O A := Algebra.IsIntegral.of_finite O A
  have hmax : ((IsLocalRing.maximalIdeal A).comap (algebraMap O A)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (IsLocalRing.maximalIdeal A)
  have heq := IsLocalRing.eq_maximalIdeal hmax
  have : ((l : ℕ) : O) ∈ (IsLocalRing.maximalIdeal A).comap (algebraMap O A) := heq ▸ hl
  simpa using this

theorem isUnit_of_coprime {A : Type} [CommRing A] [IsLocalRing A] (q l : ℕ) (h : Nat.Coprime q l)
    (hl : ((l : ℕ) : A) ∈ IsLocalRing.maximalIdeal A) : IsUnit ((q : ℕ) : A) := by
  have hc : IsCoprime ((q : ℤ)) ((l : ℤ)) := Nat.isCoprime_iff_coprime.2 h
  obtain ⟨a, b, hab⟩ := hc
  by_contra hq
  have hq' : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).2 hq
  apply (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((a : A) * ((q : ℕ) : A) + (b : A) * ((l : ℕ) : A)) = 1 := by
    have := congrArg (Int.cast : ℤ → A) hab
    push_cast at this
    exact this
  rw [← h1]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq') (Ideal.mul_mem_left _ _ hl)

end GlobalTheory.ResidueUnit


open GlobalTheory.ResidueUnit in
theorem GlobalTheory.ResidueUnit.isUnit_card_residueField_Ok {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)
    (i : X.Tw) (k : ℕ) (PP : Pl D.host.E) :
    PP ∉ X.S0 i → IsUnit ((Nat.card (kP PP) : ℕ) : X.Ok i k) := by
  intro hP
  have hl : ((X.l i : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun h => hP (X.twistExcludedPlaces_contains_residueChar i h)
  haveI := X.Ok_fin i k
  exact isUnit_of_coprime _ _ (card_residueField_coprime PP (X.l i) (X.lPrime i).out hl)
    (natCast_mem_maximalIdeal_of_finite (O := X.O i) (X.l i) (X.O_l i))
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.NX

noncomputable section

namespace GlobalTheory

theorem exists_desc_of_isKsForm : ∀ (D : D7) (S : RatDat D.ntw) (j : ℕ), (S.A j).IsKsForm → ∀ (i : D.ntw.Tw) (b : Bool) (x : S.WL j), x ≠ 0 →
    ∃ Φ : S.WL j →+ Fm S i j b, Φ x ≠ 0 ∧
      (∀ (c : ↥D.LL0) (w : S.WL j), Φ (((c : ↥D.LL0) : D.what₂.LL) • w) = readLL0 S i b c • Φ w) ∧
      ∀ (T : Module.End D.what₂.LL (S.WL j)) (hT : ∀ w ∈ (S.A j).WK, T w ∈ (S.A j).WK) (w : S.WL j),
        Φ (T w) = Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j)
          ((T.restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) hT) (Φ w) := by
  intro D S j hK i b x hx
  classical
  obtain ⟨n, v, hvK, hliK, hspK, hliL, hspL⟩ := hK
  let bL : Module.Basis (Fin n) D.what₂.LL (S.WL j) := Module.Basis.mk hliL (by rw [hspL])
  let bK0 : Module.Basis (Fin n) S.Ks (Submodule.span S.Ks (Set.range v)) := Module.Basis.span hliK
  let bK : Module.Basis (Fin n) S.Ks (FmK S j) := bK0.map (LinearEquiv.ofEq _ _ hspK)
  let ι : FmK S j →ₗ[S.Ks] S.WL j := (S.A j).WK.subtype
  have hbK : ∀ r, ι (bK r) = v r := by
    intro r
    show ((bK0 r : Submodule.span S.Ks (Set.range v)) : S.WL j) = v r
    exact congrArg Subtype.val (Module.Basis.span_apply hliK r)
  have hbL : ∀ r, bL r = v r := by intro r; simp [bL]
  let bF : Module.Basis (Fin n) (KB S i b) (Fm S i j b) := Algebra.TensorProduct.basis (KB S i b) bK
  obtain ⟨r0, ha⟩ : ∃ r0, bL.repr x r0 ≠ 0 := by
    by_contra h; push_neg at h; exact hx (bL.ext_elem fun r => by simpa using h r)
  obtain ⟨g, hg⟩ : ∃ g : Module.Dual ↥D.LL0 D.what₂.LL, g (bL.repr x r0) ≠ 0 := by
    by_contra h; push_neg at h; exact ha ((Module.forall_dual_apply_eq_zero_iff _ _).1 h)
  let f : D.what₂.LL →ₗ[↥D.LL0] ↥D.LL0 := (g (bL.repr x r0))⁻¹ • g
  have hfa : f (bL.repr x r0) = 1 := by simp [f, hg]
  have hfc : ∀ (c : ↥D.LL0) (y : D.what₂.LL), f ((c : D.what₂.LL) * y) = c * f y := by
    intro c y
    rw [show (c : D.what₂.LL) * y = c • y from (Algebra.smul_def c y).symm, map_smul, smul_eq_mul]
  let φ : (Fin n → D.what₂.LL) →+ (Fin n → KB S i b) :=
    AddMonoidHom.compLeft ((readLL0 S i b).toAddMonoidHom.comp f.toAddMonoidHom) (Fin n)
  let Φ : S.WL j →+ Fm S i j b :=
    (bF.equivFun.symm.toLinearMap.toAddMonoidHom).comp (φ.comp bL.equivFun.toLinearMap.toAddMonoidHom)
  have hΦ : ∀ w, bF.equivFun (Φ w) = fun r => readLL0 S i b (f (bL.repr w r)) := by
    intro w
    show bF.equivFun (bF.equivFun.symm (φ (bL.equivFun w))) = _
    rw [LinearEquiv.apply_symm_apply]; rfl
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro h0
    have := congrFun (hΦ x) r0
    rw [h0, map_zero, hfa, map_one] at this
    exact zero_ne_one this
  · intro c w
    apply bF.equivFun.injective
    rw [hΦ, bF.equivFun.map_smul, hΦ, bL.repr.map_smul]
    funext r
    simp only [Pi.smul_apply, smul_eq_mul, map_smul, Finsupp.smul_apply]
    rw [hfc, map_mul]
  · intro T hT w
    let T' : Module.End S.Ks (FmK S j) := (T.restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) hT
    let t := LinearMap.toMatrix bK bK T'
    have hTm : LinearMap.toMatrix bL bL T = t.map (algebraMap S.Ks D.what₂.LL) := by
      ext r q
      simp only [t, LinearMap.toMatrix_apply, Matrix.map_apply]
      have e1 : T (bL q) = ι (T' (bK q)) := by
        rw [hbL, ← hbK]; rfl
      have e2 : T (bL q) = ∑ s, (algebraMap S.Ks D.what₂.LL (bK.repr (T' (bK q)) s)) • bL s := by
        rw [e1]; conv_lhs => rw [← bK.sum_repr (T' (bK q))]

        rw [map_sum]; refine Finset.sum_congr rfl fun s _ => ?_
        rw [map_smul, hbK, hbL, algebraMap_smul]
      rw [e2, Module.Basis.repr_sum_self]
    apply bF.equivFun.injective
    have hbc : Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) T' = LinearMap.baseChange (KB S i b) T' := rfl
    change bF.equivFun (Φ (T w)) = bF.equivFun (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) T' (Φ w))
    rw [hbc]
    have hMF : LinearMap.toMatrix bF bF (LinearMap.baseChange (KB S i b) T') = t.map (algebraMap S.Ks (KB S i b)) :=
      LinearMap.toMatrix_baseChange _ _ _ _
    have hL : ∀ r, bL.repr (T w) r = ∑ q, algebraMap S.Ks D.what₂.LL (t r q) * bL.repr w q := by
      intro r
      rw [← LinearMap.toMatrix_mulVec_repr bL bL T w, hTm]; rfl
    have hKB : ∀ r, bF.equivFun (LinearMap.baseChange (KB S i b) T' (Φ w)) r =
        ∑ q, algebraMap S.Ks (KB S i b) (t r q) * bF.equivFun (Φ w) q := by
      intro r
      have h1 := congrFun (LinearMap.toMatrix_mulVec_repr bF bF (LinearMap.baseChange (KB S i b) T') (Φ w)) r
      rw [hMF] at h1
      exact h1.symm
    funext r
    rw [hΦ, hKB, hΦ]
    simp only []

    rw [hL, map_sum, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← S.kKs_spec, hfc, map_mul]; rfl

end GlobalTheory
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory

theorem adicIntegers_red_eq_zero_iff {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (g : ℕ) (hg : g.Prime)
    (red : v.adicCompletionIntegers K →+* ZMod g) (y : v.adicCompletionIntegers K) :
    red y = 0 ↔ Valued.v (y : v.adicCompletion K) < 1 := by
  have : Fact g.Prime := ⟨hg⟩
  have hker : RingHom.ker red = IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective red (ZMod.ringHom_surjective red))
  rw [← RingHom.mem_ker, hker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  exact ⟨fun h => lt_of_le_of_ne y.2 h, ne_of_lt⟩

theorem exists_ringHom_adicIntegers {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) {R : Type} [CommRing R] (f : R →+* v.adicCompletion K)
    (hf : ∀ a, Valued.v (f a) ≤ 1) :
    ∃ j : R →+* v.adicCompletionIntegers K, ∀ a, (j a : v.adicCompletion K) = f a :=
  ⟨f.codRestrict (v.adicCompletionIntegers K) hf, fun _ => rfl⟩

theorem zmod_iso_comp_eq_mk {R : Type} [CommRing R] (I : Ideal R) (g : ℕ) (φ : R →+* ZMod g)
    (hφ : ∀ a ∈ I, φ a = 0) (iso : ZMod g ≃+* R ⧸ I) (u : R) :
    iso (φ u) = Ideal.Quotient.mk I u := by

  have hid : (Ideal.Quotient.lift I φ hφ).comp (iso : ZMod g →+* R ⧸ I) = RingHom.id (ZMod g) :=
    Subsingleton.elim _ _
  have h : φ u = iso.symm (Ideal.Quotient.mk I u) := by
    simpa using congrArg (fun F : ZMod g →+* ZMod g => F (iso.symm (Ideal.Quotient.mk I u))) hid
  rw [h, RingEquiv.apply_symm_apply]

theorem adicIntegers_red_eq_iff {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (g : ℕ) (hg : g.Prime)
    (red : v.adicCompletionIntegers K →+* ZMod g) (y x : v.adicCompletionIntegers K) :
    Valued.v ((y : v.adicCompletion K) - (x : v.adicCompletion K)) < 1 ↔ red x = red y := by
  have h := adicIntegers_red_eq_zero_iff v g hg red (y - x)
  rw [map_sub, sub_eq_zero] at h
  exact h.symm.trans eq_comm

theorem splitPlace_red_eq_reduction : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (g : ℕ), g.Prime → ∀ (red : s.v.adicCompletionIntegers (maximalRealSubfield L) →+* ZMod g) (iso : ZMod g ≃+* kP s.w) (x : s.v.adicCompletionIntegers (maximalRealSubfield L)) (u : 𝓞 L), Valued.v (s.i (u : L) - (x : s.v.adicCompletion (maximalRealSubfield L))) < 1 ↔ iso (red x) = Ideal.Quotient.mk s.w.asIdeal u := by
  intro L _ _ _ s g hg red iso x u

  obtain ⟨j, hj⟩ := exists_ringHom_adicIntegers s.v
    ((s.i : L →+* s.v.adicCompletion (maximalRealSubfield L)).comp (algebraMap (𝓞 L) L))
    (fun a => s.split_le_one a)
  have hj' : ∀ a : 𝓞 L, (j a : s.v.adicCompletion (maximalRealSubfield L)) = s.i (a : L) :=
    fun a => hj a

  have hφ : ∀ a ∈ s.w.asIdeal, (red.comp j) a = 0 := by
    intro a ha
    have hlt : Valued.v (s.i (a : L)) < 1 := (s.split_mem_ideal a).1 ha
    exact (adicIntegers_red_eq_zero_iff s.v g hg red (j a)).2 (by rw [hj' a]; exact hlt)
  have key := zmod_iso_comp_eq_mk s.w.asIdeal g (red.comp j) hφ iso u
  have h4 := adicIntegers_red_eq_iff s.v g hg red (j u) x
  rw [hj' u] at h4
  rw [← key, iso.injective.eq_iff]
  exact h4

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.AlgSubrep

theorem toMatrix_sandwich {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι ℂ V) (e : Module.Basis κ ℂ U) (π : V →ₗ[ℂ] U) (s : U →ₗ[ℂ] V)
    (f : V →ₗ[ℂ] V) :
    LinearMap.toMatrix e e (π ∘ₗ f ∘ₗ s) =
      LinearMap.toMatrix b e π * LinearMap.toMatrix b b f * LinearMap.toMatrix e b s := by
  rw [LinearMap.toMatrix_comp e b e, LinearMap.toMatrix_comp e b b, Matrix.mul_assoc]

theorem eval_sandwich {ι κ σ : Type} [Fintype ι] [Fintype κ] (A : Matrix κ ι ℂ) (B : Matrix ι κ ℂ)
    (P : ι → ι → MvPolynomial σ ℂ) (x : σ → ℂ) (M : Matrix ι ι ℂ)
    (hM : M = fun k l => MvPolynomial.eval x (P k l)) :
    A * M * B =
      fun i j => MvPolynomial.eval x (∑ k, ∑ l, MvPolynomial.C (A i k) * P k l * MvPolynomial.C (B l j)) := by
  funext i j
  simp only [Matrix.mul_apply, Finset.sum_mul]
  subst hM
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  rw [Finset.sum_comm]

end GlobalTheory.AlgSubrep

namespace GlobalTheory.AlgSubrep

theorem isAlgWeight_subrep (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) V)
    (hρ : Formalism.AUTREP.IsAlgWeight L n ρ) (S : Subrepresentation ρ) :
    Formalism.AUTREP.IsAlgWeight L n S.toRepresentation := by
  classical
  obtain ⟨hfin, ι, _, _, b, P, hP⟩ := hρ
  haveI := hfin
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl S.toSubmodule
  let π : V →ₗ[ℂ] S.toSubmodule := Submodule.linearProjOfIsCompl S.toSubmodule C hC
  let e := Module.Free.chooseBasis ℂ S.toSubmodule
  refine ⟨inferInstance, Module.Free.ChooseBasisIndex ℂ S.toSubmodule, inferInstance, inferInstance, e,
    fun i j => ∑ k, ∑ l, MvPolynomial.C (LinearMap.toMatrix b e π i k) * P k l *
      MvPolynomial.C (LinearMap.toMatrix e b S.toSubmodule.subtype l j), ?_⟩
  intro γ γ₀ hγ
  have hres : S.toRepresentation γ = π ∘ₗ ρ γ ∘ₗ S.toSubmodule.subtype := by
    ext x : 1
    have hm : ρ γ x ∈ S.toSubmodule := S.apply_mem_toSubmodule γ x.2
    have h1 := Submodule.linearProjOfIsCompl_apply_left hC ⟨ρ γ x, hm⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [show π (ρ γ ↑x) = _ from h1]
    apply Subtype.ext
    rfl
  have h4 := hP γ γ₀ hγ
  have h5 := toMatrix_sandwich b e π S.toSubmodule.subtype (ρ γ)
  exact (congrArg (LinearMap.toMatrix e e) hres).trans
    (h5.trans (eval_sandwich (LinearMap.toMatrix b e π) (LinearMap.toMatrix e b S.toSubmodule.subtype) P _ _ h4))
end GlobalTheory.AlgSubrep

namespace GlobalTheory.AlgSubrep

theorem exists_irreducible_algWt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [Nontrivial V] (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) V), Formalism.AUTREP.IsAlgWeight L n ρ → ∃ (a : NG.AlgWt L n) (j : a.W →ₗ[ℂ] V), Function.Injective j ∧ ∀ γ x, j (a.ρ γ x) = ρ γ (j x) := by
  intro L _ _ _ n V _ _ _ ρ hρ
  haveI := hρ.1
  obtain ⟨S, hS⟩ := GlobalTheory.PiIsotypic.exists_irreducible_subrep ρ
  exact ⟨⟨S.toSubmodule, S.toRepresentation, isAlgWeight_subrep L n ρ hρ S, hS⟩,
    S.toSubmodule.subtype, S.toSubmodule.injective_subtype, fun γ x => rfl⟩

end GlobalTheory.AlgSubrep
end
