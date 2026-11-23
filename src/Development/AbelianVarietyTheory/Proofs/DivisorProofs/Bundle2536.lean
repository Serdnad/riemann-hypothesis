module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle642
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle539
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeomRegFibAdicCompletionOfEssFiniteTypeInt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.RingKrullDimQuotientSpanSingletonAddOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle020
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle978
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2529
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
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Std.Tactic.BVDecide.Normalize.BitVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isFinite_iff_tateModuleMap_injective_and_isogeny_iff : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A B : AbVar K) (f : A ⟶ B), (IsFinite f.hom.left ↔ Function.Injective (tmap l A B f)) ∧ (IsIsogeny f ↔ Function.Bijective (vmap l f)) := by
  first | exact @GlobalTheory.AV.AbVar.isFinite_iff_tmap_injective_and_isIsogeny_iff_vmap_bijective | exact GlobalTheory.AV.AbVar.isFinite_iff_tmap_injective_and_isIsogeny_iff_vmap_bijective | (intros; apply GlobalTheory.AV.AbVar.isFinite_iff_tmap_injective_and_isIsogeny_iff_vmap_bijective <;> assumption)
end

section

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.ModulusNorm

theorem absNorm_eq_of_two_over {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {w w' : HeightOneSpectrum (𝓞 E)} (hne : w ≠ w')
    (h : w'.under (𝓞 F) = w.under (𝓞 F)) :
    Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 F)).asIdeal := by
  set p := (w.under (𝓞 F)).asIdeal with hp
  have l1 : w.asIdeal.LiesOver p := ⟨rfl⟩
  have l2 : w'.asIdeal.LiesOver p := ⟨by rw [hp, ← h]; rfl⟩
  have f1 := Ideal.absNorm_pow_inertiaDeg p w.asIdeal
  have f2 := Ideal.absNorm_pow_inertiaDeg p w'.asIdeal
  have c1 := w.asIdeal.inertiaDeg_pos (𝓞 F)
  have c2 := w'.asIdeal.inertiaDeg_pos (𝓞 F)
  have m1 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p ≤ w.asIdeal := Ideal.map_le_iff_le_comap.2 (le_of_eq l1.over)
  have m2 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p ≤ w'.asIdeal := Ideal.map_le_iff_le_comap.2 (le_of_eq l2.over)
  have cop : w.asIdeal ⊔ w'.asIdeal = ⊤ :=
    Ideal.IsMaximal.coprime_of_ne w.isMaximal w'.isMaximal fun e => hne (HeightOneSpectrum.ext e)
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p ≤ w.asIdeal * w'.asIdeal := by
    rw [Ideal.mul_eq_inf_of_coprime cop]; exact le_inf m1 m2
  have hd := map_dvd Ideal.absNorm (Ideal.dvd_iff_le.2 hle)
  rw [map_mul, Ideal.absNorm_algebraMap, ← f1, ← f2, ← pow_add,
    ← Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E, h2] at hd
  have hq : 1 < Ideal.absNorm p := by
    rcases Nat.lt_or_ge 1 (Ideal.absNorm p) with h' | h'
    · exact h'
    · exfalso
      interval_cases hh : Ideal.absNorm p
      · exact (w.under (𝓞 F)).ne_bot (Ideal.absNorm_eq_zero_iff.1 hh)
      · exact (w.under (𝓞 F)).isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 hh)
  have := (Nat.pow_dvd_pow_iff_le_right hq).1 hd
  have e1 : w.asIdeal.inertiaDeg (𝓞 F) = 1 := by omega
  rw [← f1, e1, pow_one]

variable {D : D7}

theorem conjPl_ne_of_isIdemAt {w : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e w) : Formalism.DivisionValues.conjPl w ≠ w := by
  rw [GlobalTheory.FunObj.conjPl_eq_cP]
  exact GlobalTheory.FunObj.conjPrime_ne_of_isIdempotentAt he

theorem absNorm_of_isIdemAt {w : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : Formalism.L2.NTheta.IsIdemAt e w) :
    Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal :=
  absNorm_eq_of_two_over D.sp.cm.deg2 (conjPl_ne_of_isIdemAt he).symm (GlobalTheory.ChainTw.ParInv.under_conjPl w)

variable {T : Type} {L : LevCh D T}

theorem absNorm_condE (P : Places L) : Ideal.absNorm (GlobalTheory.FunObj.SqNum.condE P) = GlobalTheory.FunObj.SqNum.levQ P := by
  unfold GlobalTheory.FunObj.SqNum.condE GlobalTheory.FunObj.SqNum.levQ
  rw [map_prod]
  refine Finset.prod_congr rfl fun v hv => ?_
  obtain ⟨e, he⟩ := P.w_split v hv
  rw [map_pow, absNorm_of_isIdemAt he, P.under_w hv]

end GlobalTheory.ModulusNorm
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SumSize GlobalTheory.SumCount

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CosCount

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem cosFam_apply_eq_of_mem_supp {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {P : Pl D.host.E} (hP : P ∈ G.pl.W0)
    (hl : P ∈ locPl G t) {β β' : CosFam G t} (hβ : β ∈ S.supp t Φ) (hβ' : β' ∈ S.supp t Φ) :
    β ⟨P, hl⟩ = β' ⟨P, hl⟩ := by
  classical
  have hs : 1 ≤ (locGrid G t P).s := one_le_sLen
  have hkeep : keepAt G P = false := by simp [keepAt, hP]
  have hdep : depthAt G P = cosExp G P := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨h1, h2⟩ := depthAt_w G hv
    rw [h1, h2]
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := ((Good.locGrid_isGood hL G W t hde hc).1 P hl).square 0 hm 0 hm
  haveI := (isUnitVol_unitVol P).1
  have hT := isTensor_Tflip hL W S.B t Φ hde hc hl
  rw [hdep] at hT
  have hO := oneCoset hs (psiAt W P) (unitVol P) (givenLevel G t P) (Tflip W S.B t Φ P) (unifAt P) (cosExp G P) D.R.m_even
    (isUnif_unifAt P) h00.cond hT (fun j hj _ => ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.givenLevel_KO G t P hj)
  have hk : keepAt G (⟨P, hl⟩ : locPl G t).1 = false := hkeep
  have hb := hβ ⟨P, hl⟩
  have hb2 := hβ' ⟨P, hl⟩
  rw [hk] at hb hb2
  exact funext fun i => (hO _ hb i).trans (hO _ hb2 i).symm

theorem supp_subsingleton {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) (hQ : L.Q t = ∅) : (S.supp t Φ).Subsingleton := by
  classical
  intro β hβ β' hβ'
  have hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro P hP; rw [hQ] at hP; exact absurd hP (Finset.notMem_empty _)
  funext ⟨P, hl⟩
  have hP : P ∈ G.pl.W0 := by
    rcases Finset.mem_union.1 hl with h | h
    · exact h
    · rw [hQ] at h; exact absurd h (Finset.notMem_empty _)
  exact cosFam_apply_eq_of_mem_supp hL S t Φ hde hc hP hl hβ hβ'

end GlobalTheory.CosCount
end
end

section

open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory.EtaleCompletionRadical

theorem isRadical_map_of_flat {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [Module.Flat A B] (I : Ideal A) (hI : I.IsRadical)
    (hfib : ∀ (P : Ideal A) [P.IsPrime], _root_.IsReduced (B ⊗[A] P.ResidueField)) :
    (I.map (algebraMap A B)).IsRadical := by
  classical
  haveI : Finite I.minimalPrimes := (Ideal.finite_minimalPrimes_of_isNoetherianRing A I).to_subtype
  haveI : Fintype I.minimalPrimes := Fintype.ofFinite _
  haveI hpr : ∀ P : I.minimalPrimes, P.1.IsPrime := fun P => P.2.1.1
  have hle : ∀ P : I.minimalPrimes, I ≤ P.1 := fun P => P.2.1.2
  let g : ∀ P : I.minimalPrimes, (A ⧸ I) →ₐ[A] P.1.ResidueField := fun P =>
    Ideal.Quotient.liftₐ I (IsScalarTower.toAlgHom A A P.1.ResidueField) (fun a ha => by
      change algebraMap A P.1.ResidueField a = 0
      exact Ideal.algebraMap_residueField_eq_zero.2 (hle P ha))
  let f : (A ⧸ I) →ₗ[A] ∀ P : I.minimalPrimes, P.1.ResidueField := LinearMap.pi fun P => (g P).toLinearMap
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine hI (Ideal.sInf_minimalPrimes (I := I) ▸ ?_)
    refine Ideal.mem_sInf.2 fun P hP => ?_
    have h0 := congrFun hy ⟨P, hP⟩
    haveI : P.IsPrime := hP.1.1
    exact Ideal.algebraMap_residueField_eq_zero.1 h0
  have hfB := Module.Flat.lTensor_preserves_injective_linearMap (M := B) f hf
  intro x ⟨n, hn⟩

  have hz : (x ⊗ₜ[A] (1 : A ⧸ I) : B ⊗[A] (A ⧸ I)) = 0 := by
    apply hfB
    rw [map_zero]
    apply (TensorProduct.piRight A A B fun P : I.minimalPrimes => P.1.ResidueField).injective
    rw [map_zero]
    funext P
    simp only [LinearMap.lTensor_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, Pi.zero_apply]
    change x ⊗ₜ[A] (g P 1) = 0
    rw [map_one]
    have hnil : IsNilpotent (x ⊗ₜ[A] (1 : P.1.ResidueField) : B ⊗[A] P.1.ResidueField) := by
      refine ⟨n, ?_⟩
      rw [Algebra.TensorProduct.tmul_pow, one_pow]
      change Algebra.TensorProduct.includeLeft (S := A) (x ^ n) = 0
      have hk : I.map (algebraMap A B) ≤ RingHom.ker
          (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := P.1.ResidueField)).toRingHom := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeLeft_apply]
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one,
          Ideal.algebraMap_residueField_eq_zero.2 (hle P ha), TensorProduct.tmul_zero]
      exact hk hn
    exact hnil.eq_zero
  have := congrArg (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm hz
  rw [← Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, AlgEquiv.symm_apply_apply, map_zero,
    Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

end GlobalTheory.EtaleCompletionRadical

namespace GlobalTheory.EtaleCompletionRadical


set_option synthInstance.maxHeartbeats 400000 in
theorem isReduced_adicCompletion_tensor_residueField (A : Type) [CommRing A] [IsLocalRing A]
    [Algebra.EssFiniteType ℤ A] (P : Ideal A) [P.IsPrime] :
    _root_.IsReduced (AdicCompletion (maximalIdeal A) A ⊗[A] P.ResidueField) := by
  have h := GlobalTheory.GeomRegFibTransport.geomRegFib_adicCompletion_of_essFiniteType_int
    GlobalTheory.qeRing_of_finiteType_int A P P.ResidueField (IntermediateField.fg_of_noetherian _)
  obtain ⟨-, hreg⟩ := h
  refine isReduced_ofLocalizationMaximal _ fun Q hQ => ?_
  haveI := hreg Q
  infer_instance

theorem isRadical_map_of_isEtaleCompletion : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (φ : A →+* R), IsAdicComplete (maximalIdeal R) R →
    IsEtaleCompletion φ → ((residue R).comp φ).FormallyUnramified → ∀ I : Ideal A, I.IsRadical →
    (I.map φ).IsRadical := by
  intro A R _ _ _ _ _ _ φ hc het hfu I hI
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing ℤ A
  haveI := hc
  letI : Algebra A R := φ.toAlgebra
  obtain ⟨g, hg, het'⟩ := GlobalTheory.NormalBaseChange.exists_etale_of_isEtaleCompletion A R het hfu
  letI : Algebra (AdicCompletion (maximalIdeal A) A) R := g.toAlgebra
  have h1 : (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))).IsRadical :=
    isRadical_map_of_flat I hI fun P _ => isReduced_adicCompletion_tensor_residueField A P
  have h2 := GlobalTheory.EtaleReducedEq.isRadical_map_of_etale (C := R) _ h1
  rw [Ideal.map_map] at h2
  change (I.map (g.comp _)).IsRadical at h2
  rwa [hg] at h2

end GlobalTheory.EtaleCompletionRadical
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_differentials_from_globalForms : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Par A.hom := by
  first | exact @GlobalTheory.ParForm.par | exact GlobalTheory.ParForm.par | (intros; apply GlobalTheory.ParForm.par <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

section Lin

variable {S : Type*} [CommRing S] {M N : Type*} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]

theorem smul_top_le_comap (f : M →ₗ[S] N) (J : Ideal S) :
    J • (⊤ : Submodule S M) ≤ (J • (⊤ : Submodule S N)).comap f :=
  Submodule.smul_le.2 fun r hr n _ ↦ by
    rw [Submodule.mem_comap, map_smul]; exact Submodule.smul_mem_smul hr trivial

theorem mem_smul_top_equiv (e : M ≃ₗ[S] N) (J : Ideal S) (x : M) :
    e x ∈ J • (⊤ : Submodule S N) ↔ x ∈ J • (⊤ : Submodule S M) :=
  ⟨fun h ↦ by simpa using smul_top_le_comap (e.symm : N →ₗ[S] M) J h,
   fun h ↦ smul_top_le_comap (e : M →ₗ[S] N) J h⟩

theorem mem_sup_smul_top_equiv (e : M ≃ₗ[S] N) (J : Ideal S) (K : Submodule S N) (x : M) :
    x ∈ K.comap (e : M →ₗ[S] N) ⊔ J • ⊤ ↔ e x ∈ K ⊔ J • ⊤ := by
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup ha ((mem_smul_top_equiv e J b).2 hb)
  · intro h
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h
    have hx : x = e.symm a + e.symm b := by rw [← map_add (f := _), hab, LinearEquiv.symm_apply_apply]
    rw [hx]
    refine Submodule.add_mem_sup ?_ ((mem_smul_top_equiv e J _).1 (by simpa using hb))
    simpa using ha

theorem exists_isCompl_comap_iff (e : M ≃ₗ[S] N) (K : Submodule S N) :
    (∃ L, IsCompl K L) ↔ ∃ L, IsCompl (K.comap (e : M →ₗ[S] N)) L := by
  constructor
  · rintro ⟨L, h⟩
    exact ⟨L.comap (e : M →ₗ[S] N), (Submodule.orderIsoMapComap e).symm.isCompl h⟩
  · rintro ⟨L, h⟩
    refine ⟨L.map (e : M →ₗ[S] N), ?_⟩
    have := (Submodule.orderIsoMapComap e).isCompl h
    simpa [Submodule.orderIsoMapComap, Submodule.map_comap_eq_of_surjective e.surjective] using this

end Lin

theorem admissible_classification : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → (∀ K : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) → (∀ c, c ∈ K ⊔ I • ⊤ ↔ rho hI hk A₀.hom c ∈ F1 A₀.hom) → ∃ F : Submodule R (HdR A'), GrothendieckMessing.IsAdmissible h' F ∧ (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = F.comap (crysToDR (divided₂ hI) h')) ∧ (∀ F : Submodule R (HdR A'), GrothendieckMessing.IsAdmissible h' F → ∃ K : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) ∧ (∀ c, c ∈ K ⊔ I • ⊤ ↔ rho hI hk A₀.hom c ∈ F1 A₀.hom) ∧ (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = F.comap (crysToDR (divided₂ hI) h')) ∧ ∀ K K' : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) → (∃ N, IsCompl K' N) → (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = (K'.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator → K = K' := by
  intro H1 H2 R R₀ _ _ I hI π hπ hk g A₀ _ A' _ i' h' hA hg
  obtain ⟨-, -, pc, bij, fin, proj, hA₀, hg₀⟩ :=
    abelianLift_facts H1 H2 R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  obtain ⟨rs, rk⟩ := GlobalTheory.T.abelianScheme_crystal_reduces_to_deRham_sqZero H1 H2 R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  obtain ⟨-, ⟨N₀, hN₀⟩, -⟩ := GlobalTheory.AbelianHodge.abelianDeRham_hodge H1 H2 R₀ A₀ g hA₀ hg₀
  let P := prim (divided₂ hI) (spMap π) A₀
  let Ψ : primDR A' ≃ₗ[R] P := LinearEquiv.ofBijective (liftMor (divided₂ hI) h').pull bij
  let Φ : primDR A' ≃ₗ[R] Cr hI π A₀.hom := Ψ.trans (LinearEquiv.ofTop _ pc)
  have hΦ : ∀ c, Φ c = ((Ψ c : P) : Cr hI π A₀.hom) := fun _ ↦ rfl
  let ρ := (GrothendieckMessing.redMor h').pull
  have mT : IsMor (dp0 R₀) (A₀.hom ≫ 𝟙 _) (dp0 R₀) A₀.hom (RingHom.id R₀) (𝟙 _) :=
    IsMor.of_over _ (by simp)
  have mT' : IsMor (dp0 R₀) A₀.hom (dp0 R₀) (A₀.hom ≫ 𝟙 _) (RingHom.id R₀) (𝟙 _) :=
    IsMor.of_over _ (by simp)
  have back : ∀ x, mT'.pull1 (mT.pull1 x) = x := fun x ↦
    (IsMor.pullback1_comp mT mT' (IsMor.id _ _) (fun _ ↦ rfl) (Category.id_comp _) x).trans
      (IsMor.pullCohomologyOne_id _ x)
  have inj : Function.Injective mT.pull1 := Function.LeftInverse.injective back
  have mD : IsMor (dp0 R) (A'.hom ≫ 𝟙 _) (dp0 R₀) A₀.hom π i' :=
    IsMor.of_dividedPowersZeroIdeal _ (by rw [Category.comp_id]; exact h'.1.w)
  have key : ∀ c : primDR A',
      mT.pull1 ((ρ c : primDR A₀) : FirstDeRham (A₀.hom ≫ 𝟙 _)) = rho hI hk A₀.hom (Φ c) := by
    intro c
    rw [hΦ]
    exact (IsMor.pullback1_comp _ mT mD (fun _ ↦ rfl) (Category.id_comp _) c.1).trans
      (IsMor.pullback1_comp _ (redMor hI hk A₀.hom) mD (fun _ ↦ rfl) (Category.id_comp _) c.1).symm
  have F1iff : ∀ c : primDR A', ρ c ∈ PrimitiveSubmodule A₀ ↔ rho hI hk A₀.hom (Φ c) ∈ F1 A₀.hom := by
    intro c
    rw [← key]
    constructor
    · intro h
      exact mT.pullback1_mem_hodgeFiltration h
    · intro h
      have := mT'.pullback1_mem_hodgeFiltration h
      rw [back] at this
      exact this
  have ρker : ∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R (primDR A')) := by
    intro c
    rw [hk, ← mem_smul_top_equiv Φ, ← rk, ← key, map_eq_zero_iff _ inj, Submodule.coe_eq_zero]
  have ρsurj : Function.Surjective ρ := by
    intro y
    obtain ⟨d, hd⟩ := rs (mT.pull1 y.1)
    refine ⟨Φ.symm d, Subtype.ext (inj ?_)⟩
    rw [key, LinearEquiv.apply_symm_apply, hd]
  obtain ⟨D1, D2⟩ := GlobalTheory.T.summand_dualAnnihilator_reduction_projective R R₀ π hπ (primDR A') (primDR A₀) (Module.Finite.equiv Φ.symm)
    (Module.Projective.of_equiv Φ.symm) ρ ρsurj ρker (PrimitiveSubmodule A₀) ⟨N₀, hN₀⟩
  have cond : ∀ K : Submodule R (Cr hI π A₀.hom),
      (∀ c, c ∈ K ⊔ I • ⊤ ↔ rho hI hk A₀.hom c ∈ F1 A₀.hom) ↔
        ∀ c, c ∈ K.comap (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom) ⊔ RingHom.ker π • ⊤ ↔
          ρ c ∈ PrimitiveSubmodule A₀ := by
    intro K
    rw [hk]
    constructor
    · intro H c
      rw [mem_sup_smul_top_equiv, F1iff]
      exact H (Φ c)
    · intro H c
      have := H (Φ.symm c)
      rwa [mem_sup_smul_top_equiv, F1iff, LinearEquiv.apply_symm_apply] at this
  have crysSurj : Function.Surjective (crysToDR (divided₂ hI) h') := fun y ↦
    ⟨y.comp (Ψ.symm : P →ₗ[R] primDR A'), LinearMap.ext fun c ↦ by
      rw [crysToDR_apply]
      exact congrArg y (Ψ.symm_apply_apply c)⟩
  have ann : ∀ K : Submodule R (Cr hI π A₀.hom),
      (K.comap P.subtype).dualAnnihilator =
        (K.comap (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom)).dualAnnihilator.comap
          (crysToDR (divided₂ hI) h') := by
    intro K
    ext d
    simp only [Submodule.mem_comap, Submodule.mem_dualAnnihilator, crysToDR_apply]
    constructor
    · intro H c hc
      exact H _ hc
    · intro H p hp
      have e : (liftMor (divided₂ hI) h').pull (Ψ.symm p) = p := Ψ.apply_symm_apply p
      have hm : Φ (Ψ.symm p) ∈ K := by
        rw [hΦ, Ψ.apply_symm_apply]
        exact hp
      have := H (Ψ.symm p) hm
      rwa [crysToDR_apply, e] at this
  have eqiff : ∀ (K : Submodule R (Cr hI π A₀.hom)) (F : Submodule R (HdR A')),
      (K.comap P.subtype).dualAnnihilator = F.comap (crysToDR (divided₂ hI) h') ↔
        (K.comap (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom)).dualAnnihilator = F := by
    intro K F
    rw [ann]
    exact (Submodule.comap_injective_of_surjective crysSurj).eq_iff
  refine ⟨fun K hK hc ↦ ?_, fun F hF ↦ ?_, fun K K' hK hK' he ↦ ?_⟩
  · obtain ⟨c1, -, c3⟩ := D1 _ ((exists_isCompl_comap_iff Φ K).1 hK)
    exact ⟨_, ⟨c1, c3.1 ((cond K).1 hc)⟩, (eqiff K _).2 rfl⟩
  · obtain ⟨K', hK', rfl⟩ := D2 F hF.1
    have hKK : (K'.map (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom)).comap
        (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom) = K' :=
      Submodule.comap_map_eq_of_injective Φ.injective K'
    obtain ⟨-, -, c3⟩ := D1 K' hK'
    refine ⟨K'.map (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom), (exists_isCompl_comap_iff Φ _).2 (by rw [hKK]; exact hK'),
      (cond _).2 (by rw [hKK]; exact c3.2 hF.2), (eqiff _ _).2 (by rw [hKK])⟩
  · rw [ann, ann] at he
    have e := Submodule.comap_injective_of_surjective crysSurj he
    obtain ⟨-, c2, -⟩ := D1 _ ((exists_isCompl_comap_iff Φ K).1 hK)
    obtain ⟨-, c2', -⟩ := D1 _ ((exists_isCompl_comap_iff Φ K').1 hK')
    refine Submodule.comap_injective_of_surjective Φ.surjective ?_
    rw [← c2, ← c2', e]

end GlobalTheory.LiftSys
end
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

attribute [local instance high] Submodule.module


theorem _root_.GlobalTheory.T.kronecker_character_frame_third : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → GoodW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) → latW U (wtZ a n) ≠ ⊥ → slopeMax_sq (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n)) (latW U (wtZ a n)) ≤ 2 * lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 2 * Real.log (supConst D.host.E D.R.r D.host.d l.M (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1)) + Real.log |(discr c.F : ℝ)| / (Module.finrank ℚ c.F : ℝ) := by
  first | exact @GlobalTheory.mumaxTop | exact GlobalTheory.mumaxTop | (intros; apply GlobalTheory.mumaxTop <;> assumption)
end
