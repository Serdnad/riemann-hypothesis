module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Bundle012
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.HighUnits
import GroundTheory.ProfiniteCohomology.Bundle007
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.HighUnitsLocal
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.HighDecomp
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.HighDecompLadic
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.HighDivisor
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseClassIdele
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Bundle009
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCupKummer
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFormal
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseKummer
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.MkFiniteEmbeddingGlobalUniformizer
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Bundle010
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCupGlobal
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCupNat
import GroundTheory.ProfiniteCohomology.RestrictedRamification.ClassFieldGSPresentation
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits NumberField IsDedekindDomain GroundTheory.Global

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

section TwoTorsion

variable {K : FiniteSubfield}

theorem two_nsmul_cohomology_unitsLimitRep {r : ℕ} (hr : 4 ≤ r) (y : cohomology (unitsLimitRep K) r) :
    2 • y = 0 := by
  obtain ⟨ι⟩ := nonempty_localEmbeddings K
  apply (bijective_realLocalization ι hr).1
  rw [map_nsmul, map_zero]
  funext v
  rw [Pi.smul_apply]
  rcases Nat.even_or_odd r with he | ho
  · have hc := natCard_localGaloisCohomology_of_isReal_of_even v.1 v.2 (by omega) he
    rw [← hc]
    exact card_nsmul_eq_zero'
  · have := subsingleton_localGaloisCohomology_of_isReal_of_odd v.1 v.2 ho
    exact Subsingleton.elim _ _

end TwoTorsion

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) {ℓ : ℕ} (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)


include hℓ hS in
theorem eq_zero_of_pow_nsmul_cohomology_gsDiv_QZ (ιs : LocalEmbeddings K) {p : ℕ} (hp : 2 ≤ p)
    (x : cohomology (gsDiv K S ιs QZ) p) (k : ℕ) (hx : ℓ ^ k • x = 0) : x = 0 :=
  eq_zero_of_pow_nsmul_cohomology_divFunRep (gsDecomp K S ιs) (continuous_gsDecomp K S ιs) hℓ (by omega)
    (fun v y hy => hy.elim fun j hj => eq_zero_of_pow_nsmul_cohomology_range_gsDecomp K S ιs v hℓ hS hp y j hj)
    x k hx


include hℓ hS in
theorem isIsoModCoprime_sUnitsToUnits_of_four_le {r : ℕ} (hr : 4 ≤ r) :
    IsIsoModCoprime ℓ (cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) r).hom.toAddMonoidHom :=
  isIsoModCoprime_sUnitsToUnits K S (nonempty_localEmbeddings K).some hℓ hS
    (fun _ hp x k hx => eq_zero_of_pow_nsmul_cohomology_gsDiv_QZ K S hℓ hS _ hp x k hx) hr


include hℓ hS in
theorem isIsoModCoprime_sUnitsInfl {r : ℕ} (hr : 4 ≤ r) : IsIsoModCoprime ℓ (sUnitsInfl K S r) :=
  (isIsoModCoprime_gsUnitsInfl K S hℓ hS (by omega)).comp (isIsoModCoprime_sUnitsToUnits_of_four_le K S hℓ hS hr)

noncomputable def sUnitsToUnitsPrimaryEquiv {r : ℕ} (hr : 4 ≤ r) :
    AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) r) ℓ ≃+
      AddCommGroup.primaryComponent (cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r) ℓ :=
  AddEquiv.ofBijective _
    ((isIsoModCoprime_sUnitsToUnits_of_four_le K S hℓ hS hr).bijective_primaryComponentMap hℓ
      (isTorsion_cohomology _ (by omega)))

noncomputable def sUnitsInflPrimaryEquiv {r : ℕ} (hr : 4 ≤ r) :
    AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) r) ℓ ≃+
      AddCommGroup.primaryComponent (cohomology (unitsLimitRep K) r) ℓ :=
  AddEquiv.ofBijective _
    ((isIsoModCoprime_sUnitsInfl K S hℓ hS hr).bijective_primaryComponentMap hℓ (isTorsion_cohomology _ (by omega)))

section Odd



end Odd

section Real

variable (ι : LocalEmbeddings K)

theorem mem_primaryComponent_two_unitsLimitRep {r : ℕ} (hr : 4 ≤ r) (y : cohomology (unitsLimitRep K) r) :
    y ∈ AddCommGroup.primaryComponent (cohomology (unitsLimitRep K) r) 2 :=
  ⟨1, by rw [pow_one]; exact two_nsmul_cohomology_unitsLimitRep hr y⟩

theorem bijective_realLocalization_comp_primaryComponent {X : Type*} [AddCommGroup X] {r : ℕ} (hr : 4 ≤ r)
    (f : X →+ cohomology (unitsLimitRep K) r) (hf : IsIsoModCoprime 2 f) (hX : IsAddTorsion X) :
    Function.Bijective ((realLocalization ι (r := r) (by omega)).comp
      (f.comp (AddCommGroup.primaryComponent X 2).subtype)) := by
  have hb := hf.bijective_primaryComponentMap Nat.prime_two hX
  have hR := bijective_realLocalization ι hr
  refine ⟨fun a b hab => hb.1 (Subtype.ext (hR.1 hab)), fun t => ?_⟩
  obtain ⟨y, rfl⟩ := hR.2 t
  obtain ⟨a, ha⟩ := hb.2 ⟨y, mem_primaryComponent_two_unitsLimitRep (K := K) hr y⟩
  exact ⟨a, congrArg (realLocalization ι (r := r) (by omega)) (congrArg Subtype.val ha)⟩

variable (h2S : ∀ v : HeightOneSpectrum (𝓞 K.1), ((2 : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

noncomputable def gsUnitsRealPrimaryEquiv {r : ℕ} (hr : 4 ≤ r) :
    AddCommGroup.primaryComponent (cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) r) 2 ≃+
      ∀ v : {v : InfinitePlace K.1 // v.IsReal}, localGaloisCohomology K r (.inl v.1) :=
  AddEquiv.ofBijective _ (bijective_realLocalization_comp_primaryComponent K ι hr (gsUnitsInfl K S r)
    (isIsoModCoprime_gsUnitsInfl K S Nat.prime_two h2S (by omega)) (isTorsion_cohomology _ (by omega)))

noncomputable def sUnitsRealPrimaryEquiv {r : ℕ} (hr : 4 ≤ r) :
    AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) r) 2 ≃+
      ∀ v : {v : InfinitePlace K.1 // v.IsReal}, localGaloisCohomology K r (.inl v.1) :=
  AddEquiv.ofBijective _ (bijective_realLocalization_comp_primaryComponent K ι hr (sUnitsInfl K S r)
    (isIsoModCoprime_sUnitsInfl K S Nat.prime_two h2S hr) (isTorsion_cohomology _ (by omega)))

theorem sUnitsRealPrimaryEquiv_apply {r : ℕ} (hr : 4 ≤ r)
    (x : AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) r) 2) :
    sUnitsRealPrimaryEquiv K S ι h2S hr x = realLocalization ι (r := r) (by omega) (sUnitsInfl K S r x) :=
  rfl

end Real

end

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory IsDedekindDomain NumberField GroundTheory.Global GroundTheory.GroupCoh GroundTheory.Global.IdeleGroup

attribute [local instance 2000] Rep.hV2

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n] (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal)

omit [NeZero n] in
theorem linearMap_apply_add_apply {R M N P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N →ₗ[R] P) (a b : M) (c : N) :
    f (a + b) c = f a c + f b c := by
  rw [map_add (f := _), LinearMap.add_apply]



theorem gsRootsToUnitsCompact_comparison_cup (h : gsUnitsCompact S ιs 1)
    (x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    (gsRootsToUnitsCompact S ιs n 3).hom ((gsRootsComparison S ιs n 3).hom
      (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))
        (show 2 + 1 = 3 from rfl) ((gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom h))
        x)) =
      compactCup (gsFinFamily S ιs) (gsPairingμ S n) (gsPairingμᵥ S ιs n) (gsPairingμ_hμ S ιs n)
        (show 1 + 1 + 1 = 2 + 1 from rfl) ((gsKummerCompactδ S ιs n hnS 1).hom h) x := by
  have ea := gsRootsComparison_compactCupRes S ιs n
    ((gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom h)) x
  have ea' : (gsRootsComparison S ιs n 2).hom ((gsRootsComparisonIso S ιs n hnS 2).inv.hom
      ((gsKummerCompactδ S ιs n hnS 1).hom h)) = (gsKummerCompactδ S ιs n hnS 1).hom h :=
    hom_apply_hom_apply_of_comp_eq (gsRootsComparisonIso S ιs n hnS 2).inv_hom_id _
  have eb := compactCohomologyMap_compactCup (gsFinFamily S ιs) (A := gsRoots S n)
    (B := zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (C := gsRoots S n) (C' := galSUnitsMax K.1 ℚ̄ S)
    (Aᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (Cᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (C'ᵥ := fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))
    (a := gsRootsOmegaMor S ιs n) (c := gsRootsOmegaMor S ιs n) (c' := gsSUnitsLocalMor S ιs)
    (gsZmodPairing S n) (gsZmodPairingᵥ S ιs n) (gsZmodPairing_hμ S ιs n)
    (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) n).f
    (fun v => (kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n).f)
    (fun v => (gsKummerLocalMap S ιs n v).comm₁₂) (gsPairingμ_hμ S ιs n) (show 1 + 1 + 1 = 2 + 1 from rfl)
    ((gsKummerCompactδ S ιs n hnS 1).hom h) x
  exact (congrArg (gsRootsToUnitsCompact S ιs n 3).hom (ea.trans (congrArg (fun w =>
    compactCup (gsFinFamily S ιs) (gsZmodPairing S n) (gsZmodPairingᵥ S ιs n) (gsZmodPairing_hμ S ιs n)
      (show 2 + 1 = 3 from rfl) w x) ea'))).trans eb



theorem gsRootsToUnitsCompact_cup_eq (ℓ k : ℕ) (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (d : GsUnitsDatum S) (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    ∃ W : cocycles (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2,
      (∀ g h, (Additive.toMul (cochainOf _ (cocycleι _ 2 W) ![g, h]) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) *
        (((Additive.toMul d.1 : sInvariantSubgroup (F := K.1) ℚ̄ S) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) ^
          bockInt (zmodCocycleHom z) g h)⁻¹ ∈ sUnitsMax K.1 ℚ̄ S) ∧
      (gsRootsToUnitsCompact S ιs n 3).hom ((gsRootsComparison S ιs n 3).hom
        (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))
          (show 2 + 1 = 3 from rfl)
          ((gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom (gsUnitsData S ιs d)))
          (cohomologyπ _ 1 z))) =
        (localToCompact (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) (fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (gsSUnitsLocalMor S ιs) 2).hom
          (fun v => (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
              (gsUnitsLocalMor S ιs v) 2).hom (cohomologyπ _ 2 W) +
            cupPairing (mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (show 0 + 2 = 2 from rfl)
              ((H0Iso _).inv.hom (unitsToInvariants _ _ (d.2 v)))
              ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _) (𝟙 _) 2).hom
                ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom
                  (cohomologyπ _ 1 z)))) := by
  have ex := exists_gsUnitsData_cup_bock S ιs n ℓ k hℓ hnk hS (Additive.toMul d.1) z
  refine ⟨ex.choose, ex.choose_spec.1, ?_⟩
  have hd : gsUnitsData S ιs d = gsUnitsData S ιs (Additive.ofMul (Additive.toMul d.1), 0) +
      gsUnitsData S ιs (0, d.2) :=
    (congrArg (gsUnitsData S ιs) (Prod.ext (add_zero _).symm (zero_add _).symm)).trans (map_add _ _ _)
  have eloc := compactCup_localToCompact (gsFinFamily S ιs) (gsPairingU S)
    (fun v => mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (gsPairingU_hμ S ιs)
    (show 0 + 2 = 2 from rfl) (show 0 + 1 + 2 = 2 + 1 from rfl)
    (fun v => (H0Iso _).inv.hom (unitsToInvariants _ _ (d.2 v)))
    ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom (cohomologyπ _ 1 z))
  refine (gsRootsToUnitsCompact_comparison_cup S ιs n hnS (gsUnitsData S ιs d) (cohomologyπ _ 1 z)).trans
    ((gsKummerCompactδ_cup S ιs n hnS (gsUnitsData S ιs d) (cohomologyπ _ 1 z)).trans ?_)
  refine (congrArg (fun w => compactCup (gsFinFamily S ιs) (gsPairingU S)
      (fun v => mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (gsPairingU_hμ S ιs)
      (show 1 + (1 + 1) = 2 + 1 from rfl) w
      ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom (cohomologyπ _ 1 z)))
    hd).trans ((linearMap_apply_add_apply _ _ _ _).trans ?_)
  refine (congrArg₂ (· + ·) ex.choose_spec.2 ((congrArg (fun w => compactCup (gsFinFamily S ιs) (gsPairingU S)
      (fun v => mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (gsPairingU_hμ S ιs)
      (show 1 + (1 + 1) = 2 + 1 from rfl) w
      ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom (cohomologyπ _ 1 z)))
    (gsUnitsData_zero_local S ιs d.2)).trans eloc)).trans ?_
  exact (map_add _ _ _).symm

section Idele

variable [Fintype S] (hodd : Odd n ∨ IsTotallyComplex K.1)

omit [NeZero n] in
theorem prod_ofFinite_eq {M : Type*} [CommMonoid M] (f : S → M) :
    (letI := Fintype.ofFinite S; ∏ w : S, f w) = ∏ w : S, f w := by
  congr
  exact Subsingleton.elim _ _


omit [NeZero n] in
theorem sPresentation_fst (a : ∀ w : S, ((w : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ) :
    sPresentation S (a, 1) = ∏ w : S, SIdeleClassGroup.mk S (finiteEmbedding (w : HeightOneSpectrum (𝓞 K.1)) (a w)) := by
  rw [sPresentation_apply, toAdd_one, map_zero, toMul_zero, mul_one, placesIdele_apply, map_prod]
  exact prod_ofFinite_eq S _



theorem zmodToQZ_charEquiv_gsUnitsClass
    (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n))) (d : GsUnitsDatum S) :
    zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd χ (Additive.toMul (gsUnitsClass S d)))) =
      ∑ v : S, zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd χ
        (SIdeleClassGroup.mk S (finiteEmbedding (v : HeightOneSpectrum (𝓞 K.1)) (Additive.toMul (d.2 v)))))) -
      divChar S hodd χ (divAbove S d.1) := by
  have e1 : Additive.toMul (gsUnitsClass S d) =
      sPresentation S (fun w => Additive.toMul (d.2 w), 1) *
        sPresentation S (1, Multiplicative.ofAdd (-divAbove S d.1)) :=
    (congrArg Additive.toMul (gsUnitsClass_apply S d)).trans
      ((congrArg (sPresentation S) (Prod.ext (mul_one _).symm (one_mul _).symm)).trans (map_mul _ _ _))
  set ψ := charEquiv ℚ̄ (Set.toFinite S) hodd χ with hψ
  have e2 : ψ (Additive.toMul (gsUnitsClass S d)) =
      (∏ w : S, ψ (SIdeleClassGroup.mk S (finiteEmbedding (w : HeightOneSpectrum (𝓞 K.1)) (Additive.toMul (d.2 w))))) *
        ψ (sPresentation S (1, Multiplicative.ofAdd (-divAbove S d.1))) :=
    (congrArg ψ e1).trans ((map_mul ψ _ _).trans (congrArg (· * _)
      ((congrArg ψ (sPresentation_fst S _)).trans (map_prod ψ _ _))))
  have e3 : zmodToQZ n (Multiplicative.toAdd (ψ (sPresentation S (1, Multiplicative.ofAdd (-divAbove S d.1))))) =
      -divChar S hodd χ (divAbove S d.1) :=
    (divChar_apply S hodd χ (-divAbove S d.1)).symm.trans (map_neg _ _)
  have e4 : zmodToQZ n (Multiplicative.toAdd (∏ w : S, ψ (SIdeleClassGroup.mk S
      (finiteEmbedding (w : HeightOneSpectrum (𝓞 K.1)) (Additive.toMul (d.2 w)))))) =
      ∑ w : S, zmodToQZ n (Multiplicative.toAdd (ψ (SIdeleClassGroup.mk S
        (finiteEmbedding (w : HeightOneSpectrum (𝓞 K.1)) (Additive.toMul (d.2 w)))))) :=
    (congrArg (zmodToQZ n) (toAdd_prod _ _)).trans (map_sum (zmodToQZ n) _ _)
  exact (congrArg (fun u => zmodToQZ n (Multiplicative.toAdd u)) e2).trans
    ((congrArg (zmodToQZ n) (toAdd_mul _ _)).trans ((map_add (zmodToQZ n) _ _).trans
      ((congrArg₂ (· + ·) e4 e3).trans (sub_eq_add_neg _ _).symm)))

end Idele

end

end GroundTheory.ProfCoh
end
