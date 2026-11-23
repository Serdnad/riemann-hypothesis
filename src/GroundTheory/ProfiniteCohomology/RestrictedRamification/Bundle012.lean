module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Bundle006
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Bundle008
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Bundle009
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseLocal
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Bundle011
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseInv
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Finite
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteOpen
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.HighInflUnits
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerDivisor
import GroundTheory.ProfiniteCohomology.Bundle007
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
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

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Local

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n] (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
include hnS



theorem bijective_gsRootsLocalMor_of_places (v : S) : Function.Bijective (gsRootsLocalMor S ιs n v).hom :=
  (exists_isPrimitiveRoot_maxUnramifiedOutside K S n (NeZero.ne n) hnS).elim fun _ hz =>
    Additive.ofMul.bijective.comp ((bijective_rootsOfUnityMapHom n
      ((ιs v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom hz).comp Additive.toMul.bijective)

theorem bijective_gsLocalInvRoots_of_places (v : S) : Function.Bijective (gsLocalInvRoots S ιs n v) := by
  have e : ⇑(gsLocalInvRoots S ιs n v) =
      (localDualityHypotheses (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
        (natCast_ne_zero_adicCompletion S n v)).tTop ∘ (cohomologyMap (gsRootsLocalMor S ιs n v) 2).hom :=
    funext (gsLocalInvRoots_eq S ιs n v)
  rw [e]
  exact (bijective_localDualityHypotheses_tTop S n v).comp
    (bijective_cohomologyMap_of_bijective _ (bijective_gsRootsLocalMor_of_places S ιs n hnS v) 2)

end Local

section P1

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n] (hodd : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3))

def GsPairingNondegenerate : Prop :=
  (∀ x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
      (∀ y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2,
        gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n)
          (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) → x = 0) ∧
    (∀ y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2,
      (∀ x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
        gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n)
          (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) → y = 0)

end P1

section Level

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (n ℓ k : ℕ) [NeZero n] (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hodd : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3))

def GsPairingInput (n ℓ : ℕ) [NeZero n] : Prop :=
  ∀ (L : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 L.1))) [Fintype S']
    (ιs' : ∀ v : S', ℚ̄ →ₐ[L.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 L.1)).adicCompletion L.1)),
    (∀ v : HeightOneSpectrum (𝓞 L.1), ((ℓ : ℕ) : 𝓞 L.1) ∈ v.asIdeal → v ∈ S') →
    (∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ L.1) → ∀ (hodd' : Odd n ∨ IsTotallyComplex L.1)
    (h3' : Subsingleton (cohomology (gsRoots S' n) 3)), GsPairingNondegenerate S' ιs' n hodd' h3'


omit [Fintype S] [NeZero n] in
include hnk hS in
theorem natCast_not_mem_of_not_mem : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal :=
  fun v hv h => hv (mem_of_natCast_pow_mem S n ℓ k hnk hS v h)


include hℓ hnk hS in
private theorem gsLevelBijective_of_pairing [Nonempty S] (hμ : ∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ K.1)
    (hP : GsPairingNondegenerate S ιs n hodd h3) :
    GsLevelBijective (S := S) (ιs := ιs) (n := n) (gsCompactInv S ιs n hodd h3) := by
  refine ⟨bijective_gsCompactInv_of_mem S n ιs ℓ k hℓ hnk hS hμ hodd h3, ?_⟩
  intro r s h
  have h3Z := subsingleton_zmodRep_gs_three S n ℓ k hnk hS hodd
  have hfin1 := finite_zmodRep_gs_one S n ℓ k hnk hS
  have hfin2 := finite_gsRoots_compact_two S n ℓ k hnk hS ιs
  have hleft := hP.1
  have hright := hP.2
  have hdual := bijective_gs_compactZmodDualityMap S ιs n ℓ k hℓ hnk hS hμ
    hodd h3 h3Z hfin1 hfin2
  -- The kernel checks the conversion of the pairing hypotheses and the duality map.
  run_tac Lean.Elab.Tactic.withMainContext do
    let dual ← Lean.Meta.getFVarFromUserName `hdual
    let args ← #[`hleft, `hright, `r, `s, `h].mapM (m := Lean.MetaM) Lean.Meta.getFVarFromUserName
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.assign (Lean.Meta.mkExpectedPropHint (Lean.mkAppN dual args) (← goal.getType))


include hℓ hnk hS in
theorem gsBaseBijective_of_le (hP : GsPairingInput n ℓ)
    (hcores : ∀ U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
      Function.Surjective (compactCores (gsFinFamily S ιs) U (gsRoots S n) 3).hom)
    (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ n = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    {L : FiniteSubfield} [Fact (K ≤ L)] (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hUW : gsOpenSubgroup S hL ≤ W₀) :
    GsBaseBijective S ιs n (gsOpenSubgroup S hL) (gsCompactInv S ιs n hodd h3) := by
  have hnS := natCast_not_mem_of_not_mem S n ℓ k hnk hS
  have : Nonempty S := nonempty_of_natCast_mem S ℓ hℓ hS
  let SL := placesOver (F := K.1) (L := L.1) S
  let ιsL := gsMackeyEmbeddings (F := K.1) (L := L.1) (Ω := ℚ̄) hL ιs
  let : Fintype SL := fintypePlacesOver (L := L) S
  have : Nonempty SL := nonempty_placesOver_of_natCast_mem (L := L) S hℓ hS
  have hSL : ∀ w : HeightOneSpectrum (𝓞 L.1), ((ℓ : ℕ) : 𝓞 L.1) ∈ w.asIdeal → w ∈ SL :=
    fun w hw => mem_placesOver_of_natCast_mem hS hw
  have hμL : ∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ L.1 :=
    rootsOfUnity_mem_of_gsOpenSubgroup_le (L := L) S n hL W₀ hW₀ hUW (NeZero.ne n) hnS
  have hoddL : Odd n ∨ IsTotallyComplex L.1 := hodd.imp id fun h => by
    have := h
    exact isTotallyComplex_of_algebra K.1 L.1
  have h3L := subsingleton_gsRoots_three (K := L) SL n ℓ k hnk hSL hoddL
  have hPL := hP L SL ιsL hSL hμL hoddL h3L
  let U := gsOpenSubgroup (F := K.1) (L := L.1) (Ω := ℚ̄) S hL
  have hInv := surjective_gsCompactInv S n ιs hodd h3 fun v =>
    (bijective_gsLocalInvRoots_of_places S ιs n hnS v).2
  have hsurj : GsCoresSurjective S ιs n U (gsCompactInv S ιs n hodd h3) := by
    have hcomp := hInv.comp (hcores U)
    -- The kernel identifies the underlying function with the bundled composition.
    run_tac Lean.Elab.Tactic.withMainContext do
      let proof ← Lean.Meta.getFVarFromUserName `hcomp
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.assign (Lean.Meta.mkExpectedPropHint proof (← goal.getType))
  have hLev := gsLevelBijective_of_pairing (K := L) SL ιsL n ℓ k hℓ hnk hSL hoddL h3L hμL hPL
  intro r s h
  exact bijective_zmodCompactDualityMap_gsOpenSubgroup (K := K) (L := L) S ιs hL n (gsCompactInv S ιs n hodd h3)
    (gsCompactInv (K := L) SL ιsL n hoddL h3L) hLev hsurj (r := r) (s := s) h

end Level

end

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.IdeleGroup

attribute [local instance 2000] Rep.hV2

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  {n : ℕ} [NeZero n] (hodd : Odd n ∨ IsTotallyComplex K.1)

instance isDiscreteRep_res_intRepTriv_gs (v : S) :
    IsDiscreteRep (Rep.res (gsFinFamily S ιs v).toMonoidHom (intRepTriv (galUnramifiedOutside K.1 ℚ̄ S))) :=
  isDiscreteRep_res_toMonoidHom (gsFinFamily S ιs v) _

section General

variable (F E : Type) [Field F] [Field E] [Algebra F E] [IsGalois F E]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  (ψ : Gal(E/F) →* Γ) (hψ : Continuous ψ) [IsDiscreteRep (Rep.res ψ (intRepTriv Γ))] {m : ℕ} [NeZero m]
  [IsDiscreteRep (uliftIntToIntRep (galUnits.{0} F E))]

theorem cohomologyMap_galUnitsToZ_cupPairing_δ_bockSeq (z : cocycles (zmodRep.{0} Γ m) 1)
    (χ' : Additive Gal(E/F) →ₜ+ QZ)
    (hχ' : ∀ σ : Gal(E/F), χ' (Additive.ofMul σ) = zmodToQZ m (zmodCocycleHom z (ψ σ))) (a : Fˣ) :
    (cohomologyMap (galUnitsToZ F E) 2).hom (cohomologyULiftIntAddEquiv _ 2
      (cupPairing (mulIntRight ψ (galUnits.{0} F E)) (show 0 + 2 = 2 from rfl)
        ((H0Iso (galUnits.{0} F E)).inv.hom (unitsToInvariants F E (Additive.ofMul a)))
        ((cohomologyMapAlong ψ hψ (𝟙 _) 2).hom
          ((δ (bockSeq_shortExact Γ m (NeZero.ne m)) 1 2 rfl).hom (cohomologyπ _ 1 z))))) =
      galCupClass F E χ' a := by
  obtain ⟨x₁, hx₁, hx₁v⟩ := exists_cocycle_δ_bockSeq (NeZero.ne m) z
  obtain ⟨z0, hz0, hz0c⟩ := exists_cocycle_H0Iso_inv (galUnits.{0} F E) (unitsToInvariants F E (Additive.ofMul a))
  obtain ⟨w, hw, hwv⟩ := exists_cocycle_cupCharClassProf (galUnitsZ F E) χ' (unitsInvariant F E a)
  rw [← hx₁, ← hz0, cohomologyMapAlong_cohomologyπ, cupPairing_cohomologyπ, cohomologyULiftIntAddEquiv_cohomologyπ',
    cohomologyMap_cohomologyπ]
  change _ = (cupCharClassProf (galUnitsZ F E) χ').hom (unitsInvariant F E a)
  rw [← hw]
  congr 1
  apply cocycles_ext
  funext s
  rw [cochainOf_cocycleι_cyclesMap, cochainOf_cocycleι_cocyclesULiftInt]
  beta_reduce
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hz0c, cochainOf_cocycleι_cocyclesMapAlong, hwv]
  have hs : (⇑ψ ∘ fun j : Fin 2 => s ⟨0 + j, by omega⟩) = ![ψ (s 0), ψ (s 1)] := by
    funext j
    fin_cases j <;> rfl
  have hb := hx₁v (ψ (s 0)) (ψ (s 1))
  have hχf : ∀ σ : Gal(E/F), charAdd χ' (Additive.ofMul σ) =
      QZ.toAddCircle (zmodToQZ m ((fun σ => zmodCocycleHom z (ψ σ)) σ)) := fun σ => by
    rw [charAdd_apply, hχ']
  rw [charCocycle_eq_bockInt (fun σ => zmodCocycleHom z (ψ σ)) (charAdd χ') hχf]
  change (mulIntRight ψ (galUnits.{0} F E)).hom
      ((unitsToInvariants F E (Additive.ofMul a) : galUnits.{0} F E) ⊗ₜ[ULift.{0} ℤ]
        (cochainOf (intRepTriv Γ) (cocycleι (intRepTriv Γ) 2 x₁) (⇑ψ ∘ fun j : Fin 2 => s ⟨0 + j, by omega⟩))) = _
  rw [hs]
  have hx : cochainOf (intRepTriv Γ) (cocycleι (intRepTriv Γ) 2 x₁) ![ψ (s 0), ψ (s 1)] =
      ULift.up (bockInt (zmodCocycleHom z) (ψ (s 0)) (ψ (s 1))) := ULift.ext hb
  rw [hx]
  exact mulIntRight_tmul ψ (galUnits.{0} F E) _ _

end General

theorem localInvU_cupPairing_δ_bockSeq (v : S) (a : ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ)
    (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n)))
    (hχ : ∀ g, Multiplicative.toAdd (χ g) = zmodCocycleHom z g) :
    localInvU (v : HeightOneSpectrum (𝓞 K.1))
      (cupPairing (mulIntRight (gsFinFamily S ιs v).toMonoidHom
          (galUnits.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
            (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))))
        (show 0 + 2 = 2 from rfl)
        ((H0Iso (galUnits.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
            (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))).inv.hom
          (unitsToInvariants _ _ (Additive.ofMul a)))
        ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _) (𝟙 _) 2).hom
          ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom
            (cohomologyπ _ 1 z)))) =
      zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd χ
        (SIdeleClassGroup.mk S (finiteEmbedding (v : HeightOneSpectrum (𝓞 K.1)) a)))) := by
  refine (DFunLike.congr_fun (localInvU_eq (v : HeightOneSpectrum (𝓞 K.1))) _).trans ?_
  refine (AddMonoidHom.comp_apply _ _ _).trans ?_
  refine (congrArg (brauerInvZOfIsSepClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
    (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))
    ((AddMonoidHom.comp_apply _ _ _).trans (cohomologyMap_galUnitsToZ_cupPairing_δ_bockSeq _ _
      (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _) z
      (contCharComp (charQZ χ) (decompHomS ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) S (ιs v))
        (continuous_decompHomS (Kv := (v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) S (ιs v)))
      (fun σ => (charQZ_apply χ _).trans (congrArg (zmodToQZ n) (hχ _))) a))).trans ?_
  exact brauerInvZ_galCupClass_decompHomS (Set.toFinite S) hodd χ (v : HeightOneSpectrum (𝓞 K.1)) (ιs v) a

end

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits NumberField IsDedekindDomain GroundTheory.Global

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem exists_coprime_nsmul_of_primary_eq_zero {M : Type*} [AddCommGroup M] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hM : ∀ y : M, ∀ k : ℕ, ℓ ^ k • y = 0 → y = 0) {x : M} (hx : IsOfFinAddOrder x) :
    ∃ m : ℕ, m.Coprime ℓ ∧ m • x = 0 := by
  have hn : addOrderOf x ≠ 0 := hx.addOrderOf_pos.ne'
  have hnm : ℓ ^ (addOrderOf x).factorization ℓ * (addOrderOf x / ℓ ^ (addOrderOf x).factorization ℓ) =
      addOrderOf x := Nat.ordProj_mul_ordCompl_eq_self _ ℓ
  refine ⟨addOrderOf x / ℓ ^ (addOrderOf x).factorization ℓ, (Nat.coprime_ordCompl hℓ hn).symm,
    hM _ ((addOrderOf x).factorization ℓ) ?_⟩
  rw [smul_smul, hnm]
  exact addOrderOf_nsmul_eq_zero x

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ιs : LocalEmbeddings K) {ℓ : ℕ}
  (hℓ : ℓ.Prime) (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hD : ∀ p : ℕ, 2 ≤ p → ∀ x : cohomology (gsDiv K S ιs QZ) p, ∀ k : ℕ, ℓ ^ k • x = 0 → x = 0)


include hℓ hD in
theorem eq_zero_of_pow_nsmul_cohomology_gsDiv_int {q : ℕ} (hq : 3 ≤ q) (x : cohomology (gsDiv K S ιs ℤ) q)
    (k : ℕ) (hx : ℓ ^ k • x = 0) : x = 0 := by
  have hX := divFunSequence_shortExact (gsDecomp K S ιs)
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have hzero : IsZero (cohomology (divFunSequence (gsDecomp K S ιs)).X₂ (p + 1)) :=
    isZero_cohomology_of_bijective_nsmul_ulift _ (fun n hn => bijective_nsmul_divFun_rat _ hn) (by omega)
  have hs := ModuleCat.subsingleton_of_isZero hzero
  let x' : cohomology (divFunSequence (gsDecomp K S ιs)).X₁ (p + 1) := x
  obtain ⟨y, hy⟩ := exists_δ_eq_of_cohomologyMap_f_eq_zero hX p (p + 1) rfl x' (Subsingleton.elim _ _)
  have hx' : ℓ ^ k • x' = 0 := hx
  have hk : ℓ ^ k • (δ hX p (p + 1) rfl).hom.toAddMonoidHom y = 0 :=
    (congrArg (fun t => ℓ ^ k • t) hy).trans hx'
  obtain ⟨y', ⟨j, hj⟩, hy'⟩ := exists_primary_map_eq (δ hX p (p + 1) rfl).hom.toAddMonoidHom hℓ
    (isTorsion_cohomology _ (by omega) y) hk
  have h0 : y' = 0 := hD p (by omega) y' j hj
  have e : x' = (δ hX p (p + 1) rfl).hom y' := hy.symm.trans hy'.symm
  rw [h0, map_zero] at e
  exact e

local instance highSUnitsDiscreteQuotient : IsDiscreteRep (galUnitsModSUnits K.1 ℚ̄ S) :=
  isDiscreteRep_sUnitsQuotSequence_X₃ K.1 ℚ̄ S

include hℓ hS hD in
theorem eq_zero_of_pow_nsmul_cohomology_galUnitsModSUnits {q : ℕ} (hq : 3 ≤ q)
    (x : cohomology (galUnitsModSUnits K.1 ℚ̄ S) q) (k : ℕ) (hx : ℓ ^ k • x = 0) : x = 0 := by
  let : IsDiscreteRep (picSequence K S ιs).X₁ := highSUnitsDiscreteQuotient K S
  have hP := picSequence_shortExact K S ιs
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  let x' : cohomology (picSequence K S ιs).X₁ (p + 1) := x
  have hx' : ℓ ^ k • x' = 0 := hx
  have hxD : (cohomologyMap (picSequence K S ιs).f (p + 1)).hom x' = 0 :=
    eq_zero_of_pow_nsmul_cohomology_gsDiv_int K S ιs hℓ hD hq _ k
      ((map_nsmul (cohomologyMap (picSequence K S ιs).f (p + 1)).hom (ℓ ^ k) x').symm.trans
        ((congrArg _ hx').trans (map_zero _)))
  exact eq_zero_of_mem_range_δ_of_coprime hP p (p + 1) rfl
    (exists_δ_eq_of_cohomologyMap_f_eq_zero hP p (p + 1) rfl x' hxD) ℓ
    (fun r => exists_coprime_smul_cohomology_eq_zero (picInfRep K S ιs) ℓ
      (exists_coprime_smul_picInfRep K S ιs ℓ hℓ hS) p r) k hx


include hℓ hS hD in
theorem isIsoModCoprime_sUnitsToUnits {r : ℕ} (hr : 4 ≤ r) :
    IsIsoModCoprime ℓ (cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) r).hom.toAddMonoidHom := by
  have hQ := sUnitsQuotSequence_shortExact K.1 ℚ̄ S
  have hP : ∀ q, 3 ≤ q → ∀ w : cohomology (galUnitsModSUnits K.1 ℚ̄ S) q,
      ∃ m : ℕ, m.Coprime ℓ ∧ m • w = 0 := fun q hq w =>
    exists_coprime_nsmul_of_primary_eq_zero hℓ
      (fun w' k hk => eq_zero_of_pow_nsmul_cohomology_galUnitsModSUnits K S ιs hℓ hS hD hq w' k hk)
      (isTorsion_cohomology _ (by omega) w)
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 1 := ⟨r - 1, by omega⟩
  refine ⟨fun z hz => ?_, fun y => ?_⟩
  · let z' : cohomology (sUnitsQuotSequence K.1 ℚ̄ S).X₁ (p + 1) := z
    obtain ⟨w, hw⟩ := exists_δ_eq_of_cohomologyMap_f_eq_zero hQ p (p + 1) rfl z' hz
    obtain ⟨m, hm, hmw⟩ := hP p (by omega) w
    refine ⟨m, hm, ?_⟩
    have e : m • z' = 0 := by
      rw [← hw, ← map_nsmul]
      exact (congrArg _ hmw).trans (map_zero _)
    exact e
  · let y' : cohomology (sUnitsQuotSequence K.1 ℚ̄ S).X₂ (p + 1) := y
    obtain ⟨m, hm, hmy⟩ := hP (p + 1) (by omega) ((cohomologyMap (sUnitsQuotSequence K.1 ℚ̄ S).g (p + 1)).hom y')
    have hg : (cohomologyMap (sUnitsQuotSequence K.1 ℚ̄ S).g (p + 1)).hom (m • y') = 0 :=
      (map_nsmul _ m y').trans hmy
    obtain ⟨z, hz⟩ := exists_cohomologyMap_f_eq_of_cohomologyMap_g_eq_zero hQ (p + 1) (m • y') hg
    exact ⟨m, hm, z, hz⟩

def sUnitsInfl (r : ℕ) : cohomology (galSUnitsMax K.1 ℚ̄ S) r →+ cohomology (unitsLimitRep K) r :=
  (gsUnitsInfl K S r).comp (cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) r).hom.toAddMonoidHom

theorem sUnitsInfl_apply (r : ℕ) (y : cohomology (galSUnitsMax K.1 ℚ̄ S) r) :
    sUnitsInfl K S r y = gsUnitsInfl K S r ((cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) r).hom y) :=
  rfl


end

end GroundTheory.ProfCoh
end
