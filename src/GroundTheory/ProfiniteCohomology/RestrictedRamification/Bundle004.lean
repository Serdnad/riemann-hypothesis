module

public import GroundTheory.ProfiniteCohomology.CohomologicalDimension.PrimaryComponentCohomologyEqBotOfScdpLt
public import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.ConePairing
import GroundTheory.ProfiniteCohomology.Bundle001
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Bundle003
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeDefs
public import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
public import GroundTheory.ProfiniteCohomology.Bundle002
public import GroundTheory.ProfiniteCohomology.Bundle011
public import GroundTheory.ProfiniteCohomology.CohomologicalDimension.Bundle001
public import GroundTheory.ProfiniteCohomology.CohomologicalDimension.Subgroup
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.SUnitsDefs
public import GroundTheory.ProfiniteCohomology.ClassFormations.IsIsoCohomologyMapAlongResSubgroupOfHom
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.SInvariantToInvariantsEqZeroIff
import Mathlib.Algebra.Lie.OfAssociative
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
import Mathlib.GroupTheory.Nilpotent
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Connected
public import GroundTheory.ProfiniteCohomology.CohomologicalDimension.Closed
import Mathlib.Topology.Sheaves.Init
import GroundTheory.TateCohomology.HerbrandAbstract

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory

attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

theorem addMonoidHom_apply_zmod_addEquiv {ℓ : ℕ} [NeZero ℓ] {A : Type*} [AddCommGroup A] (e : ZMod ℓ ≃+ A)
    (f : A →+ A) (x : ZMod ℓ) : f (e x) = e (x * e.symm (f (e 1))) := by
  have hx : e x = x.val • e 1 := by
    rw [← map_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  rw [hx, map_nsmul, ← e.apply_symm_apply (f (e 1)), ← map_nsmul, e.symm_apply_apply, nsmul_eq_mul,
    ZMod.natCast_zmod_val]

theorem rho_eq_self_of_isProPGroup {ℓ : ℕ} (hℓ : ℓ.Prime) (A : Rep.{0} (ULift.{0} ℤ) G)
    [IsDiscreteRep A] (e : ZMod ℓ ≃+ A) {P : Subgroup G} (hP : IsProPGroup ℓ P) {σ : G} (hσ : σ ∈ P)
    (a : A) : A.ρ σ a = a := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  let f : G → A →+ A := fun τ => (A.ρ τ).toAddMonoidHom
  let c : G → ZMod ℓ := fun τ => e.symm (A.ρ τ (e 1))
  have hmul : ∀ (τ : G) (x : ZMod ℓ), A.ρ τ (e x) = e (x * c τ) := fun τ x =>
    addMonoidHom_apply_zmod_addEquiv e (f τ) x
  have hpow : ∀ (j : ℕ) (x : ZMod ℓ), A.ρ (σ ^ j) (e x) = e (x * c σ ^ j) := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [pow_succ, map_mul, Module.End.mul_apply, hmul, ih, pow_succ]
      congr 1
      ring
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_stabilizer A (e 1))
    (show (1 : G) ∈ (stabilizer A.ρ (e 1) : Set G) from (stabilizer A.ρ (e 1)).one_mem)
  obtain ⟨k, hk⟩ := isProPGroup_subgroup_iff.1 hP U σ hσ
  have hfix : A.ρ (σ ^ ℓ ^ k) (e 1) = e 1 := by
    exact (mem_stabilizer A.ρ (e 1) _).1 (hU hk)
  have hc : c σ = 1 := by
    rw [hpow, one_mul] at hfix
    have h1 := e.injective hfix
    rwa [ZMod.pow_card_pow] at h1
  rw [← e.apply_symm_apply a, hmul, hc, mul_one]

theorem cdp_le_of_forall_openSubgroup {ℓ : ℕ} (hℓ : ℓ.Prime) (A : Rep.{0} (ULift.{0} ℤ) G)
    [IsDiscreteRep A] (e : ZMod ℓ ≃+ A) (n : ℕ)
    (h : ∀ U : OpenSubgroup G, Subsingleton (cohomology (Rep.res (U : Subgroup G).subtype A) (n + 1))) :
    cdp ℓ G ≤ n := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨P, hP⟩ := exists_isProSylow (G := G) (p := ℓ)
  have : CompactSpace P := isCompact_iff_compactSpace.1 hP.1.isCompact
  rw [← cdp_eq_of_isProSylow hℓ hP]
  rw [cdp_le_iff_of_isProPGroup hℓ hP.2.1 n]
  have hA : Subsingleton (cohomology (Rep.res P.subtype A) (n + 1)) := by
    suffices h' : ∀ x : cohomology (Rep.res P.subtype A) (n + 1), x = 0 from
      ⟨fun x y => (h' x).trans (h' y).symm⟩
    intro x
    obtain ⟨U, hU, hPU, y, rfl⟩ := exists_cohomologyResLE_eq A hP.1 (n + 1) x
    have := h ⟨U, hU⟩
    rw [Subsingleton.elim y 0, map_zero]
  have hfix : ∀ (σ : P) (a : A), (Rep.res P.subtype A).ρ σ a = a := fun σ a =>
    rho_eq_self_of_isProPGroup hℓ A e hP.2.1 σ.2 a
  let ψ : Rep.trivial (ULift.{0} ℤ) P (ULift.{0} (ZMod ℓ)) ⟶ Rep.res P.subtype A :=
    Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm
      (e.toAddMonoidHom.comp (AddEquiv.ulift : ULift.{0} (ZMod ℓ) ≃+ ZMod ℓ).toAddMonoidHom),
      fun σ => LinearMap.ext fun x => (hfix σ _).symm⟩
  let ψ' : Rep.res P.subtype A ⟶ Rep.trivial (ULift.{0} ℤ) P (ULift.{0} (ZMod ℓ)) :=
    Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm
      ((AddEquiv.ulift : ULift.{0} (ZMod ℓ) ≃+ ZMod ℓ).symm.toAddMonoidHom.comp e.symm.toAddMonoidHom),
      fun σ => LinearMap.ext fun x => by
        change ULift.up (e.symm ((Rep.res P.subtype A).ρ σ x)) = ULift.up (e.symm x)
        rw [hfix]⟩
  have hcomp : ψ ≫ ψ' = 𝟙 _ := by
    ext x
    simp [ψ, ψ', uliftIntLinearEquivAddHom_symm_apply]
  have hinj : Function.Injective (cohomologyMap ψ (n + 1)).hom := fun x y hxy => by
    have h' := congrArg (cohomologyMap ψ' (n + 1)).hom hxy
    rwa [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← cohomologyMap_comp, hcomp,
      cohomologyMap_id, ModuleCat.id_apply, ModuleCat.id_apply] at h'
  exact hinj.subsingleton

end GroundTheory.ProfCoh
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits MonoidalCategory GroundTheory.GroupCoh

universe u

section Abstract

variable {k : Type u} [CommRing k] {K L K' L' N N' : CochainComplex (ModuleCat.{u} k) ℕ} {f : K ⟶ L}
  {f' : K' ⟶ L'} (μL : LeibnizPairing L N' L') (ρ : N ⟶ N') (μK : LeibnizPairing K N K')
  (hc : ∀ {r s n : ℕ} (h : r + s = n) (x : K.X r) (z : N.X s),
    (f'.f n).hom (μK.μ h x z) = μL.μ h ((f.f r).hom x) ((ρ.f s).hom z))

theorem LeibnizPairing.exists_coconeLeft_homology_eq_homologyδ {p s m : ℕ} (h : p + 1 + s = m + 1)
    (X : (mappingCoconeNat f).cycles (p + 1)) (e : N.cycles s) (q : K'.X m)
    (hq : (K'.d m (m + 1)).hom q = μK.μ h (((mappingCoconeNat f).iCycles (p + 1)).hom X).1 ((N.iCycles s).hom e)) :
    ∃ w : L'.cycles m, (L'.iCycles m).hom w =
        μL.μ (show p + s = m by omega) (show L.X p from (((mappingCoconeNat f).iCycles (p + 1)).hom X).2)
          ((ρ.f s).hom ((N.iCycles s).hom e)) - (f'.f m).hom q ∧
      (LeibnizPairing.coconeLeft μL ρ μK hc).homology h (((mappingCoconeNat f).homologyπ (p + 1)).hom X)
          ((N.homologyπ s).hom e) =
        (mappingCoconeNat.homologyδ f' m).hom ((L'.homologyπ m).hom w) := by
  set x := (((mappingCoconeNat f).iCycles (p + 1)).hom X).1 with hx
  set y : L.X p := (((mappingCoconeNat f).iCycles (p + 1)).hom X).2 with hy
  have hX : ((mappingCoconeNat f).d (p + 1) (p + 1 + 1)).hom
      ((x, y) : K.X (p + 1) × shiftNegOneX L (p + 1)) = 0 :=
    iCycles_d_apply (mappingCoconeNat f) (p + 1) (p + 1 + 1) X
  rw [mappingCoconeNat_d_hom_apply' f (p + 1) x y] at hX
  have hdy : (L.d p (p + 1)).hom y = (f.f (p + 1)).hom x := by
    have h2 := congrArg Prod.snd hX
    rw [shiftNegOneD_succ_apply, shiftNegOneSucc_apply] at h2
    exact (add_neg_eq_zero.1 h2).symm
  have hd : (L'.d m (m + 1)).hom (μL.μ (show p + s = m by omega) y ((ρ.f s).hom ((N.iCycles s).hom e)) -
      (f'.f m).hom q) = 0 := by
    rw [map_sub, μL.leibniz, hdy, hom_apply_hom_apply_eq_of_comp_eq (ρ.comm s (s + 1)),
      iCycles_d_apply, map_zero, map_zero, smul_zero, add_zero, ← hc h x,
      hom_apply_hom_apply_eq_of_comp_eq (f'.comm m (m + 1)), hq, sub_self]
  refine ⟨L'.cyclesMk _ (m + 1) (by simp) hd, L'.i_cyclesMk _ _ _ _, ?_⟩
  exact LeibnizPairing.coconeLeft_homology_eq_homologyδ μL ρ μK hc h X e q _ hq (L'.i_cyclesMk _ _ _ _)

end Abstract

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain CategoryTheory

universe u

noncomputable section

section Cohomology

variable {k G H : Type u} [CommRing k] [Group G] [Group H] [TopologicalSpace G]
  [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]

def resSymmHomOfIso (e : H ≃ₜ* G) {A : Rep.{u} k G} {B : Rep.{u} k H}
    (f : Rep.res e.toMulEquiv.toMonoidHom A ≅ B) : Rep.res e.symm.toMulEquiv.toMonoidHom B ⟶ A :=
  Rep.ofHom ⟨f.inv.hom.toLinearMap, fun g => LinearMap.ext fun b => by
    change f.inv.hom (B.ρ (e.symm g) b) = A.ρ g (f.inv.hom b)
    rw [Rep.hom_comm_apply f.inv (e.symm g) b]
    change A.ρ (e (e.symm g)) _ = _
    rw [e.apply_symm_apply]⟩


omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
theorem continuous_mulEquiv_toMonoidHom (e : H ≃ₜ* G) : Continuous e.toMulEquiv.toMonoidHom :=
  e.continuous_toFun

def cohomologyIsoOfContinuousMulEquiv (e : H ≃ₜ* G) {A : Rep.{u} k G} {B : Rep.{u} k H}
    [IsDiscreteRep A] [IsDiscreteRep B] (f : Rep.res e.toMulEquiv.toMonoidHom A ≅ B) (n : ℕ) :
    cohomology A n ≅ cohomology B n where
  hom := cohomologyMapAlong e.toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom e) f.hom n
  inv := cohomologyMapAlong e.symm.toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom e.symm)
    (resSymmHomOfIso e f) n
  hom_inv_id := by
    rw [← cohomologyMapAlong_comp]
    refine cohomologyMapAlong_eq_id (φ := e.toMulEquiv.toMonoidHom.comp e.symm.toMulEquiv.toMonoidHom)
      _ _ (MonoidHom.ext fun g => e.apply_symm_apply g) (fun a => ?_) n
    exact Rep.inv_hom_apply _ _ f a
  inv_hom_id := by
    rw [← cohomologyMapAlong_comp]
    refine cohomologyMapAlong_eq_id (φ := e.symm.toMulEquiv.toMonoidHom.comp e.toMulEquiv.toMonoidHom)
      _ _ (MonoidHom.ext fun h => e.symm_apply_apply h) (fun b => ?_) n
    exact Rep.hom_inv_apply _ _ f b

theorem cohomologyIsoOfContinuousMulEquiv_hom (e : H ≃ₜ* G) {A : Rep.{u} k G} {B : Rep.{u} k H}
    [IsDiscreteRep A] [IsDiscreteRep B] (f : Rep.res e.toMulEquiv.toMonoidHom A ≅ B) (n : ℕ) :
    (cohomologyIsoOfContinuousMulEquiv e f n).hom =
      cohomologyMapAlong e.toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom e) f.hom n :=
  rfl

end Cohomology

section Abstract

variable {F L Ω : Type u} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
  [IsScalarTower F L Ω] {E : IntermediateField F Ω} {E' : IntermediateField L Ω}
  (h : E'.restrictScalars F = E)

abbrev unitsEquivOfRestrictScalarsEq : Eˣ ≃* E'ˣ :=
  Units.mapEquiv (fieldEquivOfRestrictScalarsEq h).toMulEquiv

def galUnitsResIso : Rep.res (fixingOfRestrictScalarsEq h).subtype (galUnits.{u} F E) ≅
    Rep.res (fixingMulEquivOfRestrictScalarsEq h).toMonoidHom (galUnits.{u} L E') :=
  Rep.mkIso (Representation.Equiv.mk
    (uliftIntLinearEquiv.{u} (MulEquiv.toAdditive (unitsEquivOfRestrictScalarsEq h)) :
      Additive Eˣ ≃ₗ[ULift.{u} ℤ] Additive E'ˣ) fun _ =>
      LinearMap.ext fun _ => rfl)

abbrev rootsOfUnityEquivOfRestrictScalarsEq (n : ℕ) : rootsOfUnity n E ≃* rootsOfUnity n E' :=
  (fieldEquivOfRestrictScalarsEq h).toMulEquiv.restrictRootsOfUnity n

def galRootsOfUnityResIso (n : ℕ) :
    Rep.res (fixingOfRestrictScalarsEq h).subtype (galRootsOfUnity.{u} F E n) ≅
      Rep.res (fixingMulEquivOfRestrictScalarsEq h).toMonoidHom (galRootsOfUnity.{u} L E' n) :=
  Rep.mkIso (Representation.Equiv.mk
    (uliftIntLinearEquiv.{u} (MulEquiv.toAdditive (rootsOfUnityEquivOfRestrictScalarsEq h n)) :
      Additive (rootsOfUnity n E) ≃ₗ[ULift.{u} ℤ] Additive (rootsOfUnity n E')) fun _ => LinearMap.ext fun _ => rfl)

variable [NumberField F] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 F)))

theorem unitsEquivOfRestrictScalarsEq_mem_sUnitsOf {x : Eˣ} (hx : x ∈ sUnitsOf S E) :
    unitsEquivOfRestrictScalarsEq h x ∈ sUnitsOf (placesOver S : Set (HeightOneSpectrum (𝓞 L))) E' := by
  rw [sUnitsOf_placesOver_eq (L := L) (E := E') S]
  let f : E →ₐ[S.integer F] E' :=
    ((fieldEquivOfRestrictScalarsEq h : E →ₐ[F] E')).restrictScalars (S.integer F)
  refine ⟨hx.1.map f, ?_⟩
  rw [← map_inv]
  exact hx.2.map f

theorem unitsEquivOfRestrictScalarsEq_symm_mem_sUnitsOf {y : E'ˣ}
    (hy : y ∈ sUnitsOf (placesOver S : Set (HeightOneSpectrum (𝓞 L))) E') :
    (unitsEquivOfRestrictScalarsEq h).symm y ∈ sUnitsOf S E := by
  rw [sUnitsOf_placesOver_eq (L := L) (E := E') S] at hy
  let f : E' →ₐ[S.integer F] E :=
    ((fieldEquivOfRestrictScalarsEq h).symm : E' →ₐ[F] E).restrictScalars (S.integer F)
  refine ⟨hy.1.map f, ?_⟩
  rw [← map_inv]
  exact hy.2.map f

def sUnitsEquivOfRestrictScalarsEq : sUnitsOf S E ≃* sUnitsOf (placesOver S : Set (HeightOneSpectrum (𝓞 L))) E' where
  toFun x := ⟨unitsEquivOfRestrictScalarsEq h x, unitsEquivOfRestrictScalarsEq_mem_sUnitsOf h S x.2⟩
  invFun y := ⟨(unitsEquivOfRestrictScalarsEq h).symm y,
    unitsEquivOfRestrictScalarsEq_symm_mem_sUnitsOf h S y.2⟩
  left_inv x := Subtype.ext ((unitsEquivOfRestrictScalarsEq h).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((unitsEquivOfRestrictScalarsEq h).apply_symm_apply y.1)
  map_mul' x y := Subtype.ext (map_mul (unitsEquivOfRestrictScalarsEq h) x.1 y.1)

def galSUnitsResIso : Rep.res (fixingOfRestrictScalarsEq h).subtype (galSUnits S E) ≅
    Rep.res (fixingMulEquivOfRestrictScalarsEq h).toMonoidHom (galSUnits (placesOver S : Set (HeightOneSpectrum (𝓞 L))) E') :=
  Rep.mkIso (Representation.Equiv.mk
    (uliftIntLinearEquiv.{u} (MulEquiv.toAdditive (sUnitsEquivOfRestrictScalarsEq h S)) :
      Additive (sUnitsOf S E) ≃ₗ[ULift.{u} ℤ] Additive (sUnitsOf (placesOver S : Set (HeightOneSpectrum (𝓞 L))) E')) fun _ =>
      LinearMap.ext fun _ => rfl)

end Abstract

section Max

variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))
  (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S)

abbrev gsSubtype : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)) →*
    galUnramifiedOutside F Ω S :=
  (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)).subtype

def gsUnitsIso : Rep.res (gsSubtype S hL) (galUnits.{u} F (maxUnramifiedOutside F Ω S)) ≅
    Rep.res (gsBaseChange S hL).toMulEquiv.toMonoidHom
      (galUnits.{u} L (maxUnramifiedOutside L Ω (placesOver S))) :=
  galUnitsResIso (restrictScalars_maxUnramifiedOutside_eq S hL)

def gsRootsOfUnityIso (n : ℕ) :
    Rep.res (gsSubtype S hL) (galRootsOfUnity.{u} F (maxUnramifiedOutside F Ω S) n) ≅
      Rep.res (gsBaseChange S hL).toMulEquiv.toMonoidHom
        (galRootsOfUnity.{u} L (maxUnramifiedOutside L Ω (placesOver S)) n) :=
  galRootsOfUnityResIso (restrictScalars_maxUnramifiedOutside_eq S hL) n

def gsSUnitsIso : Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S) ≅
    Rep.res (gsBaseChange S hL).toMulEquiv.toMonoidHom (galSUnitsMax L Ω (placesOver S)) :=
  galSUnitsResIso (restrictScalars_maxUnramifiedOutside_eq S hL) S

instance isDiscreteRep_res_gsSubtype_galUnits :
    IsDiscreteRep (Rep.res (gsSubtype S hL) (galUnits.{u} F (maxUnramifiedOutside F Ω S))) :=
  IsDiscreteRep.res continuous_subtype_val (galUnits.{u} F (maxUnramifiedOutside F Ω S))

instance isDiscreteRep_res_gsSubtype_galRootsOfUnity (m : ℕ) :
    IsDiscreteRep (Rep.res (gsSubtype S hL) (galRootsOfUnity.{u} F (maxUnramifiedOutside F Ω S) m)) :=
  IsDiscreteRep.res continuous_subtype_val _

instance isDiscreteRep_res_gsSubtype_galSUnitsMax :
    IsDiscreteRep (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S)) :=
  IsDiscreteRep.res continuous_subtype_val _

variable [IsGalois L Ω]

def gsUnitsCohomologyIso (n : ℕ) :
    cohomology (galUnits.{u} L (maxUnramifiedOutside L Ω (placesOver S))) n ≅
      cohomology (Rep.res (gsSubtype S hL) (galUnits.{u} F (maxUnramifiedOutside F Ω S))) n :=
  cohomologyIsoOfContinuousMulEquiv (gsBaseChange S hL) (gsUnitsIso S hL).symm n

def gsRootsOfUnityCohomologyIso (m n : ℕ) :
    cohomology (galRootsOfUnity.{u} L (maxUnramifiedOutside L Ω (placesOver S)) m) n ≅
      cohomology (Rep.res (gsSubtype S hL) (galRootsOfUnity.{u} F (maxUnramifiedOutside F Ω S) m)) n :=
  cohomologyIsoOfContinuousMulEquiv (gsBaseChange S hL) (gsRootsOfUnityIso S hL m).symm n

def gsSUnitsCohomologyIso (n : ℕ) :
    cohomology (galSUnitsMax L Ω (placesOver S)) n ≅
      cohomology (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S)) n :=
  cohomologyIsoOfContinuousMulEquiv (gsBaseChange S hL) (gsSUnitsIso S hL).symm n

end Max

end

end GroundTheory.ProfCoh
end
