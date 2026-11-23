module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseLocal
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFormal
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Bundle006
public import GroundTheory.ProfiniteCohomology.LocalTateDuality.Bockstein
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
import GroundTheory.ProfiniteCohomology.CupProducts.Bundle001
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.RealPlaces
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory MonoidalCategory GroundTheory.Global

noncomputable section

attribute [local instance 2000] Rep.hV2

section CompLinear

variable {n : ℕ} {R : Type*} [CommRing R]

theorem bijective_of_bijective_comp_linear {X X' Y Y' : Type*} {_ : AddCommGroup Y} {_ : AddCommGroup Y'}
    {_ : Module R Y} {_ : Module R Y'} {F : X → (Y →+ ZMod n)} (hF : Function.Bijective F) {α : X' → X}
    (hα : Function.Bijective α) {γ : Y' →ₗ[R] Y} (hγ : Function.Bijective γ) {F' : X' → (Y' →+ ZMod n)}
    (hF' : ∀ x' y', F' x' y' = F (α x') (γ y')) : Function.Bijective F' :=
  bijective_of_bijective_comp hF hα (γ := γ.toAddMonoidHom) hγ hF'

theorem neg_apply_bilin_eq {X X₀ Y Z : Type*} [AddCommGroup X] [AddCommGroup X₀] [AddCommGroup Y] [AddCommGroup Z]
    {_ : Module R X} {_ : Module R Y} {_ : Module R Z} {_ : Module R X₀} (t : Z →+ ZMod n)
    (B : X →ₗ[R] Y →ₗ[R] Z) (f : X₀ →ₗ[R] X) (x : X₀) (y : Y) :
    -t (B (f x) y) = (t.comp (bilinAddHom B (f (-x)))) y := by
  rw [AddMonoidHom.comp_apply, bilinAddHom_apply, map_neg, map_neg, LinearMap.neg_apply, map_neg]

end CompLinear

section LocalZMod

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [TotallyDisconnectedSpace H] {m : ℕ} [NeZero m] {Dl : Rep.{0} (ULift.{0} ℤ) H} [IsDiscreteRep Dl]
  (Hd : DualityHypotheses m Dl) (hDl : ∀ d : Dl, m • d = 0)

theorem bijective_zmodMulPairing_tTop {r s : ℕ} (h : r + s = 2) :
    Function.Bijective fun x : cohomology (zmodRep.{0} H m) r =>
      Hd.tTop.comp (bilinAddHom (cupPairing (zmodMulPairing m Dl hDl) h) x) := by
  have hM : ∀ a : zmodRep.{0} H m, m • a = 0 := nsmul_zmodRep_eq_zero H m
  have : Finite (zmodRep.{0} H m) := inferInstanceAs (Finite (ULift.{0} (ZMod m)))
  have : IsDiscreteRep (dualRep Dl (zmodRep.{0} H m)) := isDiscreteRep_dualRep _ _
  refine bijective_of_bijective_comp (Hd.bijective_dualityMap_of_group (zmodRep.{0} H m) hM h)
    Function.bijective_id (γ := (cohomologyMap (zmodDualIso m Dl hDl).inv s).hom.toAddMonoidHom)
    (bijective_cohomologyMap_of_comp_eq_id _ _ (zmodDualIso m Dl hDl).inv_hom_id
      (zmodDualIso m Dl hDl).hom_inv_id s) fun x ω => ?_
  change Hd.tTop (cupPairing (zmodMulPairing m Dl hDl) h x ω) =
    Hd.tTop (cupPairing (evalPairing Dl (zmodRep.{0} H m)) h x ((cohomologyMap (zmodDualIso m Dl hDl).inv s).hom ω))
  congr 1
  have e := cupPairing_cohomologyMap (evalPairing Dl (zmodRep.{0} H m)) (𝟙 _) (zmodDualIso m Dl hDl).inv h x ω
  rw [cohomologyMap_id] at e
  refine Eq.trans ?_ e.symm
  rw [← tensorHom_zmodDualIso_zmodMulPairing m Dl hDl, ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.id_comp, Iso.inv_hom_id, MonoidalCategory.id_tensorHom_id, Category.id_comp]


omit [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H] [IsDiscreteRep Dl]
  [NeZero m] in
theorem comp_eq_tensorHom_zmodMulPairing {M Dm : Rep.{0} (ULift.{0} ℤ) H} (μ : M ⊗ Dm ⟶ Dm) (ρ : Dm ⟶ Dl)
    (ι : M ⟶ zmodRep.{0} H m)
    (hμ : ∀ (a : M) (d : Dm), μ.hom (a ⊗ₜ[ULift.{0} ℤ] d) = (ZMod.cast (ι.hom a).down : ℤ) • d) :
    μ ≫ ρ = (ι ⊗ₘ ρ) ≫ zmodMulPairing m Dl hDl := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun a d => ?_))
  change ρ.hom (μ.hom (a ⊗ₜ[ULift.{0} ℤ] d)) = (zmodMulPairing m Dl hDl).hom (ι.hom a ⊗ₜ[ULift.{0} ℤ] ρ.hom d)
  rw [hμ, map_zsmul]
  obtain ⟨b⟩ := ι.hom a
  rw [zmodMulPairing_tmul]


omit [CompactSpace H] [TotallyDisconnectedSpace H] [NeZero m] in
theorem cohomologyMap_cupPairing_of_comp_eq {M Dm M' : Rep.{0} (ULift.{0} ℤ) H} [IsDiscreteRep M]
    [IsDiscreteRep Dm] [IsDiscreteRep M'] (μ : M ⊗ Dm ⟶ Dm) (μ' : M' ⊗ Dl ⟶ Dl) (ρ : Dm ⟶ Dl) (ι : M ⟶ M')
    (hμ : μ ≫ ρ = (ι ⊗ₘ ρ) ≫ μ') {r s q : ℕ} (h : r + s = q) (x : cohomology M r) (y : cohomology Dm s) :
    (cohomologyMap ρ q).hom (cupPairing μ h x y) =
      cupPairing μ' h ((cohomologyMap ι r).hom x) ((cohomologyMap ρ s).hom y) := by
  rw [cupPairing_cohomologyMap, ← hμ, ← cohomologyMap_cupPairing]

end LocalZMod

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n]


omit [NeZero n] in
theorem nsmul_galRootsOfUnity_local (v : S)
    (ω : galRootsOfUnity.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) : n • ω = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((Additive.toMul ω : rootsOfUnity n
    (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) :
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))ˣ) ^ n = 1
  exact (mem_rootsOfUnity n _).1 (Additive.toMul ω).2

def zmodResToLocal (v : S) :
    Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) ⟶
      zmodRep.{0} (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

omit [NeZero n] in
theorem bijective_zmodResToLocal (v : S) : Function.Bijective (zmodResToLocal S ιs n v).hom :=
  Function.bijective_id


omit [NeZero n] in
theorem pairingRes_zmodMulPairing_comp_gsRootsLocalMor (v : S) :
    pairingRes (gsFinFamily S ιs v).toMonoidHom (zmodMulPairing n (gsRoots S n) (nsmul_gsRoots S n)) ≫
        gsRootsLocalMor S ιs n v =
      (zmodResToLocal S ιs n v ⊗ₘ gsRootsLocalMor S ιs n v) ≫
        zmodMulPairing n (galRootsOfUnity.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
          (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (nsmul_galRootsOfUnity_local S n v) := by
  refine comp_eq_tensorHom_zmodMulPairing (nsmul_galRootsOfUnity_local S n v) _ _ _ fun a d => ?_
  obtain ⟨a⟩ := a
  exact zmodMulPairing_tmul n (gsRoots S n) (nsmul_gsRoots S n) a d



theorem gsLocalInvRoots_cupPairing (v : S) {r s : ℕ} (h : r + s = 2)
    (ξ : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)) r)
    (η : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) s) :
    gsLocalInvRoots S ιs n v (cupPairing (pairingRes (gsFinFamily S ιs v).toMonoidHom
        (zmodMulPairing n (gsRoots S n) (nsmul_gsRoots S n))) h ξ η) =
      (localDualityHypotheses (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
        (natCast_ne_zero_adicCompletion S n v)).tTop
        (cupPairing (zmodMulPairing n (galRootsOfUnity.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
          (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (nsmul_galRootsOfUnity_local S n v)) h
          ((cohomologyMap (zmodResToLocal S ιs n v) r).hom ξ) ((cohomologyMap (gsRootsLocalMor S ιs n v) s).hom η)) := by
  refine (gsLocalInvRoots_eq S ιs n v _).trans (congrArg
    (localDualityHypotheses (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
      (natCast_ne_zero_adicCompletion S n v)).tTop ?_)
  exact cohomologyMap_cupPairing_of_comp_eq _ _ _ _
    (pairingRes_zmodMulPairing_comp_gsRootsLocalMor S ιs n v) h ξ η

variable (hμ : ∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ K.1)
include hμ

theorem bijective_gsLocalPairing_two (v : S) :
    Function.Bijective fun ξ : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom
        (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)) 2 =>
      (gsLocalInvRoots S ιs n v).comp ((bilinAddHom (cupPairing (pairingRes (gsFinFamily S ιs v).toMonoidHom
        (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))) (show 0 + 2 = 2 from rfl))).flip ξ) := by
  refine bijective_of_bijective_comp_linear (bijective_zmodMulPairing_tTop
    (localDualityHypotheses (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
      (natCast_ne_zero_adicCompletion S n v)) (nsmul_galRootsOfUnity_local S n v) (show 2 + 0 = 2 from rfl))
    (bijective_cohomologyMap_of_bijective _ (bijective_zmodResToLocal S ιs n v) 2)
    (γ := (cohomologyMap (gsRootsLocalMor S ιs n v) 0).hom)
    (bijective_cohomologyMap_of_bijective _ (bijective_gsRootsLocalMor S ιs n hμ v) 0) fun ξ η => ?_
  change gsLocalInvRoots S ιs n v (cupPairing (pairingRes (gsFinFamily S ιs v).toMonoidHom
    (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))) (show 0 + 2 = 2 from rfl) η ξ) = _
  refine (congrArg (gsLocalInvRoots S ιs n v) (cupPairing_pairingRes_zmodMulPairing_two_zero
    (gsFinFamily S ιs v).toMonoidHom (gsRoots S n) (nsmul_gsRoots S n) (show 2 + 0 = 2 from rfl)
    (show 0 + 2 = 2 from rfl) ξ η).symm).trans ?_
  exact gsLocalInvRoots_cupPairing S ιs n v _ ξ η

theorem bijective_gsLocalPairing_one (v : S) :
    Function.Bijective fun ξ : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom
        (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)) 1 =>
      (gsLocalInvRoots S ιs n v).comp ((bilinAddHom (cupPairing (pairingRes (gsFinFamily S ιs v).toMonoidHom
        (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))) (show 1 + 1 = 2 from rfl))).flip ξ) := by
  refine bijective_of_bijective_comp_linear (bijective_zmodMulPairing_tTop
    (localDualityHypotheses (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
      (natCast_ne_zero_adicCompletion S n v)) (nsmul_galRootsOfUnity_local S n v) (show 1 + 1 = 2 from rfl))
    ((bijective_cohomologyMap_of_bijective _ (bijective_zmodResToLocal S ιs n v) 1).comp neg_bijective)
    (γ := (cohomologyMap (gsRootsLocalMor S ιs n v) 1).hom)
    (bijective_cohomologyMap_of_bijective _ (bijective_gsRootsLocalMor S ιs n hμ v) 1) fun ξ η => ?_
  change gsLocalInvRoots S ιs n v (cupPairing (pairingRes (gsFinFamily S ιs v).toMonoidHom
    (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))) (show 1 + 1 = 2 from rfl) η ξ) = _
  have e := cupPairing_pairingRes_zmodMulPairing_one (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)
    (nsmul_gsRoots S n) (show 1 + 1 = 2 from rfl) ξ η
  refine (congrArg (gsLocalInvRoots S ιs n v) (neg_eq_iff_eq_neg.2 e).symm).trans ?_
  refine (map_neg _ _).trans ?_
  refine (congrArg Neg.neg (gsLocalInvRoots_cupPairing S ιs n v _ ξ η)).trans ?_
  exact neg_apply_bilin_eq _ _ _ _ _

end

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory NumberField IsDedekindDomain GroundTheory.Global

open scoped DirectSum

attribute [local instance 2000] Rep.hV2

noncomputable section

section ULiftCompareAlong

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H] (φ : H →* G) (hφ : Continuous φ) {A : Rep.{0} (ULift.{0} ℤ) G} [IsDiscreteRep A]
  {B : Rep.{0} (ULift.{0} ℤ) H} [IsDiscreteRep B] {C : Rep.{0} ℤ H} [IsDiscreteRep C]

theorem cohomologyMap_uliftInt_cohomologyMapAlong_of (f : Rep.res φ A ⟶ B) (g : uliftIntToIntRep B ⟶ C)
    (f₂ : Rep.res φ (uliftIntToIntRep A) ⟶ C) (hf : ∀ a : A, g.hom (f.hom a) = f₂.hom a) (m : ℕ)
    (x : cohomology A m) :
    (cohomologyMap g m).hom (cohomologyULiftIntAddEquiv B m ((cohomologyMapAlong φ hφ f m).hom x)) =
      (cohomologyMapAlong φ hφ f₂ m).hom (cohomologyULiftIntAddEquiv A m x) := by
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective A m x
  rw [cohomologyMapAlong_cohomologyπ, cohomologyULiftIntAddEquiv_cohomologyπ', cohomologyMap_cohomologyπ,
    cohomologyULiftIntAddEquiv_cohomologyπ', cohomologyMapAlong_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cyclesMap, cochainOf_cocycleι_cocyclesULiftInt, cochainOf_cocycleι_cocyclesMapAlong,
    cochainOf_cocycleι_cocyclesMapAlong, cochainOf_cocycleι_cocyclesULiftInt]
  funext h
  exact hf _

end ULiftCompareAlong

section Bock

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}

theorem exists_cocycle_δ_bockSeq (hn : n ≠ 0) (z : cocycles (zmodRep.{0} G n) 1) :
    ∃ x₁ : cocycles (intRepTriv G) 2,
      cohomologyπ _ 2 x₁ = (δ (bockSeq_shortExact G n hn) 1 2 rfl).hom (cohomologyπ _ 1 z) ∧
      ∀ g h : G, (cochainOf _ (cocycleι _ 2 x₁) ![g, h]).down = bockInt (zmodCocycleHom z) g h := by
  have : NeZero n := ⟨hn⟩
  have hS := bockSeq_shortExact G n hn
  have hχ : ∀ g h : G, zmodCocycleHom z (g * h) = zmodCocycleHom z g + zmodCocycleHom z h :=
    zmodCocycleHom_mul z
  have hlc : IsLocallyConstant fun v : Fin 1 → G =>
      (ULift.up ((zmodCocycleHom z (v 0)).val : ℤ) : intRepTriv G) :=
    IsLocallyConstant.comp ((isLocallyConstant_zmodCocycleHom z).comp_continuous (continuous_apply 0))
      (fun c : ZMod n => (ULift.up (c.val : ℤ) : ULift.{0} ℤ))
  let x₂ : (cochainsComplex (bockSeq G n).X₂).X 1 :=
    mkCochain (bockSeq G n).X₂ (fun v : Fin 1 → G =>
      (ULift.up ((zmodCocycleHom z (v 0)).val : ℤ) : intRepTriv G)) hlc
  have hx₂ : (cochainsMap (bockSeq G n).g).f 1 x₂ = cocycleι (bockSeq G n).X₃ 1 z := by
    apply cochainOf_injective
    rw [cochainOf_cochainsMap_f]
    funext v
    have hv : v = ![v 0] := by funext i; fin_cases i; rfl
    change (zmodReduction G n).hom (ULift.up ((zmodCocycleHom z (v 0)).val : ℤ)) =
      cochainOf _ (cocycleι _ 1 z) v
    rw [zmodReduction_hom_apply]
    apply ULift.ext
    change (((zmodCocycleHom z (v 0)).val : ℤ) : ZMod n) = (cochainOf _ (cocycleι _ 1 z) v).down
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    conv_rhs => rw [hv]
    rfl
  obtain ⟨x₁, hx₁⟩ := exists_cocycle_map_f_eq_d hS 2 z x₂ hx₂
  have hδ := δ_cohomologyπ_of_lift hS rfl z x₂ hx₂ x₁ hx₁
  refine ⟨x₁, hδ.symm, fun g h => ?_⟩
  have e : cochainOf (bockSeq G n).X₂ ((cochainsMap (bockSeq G n).f).f 2 (cocycleι _ 2 x₁)) ![g, h] =
      cochainOf (bockSeq G n).X₂ (((cochainsComplex (bockSeq G n).X₂).d 1 2).hom x₂) ![g, h] :=
    congrArg (fun c => cochainOf (bockSeq G n).X₂ c ![g, h]) hx₁
  rw [cochainOf_cochainsMap_f, cochainOf_d_one_apply] at e
  have e2 := congrArg ULift.down e
  change n • (cochainOf _ (cocycleι _ 2 x₁) ![g, h]).down =
    ((zmodCocycleHom z h).val : ℤ) - ((zmodCocycleHom z (g * h)).val : ℤ) +
      ((zmodCocycleHom z g).val : ℤ) at e2
  have e3 := natCast_mul_bockInt (zmodCocycleHom z) hχ g h
  rw [nsmul_eq_mul] at e2
  apply mul_left_cancel₀ (show (n : ℤ) ≠ 0 by exact_mod_cast hn)
  rw [e2, e3]
  ring

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (ψ : H →* G)

def resIntRepTriv : Rep.res ψ (intRepTriv G) ⟶ intRepTriv H :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

def mulIntRight (A : Rep.{0} (ULift.{0} ℤ) H) : A ⊗ Rep.res ψ (intRepTriv G) ⟶ A :=
  (β_ A (Rep.res ψ (intRepTriv G))).hom ≫ (resIntRepTriv ψ ⊗ₘ 𝟙 A) ≫ intMulPairing H A

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H] in
theorem mulIntRight_tmul (A : Rep.{0} (ULift.{0} ℤ) H) (a : A) (m : ℤ) :
    (mulIntRight ψ A).hom (a ⊗ₜ[ULift.{0} ℤ] (ULift.up m : Rep.res ψ (intRepTriv G)) :
      (A ⊗ Rep.res ψ (intRepTriv G) : Rep _ _)) = m • a :=
  intMulPairing_tmul H A m a

end Bock

section Inv

local notation "ℚ̄" => AlgebraicClosure ℚ

variable (F E : Type) [Field F] [Field E] [Algebra F E]

def galUnitsToZ : uliftIntToIntRep (galUnits.{0} F E) ⟶ galUnitsZ F E :=
  Rep.ofHom ⟨(AddMonoidHom.id (Additive Eˣ)).toIntLinearMap, fun _ => rfl⟩

variable {K : FiniteSubfield}

instance isDiscreteRep_uliftIntToIntRep_galUnits_adic (v : HeightOneSpectrum (𝓞 K.1)) :
    IsDiscreteRep (uliftIntToIntRep (galUnits.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)))) :=
  ⟨fun a => isOpen_stabilizer (galUnits.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) a⟩

def localInvU (v : HeightOneSpectrum (𝓞 K.1)) :
    cohomology (galUnits.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) 2 →+ QZ :=
  (brauerInvZOfIsSepClosure (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))).comp
    ((cohomologyMap (galUnitsToZ (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) 2).hom.toAddMonoidHom.comp
      (cohomologyULiftIntAddEquiv _ 2).toAddMonoidHom)

theorem localInvU_eq (v : HeightOneSpectrum (𝓞 K.1)) :
    localInvU v = (brauerInvZOfIsSepClosure (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))).comp
      ((cohomologyMap (galUnitsToZ (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) 2).hom.toAddMonoidHom.comp
        (cohomologyULiftIntAddEquiv _ 2).toAddMonoidHom) :=
  rfl

variable (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

theorem localInvU_cohomologyMapAlong_gsUnitsLocalMor (v : S)
    (x : cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2) :
    localInvU (v : HeightOneSpectrum (𝓞 K.1)) ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom
      (continuous_toMonoidHom _) (gsUnitsLocalMor S ιs v) 2).hom x) =
      placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1)))
        ((gsLocalRes S (ιs v) 2).hom (cohomologyULiftIntAddEquiv _ 2 x)) := by
  refine (DFunLike.congr_fun (localInvU_eq (v : HeightOneSpectrum (𝓞 K.1))) _).trans ?_
  refine (AddMonoidHom.comp_apply _ _ _).trans ?_
  refine Eq.trans ?_ (placeInv_inr_apply _ _).symm
  refine congrArg (brauerInvZOfIsSepClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
    (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) ?_
  refine (AddMonoidHom.comp_apply _ _ _).trans ?_
  have hres : cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom
      (continuous_toMonoidHom _) (embUnitsMorZ S (ιs v)) 2 = gsLocalRes S (ιs v) 2 := by
    unfold gsLocalRes gsFinFamily
    rfl
  have h := cohomologyMap_uliftInt_cohomologyMapAlong_of
    (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
    (gsUnitsLocalMor S ιs v) (galUnitsToZ _ _) (embUnitsMorZ S (ιs v)) (fun _ => rfl) 2 x
  refine h.trans ?_
  exact congrArg (fun m => m.hom (cohomologyULiftIntAddEquiv _ 2 x)) hres

theorem localInvU_cohomologyMapAlong_gsSUnitsLocalMor (v : S)
    (y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2) :
    localInvU (v : HeightOneSpectrum (𝓞 K.1)) ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom
      (continuous_toMonoidHom _) (gsSUnitsLocalMor S ιs v) 2).hom y) =
      placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1)))
        ((gsLocalRes S (ιs v) 2).hom (cohomologyULiftIntAddEquiv _ 2
          ((cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom y))) := by
  exact (congrArg (localInvU (v : HeightOneSpectrum (𝓞 K.1)))
    (cohomologyMapAlong_cohomologyMap_apply (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
      (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) (gsUnitsLocalMor S ιs v) 2 y).symm).trans
    (localInvU_cohomologyMapAlong_gsUnitsLocalMor S ιs v _)

theorem two_nsmul_placeInv_inl (v : InfinitePlace K.1) (y : localGaloisCohomology K 2 (.inl v)) :
    2 • placeInv (.inl v) y = 0 := by
  by_cases hc : v.IsComplex
  · have := subsingleton_cohomology_two_of_isComplex v hc
    rw [show y = 0 from Subsingleton.elim (α := cohomology (galUnitsZ v.Completion
      (AlgebraicClosure v.Completion)) 2) y 0, map_zero, smul_zero]
  · by_cases hy0 : y = 0
    · rw [hy0, map_zero, smul_zero]
    · change 2 • quadraticInvFun v.Completion (AlgebraicClosure v.Completion) y = 0
      rw [quadraticInvFun_of_ne_zero _ _ hy0, two_nsmul, QZ.mk_half_add_mk_half]

variable [Fintype S]

end Inv

end

end GroundTheory.ProfCoh
end
