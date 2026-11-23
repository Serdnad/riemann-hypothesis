module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseTransportGS
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseDefs
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SInvariantToInvariantsEqZeroIff
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SUnits
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFormal
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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

open CategoryTheory IsDedekindDomain NumberField GroundTheory.Global

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)

def gsUnitsLocalMor (v : S) :
    Rep.res (gsFinFamily S ιs v).toMonoidHom (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) ⟶
      galUnits ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :=
  Rep.ofHom ⟨uliftIntLinearMap (MonoidHom.toAdditive (α := (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)
      (β := (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))ˣ)
      (Units.map ((ιs v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom.toMonoidHom)),
    fun σ => LinearMap.ext fun x => congrArg Additive.ofMul
      (Units.ext (gsFinFamily_apply S ιs v σ ((Additive.toMul x : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
        maxUnramifiedOutside K.1 ℚ̄ S)))⟩

def gsSUnitsLocalMor (v : S) :
    Rep.res (gsFinFamily S ιs v).toMonoidHom (galSUnitsMax K.1 ℚ̄ S) ⟶
      galUnits ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :=
  (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) ≫
    gsUnitsLocalMor S ιs v

def gsRootsOmegaMor (v : S) :
    Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n) ⟶
      galRootsOfUnity ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n :=
  Rep.ofHom ⟨uliftIntLinearMap (MonoidHom.toAdditive (α := rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S))
      (β := rootsOfUnity n (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))
      (restrictRootsOfUnity ((ιs v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom n)),
    fun σ => LinearMap.ext fun ζ => congrArg Additive.ofMul (Subtype.ext (Units.ext
      (gsFinFamily_apply S ιs v σ ((((Additive.toMul ζ : rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S)) :
        (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) : maxUnramifiedOutside K.1 ℚ̄ S))))⟩

theorem comp_nsmul_id_eq {C : Type*} [Category C] [Preadditive C] {X Y : C} (f : X ⟶ Y) (m : ℕ) :
    f ≫ (m • 𝟙 Y) = (m • 𝟙 X) ≫ f := by
  rw [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id, Category.id_comp]

variable [NeZero n]

def gsKummerLocalMap (v : S) :
    (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) n).map
        (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom) ⟶
      kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n where
  τ₁ := gsRootsOmegaMor S ιs n v
  τ₂ := gsSUnitsLocalMor S ιs v
  τ₃ := gsSUnitsLocalMor S ιs v
  comm₁₂ := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
  comm₂₃ := (comp_nsmul_id_eq (gsSUnitsLocalMor S ιs v) n).trans
    (congrArg (· ≫ gsSUnitsLocalMor S ιs v)
      (Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))))

abbrev gsUnitsCompact (m : ℕ) :=
  compactCohomology (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S)
    (fun v : S => galUnits ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (gsSUnitsLocalMor S ιs) m

abbrev gsRootsCompact (m : ℕ) :=
  compactCohomology (gsFinFamily S ιs) (gsRoots S n)
    (fun v : S => galRootsOfUnity ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (gsRootsOmegaMor S ιs n) m

def gsRootsComparison (m : ℕ) :
    compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) m ⟶ gsRootsCompact S ιs n m :=
  compactCohomologyMap (gsFinFamily S ιs) (𝟙 (gsRoots S n)) (gsRootsOmegaMor S ιs n)
    (fun _ => Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))) m

theorem gsKummer_shortExact (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal) :
    (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) n).ShortExact :=
  sUnitsKummerSequence_shortExact S n hnS

theorem localKummer_shortExact (v : S) :
    (kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n).ShortExact :=
  kummerSequence_shortExact n (by exact_mod_cast NeZero.ne n)

def gsKummerCompactδ (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal) (m : ℕ) :
    gsUnitsCompact S ιs m ⟶ gsRootsCompact S ιs n (m + 1) :=
  compactδ (gsFinFamily S ιs) (gsKummerLocalMap S ιs n) (gsKummer_shortExact S n hnS)
    (localKummer_shortExact S n) m

end

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField GroundTheory.Global

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))

theorem mem_of_forall_gsOpenSubgroup_fixes {L : FiniteSubfield} [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) (y : maxUnramifiedOutside K.1 ℚ̄ S)
    (hy : ∀ σ ∈ gsOpenSubgroup S hL, σ y = y) : (y : ℚ̄) ∈ L.1 := by
  have hmem : y ∈ IntermediateField.fixedField (gsEmbedding (S := S) hL).fieldRange.fixingSubgroup := by
    intro σ
    refine hy σ ((mem_gsOpenSubgroup_iff S hL σ).2 fun x => ?_)
    exact σ.2 ⟨_, ⟨x, rfl⟩⟩
  rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
  obtain ⟨x, hx⟩ := hmem
  rw [← hx]
  exact x.2

variable (n : ℕ)

theorem rootsOfUnity_mem_of_gsOpenSubgroup_le {L : FiniteSubfield} [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ n = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    (hU : gsOpenSubgroup S hL ≤ W₀) (hn0 : n ≠ 0) (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (ζ : ℚ̄) (hζ : ζ ^ n = 1) : ζ ∈ L.1 := by
  have hmem := mem_maxUnramifiedOutside_of_pow_eq_one S hn0 hnS hζ
  have hne : (⟨ζ, hmem⟩ : maxUnramifiedOutside K.1 ℚ̄ S) ≠ 0 := fun h => by
    have h0 : ζ = 0 := congrArg Subtype.val h
    rw [h0, zero_pow hn0] at hζ
    exact zero_ne_one hζ
  have hpow : (Units.mk0 _ hne) ^ n = 1 := Units.ext (Subtype.ext hζ)
  exact mem_of_forall_gsOpenSubgroup_fixes S hL ⟨ζ, hmem⟩ fun σ hσ => hW₀ σ (hU hσ) _ hpow

theorem nonempty_addEquiv_gsRoots_of_places [NeZero n] (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal) :
    Nonempty (gsRoots S n ≃+ ZMod n) := by
  have hcard : Nat.card (Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S))) = Nat.card (ZMod n) := by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℚ̄ n
    have hmem := mem_maxUnramifiedOutside_of_pow_eq_one S (NeZero.ne n) hnS hζ.pow_eq_one
    have hprim : IsPrimitiveRoot (⟨ζ, hmem⟩ : maxUnramifiedOutside K.1 ℚ̄ S) n :=
      IsPrimitiveRoot.of_map_of_injective (f := (maxUnramifiedOutside K.1 ℚ̄ S).val) hζ
        Subtype.val_injective
    rw [Nat.card_congr Additive.toMul, hprim.card_rootsOfUnity, Nat.card_zmod]
  have : IsAddCyclic (Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S))) := inferInstance
  exact ⟨addEquivOfAddCyclicCardEq hcard⟩

end

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

noncomputable section

section Algebra

variable {n : ℕ} [NeZero n]

theorem exists_isUnit_mul_of_surjective_of_bijective {Y : Type*} [AddCommGroup Y] (f g : Y →+ ZMod n)
    (hf : Function.Surjective f) (hg : Function.Bijective g) :
    ∃ c : ZMod n, IsUnit c ∧ ∀ y, f y = c * g y := by
  obtain ⟨y₁, hy₁⟩ := hg.2 1
  have hy : ∀ y, y = (g y).val • y₁ := fun y => hg.1 (by
    rw [map_nsmul, hy₁, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val])
  have hfy : ∀ y, f y = f y₁ * g y := fun y => by
    conv_lhs => rw [hy y]
    rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
  refine ⟨f y₁, ?_, hfy⟩
  obtain ⟨y, hy1⟩ := hf 1
  exact IsUnit.of_mul_eq_one (g y) ((hfy y).symm.trans hy1)

omit [NeZero n] in
private theorem bijective_of_bijective_smul_transport {X X' Y Y' : Type*}
    [AddCommGroup Y] [AddCommGroup Y'] (F : X → (Y →+ ZMod n)) (F' : X' → (Y' →+ ZMod n))
    (eX : X ≃ X') (eY : Y ≃+ Y') (c : ZMod n) (hc : IsUnit c)
    (hbij : Function.Bijective F) (hF' : ∀ x y, F' (eX x) (eY y) = c * F x y) :
    Function.Bijective F' := by
  have hF : Function.Bijective fun x => c • F x := by
    refine ⟨fun x x' h => hbij.1 (AddMonoidHom.ext fun y => ?_), fun χ => ?_⟩
    · have e := DFunLike.congr_fun h y
      simp only [AddMonoidHom.smul_apply, smul_eq_mul] at e
      exact hc.mul_left_cancel e
    · obtain ⟨x, hx⟩ := hbij.2 ((hc.unit⁻¹ : (ZMod n)ˣ) • χ)
      refine ⟨x, AddMonoidHom.ext fun y => ?_⟩
      have e := DFunLike.congr_fun hx y
      simp only [AddMonoidHom.smul_apply, smul_eq_mul, Units.smul_def] at e ⊢
      rw [e, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  refine bijective_of_bijective_comp hF eX.symm.bijective (γ := eY.symm.toAddMonoidHom) eY.symm.bijective
    fun x' y' => ?_
  simpa only [Equiv.apply_symm_apply, AddEquiv.apply_symm_apply, AddEquiv.coe_toAddMonoidHom,
    AddMonoidHom.smul_apply, smul_eq_mul] using hF' (eX.symm x') (eY.symm y')

omit [NeZero n] in
theorem bijective_of_transport {X X' Y Y' W W' : Type*} [AddCommGroup X] [AddCommGroup X'] [AddCommGroup Y]
    [AddCommGroup Y'] [AddCommGroup W] [AddCommGroup W'] (B : Y →+ X →+ W) (B' : Y' →+ X' →+ W')
    (T : W →+ ZMod n) (f : W' →+ ZMod n) (eX : X ≃+ X') (eY : Y ≃+ Y') (eW : W ≃+ W')
    (hcup : ∀ y x, B' (eY y) (eX x) = eW (B y x)) (c : ZMod n) (hc : IsUnit c)
    (hf : ∀ w, f (eW w) = c * T w) (hbij : Function.Bijective fun x => T.comp (B.flip x)) :
    Function.Bijective fun x' => f.comp (B'.flip x') := by
  refine bijective_of_bijective_smul_transport (fun x => T.comp (B.flip x))
    (fun x' => f.comp (B'.flip x')) eX.toEquiv eY c hc hbij fun x y => ?_
  exact (congrArg f (hcup y x)).trans (hf (B y x))

end Algebra

section Level

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K L : FiniteSubfield} [Fact (K ≤ L)] (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) (n : ℕ) [NeZero n]

def GsBaseBijective (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (t : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 3 →+ ZMod n) : Prop :=
  ∀ {r s : ℕ} (h : r + s = 3), Function.Bijective (zmodCompactDualityMap (gsFinFamily S ιs) (gsRoots S n)
    (nsmul_gsRoots S n) U h t)

def GsCoresSurjective (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (t : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 3 →+ ZMod n) : Prop :=
  Function.Surjective (t.comp (compactCores (gsFinFamily S ιs) U (gsRoots S n) 3).hom.toAddMonoidHom)


variable {S ιs n} in
def GsLevelBijective (T : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 3 →+ ZMod n) : Prop :=
  Function.Bijective T ∧ ∀ {r s : ℕ} (h : r + s = 3), Function.Bijective (compactZmodDualityMap (gsFinFamily S ιs)
    (gsRoots S n) (nsmul_gsRoots S n) T h)



theorem bijective_zmodCompactDualityMap_gsOpenSubgroup
    (t : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 3 →+ ZMod n)
    (TL : compactCohomologyRes (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
      (gsRoots (K := L) (placesOver S) n) 3 →+ ZMod n) (hLev : GsLevelBijective TL)
    (hsurj : GsCoresSurjective S ιs n (gsOpenSubgroup S hL) t) :
    GsBaseBijective S ιs n (gsOpenSubgroup S hL) t := by
  intro r s h
  have hTL := hLev.1
  let f := (gsRootsOfUnityIso S hL n).symm
  let eW := (gsMackeyCompactIso hL ιs f 3).toLinearEquiv.toAddEquiv
  have hex := exists_isUnit_mul_of_surjective_of_bijective
    (t.comp (compactCores (gsFinFamily S ιs) (gsOpenSubgroup S hL) (gsRoots S n) 3).hom.toAddMonoidHom)
    (TL.comp eW.symm.toAddMonoidHom) hsurj (hTL.comp eW.symm.bijective)
  refine hex.elim fun c hc => ?_
  let U := gsOpenSubgroup (F := K.1) (L := L.1) (Ω := ℚ̄) S hL
  let θ := gsBaseChange (F := K.1) (L := L.1) (Ω := ℚ̄) S hL
  let SL := placesOver (F := K.1) (L := L.1) S
  let φL := gsFinFamily (F := L.1) (Ω := ℚ̄) SL
    (gsMackeyEmbeddings (F := K.1) (L := L.1) (Ω := ℚ̄) hL ιs)
  let D := gsRoots S n
  let DL := gsRoots (K := L) SL n
  let DU := Rep.res (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype D
  let hn := nsmul_gsRoots S n
  let hnL := nsmul_gsRoots (K := L) SL n
  let eY := (gsMackeyCompactIso (F := K.1) (L := L.1) (Ω := ℚ̄)
    hL ιs (A' := DL) (A := DU) f s).toLinearEquiv.toAddEquiv
  let eX := (cohomologyIsoOfContinuousMulEquiv θ (zmodRepResIso θ n) r).toLinearEquiv.toEquiv
  let tU := t.comp
    (compactCores (gsFinFamily S ιs) (gsOpenSubgroup S hL) (gsRoots S n) 3).hom.toAddMonoidHom
  have hscale (w : compactCohomologyRes φL DL 3) : tU (eW w) = c * TL w :=
    (hc.2 (eW w)).trans (congrArg (fun w => c * TL w) (eW.symm_apply_apply w))
  have hbij := hLev.2 h
  refine bijective_of_bijective_smul_transport _ _ eX eY c hc.1 hbij ?_
  intro x y
  have hcup := gsMackeyCompactIso_compactCupRes_zmod (F := K.1) (L := L.1) (Ω := ℚ̄)
    hL ιs n (D' := DL) (D := DU) hnL hn f ((Nat.add_comm s r).trans h) y x
  have htrace := congrArg tU hcup.symm
  let w := compactCupRes φL (zmodMulPairingRight n DL hnL) ((Nat.add_comm s r).trans h) y x
  have htransport := htrace.trans (hscale w)
  -- The kernel checks the definitional equality with the bundled duality maps.
  run_tac Lean.Elab.Tactic.withMainContext do
    let proof ← Lean.Meta.getFVarFromUserName `htransport
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.assign (Lean.Meta.mkExpectedPropHint proof (← goal.getType))

end Level

end

end GroundTheory.ProfCoh
end
