module

public import GroundTheory.ProfiniteCohomology.CompactSupportCohomology
public import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.ConePairing
import GroundTheory.ProfiniteCohomology.Bundle001
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.DivisorModule
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
public import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
public import Mathlib.Algebra.Lie.OfAssociative
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Bundle002
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.TateCohomology.CupCochains

@[expose] public section

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

omit [CommRing k] in
theorem mappingCoconeNat_d_hom_apply' {k : Type u} [CommRing k] {K L : CochainComplex (ModuleCat.{u} k) ℕ} (f : K ⟶ L)
    (n : ℕ) (x : K.X n) (y : shiftNegOneX L n) :
    ((mappingCoconeNat f).d n (n + 1)).hom ((x, y) : K.X n × shiftNegOneX L n) =
      (((K.d n (n + 1)).hom x, shiftNegOneSucc L n ((f.f n).hom x) + (shiftNegOneD L n).hom y) :
        K.X (n + 1) × shiftNegOneX L (n + 1)) := by
  rw [mappingCoconeNat_d]
  rfl

theorem LeibnizPairing.coconeLeft_homology_eq_homologyδ {p s m : ℕ} (h : p + 1 + s = m + 1)
    (X : (mappingCoconeNat f).cycles (p + 1)) (e : N.cycles s) (q : K'.X m) (w : L'.cycles m)
    (hq : (K'.d m (m + 1)).hom q = μK.μ h (((mappingCoconeNat f).iCycles (p + 1)).hom X).1 ((N.iCycles s).hom e))
    (hw : (L'.iCycles m).hom w =
      μL.μ (show p + s = m by omega) (show L.X p from (((mappingCoconeNat f).iCycles (p + 1)).hom X).2)
        ((ρ.f s).hom ((N.iCycles s).hom e)) - (f'.f m).hom q) :
    (LeibnizPairing.coconeLeft μL ρ μK hc).homology h (((mappingCoconeNat f).homologyπ (p + 1)).hom X)
        ((N.homologyπ s).hom e) =
      (mappingCoconeNat.homologyδ f' m).hom ((L'.homologyπ m).hom w) := by
  rw [LeibnizPairing.homology_homologyπ]
  obtain ⟨c', hc'1, hc'2⟩ := mappingCoconeNat.exists_homologyδ_homologyπ f' m w
  rw [hc'1]
  have key : (LeibnizPairing.coconeLeft μL ρ μK hc).cycles h X e =
      c' + ((mappingCoconeNat f').toCycles m (m + 1)).hom ((q, 0) : K'.X m × shiftNegOneX L' m) := by
    apply iCycles_hom_injective
    have e1 := LeibnizPairing.iCycles_cycles (LeibnizPairing.coconeLeft μL ρ μK hc) h X e
    have e2 := iCycles_toCycles_hom_apply (mappingCoconeNat f') m (m + 1)
      ((q, 0) : K'.X m × shiftNegOneX L' m)
    rw [map_add (f := _), e1, e2, mappingCoconeNat_d_hom_apply']
    refine Prod.ext ?_ ?_
    · change μK.μ h (((mappingCoconeNat f).iCycles (p + 1)).hom X).1 ((N.iCycles s).hom e) =
        (((mappingCoconeNat f').iCycles (m + 1)).hom c').1 + (K'.d m (m + 1)).hom q
      rw [show (((mappingCoconeNat f').iCycles (m + 1)).hom c').1 = 0 from congrArg Prod.fst hc'2, zero_add, hq]
    · change μL.μ (show p + s = m by omega) (show L.X p from (((mappingCoconeNat f).iCycles (p + 1)).hom X).2)
          ((ρ.f s).hom ((N.iCycles s).hom e)) =
        (((mappingCoconeNat f').iCycles (m + 1)).hom c').2 +
          (shiftNegOneSucc L' m ((f'.f m).hom q) + (shiftNegOneD L' m).hom 0)
      rw [show (((mappingCoconeNat f').iCycles (m + 1)).hom c').2 =
          shiftNegOneSucc L' m ((L'.iCycles m).hom w) from congrArg Prod.snd hc'2, map_zero, add_zero,
        shiftNegOneSucc_apply, shiftNegOneSucc_apply, hw]
      exact (sub_add_cancel _ _).symm
  rw [key, map_add (f := _)]
  exact (congrArg (_ + ·) (homologyπ_toCycles_hom_apply (mappingCoconeNat f') m (m + 1)
    ((q, 0) : K'.X m × shiftNegOneX L' m))).trans (add_zero _)

end Abstract

section Compact

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
  {Aᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Cᵥ v)]
  {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}


omit [IsDiscreteRep A] [IsDiscreteRep B] [∀ v, IsDiscreteRep (Aᵥ v)] in
theorem homologyδ_homologyπ_eq_localToCompact {m : ℕ}
    (w : (piComplex fun v => cochainsComplex (Cᵥ v)).cycles m) :
    (mappingCoconeNat.homologyδ (localRes φ C Cᵥ c) m).hom
        (((piComplex fun v => cochainsComplex (Cᵥ v)).homologyπ m).hom w) =
      (localToCompact φ C Cᵥ c m).hom (fun v => ((cochainsComplex (Cᵥ v)).homologyπ m).hom
        ((HomologicalComplex.cyclesMap (piProj (fun v => cochainsComplex (Cᵥ v)) v) m).hom w)) := by
  have e : (localCohomologyIso Cᵥ m).hom.hom
      (((piComplex fun v => cochainsComplex (Cᵥ v)).homologyπ m).hom w) =
      fun v => ((cochainsComplex (Cᵥ v)).homologyπ m).hom
        ((HomologicalComplex.cyclesMap (piProj (fun v => cochainsComplex (Cᵥ v)) v) m).hom w) :=
    funext fun v => (piHomologyIso_hom_apply _ m _ v).trans (homologyMap_homologyπ_apply _ m w)
  rw [← e, localToCompact]
  exact (hom_apply_hom_apply_of_comp_eq (Iso.hom_inv_id_assoc (localCohomologyIso Cᵥ m) _) _).symm

end Compact

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {I : Type} {H : I → Type} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)]
  (φ : ∀ i, H i →* G) (hφ : ∀ i, Continuous (φ i)) (A : Type) [AddCommGroup A]

theorem finite_divFunEval_ne_zero (n : ℕ) (x : cohomology (divFunRep φ A) n) :
    {i | (cohomologyMapAlong (φ i) (hφ i) (divFunEval φ A i) n).hom x ≠ 0}.Finite := by
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective (divFunRep φ A) n x
  set c := cochainOf (A := divFunRep φ A) (cocycleι (A := divFunRep φ A) (p := n) z) with hc
  have hfin : (Set.range c).Finite := (isLocallyConstant_cochainOf _).range_finite
  have hT : (⋃ f ∈ Set.range c, {i | ((f : divFun φ A) : I → G → A) i ≠ 0}).Finite :=
    hfin.biUnion fun f _ => (f : divFun φ A).2.1
  refine hT.subset fun i hi => ?_
  by_contra hiT
  apply hi
  have hz : cocyclesMapAlong (φ i) (hφ i) (divFunEval φ A i) n z = 0 := by
    apply cocycleι_injective
    apply cochainOf_injective
    rw [cochainOf_cocycleι_cocyclesMapAlong, map_zero]
    funext h
    rw [divFunEval_hom_apply]
    have hmem : ((c (⇑(φ i) ∘ h) : divFun φ A) : I → G → A) i = 0 := by
      by_contra hne
      exact hiT (Set.mem_biUnion ⟨_, rfl⟩ hne)
    change ((c (⇑(φ i) ∘ h) : divFun φ A) : I → G → A) i 1 = 0
    rw [hmem]
    rfl
  change (cohomologyMapAlong (φ i) (hφ i) (divFunEval φ A i) n) (cohomologyπ (divFunRep φ A) n z) = 0
  rw [cohomologyMapAlong_cohomologyπ, hz, map_zero]

end

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

section DecompHom

variable {K E Kv Ωv : Type u} [Field K] [Field E] [Field Kv] [Field Ωv] [Algebra K E]
  [Algebra K Kv] [Algebra Kv Ωv] [Algebra K Ωv] [IsScalarTower K Kv Ωv]


variable (Kv) in
noncomputable def decompHom [Normal K E] (ι : E →ₐ[K] Ωv) : Gal(Ωv/Kv) →* Gal(E/K) :=
  letI : Algebra E Ωv := ι.toRingHom.toAlgebra
  haveI : IsScalarTower K E Ωv := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  (AlgEquiv.restrictNormalHom E).comp (AlgEquiv.restrictScalarsHom K)

theorem decompHom_apply [Normal K E] (ι : E →ₐ[K] Ωv) (σ : Gal(Ωv/Kv)) (x : E) :
    ι (decompHom Kv ι σ x) = σ (ι x) := by
  let _ : Algebra E Ωv := ι.toRingHom.toAlgebra
  have : IsScalarTower K E Ωv := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) E x

theorem decompHom_eq_iff [Normal K E] (ι : E →ₐ[K] Ωv) (σ : Gal(Ωv/Kv)) (τ : Gal(E/K)) :
    decompHom Kv ι σ = τ ↔ ∀ x, ι (τ x) = σ (ι x) := by
  constructor
  · rintro rfl x
    exact decompHom_apply ι σ x
  · intro h
    ext x
    apply ι.injective
    change ι _ = ι _
    rw [decompHom_apply, h]

theorem continuous_decompHom [Normal K E] (ι : E →ₐ[K] Ωv) : Continuous (decompHom Kv ι) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro U hU
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨L, hL, hLU⟩ := hU
  let b := Module.finBasis K L
  let T : IntermediateField Kv Ωv := IntermediateField.adjoin Kv (Set.range fun i => ι (b i))
  have hT : FiniteDimensional Kv T := by
    refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
    obtain ⟨i, rfl⟩ := hx
    exact ((Algebra.IsAlgebraic.isAlgebraic (R := K) ((b i : L) : E)).isIntegral.map ι).tower_top
  apply mem_nhds_iff.mpr
  refine ⟨T.fixingSubgroup, fun σ hσ => hLU ?_, T.fixingSubgroup_isOpen, one_mem _⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  have hb : ∀ i, decompHom Kv ι σ (b i : E) = b i := fun i => by
    apply ι.injective
    change ι _ = ι _
    rw [decompHom_apply]
    exact hσ _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  intro y hy
  have hy' : y = ∑ i, b.repr ⟨y, hy⟩ i • (b i : E) := by
    have := congrArg L.val (b.sum_repr ⟨y, hy⟩)

    rw [map_sum] at this
    simp only [map_smul] at this
    exact this.symm

  rw [hy', map_sum]
  simp only [map_smul, hb]

theorem exists_eq_comp_of_normal [Normal K E] (ι ι' : E →ₐ[K] Ωv) :
    ∃ g : Gal(E/K), ι' = ι.comp (g : E →ₐ[K] E) := by
  let _ : Algebra E Ωv := ι.toRingHom.toAlgebra
  have : IsScalarTower K E Ωv := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  refine ⟨ι'.restrictNormal' E, ?_⟩
  ext x
  exact (AlgHom.restrictNormal_commutes ι' E x).symm

theorem decompHom_comp_val [Normal K E] (ι : E →ₐ[K] Ωv) (N : IntermediateField K E) [Normal K N] :
    decompHom Kv (ι.comp N.val) = (AlgEquiv.restrictNormalHom N).comp (decompHom Kv ι) := by
  ext σ x
  apply ι.injective
  change (ι.comp N.val) (decompHom Kv (ι.comp N.val) σ x) =
    ι ((AlgEquiv.restrictNormalHom N (decompHom Kv ι σ) x : N) : E)
  rw [decompHom_apply, AlgEquiv.restrictNormalHom_apply, decompHom_apply]
  rfl

theorem nonempty_algHom_of_isSepClosed [Algebra.IsSeparable K E] [IsSepClosed Ωv] :
    Nonempty (E →ₐ[K] Ωv) :=
  ⟨IsSepClosed.lift⟩

end DecompHom

section Conj

variable {k G H : Type u} [CommRing k] [Group G] [Group H] [TopologicalSpace G]
  [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H] [CompactSpace G]

noncomputable def conjResMor (A : Rep.{u} k G) {φ φ' : H →* G} (g : G)
    (h : ∀ x, φ' x = g⁻¹ * φ x * g) : Rep.res φ A ⟶ Rep.res φ' A :=
  Rep.ofHom ⟨A.ρ g⁻¹, fun x => by
    ext a
    change A.ρ g⁻¹ (A.ρ (φ x) a) = A.ρ (φ' x) (A.ρ g⁻¹ a)
    rw [h, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group⟩


theorem cohomologyMapAlong_conj (A : Rep.{u} k G) [IsDiscreteRep A] {φ φ' : H →* G}
    (hφ : Continuous φ) (hφ' : Continuous φ') (g : G) (h : ∀ x, φ' x = g⁻¹ * φ x * g)
    [IsDiscreteRep (Rep.res φ A)] [IsDiscreteRep (Rep.res φ' A)] (n : ℕ) :
    cohomologyMapAlong φ' hφ' (𝟙 _) n =
      cohomologyMapAlong φ hφ (𝟙 _) n ≫
        cohomologyMapAlong (MonoidHom.id H) continuous_id (conjResMor A g h) n := by
  have hφ'eq : φ' = (innerConjHom g).comp φ := MonoidHom.ext fun x => h x
  subst hφ'eq
  have e1 : (𝟙 (Rep.res ((innerConjHom g).comp φ) A)) =
      (Rep.resFunctor φ).map (innerConjMor A g) ≫ conjResMor A g h := by
    ext a
    change a = A.ρ g⁻¹ (A.ρ g a)
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have e2 : conjResMor A g h =
      (Rep.resFunctor (MonoidHom.id H)).map (𝟙 (Rep.res φ A)) ≫ conjResMor A g h := by
    ext a
    rfl
  calc cohomologyMapAlong ((innerConjHom g).comp φ) hφ' (𝟙 _) n
      = cohomologyMapAlong ((innerConjHom g).comp φ) ((continuous_innerConjHom g).comp hφ)
          ((Rep.resFunctor φ).map (innerConjMor A g) ≫ conjResMor A g h) n := by rw [← e1]
    _ = cohomologyInnerConj A n g ≫ cohomologyMapAlong φ hφ (conjResMor A g h) n :=
        cohomologyMapAlong_comp _ _ _ _ _ _ _
    _ = cohomologyMapAlong φ hφ (conjResMor A g h) n := by
        rw [cohomologyInnerConj_eq_id, Category.id_comp]
    _ = cohomologyMapAlong (φ.comp (MonoidHom.id H)) (hφ.comp continuous_id)
          ((Rep.resFunctor (MonoidHom.id H)).map (𝟙 (Rep.res φ A)) ≫ conjResMor A g h) n := by
        rw [← e2]
        rfl
    _ = cohomologyMapAlong φ hφ (𝟙 _) n ≫
          cohomologyMapAlong (MonoidHom.id H) continuous_id (conjResMor A g h) n :=
        cohomologyMapAlong_comp _ _ _ _ _ _ _

end Conj

section Local

variable {k K E Kv Ωv : Type u} [CommRing k] [Field K] [Field E] [Field Kv] [Field Ωv]
  [Algebra K E] [Algebra K Kv] [Algebra Kv Ωv] [Algebra K Ωv] [IsScalarTower K Kv Ωv]
  [IsGalois K E]


end Local

section Places

open NumberField IsDedekindDomain

variable {K Ω Kv Ωv : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [Field Kv] [Field Ωv] [Algebra K Kv] [Algebra Kv Ωv] [Algebra K Ωv] [IsScalarTower K Kv Ωv]


variable (Kv) in
noncomputable def decompHomS (S : Set (HeightOneSpectrum (𝓞 K))) (ι : Ω →ₐ[K] Ωv) :
    Gal(Ωv/Kv) →* galUnramifiedOutside K Ω S :=
  decompHom Kv (ι.comp (maxUnramifiedOutside K Ω S).val)

theorem decompHomS_eq (S : Set (HeightOneSpectrum (𝓞 K))) (ι : Ω →ₐ[K] Ωv) :
    decompHomS Kv S ι =
      (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S)).comp (decompHom Kv ι) :=
  decompHom_comp_val ι _

theorem continuous_decompHomS (S : Set (HeightOneSpectrum (𝓞 K))) (ι : Ω →ₐ[K] Ωv) :
    Continuous (decompHomS Kv S ι) :=
  continuous_decompHom _



end Places

end GroundTheory.ProfCoh
end
