module

public import Development.EtaleCohomology.EtaleSheaves.Bundle070
public import Development.EtaleCohomology.EtaleSheaves.Bundle071
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle015
public import Development.EtaleCohomology.EtaleSheaves.Bundle072
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.TruncationPieces LateralTheory.E.FiltPf LateralTheory.E.TruncPf
open CochainComplex.HomComplex

namespace LateralTheory.E.TruncationInclusionIso

section Gen
open ComplexShape renaming embeddingUpIntGE → eG

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

abbrev sT (K : CochainComplex C ℤ) (a : ℤ) : CochainComplex C ℤ := (K.restriction (eG a)).extend (eG a)

def comp (K : CochainComplex C ℤ) (a : ℤ) {k : ℕ} {i : ℤ} (hk : (eG a).f k = i) : (sT K a).X i ⟶ K.X i :=
  ((K.restriction (eG a)).extendXIso (eG a) hk).hom ≫ (K.restrictionXIso (eG a) hk).hom

theorem comp_indep (K : CochainComplex C ℤ) (a : ℤ) {k k' : ℕ} {i : ℤ} (hk : (eG a).f k = i)
    (hk' : (eG a).f k' = i) : comp K a hk = comp K a hk' := by
  obtain rfl : k = k' := (eG a).injective_f (hk.trans hk'.symm)
  rfl

theorem sq (K : CochainComplex C ℤ) (a : ℤ) {k : ℕ} {i j : ℤ} (hi : (eG a).f k = i) (hj : (eG a).f (k + 1) = j) :
    comp K a hi ≫ K.d i j = (sT K a).d i j ≫ comp K a hj := by
  rw [HomologicalComplex.extend_d_eq _ _ hi hj, HomologicalComplex.restriction_d_eq _ _ hi hj]
  simp only [comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

theorem le_of_f {a : ℤ} {k : ℕ} {i : ℤ} (hk : (eG a).f k = i) : a ≤ i := by
  change a + (k : ℤ) = i at hk; omega

theorem f_toNat {a i : ℤ} (h : a ≤ i) : (eG a).f (i - a).toNat = i := by
  change a + ((i - a).toNat : ℤ) = i; omega

theorem zero_below (K : CochainComplex C ℤ) {a i : ℤ} (h : i < a) : IsZero ((sT K a).X i) :=
  HomologicalComplex.isZero_extend_X _ _ i (fun _ hk => by have := le_of_f hk; omega)

def ιT (K : CochainComplex C ℤ) (a : ℤ) : sT K a ⟶ K where
  f i := if h : a ≤ i then comp K a (f_toNat h) else 0
  comm' i j hij := by
    change i + 1 = j at hij
    by_cases h : a ≤ i
    · rw [dite_eq_left h, dite_eq_left (by omega)]
      have hj : (eG a).f ((i - a).toNat + 1) = j := by
        change a + (((i - a).toNat + 1 : ℕ) : ℤ) = j; push_cast; omega
      rw [sq K a (f_toNat h) hj]
      congr 1
      apply comp_indep
    · exact (zero_below K (by omega)).eq_of_src _ _

theorem ιT_f (K : CochainComplex C ℤ) (a : ℤ) {k : ℕ} {i : ℤ} (hk : (eG a).f k = i) :
    (ιT K a).f i = comp K a hk := by
  dsimp only [ιT]
  rw [dite_eq_left (le_of_f hk)]
  apply comp_indep

instance (K : CochainComplex C ℤ) (a : ℤ) {k : ℕ} {i : ℤ} (hk : (eG a).f k = i) : IsIso (comp K a hk) := by
  dsimp only [comp]; infer_instance

theorem isIso_ιT (K : CochainComplex C ℤ) {a i : ℤ} (h : a ≤ i) : IsIso ((ιT K a).f i) := by
  rw [ιT_f K a (f_toNat h)]; infer_instance

def sTMap {K L : CochainComplex C ℤ} (f : K ⟶ L) (a : ℤ) : sT K a ⟶ sT L a :=
  HomologicalComplex.extendMap (HomologicalComplex.restrictionMap f (eG a)) (eG a)

theorem ιT_nat {K L : CochainComplex C ℤ} (f : K ⟶ L) (a : ℤ) : sTMap f a ≫ ιT L a = ιT K a ≫ f := by
  ext i
  simp only [HomologicalComplex.comp_f]
  by_cases h : a ≤ i
  · have hk := f_toNat h
    rw [ιT_f K a hk, ιT_f L a hk]
    rw [sTMap, HomologicalComplex.extendMap_f _ _ hk, HomologicalComplex.restrictionMap_f' _ _ hk]
    simp only [comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  · exact (zero_below K (by omega)).eq_of_src _ _

end Gen

def TruncData' : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (n : ℤ),
  (∀ i : ℤ, 0 < i → IsZero (K.X i) ∧ IsZero (L.X i)) →
  ∃ (P : ℕ) (K' L' : Cx R) (f' : K' ⟶ L') (g : K' ⟶ K) (h : L' ⟶ L),
    (∀ i : ℤ, (0 < i ∨ i < -(P : ℤ)) → IsZero (K'.X i) ∧ IsZero (L'.X i)) ∧ f' ≫ h = g ≫ f ∧
    (∀ p : ℤ, -(n + 1) ≤ p → IsIso (g.f p) ∧ IsIso (h.f p)) ∧
    (∀ p : ℤ, p < -(n + 1) → IsZero (K'.X p) ∧ IsZero (L'.X p))

theorem truncData' : TruncData' := by
  intro R _ K L f n hz
  refine ⟨(n + 1).toNat, sT K (-(n + 1)), sT L (-(n + 1)), sTMap f _, ιT K _, ιT L _, fun i hi => ?_, ιT_nat f _,
    fun p hp => ⟨isIso_ιT K hp, isIso_ιT L hp⟩, fun p hp => ⟨zero_below K hp, zero_below L hp⟩⟩
  by_cases h : -(n + 1) ≤ i
  · have hi' : 0 < i := by omega
    have := isIso_ιT K h
    have := isIso_ιT L h
    exact ⟨(hz i hi').1.of_iso (asIso ((ιT K _).f i)), (hz i hi').2.of_iso (asIso ((ιT L _).f i))⟩
  · exact ⟨zero_below K (by omega), zero_below L (by omega)⟩

variable (R : Type) [CommRing R] (F : Shv R)

theorem relK_of_square' {K L K' L' : Cx R} (f : K ⟶ L) (f' : K' ⟶ L') (g : K' ⟶ K) (h : L' ⟶ L)
    (w : f' ≫ h = g ≫ f) (n : ℤ)
    (hg : ∀ m : ℤ, m ≤ n → Function.Bijective (HK.pull R g F m))
    (hh : ∀ m : ℤ, m ≤ n → Function.Bijective (HK.pull R h F m))
    (hf' : RelK R F n f') : RelK R F n f := by
  have key : ∀ (m : ℤ) (z : HK R L F m),
      HK.pull R f' F m (HK.pull R h F m z) = HK.pull R g F m (HK.pull R f F m z) := by
    intro m z
    rw [← LateralTheory.E.TruncPf.pull_comp, ← LateralTheory.E.TruncPf.pull_comp, w]
  refine ⟨fun m hm y => ?_, fun x1 x2 hx => ?_⟩
  · obtain ⟨z', hz'⟩ := hf'.1 m hm (HK.pull R g F m y)
    obtain ⟨z, rfl⟩ := (hh m (by omega)).2 z'
    exact ⟨z, (hg m (by omega)).1 ((key m z).symm.trans hz')⟩
  · apply (hh n le_rfl).1
    apply hf'.2
    rw [key, key, hx]

theorem Trunc_of (hB : TruncBij) : LateralTheory.E.FiltPf.Trunc := by
  intro R _ F K L f n hz
  obtain ⟨P, K', L', f', g, h, hb, w, hiso, hzero⟩ := truncData' R f n hz
  refine ⟨P, K', L', f', hb, fun hp p => ?_, relK_of_square' R F f f' g h w n
    (hB R F g n fun q hq => (hiso q hq).1) (hB R F h n fun q hq => (hiso q hq).2)⟩
  by_cases hq : -(n + 1) ≤ -(p : ℤ)
  · have := (hiso _ hq).1
    have := (hiso _ hq).2
    refine relK_of_square R F (pieceC R f' p) (pieceC R f p)
      ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (g.f _))
      ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (h.f _)) ?_ n
      (fun m _ => pull_bij_of_iso R F _ m) (fun m _ => pull_bij_of_iso R F _ m) (hp p)
    simp only [pieceC, ← Functor.map_comp]
    congr 1
    have := congrArg (fun φ => HomologicalComplex.Hom.f φ (-(p : ℤ))) w
    simp only [HomologicalComplex.comp_f] at this
    exact this.symm
  · exact relK_of_isZero R F _ n
      (Functor.map_isZero _ (hzero _ (by omega)).1) (Functor.map_isZero _ (hzero _ (by omega)).2)

end LateralTheory.E.TruncationInclusionIso
end
end

section

set_option linter.style.haveILetI false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace LateralTheory.E.BaseLocLocPf

theorem pb_cancel {C : Type*} [Category C] {P X Y Z T : C} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {i : Z ⟶ T} [Mono i] (h : IsPullback a b (f ≫ i) (g ≫ i)) : IsPullback a b f g := by
  refine ⟨⟨by simpa [← cancel_mono i] using h.w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => h.lift s.fst s.snd (by simp [s.condition_assoc])) (fun s => by simp) (fun s => by simp) ?_⟩⟩
  intro s m h1 h2
  apply h.hom_ext <;> simp [h1, h2]

theorem loc_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (M : Submonoid A)
    (hf : @IsLocalization _ _ M _ _ f.toAlgebra) [Algebra B C] (N : Submonoid B) [IsLocalization N C] :
    ∃ M' : Submonoid A, @IsLocalization _ _ M' _ _ ((algebraMap B C).comp f).toAlgebra := by
  letI := f.toAlgebra
  letI : Algebra A C := ((algebraMap B C).comp f).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact ⟨_, IsLocalization.localization_localization_isLocalization M N C⟩

theorem loc_equiv' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] (M : Submonoid A)
    [IsLocalization M B] (e : B ≃+* C) :
    @IsLocalization _ _ M _ _ ((e : B →+* C).comp (algebraMap A B)).toAlgebra := by
  letI : Algebra A C := ((e : B →+* C).comp (algebraMap A B)).toAlgebra
  exact IsLocalization.isLocalization_of_algEquiv M (AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl))

theorem chart {Z S : Scheme.{0}} (c : Z ⟶ S) (x : S) (W : (pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens)
    (y : (pullback c (S.fromSpecStalk x) : Scheme.{0})) (hy : y ∈ W) :
    ∃ U : (pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens, y ∈ U ∧ U ≤ W ∧
    ∃ V : Z.Opens, IsAffineOpen V ∧ (V : Set Z).Nonempty ∧
    ∃ f : Γ(Z, V) →+* Γ((pullback c (S.fromSpecStalk x) : Scheme.{0}), U), ∃ M : Submonoid Γ(Z, V),
      @IsLocalization _ _ M _ _ f.toAlgebra := by
  obtain ⟨U0, hU0a, hxU0, -⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : S.Opens) from trivial)
  have hg : S.fromSpecStalk x = Spec.map (S.presheaf.germ U0 x hxU0) ≫ hU0a.fromSpec :=
    (hU0a.fromSpecStalk_eq_fromSpecStalk hxU0).symm
  have hgU : ∀ z, S.fromSpecStalk x z ∈ U0 := by
    intro z; rw [hg, Scheme.Hom.comp_apply]; exact hU0a.range_fromSpec.le (Set.mem_range_self _)
  have hcy : c (pullback.fst c (S.fromSpecStalk x) y) ∈ U0 := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]; exact hgU _
  obtain ⟨V, hVa, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show pullback.fst c (S.fromSpecStalk x) y ∈ c ⁻¹ᵁ U0 from hcy)
  have hVU' : V ≤ c ⁻¹ᵁ U0 := hVU
  set p := pullback.fst c (S.fromSpecStalk x)
  set O := p ⁻¹ᵁ V with hOdef
  have H1 : IsPullback (p ∣_ V) O.ι V.ι p := isPullback_morphismRestrict p V
  have H2 : IsPullback (p ∣_ V) (O.ι ≫ pullback.snd c (S.fromSpecStalk x)) (V.ι ≫ c) (S.fromSpecStalk x) :=
    H1.paste_vert (IsPullback.of_hasPullback c (S.fromSpecStalk x))
  let ψ := c.appLE U0 V hVU'
  have e1 : V.ι ≫ c = hVa.isoSpec.hom ≫ Spec.map ψ ≫ hU0a.fromSpec := by
    rw [IsAffineOpen.SpecMap_appLE_fromSpec c hU0a hVa hVU', ← IsAffineOpen.isoSpec_inv_ι]; simp
  have H3 : IsPullback ((p ∣_ V) ≫ hVa.isoSpec.hom) (O.ι ≫ pullback.snd c (S.fromSpecStalk x)) (Spec.map ψ ≫ hU0a.fromSpec)
      (Spec.map (S.presheaf.germ U0 x hxU0) ≫ hU0a.fromSpec) := by
    rw [← hg]
    exact IsPullback.of_iso H2 (Iso.refl _) hVa.isoSpec (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp [e1]) (by simp)
  have H4 := pb_cancel H3
  letI : Algebra Γ(S, U0) Γ(Z, V) := ψ.hom.toAlgebra
  letI := S.presheaf.algebra_section_stalk ⟨x, hxU0⟩
  haveI hSt : IsLocalization.AtPrime (S.presheaf.stalk x) (hU0a.primeIdealOf ⟨x, hxU0⟩).asIdeal :=
    hU0a.isLocalization_stalk ⟨x, hxU0⟩
  have H5 := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(S, U0) Γ(Z, V) (S.presheaf.stalk x))
  let e := H4.isoIsPullback _ _ H5
  haveI : IsAffine O.toScheme := IsAffine.of_isIso e.hom
  have hOa : IsAffineOpen O := this
  let eR : CommRingCat.of (Γ(Z, V) ⊗[Γ(S, U0)] S.presheaf.stalk x) ≅ Γ(pullback c (S.fromSpecStalk x), O) :=
    (Scheme.ΓSpecIso _).symm ≪≫ Scheme.Γ.mapIso e.op ≪≫ O.topIso
  have hL := loc_equiv' (Algebra.algebraMapSubmonoid Γ(Z, V) (hU0a.primeIdealOf ⟨x, hxU0⟩).asIdeal.primeCompl)
    eR.commRingCatIsoToRingEquiv
  have hyO : y ∈ O := hyV
  obtain ⟨h, hhW, hyh⟩ := hOa.exists_basicOpen_le (V := W) ⟨y, hy⟩ hyO
  haveI := hOa.isLocalization_basicOpen h
  obtain ⟨M, hM⟩ := loc_comp (C := Γ(pullback c (S.fromSpecStalk x), (pullback c (S.fromSpecStalk x)).basicOpen h)) _ _ hL (Submonoid.powers h)
  exact ⟨_, hyh, hhW, V, hVa, ⟨_, hyV⟩, _, M, hM⟩

theorem BaseLocLoc_of : LateralTheory.E.BaseAICPf.BaseLocLoc := by
  intro Z S c _ _ _ _ _ x W y hy
  exact chart c x W y hy

end LateralTheory.E.BaseLocLocPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Topology

namespace LateralTheory.E.BaseIntPf

theorem bij_of_flat_surj {A B : CommRingCat.{0}} [IsLocalRing A] [IsLocalRing B] (φ : A ⟶ B)
    [IsLocalHom φ.hom] (hf : φ.hom.Flat) (hs : Function.Surjective φ.hom) : Function.Bijective φ.hom := by
  letI := φ.hom.toAlgebra
  have : Module.Flat A B := hf
  have : IsLocalHom (algebraMap A B) := ‹IsLocalHom φ.hom›
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := B)
  exact ⟨FaithfulSMul.algebraMap_injective A B, hs⟩

theorem reduced_of_flat_preimm {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] [IsPreimmersion f] [IsReduced Y] :
    IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    have hb := bij_of_flat_surj (f.stalkMap x) (Flat.stalkMap f x) (f.stalkMap_surjective x)
    exact isReduced_of_injective (RingEquiv.ofBijective _ hb).symm (RingEquiv.injective _)
  exact isReduced_of_isReduced_stalk X

theorem gen_spec {Z S : Scheme.{0}} [IrreducibleSpace Z] [IrreducibleSpace S] (c : Z ⟶ S) [IsDominant c] (x : S) :
    c.base (genericPoint Z) ⤳ x := by
  rw [specializes_iff_mem_closure]
  have h1 : Set.range c.base ⊆ closure {c.base (genericPoint Z)} := by
    rintro _ ⟨z, rfl⟩
    exact specializes_iff_mem_closure.mp (((genericPoint_spec Z).specializes (Set.mem_univ z)).map c.continuous)
  have h2 := closure_minimal h1 isClosed_closure
  rw [c.denseRange.closure_range] at h2
  exact h2 (Set.mem_univ x)

theorem BaseInt_of : LateralTheory.E.BaseAICPf.BaseInt := by
  intro Z S c _ _ _ hZ hS x
  have := hZ.1; have := hS.1
  have : Flat (S.fromSpecStalk x) := GlobalTheory.GenericExt.flat_fromSpecStalk S x
  have : IsReduced (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}) := reduced_of_flat_preimm (pullback.fst c (S.fromSpecStalk x))
  have hT : IsIrreducible (Set.range (pullback.fst c (S.fromSpecStalk x)).base) := by
    have hη : genericPoint Z ∈ Set.range (pullback.fst c (S.fromSpecStalk x)).base := by
      rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecStalk]
      exact gen_spec c x
    rw [← isIrreducible_iff_closure]
    have : closure (Set.range (pullback.fst c (S.fromSpecStalk x)).base) = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← (genericPoint_spec Z).def]
      exact closure_mono (Set.singleton_subset_iff.mpr hη)
    rw [this]; exact IrreducibleSpace.isIrreducible_univ Z
  have : IrreducibleSpace (Set.range (pullback.fst c (S.fromSpecStalk x)).base) := Subtype.irreducibleSpace hT
  have : IrreducibleSpace (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}) :=
    ((pullback.fst c (S.fromSpecStalk x)).isEmbedding.toHomeomorph).irreducibleSpace_iff.mpr inferInstance
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end LateralTheory.E.BaseIntPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.E.RootPowPf

theorem prim_eval {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : IsRoot (cyclotomic q A) ζ.1 := by
  have h := ζ.2.2
  rw [IsRoot.def, ← map_cyclotomic_int q A, Polynomial.eval_map]
  rw [aeval_def] at h
  exact h

theorem prim_pow {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  have h := (prim_eval ζ).dvd (cyclotomic.dvd_X_pow_sub_one q A)
  simpa [IsRoot.def, sub_eq_zero] using h

theorem field_case {q : ℕ} {K : Type} [Field K] (ζ ξ : Prim q K) :
    ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val := by
  have : NeZero (q : K) := ⟨ζ.2.1.ne_zero⟩
  have : NeZero q := NeZero.of_neZero_natCast K
  have hζ : IsPrimitiveRoot ζ.1 q := isRoot_cyclotomic_iff.1 (prim_eval ζ)
  have hξ : IsPrimitiveRoot ξ.1 q := isRoot_cyclotomic_iff.1 (prim_eval ξ)
  obtain ⟨i, hi, he⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  have hc : i.Coprime q := (hζ.pow_iff_coprime (NeZero.pos q) i).1 (he ▸ hξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, he]

theorem local_case {q : ℕ} {O : Type} [CommRing O] [IsLocalRing O] (ζ ξ : Prim q O) :
    ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val := by
  obtain ⟨a, ha⟩ := field_case (ζ.map (IsLocalRing.residue O)) (ξ.map (IsLocalRing.residue O))
  refine ⟨a, ?_⟩
  change IsLocalRing.residue O ξ.1 = (IsLocalRing.residue O ζ.1) ^ _ at ha
  rw [← map_pow] at ha
  set η := ζ.1 ^ (a : ZMod q).val with hη
  have hηq : η ^ q = 1 := by rw [hη, ← pow_mul, mul_comm, pow_mul, prim_pow, one_pow]
  have hq : q ≠ 0 := by
    rintro rfl
    have := ζ.2.1
    simp at this
  have hηu : IsUnit η := IsUnit.of_pow_eq_one hηq hq
  have hg := (Commute.all ξ.1 η).geom_sum₂_mul q
  rw [prim_pow, hηq, sub_self] at hg
  have hu : IsUnit (∑ i ∈ Finset.range q, ξ.1 ^ i * η ^ (q - 1 - i)) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]

    simp only [map_sum, map_mul, map_pow, ha]
    rw [geom_sum₂_self]
    have h1 : IsUnit ((q : O) * η ^ (q - 1)) := ζ.2.1.mul (hηu.pow _)
    have h2 := (h1.map (IsLocalRing.residue O)).ne_zero
    simpa using h2
  exact sub_eq_zero.1 (hu.mul_right_eq_zero.1 hg)

def sv {q : ℕ} {Y : Scheme.{0}} (ζ ξ : Prim q Γ(Y, ⊤)) : Sieve Y where
  arrows := fun Z g => ∃ a : (ZMod q)ˣ, (ξ.map g.appTop.hom).1 = (ζ.map g.appTop.hom).1 ^ (a : ZMod q).val
  downward_closed := by
    rintro Z W g ⟨a, ha⟩ h
    refine ⟨a, ?_⟩
    change g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ _ at ha
    change (h ≫ g).appTop.hom ξ.1 = (h ≫ g).appTop.hom ζ.1 ^ _
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, ha, map_pow]

theorem nhd {q : ℕ} {Y : Scheme.{0}} (ζ ξ : Prim q Γ(Y, ⊤)) (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ sv ζ ξ U.ι := by
  obtain ⟨a, ha⟩ := local_case (ζ.map (Y.presheaf.germ ⊤ y trivial).hom) (ξ.map (Y.presheaf.germ ⊤ y trivial).hom)
  change (Y.presheaf.germ ⊤ y trivial).hom ξ.1 = (Y.presheaf.germ ⊤ y trivial).hom ζ.1 ^ _ at ha
  rw [← map_pow] at ha
  obtain ⟨(U : Y.Opens), hU, i, i', he⟩ := TopCat.Presheaf.germ_eq Y.presheaf (U := ⊤) (V := ⊤) y trivial trivial _ _ ha
  refine ⟨U, hU, a, ?_⟩
  change U.ι.appTop.hom ξ.1 = U.ι.appTop.hom ζ.1 ^ _
  rw [← map_pow]
  have hf : U.ι.appTop = Y.presheaf.map i.op ≫ U.topIso.inv := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
    exact (Y.presheaf.map_comp _ _).symm ▸ rfl
  have hi : i' = i := Subsingleton.elim _ _
  subst hi
  rw [hf]
  exact congrArg U.topIso.inv.hom he

theorem sv_mem {q : ℕ} {Y : Scheme.{0}} (ζ ξ : Prim q Γ(Y, ⊤)) : sv ζ ξ ∈ Scheme.etaleTopology Y := by
  apply Scheme.zariskiTopology_le_etaleTopology
  choose U hU hS using nhd ζ ξ
  refine Scheme.mem_grothendieckTopology_iff.2 ⟨Scheme.Cover.mkOfCovers Y (fun y => (U y : Scheme)) (fun y => (U y).ι)
    (fun y => ⟨y, ⟨y, hU y⟩, rfl⟩) (fun y => inferInstance), ?_⟩
  rintro _ _ ⟨y⟩
  exact hS y

theorem RootPow_of : LateralTheory.E.MulPf.RootPow := by
  classical
  intro q Y ζ s
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ _ _ ξ h => absurd h (Finset.notMem_empty ξ)⟩
  | insert ξ s _ ih =>
    obtain ⟨S, hS, h⟩ := ih
    refine ⟨S ⊓ sv ζ ξ, GrothendieckTopology.intersection_covering _ hS (sv_mem ζ ξ), ?_⟩
    rintro Z g ⟨h1, h2⟩ η hη
    rcases Finset.mem_insert.1 hη with rfl | hη
    · exact h2
    · exact h g h1 η hη

end LateralTheory.E.RootPowPf
end
end
