module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle032
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle108
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle035
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

namespace GlobalTheory.HilbAff


set_option backward.isDefEq.respectTransparency.types false in
theorem of_isPullback_openImmersions (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    {X T : Scheme.{0}} (φ : X ⟶ T) {ι : Type u} {V : ι → Scheme.{0}} (f : ∀ i, V i ⟶ T)
    [∀ i, IsOpenImmersion (f i)] (hcov : ∀ x : T, ∃ i y, f i y = x)
    {Z : ι → Scheme.{0}} (k : ∀ i, Z i ⟶ X) (q : ∀ i, Z i ⟶ V i)
    (H : ∀ i, IsPullback (k i) (q i) φ (f i)) (hq : ∀ i, P (q i)) : P φ := by
  have hU : iSup (fun i => (f i).opensRange) = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, y, rfl⟩ := hcov x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, rfl⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top _ hU fun i => ?_
  refine (P.arrow_mk_iso_iff (morphismRestrictOpensRange φ (f i))).mpr ?_
  rw [← (H i).isoPullback_inv_snd]
  exact (P.cancel_left_of_respectsIso _ _).mpr (hq i)

set_option backward.isDefEq.respectTransparency.types false in
theorem good_of_cover : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    {T : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ T),
    (∀ i, IsOpenImmersion (f i)) → (∀ x : T, ∃ i y, f i y = x) →
    ∀ (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData),
    (∀ i, GlobalTheory.HilbAff.Good A B r (f i ≫ g) (I.comap (GlobalTheory.HilbAff.bc A B g (f i)))) →
    GlobalTheory.HilbAff.Good A B r g I := by
  intro A B _ _ _ r T ι V f hf hcov g I hG
  have H : ∀ i, IsPullback (pullback.snd (bc A B g (f i)) I.subschemeι)
      (pullback.fst (bc A B g (f i)) I.subschemeι ≫ pullback.snd _ (f i ≫ g))
      (I.subschemeι ≫ pullback.snd _ g) (f i) := fun i =>
    (IsPullback.of_hasPullback (bc A B g (f i)) I.subschemeι).flip.paste_vert
      (isPullback_bc A B g (f i))
  have e : ∀ i, (I.comap (bc A B g (f i))).subschemeι ≫ pullback.snd _ (f i ≫ g) =
      (I.comapIso (bc A B g (f i))).hom ≫ (pullback.fst (bc A B g (f i)) I.subschemeι ≫
        pullback.snd _ (f i ≫ g)) := fun i => by
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have hfin : ∀ i, IsFinite (pullback.fst (bc A B g (f i)) I.subschemeι ≫
      pullback.snd _ (f i ≫ g)) := fun i => by
    have h := (hG i).1
    rw [e i, MorphismProperty.cancel_left_of_respectsIso @IsFinite.{0}] at h
    exact h
  have hfl : ∀ i, Flat (pullback.fst (bc A B g (f i)) I.subschemeι ≫
      pullback.snd _ (f i ≫ g)) := fun i => by
    have h := (hG i).2.1
    rw [e i, MorphismProperty.cancel_left_of_respectsIso @Flat.{0}] at h
    exact h
  have : IsZariskiLocalAtTarget @Flat.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{0})
  have : IsZariskiLocalAtTarget @IsFinite.{0} := inferInstance
  have h1 : IsFinite (I.subschemeι ≫ pullback.snd _ g) :=
    of_isPullback_openImmersions @IsFinite.{0} _ f hcov _ _ H hfin
  have h2 : Flat (I.subschemeι ≫ pullback.snd _ g) :=
    of_isPullback_openImmersions @Flat.{0} _ f hcov _ _ H hfl
  refine ⟨h1, h2, fun y => ?_⟩
  obtain ⟨i, y', rfl⟩ := hcov y
  have h := (hG i).2.2 y'
  rw [e i, Scheme.Hom.finrank_comp_left_of_isIso,
    Scheme.Hom.finrank_of_isPullback _ _ _ _ (H i) y'] at h
  exact h

end GlobalTheory.HilbAff
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

namespace GlobalTheory.HilbGlue

theorem isProper_of_represents_of_local_proper : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (H : Scheme.{0}) (u : GlobalTheory.HilbGlue.HPt z r H), (∀ (T : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r T), ∃! c : T ⟶ H, GlobalTheory.HilbGlue.HPt.map c u = x) → (∀ s : S, ∃ W : S.Opens, s ∈ W ∧ ∃ (T : Scheme.{0}) (y : GlobalTheory.HilbGlue.HPt z r T) (π : T ⟶ W.toScheme), IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r Y) (b : Y ⟶ W.toScheme), x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, GlobalTheory.HilbGlue.HPt.map c y = x) → IsProper u.1 := by
  intro S Z z r H u hu hloc
  choose W hsW T y π hπ hy hT using hloc
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) W ?_ ?_
  · rw [eq_top_iff]
    intro s _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨s, hsW s⟩
  intro s
  set V : H.Opens := u.1 ⁻¹ᵁ W s
  have hx1 : (HPt.map V.ι u).1 = (u.1 ∣_ W s) ≫ (W s).ι := by
    change V.ι ≫ u.1 = _
    rw [morphismRestrict_ι]
  obtain ⟨φ, hφ, -⟩ := hT s V (HPt.map V.ι u) (u.1 ∣_ W s) hx1
  obtain ⟨ψ, hψ, -⟩ := hu (T s) (y s)
  have hψ1 : ψ ≫ u.1 = π s ≫ (W s).ι := by
    rw [← hy s, ← hψ]; rfl
  have hrange : Set.range ψ ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    change u.1 (ψ t) ∈ W s
    have : u.1 (ψ t) = (W s).ι (π s t) := by
      rw [← Scheme.Hom.comp_apply, hψ1, Scheme.Hom.comp_apply]
    rw [this]
    exact ((π s) t).2
  let ψ' : T s ⟶ V := IsOpenImmersion.lift V.ι ψ hrange
  have hψ' : ψ' ≫ V.ι = ψ := IsOpenImmersion.lift_fac _ _ _
  have h1 : ψ' ≫ φ = 𝟙 _ := by
    obtain ⟨c, -, hc⟩ := hT s (T s) (y s) (π s) (hy s)
    have e1 : HPt.map (ψ' ≫ φ) (y s) = y s := by
      rw [HPt.map_comp, hφ, ← HPt.map_comp, hψ', hψ]
    have e2 : HPt.map (𝟙 (T s)) (y s) = y s := HPt.map_id _
    exact (hc _ e1).trans (hc _ e2).symm
  have h2 : φ ≫ ψ' = 𝟙 _ := by
    obtain ⟨c, -, hc⟩ := hu V (HPt.map V.ι u)
    have e1 : HPt.map ((φ ≫ ψ') ≫ V.ι) u = HPt.map V.ι u := by
      rw [Category.assoc, hψ', HPt.map_comp, hψ, hφ]
    have e2 := (hc _ e1).trans (hc _ rfl).symm
    rw [← cancel_mono V.ι, e2, Category.id_comp]
  have hiso : IsIso φ := ⟨⟨ψ', h2, h1⟩⟩
  have hcomp : φ ≫ π s = u.1 ∣_ W s := by
    rw [← cancel_mono (W s).ι, Category.assoc, ← hy s, ← hx1, ← hφ]
    rfl
  rw [← hcomp]
  haveI := hπ s
  infer_instance

end GlobalTheory.HilbGlue
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem pushout_inl_injective {R S R' P : CommRingCat.{0}} {f : R ⟶ S} {g : R ⟶ R'}
    {inl : S ⟶ P} {inr : R' ⟶ P} (h : IsPushout f g inl inr) (hf : f.hom.Flat)
    (hg : Function.Injective g.hom) : Function.Injective inl.hom := by
  letI := f.hom.toAlgebra
  letI := g.hom.toAlgebra
  haveI : Module.Flat R S := hf
  have ht := CommRingCat.isPushout_tensorProduct R R' S
  let e := IsPushout.isoIsPushout _ _ h.flip ht
  have he : inl ≫ e.hom = CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom :=
    IsPushout.inr_isoIsPushout_hom _ _ h.flip ht
  intro x y hxy
  have hi : Function.Injective (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := S)) :=
    Algebra.TensorProduct.includeRight_injective hg
  apply hi
  have h1 := congrArg (fun φ => φ.hom x) he
  have h2 := congrArg (fun φ => φ.hom y) he
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h1 h2
  change _ = Algebra.TensorProduct.includeRight.toRingHom x at h1
  change _ = Algebra.TensorProduct.includeRight.toRingHom y at h2
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1 h2
  rw [← h1, ← h2, hxy]

theorem ker_eq_bot_of_isPullback {Z ZK Y Y' : Scheme.{0}} [IsAffine Z] [IsAffine Y] [IsAffine Y']
    {p : ZK ⟶ Z} {q : ZK ⟶ Y'} {π : Z ⟶ Y} {j : Y' ⟶ Y} (H : IsPullback p q π j) [Flat π]
    (hj : Function.Injective j.appTop.hom) : p.ker = ⊥ := by
  haveI : IsAffine ZK := .of_isPullback H
  have hP := isPushout_appTop_of_isPullback H
  have hf : π.appTop.hom.Flat := (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mp inferInstance
  have hinj := pushout_inl_injective hP hf hj
  rw [Scheme.ker_of_isAffine, (RingHom.injective_iff_ker_eq_bot _).mp hinj]
  first | exact map_bot (Scheme.IdealSheafData.equivOfIsAffine (X := Z)).symm | simp

theorem appTop_spec_injective {R S : CommRingCat.{0}} (f : R ⟶ S) (hf : Function.Injective f.hom) :
    Function.Injective (Spec.map f).appTop.hom := by
  intro x y hxy
  have e := Scheme.ΓSpecIso_naturality f
  have h1 := congrArg (fun φ => φ.hom x) e
  have h2 := congrArg (fun φ => φ.hom y) e
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h1 h2
  rw [hxy] at h1
  have := hf (h1.symm.trans h2)
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1 this

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

theorem map_comap_bc_eq (r : ℕ) {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K]
    [IsFractionRing V K] (g : Spec (CommRingCat.of V) ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (hI : Good A B r g I) :
    (I.comap (bc A B g (Spec.map (CommRingCat.ofHom (algebraMap V K))))).map
      (bc A B g (Spec.map (CommRingCat.ofHom (algebraMap V K)))) = I := by
  set a := Spec.map (CommRingCat.ofHom (algebraMap V K))
  obtain ⟨-, h2, -⟩ := hI
  haveI : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  have H : IsPullback (pullback.snd (bc A B g a) I.subschemeι)
      (pullback.fst (bc A B g a) I.subschemeι ≫ pullback.snd _ (a ≫ g))
      (I.subschemeι ≫ pullback.snd _ g) a :=
    (IsPullback.of_hasPullback (bc A B g a) I.subschemeι).flip.paste_vert (isPullback_bc A B g a)
  have hk : (pullback.snd (bc A B g a) I.subschemeι).ker = ⊥ :=
    ker_eq_bot_of_isPullback H (appTop_spec_injective _ (IsFractionRing.injective V K))
  rw [Scheme.IdealSheafData.comap, Scheme.IdealSheafData.map_ker, pullback.condition,
    Scheme.Hom.ker_comp, hk, Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]

theorem eq_of_comap_bc_eq (r : ℕ) {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K]
    [IsFractionRing V K] (g : Spec (CommRingCat.of V) ⟶ Spec (CommRingCat.of A))
    (I I' : (pullback (str A B) g).IdealSheafData) (hI : Good A B r g I) (hI' : Good A B r g I')
    (h : I.comap (bc A B g (Spec.map (CommRingCat.ofHom (algebraMap V K)))) =
      I'.comap (bc A B g (Spec.map (CommRingCat.ofHom (algebraMap V K))))) : I = I' := by
  rw [← map_comap_bc_eq A B r (K := K) g I hI, ← map_comap_bc_eq A B r (K := K) g I' hI', h]

end GlobalTheory.HilbAff

namespace GlobalTheory.HilbAff

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

theorem eq_of_map_eq (r : ℕ) {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K]
    [IsFractionRing V K] (x x' : (functor A B r).obj (op (Spec (CommRingCat.of V))))
    (h1 : x.1 = x'.1)
    (h2 : (functor A B r).map (Spec.map (CommRingCat.ofHom (algebraMap V K))).op x =
      (functor A B r).map (Spec.map (CommRingCat.ofHom (algebraMap V K))).op x') : x = x' := by
  rw [functor_map, functor_map] at h2
  have h3 := (Sigma.ext_iff.mp h2).2
  obtain ⟨g, I, hI⟩ := x
  obtain ⟨g', I', hI'⟩ := x'
  dsimp only at h1 h3
  subst h1
  have h4 := congrArg Subtype.val (eq_of_heq h3)
  have := eq_of_comap_bc_eq A B r (K := K) g I I' hI hI' h4
  subst this
  rfl

theorem valuativeCriterion_uniqueness : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (r : ℕ) (H : Scheme.{0})
    (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H),
    ValuativeCriterion.Uniqueness (R.homEquiv (𝟙 H)).1 := by
  intro A B _ _ _ _ _ r H Rep S
  refine ⟨fun l₁ l₂ => CommSq.LiftStruct.ext ?_⟩
  apply Rep.homEquiv.injective
  have e : ∀ l : Spec (CommRingCat.of S.R) ⟶ H,
      Rep.homEquiv l = (functor A B r).map l.op (Rep.homEquiv (𝟙 H)) := fun l => by
    rw [← Rep.homEquiv_comp, Category.comp_id]
  apply eq_of_map_eq A B r (K := S.K)
  · rw [e l₁.l, e l₂.l, functor_map, functor_map]
    dsimp only
    rw [l₁.fac_right, l₂.fac_right]
  · rw [← Rep.homEquiv_comp, ← Rep.homEquiv_comp, l₁.fac_left, l₂.fac_left]

end GlobalTheory.HilbAff
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.FerrandPush

theorem isLocalization_away_eqLocus {A B C A' B' C' : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing A'] [CommRing B'] [CommRing C'] (f : B →+* A) (g : C →+* A)
    (f' : B' →+* A') (g' : C' →+* A') (ρA : A →+* A') (ρB : B →+* B') (ρC : C →+* C')
    (hB : f'.comp ρB = ρA.comp f) (hC : g'.comp ρC = ρA.comp g)
    (x : RingHom.eqLocus (f.comp (RingHom.fst B C)) (g.comp (RingHom.snd B C)))
    (φ : RingHom.eqLocus (f.comp (RingHom.fst B C)) (g.comp (RingHom.snd B C)) →+*
      RingHom.eqLocus (f'.comp (RingHom.fst B' C')) (g'.comp (RingHom.snd B' C')))
    (hφ : ∀ y, (φ y : B' × C') = (ρB (y : B × C).1, ρC (y : B × C).2))
    (hlB : letI := ρB.toAlgebra; IsLocalization.Away (x : B × C).1 B')
    (hlC : letI := ρC.toAlgebra; IsLocalization.Away (x : B × C).2 C')
    (hlA : letI := ρA.toAlgebra; IsLocalization.Away (f (x : B × C).1) A') :
    letI := φ.toAlgebra
    IsLocalization.Away x
      (RingHom.eqLocus (f'.comp (RingHom.fst B' C')) (g'.comp (RingHom.snd B' C'))) := by
  letI := ρB.toAlgebra
  letI := ρC.toAlgebra
  letI := ρA.toAlgebra
  letI := φ.toAlgebra
  obtain ⟨⟨b, c⟩, hx⟩ := x
  have hx' : f b = g c := hx
  have eB : ∀ y, f' (ρB y) = ρA (f y) := fun y ↦ RingHom.congr_fun hB y
  have eC : ∀ y, g' (ρC y) = ρA (g y) := fun y ↦ RingHom.congr_fun hC y
  have hfst : ∀ y, ((φ y : B' × C')).1 = ρB (y : B × C).1 := fun y ↦ by rw [hφ]
  have hsnd : ∀ y, ((φ y : B' × C')).2 = ρC (y : B × C).2 := fun y ↦ by rw [hφ]
  have hpow : ∀ (y : RingHom.eqLocus (f.comp (RingHom.fst B C)) (g.comp (RingHom.snd B C)))
      (k : ℕ), ((y ^ k : RingHom.eqLocus (f.comp (RingHom.fst B C))
        (g.comp (RingHom.snd B C))) : B × C) = ((y : B × C).1 ^ k, (y : B × C).2 ^ k) :=
    fun y k ↦ by rw [SubmonoidClass.coe_pow, Prod.pow_def]
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  ·
    have hu : IsUnit (φ ⟨(b, c), hx⟩) := by
      obtain ⟨u₁, hu₁⟩ := IsLocalization.Away.algebraMap_isUnit (S := B') b
      obtain ⟨u₂, hu₂⟩ := IsLocalization.Away.algebraMap_isUnit (S := C') c
      have hu₁' : (u₁ : B') = ρB b := hu₁
      have hu₂' : (u₂ : C') = ρC c := hu₂
      have e0 : f' u₁ = g' u₂ := by rw [hu₁', hu₂', eB, eC, hx']
      have e1 : f' ↑u₁⁻¹ = g' ↑u₂⁻¹ := by
        calc f' ↑u₁⁻¹ = f' ↑u₁⁻¹ * (g' u₂ * g' ↑u₂⁻¹) := by
                rw [← map_mul, Units.mul_inv, map_one, mul_one]
          _ = f' ↑u₁⁻¹ * f' u₁ * g' ↑u₂⁻¹ := by rw [e0, mul_assoc]
          _ = g' ↑u₂⁻¹ := by rw [← map_mul, Units.inv_mul, map_one, one_mul]
      refine isUnit_iff_exists_inv.mpr ⟨⟨(↑u₁⁻¹, ↑u₂⁻¹), e1⟩, ?_⟩
      apply Subtype.ext
      change (φ ⟨(b, c), hx⟩ : B' × C') * ((↑u₁⁻¹ : B'), (↑u₂⁻¹ : C')) = (1 : B' × C')
      rw [hφ]
      ext
      · change ρB b * ↑u₁⁻¹ = 1
        rw [← hu₁', Units.mul_inv]
      · change ρC c * ↑u₂⁻¹ = 1
        rw [← hu₂', Units.mul_inv]
    rintro ⟨_, n, rfl⟩
    change IsUnit (φ (⟨(b, c), hx⟩ ^ n))
    rw [map_pow]
    exact hu.pow n
  ·
    rintro ⟨⟨z₁, z₂⟩, hz⟩
    have hz' : f' z₁ = g' z₂ := hz
    obtain ⟨n₁, y₁, h₁⟩ := IsLocalization.Away.surj b z₁
    obtain ⟨n₂, y₂, h₂⟩ := IsLocalization.Away.surj c z₂
    have h₁' : z₁ * ρB b ^ (n₁ + n₂) = ρB (y₁ * b ^ n₂) := by
      change z₁ * ρB b ^ n₁ = ρB y₁ at h₁
      rw [pow_add, ← mul_assoc, h₁, map_mul, map_pow]
    have h₂' : z₂ * ρC c ^ (n₁ + n₂) = ρC (y₂ * c ^ n₁) := by
      change z₂ * ρC c ^ n₂ = ρC y₂ at h₂
      rw [add_comm, pow_add, ← mul_assoc, h₂, map_mul, map_pow]
    have hA : algebraMap A A' (f (y₁ * b ^ n₂)) = algebraMap A A' (g (y₂ * c ^ n₁)) := by
      change ρA _ = ρA _
      have k₁ := congrArg f' h₁'
      have k₂ := congrArg g' h₂'
      rw [map_mul, map_pow, eB, eB] at k₁
      rw [map_mul, map_pow, eC, eC] at k₂
      rw [← k₁, ← k₂, hz', hx']
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (f b)) hA
    change f b ^ m * f (y₁ * b ^ n₂) = f b ^ m * g (y₂ * c ^ n₁) at hm
    have hmem : f (b ^ m * (y₁ * b ^ n₂)) = g (c ^ m * (y₂ * c ^ n₁)) := by
      rw [map_mul f (b ^ m), map_pow f, hm, map_mul g (c ^ m), map_pow g, hx']
    refine ⟨(⟨(b ^ m * (y₁ * b ^ n₂), c ^ m * (y₂ * c ^ n₁)), hmem⟩,
      ⟨⟨(b, c), hx⟩ ^ (m + (n₁ + n₂)), m + (n₁ + n₂), rfl⟩), ?_⟩
    apply Subtype.ext
    change ((⟨(z₁, z₂), hz⟩ : RingHom.eqLocus _ _) : B' × C') * (φ (⟨(b, c), hx⟩ ^ (m + (n₁ + n₂))) : B' × C') = (φ _ : B' × C')
    rw [hφ, hφ, hpow]
    ext
    · change z₁ * ρB (b ^ (m + (n₁ + n₂))) = ρB (b ^ m * (y₁ * b ^ n₂))
      rw [map_mul, ← h₁']
      simp only [map_pow]
      ring
    · change z₂ * ρC (c ^ (m + (n₁ + n₂))) = ρC (c ^ m * (y₂ * c ^ n₁))
      rw [map_mul, ← h₂']
      simp only [map_pow]
      ring
  ·
    intro y y' e
    have e' : φ y = φ y' := e
    have e₁ : algebraMap B B' (y : B × C).1 = algebraMap B B' (y' : B × C).1 := by
      change ρB _ = ρB _
      rw [← hfst, ← hfst]; exact congrArg (fun t : RingHom.eqLocus (f'.comp (RingHom.fst B' C')) (g'.comp (RingHom.snd B' C')) ↦ (t : B' × C').1) e'
    have e₂ : algebraMap C C' (y : B × C).2 = algebraMap C C' (y' : B × C).2 := by
      change ρC _ = ρC _
      rw [← hsnd, ← hsnd]; exact congrArg (fun t : RingHom.eqLocus (f'.comp (RingHom.fst B' C')) (g'.comp (RingHom.snd B' C')) ↦ (t : B' × C').2) e'
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers b) e₁
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers c) e₂
    change b ^ n * _ = b ^ n * _ at hn
    change c ^ k * _ = c ^ k * _ at hk
    refine ⟨⟨⟨(b, c), hx⟩ ^ (n + k), n + k, rfl⟩, ?_⟩
    apply Subtype.ext
    change ((⟨(b, c), hx⟩ ^ (n + k) : RingHom.eqLocus _ _) : B × C) * (y : B × C) =
      ((⟨(b, c), hx⟩ ^ (n + k) : RingHom.eqLocus _ _) : B × C) * (y' : B × C)
    rw [hpow]
    ext
    · change b ^ (n + k) * _ = b ^ (n + k) * _
      calc b ^ (n + k) * (y : B × C).1 = b ^ k * (b ^ n * (y : B × C).1) := by ring
        _ = b ^ k * (b ^ n * (y' : B × C).1) := by rw [hn]
        _ = _ := by ring
    · change c ^ (n + k) * _ = c ^ (n + k) * _
      calc c ^ (n + k) * (y : B × C).2 = c ^ n * (c ^ k * (y : B × C).2) := by ring
        _ = c ^ n * (c ^ k * (y' : B × C).2) := by rw [hk]
        _ = _ := by ring

end GlobalTheory.FerrandPush

namespace GlobalTheory.FerrandPush

section Geo
variable {Y₀ Y₁ Y₂ : Scheme.{0}}

theorem upOpen_basicOpen (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i] (U : Y₀.Opens)
    (s : Γ(Y₁, upOpen i U)) : upOpen i (Y₀.basicOpen ((res i U).hom s)) = Y₁.basicOpen s := by
  have h1 : Y₀.basicOpen ((res i U).hom s) = U ⊓ i ⁻¹ᵁ Y₁.basicOpen s :=
    Scheme.basicOpen_appLE i U (upOpen i U) (preimage_upOpen i U).ge s
  have h2 : i ⁻¹ᵁ Y₁.basicOpen s ≤ U :=
    le_trans ((Scheme.Hom.preimage_mono i) (Y₁.basicOpen_le s)) (preimage_upOpen i U).le
  rw [h1, inf_eq_right.mpr h2, upOpen_preimage]

variable (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) [IsClosedImmersion i₁] [Surjective i₁]
  [IsClosedImmersion i₂] [Surjective i₂]

end Geo
end GlobalTheory.FerrandPush

namespace GlobalTheory.FerrandPush

theorem isLocalization_away_fib : ∀ {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂)
    [IsClosedImmersion i₁] [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂],
    ∀ U ∈ GlobalTheory.FerrandPush.good i₁ i₂, ∀ a : (GlobalTheory.FerrandPush.fib i₁ i₂).obj (op U),
    letI := ((GlobalTheory.FerrandPush.fib i₁ i₂).map (homOfLE (Y₀.basicOpen_le
      (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a))).op).hom.toAlgebra;
    IsLocalization.Away a ((GlobalTheory.FerrandPush.fib i₁ i₂).obj
      (op (Y₀.basicOpen (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a)))) := by
  intro Y₀ Y₁ Y₂ i₁ i₂ _ _ _ _ U hU a
  obtain ⟨hU0, hU1, hU2⟩ := hU
  have hD : Y₀.basicOpen (((fibπ i₁ i₂).app (op U)).hom a) ≤ U := Y₀.basicOpen_le _
  have hs2 : ((fibπ i₁ i₂).app (op U)).hom a = (res i₂ U).hom ((cone i₁ i₂ U).snd.hom a) := a.2
  have e1 : upOpen i₁ (Y₀.basicOpen (((fibπ i₁ i₂).app (op U)).hom a)) =
      Y₁.basicOpen ((cone i₁ i₂ U).fst.hom a) := upOpen_basicOpen i₁ U _
  have e2 : upOpen i₂ (Y₀.basicOpen (((fibπ i₁ i₂).app (op U)).hom a)) =
      Y₂.basicOpen ((cone i₁ i₂ U).snd.hom a) := by
    rw [hs2]; exact upOpen_basicOpen i₂ U _
  exact isLocalization_away_eqLocus (res i₁ U).hom (res i₂ U).hom (res i₁ _).hom (res i₂ _).hom
    (Y₀.presheaf.map (homOfLE hD).op).hom (Y₁.presheaf.map (homOfLE (upOpen_mono i₁ hD)).op).hom
    (Y₂.presheaf.map (homOfLE (upOpen_mono i₂ hD)).op).hom
    (congrArg CommRingCat.Hom.hom (res_naturality i₁ hD))
    (congrArg CommRingCat.Hom.hom (res_naturality i₂ hD)) a
    ((fib i₁ i₂).map (homOfLE hD).op).hom (fun _ ↦ rfl)
    (hU1.isLocalization_of_eq_basicOpen _ (homOfLE (upOpen_mono i₁ hD)) e1)
    (hU2.isLocalization_of_eq_basicOpen _ (homOfLE (upOpen_mono i₂ hD)) e2)
    (hU0.isLocalization_of_eq_basicOpen _ (homOfLE hD) rfl)

end GlobalTheory.FerrandPush
end

section

open scoped TensorProduct

namespace GlobalTheory.CentralizerMapTensor

theorem cenMap_tmul_eq (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (F B : Type) [Field F] [NumberField F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] (x : ℚ_[ℓ]) (f : F) :
    GlobalTheory.LKInvGood.cenMap ℓ F B (x ⊗ₜ[ℚ] f) = x ⊗ₜ[ℚ] algebraMap F B f := rfl

theorem commute_cenMap (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (F B : Type) [Field F] [NumberField F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] (a : ℚ_[ℓ] ⊗[ℚ] F) (y : ℚ_[ℓ] ⊗[ℚ] B) :
    Commute (GlobalTheory.LKInvGood.cenMap ℓ F B a) y := by
  induction a using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Commute.zero_left _
  | add a₁ a₂ h₁ h₂ => rw [map_add (f := _)]; exact h₁.add_left h₂
  | tmul x f =>
    rw [cenMap_tmul_eq]
    induction y using TensorProduct.induction_on with
    | zero => exact Commute.zero_right _
    | add y₁ y₂ h₁ h₂ => exact h₁.add_right h₂
    | tmul z b =>
      unfold Commute SemiconjBy
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_comm x z, Algebra.commutes f b]

end GlobalTheory.CentralizerMapTensor
end
