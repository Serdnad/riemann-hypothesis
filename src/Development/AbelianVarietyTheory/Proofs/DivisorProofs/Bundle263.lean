module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
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
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

open Polynomial

theorem mem_range_of_AIC_of_eval₂_eq_zero {T L : Type} [CommRing T] [CommRing L] [IsDomain L]
    (hA : AIC T) (f : T →+* L) (x : L) :
    ∀ (n : ℕ) (p : T[X]), p.natDegree = n → p.Monic → p.eval₂ f x = 0 → x ∈ Set.range f := by
  intro n
  haveI : Nontrivial T := f.domain_nontrivial
  induction n with
  | zero =>
    intro p hd hm hx
    have hp : p = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm hd
    subst hp
    simp at hx
  | succ n ih =>
    intro p hd hm hx
    obtain ⟨a, ha⟩ := hA p hm (by omega)
    have hroot : IsRoot p a := ha
    have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hroot
    set q := p /ₘ (X - C a) with hq
    have hXm : (X - C a : T[X]).Monic := Polynomial.monic_X_sub_C a
    have hqm : q.Monic := by
      exact Polynomial.Monic.of_mul_monic_left hXm (by rw [hfac]; exact hm)
    have hqd : q.natDegree = n := by
      have h1 : ((X - C a) * q).natDegree = (X - C a).natDegree + q.natDegree :=
        hXm.natDegree_mul hqm
      rw [hfac, hd, Polynomial.natDegree_X_sub_C] at h1
      omega
    rw [← hfac, Polynomial.eval₂_mul] at hx
    rcases mul_eq_zero.mp hx with h | h
    · refine ⟨a, ?_⟩
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at h
      exact (sub_eq_zero.mp h).symm
    · exact ih q hqd hqm h

theorem exists_retraction_of_AIC : ∀ (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T]
    [Algebra D T] [Algebra.IsIntegral D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E],
    AIC T → ∀ (ι : T →ₐ[D] E) (Q : Ideal E), Q.IsPrime → Q.comap (algebraMap D E) = ⊥ →
    ∃ χ : E →ₐ[D] T, χ.comp ι = AlgHom.id D T ∧ RingHom.ker χ = Q := by
  intro D T E _ _ _ _ _ _ _ _ _ hA ι Q hQ hQD
  let π : E →ₐ[D] E ⧸ Q := Ideal.Quotient.mkₐ D Q
  let f : T →ₐ[D] E ⧸ Q := π.comp ι

  have hker : RingHom.ker (f : T →+* E ⧸ Q) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := D)
    rw [← hQD]
    ext d
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    change f (algebraMap D T d) = 0 ↔ _
    rw [f.commutes]
    change algebraMap D (E ⧸ Q) d = 0 ↔ _
    rw [IsScalarTower.algebraMap_apply D E (E ⧸ Q), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  have hinj : Function.Injective f := by
    have := (RingHom.injective_iff_ker_eq_bot (f : T →+* E ⧸ Q)).mpr hker
    exact this

  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨p, hpm, hpe⟩ := (Algebra.IsIntegral.isIntegral (R := D) e)
    have hmem := mem_range_of_AIC_of_eval₂_eq_zero hA (f : T →+* E ⧸ Q) (Ideal.Quotient.mk Q e)
      _ (p.map (algebraMap D T)) rfl (hpm.map _) (by
        rw [Polynomial.eval₂_map]
        have hc : (f : T →+* E ⧸ Q).comp (algebraMap D T) = (Ideal.Quotient.mk Q).comp (algebraMap D E) := by
          ext d
          simp only [RingHom.comp_apply, RingHom.coe_coe]
          rw [f.commutes]
          rfl
        rw [hc, ← Polynomial.hom_eval₂, hpe, map_zero])
    obtain ⟨t, ht⟩ := hmem
    exact ⟨t, ht⟩
  let eqv : T ≃ₐ[D] E ⧸ Q := AlgEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨(eqv.symm : E ⧸ Q →ₐ[D] T).comp π, ?_, ?_⟩
  · ext t
    simp only [AlgHom.comp_apply, AlgHom.id_apply, AlgHom.coe_coe]
    apply eqv.injective
    change eqv (eqv.symm (π (ι t))) = eqv t
    rw [AlgEquiv.apply_symm_apply]
    rfl
  · ext e
    rw [RingHom.mem_ker]
    change eqv.symm (π e) = 0 ↔ e ∈ Q
    rw [AlgEquiv.symm_apply_eq, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EtC.MVLeft

theorem mono_freePresheaf_map (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) [Mono f] : Mono ((freeP R).map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [ModuleCat.mono_iff_injective]
  have hf : Function.Injective (f.app U) := (mono_iff_injective (f.app U)).1 inferInstance
  have hu : Function.Injective (uliftFunctor.{1}.map (f.app U)) := by
    intro a b h; cases a; cases b; exact congrArg ULift.up (hf (congrArg ULift.down h))
  exact Finsupp.mapDomain_injective hu

theorem free_mono (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) [Mono f] : Mono ((free R).map f) := by
  haveI := mono_freePresheaf_map R f
  exact (presheafToSheaf _ _).map_mono ((freeP R).map f)

theorem left_mono : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), Mono (biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f))))) (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))))))) := by
  intro R _ A A' _ _ _ f
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f))))) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f))))))
  haveI : Mono (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))))) :=
    yoneda.map_mono _
  haveI := free_mono R (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f))))))
  exact mono_of_mono_fac (biprod.lift_snd _ _)

end GlobalTheory.EtC.MVLeft
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

theorem chains_spMap_comp (R : Type) [CommRing R] {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B)
    (h : B →+* C) : (chains R).map (spMap h) ≫ (chains R).map (spMap g) = (chains R).map (spMap (h.comp g)) := by
  rw [← Functor.map_comp]
  congr 1
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
  rfl

theorem awayMap_comp_algebraMap {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (f : A) :
    (Localization.awayMap g f).comp (algebraMap A (Localization.Away f)) = (algebraMap B (Localization.Away (g f))).comp g :=
  IsLocalization.map_comp _

theorem excision_square_comm (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) :
    (chains R).map (spMap (algebraMap A' (Localization.Away (algebraMap A A' f)))) ≫ (chains R).map (spMap (algebraMap A A')) =
      (chains R).map (spMap (Localization.awayMap (algebraMap A A') f)) ≫
        (chains R).map (spMap (algebraMap A (Localization.Away f))) := by
  rw [chains_spMap_comp, chains_spMap_comp, awayMap_comp_algebraMap]

def excisionConeMap (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) :
    mappingCone ((chains R).map (spMap (algebraMap A' (Localization.Away (algebraMap A A' f))))) ⟶
      mappingCone ((chains R).map (spMap (algebraMap A (Localization.Away f)))) :=
  mappingCone.map _ _ _ _ (excision_square_comm R A A' f)

end GlobalTheory.EtC
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.CechRep

variable {V W : Scheme.{0}} (f : V ⟶ W)

def IsPow (n : ℕ) (Z : Scheme.{0}) (p : Fin (n + 1) → (Z ⟶ V)) : Prop :=
  (∀ i, p i ≫ f = p 0 ≫ f) ∧ ∀ (U : Scheme.{0}) (y : Fin (n + 1) → (U ⟶ V)), (∀ i, y i ≫ f = y 0 ≫ f) →
    ∃! g : U ⟶ Z, ∀ i, g ≫ p i = y i

theorem exists_pow (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [P.IsMultiplicative]
    (hf : P f) (n : ℕ) : ∃ (Z : Scheme.{0}) (p : Fin (n + 1) → (Z ⟶ V)), IsPow f n Z p ∧ P (p 0) := by
  induction n with
  | zero =>
    refine ⟨V, fun _ => 𝟙 V, ⟨fun _ => rfl, fun U y _ => ⟨y 0, fun i => ?_, fun g hg => ?_⟩⟩, P.id_mem V⟩
    · rw [Fin.fin_one_eq_zero i]; simp
    · simpa using hg 0
  | succ n ih =>
    obtain ⟨Z, p, ⟨hc, hu⟩, hP⟩ := ih
    let q : Fin (n + 2) → (pullback (p 0 ≫ f) f ⟶ V) :=
      Fin.snoc (α := fun _ => pullback (p 0 ≫ f) f ⟶ V) (fun j => pullback.fst _ _ ≫ p j) (pullback.snd _ _)
    have qc : ∀ j : Fin (n + 1), q j.castSucc = pullback.fst _ _ ≫ p j := fun j => by simp [q]
    have ql : q (Fin.last _) = pullback.snd _ _ := by simp [q]
    have hz : (Fin.castSucc (0 : Fin (n + 1)) : Fin (n + 2)) = 0 := rfl
    have q0 : q 0 = pullback.fst _ _ ≫ p 0 := qc 0
    refine ⟨pullback (p 0 ≫ f) f, q, ⟨fun i => ?_, fun U y hy => ?_⟩, ?_⟩
    · rw [q0]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [ql, ← pullback.condition, Category.assoc]
      · rw [qc, Category.assoc, Category.assoc, hc j]
    · have h' : ∀ j : Fin (n + 1), y j.castSucc ≫ f = y (Fin.castSucc 0) ≫ f := fun j => by
        rw [hy, hz, hy]
      obtain ⟨g0, hg0, hg0u⟩ := hu U (fun j => y j.castSucc) h'
      have hw : g0 ≫ p 0 ≫ f = y (Fin.last _) ≫ f := by
        rw [← Category.assoc, hg0 0, hy (Fin.last _), hz]
      refine ⟨pullback.lift g0 (y (Fin.last _)) hw, fun i => ?_, fun g hg => ?_⟩
      · refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [ql, pullback.lift_snd]
        · rw [qc, pullback.lift_fst_assoc, hg0 j]
      · apply pullback.hom_ext
        · rw [pullback.lift_fst]
          refine hg0u _ (fun j => ?_)
          rw [Category.assoc, ← qc, hg]
        · rw [pullback.lift_snd, ← ql, hg]
    · rw [q0]
      exact P.comp_mem _ _ (P.pullback_fst _ _ hf) hP

end GlobalTheory.EtC.CechRep

namespace GlobalTheory.EtC.CechRep

variable {V W : Scheme.{0}} (f : V ⟶ W)

noncomputable section

def isLimitPow {n : ℕ} {Z : Scheme.{0}} {p : Fin (n + 1) → (Z ⟶ V)} (h : IsPow f n Z p) :
    IsLimit (WidePullbackShape.mkCone (F := WidePullbackShape.wideCospan W (fun _ : Fin (n + 1) => V) (fun _ => f))
      (p 0 ≫ f) p (fun j => h.1 j)) := by
  have hs : ∀ s : Cone (WidePullbackShape.wideCospan W (fun _ : Fin (n + 1) => V) (fun _ => f)),
      ∀ j, s.π.app (some j) ≫ f = s.π.app (some 0) ≫ f := fun s j => by
    have a : s.π.app (some j) ≫ f = s.π.app none := s.w (WidePullbackShape.Hom.term j)
    have b : s.π.app (some 0) ≫ f = s.π.app none := s.w (WidePullbackShape.Hom.term 0)
    rw [a, b]
  refine IsLimit.mk (fun s => (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).exists.choose) (fun s j => ?_)
    (fun s m hm => ?_)
  · have hl := (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).exists.choose_spec
    cases j with
    | none =>
      have b : s.π.app (some 0) ≫ f = s.π.app none := s.w (WidePullbackShape.Hom.term 0)
      change (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).exists.choose ≫ (p 0 ≫ f) = s.π.app none
      rw [← Category.assoc, hl 0]
      exact b
    | some j =>
      exact hl j
  · exact (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).unique (fun j => hm (some j))
      (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).exists.choose_spec

end

end GlobalTheory.EtC.CechRep

theorem GlobalTheory.EtC.cech_level_representable : ∀ (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [P.IsMultiplicative] (V W : Scheme.{0}) (f : V ⟶ W), P f → ∀ k : SimplexCategoryᵒᵖ, ∃ (Z : Scheme.{0}) (π : Z ⟶ V) (e : yoneda.obj Z ≅ (cech f).obj k), P π ∧ e.hom ≫ (cechAug f).app k = yoneda.map (π ≫ f) := by
  intro P _ _ V W f hf k
  obtain ⟨Z, p, h, hP⟩ := GlobalTheory.EtC.CechRep.exists_pow f P hf k.unop.len
  have hY := isLimitOfPreserves yoneda (GlobalTheory.EtC.CechRep.isLimitPow f h)
  let D := WidePullbackShape.wideCospan (yoneda.obj W) (fun _ : Fin (k.unop.len + 1) => yoneda.obj V)
    (fun _ => yoneda.map f)
  let iso : WidePullbackShape.wideCospan W (fun _ : Fin (k.unop.len + 1) => V) (fun _ => f) ⋙ yoneda ≅ D :=
    WidePullbackShape.diagramIsoWideCospan _
  have hL := (IsLimit.postcomposeHomEquiv iso _).symm hY
  refine ⟨Z, p 0, IsLimit.conePointUniqueUpToIso hL (limit.isLimit D), hP, ?_⟩
  have := IsLimit.conePointUniqueUpToIso_hom_comp hL (limit.isLimit D) none
  change _ ≫ limit.π D none = _
  refine this.trans ?_
  change yoneda.map (p 0 ≫ f) ≫ iso.hom.app none = _
  simp [iso, WidePullbackShape.diagramIsoWideCospan]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem EtC.isIso_chains_map_of_isIso_free (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E')
    (h : ∀ n, IsIso ((free R).map (f.app n))) : IsIso ((chains R).map f) := by
  have hw : IsIso (((SimplicialObject.whiskering _ _).obj (free R)).map f) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    exact h n
  have : IsIso ((chainsN R).map f) := by
    unfold chainsN
    rw [Functor.comp_map]
    infer_instance
  unfold chains
  rw [Functor.comp_map]
  infer_instance

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem cocycle_comp_assoc_classes : ∀ (R : Type) [CommRing R] {K L M N : Cx R} {a b c ab bc abc : ℤ} (h1 : a + b = ab) (h2 : b + c = bc) (h3 : ab + c = abc) (h4 : a + bc = abc), (∀ (x : Cocycle K L a) (y : Cocycle L M b) (z : CohomologyClass M N c), cpre (zcomp x y h1) N c abc h3 z = cpre x N bc abc h4 (cpre y N c bc h2 z)) ∧ (∀ (x : Cocycle K L a) (y : CohomologyClass L M b) (z : Cocycle M N c), cpost K z ab abc h3 (cpre x M b ab h1 y) = cpre x N bc abc h4 (cpost L z b bc h2 y)) ∧ (∀ (x : CohomologyClass K L a) (y : Cocycle L M b) (z : Cocycle M N c), cpost K (zcomp y z h2) a abc h4 x = cpost K z ab abc h3 (cpost K y a ab h1 x)) := by
  intro R _ K L M N a b c ab bc abc h1 h2 h3 h4
  have hA : a + b + c = abc := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro x y z
    obtain ⟨z, rfl⟩ := z.mk_surjective
    rw [cpre_mk, cpre_mk, cpre_mk]
    exact congrArg CohomologyClass.mk (Cocycle.ext (Cochain.comp_assoc x.1 y.1 z.1 h1 h2 hA))
  · intro x y z
    obtain ⟨y, rfl⟩ := y.mk_surjective
    rw [cpre_mk, cpost_mk, cpost_mk, cpre_mk]
    exact congrArg CohomologyClass.mk (Cocycle.ext (Cochain.comp_assoc x.1 y.1 z.1 h1 h2 hA))
  · intro x y z
    obtain ⟨x, rfl⟩ := x.mk_surjective
    rw [cpost_mk, cpost_mk, cpost_mk]
    exact congrArg CohomologyClass.mk (Cocycle.ext (Cochain.comp_assoc x.1 y.1 z.1 h1 h2 hA).symm)

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ChainsIso

variable (R : Type) [CommRing R]

theorem chains_map_f {E E' : Spc} (g : E ⟶ E') (p : ℕ) :
    ((chains R).map g).f (-(p : ℤ)) =
      (chainsXIso R E p).hom ≫ (free R).map (g.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  have h1 : ((chains R).map g).f (-(p : ℤ)) =
      (chainsXIso R E p).hom ≫ (((chainsN R).map g).f p) ≫ (chainsXIso R E' p).inv :=
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := p) rfl
  rw [h1]
  rfl

theorem chains_isZero (E : Spc) (i : ℤ) (hi : 0 < i) : IsZero (((chains R).obj E).X i) := by
  apply HomologicalComplex.isZero_extend_X
  intro n h
  change -(n : ℤ) = i at h
  omega

end ChainsIso


open ChainsIso in
theorem chains_disc_biprod_isIso : ∀ (R : Type) [CommRing R] {P₁ P₂ Q : PSh} (f₁ : P₁ ⟶ Q) (f₂ : P₂ ⟶ Q),
    IsIso (biprod.desc ((free R).map f₁) ((free R).map f₂)) →
      IsIso (biprod.desc ((chains R).map (disc.map f₁)) ((chains R).map (disc.map f₂))) := by
  intro R _ P₁ P₂ Q f₁ f₂ h
  suffices hc : ∀ i, IsIso ((biprod.desc ((chains R).map (disc.map f₁)) ((chains R).map (disc.map f₂))).f i) from
    HomologicalComplex.Hom.isIso_of_components _
  intro i
  have e := biprod.mapBiprod_hom_desc (HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) i)
    (f := (chains R).map (disc.map f₁)) (g := (chains R).map (disc.map f₂))
  change IsIso ((HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) i).map _)
  rw [← e]
  suffices hs : IsIso (biprod.desc (((chains R).map (disc.map f₁)).f i) (((chains R).map (disc.map f₂)).f i)) by
    exact IsIso.comp_isIso' inferInstance hs
  rcases lt_or_ge 0 i with hi | hi
  · have h1 := chains_isZero R (disc.obj P₁) i hi
    have h2 := chains_isZero R (disc.obj P₂) i hi
    have hQ := chains_isZero R (disc.obj Q) i hi
    refine ⟨⟨0, ?_, hQ.eq_of_src _ _⟩⟩
    apply biprod.hom_ext'
    · exact h1.eq_of_src _ _
    · exact h2.eq_of_src _ _
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨i.natAbs, by omega⟩
    rw [chains_map_f, chains_map_f]
    have hfree : IsIso (biprod.desc ((free R).map ((disc.map f₁).app (op (SimplexCategory.mk p))))
        ((free R).map ((disc.map f₂).app (op (SimplexCategory.mk p))))) := h
    have hc : biprod.desc ((chainsXIso R (disc.obj P₁) p).hom ≫ (free R).map ((disc.map f₁).app (op (SimplexCategory.mk p))) ≫
          (chainsXIso R (disc.obj Q) p).inv)
        ((chainsXIso R (disc.obj P₂) p).hom ≫ (free R).map ((disc.map f₂).app (op (SimplexCategory.mk p))) ≫
          (chainsXIso R (disc.obj Q) p).inv) =
        biprod.map (chainsXIso R (disc.obj P₁) p).hom (chainsXIso R (disc.obj P₂) p).hom ≫
          biprod.desc ((free R).map ((disc.map f₁).app (op (SimplexCategory.mk p))))
            ((free R).map ((disc.map f₂).app (op (SimplexCategory.mk p)))) ≫ (chainsXIso R (disc.obj Q) p).inv := by
      apply biprod.hom_ext' <;> simp
    rw [hc]
    exact IsIso.comp_isIso' (show IsIso (biprod.mapIso (chainsXIso R (disc.obj P₁) p) (chainsXIso R (disc.obj P₂) p)).hom
      from inferInstance) (IsIso.comp_isIso' hfree inferInstance)

end GlobalTheory.EtC
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC

def liftHom {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) : ULift.{1} R →+* ULift.{1} S :=
  (ULift.ringEquiv.symm : S ≃+* ULift.{1} S).toRingHom.comp (φ.comp (ULift.ringEquiv : ULift.{1} R ≃+* R).toRingHom)

instance {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) :
    (ModuleCat.coextendScalars.{1, 1, 1} (liftHom φ)).IsRightAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} (liftHom φ)).isRightAdjoint

def coind {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) : Shv R ⥤ Shv S :=
  sheafCompose _ (ModuleCat.coextendScalars.{1, 1, 1} (liftHom φ))

end GlobalTheory.EtC

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem yoneda_map_isLocallySurjective_of_etale_surjective (Y X : Scheme.{0}) (f : Y ⟶ X)
    (hf : Etale f) (hs : Surjective f) :
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (yoneda.map f) where
  imageSieve_mem {U} s := by
    refine Scheme.mem_grothendieckTopology_iff.2 ⟨Scheme.Cover.mkOfCovers PUnit (fun _ => pullback f s) (fun _ => pullback.snd f s)
      (fun x => ?_) (fun _ => inferInstance), ?_⟩
    · obtain ⟨y, hy⟩ := (inferInstance : Surjective (pullback.snd f s)).surj x
      exact ⟨⟨⟩, y, hy⟩
    · rintro V g ⟨j⟩
      exact ⟨pullback.fst f s, by simp; exact pullback.condition⟩

theorem isLocallySurjective_of_section {P Q : PSh} (f : P ⟶ Q) (s : Q ⟶ P) (h : s ≫ f = 𝟙 Q) :
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f :=
  Presheaf.isLocallySurjective_of_surjective _ f fun U q =>
    ⟨s.app U q, by simpa using ConcreteCategory.congr_hom (NatTrans.congr_app h U) q⟩

theorem isLocallySurjective_of_isPullback {P Q P' Q' : PSh} (a : P' ⟶ P) (f' : P' ⟶ Q')
    (f : P ⟶ Q) (b : Q' ⟶ Q) (hpb : IsPullback a f' f b)
    (hf : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f) :
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f' where
  imageSieve_mem {U} y := by
    refine Scheme.etaleTopology.superset_covering ?_ (Presheaf.imageSieve_mem _ f (b.app _ y))
    rintro V i ⟨t, ht⟩
    have hV := hpb.map ((evaluation _ _).obj (op V))
    obtain ⟨x, hx1, hx2⟩ := Types.exists_of_isPullback hV t (Q'.map i.op y)
      (by simpa [NatTrans.naturality_apply] using ht)
    exact ⟨x, hx2⟩

theorem locallySurjective_etale_section_baseChange :
    (∀ (Y X : Scheme.{0}) (f : Y ⟶ X), Etale f → Surjective f → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (yoneda.map f)) ∧ (∀ (P Q : PSh) (f : P ⟶ Q) (s : Q ⟶ P), s ≫ f = 𝟙 Q → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f) ∧ ∀ (P Q P' Q' : PSh) (a : P' ⟶ P) (f' : P' ⟶ Q') (f : P ⟶ Q) (b : Q' ⟶ Q), IsPullback a f' f b → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f' :=
  ⟨yoneda_map_isLocallySurjective_of_etale_surjective,
   fun _ _ f s h => isLocallySurjective_of_section f s h,
   fun _ _ _ _ a f' f b h hf => isLocallySurjective_of_isPullback a f' f b h hf⟩

end GlobalTheory.EtC
end
