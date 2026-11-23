module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle019
public import Mathlib.Order.CompletePartialOrder
public import Development.EtaleCohomology.CohomologicalPurity.Bundle025
public import Development.EtaleCohomology.CohomologicalPurity.Bundle004
public import Development.EtaleCohomology.CohomologicalPurity.LeafClCut
public import Development.EtaleCohomology.KummerTheory.Bundle015
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
public import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

variable {R : Type} [CommRing R]

theorem imageSieve_add' {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : F ⟶ G) {T : Scheme.{0}}
    (s₁ s₂ : G.obj (op T)) :
    Presheaf.imageSieve f s₁ ⊓ Presheaf.imageSieve f s₂ ≤ Presheaf.imageSieve f (s₁ + s₂) := by
  rintro V g ⟨⟨t₁, h₁⟩, ⟨t₂, h₂⟩⟩
  exact ⟨t₁ + t₂, by rw [map_add (f := _), map_add (f := _), h₁, h₂]⟩

theorem imageSieve_smul' {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : F ⟶ G) {T : Scheme.{0}}
    (r : ULift.{1} R) (s : G.obj (op T)) :
    Presheaf.imageSieve f s ≤ Presheaf.imageSieve f (r • s) := by
  rintro V g ⟨t, h⟩
  exact ⟨r • t, by rw [map_smul, map_smul, h]⟩

theorem imageSieve_zero' {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : F ⟶ G) {T : Scheme.{0}} :
    Presheaf.imageSieve f (0 : G.obj (op T)) = ⊤ := by
  ext V g
  simp only [Sieve.top_apply, iff_true]
  exact ⟨0, by rw [map_zero, map_zero]⟩

theorem pcok_π_apply (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
    (b : B' ⟶ B) (w : i' ≫ b = a ≫ i) (V : Scheme.{0}ᵒᵖ) (m : ((freeP R).obj B').obj V) :
    (pcok R i' i a b w).app V ((cokernel.π ((freeP R).map i')).app V m) =
      (cokernel.π ((freeP R).map i)).app V (((freeP R).map b).app V m) := by
  have e : cokernel.π ((freeP R).map i') ≫ pcok R i' i a b w = (freeP R).map b ≫ cokernel.π _ := by
    simp [pcok]
  have := ConcreteCategory.congr_hom (NatTrans.congr_app e V) m
  simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using this

theorem π_freeP_apply (R : Type) [CommRing R] {A B : PSh} (i : A ⟶ B) (V : Scheme.{0}ᵒᵖ)
    (m : ((freeP R).obj A).obj V) :
    (cokernel.π ((freeP R).map i)).app V (((freeP R).map i).app V m) = 0 := by
  have := ConcreteCategory.congr_hom (NatTrans.congr_app (cokernel.condition ((freeP R).map i)) V) m
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at this
  rw [this]; rfl

theorem freePresheaf_map_freeMk (R : Type) [CommRing R] {A B : PSh} (i : A ⟶ B) (V : Scheme.{0}ᵒᵖ) (x : A.obj V) :
    ((freeP R).map i).app V (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (i.app V x)) := by
  exact ModuleCat.free_map_apply _ _

theorem freePresheaf_obj_map_freeMk (R : Type) [CommRing R] (B : PSh) {V W : Scheme.{0}ᵒᵖ} (g : V ⟶ W) (x : B.obj V) :
    ((freeP R).obj B).map g (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (B.map g x)) := by
  exact ModuleCat.free_map_apply _ _

theorem π_app_surj (R : Type) [CommRing R] {A B : PSh} (i : A ⟶ B) (V : Scheme.{0}ᵒᵖ) :
    Function.Surjective ((cokernel.π ((freeP R).map i)).app V) := by
  have : Epi ((cokernel.π ((freeP R).map i)).app V) := inferInstance
  exact (ModuleCat.epi_iff_surjective _).1 this

theorem exists_finset_adjoin_laurent_preimage (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
    (b : B' ⟶ B) (w : i' ≫ b = a ≫ i)
    (h2 : ∀ (T : Scheme.{0}) (y : B.obj (op T)), ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
      (∃ x : A.obj (op V), i.app (op V) x = B.map g.op y) ∨ ∃ y' : B'.obj (op V), b.app (op V) y' = B.map g.op y)
    (T : Scheme.{0}) (v : ((freeP R).obj B).obj (op T)) :
    Presheaf.imageSieve (pcok R i' i a b w) ((cokernel.π ((freeP R).map i)).app (op T) v) ∈
      Scheme.etaleTopology T := by
  let J := Scheme.etaleTopology.{0}
  let N : Submodule (ULift.{1} R) (((freeP R).obj B).obj (op T)) :=
    { carrier := {v | Presheaf.imageSieve (pcok R i' i a b w) ((cokernel.π ((freeP R).map i)).app (op T) v) ∈ J T}
      zero_mem' := by
        simp only [Set.mem_setOf_eq]; rw [map_zero, imageSieve_zero']; exact J.top_mem T
      add_mem' := fun {v₁ v₂} h₁ h₂ => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_add (f := _)]; exact J.superset_covering (imageSieve_add' _ _ _) (J.intersection_covering h₁ h₂)
      smul_mem' := fun r v h => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_smul]; exact J.superset_covering (imageSieve_smul' _ _ _) h }
  have gen : ∀ x, ModuleCat.freeMk x ∈ N := by
    rintro ⟨y⟩
    show Presheaf.imageSieve _ _ ∈ J T
    obtain ⟨S, hS, hS'⟩ := h2 T y
    refine J.superset_covering ?_ hS
    intro V g hg
    have nat := NatTrans.naturality_apply (cokernel.π ((freeP R).map i)) g.op (ModuleCat.freeMk (ULift.up y))
    rcases hS' g hg with ⟨x₀, hx₀⟩ | ⟨y', hy'⟩
    · refine ⟨0, ?_⟩
      rw [map_zero]; erw [← nat]
      rw [freePresheaf_obj_map_freeMk]; erw [← hx₀]; rw [← freePresheaf_map_freeMk R i (op V) x₀]; exact (π_freeP_apply R i (op V) _).symm
    · refine ⟨_, (pcok_π_apply R i' i a b w (op V) (ModuleCat.freeMk (ULift.up y'))).trans ?_⟩
      rw [freePresheaf_map_freeMk R b (op V) y']; erw [hy', ← freePresheaf_obj_map_freeMk R B g.op y]; exact nat
  show v ∈ N
  induction v using Finsupp.induction_linear with
  | zero => exact N.zero_mem
  | add v₁ v₂ h₁ h₂ => exact N.add_mem h₁ h₂
  | single x r =>
    have := N.smul_mem r (gen x)
    convert this using 1
    first
    | exact (Finsupp.smul_single_one x r).symm
    | (unfold ModuleCat.freeMk; erw [Finsupp.smul_single_one])

theorem leafFreeCokSurj : LeafFreeCokSurj := by
  intro R _ A' B' A B i' i a b w h2
  constructor
  intro T s
  obtain ⟨v, rfl⟩ := π_app_surj R i (op T) s
  exact exists_finset_adjoin_laurent_preimage R i' i a b w h2 T v

theorem LeafFreeCok_of_inj (hI : LeafFreeCokInj) : LeafFreeCok := LeafFreeCok_of leafFreeCokSurj hI

end LateralTheory.CohomologicalPurity
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

abbrev PCx (R : Type) [CommRing R] := ChainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℕ

def Cyc {R : Type} [CommRing R] (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (x : (K.X n).obj T) : Prop :=
  ∀ m, ((K.d n m).app T).hom x = 0

def Bdy {R : Type} [CommRing R] (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (x : (K.X n).obj T) : Prop :=
  ∃ y, ((K.d (n + 1) n).app T).hom y = x

def InjC {R : Type} [CommRing R] {K L : PCx R} (φ : K ⟶ L) (n : ℕ) : Prop :=
  ∀ (T : Scheme.{0}ᵒᵖ) (x : (K.X n).obj T), Cyc K n T x → Bdy L n T ((φ.f n).app T |>.hom x) →
    ∃ S ∈ Scheme.etaleTopology.{0} T.unop, ∀ ⦃U : Scheme.{0}⦄ (f : U ⟶ T.unop), S f → Bdy K n (op U) (((K.X n).map f.op).hom x)

def SurjC {R : Type} [CommRing R] {K L : PCx R} (φ : K ⟶ L) (n : ℕ) : Prop :=
  ∀ (T : Scheme.{0}ᵒᵖ) (x : (L.X n).obj T), Cyc L n T x →
    ∃ S ∈ Scheme.etaleTopology.{0} T.unop, ∀ ⦃U : Scheme.{0}⦄ (f : U ⟶ T.unop), S f →
      ∃ x', Cyc K n (op U) x' ∧ Bdy L n (op U) (((φ.f n).app (op U)).hom x' - ((L.X n).map f.op).hom x)

def LeafHomLoc : Prop := ∀ (R : Type) [CommRing R] (K L : PCx R) (φ : K ⟶ L) (n : ℕ), InjC φ n → SurjC φ n →
  Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap φ n) ∧
  Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap φ n)

def LeafAugSurj : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R] (n : ℕ),
    SurjC ((chainsP R).map (aug _ hc)) n

def LeafAugInj : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  (∀ (x : X) j k, x ∈ Set.range (c j) → x ∈ Set.range (c k) → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ Set.range (c l)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R] (n : ℕ),
    InjC ((chainsP R).map (aug _ hc)) n

theorem LeafAugLocal_of (h1 : LeafHomLoc) (hs : LeafAugSurj) (hi : LeafAugInj) : LeafAugLocal := by
  intro J _ D X c ho hcov hdir hc R _ n
  exact h1 R _ _ _ n (hi J D X c ho hcov hdir hc R n) (hs J D X c ho hcov hc R n)

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem quotC_bij (d : ℕ) (R : Type) [CommRing R] :
    Function.Bijective ((Ideal.Quotient.mk (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R)))).comp
      MvPolynomial.C) := by
  have hJ : Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R) = MvPolynomial.X '' Set.univ := Set.image_univ.symm
  constructor
  · rw [injective_iff_map_eq_zero]
    intro r hr
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hJ, MvPolynomial.mem_ideal_span_X_image] at hr
    by_contra h
    obtain ⟨i, -, hi⟩ := hr 0 (by rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C, if_pos rfl]; exact h)
    exact hi rfl
  · intro y
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨MvPolynomial.constantCoeff p, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.eq, hJ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hcon
    push_neg at hcon
    have : m = 0 := Finsupp.ext fun i => hcon i (Set.mem_univ i)
    subst this
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_pos rfl,
      ← MvPolynomial.constantCoeff_eq, sub_self] at hm
    exact hm rfl

theorem leafAffQuot_pf : LeafAffQuot := by
  intro hQ d R B C _ _ _ ψ η hψ I K hη hK hI
  subst hK
  have hJI : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).map ψ = I := by
    rw [Ideal.map_span, ← Set.range_comp]; exact hI
  subst hJI
  have b2 := hψ.2
  have b3 := hQ B C η _ hη
  have e : (Ideal.Quotient.mk _).comp (η.comp (ψ.comp MvPolynomial.C)) =
      ((Ideal.quotientMap _ η Ideal.le_comap_map).comp (Ideal.quotientMap _ ψ Ideal.le_comap_map)).comp
        ((Ideal.Quotient.mk (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R)))).comp
          MvPolynomial.C) := by
    ext r; simp [Ideal.quotientMap_mk]
  rw [e]
  exact (b3.comp b2).comp (quotC_bij d R)

theorem LeafPrdAff_of' (hT : LeafThom) (hA : LeafActNat) (h1 : LeafHensH) (h3 : LeafExcAff)
    (hQ : LeafQuot) (hI : LeafIndExc) : LeafPrdAff :=
  LeafPrdAff_of hT hA h1 leafAffQuot_pf h3 hQ hI

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem off_map_le {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (J : Ideal A) :
    off B (J.map φ) ≤ Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ off A J := by
  intro x hx
  change x ∈ (PrimeSpectrum.zeroLocus _)ᶜ at hx
  change PrimeSpectrum.comap φ x ∈ (PrimeSpectrum.zeroLocus (J : Set A))ᶜ
  intro h; apply hx
  rw [PrimeSpectrum.mem_zeroLocus] at h
  exact (Ideal.map_le_iff_le_comap.2 h : J.map φ ≤ _)

theorem opnMap_comp' {X'' X' X : Scheme.{0}} (k : X'' ⟶ X) (g : X'' ⟶ X') (f : X' ⟶ X) (hk : k = g ≫ f)
    (U'' : X''.Opens) (U' : X'.Opens) (U : X.Opens) (h1 : U'' ≤ g ⁻¹ᵁ U') (h2 : U' ≤ f ⁻¹ᵁ U)
    (h : U'' ≤ k ⁻¹ᵁ U) : opnMap k U'' U h = opnMap g U'' U' h1 ≫ opnMap f U' U h2 := by
  subst hk
  apply Arrow.hom_ext
  · change sch.map (Scheme.Hom.resLE (g ≫ f) U U'' h) =
      sch.map (Scheme.Hom.resLE g U' U'' h1) ≫ sch.map (Scheme.Hom.resLE f U U' h2)
    rw [← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]
  · change sch.map (g ≫ f) = sch.map g ≫ sch.map f
    exact Functor.map_comp _ _ _

theorem leafExcAff_pf : LeafExcAff := by
  intro hyp hIE d q _ R B C _ _ _ ψ η hq hψ I K hη hK hI
  have hJI : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).map ψ = I := by
    rw [Ideal.map_span, ← Set.range_comp]; exact hI
  subst hJI; subst hK
  have hJfg : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).FG :=
    Submodule.fg_span (Set.finite_range _)
  have hIfg := hJfg.map ψ
  have hqP : IsUnit (q : MvPolynomial (Fin d) R) := by
    simpa using hq.map (MvPolynomial.C : R →+* MvPolynomial (Fin d) R)
  have hqB : IsUnit (q : B) := by simpa using hqP.map ψ
  have e1 := hIE hyp.1 hyp.2.2.2.1 hyp.2.2.2.2.2.2.2.2.1 q ψ _ hJfg (indNbhd_of_nbhd ψ _ hψ) hqP (off_map_le ψ _)
  have e2 := hIE hyp.1 hyp.2.2.2.1 hyp.2.2.2.2.2.2.2.2.1 q η _ hIfg hη hqB (off_map_le η _)
  have hle : off C ((Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).map ψ |>.map η) ≤
      Spec.map (CommRingCat.ofHom (η.comp ψ)) ⁻¹ᵁ off _ (Ideal.span (Set.range MvPolynomial.X)) := by
    rw [Ideal.map_map]; exact off_map_le _ _
  refine ⟨hle, ?_⟩
  have hs : Spec.map (CommRingCat.ofHom (η.comp ψ)) =
      Spec.map (CommRingCat.ofHom η) ≫ Spec.map (CommRingCat.ofHom ψ) := by
    rw [← Spec.map_comp]; rfl
  rw [opnMap_comp' _ _ _ hs _ _ _ (off_map_le η _) (off_map_le ψ _)]
  exact exc_comp q e2 e1

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.DiscPf

variable {R : Type} [CommRing R]

abbrev Cd (R : Type) [CommRing R] (P : PSh) : Cx R := (chains R).obj (disc.obj P)

abbrev e0 (R : Type) [CommRing R] (P : PSh) : (Cd R P).X (-((0 : ℕ) : ℤ)) ≅ (free R).obj P := chainsXIso R (disc.obj P) 0

theorem isZero_pos (P : PSh) (j : ℤ) (hj : 0 < j) : IsZero ((Cd R P).X j) :=
  HomologicalComplex.isZero_extend_X ((chainsN R).obj (disc.obj P)) ComplexShape.embeddingDownNat j
    (fun i h => by change (-(i : ℤ)) = j at h; omega)

theorem d_one (P : PSh) : (Cd R P).d (-1) (-((0 : ℕ) : ℤ)) = 0 := by
  have h := LateralTheory.KummerTheory.chains_d R (disc.obj P) 0
  have hs : (∑ i : Fin (0 + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ (disc.obj P) i)) = 0 := by
    have : ∀ i : Fin (0 + 2), (free R).map (SimplicialObject.δ (disc.obj P) i) = 𝟙 _ := fun i => (free R).map_id _
    simp only [this]
    simp
  rw [hs, zero_comp] at h
  have : (chainsXIso R (disc.obj P) (0 + 1)).hom ≫ (chainsXIso R (disc.obj P) (0 + 1)).inv ≫
      (Cd R P).d (-((0 + 1 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ)) = 0 := by rw [h, comp_zero]
  simpa using this

def coch {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) : Cochain (Cd R P) K n :=
  Cochain.single (p := -((0 : ℕ) : ℤ)) (q := n) ((e0 R P).hom ≫ a) n

theorem coch_add {K : Cx R} {n : ℤ} (P : PSh) (a b : (free R).obj P ⟶ K.X n) : coch P (a + b) = coch P a + coch P b := by
  ext p q hpq
  by_cases hp : p = -((0 : ℕ) : ℤ)
  · subst hp
    obtain rfl : q = n := by omega
    simp [coch, Cochain.single_v]
  · simp [coch, Cochain.single_v_eq_zero _ _ _ _ _ hp]

theorem delta_coch {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) :
    δ n (n + 1) (coch P a) = Cochain.single (p := -((0 : ℕ) : ℤ)) ((e0 R P).hom ≫ a ≫ K.d n (n + 1)) (n + 1) := by
  rw [coch, Cochain.δ_single _ n (n + 1) rfl (-1) (n + 1) (by simp) rfl, d_one, zero_comp, Cochain.single_zero, smul_zero,
    add_zero, Category.assoc]

theorem coch_cocycle {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) :
    δ n (n + 1) (coch P a) = 0 := by
  rw [delta_coch, ha, comp_zero, Cochain.single_zero]

def cz {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) : Cocycle (Cd R P) K n :=
  ⟨coch P a, (Cocycle.mem_iff n (n + 1) rfl _).2 (coch_cocycle P a ha)⟩

open Classical in
def cl (K : Cx R) (n : ℤ) (P : PSh) (a : (free R).obj P ⟶ K.X n) : CohomologyClass (Cd R P) K n :=
  if ha : a ≫ K.d n (n + 1) = 0 then CohomologyClass.mk (cz P a ha) else 0

theorem cl_eq {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) :
    cl K n P a = CohomologyClass.mk (cz P a ha) := dif_pos ha

theorem cl_add {K : Cx R} {n : ℤ} (P : PSh) (a b : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0)
    (hb : b ≫ K.d n (n + 1) = 0) : cl K n P (a + b) = cl K n P a + cl K n P b := by
  have hab : (a + b) ≫ K.d n (n + 1) = 0 := by rw [Preadditive.add_comp, ha, hb, add_zero]
  rw [cl_eq _ _ ha, cl_eq _ _ hb, cl_eq _ _ hab, ← CohomologyClass.mk_add]
  congr 1
  exact Cocycle.ext (coch_add P a b)

theorem cl_zero_iff {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) :
    cl K n P a = 0 ↔ ∃ b, b ≫ K.d (n - 1) n = a := by
  rw [cl_eq _ _ ha, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  constructor
  · rintro ⟨β, hβ⟩
    refine ⟨(e0 R P).inv ≫ β.v (-((0 : ℕ) : ℤ)) (n - 1) (by omega), ?_⟩
    have h1 := Cochain.congr_v hβ (-((0 : ℕ) : ℤ)) n (by omega)
    rw [δ_v (n - 1) n (by omega) β _ n _ (n - 1) (-((0 : ℕ) : ℤ) + 1) (by omega) rfl,
      (isZero_pos P (-((0 : ℕ) : ℤ) + 1) (by omega)).eq_of_tgt ((Cd R P).d (-((0 : ℕ) : ℤ)) _) 0, zero_comp, smul_zero, add_zero] at h1
    have h2 : (cz P a ha).1.v (-((0 : ℕ) : ℤ)) n (by omega) = (e0 R P).hom ≫ a := Cochain.single_v _ _ _
    rw [h2] at h1
    rw [Category.assoc, h1, Iso.inv_hom_id_assoc]
  · rintro ⟨b, rfl⟩
    refine ⟨Cochain.single (p := -((0 : ℕ) : ℤ)) (q := n - 1) ((e0 R P).hom ≫ b) (n - 1), ?_⟩
    rw [Cochain.δ_single _ (n - 1) n (by omega) (-1) n (by simp) (by omega), d_one, zero_comp, Cochain.single_zero, smul_zero,
      add_zero, Category.assoc]
    rfl

theorem etale_discrete_chains_degree_zero_iso_free_naturality (P' P : PSh) (f : P' ⟶ P) :
    ((chains R).map (disc.map f)).f (-((0 : ℕ) : ℤ)) ≫ (e0 R P).hom = (e0 R P').hom ≫ (free R).map f := by
  dsimp only [chains, e0, chainsXIso, Functor.comp_map, Functor.comp_obj]
  erw [HomologicalComplex.extendMap_f _ _ (i := 0) rfl]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem cl_nat {K : Cx R} {n : ℤ} (P' P : PSh) (f : P' ⟶ P) (a : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) :
    cpre (Cocycle.ofHom ((chains R).map (disc.map f))) K n n (zero_add n) (cl K n P a) = cl K n P' ((free R).map f ≫ a) := by
  have ha' : ((free R).map f ≫ a) ≫ K.d n (n + 1) = 0 := by rw [Category.assoc, ha, comp_zero]
  rw [cl_eq _ _ ha, cl_eq _ _ ha', cpre_mk]
  congr 1
  apply Cocycle.ext
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  change ((Cochain.ofHom ((chains R).map (disc.map f))).comp (coch P a) (zero_add n)).v p q hpq = (coch P' _).v p q hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  by_cases hp : p = -((0 : ℕ) : ℤ)
  · subst hp
    obtain rfl : q = n := by omega
    simp only [coch, Cochain.single_v]
    rw [← Category.assoc, etale_discrete_chains_degree_zero_iso_free_naturality, Category.assoc]
  · simp only [coch, Cochain.single_v_eq_zero _ _ _ _ _ hp, comp_zero]

end LateralTheory.CohomologicalPurity.Cl.DiscPf

namespace LateralTheory.CohomologicalPurity.Cl


open DiscPf in
def LeafDiscNrm : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (n : ℤ) (P : PSh)
  (z : Cocycle ((chains R).obj (disc.obj P)) K n),
  ∃ (a : (free R).obj P ⟶ K.X n) (β : Cochain ((chains R).obj (disc.obj P)) K (n - 1)),
    z.1 = Cochain.single (p := -((0 : ℕ) : ℤ)) (q := n) ((chainsXIso R (disc.obj P) 0).hom ≫ a) n + δ (n - 1) n β

open DiscPf in
theorem LeafDisc_of (hN : LeafDiscNrm) : LeafDisc := by
  intro R _ K n
  refine ⟨cl K n, fun P a b ha hb => cl_add P a b ha hb, ?_, fun P a ha => cl_zero_iff P a ha,
    fun P' P f a ha => cl_nat P' P f a ha⟩
  intro P x
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨a, β, hz⟩ := hN R K n P z
  have hz0 : δ n (n + 1) z.1 = 0 := (Cocycle.mem_iff n (n + 1) rfl z.1).1 z.2
  have hc : δ n (n + 1) (coch P a) = 0 := by
    have := hz0
    rw [hz, δ_add, δ_δ, add_zero] at this
    exact this
  have ha : a ≫ K.d n (n + 1) = 0 := by
    rw [delta_coch] at hc
    have h1 := Cochain.congr_v hc (-((0 : ℕ) : ℤ)) (n + 1) (by omega)
    rw [Cochain.single_v, Cochain.zero_v] at h1
    exact (cancel_epi (e0 R P).hom).1 (h1.trans (comp_zero).symm)
  refine ⟨a, ha, ?_⟩
  rw [cl_eq _ _ ha, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨-β, ?_⟩
  rw [δ_neg]
  change _ = coch P a - z.1
  rw [hz]
  unfold coch
  abel

end LateralTheory.CohomologicalPurity.Cl
end
end
