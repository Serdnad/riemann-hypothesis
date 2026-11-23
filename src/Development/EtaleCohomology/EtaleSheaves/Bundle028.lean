module

public import Development.EtaleCohomology.EtaleSheaves.Bundle013
public import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Development.EtaleCohomology.EtaleSheaves.LineHigh
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC MonoidalCategory

open scoped TensorProduct DirectSum

namespace LateralTheory.E.LeafTwTensExistsPf

variable {R : Type} [CommRing R]

abbrev PSh1 (R : Type) [CommRing R] := Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)

def tF (R : Type) [CommRing R] : Shv R ⥤ Shv R ⥤ PSh1 R :=
  sheafToPresheaf _ _ ⋙ curriedTensor (PSh1 R) ⋙ (Functor.whiskeringLeft _ _ _).obj (sheafToPresheaf _ _)

instance : MonoidalPreadditive (PSh1 R) where
  whiskerLeft_zero := by intros; exact NatTrans.ext (funext fun U => by simp; rfl)
  zero_whiskerRight := by intros; exact NatTrans.ext (funext fun U => by simp; rfl)
  whiskerLeft_add := by intros; exact NatTrans.ext (funext fun U => by simp; rfl)
  add_whiskerRight := by intros; exact NatTrans.ext (funext fun U => by simp; rfl)

instance : (tF R).PreservesZeroMorphisms where
  map_zero A B := by
    apply NatTrans.ext; funext C
    change (sheafToPresheaf _ _).map (0 : A ⟶ B) ▷ C.obj = 0
    rw [Functor.map_zero]; exact MonoidalPreadditive.zero_whiskerRight

instance (A : Shv R) : ((tF R).obj A).PreservesZeroMorphisms where
  map_zero B C := by
    change A.obj ◁ (sheafToPresheaf _ _).map (0 : B ⟶ C) = 0
    rw [Functor.map_zero]; exact MonoidalPreadditive.whiskerLeft_zero

abbrev P (I J : Cx R) : CochainComplex (PSh1 R) ℤ := HomologicalComplex.mapBifunctor I J (tF R) (ComplexShape.up ℤ)

abbrev T (I J : Cx R) : Cx R := ((presheafToSheaf Scheme.etaleTopology _).mapHomologicalComplex _).obj (P I J)

abbrev jm (I J : Cx R) (s t w : ℤ) (h : s + t = w) : ((tF R).obj (I.X s)).obj (J.X t) ⟶ sheafify Scheme.etaleTopology ((P I J).X w) :=
  HomologicalComplex.ιMapBifunctor I J (tF R) (ComplexShape.up ℤ) s t w h ≫ toSheafify Scheme.etaleTopology _

theorem jm_d (I J : Cx R) (s t w : ℤ) (h : s + t = w) :
    jm I J s t w h ≫ sheafifyMap Scheme.etaleTopology ((P I J).d w (w + 1)) =
      ((tF R).map (I.d s (s + 1))).app (J.X t) ≫ jm I J (s + 1) t (w + 1) (by omega) +
      s.negOnePow • (((tF R).obj (I.X s)).map (J.d t (t + 1)) ≫ jm I J s (t + 1) (w + 1) (by omega)) := by
  rw [jm, Category.assoc, ← toSheafify_naturality, ← Category.assoc, HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.up ℤ).Rel s (s + 1) by simp) _ _ (by simp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (show (ComplexShape.up ℤ).Rel t (t + 1) by simp) _ (by simp; omega)]
  simp [Preadditive.add_comp, Category.assoc]

def tau (I J : Cx R) : Pair I J (T I J) where
  mul U s t w h := (TensorProduct.mk _ _ _).compr₂ ((jm I J s t w h).app (op U)).hom
  nat := by
    intro V U g s t w h a b
    have := congrArg (fun f => f.hom (a ⊗ₜ b)) ((jm I J s t w h).naturality g.op)
    exact this.symm
  leibniz := by
    intro U s t w h a b
    change ((jm I J s t w h ≫ sheafifyMap Scheme.etaleTopology ((P I J).d w (w + 1))).app (op U)).hom (a ⊗ₜ b) = _
    rw [jm_d]
    simp only [NatTrans.app_add, NatTrans.app_zsmul, NatTrans.comp_app, ModuleCat.hom_add, ModuleCat.hom_comp,
      LinearMap.add_apply, LinearMap.comp_apply, Units.smul_def]
    simp only [ModuleCat.hom_zsmul, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply]
    rfl

def Phi (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] ToType ((P I J).X w |>.obj (op U)) := by
  classical
  exact DirectSum.toModule _ _ _ fun p =>
    ((HomologicalComplex.ιMapBifunctor I J (tF R) (ComplexShape.up ℤ) p.1.1 p.1.2 w p.2).app (op U)).hom

theorem Phi_lof (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (t : Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) :
    Phi I J U w (DirectSum.of (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p t) =
      ((HomologicalComplex.ιMapBifunctor I J (tF R) (ComplexShape.up ℤ) p.1.1 p.1.2 w p.2).app (op U)).hom t := by
  classical
  unfold Phi
  exact DirectSum.toModule_lof (ULift.{1} R) (M := fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p t

theorem lift_eq (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    (tau I J).lift U w x = ((toSheafify Scheme.etaleTopology ((P I J).X w)).app (op U)).hom (Phi I J U w x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => first | (erw [map_zero, map_zero] <;> rfl) | (erw [map_zero, map_zero, map_zero] <;> rfl) | (erw [map_zero, map_zero, map_zero, map_zero] <;> rfl) | (simp only [map_zero]) | rfl
  | add x y hx hy => erw [map_add, map_add, map_add, hx, hy] <;> rfl
  | of p t =>
    rw [Phi_lof]
    unfold Pair.lift
    erw [DirectSum.toModule_lof]
    induction t using TensorProduct.induction_on with
    | zero => erw [map_zero, map_zero, map_zero]
    | add x y hx hy => erw [map_add, map_add, map_add, hx, hy]
    | tmul a b => rw [TensorProduct.lift.tmul]; rfl

theorem Phi_nat (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    ((P I J).X w |>.map g.op).hom (Phi I J U w x) = Phi I J V w (Tens.res g w x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => first | (erw [map_zero, map_zero] <;> rfl) | (erw [map_zero, map_zero, map_zero] <;> rfl) | (erw [map_zero, map_zero, map_zero, map_zero] <;> rfl) | (simp only [map_zero]) | rfl
  | add x y hx hy => erw [map_add, map_add, map_add, map_add, hx, hy] <;> rfl
  | of p t =>
    rw [Phi_lof]
    unfold Tens.res
    erw [DirectSum.lmap_lof]
    erw [Phi_lof]
    have := congrArg (fun f => f.hom t)
      ((HomologicalComplex.ιMapBifunctor I J (tF R) (ComplexShape.up ℤ) p.1.1 p.1.2 w p.2).naturality g.op)
    exact this.symm

abbrev GX (I J : Cx R) : GradedObject (ℤ × ℤ) (PSh1 R) :=
  ((((tF R).mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj I).obj J).toGradedObject

def hcol (I J : Cx R) (U : Scheme.{0}) (w : ℤ) :
    IsColimit (((evaluation Scheme.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} R))).obj (op U)).mapCocone
      ((GX I J).cofanMapObj (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) w)) :=
  isColimitOfPreserves _ ((GX I J).isColimitCofanMapObj _ w)

def dsCocone (I J : Cx R) (U : Scheme.{0}) (w : ℤ) :
    Cocone (Discrete.functor ((GX I J).mapObjFun (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) w) ⋙
      (evaluation Scheme.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} R))).obj (op U)) where
  pt := ModuleCat.of (ULift.{1} R) (Tens I J U w)
  ι := Discrete.natTrans fun k => ModuleCat.ofHom (DirectSum.lof (ULift.{1} R) _
    (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨k.as.1, k.as.2⟩)

theorem Phi_bij (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Function.Bijective (Phi I J U w) := by
  classical
  let hc := hcol I J U w
  let Ψ := hc.desc (dsCocone I J U w)
  have h1 : ∀ x, Ψ.hom (Phi I J U w x) = x := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => erw [map_zero]; first | rfl | exact map_zero Ψ.hom
    | add x y hx hy => erw [map_add, map_add, hx, hy]; rfl
    | of p t =>
      rw [Phi_lof]
      have := congrArg (fun f => f.hom t) (hc.fac (dsCocone I J U w) ⟨⟨p.1, p.2⟩⟩)
      exact this
  have h2 : ∀ y, Phi I J U w (Ψ.hom y) = y := by
    let PhiH : (dsCocone I J U w).pt ⟶ (((evaluation Scheme.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} R))).obj (op U)).mapCocone
      ((GX I J).cofanMapObj (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) w)).pt :=
      ModuleCat.ofHom (Phi I J U w)
    have : Ψ ≫ PhiH = 𝟙 _ := by
      apply hc.hom_ext
      rintro ⟨k⟩
      rw [← Category.assoc, hc.fac, Category.comp_id]
      ext t
      exact Phi_lof I J U w ⟨k.1, k.2⟩ t
    intro y
    exact congrArg (fun f => f.hom y) this
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem tau_isTensor (I J : Cx R) : (tau I J).IsTensor := by
  constructor
  · intro U w y
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology ((P I J).X w)) y, ?_⟩
    rintro V g ⟨t, ht⟩
    obtain ⟨x, rfl⟩ := (Phi_bij I J V w).2 t
    exact ⟨x, by rw [lift_eq]; exact ht⟩
  · intro U w x hx
    rw [lift_eq] at hx
    have hm := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology ((P I J).X w))
      (X := op U) (Phi I J U w x) 0 (by rw [map_zero]; exact hx)
    refine ⟨_, hm, ?_⟩
    intro V g hg
    apply (Phi_bij I J V w).1
    rw [map_zero, ← Phi_nat]
    have hg' : ((P I J).X w |>.map g.op).hom (Phi I J U w x) = ((P I J).X w |>.map g.op).hom 0 := hg
    rw [hg', map_zero]

theorem tens_exists (I J : Cx R) : ∃ (K : Cx R) (τ : Pair I J K), τ.IsTensor := ⟨_, tau I J, tau_isTensor I J⟩

end LateralTheory.E.LeafTwTensExistsPf

theorem LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensExists_of : LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensExists := by
  intro q _ i j
  exact LateralTheory.E.LeafTwTensExistsPf.tens_exists _ _
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.FibPf

def FibClosed : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) → ∀ {Z S : Scheme.{0}}
  (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S →
  (∀ (B : Type) [CommRing B] [IsLocalRing B], SH B → IsUnit (q : B) → ∀ t : Spec (CommRingCat.of B) ⟶ S, PB q i (pullback.snd c t)) →
  Eqv _ (sch.map (pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i)

theorem total (H : Hyp) (h0 : HZero) (hA : AICAcyc) (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A] (hq : IsUnit (q : A))
    {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact c]
    [QuasiSeparated c] (hZ : AICSch Z) (hS : AICSch S) : Eqv _ (sch.map c) (tw q i) := by
  obtain ⟨_, _⟩ := qcqs_of p
  obtain ⟨_, _⟩ := qcqs_of (c ≫ p)
  have : IsIntegral Z := hZ.1
  have : ConnectedSpace Z := inferInstance
  exact eqv_of H.a9 _ (h0 H q c hS this (unit_of hq p) i)
    (fun n hn => hA H q Z hZ (unit_of hq (c ≫ p)) n i hn) (fun n hn => hA H q S hS (unit_of hq p) n i hn)

theorem Fib_of (hF0 : FibClosed) (h0 : HZero) (hA : AICAcyc) : Fib := by
  intro H q i A _ _ hq Z S c p _ _ _ _ _ hZ hS hB
  have ec := total H h0 hA q i A hq c p hZ hS
  have em := hF0 H q i A hq c p hZ hS hB
  have sq : pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.fst p (cpt A)
      = pullback.fst (c ≫ p) (cpt A) ≫ c := pullback.lift_fst _ _ _
  have key : ∀ n x, pull _ (sch.map (pullback.fst (c ≫ p) (cpt A))) (tw q i) n (pull _ (sch.map c) (tw q i) n x)
      = pull _ (sch.map (pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) n
          (pull _ (sch.map (pullback.fst p (cpt A))) (tw q i) n x) := by
    intro n x
    rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, sq]
  have fe : ∀ n, (pull _ (sch.map (pullback.fst (c ≫ p) (cpt A))) (tw q i) n) ∘ (pull _ (sch.map c) (tw q i) n)
      = (pull _ (sch.map (pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) n) ∘
          (pull _ (sch.map (pullback.fst p (cpt A))) (tw q i) n) := fun n => funext (key n)
  constructor
  · intro h n
    have h1 : Function.Bijective ((pull _ (sch.map (pullback.fst (c ≫ p) (cpt A))) (tw q i) n) ∘ (pull _ (sch.map c) (tw q i) n)) :=
      (h n).comp (ec n)
    rw [fe n] at h1
    exact (Function.Bijective.of_comp_iff' (em n) _).1 h1
  · intro h n
    have h1 : Function.Bijective ((pull _ (sch.map (pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) n) ∘
        (pull _ (sch.map (pullback.fst p (cpt A))) (tw q i) n)) := (em n).comp (h n)
    rw [← fe n] at h1
    exact (Function.Bijective.of_comp_iff _ (ec n)).1 h1

end LateralTheory.E.FibPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.LineHighPf

open LateralTheory.E.t_E2Cut

def QAIC (q : ℕ) (W : Scheme.{0}) : Prop :=
  ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (I : Ideal B), AIC B ∧ IsUnit (q : B) ∧
    Nonempty (W ≅ Spec (CommRingCat.of (B ⧸ I)))

def Cover2 : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) → ∀ {Z : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z →
  ∃ (U V : Scheme.{0}) (f : U ⟶ pullback p (cpt A)) (g : V ⟶ pullback p (cpt A)),
    IsOpenImmersion f ∧ IsOpenImmersion g ∧ Set.range f ∪ Set.range g = Set.univ ∧
    QAIC q U ∧ QAIC q V ∧ QAIC q (pullback f g)

theorem acyc_of_iso {q : ℕ} {W W' : Scheme.{0}} (e : W ≅ W') (h : Acyc q (sch.obj W')) : Acyc q (sch.obj W) := by
  intro n i hn
  have := h n i hn
  refine ⟨fun x y => ?_⟩
  have hs : ∀ z : Ht q (sch.obj W) n i,
      pull _ (sch.map e.hom) (tw q i) n (pull _ (sch.map e.inv) (tw q i) n z) = z := by
    intro z
    rw [← pull_comp, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [← hs x, ← hs y, Subsingleton.elim (pull _ (sch.map e.inv) (tw q i) n x) (pull _ (sch.map e.inv) (tw q i) n y)]

theorem acyc_of_QAIC (H : Hyp) (hQ : QuotAcyc) {q : ℕ} {W : Scheme.{0}} (h : QAIC q W) : Acyc q (sch.obj W) := by
  obtain ⟨B, _, _, I, hB, hq, ⟨e⟩⟩ := h
  exact acyc_of_iso e (hQ H q B I hB hq)

theorem high_of_cover (H : Hyp) (hM : MV) {q : ℕ} {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f]
    [IsOpenImmersion g] (hc : Set.range f ∪ Set.range g = Set.univ) (hU : Acyc q (sch.obj U)) (hV : Acyc q (sch.obj V))
    (hW : Acyc q (sch.obj (pullback f g))) (i n : ℤ) (hn : 2 ≤ n) : Subsingleton (Ht q (sch.obj X) n i) := by
  obtain ⟨δ, hδ, -⟩ := hM H (ZMod q) (tw q i)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  have key : ∀ x : Ht q (sch.obj X) (m + 1) i, x = 0 := by
    intro x
    have h3 := ((hδ f g hc m).2.2 x).1
    have := hU (m + 1) i (by omega)
    have := hV (m + 1) i (by omega)
    have := hW m i (by omega)
    obtain ⟨w, hw⟩ := h3 ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    rw [← hw, Subsingleton.elim w 0, map_zero]
  exact ⟨fun x y => by rw [key x, key y]⟩

theorem LineHigh_of (hQ : QuotAcyc) (hM : MV) (hC : Cover2) : LineHigh := by
  intro H q i A _ _ hq Z p hp hZ n hn
  obtain ⟨U, V, f, g, hf, hg, hc, hU, hV, hW⟩ := hC q A hq p hp hZ
  exact high_of_cover H hM f g hc (acyc_of_QAIC H hQ hU) (acyc_of_QAIC H hQ hV) (acyc_of_QAIC H hQ hW) i n hn

theorem fibre_affine (A B : Type) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B] :
    Nonempty (pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) (cpt A) ≅
      Spec (CommRingCat.of (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)))) := by
  refine ⟨pullbackSpecIso A B (IsLocalRing.ResidueField A) ≪≫ ?_⟩
  exact Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (IsLocalRing.maximalIdeal A)).toRingEquiv).op

def Good {A : Type} [CommRing A] {W : Scheme.{0}} (w : W ⟶ Spec (CommRingCat.of A)) : Prop :=
  IsEmpty W ∨ ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra A B), AIC B ∧
    ∃ e : W ≅ Spec (CommRingCat.of B), e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = w

def ZCov : Prop := ∀ (A : Type) [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z →
  ∃ (U V : Scheme.{0}) (f : U ⟶ Z) (g : V ⟶ Z), IsOpenImmersion f ∧ IsOpenImmersion g ∧ Set.range f ∪ Set.range g = Set.univ ∧
    Good (f ≫ p) ∧ Good (g ≫ p) ∧ Good (pullback.fst f g ≫ f ≫ p)

def FibCov : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) → ∀ {Z : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)), AICSch Z → ∀ {U V : Scheme.{0}} (f : U ⟶ Z) (g : V ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g],
  Set.range f ∪ Set.range g = Set.univ → Good (f ≫ p) → Good (g ≫ p) → Good (pullback.fst f g ≫ f ≫ p) →
  ∃ (U V : Scheme.{0}) (f : U ⟶ pullback p (cpt A)) (g : V ⟶ pullback p (cpt A)),
    IsOpenImmersion f ∧ IsOpenImmersion g ∧ Set.range f ∪ Set.range g = Set.univ ∧
    QAIC q U ∧ QAIC q V ∧ QAIC q (pullback f g)

theorem Cover2_of (hZ : ZCov) (hF : FibCov) : Cover2 := by
  intro q A _ _ hq Z p hp hZA
  obtain ⟨U, V, f, g, hf, hg, hc, h1, h2, h3⟩ := hZ A p hp hZA
  exact hF q A hq p hZA f g hc h1 h2 h3

end LateralTheory.E.LineHighPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.LineOneCut

abbrev fib {A : Type} [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) : Scheme.{0} :=
  pullback p (cpt A)

def fibMap {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z) :
    fib (ι ≫ p) ⟶ fib p :=
  pullback.map (ι ≫ p) (cpt A) p (cpt A) ι (𝟙 _) (𝟙 _) (by simp) (by simp)

def Charts : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p →
  ∃ (U V : Scheme.{0}) (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z), IsOpenImmersion ι₁ ∧ IsOpenImmersion ι₂ ∧ IsAffine U ∧ IsAffine V ∧
    Set.range ι₁ ∪ Set.range ι₂ = Set.univ

def FibCover : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A))
  (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z), IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
  IsOpenImmersion (fibMap p ι₁) ∧ IsOpenImmersion (fibMap p ι₂) ∧ Set.range (fibMap p ι₁) ∪ Set.range (fibMap p ι₂) = Set.univ

def ChartAcyc : Prop := Hyp → ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] {Z U : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z), IsOpenImmersion ι → IsAffine U → AICSch Z → IsUnit (q : A) →
  Acyc q (sch.obj (fib (ι ≫ p)))

def ChartSurj : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
  ∀ {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z → ∀ (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z),
  IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → IsAffine U → IsAffine V → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
  ∀ w : Ht q (sch.obj (pullback (fibMap p ι₁) (fibMap p ι₂))) 0 i, ∃ a b,
    w = pull _ (sch.map (pullback.fst (fibMap p ι₁) (fibMap p ι₂))) (tw q i) 0 a -
      pull _ (sch.map (pullback.snd (fibMap p ι₁) (fibMap p ι₂))) (tw q i) 0 b

theorem goal_of (hMV : MV) (hC : Charts) (hF : FibCover) (hA : ChartAcyc) (hS : ChartSurj) : LineOne := by
  intro H q i A _ _ hSH hq Z p hp hZ
  obtain ⟨U, V, ι₁, ι₂, h1, h2, hU, hV, hcov⟩ := hC A p hp
  obtain ⟨hf1, hf2, hfcov⟩ := hF A p ι₁ ι₂ h1 h2 hcov
  obtain ⟨δ, hex, -⟩ := hMV H (ZMod q) (tw q i)
  have e := hex (fibMap p ι₁) (fibMap p ι₂) hfcov 0
  have aU := hA H q A p ι₁ h1 hU hZ hq
  have aV := hA H q A p ι₂ h2 hV hZ hq
  have key : ∀ x : Ht q (sch.obj (fib p)) 1 i, x = 0 := by
    intro x
    have s1 := aU 1 i one_pos
    have s2 := aV 1 i one_pos
    obtain ⟨w, hw⟩ := (e.2.2 x).1 ⟨@Subsingleton.elim _ s1 _ _, @Subsingleton.elim _ s2 _ _⟩
    obtain ⟨a, b, hab⟩ := hS H q i A hSH hq p hp hZ ι₁ ι₂ h1 h2 hU hV hcov w
    rw [← hw]
    exact (e.2.1 w).2 ⟨a, b, hab⟩
  exact ⟨fun x y => by rw [key x, key y]⟩

end LateralTheory.E.LineOneCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.QuotAcycCut

def ProdAcyc : Prop := LateralTheory.E.t_E2Cut.Hyp → ∀ (q : ℕ) (A : Type) [CommRing A] (n : ℕ) (R : Fin n → Type) [∀ k, CommRing (R k)],
  Nonempty (A ≃+* ∀ k, R k) → (∀ k, Acyc q (sp (R k))) → Acyc q (sp A)

def Hens : Prop := ∀ (q : ℕ) (B : Type) [CommRing B] [IsDomain B] (I : Ideal B), AIC B → IsUnit (q : B) →
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (_ : IsColimit c),
    (∀ j, ∃ (m : ℕ) (R : Fin m → Type) (_ : ∀ k, CommRing (R k)),
      (∀ k, IsDomain (R k) ∧ AIC (R k) ∧ IsUnit (q : R k)) ∧ Nonempty (D.obj j ≃+* ∀ k, R k)) ∧
    IsUnit (q : c.pt) ∧ ∃ K : Ideal c.pt, HenselianRing c.pt K ∧ Nonempty (B ⧸ I ≃+* c.pt ⧸ K)

theorem goal_of (hP : ProdAcyc) (hH : Hens) : LateralTheory.E.t_E2Cut.QuotAcyc := by
  intro H q B _ _ I hB hq
  obtain ⟨J, _, _, D, c, hc, hD, hqc, K, hK, ⟨e⟩⟩ := hH q B I hB hq

  have hst : ∀ j, Acyc q (sp (D.obj j)) := by
    intro j
    obtain ⟨m, R, _, hR, hiso⟩ := hD j
    refine hP H q (D.obj j) m R hiso fun k => ?_
    have := (hR k).1
    exact H.b5 q (R k) (hR k).2.1 (hR k).2.2

  have hC : Acyc q (sp c.pt) := by
    intro n i hn
    refine ⟨fun x y => ?_⟩
    have h0 : ∀ x : Ht q (sp c.pt) n i, x = 0 := by
      intro x
      obtain ⟨j, y, rfl⟩ := (H.b1 q D c hc n i).1 x hqc
      have := hst j n i hn
      rw [Subsingleton.elim y 0, map_zero]
    rw [h0 x, h0 y]

  have hCK : Acyc q (sp (c.pt ⧸ K)) := by
    intro n i hn
    have := hC n i hn
    have hE := H.e1 q c.pt K hqc i n
    exact hE.2.subsingleton
  exact hP H q (B ⧸ I) 1 (fun _ => c.pt ⧸ K) ⟨e.trans (RingEquiv.piUnique (fun _ : Fin 1 => c.pt ⧸ K)).symm⟩ fun _ => hCK

end LateralTheory.E.QuotAcycCut
end
end
