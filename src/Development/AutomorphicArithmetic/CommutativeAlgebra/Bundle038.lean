module

public import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle689
public import Development.AutomorphicArithmetic.CommutativeAlgebra.FirstChernClassEqZeroOfIsTrivialized
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle010
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle037
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle034
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
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

noncomputable section
namespace UpperTheory.Rel1

private abbrev Ac (N : ℕ) : Act := (BC N).sub ((Q1 N).comap (βC N))

private theorem isUnit_cyclotomicPeriod_deRham {N : ℕ} {A : CommRingCat.{0}} (p : Ob (Ac N) A) :
    IsUnit ((show Um N A × Um 2 A from p.pt.1).2.1 1) := by
  have h := p.pt.2
  change IsUnit ((Um.join (show Um N A × Um 2 A from p.pt.1)).1 (Fin.last N)) at h
  simpa [Um.join] using h

private def tU {N : ℕ} {A : CommRingCat.{0}} (p : Ob (Ac N) A) : Aˣ := (isUnit_cyclotomicPeriod_deRham p).unit

private def vert {E : Spc} {N : ℕ} {T : Scheme.{0}} (x : Sx (Sp E (Ac N)) 0 T) : Ob (Ac N) Γ(T, ⊤) :=
  (show ComposableArrows (Ob (Ac N) Γ(T, ⊤)) 0 from x.2).obj 0

private def ww (E : Spc) (N : ℕ) (T : Scheme.{0}) (x : Sx (Sp E (Ac N)) 0 T) : (Γ(T, ⊤))ˣ := tU (vert x)

private theorem triv1 (E : Spc) (N : ℕ) {T' T : Scheme.{0}} (g : T' ⟶ T) (x : Sx (Sp E (Ac N)) 0 T) :
    ww E N T' (x.res g) = Units.map g.appTop.hom.toMonoidHom (ww E N T x) := by
  ext
  rfl

private theorem triv2 (E : Spc) (N : ℕ) (T : Scheme.{0}) (x : Sx (Sp E (Ac N)) 1 T) :
    lineUnit (Sp.map E (incl ((Q1 N).comap (βC N))) ≫ Sp.line E (chiB N)) x * ww E N T (x.face 0) = ww E N T (x.face 1) := by
  let c : ComposableArrows (Ob (Ac N) Γ(T, ⊤)) 1 := x.2
  let f := c.map' 0 1
  have hl : lineUnit (Sp.map E (incl ((Q1 N).comap (βC N))) ≫ Sp.line E (chiB N)) x = (show (Γ(T, ⊤))ˣ × (Γ(T, ⊤))ˣ from f.1).2 := by
    have e : lineUnit (Sp.map E (incl ((Q1 N).comap (βC N))) ≫ Sp.line E (chiB N)) x =
        Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1)
          (show (Γ(T, ⊤))ˣ from (chiB N).app Γ(T, ⊤) f.1)) := rfl
    rw [e]
    ext
    simp [Matrix.GeneralLinearGroup.scalar]
    rfl
  rw [hl]
  change _ * tU (c.obj 1) = tU (c.obj 0)
  ext
  have e := congrArg (fun p => (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from p.1).2.1 1) f.2
  change ((show (Γ(T, ⊤))ˣ × (Γ(T, ⊤))ˣ from f.1).2 : Γ(T, ⊤)) * (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from (c.obj 1).pt.1).2.1 1 =
    (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from (c.obj 0).pt.1).2.1 1
  refine Eq.trans ?_ e.symm
  rfl

end UpperTheory.Rel1
end

theorem UpperTheory.chernClass_pullback_blowupFirstLocus_eq_zero :
    ∀ (q : ℕ) [NeZero q] (N : ℕ) (E : Spc), Inv q E →
        pull _ (Sp.map E (incl ((Q1 N).comap (βC N)))) _ _ (c1 q (Sp.line E (chiB N))) = 0 := by
  intro q _ N E hE
  have hX : Inv q (Sp E (BC N)) := fun U ⟨x⟩ => hE U ⟨x.1⟩
  have hY : Inv q (Sp E (UpperTheory.Rel1.Ac N)) := fun U ⟨x⟩ => hE U ⟨x.1⟩
  rw [(GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.1 _ _ hX]
  exact UpperTheory.firstChernClass_eq_zero_of_isTrivialized q _ (UpperTheory.Rel1.ww E N) hY ⟨fun g x => UpperTheory.Rel1.triv1 E N g x, UpperTheory.Rel1.triv2 E N⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

noncomputable section

namespace UpperTheory.LineUnitTrivialization

private def arr {a : Act} {E : Spc} {U : Scheme.{0}} (x : Sx (Sp E a) 1 U) : a.G.obj Γ(U, ⊤) :=
  (show ComposableArrows (Ob a Γ(U, ⊤)) 1 from x.2).hom.1

private theorem det_scalar {A : Type} [CommRing A] (u : Aˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) u) = u := by
  ext
  simp

private theorem lineUnit_line {a : Act} {E : Spc} (χ : a.G ⟶ gmF) {U : Scheme.{0}} (x : Sx (Sp E a) 1 U) :
    lineUnit (Sp.line E χ) x = (show (Γ(U, ⊤))ˣ from χ.app Γ(U, ⊤) (arr x)) :=
  det_scalar _

private theorem lineUnit_map {a b : Act} {E : Spc} (φ : Act.Hom a b) (χ : b.G ⟶ gmF) {U : Scheme.{0}} (x : Sx (Sp E a) 1 U) :
    lineUnit (Sp.map E φ ≫ Sp.line E χ) x = (show (Γ(U, ⊤))ˣ from χ.app Γ(U, ⊤) (φ.g.app Γ(U, ⊤) (arr x))) :=
  det_scalar _

private def chiM (N : ℕ) (Q : Pred (BC N)) : ((BC N).sub Q).G ⟶ gmF where
  app A := GrpCat.ofHom (MonoidHom.snd Aˣ Aˣ / MonoidHom.fst Aˣ Aˣ)
  naturality A B f := by
    ext x
    exact (map_div (Units.map (f.hom : A →* B)) x.2 x.1).symm

private theorem isUnit_um_join_of_span_castSucc_eq_whole {N : ℕ} {A : Type} [CommRing A] (x : Um N A × Um 2 A)
    (h : Ideal.span ((Um.join x).1 '' Set.range Fin.castSucc) = ⊤) : IsUnit (x.2.1 0) := by
  have h' : Ideal.span ((Um.join x).1 '' Set.range Fin.castSucc) ≤ Ideal.span {x.2.1 0} := by
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp only [Um.join, Fin.snoc_castSucc]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  rw [h, top_le_iff, Ideal.span_singleton_eq_top] at h'
  exact h'

private def sU {N : ℕ} {A : CommRingCat.{0}} (y : ((BC N).sub ((Q2 N).comap (βC N))).D.obj A) : Aˣ :=
  (isUnit_um_join_of_span_castSucc_eq_whole (A := A) y.1 y.2).unit

private def wS (N : ℕ) (E : Spc) (T : Scheme.{0}) (y : Sx (Sp E ((BC N).sub ((Q2 N).comap (βC N)))) 0 T) : (Γ(T, ⊤))ˣ :=
  sU (show ComposableArrows (Ob ((BC N).sub ((Q2 N).comap (βC N))) Γ(T, ⊤)) 0 from y.2).left.pt

private theorem triv (N : ℕ) (E : Spc) :
    IsTrivBy (Sp.line E (chiM N ((Q2 N).comap (βC N)))) (wS N E) := by
  refine ⟨?_, ?_⟩
  · intro T' T g x
    apply Units.ext
    simp only [wS, sU, IsUnit.unit_spec, Units.coe_map]
    rfl
  · intro T x
    rw [lineUnit_line]
    apply Units.ext
    have key := (show ComposableArrows (Ob ((BC N).sub ((Q2 N).comap (βC N))) Γ(T, ⊤)) 1 from x.2).hom.2
    have k2 := congrArg (fun y => (y.1.2.1 0 : Γ(T, ⊤))) key
    simp only [wS, sU, IsUnit.unit_spec]
    exact k2.symm

end UpperTheory.LineUnitTrivialization

end

open UpperTheory.LineUnitTrivialization in
theorem UpperTheory.chernClass_pullback_blowupSecondLocus_eq :
    ∀ (q : ℕ) [NeZero q] (N : ℕ) (E : Spc), Inv q E →
        pull _ (Sp.map E (incl ((Q2 N).comap (βC N)))) _ _ (c1 q (Sp.line E (chiB N))) =
          pull _ (Sp.map E (incl ((Q2 N).comap (βC N)))) _ _ (c1 q (Sp.line E (chiH N))) := by
  intro q _ N E hE
  have hI : Inv q (Sp E ((BC N).sub ((Q2 N).comap (βC N)))) := fun U ⟨x⟩ => hE U ⟨x.1⟩
  have hI' : Inv q (Sp E (BC N)) := fun U ⟨x⟩ => hE U ⟨x.1⟩
  obtain ⟨-, hpull, hadd⟩ := GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q
  rw [hpull _ _ hI', hpull _ _ hI']
  have h0 : c1 q (Sp.line E (chiM N ((Q2 N).comap (βC N)))) = 0 := UpperTheory.firstChernClass_eq_zero_of_isTrivialized q _ _ hI (triv N E)
  have hsum := hadd (Sp.map E (incl ((Q2 N).comap (βC N))) ≫ Sp.line E (chiH N))
    (Sp.line E (chiM N ((Q2 N).comap (βC N))))
    (Sp.map E (incl ((Q2 N).comap (βC N))) ≫ Sp.line E (chiB N)) hI (by
      intro U x
      rw [lineUnit_map, lineUnit_map, lineUnit_line]
      first
        | exact (mul_div_cancel _ _).symm
        | exact (mul_div_cancel_left _ _).symm
        | exact (mul_div_cancel'_right _ _).symm)
  rw [hsum, h0, add_zero]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

private theorem sec_comp {F G H : Shv ℤ} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

private theorem sec_zero {F G : Shv ℤ} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := rfl

private theorem UpperTheory.sec_map_res_comm {F G : Shv ℤ} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  show (φ.hom.app (op V)).hom ((F.obj.map g.op).hom x) =
    (G.obj.map g.op).hom ((φ.hom.app (op U)).hom x)
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

private theorem UpperTheory.injective_sec_map_of_mono {F G : Shv ℤ} (φ : F ⟶ G) [Mono φ] (U : Scheme.{0}) :
    Function.Injective (fun x : Sec F U => Sec.map φ x) := by
  have : Mono φ.hom := (sheafToPresheaf _ _).map_mono φ
  have : Mono (φ.hom.app (op U)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).mp this

private theorem UpperTheory.acy_of_isZero (Q : Scheme.{0} → Prop) (G : Shv ℤ) (hG : IsZero G) :
    Acy Q G := by
  intro P hP n _
  have hid : (𝟙 G : G ⟶ G) = 0 := hG.eq_of_src _ _
  have hsub : ∀ {U : Scheme.{0}} (x : Sec G U), x = 0 := fun {U} x => by
    calc x = Sec.map (𝟙 G) x := rfl
      _ = 0 := by rw [hid, sec_zero]
  exact UpperTheory.subsingleton_hypercohomology_free_of_supp_of_sections_vanish Q G (fun U _ => ⟨fun x y => by rw [hsub x, hsub y]⟩) P hP n

theorem UpperTheory.exists_primitive_free_of_acy_locally_exact :
    ∀ (C : Cx ℤ) (a : ℤ) [C.IsStrictlyGE a] (Q : Scheme.{0} → Prop), (∀ {V U : Scheme.{0}}, (V ⟶ U) → Q U → Q V) → (∀ s, Acy Q (C.X s)) → (∀ (U : Scheme.{0}), Q U → ∀ (n : ℤ) (b : Sec (C.X n) U), Sec.map (C.d n (n + 1)) b = 0 → Loc U fun V g => ∃ c : Sec (C.X (n - 1)) V, Sec.map (C.d (n - 1) n) c = Sec.res g b) → ∀ P : PSh, Supp Q P → ∀ (j : ℤ) (f : (free ℤ).obj P ⟶ C.X j), f ≫ C.d j (j + 1) = 0 → ∃ g : (free ℤ).obj P ⟶ C.X (j - 1), g ≫ C.d (j - 1) j = f := by
  intro C a _ Q hQ hacy hexact P hP j f hf
  have step : ∀ i : ℤ, Acy Q (kernel (C.d i (i + 1))) →
      Acy Q (kernel (C.d (i + 1) (i + 1 + 1))) ∧ ∀ P : PSh, Supp Q P →
        ∀ f : (free ℤ).obj P ⟶ kernel (C.d (i + 1) (i + 1 + 1)),
          ∃ h, h ≫ kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1))
            (C.d_comp_d _ _ _) = f := by
    intro i hi
    have w : kernel.ι (C.d i (i + 1)) ≫ kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1))
        (C.d_comp_d _ _ _) = 0 := by
      rw [← cancel_mono (kernel.ι (C.d (i + 1) (i + 1 + 1))), Category.assoc, kernel.lift_ι,
        kernel.condition, zero_comp]
    have hex : (ShortComplex.mk (kernel.ι (C.d i (i + 1)))
        (kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1)) (C.d_comp_d _ _ _)) w).Exact := by
      apply ShortComplex.exact_of_f_is_kernel
      refine KernelFork.IsLimit.ofι _ _
        (fun g' hg' => kernel.lift (C.d i (i + 1)) g' (by
          rw [← kernel.lift_ι (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1)) (C.d_comp_d _ _ _),
            ← Category.assoc, hg', zero_comp]))
        (fun g' hg' => kernel.lift_ι _ _ _)
        (fun g' hg' m hm => by
          rw [← cancel_mono (kernel.ι (C.d i (i + 1))), kernel.lift_ι]
          exact hm)
    have hloc : ∀ U : Scheme.{0}, Q U → ∀ b : Sec (kernel (C.d (i + 1) (i + 1 + 1))) U,
        Loc U fun V g => ∃ c, Sec.map (kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1))
          (C.d_comp_d _ _ _)) c = Sec.res g b := by
      intro U hU b
      have hb : Sec.map (C.d (i + 1) (i + 1 + 1))
          (Sec.map (kernel.ι (C.d (i + 1) (i + 1 + 1))) b) = 0 := by
        rw [← sec_comp, kernel.condition, sec_zero]
      have h1 := hexact U hU (i + 1) _ hb
      rw [show i + 1 - 1 = i by omega] at h1
      obtain ⟨S, hS, hSp⟩ := h1
      refine ⟨S, hS, fun V g hg => ?_⟩
      obtain ⟨c, hc⟩ := hSp V g hg
      refine ⟨c, UpperTheory.injective_sec_map_of_mono (kernel.ι (C.d (i + 1) (i + 1 + 1))) V ?_⟩
      show Sec.map _ (Sec.map _ c) = Sec.map _ (Sec.res g b)
      rw [← sec_comp, kernel.lift_ι, hc, UpperTheory.sec_map_res_comm]
    exact UpperTheory.acy_and_lift_of_locally_surjective_exact Q @hQ _ _ _ _ _ w inferInstance hex hloc hi (hacy i)
  have hAcy : ∀ i : ℤ, Acy Q (kernel (C.d i (i + 1))) := by
    intro i
    have below (n : ℤ) (hn : n < a) : Acy Q (kernel (C.d n (n + 1))) :=
      UpperTheory.acy_of_isZero Q _
        (IsZero.of_mono (kernel.ι _) (isZero_of_isStrictlyGE C a n hn))
    refine Int.inductionOn' (motive := fun n => Acy Q (kernel (C.d n (n + 1)))) i (a - 1)
      (below (a - 1) (by omega)) (fun n _ ih => (step n ih).1) ?_
    intro n hn _
    exact below (n - 1) (by omega)
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [show i + 1 - 1 = i by omega]
  obtain ⟨h, hh⟩ := (step i (hAcy i)).2 P hP (kernel.lift _ f hf)
  refine ⟨h, ?_⟩
  rw [← kernel.lift_ι (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1)) (C.d_comp_d _ _ _),
    ← Category.assoc, hh, kernel.lift_ι]
end
