module

public import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle013
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle028
public import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOfMayerVietorisCover
public import Development.EtaleCohomology.KummerTheory.InjSlice
public import Development.EtaleCohomology.WeilConjectures.Bundle002
public import Development.EtaleCohomology.EtaleSheaves.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle033
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle020
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle032
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle031
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle030
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CompLeft

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem q_of_unit {N : ℕ} {A : Type} [CommRing A] (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤)
    (h : ∃ i, IsUnit (v i)) :
    IsUnit (v (Fin.last N)) ∨ Ideal.span (v '' Set.range Fin.castSucc) = ⊤ := by
  obtain ⟨i, hi⟩ := h
  by_cases hl : i = Fin.last N
  · left
    rw [← hl]
    exact hi
  · right
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hl
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, ⟨j, rfl⟩, rfl⟩) hi

theorem UpperTheory.two_open_cover_of_map_incl :
    ∀ (R : Type) [CommRing R] (N : ℕ) (E : Spc), Cover2 R (Sp.map E (incl (Q1 N))) (Sp.map E (incl (Q2 N))) := by
  intro R _ N E
  refine UpperTheory.mayerVietoris_stackProduct_of_injective_of_locally_covered R E (incl (Q1 N)) (incl (Q2 N)) (fun A x y h => Subtype.ext h) (fun A x y h => Subtype.ext h)
    (fun A => Function.bijective_id) (fun A => Function.bijective_id) ?_
  intro T x
  obtain ⟨S, hS, hP⟩ := UpperTheory.locally_exists_isUnit_of_span_range_eq_top T (show Um (N + 1) Γ(T, ⊤) from x).1 (show Um (N + 1) Γ(T, ⊤) from x).2
  refine ⟨S, hS, fun V g hg => ?_⟩
  let w : (XC (N + 1)).D.obj Γ(V, ⊤) := (XC (N + 1)).D.map g.appTop x
  rcases q_of_unit (fun i => g.appTop.hom ((show Um (N + 1) Γ(T, ⊤) from x).1 i))
      (show Um (N + 1) Γ(V, ⊤) from (XC (N + 1)).D.map g.appTop x).2 (hP V g hg) with h | h
  · have h' : (Q1 N).P Γ(V, ⊤) w := h
    exact Or.inl ⟨⟨w, h'⟩, rfl⟩
  · have h' : (Q2 N).P Γ(V, ⊤) w := h
    exact Or.inr ⟨⟨w, h'⟩, rfl⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem isUnit_last_join {N : ℕ} {A : Type} [CommRing A] (x : Um N A × Um 2 A) (h : IsUnit (x.2.1 1)) :
    IsUnit ((Um.join x).1 (Fin.last N)) := by
  simpa [Um.join] using h

private theorem closedSubgroup_cutoff_exists {N : ℕ} {A : Type} [CommRing A] (x : Um N A × Um 2 A) (h : IsUnit (x.2.1 0)) :
    Ideal.span ((Um.join x).1 '' Set.range Fin.castSucc) = ⊤ := by
  obtain ⟨u, hu⟩ := h
  have e : (Um.join x).1 '' Set.range Fin.castSucc = (fun i => (u : A) * x.1.1 i) '' Set.univ := by
    ext y
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, trivial, by simp [Um.join, hu]⟩
    · rintro ⟨i, -, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, by simp [Um.join, hu]⟩
  rw [e, span_scale, Set.image_univ]
  exact x.1.2

theorem UpperTheory.two_open_cover_of_map_incl_comap :
    ∀ (R : Type) [CommRing R] (N : ℕ) (E : Spc),
        Cover2 R (Sp.map E (incl ((Q1 N).comap (βC N)))) (Sp.map E (incl ((Q2 N).comap (βC N)))) := by
  intro R _ N E
  refine UpperTheory.mayerVietoris_stackProduct_of_injective_of_locally_covered R E _ _ (fun A => Subtype.val_injective) (fun A => Subtype.val_injective)
    (fun A => Function.bijective_id) (fun A => Function.bijective_id) ?_
  intro T x
  obtain ⟨S, hS, hP⟩ := UpperTheory.locally_exists_isUnit_of_span_range_eq_top T (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from x).2.1
    (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from x).2.2
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨i, hi⟩ := hP V g hg
  have hx : (show Um N Γ(V, ⊤) × Um 2 Γ(V, ⊤) from (BC N).D.map g.appTop x).2.1 i =
      g.appTop.hom ((show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from x).2.1 i) := rfl
  rw [← hx] at hi
  fin_cases i
  · exact Or.inr ⟨⟨_, closedSubgroup_cutoff_exists _ hi⟩, rfl⟩
  · exact Or.inl ⟨⟨_, isUnit_last_join _ hi⟩, rfl⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.Glue

private theorem map_incl (E : Spc) {a : Act} {Q R : Pred a} (h : Q.Le R) :
    Sp.map E (inclLe h) ≫ Sp.map E (incl R) = Sp.map E (incl Q) := by
  rfl

private theorem map_inclLe (E : Spc) {a : Act} {Q R S : Pred a} (h : Q.Le R) (h' : R.Le S) (h'' : Q.Le S) :
    Sp.map E (inclLe h) ≫ Sp.map E (inclLe h') = Sp.map E (inclLe h'') := by
  rfl

private theorem comap_le {c a : Act} (π : Act.Hom c a) {Q' Q : Pred a} (h : Q'.Le Q) : (Q'.comap π).Le (Q.comap π) :=
  fun A _ hx => h A _ hx

private theorem sq (E : Spc) {c a : Act} (π : Act.Hom c a) {Q' Q : Pred a} (h : Q'.Le Q) :
    IsPullback (Sp.map E (inclLe (comap_le π h))) (Sp.map E (π.sub Q')) (Sp.map E (π.sub Q)) (Sp.map E (inclLe h)) := by
  refine UpperTheory.stackProduct_isPullback_of_actionPullback E _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_
  · intro A x y hxy
    have e : π.d.app A x.1 = y.1 := congrArg Subtype.val hxy
    have hx : Q'.P A (π.d.app A x.1) := by
      rw [e]
      exact y.2
    refine ⟨⟨x.1, hx⟩, ⟨rfl, Subtype.ext e⟩, ?_⟩
    rintro z ⟨h1, -⟩
    have e1 : z.1 = x.1 := congrArg Subtype.val h1
    exact Subtype.ext e1
  · intro A g g' hg
    exact ⟨g, ⟨rfl, hg⟩, fun z hz => hz.1⟩

private theorem sq_inf (E : Spc) {a : Act} {Q Q₁ Q₂ : Pred a} (h₁ : Q₁.Le Q) (h₂ : Q₂.Le Q) :
    IsPullback (Sp.map E (inclLe (show (Q₁.inf Q₂).Le Q₁ from fun _ _ h => h.1)))
      (Sp.map E (inclLe (show (Q₁.inf Q₂).Le Q₂ from fun _ _ h => h.2)))
      (Sp.map E (inclLe h₁)) (Sp.map E (inclLe h₂)) := by
  refine UpperTheory.stackProduct_isPullback_of_actionPullback E _ _ _ _ (fun A z => rfl) (fun A z => rfl) ?_ ?_
  · intro A x y hxy
    have hv : x.1 = y.1 := congrArg Subtype.val hxy
    refine ⟨⟨x.1, x.2, ?_⟩, ⟨rfl, ?_⟩, ?_⟩
    · rw [hv]
      exact y.2
    · apply Subtype.ext
      exact hv
    · rintro z ⟨hz, -⟩
      have hz' : z.1 = x.1 := congrArg Subtype.val hz
      apply Subtype.ext
      exact hz'
  · intro A g k hgk
    exact ⟨g, ⟨rfl, hgk⟩, fun z hz => hz.1⟩

private theorem cover_tr {R : Type} [CommRing R] {U U' V V' E : Spc} (u : U ⟶ E) (v : V ⟶ E) (u' : U' ⟶ E) (v' : V' ⟶ E)
    (e : U ⟶ U') (e' : V ⟶ V') [IsIso e] [IsIso e'] (hu : e ≫ u' = u) (hv : e' ≫ v' = v) (h : Cover2 R u v) :
    Cover2 R u' v' := by
  subst hu hv
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun n => ?_⟩
  · have : u' = inv e ≫ e ≫ u' := by simp
    rw [this]
    letI : Mono (e ≫ u') := h1
    exact mono_comp (inv e) (e ≫ u')
  · have : v' = inv e' ≫ e' ≫ v' := by simp
    rw [this]
    letI : Mono (e' ≫ v') := h2
    exact mono_comp (inv e') (e' ≫ v')
  · have h4 := h3 n
    have : biprod.desc ((free R).map ((e ≫ u').app n)) ((free R).map ((e' ≫ v').app n)) =
        biprod.map ((free R).map (e.app n)) ((free R).map (e'.app n)) ≫
          biprod.desc ((free R).map (u'.app n)) ((free R).map (v'.app n)) := by
      apply biprod.hom_ext' <;> simp
    rw [this] at h4
    exact epi_of_epi (biprod.map ((free R).map (e.app n)) ((free R).map (e'.app n))) _

private theorem cov (R : Type) [CommRing R] (E : Spc) {a : Act} {Q Q₁ Q₂ : Pred a} (h₁ : Q₁.Le Q) (h₂ : Q₂.Le Q)
    (hloc : ∀ (T : Scheme.{0}) (x : a.D.obj Γ(T, ⊤)), Q.P _ x →
      Loc T fun V g => Q₁.P _ (a.D.map g.appTop x) ∨ Q₂.P _ (a.D.map g.appTop x)) :
    Cover2 R (Sp.map E (inclLe h₁)) (Sp.map E (inclLe h₂)) := by
  refine UpperTheory.mayerVietoris_stackProduct_of_injective_of_locally_covered R E _ _ ?_ ?_ (fun _ => Function.bijective_id) (fun _ => Function.bijective_id) ?_
  · intro A x y h
    have e := congrArg (fun w : {z // Q.P A z} => w.1) h
    exact Subtype.ext e
  · intro A x y h
    have e := congrArg (fun w : {z // Q.P A z} => w.1) h
    exact Subtype.ext e
  · intro T x
    obtain ⟨S, hS, hP⟩ := hloc T x.1 x.2
    refine ⟨S, hS, fun V g hg => ?_⟩
    rcases hP V g hg with h | h
    · exact Or.inl ⟨⟨_, h⟩, rfl⟩
    · exact Or.inr ⟨⟨_, h⟩, rfl⟩

private theorem tr (q : ℕ) [NeZero q] (E : Spc) {c a : Act} (π : Act.Hom c a) {m : ℕ} (d e : Fin m → ℤ)
    (cl : ∀ j, Ht q (Sp E c) (d j) (e j)) {Q' Q : Pred a} (h : Q'.Le Q) {P B' : Spc}
    (fs : P ⟶ Sp E (c.sub (Q.comap π))) (sn : P ⟶ B') (u : P ⟶ Sp E (c.sub (Q'.comap π))) (b : B' ⟶ Sp E (a.sub Q'))
    [IsIso u] [IsIso b] (hu : u ≫ Sp.map E (inclLe (comap_le π h)) = fs) (hb : u ≫ Sp.map E (π.sub Q') = sn ≫ b)
    (L : LHQ q E π d e cl Q') :
    LH q sn d e (fun j => pull _ fs _ _ (pull _ (Sp.map E (incl (Q.comap π))) _ _ (cl j))) := by
  have h1 := UpperTheory.lerayHirsch_of_iso_square q (Sp.map E (π.sub Q')) sn u b hb d e _ L
  have h2 : (fun j => pull _ fs _ _ (pull _ (Sp.map E (incl (Q.comap π))) _ _ (cl j))) =
      fun j => pull _ u _ _ (pull _ (Sp.map E (incl (Q'.comap π))) _ _ (cl j)) := by
    funext j
    rw [← pull_comp, ← pull_comp, ← hu, Category.assoc, map_incl]
  rw [h2]
  exact h1

end UpperTheory.Glue

theorem UpperTheory.leraHirsch_of_local_cover_of_inf :
    ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E → ∀ {c a : Act} (π : Act.Hom c a) {m : ℕ} (d e : Fin m → ℤ) (cl : ∀ j, Ht q (Sp E c) (d j) (e j))
        (Q Q₁ Q₂ : Pred a) (_ : Q₁.Le Q) (_ : Q₂.Le Q),
        (∀ (T : Scheme.{0}) (x : a.D.obj Γ(T, ⊤)), Q.P _ x → Loc T fun V g => Q₁.P _ (a.D.map g.appTop x) ∨ Q₂.P _ (a.D.map g.appTop x)) →
        LHQ q E π d e cl Q₁ → LHQ q E π d e cl Q₂ → LHQ q E π d e cl (Q₁.inf Q₂) → LHQ q E π d e cl Q := by
  intro q _ E _ c a π m d e cl Q Q₁ Q₂ h₁ h₂ hloc L₁ L₂ L₁₂
  have hinf : (Q₁.inf Q₂).Le Q := fun A x hx => h₁ A x hx.1
  have sq1 := UpperTheory.Glue.sq E π h₁
  have sq2 := UpperTheory.Glue.sq E π h₂
  have sqi := UpperTheory.Glue.sq_inf E h₁ h₂
  letI := sq1.hasPullback
  letI := sq2.hasPullback
  letI := sqi.hasPullback
  have hloc' : ∀ (T : Scheme.{0}) (x : c.D.obj Γ(T, ⊤)), (Q.comap π).P _ x →
      Loc T fun V g => (Q₁.comap π).P _ (c.D.map g.appTop x) ∨ (Q₂.comap π).P _ (c.D.map g.appTop x) := by
    intro T x hx
    obtain ⟨S, hS, hP⟩ := hloc T _ hx
    refine ⟨S, hS, fun V g hg => ?_⟩
    show Q₁.P _ _ ∨ Q₂.P _ _
    rw [NatTrans.naturality_apply]
    exact hP V g hg
  have sq' : IsPullback (Sp.map E (inclLe (UpperTheory.Glue.comap_le π hinf)))
      (Sp.map E (π.sub (Q₁.inf Q₂)) ≫ sqi.isoPullback.hom) (Sp.map E (π.sub Q))
      (pullback.fst (Sp.map E (inclLe h₁)) (Sp.map E (inclLe h₂)) ≫ Sp.map E (inclLe h₁)) := by
    refine (UpperTheory.Glue.sq E π hinf).of_iso (Iso.refl _) (Iso.refl _) sqi.isoPullback (Iso.refl _)
      (by simp) (by simp) (by simp) ?_
    rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, IsPullback.isoPullback_hom_fst,
      UpperTheory.Glue.map_inclLe]
  letI := sq'.hasPullback
  refine UpperTheory.lerayHirsch_of_mayerVietoris_cover q (Sp.map E (inclLe h₁)) (Sp.map E (inclLe h₂)) (Sp.map E (π.sub Q)) d e _
    (UpperTheory.Glue.cov _ E h₁ h₂ hloc) ?_ ?_ ?_ ?_
  · exact UpperTheory.Glue.cover_tr (Sp.map E (inclLe (UpperTheory.Glue.comap_le π h₁)))
      (Sp.map E (inclLe (UpperTheory.Glue.comap_le π h₂))) _ _ sq1.isoPullback.hom sq2.isoPullback.hom
      sq1.isoPullback_hom_fst sq2.isoPullback_hom_fst
      (UpperTheory.Glue.cov _ E (UpperTheory.Glue.comap_le π h₁) (UpperTheory.Glue.comap_le π h₂) hloc')
  · exact UpperTheory.Glue.tr q E π d e cl h₁ _ _ sq1.isoPullback.inv (𝟙 _) sq1.isoPullback_inv_fst
      (by rw [sq1.isoPullback_inv_snd, Category.comp_id]) L₁
  · exact UpperTheory.Glue.tr q E π d e cl h₂ _ _ sq2.isoPullback.inv (𝟙 _) sq2.isoPullback_inv_fst
      (by rw [sq2.isoPullback_inv_snd, Category.comp_id]) L₂
  · exact UpperTheory.Glue.tr q E π d e cl hinf _ _ sq'.isoPullback.inv sqi.isoPullback.inv
      sq'.isoPullback_inv_fst
      (by rw [← sq'.isoPullback_inv_snd, Category.assoc, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]) L₁₂
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

noncomputable section

private theorem rmap_comp' (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (c : f' ≫ e = u ≫ f) (c' : f'' ≫ e' = u' ≫ f') :
    rmap R f' f'' u' e' c' ≫ rmap R f f' u e c =
      rmap R f f'' (u' ≫ u) (e' ≫ e) (by rw [← Category.assoc, c', Category.assoc, c, Category.assoc]) := by
  simp only [rmap, Functor.map_comp]
  exact (mappingCone.map_comp _ _ _ _ _ _ _ _ _).symm

private theorem rmap_congr' (R : Type) [CommRing R] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E')
    {u u₂ : U' ⟶ U} {e e₂ : E' ⟶ E} (c : f' ≫ e = u ≫ f) (c₂ : f' ≫ e₂ = u₂ ≫ f) (hu : u = u₂) (he : e = e₂) :
    rmap R f f' u e c = rmap R f f' u₂ e₂ c₂ := by
  subst hu he
  rfl

private def coneM {B : Scheme.{0}} {G₁ G₂ G₁' G₂' : B.Etale ⥤ Scheme.{0}} {F : G₁ ⟶ G₂} {F' : G₁' ⟶ G₂'}
    (u : G₁' ⟶ G₁) (e : G₂' ⟶ G₂) (w : F' ≫ e = u ≫ F) (q : ℕ) : coneF F' q ⟶ coneF F q where
  app U := rmap (ZMod q) (sch.map (F.app U)) (sch.map (F'.app U)) (sch.map (u.app U)) (sch.map (e.app U))
    (by rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg sch.map (NatTrans.congr_app w U))
  naturality U V a := by
    have cc : ∀ U, sch.map (F'.app U) ≫ sch.map (e.app U) = sch.map (u.app U) ≫ sch.map (F.app U) := fun U => by
      rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg sch.map (NatTrans.congr_app w U)
    have c1 : sch.map (F'.app U) ≫ sch.map (G₂'.map a) = sch.map (G₁'.map a) ≫ sch.map (F'.app V) := by
      rw [← Functor.map_comp, ← Functor.map_comp, F'.naturality]
    have c2 : sch.map (F.app U) ≫ sch.map (G₂.map a) = sch.map (G₁.map a) ≫ sch.map (F.app V) := by
      rw [← Functor.map_comp, ← Functor.map_comp, F.naturality]
    exact (rmap_comp' _ _ _ _ _ _ _ _ (cc V) c1).trans ((rmap_congr' _ _ _ _ _
      (by rw [← Functor.map_comp, ← Functor.map_comp, u.naturality])
      (by rw [← Functor.map_comp, ← Functor.map_comp, e.naturality])).trans
      (rmap_comp' _ _ _ _ _ _ _ _ c2 (cc U)).symm)

private theorem pm_y {B Y Y' U V : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) (x : U ⟶ B) (y : V ⟶ B) (a : U ⟶ V)
    (h : x = a ≫ y) (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈) :
    pullback.map (g ≫ p) x (g ≫ p) y (𝟙 Y') a (𝟙 B) c₁ c₂ ≫ pullback.map (g ≫ p) y p y g (𝟙 V) (𝟙 B) c₃ c₄ =
      pullback.map (g ≫ p) x p x g (𝟙 U) (𝟙 B) c₅ c₆ ≫ pullback.map p x p y (𝟙 Y) a (𝟙 B) c₇ c₈ := by
  apply pullback.hom_ext <;> simp [pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, h]

private theorem pm_w {A₁ A₂ A₃ A₄ W B : Scheme.{0}} (s₁ : A₁ ⟶ B) (s₂ : A₂ ⟶ B) (s₃ : A₃ ⟶ B) (s₄ : A₄ ⟶ B) (ι : W ⟶ B)
    (r : A₁ ⟶ A₂) (m₂ : A₂ ⟶ A₄) (m₁ : A₁ ⟶ A₃) (r' : A₃ ⟶ A₄) (h : r ≫ m₂ = m₁ ≫ r') (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈) :
    pullback.map s₁ ι s₂ ι r (𝟙 W) (𝟙 B) c₁ c₂ ≫ pullback.map s₂ ι s₄ ι m₂ (𝟙 W) (𝟙 B) c₃ c₄ =
      pullback.map s₁ ι s₃ ι m₁ (𝟙 W) (𝟙 B) c₅ c₆ ≫ pullback.map s₃ ι s₄ ι r' (𝟙 W) (𝟙 B) c₇ c₈ := by
  apply pullback.hom_ext
  · simp [pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, h]
  · simp [pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

private theorem mY_nat {B Y Y' : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) {U V : B.Etale} (a : U ⟶ V) :
    resY (g ≫ p) a ≫ mY p g V = mY p g U ≫ resY p a :=
  pm_y p g U.hom V.hom a.left (by simpa using a.w.symm) _ _ _ _ _ _ _ _

private theorem bY_nat {B Y : Scheme.{0}} (p : Y ⟶ B) {U V : B.Etale} (a : U ⟶ V) :
    resY p a ≫ toBY p V = toBY p U ≫ a.left :=
  pullback.lift_snd _ _ _

private theorem mW_nat {B Y Y' W : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) (ι : W ⟶ B) {U V : B.Etale} (a : U ⟶ V) :
    resYW (g ≫ p) ι a ≫ mW p g ι V = mW p g ι U ≫ resYW p ι a :=
  pm_w _ _ _ _ ι _ _ _ _ (mY_nat p g a) _ _ _ _ _ _ _ _

private theorem bW_nat {B Y W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) {U V : B.Etale} (a : U ⟶ V) :
    resYW p ι a ≫ toBW p ι V = toBW p ι U ≫ resBW ι a :=
  pm_w _ _ _ _ ι _ _ _ _ (bY_nat p a) _ _ _ _ _ _ _ _

private def mYn {B Y Y' : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) : gY (g ≫ p) ⟶ gY p where
  app U := mY p g U
  naturality _ _ a := mY_nat p g a

private def bY {B Y : Scheme.{0}} (p : Y ⟶ B) : gY p ⟶ gB B where
  app U := toBY p U
  naturality _ _ a := bY_nat p a

private def mWn {B Y Y' W : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) (ι : W ⟶ B) : gYW (g ≫ p) ι ⟶ gYW p ι where
  app U := mW p g ι U
  naturality _ _ a := mW_nat p g ι a

private def bW {B Y W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) : gYW p ι ⟶ gBW ι where
  app U := toBW p ι U
  naturality _ _ a := bW_nat p ι a

theorem UpperTheory.leafLocalization_of_injective_slice_of_restriction_injective :
    LateralTheory.KummerTheory.InjSlice → LateralTheory.EWeil.AcycPf.RestrInj → LateralTheory.E.LeafConsPf.LeafLoc := by
  intro hS hR q _ i B W Y0 Y1 Y2 ι _ p g1 g2
  obtain ⟨-, hinj, hGE, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q i)
  have key : ∀ {G₁ G₂ : B.Etale ⥤ Scheme.{0}} (F : G₁ ⟶ G₂), Good (G₁ ⋙ yoneda ⋙ free (ZMod q)) →
      Good (G₂ ⋙ yoneda ⋙ free (ZMod q)) →
      ∃ h, (TC (coneF F q) (res (ZMod q) (tw q i)) h).IsKInjective := by
    intro G₁ G₂ F h₁ h₂
    obtain ⟨a, b⟩ := UpperTheory.homAcyclic_mappingCone_chains_of_homAcyclic_free q F h₁ h₂
    have c := UpperTheory.totalHomPresheaf_isSheaf_injective_of_homAcyclic q (coneF F q) (res (ZMod q) (tw q i)) a hinj
    choose h hi using c
    refine ⟨h, UpperTheory.totalHomComplex_isKInjective_of_bounded_injective q _ _ h hi b fun n hn => ?_⟩
    exact (res (ZMod q) (tw q i)).isZero_of_isStrictlyGE 0 n hn
  have gy : ∀ {Y : Scheme.{0}} (P : Y ⟶ B), Good (gY P ⋙ yoneda ⋙ free (ZMod q)) :=
    fun P => UpperTheory.homAcyclic_free_pullback_yoneda_of_injective_restriction hS hR q P
  have tr : ∀ {G G' : B.Etale ⥤ Scheme.{0}}, Nonempty (G ≅ G') → Good (G' ⋙ yoneda ⋙ free (ZMod q)) →
      Good (G ⋙ yoneda ⋙ free (ZMod q)) := by
    rintro G G' ⟨e⟩ h
    exact (UpperTheory.homAcyclic_of_iso_of_isZero_of_biproduct q B).1 _ _ ⟨Functor.isoWhiskerRight e.symm _⟩ h
  have gyw : ∀ {Y : Scheme.{0}} (P : Y ⟶ B), Good (gYW P ι ⋙ yoneda ⋙ free (ZMod q)) :=
    fun P => tr (UpperTheory.nonempty_iso_relativeEtaleFamily_baseChange P ι).1 (gy _)
  have gb : Good (gB B ⋙ yoneda ⋙ free (ZMod q)) := tr (UpperTheory.nonempty_iso_relativeEtaleFamily_baseChange p ι).2.1 (gy _)
  have gbw : Good (gBW ι ⋙ yoneda ⋙ free (ZMod q)) := tr (UpperTheory.nonempty_iso_relativeEtaleFamily_baseChange p ι).2.2 (gy _)
  obtain ⟨h0, k0⟩ := key (fY p ι) (gyw _) (gy _)
  obtain ⟨h1, k1⟩ := key (fY (g1 ≫ p) ι) (gyw _) (gy _)
  obtain ⟨h2, k2⟩ := key (fY (g2 ≫ g1 ≫ p) ι) (gyw _) (gy _)
  obtain ⟨hL, kL⟩ := key (fB ι) gbw gb
  obtain ⟨l, lb, ln, lm⟩ := UpperTheory.exists_cohomologyClass_to_derivedHom_bijective_of_kInjective q B (res (ZMod q) (tw q i))
  have w1 : fY (g1 ≫ p) ι ≫ mYn p g1 = mWn p g1 ι ≫ fY p ι :=
    NatTrans.ext (funext fun U => (pullback.lift_fst _ _ _).symm)
  have w2 : fY (g2 ≫ g1 ≫ p) ι ≫ mYn (g1 ≫ p) g2 = mWn (g1 ≫ p) g2 ι ≫ fY (g1 ≫ p) ι :=
    NatTrans.ext (funext fun U => (pullback.lift_fst _ _ _).symm)
  have w3 : fY (g2 ≫ g1 ≫ p) ι ≫ bY (g2 ≫ g1 ≫ p) = bW (g2 ≫ g1 ≫ p) ι ≫ fB ι :=
    NatTrans.ext (funext fun U => (pullback.lift_fst _ _ _).symm)
  refine ⟨DerivedCategory.Q.obj (TC _ _ h0), DerivedCategory.Q.obj (TC _ _ h1), DerivedCategory.Q.obj (TC _ _ h2),
    DerivedCategory.Q.obj (TC _ _ hL),
    DerivedCategory.Q.map (TM (coneM _ _ w1 q) _ h0 h1), DerivedCategory.Q.map (TM (coneM _ _ w2 q) _ h1 h2),
    DerivedCategory.Q.map (TM (coneM _ _ w3 q) _ hL h2),
    fun U n => l _ h0 U n, fun U n => l _ h1 U n, fun U n => l _ h2 U n, fun U n => l _ hL U n,
    ⟨fun U n => (lb _ h0 k0 U n), fun U U' a n y => ln _ h0 U U' a n y⟩,
    ⟨fun U n => (lb _ h1 k1 U n), fun U U' a n y => ln _ h1 U U' a n y⟩,
    ⟨fun U n => (lb _ h2 k2 U n), fun U U' a n y => ln _ h2 U U' a n y⟩,
    ⟨fun U n => (lb _ hL kL U n), fun U U' a n y => ln _ hL U U' a n y⟩,
    fun U n y => lm _ _ h0 h1 (coneM _ _ w1 q) U n y,
    fun U n y => lm _ _ h1 h2 (coneM _ _ w2 q) U n y,
    fun U n y => lm _ _ hL h2 (coneM _ _ w3 q) U n y⟩

end
end
