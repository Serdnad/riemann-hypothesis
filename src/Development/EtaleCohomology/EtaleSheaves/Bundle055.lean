module

public import Development.EtaleCohomology.EtaleSheaves.Bundle044
public import Development.EtaleCohomology.EtaleSheaves.Bundle028
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Development.EtaleCohomology.EtaleSheaves.HalfDegreeVanishing.SecondBlockUnimodularLocusInclusionMono
public import Development.EtaleCohomology.EtaleSheaves.KernelLocalization.RangeOfBd
public import Development.EtaleCohomology.EtaleSheaves.Bundle012
public import Development.EtaleCohomology.EtaleSheaves.LZProperCut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.EtaleCohomology.EtaleSheaves.Bundle037
import Development.EtaleCohomology.EtaleSheaves.Bundle022

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.SpecLimPf
open LateralTheory.E.LevelsGenPf

def gam {T : Scheme.{0}} {R : Type} [CommRing R] (x : T ⟶ Spec (CommRingCat.of R)) : R →+* Γ(T, ⊤) :=
  ((ΓSpec.adjunction.homEquiv T (op (CommRingCat.of R))).symm x).unop.hom

def uns {T : Scheme.{0}} {R : Type} [CommRing R] (h : R →+* Γ(T, ⊤)) : T ⟶ Spec (CommRingCat.of R) :=
  ΓSpec.adjunction.homEquiv T (op (CommRingCat.of R)) (CommRingCat.ofHom h).op

theorem gam_uns {T : Scheme.{0}} {R : Type} [CommRing R] (h : R →+* Γ(T, ⊤)) : gam (uns h) = h := by
  have e := (ΓSpec.adjunction.homEquiv T (op (CommRingCat.of R))).symm_apply_apply (CommRingCat.ofHom h).op
  simp only [gam, uns]
  erw [e]
  rfl

theorem gam_inj {T : Scheme.{0}} {R : Type} [CommRing R] {x y : T ⟶ Spec (CommRingCat.of R)}
    (h : gam x = gam y) : x = y := by
  apply (ΓSpec.adjunction.homEquiv T (op (CommRingCat.of R))).symm.injective
  apply Opposite.unop_injective
  exact CommRingCat.hom_ext h

theorem gam_comp {T : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (x : T ⟶ Spec (CommRingCat.of S)) : gam (x ≫ Spec.map (CommRingCat.ofHom f)) = (gam x).comp f := by
  have := ΓSpec.adjunction.homEquiv_naturality_right_symm x (CommRingCat.ofHom f).op
  simp only [gam]
  erw [this]
  rfl

theorem SpecLim_of : SpecLim := by
  intro A A' B _ _ _ φ χ n l hl hcop
  refine ⟨evaluationJointlyReflectsLimits _ fun k => ?_⟩
  obtain ⟨T⟩ := k

  let F := WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A)))
      (fun _ : Fin (n + 1) => yoneda.obj (Spec (CommRingCat.of A'))) (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom φ)))
  have key : ∀ (s : Cone (F ⋙ (evaluation _ _).obj (op T))) (p : s.pt),
      ∀ i, (gam (s.π.app (some i) p)).comp φ = gam (s.π.app none p) := by
    intro s p i
    have h : (s.π.app none p : T ⟶ Spec (CommRingCat.of A)) =
        (s.π.app (some i) p : T ⟶ Spec (CommRingCat.of A')) ≫ Spec.map (CommRingCat.ofHom φ) :=
      (types_congr_hom (s.w (WidePullbackShape.Hom.term i)) p).symm
    rw [h]
    exact (gam_comp φ _).symm
  refine IsLimit.mk (fun s => TypeCat.ofHom fun p => uns (hcop Γ(T, ⊤) (fun i => gam (s.π.app (some i) p)) (gam (s.π.app none p))
      (key s p)).exists.choose) ?_ ?_
  · intro s j
    ext p
    have hs := (hcop Γ(T, ⊤) (fun i => gam (s.π.app (some i) p)) (gam (s.π.app none p)) (key s p)).exists.choose_spec
    rcases j with _ | i
    · apply gam_inj
      change gam (uns _ ≫ Spec.map (CommRingCat.ofHom χ)) = _
      rw [gam_comp, gam_uns, hs.2]
      rfl
    · apply gam_inj
      change gam (uns _ ≫ Spec.map (CommRingCat.ofHom (l i))) = _
      rw [gam_comp, gam_uns, hs.1 i]
      rfl
  · intro s m hm
    ext p
    have H := hcop Γ(T, ⊤) (fun i => gam (s.π.app (some i) p)) (gam (s.π.app none p)) (key s p)
    change (m p : T ⟶ Spec (CommRingCat.of B)) = uns _
    apply gam_inj
    rw [gam_uns]
    refine H.unique ⟨fun i => ?_, ?_⟩ H.exists.choose_spec
    · have e : (s.π.app (some i) p : T ⟶ Spec (CommRingCat.of A')) =
          (m p : T ⟶ Spec (CommRingCat.of B)) ≫ Spec.map (CommRingCat.ofHom (l i)) :=
        (types_congr_hom (hm (some i)) p).symm
      change _ = gam (s.π.app (some i) p)
      rw [e]
      exact (gam_comp _ _).symm
    · have e : (s.π.app none p : T ⟶ Spec (CommRingCat.of A)) =
          (m p : T ⟶ Spec (CommRingCat.of B)) ≫ Spec.map (CommRingCat.ofHom χ) :=
        (types_congr_hom (hm none) p).symm
      rw [e]
      exact (gam_comp _ _).symm

end LateralTheory.E.SpecLimPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut

namespace LateralTheory.E.StandardEtaleChartsMultivariableHensel


attribute [local instance] MvPolynomial.gradedAlgebra in
def stdOpen (i : Fin 2) : P1.Opens := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (MvPolynomial.X i)

def StdPair {A : Type} [CommRing A] {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z) : Prop :=
  ∃ (L : Scheme.{0}) (u : Z ⟶ L) (l : L ⟶ Spec (CommRingCat.of A)) (f : L ⟶ P1), IsIntegralHom u ∧ IsProper l ∧
    IsPullback f l (terminal.from P1) (terminal.from _) ∧ u ≫ l = p ∧
    Set.range ι₁ = ((u ≫ f) ⁻¹ᵁ stdOpen 0 : Set Z) ∧ Set.range ι₂ = ((u ≫ f) ⁻¹ᵁ stdOpen 1 : Set Z)

def StdCharts : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p →
  ∃ (U V : Scheme.{0}) (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z), IsOpenImmersion ι₁ ∧ IsOpenImmersion ι₂ ∧ IsAffine U ∧ IsAffine V ∧
    Set.range ι₁ ∪ Set.range ι₂ = Set.univ ∧ StdPair p ι₁ ι₂

def Heart : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
  ∀ {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z → ∀ (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z),
  IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → IsAffine U → IsAffine V → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
  StdPair p ι₁ ι₂ →
  ∀ g : LocallyConstant ↥(pullback (fibMap p ι₁) (fibMap p ι₂)) (ZMod q),
    ∃ (a : LocallyConstant ↥(fib (ι₁ ≫ p)) (ZMod q)) (b : LocallyConstant ↥(fib (ι₂ ≫ p)) (ZMod q)),
      g = a.comap (pullback.fst (fibMap p ι₁) (fibMap p ι₂)).base.hom -
        b.comap (pullback.snd (fibMap p ι₁) (fibMap p ι₂)).base.hom

theorem chartSurj (hR : LateralTheory.E.ChartSurjCut.Root) (hL : LateralTheory.E.ChartSurjCut.LCIso) (hT : Heart) :
    ∀ (H : Hyp) (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
    ∀ {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z → ∀ (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z),
    IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → IsAffine U → IsAffine V → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
    StdPair p ι₁ ι₂ →
    ∀ w : Ht q (sch.obj (pullback (fibMap p ι₁) (fibMap p ι₂))) 0 i, ∃ a b,
      w = pull _ (sch.map (pullback.fst (fibMap p ι₁) (fibMap p ι₂))) (tw q i) 0 a -
        pull _ (sch.map (pullback.snd (fibMap p ι₁) (fibMap p ι₂))) (tw q i) 0 b := by
  unfold LateralTheory.E.ChartSurjCut.Root at hR
  unfold LateralTheory.E.ChartSurjCut.LCIso at hL
  intro H q i A _ _ hSH hq Z U V p hp hZ ι₁ ι₂ h1 h2 hU hV hcov hstd w
  obtain ⟨ζ⟩ := hR q A p hZ hq
  obtain ⟨e, he⟩ := hL H q i Z ζ
  have k1 : fibMap p ι₁ ≫ pullback.fst p (cpt A) = pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ := by rw [fibMap]; exact pullback.lift_fst _ _ _
  have k2 : fibMap p ι₂ ≫ pullback.fst p (cpt A) = pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂ := by rw [fibMap]; exact pullback.lift_fst _ _ _
  have eq : pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂ =
      pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ := by
    rw [← k2, ← k1, ← Category.assoc, ← pullback.condition, Category.assoc]
  obtain ⟨a, b, hab⟩ := hT q A hSH hq p hp hZ ι₁ ι₂ h1 h2 hU hV hcov hstd
    ((e _ (pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁)).symm w)
  refine ⟨e _ (pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁) a, e _ (pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂) b, ?_⟩
  rw [he _ _ (pullback.fst (fibMap p ι₁) (fibMap p ι₂)) rfl, he _ _ (pullback.snd (fibMap p ι₁) (fibMap p ι₂)) eq,
    ← map_sub, ← hab, AddEquiv.apply_symm_apply]

theorem goal_of (hMV : MV) (hC : StdCharts) (hF : LateralTheory.E.LineOneCut.FibCover) (hA : ChartAcyc)
    (hR : LateralTheory.E.ChartSurjCut.Root) (hL : LateralTheory.E.ChartSurjCut.LCIso) (hT : Heart) : LineOne := by
  intro H q i A _ _ hSH hq Z p hp hZ
  obtain ⟨U, V, ι₁, ι₂, h1, h2, hU, hV, hcov, hstd⟩ := hC A p hp
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
    obtain ⟨a, b, hab⟩ := chartSurj hR hL hT H q i A hSH hq p hp hZ ι₁ ι₂ h1 h2 hU hV hcov hstd w
    rw [← hw]
    exact (e.2.1 w).2 ⟨a, b, hab⟩
  exact ⟨fun x y => by rw [key x, key y]⟩

end LateralTheory.E.StandardEtaleChartsMultivariableHensel
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.D2 LateralTheory.E.LeafGeomPf

namespace LateralTheory.E.HalfDegreeVanishing

theorem um_hom_val {N : ℕ} {A : Type} [CommRing A] {v w v' w' : Um N A} (hv : v = v') (hw : w = w') (p : v' ⟶ w') :
    (eqToHom hv ≫ p ≫ eqToHom hw.symm).1 = p.1 := by
  subst hv hw; simp

theorem um_functor_ext {N n : ℕ} {A : Type} [CommRing A] (F G : Fin (n + 1) ⥤ Um N A)
    (ho : ∀ i, (F.obj i).1 = (G.obj i).1) (hm : ∀ {i j : Fin (n + 1)} (f : i ⟶ j), (F.map f).1 = (G.map f).1) : F = G := by
  refine CategoryTheory.Functor.ext (fun i => Subtype.ext (ho i)) (fun i j f => ?_)
  apply Subtype.ext
  exact (hm f).trans (um_hom_val (Subtype.ext (ho i)) (Subtype.ext (ho j)) (G.map f)).symm

variable {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b))

theorem arrow_eq {n : ℕ} {X : Scheme.{0}} (x : Sx (PB (bsumOf V W)) n X) {i j : Fin (n + 1)} (f : i ⟶ j) :
    (show GL (Fin b) (Scheme.Γ.obj (op X)) from (pw W (pe V W x)).map f).val.mulVec (wb (a := a) ((pv V W x).obj i).1) =
      (((pv V W x).map f).1.2 : Scheme.Γ.obj (op X)) • wb (a := a) ((pv V W x).obj j).1 := by
  have e := ((pv V W x).map f).2
  rw [cond] at e
  have e2 := congrArg (wb (a := a)) e
  rw [wb_mulVec] at e2
  exact e2

def gfun {n : ℕ} {X : Scheme.{0}} (x : Sx (PB (bsumOf V W)) n X) (hx : AllSec V W x) :
    Fin (n + 1) ⥤ Um b (Scheme.Γ.obj (op X)) where
  obj i := ⟨wb (a := a) ((pv V W x).obj i).1, hx i⟩
  map {i j} f := ⟨((pw W (pe V W x)).map f, ((pv V W x).map f).1.2), arrow_eq V W x f⟩
  map_id i := Subtype.ext (Prod.ext ((pw W (pe V W x)).map_id i) (congrArg (fun p => p.1.2) ((pv V W x).map_id i)))
  map_comp f g := Subtype.ext (Prod.ext ((pw W (pe V W x)).map_comp f g) (congrArg (fun p => p.1.2) ((pv V W x).map_comp f g)))

theorem pe_res {n : ℕ} {X Y : Scheme.{0}} (k : Y ⟶ X) (x : Sx (PB (bsumOf V W)) n X) :
    pe V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x) = (E.obj (op (SimplexCategory.mk n))).map k.op (pe V W x) :=
  NatTrans.naturality_apply
    ((pullback.fst (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))) k.op x

theorem pw_res {n : ℕ} {X Y : Scheme.{0}} (k : Y ⟶ X) (e : Sx E n X) {i j : Fin (n + 1)} (f : i ⟶ j) :
    (show GL (Fin b) (Scheme.Γ.obj (op Y)) from (pw W ((E.obj (op (SimplexCategory.mk n))).map k.op e)).map f) =
      Matrix.GeneralLinearGroup.map (Scheme.Γ.map k.op).hom (show GL (Fin b) (Scheme.Γ.obj (op X)) from (pw W e).map f) :=
  eq_of_heq (Functor.hcongr_hom (NatTrans.naturality_apply (W.app (op (SimplexCategory.mk n))) k.op e) f)

end LateralTheory.E.HalfDegreeVanishing
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf
open LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.KernelLocalization

abbrev PP (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) := pull (ZMod q) (sch.map (Spec.map f)) (tw q i) n
theorem PP_comp (q : ℕ) (i n : ℤ) {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (x) :
    PP q i n (f ≫ g) x = PP q i n g (PP q i n f x) := by
  rw [PP, Spec.map_comp, Functor.map_comp, pull_comp]
theorem unit_of {q : ℕ} {A B : CommRingCat.{0}} (f : A ⟶ B) (h : IsUnit (q : A)) : IsUnit (q : B) := by
  simpa using h.map f.hom

abbrev HR (q : ℕ) (i n : ℤ) {D Y : CommRingCat.{0}} (φ : D ⟶ Y) := Hrel (ZMod q) (sch.map (Spec.map φ)) (tw q i) n

abbrev RP (q : ℕ) (i n : ℤ) {D Y E Z : CommRingCat.{0}} (φ : D ⟶ Y) (e : D ⟶ E) (u : Y ⟶ Z) (ψ : E ⟶ Z)
    (h : φ ≫ u = e ≫ ψ) : HR q i n φ →+ HR q i n ψ :=
  rpl q i (Spec.map φ) (Spec.map ψ) (Spec.map u) (Spec.map e) (by rw [← Spec.map_comp, ← Spec.map_comp, h]) n

theorem RP_comp (q : ℕ) (i n : ℤ) {D Y E Z E' Z' : CommRingCat.{0}} (φ : D ⟶ Y) (e : D ⟶ E) (u : Y ⟶ Z) (ψ : E ⟶ Z)
    (h : φ ≫ u = e ≫ ψ) (e' : E ⟶ E') (u' : Z ⟶ Z') (ψ' : E' ⟶ Z') (h' : ψ ≫ u' = e' ≫ ψ') (e2 : D ⟶ E') (u2 : Y ⟶ Z')
    (h2 : φ ≫ u2 = e2 ≫ ψ') (he : e ≫ e' = e2) (hu : u ≫ u' = u2) (z : HR q i n φ) :
    RP q i n φ e2 u2 ψ' h2 z = RP q i n ψ e' u' ψ' h' (RP q i n φ e u ψ h z) :=
  rpull_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by rw [← hu, Spec.map_comp, Functor.map_comp])
    (by rw [← he, Spec.map_comp, Functor.map_comp]) n z

theorem RP_bd (q : ℕ) (i m n : ℤ) (hm : 1 + m = n) {D Y E Z : CommRingCat.{0}} (φ : D ⟶ Y) (e : D ⟶ E) (u : Y ⟶ Z)
    (ψ : E ⟶ Z) (h : φ ≫ u = e ≫ ψ) (y) :
    RP q i n φ e u ψ h (bd _ _ _ m n hm y) = bd _ _ _ m n hm (PP q i m u y) := rpull_bd ..

theorem fgt_RP (q : ℕ) (i n : ℤ) {D Y E Z : CommRingCat.{0}} (φ : D ⟶ Y) (e : D ⟶ E) (u : Y ⟶ Z)
    (ψ : E ⟶ Z) (h : φ ≫ u = e ≫ ψ) (z : HR q i n φ) :
    fgt _ _ _ n (RP q i n φ e u ψ h z) = PP q i n e (fgt _ _ _ n z) := relNat _ _ _ _ _ _ _ n z

theorem pushColim {A Y C Y' : CommRingCat.{0}} (φ : A ⟶ Y) (c : A ⟶ C) (w : Y ⟶ Y') (φ' : C ⟶ Y')
    (hpo : IsPushout φ c w φ') {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
    (t : (Functor.const J).obj A ⟶ D) (s : D ⟶ (Functor.const J).obj C) (hc : IsColimit (Cocone.mk _ s))
    (ht : ∀ j, t.app j ≫ s.app j = c) :
    ∃ (E : J ⥤ CommRingCat.{0}) (p : D ⟶ E) (e : E ⟶ (Functor.const J).obj Y') (v : ∀ j, Y ⟶ E.obj j),
      Nonempty (IsColimit (Cocone.mk _ e)) ∧ (∀ j, IsPushout φ (t.app j) (v j) (p.app j)) ∧
      (∀ j, p.app j ≫ e.app j = s.app j ≫ φ') ∧ ∀ j k (f : j ⟶ k), v j ≫ E.map f = v k := by
  have : IsConnected J := IsFiltered.isConnected J
  let F : J ⥤ Under A := D.toUnder A (fun j => t.app j) (fun {j k} g => by
    have := t.naturality g
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
    exact this.symm)
  let cU : Cocone F :=
    { pt := Under.mk c
      ι := { app := fun j => Under.homMk (s.app j) (ht j)
             naturality := fun j k g => by
               apply Under.UnderMorphism.ext
               exact s.naturality g } }
  have hcU : IsColimit cU := isColimitOfReflects (Under.forget A) (by exact hc)
  have h2 := isColimitOfPreserves (Under.pushout φ ⋙ Under.forget Y) hcU
  let E : J ⥤ CommRingCat.{0} := F ⋙ Under.pushout φ ⋙ Under.forget Y
  let e : E ⟶ (Functor.const J).obj Y' :=
    ((Under.pushout φ ⋙ Under.forget Y).mapCocone cU).ι ≫ (Functor.const J).map hpo.flip.isoPushout.inv
  have hE : IsColimit (Cocone.mk _ e) :=
    h2.ofIsoColimit (Cocone.ext hpo.flip.isoPushout.symm (fun j => rfl))
  let p : D ⟶ E :=
    { app := fun j => (pushout.inl (t.app j) φ : D.obj j ⟶ pushout (t.app j) φ)
      naturality := fun j k g => by
        exact (pushout.inl_desc _ _ _).symm }
  refine ⟨E, p, e, fun j => pushout.inr (t.app j) φ, ⟨hE⟩, fun j => (IsPushout.of_hasPushout (t.app j) φ).flip,
    fun j => ?_, fun j k f => pushout.inr_desc _ _ _⟩
  have key : ∀ h, pushout.inl (t.app j) φ ≫ (pushout.desc (s.app j ≫ pushout.inl c φ) (pushout.inr c φ) h ≫
      hpo.flip.isoPushout.inv) = s.app j ≫ φ' := by
    intro h; rw [← Category.assoc, pushout.inl_desc, Category.assoc, hpo.flip.inl_isoPushout_inv]
  exact key _

theorem relAt (hB1 : B1) (q : ℕ) (i n : ℤ) {D Y' O : CommRingCat.{0}} (φ' : D ⟶ Y') (hq : IsUnit (q : D)) (o : D ⟶ O)
    (hIE : IE o) (hBC : BC q i φ' o) (z : HR q i n φ') (hz : PP q i n φ' (fgt _ _ _ n z) = 0) :
    ∃ (E : CommRingCat.{0}) (e : D ⟶ E) (s : E ⟶ O) (Z : CommRingCat.{0}) (u : Y' ⟶ Z) (ψ : E ⟶ Z)
      (h : IsPushout φ' e u ψ), Et e ∧ e ≫ s = o ∧ RP q i n φ' e u ψ h.w z = 0 := by
  obtain ⟨J, _, _, F, t, s, hc, hts⟩ := hIE
  have hZ := IsPushout.of_hasPushout φ' o
  set ψ := pushout.inr φ' o
  have hRE := hBC _ _ _ hZ
  obtain ⟨G, p, e, v, ⟨hG⟩, hpo, hpe, hv⟩ := pushColim φ' o _ ψ hZ F t s hc (fun j => (hts j).2)
  have hnat : ∀ {j k} (f : j ⟶ k), t.app j ≫ F.map f = t.app k := fun f => by simpa using (t.naturality f).symm
  have hs : ∀ {j k} (f : j ⟶ k), F.map f ≫ s.app k = s.app j := fun f => by simpa using s.naturality f
  have he : ∀ {j k} (f : j ⟶ k), G.map f ≫ e.app k = e.app j := fun f => by simpa using e.naturality f
  have hxO : PP q i n o (fgt _ _ _ n z) = 0 := by
    apply (hRE n).1
    change PP q i n ψ _ = _
    rw [map_zero, ← PP_comp, ← hZ.w, PP_comp, hz, map_zero]
  obtain ⟨j0⟩ : Nonempty J := IsFiltered.nonempty
  obtain ⟨k, f, hk⟩ := (hB1 q F _ hc n i).2 j0 (PP q i n (t.app j0) (fgt _ _ _ n z)) (unit_of (t.app j0) hq) (by
    change PP q i n (s.app j0) _ = 0
    rw [← PP_comp, (hts j0).2, hxO])
  change PP q i n (F.map f) _ = 0 at hk
  rw [← PP_comp, hnat] at hk
  have hm : 1 + (n - 1) = n := by omega
  obtain ⟨y, hy⟩ := exists_bd _ _ _ (n - 1) n hm (RP q i n φ' (t.app k) (v k) (p.app k) (hpo k).w z)
    (by rw [fgt_RP]; exact hk)
  obtain ⟨a, ha⟩ := (hRE (n - 1)).2 (PP q i (n - 1) (e.app k) y)
  obtain ⟨j, b, rfl⟩ := (hB1 q F _ hc (n - 1) i).1 a (unit_of o hq)
  change PP q i (n - 1) ψ (PP q i (n - 1) (s.app j) b) = _ at ha
  obtain ⟨l, g, hl⟩ := (hB1 q G _ hG (n - 1) i).2 (IsFiltered.max j k)
    (PP q i (n - 1) (G.map (IsFiltered.rightToMax j k)) y -
      PP q i (n - 1) (F.map (IsFiltered.leftToMax j k) ≫ p.app _) b) (unit_of (t.app _ ≫ p.app _) hq) (by
    change PP q i (n - 1) (e.app _) _ = 0
    rw [map_sub, ← PP_comp, ← PP_comp, he, Category.assoc, hpe, ← Category.assoc, hs, PP_comp, ha, sub_self])
  change PP q i (n - 1) (G.map g) _ = 0 at hl
  rw [map_sub, sub_eq_zero, ← PP_comp, ← PP_comp, ← G.map_comp, Category.assoc, ← p.naturality g,
    ← Category.assoc, PP_comp q i (n - 1) _ (p.app l)] at hl
  refine ⟨F.obj l, t.app l, s.app l, G.obj l, v l, p.app l, hpo l, (hts l).1, (hts l).2, ?_⟩
  rw [RP_comp q i n φ' (t.app k) (v k) (p.app k) (hpo k).w (F.map (IsFiltered.rightToMax j k ≫ g))
    (G.map (IsFiltered.rightToMax j k ≫ g)) (p.app l) (p.naturality _).symm _ _ _ (hnat _) (hv _ _ _), ← hy, RP_bd, hl]
  exact bd_pull ..

end LateralTheory.E.KernelLocalization
end
end

section

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.E.LZHensFinitePf

def HensIdemLift : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
  (B : Type) [CommRing B] [Algebra A B] [Module.Finite A B]
  (e : B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)), IsIdempotentElem e →
  ∃ f : B, IsIdempotentElem f ∧ Ideal.Quotient.mk _ f = e

theorem hensIdemLift : HensIdemLift := by
  intro A _ _ _ B _ _ _ e he
  exact GlobalTheory.exists_idempotent_lift_of_henselian A (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective he

theorem idem_triv_of_preconnected (R : Type) [CommRing R] [PreconnectedSpace (PrimeSpectrum R)]
    (e : R) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hc : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  rcases isClopen_iff.mp hc with h | h
  · left
    apply he.eq_zero_of_isNilpotent
    rw [← PrimeSpectrum.basicOpen_eq_bot_iff]
    exact SetLike.coe_injective h
  · right
    have hz : PrimeSpectrum.zeroLocus ({e} : Set R) = ∅ := by
      rw [← compl_compl (PrimeSpectrum.zeroLocus ({e} : Set R)), ← PrimeSpectrum.basicOpen_eq_zeroLocus_compl, h,
        Set.compl_univ]
    have h1 : IsNilpotent (1 - e) := by
      rw [← PrimeSpectrum.basicOpen_eq_bot_iff]
      apply SetLike.coe_injective
      rw [PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem _ he.one_sub, sub_sub_cancel, hz]
      rfl
    exact (sub_eq_zero.mp (he.one_sub.eq_zero_of_isNilpotent h1)).symm

theorem subsingleton_of_idem (R : Type) [CommRing R] [IsArtinianRing R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) : Subsingleton (PrimeSpectrum R) := by
  have hp : PreconnectedSpace (PrimeSpectrum R) := by
    rw [preconnectedSpace_iff_clopen]
    intro s hs
    obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
    rcases h e he with rfl | rfl
    · left; simp
    · right; simp
  exact ⟨fun x y => hp.constant (f := id) continuous_id⟩

theorem LZHensFinite_of_lift (hL : HensIdemLift) : LateralTheory.E.LZProperCut.LZHensFinite := by
  intro A _ _ _ B _ _ _ hB
  have : ConnectedSpace (PrimeSpectrum B) := hB
  have : Nontrivial B := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  set I := (IsLocalRing.maximalIdeal A).map (algebraMap A B) with hI
  have hle : ∀ M : Ideal B, M.IsMaximal → I ≤ M := by
    intro M hM
    rw [hI, Ideal.map_le_iff_le_comap]
    have : (M.comap (algebraMap A B)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal M
    exact (IsLocalRing.eq_maximalIdeal this).ge
  have htriv : ∀ e : B ⧸ I, IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := hL A B e he
    rcases idem_triv_of_preconnected B f hf with rfl | rfl
    · left; simp
    · right; simp
  have : Module.Finite (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ I) :=
    Module.Finite.of_restrictScalars_finite A _ _
  let _ : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  have : IsArtinianRing (B ⧸ I) := IsArtinianRing.of_finite (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ I)
  have hsub := subsingleton_of_idem (B ⧸ I) htriv
  have key : ∀ P : Ideal B, P.IsMaximal →
      P = (P.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) ∧ (P.map (Ideal.Quotient.mk I)).IsPrime := by
    intro P hP
    refine ⟨(Ideal.comap_map_mk (hle P hP)).symm, ?_⟩
    exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hle P hP)
  apply IsLocalRing.of_unique_max_ideal
  obtain ⟨M, hM⟩ := Ideal.exists_maximal B
  refine ⟨M, hM, fun N hN => ?_⟩
  obtain ⟨hN1, hN2⟩ := key N hN
  obtain ⟨hM1, hM2⟩ := key M hM
  have : (⟨_, hN2⟩ : PrimeSpectrum (B ⧸ I)) = ⟨_, hM2⟩ := Subsingleton.elim _ _
  exact hN1.trans ((congrArg (fun P : PrimeSpectrum (B ⧸ I) => P.asIdeal.comap (Ideal.Quotient.mk I)) this).trans hM1.symm)

end LateralTheory.E.LZHensFinitePf
end
end
