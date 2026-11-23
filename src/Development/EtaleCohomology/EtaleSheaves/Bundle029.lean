module

public import Development.EtaleCohomology.EtaleSheaves.LineHigh
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Order.CompletePartialOrder
public import Development.EtaleCohomology.TateTwists.Bundle017
public import Development.EtaleCohomology.EtaleSheaves.Bundle006
public import Development.EtaleCohomology.TateTwists.Bundle004
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
import Mathlib.Tactic.Lemma
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
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.MayerVietorisSequence

def MVSpc : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R), ∃ d : ∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g →
  ∀ n : ℤ, H R (pullback f g) F n →+ H R E F (n + 1),
  (∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (h : Cover2 R f g) (n : ℤ),
    (∀ a b, pull R (pullback.fst f g) F n a = pull R (pullback.snd f g) F n b ↔ ∃ x, pull R f F n x = a ∧ pull R g F n x = b) ∧
    (∀ c, d f g h n c = 0 ↔ ∃ a b, c = pull R (pullback.fst f g) F n a - pull R (pullback.snd f g) F n b) ∧
    ∀ x, (pull R f F (n + 1) x = 0 ∧ pull R g F (n + 1) x = 0) ↔ ∃ c, d f g h n c = x) ∧
  ∀ {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E') (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V')
    (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') (h : Cover2 R f g) (h' : Cover2 R f' g') (n : ℤ) c,
    pull R p F (n + 1) (d f' g' h' n c) = d f g h n (pull R (pullback.map f g f' g' u v p hu hv) F n c)

def OpenCov : Prop := ∀ (R : Type) [CommRing R] {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f]
  [IsOpenImmersion g], Set.range f ∪ Set.range g = Set.univ → Cover2 R (sch.map f) (sch.map g)

def SchPB : Prop := ∀ {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X), IsIso (pullbackComparison sch f g)

variable (R : Type) [CommRing R]

theorem pull_hom_inv {E E' : Spc} (e : E ⟶ E') [IsIso e] (F : Shv R) (n : ℤ) (x : H R E F n) :
    pull R e F n (pull R (inv e) F n x) = x := by
  rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem pull_inv_hom {E E' : Spc} (e : E ⟶ E') [IsIso e] (F : Shv R) (n : ℤ) (x : H R E' F n) :
    pull R (inv e) F n (pull R e F n x) = x := by
  rw [← pull_comp, IsIso.inv_hom_id, pull_id]

theorem pull_inj_of_iso' {E E' : Spc} (e : E ⟶ E') [IsIso e] (F : Shv R) (n : ℤ) :
    Function.Injective (pull R e F n) := fun x y h => by
  rw [← pull_inv_hom R e F n x, h, pull_inv_hom]

theorem comp_sq (hP : SchPB) {U V X U' V' X' : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) (f' : U' ⟶ X') (g' : V' ⟶ X')
    (u : U ⟶ U') (v : V ⟶ V') (p : X ⟶ X') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g')
    (hu' : sch.map f ≫ sch.map p = sch.map u ≫ sch.map f') (hv' : sch.map g ≫ sch.map p = sch.map v ≫ sch.map g') :
    have := hP f g; have := hP f' g'
    inv (pullbackComparison sch f g) ≫ sch.map (pullback.map f g f' g' u v p hu hv) =
      pullback.map _ _ _ _ (sch.map u) (sch.map v) (sch.map p) hu' hv' ≫ inv (pullbackComparison sch f' g') := set_option synthInstance.maxHeartbeats 200000 in by
  have := hP f g; have := hP f' g'
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackComparison_comp_fst, pullback.lift_fst, ← Functor.map_comp, pullback.lift_fst_assoc]
    rw [pullbackComparison_comp_fst_assoc, ← Functor.map_comp]
  · simp only [Category.assoc, pullbackComparison_comp_snd, pullback.lift_snd, ← Functor.map_comp, pullback.lift_snd_assoc]
    rw [pullbackComparison_comp_snd_assoc, ← Functor.map_comp]

end LateralTheory.E.MayerVietorisSequence

open LateralTheory.E.MayerVietorisSequence in
theorem LateralTheory.E.t_E2Cut.MV_of_three (hS : MVSpc) (hC : OpenCov) (hP : SchPB) : LateralTheory.E.t_E2Cut.MV := by
  classical
  intro hyp R _ F
  obtain ⟨d, hex, hnat⟩ := hS hyp.a1 R F
  refine ⟨fun {U V X} f g n => if h : Cover2 R (sch.map f) (sch.map g) then
    have := hP f g; (d _ _ h n).comp (pull R (inv (pullbackComparison sch f g)) F n) else 0, ?_, ?_⟩
  · intro U V X f g _ _ hcov n
    have := hP f g
    have h := hC R f g hcov
    obtain ⟨h1, h2, h3⟩ := hex (sch.map f) (sch.map g) h n
    have hf : sch.map (pullback.fst f g) = pullbackComparison sch f g ≫ pullback.fst _ _ :=
      (pullbackComparison_comp_fst _ _ _).symm
    have hg : sch.map (pullback.snd f g) = pullbackComparison sch f g ≫ pullback.snd _ _ :=
      (pullbackComparison_comp_snd _ _ _).symm
    simp only [dif_pos h, AddMonoidHom.comp_apply]
    refine ⟨?_, ?_, ?_⟩
    · intro a b hab
      rw [hf, hg, pull_comp, pull_comp] at hab
      exact (h1 a b).1 (pull_inj_of_iso' R _ F n hab)
    · intro w
      rw [h2]
      constructor
      · rintro ⟨a, b, hab⟩
        refine ⟨a, b, ?_⟩
        rw [hf, hg, pull_comp, pull_comp, ← map_sub, ← hab, pull_hom_inv]
      · rintro ⟨a, b, rfl⟩
        refine ⟨a, b, ?_⟩
        rw [hf, hg, pull_comp, pull_comp, ← map_sub, pull_inv_hom]
    · intro x
      rw [h3]
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨pull R (pullbackComparison sch f g) F n c, by rw [pull_inv_hom]⟩
      · rintro ⟨w, rfl⟩
        exact ⟨_, rfl⟩
  · intro U V X U' V' X' f g f' g' _ _ _ _ hcov hcov' u v p hu hv n w
    have := hP f g; have := hP f' g'
    have h := hC R f g hcov
    have h' := hC R f' g' hcov'
    simp only [dif_pos h, dif_pos h', AddMonoidHom.comp_apply]
    have hu' : sch.map f ≫ sch.map p = sch.map u ≫ sch.map f' := by rw [← Functor.map_comp, hu, Functor.map_comp]
    have hv' : sch.map g ≫ sch.map p = sch.map v ≫ sch.map g' := by rw [← Functor.map_comp, hv, Functor.map_comp]
    rw [hnat (sch.map f) (sch.map g) (sch.map f') (sch.map g') (sch.map p) (sch.map u) (sch.map v) hu' hv' h h' n,
      ← pull_comp, ← pull_comp, comp_sq hP f g f' g' u v p hu hv hu' hv']

namespace LateralTheory.E.MayerVietorisSequence

theorem schPB : SchPB := fun f g => by
  have : PreservesLimitsOfShape WalkingCospan sch := by unfold sch; infer_instance
  infer_instance

end LateralTheory.E.MayerVietorisSequence

namespace LateralTheory.E.MayerVietorisSequence

def SES : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∃ w,
  (ShortComplex.mk (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)))
    (biprod.desc ((chains R).map f) ((chains R).map g)) w).ShortExact

def LES : Prop := ∀ (R : Type) [CommRing R] (F : Shv R), ∃ d : ∀ {N K L M : Cx R} (a : N ⟶ K) (b : N ⟶ L) (c : K ⟶ M)
    (e : L ⟶ M) (w : biprod.lift a (-b) ≫ biprod.desc c e = 0), (ShortComplex.mk _ _ w).ShortExact →
    ∀ n : ℤ, HK R N F n →+ HK R M F (n + 1),
  (∀ {N K L M : Cx R} (a : N ⟶ K) (b : N ⟶ L) (c : K ⟶ M) (e : L ⟶ M) (w : biprod.lift a (-b) ≫ biprod.desc c e = 0)
    (hS : (ShortComplex.mk _ _ w).ShortExact) (n : ℤ),
    (∀ x y, HK.pull R a F n x = HK.pull R b F n y ↔ ∃ z, HK.pull R c F n z = x ∧ HK.pull R e F n z = y) ∧
    (∀ t, d a b c e w hS n t = 0 ↔ ∃ x y, t = HK.pull R a F n x - HK.pull R b F n y) ∧
    ∀ z, (HK.pull R c F (n + 1) z = 0 ∧ HK.pull R e F (n + 1) z = 0) ↔ ∃ t, d a b c e w hS n t = z) ∧
  ∀ {N K L M N' K' L' M' : Cx R} (a : N ⟶ K) (b : N ⟶ L) (c : K ⟶ M) (e : L ⟶ M) (a' : N' ⟶ K') (b' : N' ⟶ L')
    (c' : K' ⟶ M') (e' : L' ⟶ M') (w : biprod.lift a (-b) ≫ biprod.desc c e = 0)
    (w' : biprod.lift a' (-b') ≫ biprod.desc c' e' = 0) (hS : (ShortComplex.mk _ _ w).ShortExact)
    (hS' : (ShortComplex.mk _ _ w').ShortExact) (φN : N ⟶ N') (φK : K ⟶ K') (φL : L ⟶ L') (φM : M ⟶ M'),
    a ≫ φK = φN ≫ a' → b ≫ φL = φN ≫ b' → c ≫ φM = φK ≫ c' → e ≫ φM = φL ≫ e' → ∀ (n : ℤ) t,
    HK.pull R φM F (n + 1) (d a' b' c' e' w' hS' n t) = d a b c e w hS n (HK.pull R φN F n t)

theorem mvSpc_of (hE : SES) (hL : LES) : MVSpc := by
  intro _ R _ F
  obtain ⟨d, hex, hnat⟩ := hL R F
  refine ⟨fun f g h n => d _ _ _ _ (hE R f g h).choose (hE R f g h).choose_spec n, ?_, ?_⟩
  · intro U V E f g h n
    exact hex _ _ _ _ (hE R f g h).choose (hE R f g h).choose_spec n
  · intro U V E U' V' E' f g f' g' p u v hu hv h h' n c
    refine hnat _ _ _ _ _ _ _ _ _ _ _ _ ((chains R).map (pullback.map f g f' g' u v p hu hv)) ((chains R).map u)
      ((chains R).map v) ((chains R).map p) ?_ ?_ ?_ ?_ n c
    · rw [← Functor.map_comp, ← Functor.map_comp, pullback.lift_fst]
    · rw [← Functor.map_comp, ← Functor.map_comp, pullback.lift_snd]
    · rw [← Functor.map_comp, ← Functor.map_comp, hu]
    · rw [← Functor.map_comp, ← Functor.map_comp, hv]

end LateralTheory.E.MayerVietorisSequence
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ChartsPf

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev D (i : Fin 2) : P1.Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (MvPolynomial.X i)

lemma X_mem (i : Fin 2) : (MvPolynomial.X i : MvPolynomial (Fin 2) ℤ) ∈ MvPolynomial.homogeneousSubmodule (Fin 2) ℤ 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X ℤ i)

lemma D_affine (i : Fin 2) : IsAffineOpen (D i) :=
  Proj.isAffineOpen_basicOpen _ _ (X_mem i) one_pos

lemma D_cover : ⨆ i, D i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top'
  · exact fun i => ⟨1, X_mem i⟩
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ Algebra.adjoin ℤ (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ)) := by
      rw [MvPolynomial.adjoin_range_X]; trivial
    have h : Algebra.adjoin ℤ (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ)) ≤
        (Algebra.adjoin (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ 0)
          (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ))).restrictScalars ℤ :=
      Algebra.adjoin_le Algebra.subset_adjoin
    exact h hx

end LateralTheory.E.ChartsPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernClassExistence

def LeafEvMk : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

def LeafEvDelta : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}), (∀ (x : Sx E 0 U), ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x)) ∧ ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U), ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) + m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i)

def EtaleKummerChernEdgeValuesExistNatural : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ a : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res _ (tw q 1)).X 1) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (a U x) = a V (x.res g)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      a U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)

def EtaleKummerChernTriangleValuesExistNatural : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ a : ∀ U : Scheme.{0}, Sx E 2 U → Sec ((res _ (tw q 1)).X 0) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 2 U), Sec.res g (a U x) = a V (x.res g)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      a U x = kumT q U v + kumT q U w - kumT q U (v * w)

def EtaleKummerChernCochainCoboundaryVanishesOnEdges : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev (δ 2 3 α) 1 2 (by simp) U x = 0

def EtaleKummerChernCochainCoboundaryVanishesOnTriangles : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 2 U), ev (δ 2 3 α) 2 1 (by simp) U x = 0

def EtaleKummerChernCochainCoboundaryVanishesOnTetrahedra : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 3 U), ev (δ 2 3 α) 3 0 (by simp) U x = 0

theorem cx_ext_pf : LateralTheory.EtaleFoundations.cx_ext := by
  intro R _ E I n α h
  apply LateralTheory.E.ChernCocycleExistenceAndUniqueness.cochain_ext_ev α 0
  intro p s hs U x
  rw [h]
  simp [ev]

theorem res_neg_pf : LateralTheory.EtaleFoundations.res_neg := by
  intro q s hs U a
  exact LateralTheory.EtaleFoundations.FirstChernUniqueness.sec_sub (LateralTheory.EtaleFoundations.FirstChernUniqueness.res_zero_neg q s hs) U a 0

theorem etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness (hmk : LeafEvMk) (hd : LeafEvDelta) (h1 : EtaleKummerChernEdgeValuesExistNatural) (h2 : EtaleKummerChernTriangleValuesExistNatural)
    (c1 : EtaleKummerChernCochainCoboundaryVanishesOnEdges) (c2 : EtaleKummerChernCochainCoboundaryVanishesOnTriangles) (c3 : EtaleKummerChernCochainCoboundaryVanishesOnTetrahedra) : LateralTheory.E.ChernCocycleExistenceAndUniqueness.EtaleKummerChernCocycleExists := by
  intro q _ E L hi
  exact LateralTheory.EtaleFoundations.exists_closed_etale_kummer_chern_class_cochain_of_values hmk h1 h2 (LateralTheory.EtaleFoundations.etale_first_chern_cochain_closed_of_components hd cx_ext_pf res_neg_pf c1 c2 c3) q L hi

end LateralTheory.E.ChernClassExistence
end
end
