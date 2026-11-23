module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
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

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.CompanionTheory.KummerPrimitive

theorem res_d_neg {R : Type} [CommRing R] (F : Shv R) : (res R F).d (-1) 0 = 0 := by
  have : (res R F).IsStrictlyGE 0 := by
    unfold res
    infer_instance
  exact (CochainComplex.isZero_of_isStrictlyGE (res R F) 0 (-1) (by omega)).eq_of_src _ _

theorem cechPt_congr {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) {U : Scheme.{0}} {x x' : U ⟶ X}
    {y y' : Fin (k + 1) → (U ⟶ Y)} (h : ∀ i, y i ≫ f = x) (h' : ∀ i, y' i ≫ f = x') (hx : x = x')
    (hy : ∀ i, y i = y' i) : cechPt f k x y h = cechPt f k x' y' h' := by
  subst hx
  obtain rfl := funext hy
  rfl

def pt0 {Y X : Scheme.{0}} (f : Y ⟶ X) {V : Scheme.{0}} (b : V ⟶ Y) : Sx (cech f) 0 V :=
  cechPt f 0 (b ≫ f) ![b] (by intro i; fin_cases i; rfl)

def pt1 {Y X : Scheme.{0}} (f : Y ⟶ X) {V : Scheme.{0}} (b c : V ⟶ Y) (h : b ≫ f = c ≫ f) : Sx (cech f) 1 V :=
  cechPt f 1 (b ≫ f) ![b, c] (by
    intro i; fin_cases i
    · rfl
    · exact h.symm)

def pt2 {Y X : Scheme.{0}} (f : Y ⟶ X) {V : Scheme.{0}} (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) :
    Sx (cech f) 2 V :=
  cechPt f 2 (b ≫ f) ![b, c, e] (by
    intro i; fin_cases i
    · rfl
    · exact h.symm
    · exact (h.trans h').symm)

section Simplices

variable (hC : CechPt) {Y X : Scheme.{0}} (f : Y ⟶ X) {V V' : Scheme.{0}}
include hC

theorem cechPoint_augmentation (b : V ⟶ Y) : Sx.map (_root_.GlobalTheory.EtC.cechAug f) (pt0 f b) = b ≫ f :=
  (((hC Y X f 0 V).2.2 _ _ _).1)

theorem cechPoint_restrict (g : V' ⟶ V) (b : V ⟶ Y) : Sx.res g (pt0 f b) = pt0 f (g ≫ b) := by
  refine ((hC Y X f 0 V).2.2 _ _ _).2.1 V' g |>.trans (cechPt_congr _ _ _ _ (Category.assoc _ _ _).symm ?_)
  intro i; fin_cases i; rfl

theorem cechPair_restrict (g : V' ⟶ V) (b c : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : (g ≫ b) ≫ f = (g ≫ c) ≫ f) :
    Sx.res g (pt1 f b c h) = pt1 f (g ≫ b) (g ≫ c) h' := by
  refine ((hC Y X f 1 V).2.2 _ _ _).2.1 V' g |>.trans (cechPt_congr _ _ _ _ (Category.assoc _ _ _).symm ?_)
  intro i; fin_cases i <;> rfl

theorem cechPair_face_zero (b c : V ⟶ Y) (h : b ≫ f = c ≫ f) : (pt1 f b c h).face 0 = pt0 f c := by
  refine ((hC Y X f 1 V).2.2 _ _ _).2.2 0 (SimplexCategory.δ 0) |>.trans (cechPt_congr _ _ _ _ h ?_)
  intro i; fin_cases i; rfl

theorem cechPair_face_one (b c : V ⟶ Y) (h : b ≫ f = c ≫ f) : (pt1 f b c h).face 1 = pt0 f b := by
  refine ((hC Y X f 1 V).2.2 _ _ _).2.2 0 (SimplexCategory.δ 1) |>.trans (cechPt_congr _ _ _ _ rfl ?_)
  intro i; fin_cases i; rfl

theorem cechTriple_face_zero (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) :
    (pt2 f b c e h h').face 0 = pt1 f c e h' := by
  refine ((hC Y X f 2 V).2.2 _ _ _).2.2 1 (SimplexCategory.δ 0) |>.trans (cechPt_congr _ _ _ _ h ?_)
  intro i; fin_cases i <;> rfl

theorem cechTriple_face_one (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) :
    (pt2 f b c e h h').face 1 = pt1 f b e (h.trans h') := by
  refine ((hC Y X f 2 V).2.2 _ _ _).2.2 1 (SimplexCategory.δ 1) |>.trans (cechPt_congr _ _ _ _ rfl ?_)
  intro i; fin_cases i <;> rfl

theorem cechTriple_face_two (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) :
    (pt2 f b c e h h').face 2 = pt1 f b c h := by
  refine ((hC Y X f 2 V).2.2 _ _ _).2.2 1 (SimplexCategory.δ 2) |>.trans (cechPt_congr _ _ _ _ rfl ?_)
  intro i; fin_cases i <;> rfl

theorem cechTriple_subface_zero (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) (hs : 0 + 1 ≤ 2) :
    (pt2 f b c e h h').sub 0 1 hs = pt1 f b c h := by
  refine ((hC Y X f 2 V).2.2 _ _ _).2.2 1 (SimplexCategory.subinterval 0 1 hs) |>.trans (cechPt_congr _ _ _ _ rfl ?_)
  intro i; fin_cases i <;> rfl

theorem cechTriple_subface_one (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) (hs : 1 + 1 ≤ 2) :
    (pt2 f b c e h h').sub 1 1 hs = pt1 f c e h' := by
  refine ((hC Y X f 2 V).2.2 _ _ _).2.2 1 (SimplexCategory.subinterval 1 1 hs) |>.trans (cechPt_congr _ _ _ _ h ?_)
  intro i; fin_cases i <;> rfl

end Simplices

section Coboundary

variable (hD : EvDel) {R : Type} [CommRing R] {E : Spc} {I : GlobalTheory.EtC.Cx R} (β : Cochain ((chains R).obj E) I 1)
  (U : Scheme.{0})
include hD

theorem del_one (z : Sx E 1 U) : ev (δ 1 2 β) 1 1 (by simp) U z =
    Sec.map (I.d 0 1) (ev β 1 0 (by simp) U z) +
      (ev β 0 1 (by simp) U (z.face 0) - ev β 0 1 (by simp) U (z.face 1)) := by
  refine ((hD R E I 1 2 (by norm_num) β U).2 0 0 1 (by simp) (by simp) z).trans ?_
  rw [Int.negOnePow_even 2 (by decide), one_smul, Fin.sum_univ_two]
  simp [sub_eq_add_neg]

theorem del_two (z : Sx E 2 U) : ev (δ 1 2 β) 2 0 (by simp) U z =
    Sec.map (I.d (-1) 0) (ev β 2 (-1) (by simp) U z) +
      (ev β 1 0 (by simp) U (z.face 0) - ev β 1 0 (by simp) U (z.face 1) + ev β 1 0 (by simp) U (z.face 2)) := by
  refine ((hD R E I 1 2 (by norm_num) β U).2 1 (-1) 0 (by simp) (by simp) z).trans ?_
  rw [Int.negOnePow_even 2 (by decide), one_smul, Fin.sum_univ_three]
  simp [sub_eq_add_neg]

end Coboundary

theorem main : CrystallineSemistableComparison.E.EvExt → CrystallineSemistableComparison.E.EvNat → CrystallineSemistableComparison.E.EvDel → CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.CechPt →
    CrystallineSemistableComparison.E.FirstChernCoboundary := by
  intro hExt hNat hDel hConc hBasic hCech hC1 q _ X D L hL hInv x hx
  obtain ⟨γ, hγ, hγ0, hγ1, hγ2⟩ := hC1 q (cech D.f) L hInv
  obtain ⟨a, ha⟩ := (hBasic (ZMod q) (res _ (tw q 1)) X 2).1 x
  obtain ⟨α, hαc, hαx⟩ := (hConc (ZMod q) (res _ (tw q 1)) X 2 a).2.1 x ha
  have hmk : CohomologyClass.mk (γ - zcomp (Cocycle.ofHom ((chains (ZMod q)).map (_root_.GlobalTheory.EtC.cechAug D.f))) α (zero_add 2)) = 0 := by
    rw [CohomologyClass.mk_sub, hγ, ← hx, ← hαx]
    exact sub_self _
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 1 (by norm_num)] at hmk
  obtain ⟨β, hβ⟩ := hmk
  have hv : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + 2 = s) (U : Scheme.{0}) (z : Sx (cech D.f) p U),
      ev (δ 1 2 β) p s h U z = ev γ.1 p s h U z - ev α.1 p s h U (Sx.map (_root_.GlobalTheory.EtC.cechAug D.f) z) := by
    intro p s h U z
    have e : δ 1 2 β = γ.1 - (Cochain.ofHom ((chains (ZMod q)).map (_root_.GlobalTheory.EtC.cechAug D.f))).comp α.1 (zero_add 2) := hβ
    rw [e, ((hExt _ _ _ _ _ _).2 p s h U z).2.1, ((hNat _ _ _ _ α.1 p s h U).2 _ _ z)]
  have hv1 : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + 2 = s) (U : Scheme.{0}) (z : Sx (cech D.f) (p + 1) U),
      ev (δ 1 2 β) (p + 1) s h U z = ev γ.1 (p + 1) s h U z := by
    intro p s h U z
    rw [hv, show ev α.1 (p + 1) s h U (Sx.map (_root_.GlobalTheory.EtC.cechAug D.f) z) = 0 from hαc.2 p s h U (Sx.map (_root_.GlobalTheory.EtC.cechAug D.f) z), sub_zero]
  refine ⟨a, fun V b => - ev β 0 1 (by simp) V (pt0 D.f b), fun V b c h => ev β 1 0 (by simp) V (pt1 D.f b c h),
    ha, ?_, ?_, ?_, ?_, ?_⟩
  · intro V V' g b
    have e := (hNat _ _ _ _ β 0 1 (by simp) V).1 V' g (pt0 D.f b)
    rw [cechPoint_restrict hCech] at e
    simp only [map_neg]
    exact congrArg Neg.neg e.symm
  · intro V V' g b c h h'
    rw [← (hNat _ _ _ _ β 1 0 (by simp) V).1 V' g (pt1 D.f b c h), cechPair_restrict hCech]
  · intro V b
    have h0 := ((hDel _ _ _ 1 2 (by norm_num) β V).1 (pt0 D.f b))
    rw [hv, hγ0, cechPoint_augmentation hCech, show ev α.1 0 2 (by simp) V (b ≫ D.f) = Sec.res (b ≫ D.f) a from hαc.1 V _, zero_sub] at h0
    simp only [map_neg]
    exact (congrArg Neg.neg h0).symm.trans (neg_neg _)
  · intro V b c h v hv'
    have hu : v ^ q = lineUnit L (pt1 D.f b c h) := hv'.trans (hL V _ ![b, c] _).symm
    have h1 := del_one hDel β V (pt1 D.f b c h)
    rw [hv1 0 1 _ V (pt1 D.f b c h), hγ1 V _ v hu, cechPair_face_zero hCech, cechPair_face_one hCech] at h1
    simp only [map_sub]
    change -ev β 0 1 (by simp) V (pt0 D.f c) - -ev β 0 1 (by simp) V (pt0 D.f b) =
      Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (ev β 1 0 (by simp) V (pt1 D.f b c h)) -
        Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q V v)
    rw [h1]
    abel
  · intro V b c e h h' v w hv' hw'
    have hu : v ^ q = lineUnit L ((pt2 D.f b c e h h').sub 0 1 (by omega)) := by
      rw [cechTriple_subface_zero hCech]
      exact hv'.trans (hL V _ ![b, c] _).symm
    have hu' : w ^ q = lineUnit L ((pt2 D.f b c e h h').sub 1 1 (by omega)) := by
      rw [cechTriple_subface_one hCech]
      exact hw'.trans (hL V _ ![c, e] _).symm
    have h2 := del_two hDel β V (pt2 D.f b c e h h')
    have hz : ∀ y : Sec ((res (ZMod q) (tw q 1)).X (-1)) V, Sec.map ((res (ZMod q) (tw q 1)).d (-1) 0) y = 0 := by
      intro y
      rw [res_d_neg]
      rfl
    rw [hv1 1 0 _ V (pt2 D.f b c e h h'), hγ2 V _ v w hu hu', cechTriple_face_zero hCech, cechTriple_face_one hCech, cechTriple_face_two hCech,
      hz, zero_add] at h2
    exact h2.symm

end GlobalTheory.CompanionTheory.KummerPrimitive
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMapPull

universe w w' w₁ w₁' u v u' v'

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
  {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w'} R} {F' : C' ⥤ ModuleCat.{w₁'} R'}
  {T : Res.{w} F} {T' : Res.{w₁} F'} {m : Mor F F' σ}

theorem d_pullC (n : ResMor T T' m) (s k : ℕ) (x : Cn (T.K s) k) :
    d (T'.K s) k (n.pullC s k x) = n.pullC s (k + 1) (d (T.K s) k x) := by
  funext t
  change ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • ((T'.K s).map (GlobalTheory.CatH.toLast i t)).hom
      (n.τ s _ (x (GlobalTheory.CatH.face i t ⋙ m.G))) =
    n.τ s _ (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
      ((T.K s).map (m.G.map (GlobalTheory.CatH.toLast i t))).hom (x (GlobalTheory.CatH.face i t ⋙ m.G)))

  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul, n.nat]

theorem dvC_pullC (n : ResMor T T' m) (s k : ℕ) (x : Cn (T.K s) k) :
    T'.dvC s k (n.pullC s k x) = n.pullC (s + 1) k (T.dvC s k x) :=
  funext fun t => (n.dv s _ (x (t ⋙ m.G))).symm

theorem ιC_pullC (n : ResMor T T' m) (k : ℕ) (z : Cn F k) :
    T'.ιC k (m.pullC k z) = n.pullC 0 k (T.ιC k z) :=
  funext fun t => (n.ι _ (z (t ⋙ m.G))).symm

theorem pullC_zsmul (n : ResMor T T' m) (s k : ℕ) (c : ℤ) (x : Cn (T.K s) k) :
    n.pullC s k (c • x) = c • n.pullC s k x :=
  funext fun t => map_zsmul (n.τ s _) c (x (t ⋙ m.G))

theorem st_pullC (n : ResMor T T' m) {j : ℕ} (z : Cn F j) :
    ∀ (s k : ℕ) (x : Cn (T.K s) k), T.St z s k x → T'.St (m.pullC j z) s k (n.pullC s k x) := by
  intro s
  induction s with
  | zero =>
    intro k x h
    simp only [Res.St] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, ιC_pullC n j z⟩
  | succ s ih =>
    intro k x h
    simp only [Res.St] at h ⊢
    obtain ⟨a, rfl, ha⟩ := h
    refine ⟨n.pullC s k a, dvC_pullC n s k a, ?_⟩
    have := ih (k + 1) _ ha
    rwa [pullC_zsmul, ← d_pullC] at this

end GlobalTheory.CompanionTheory.EdgeMapPull


open GlobalTheory.CompanionTheory.EdgeMapPull in
theorem GlobalTheory.CompanionTheory.EdgeMapPull.edgeMap : CrystallineSemistableComparison.E.EdgeMap := by
  intro R R' _ _ σ C C' _ _ F F' T T' m n j x h hE
  obtain ⟨z, hz, hS, rfl⟩ := hE
  exact ⟨m.pullC j z, by rw [m.d_pullC, hz, map_zero], st_pullC n z j 0 x hS, rfl⟩
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.EdgeRed

theorem res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res h (Sec.res g x) = Sec.res (h ≫ g) x := by
  simp [Sec.res]

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun t => t.hom x) h).symm

variable {C C' : Type 1} [Category.{0} C] [Category.{0} C']

def redResMor (hS : KapSpec) (hK : KapRed) (hR : InRed) {Q q : ℕ} [NeZero Q] [NeZero q] (h : q ∣ Q)
    (P : Probe C Q) (P' : Probe C' q) (m : Mor P.L P'.L (RingHom.id ℤ))
    (g : ∀ c : C', P'.U c ⟶ P.U (m.G.obj c))
    (hg : ∀ {c c' : C'} (φ : c ⟶ c'), g c' ≫ (P.S.map (m.G.map φ)).unop = (P'.S.map φ).unop ≫ g c)
    (hτ : ∀ c (f : LocallyConstant (P.U (m.G.obj c)) (ZMod Q)),
      m.τ c f = lcRes q (g c) (f.map (ZMod.castHom h (ZMod q))))
    (hζ : ∀ c, (P'.ζ c).1 = (primRes (g c) (P.ζ _)).1 ^ (Q / q)) (i : ℤ) :
    ResMor (P.res i) (P'.res i) m where
  τ s c :=
    { toFun := fun x => Sec.res (g c) ((redMap Q q i).app (P.U (m.G.obj c)) (s : ℤ) x)
      map_zero' := by simp
      map_add' := fun x y => by simp }
  nat s {c c'} φ x := by
    change Sec.res (g c') ((redMap Q q i).app _ (s : ℤ) (Sec.res (P.S.map (m.G.map φ)).unop x)) =
      Sec.res (P'.S.map φ).unop (Sec.res (g c) ((redMap Q q i).app _ (s : ℤ) x))
    rw [← (redMap Q q i).nat, res_res, res_res, hg]
  ι c x := by
    change Sec.res (g c) ((redMap Q q i).app _ 0 (Sec.map (resι _ (tw Q i)) (kap i (P.ζ (m.G.obj c)) x))) =
      Sec.map (resι _ (tw q i)) (kap i (P'.ζ c) (m.τ c x))
    rw [(redMap Q q i).nat, res_map, (hS Q i _ (P.ζ (m.G.obj c)) x).2.2 _ (g c),
      hK hR Q q h i _ (primRes (g c) (P.ζ (m.G.obj c))) (P'.ζ c) (hζ c), hτ]
    rfl
  dv s c x := by
    change Sec.res (g c) ((redMap Q q i).app _ ((s + 1 : ℕ) : ℤ) (Sec.map ((GlobalTheory.EtC.res _ (tw Q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) x)) =
      Sec.map ((GlobalTheory.EtC.res _ (tw q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) (Sec.res (g c) ((redMap Q q i).app _ (s : ℤ) x))
    rw [← (redMap Q q i).comm, res_map]

theorem etRed : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.EdgeMap → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepOp → CrystallineSemistableComparison.E.KapSpec →
    CrystallineSemistableComparison.E.KapRed → CrystallineSemistableComparison.E.EtRed := by
  intro hSpec hEdge hRep hOpR hS hK hGen hR hOp Q q _ _ h C C' _ _ P P' X Y Y' m g hg hτ hy hζ i j x
  obtain ⟨a, ha⟩ := (hRep _ _ X (j : ℤ)).1 x
  have hE := (hSpec hGen Q C P X Y i j x).1 a ha
  have hE' := hEdge ℤ ℤ (RingHom.id ℤ) C C' P.L P'.L (P.res i) (P'.res i) m
    (redResMor hS hK hR h P P' m g hg hτ hζ i) j _ _ hE
  have hr : Rep (red Q q _ (j : ℤ) i x) ((redMap Q q i).app X (j : ℤ) a) :=
    hOpR hOp _ _ _ _ (redMap Q q i) X (j : ℤ) x a ha
  refine (hSpec hGen q C' P' X Y' i j (red Q q _ (j : ℤ) i x)).2 _ ⟨_, hr, ?_⟩
  convert hE' using 1
  funext t
  change Sec.res (Y'.y _) ((redMap Q q i).app X (j : ℤ) a) =
    Sec.res (g _) ((redMap Q q i).app _ (j : ℤ) (Sec.res (Y.y _) a))
  rw [← (redMap Q q i).nat, res_res, hy]

end GlobalTheory.CompanionTheory.EdgeRed
end
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeRep

theorem repOp : CrystallineSemistableComparison.E.EvNat → CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepOp := by
  intro _ hConc hBasic hOp S R _ _ I J ρ X n x a hRep
  obtain ⟨α, hα, hmk⟩ := (hConc S I X n a).2.1 x hRep
  have hcl : Sec.map (J.d n (n + 1)) (ρ.app X n a) = 0 := by
    rw [ρ.comm X n (n + 1) a, (hBasic S I X n).2.1 x a hRep (n + 1), map_zero]
  obtain ⟨β, hβ⟩ := (hConc R J X n (ρ.app X n a)).1 hcl
  have himg : ρ.IsImage α.1 β.1 := by
    intro p s h U y
    cases p with
    | zero =>
      have hs : n = s := by omega
      subst hs
      rw [hβ.1 U y, hα.1 U y]
      exact ρ.nat y n a
    | succ p =>
      rw [hβ.2 p s h U y, hα.2 p s h U y, map_zero]
  refine ⟨β, ?_, ?_⟩
  · rw [← hOp S R I J ρ (sch.obj X) n α β himg, hmk]
  · rw [hβ.1 X (𝟙 X)]
    change ((J.X n).obj.map (𝟙 (op X))).hom (ρ.app X n a) = ρ.app X n a
    rw [CategoryTheory.Functor.map_id]
    rfl

end GlobalTheory.CompanionTheory.EdgeRep
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.ResSplitProof

theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  have h := φ.hom.naturality g.op
  exact congrArg (fun k => ModuleCat.Hom.hom k x) h

theorem resSplit : CrystallineSemistableComparison.E.ResLoc → CrystallineSemistableComparison.E.LocSplit → CrystallineSemistableComparison.E.LcCover → CrystallineSemistableComparison.E.ResSplit := by
  intro hRL hLS hLC R _ F U hU s x
  constructor
  · intro hx
    obtain ⟨ι, f, hf⟩ := hLS U hU _ (hRL R F s U x hx)
    obtain ⟨W, j, hj, -, -, hglue⟩ := hLC U ι f
    have hP : ∀ a, ∃ y, Sec.map ((GlobalTheory.EtC.res R F).d (↑s) (↑(s + 1))) y = Sec.res (j a) x :=
      fun a => hf (W a) (j a) a (hj a)
    choose y hy using hP
    obtain ⟨z, hz, -⟩ := hglue R _ y
    obtain ⟨w, -, huniq⟩ := hglue R _ (fun a => Sec.res (j a) x)
    refine ⟨z, ?_⟩
    have h1 := huniq (Sec.map ((GlobalTheory.EtC.res R F).d (↑s) (↑(s + 1))) z)
      (fun a => by rw [← map_res, hz a, hy a])
    have h2 := huniq x (fun a => rfl)
    exact h1.trans h2.symm
  · rintro ⟨y, rfl⟩
    have h := (GlobalTheory.EtC.res R F).d_comp_d (↑s) (↑(s + 1)) (↑(s + 1 + 1))
    calc Sec.map ((GlobalTheory.EtC.res R F).d (↑(s + 1)) (↑(s + 1 + 1)))
          (Sec.map ((GlobalTheory.EtC.res R F).d (↑s) (↑(s + 1))) y)
        = Sec.map ((GlobalTheory.EtC.res R F).d (↑s) (↑(s + 1)) ≫ (GlobalTheory.EtC.res R F).d (↑(s + 1)) (↑(s + 1 + 1))) y := rfl
      _ = Sec.map 0 y := by rw [h]
      _ = 0 := by first | rfl | simp [Sec.map]

end GlobalTheory.CompanionTheory.ResSplitProof
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeRes

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.map φ (Sec.res g y) = Sec.res g (Sec.map φ y) := by
  have h := φ.hom.naturality g.op
  exact congrArg (fun f => f.hom y) h

theorem resGood : CrystallineSemistableComparison.E.KapSpec → CrystallineSemistableComparison.E.KapBij → CrystallineSemistableComparison.E.ResZero → CrystallineSemistableComparison.E.ResSplit → CrystallineSemistableComparison.E.ResGood := by
  intro hS hB hZ hX hgen q _ C _ P i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c c' φ x
    have h1 := (hS q i (P.U c) (P.ζ c) x).2.2 (P.U c') (P.S.map φ).unop
    rw [P.ζ_nat φ] at h1
    have h2 := sec_map_res (resι _ (tw q i)) (P.S.map φ).unop (kap i (P.ζ c) x)
    rw [h1] at h2
    exact h2
  · intro s c c' φ x
    exact sec_map_res ((GlobalTheory.EtC.res _ (tw q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) (P.S.map φ).unop x
  · intro c a b h
    exact (hB hgen q i (P.U c) (P.ζ c)).1 ((hZ _ (tw q i) (P.U c)).1 h)
  · intro c y
    have h := (hZ _ (tw q i) (P.U c)).2.1 y
    constructor
    · intro h0
      obtain ⟨t, ht⟩ := h.1 h0
      obtain ⟨f, hf⟩ := (hB hgen q i (P.U c) (P.ζ c)).2 t
      exact ⟨f, by rw [← ht, ← hf]; rfl⟩
    · rintro ⟨f, rfl⟩
      exact h.2 ⟨_, rfl⟩
  · intro s c
    exact hX _ (tw q i) (P.U c) (P.split c) s

end GlobalTheory.CompanionTheory.EdgeRes
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.StairAdd

theorem stAdd : CrystallineSemistableComparison.E.StAdd := by
  intro R _ C _ F T j z z' s
  induction s with
  | zero =>
    intro k x x' hx hx'
    obtain ⟨h, rfl⟩ := hx
    obtain ⟨h', rfl⟩ := hx'
    subst h
    exact ⟨⟨rfl, by simp⟩, ⟨rfl, by simp⟩⟩
  | succ s ih =>
    intro k x x' hx hx'
    obtain ⟨a, rfl, ha⟩ := hx
    obtain ⟨a', rfl, ha'⟩ := hx'
    obtain ⟨h1, h2⟩ := ih (k + 1) _ _ ha ha'
    refine ⟨⟨a + a', by simp, ?_⟩, ⟨a - a', by simp, ?_⟩⟩
    · simpa [map_add (f := _), smul_add] using h1
    · simpa [map_sub, smul_sub] using h2

end GlobalTheory.CompanionTheory.StairAdd
end
