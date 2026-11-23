module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle127
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.CechLine

variable {X : Scheme.{0}} (D : LineData X)

theorem u_self {V : Scheme.{0}} (a : V ⟶ D.Y) (h : a ≫ D.f = a ≫ D.f) : D.u a a h = 1 := by
  have h2 : D.u a a h * D.u a a h = D.u a a h * 1 := by
    rw [mul_one]
    exact D.coc a a a h h
  exact mul_left_cancel h2

theorem u_congr {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y} (ha : a = a') (hb : b = b')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) : D.u a b h = D.u a' b' h' := by
  subst ha
  subst hb
  rfl

def lineFun {V : Scheme.{0}} {k : ℕ} (y : Fin (k + 1) → (V ⟶ D.Y)) (hy : ∀ i j, y i ≫ D.f = y j ≫ D.f) :
    ComposableArrows (SingleObj (GL (Fin 1) Γ(V, ⊤))) k where
  obj _ := SingleObj.star _
  map {i j} _ := Matrix.GeneralLinearGroup.scalar (Fin 1) (D.u (y i) (y j) (hy i j))
  map_id i := by rw [u_self]; exact map_one (Matrix.GeneralLinearGroup.scalar (Fin 1))
  map_comp {i j l} _ _ := by
    rw [SingleObj.comp_as_mul]
    refine Eq.trans ?_ (map_mul (Matrix.GeneralLinearGroup.scalar (Fin 1)) _ _)
    rw [mul_comm, D.coc]

variable {D}

theorem exists_pts (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) :
    ∃ y : Fin (k + 1) → (U ⟶ D.Y), ∃ x h, z = cechPt D.f k x y h := by
  obtain ⟨x, y, h, hz⟩ := (hC D.Y X D.f k U).1 z
  exact ⟨y, x, h, hz⟩

def pts (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) : Fin (k + 1) → (U ⟶ D.Y) :=
  (exists_pts hC z).choose

theorem pts_spec (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) :
    ∃ x h, z = cechPt D.f k x (pts hC z) h := by
  exact (exists_pts hC z).choose_spec

theorem pts_eq (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) (i j : Fin (k + 1)) :
    pts hC z i ≫ D.f = pts hC z j ≫ D.f := by
  obtain ⟨x, h, -⟩ := pts_spec hC z
  exact (h i).trans (h j).symm

theorem pts_cechPt (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ D.Y))
    (h : ∀ i, y i ≫ D.f = x) : pts hC (cechPt D.f k x y h) = y := by
  obtain ⟨x', h', hz⟩ := pts_spec hC (cechPt D.f k x y h)
  exact ((hC D.Y X D.f k U).2.1 _ _ _ _ _ _ hz).symm

theorem pts_res (hC : CechPt) {k : ℕ} {U V : Scheme.{0}} (g : V ⟶ U) (z : Sx (cech D.f) k U) (i : Fin (k + 1)) :
    pts hC (Sx.res g z) i = g ≫ pts hC z i := by
  obtain ⟨x, h, hz⟩ := pts_spec hC z
  have e := ((hC D.Y X D.f k U).2.2 x (pts hC z) h).2.1 V g
  rw [← hz] at e
  rw [e, pts_cechPt]

theorem pts_along (hC : CechPt) {k p : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk k) (i : Fin (p + 1)) :
    pts hC (Sx.along z θ) i = pts hC z (θ.toOrderHom i) := by
  obtain ⟨x, h, hz⟩ := pts_spec hC z
  have e := ((hC D.Y X D.f k U).2.2 x (pts hC z) h).2.2 p θ
  rw [← hz] at e
  rw [e, pts_cechPt]

theorem scalar_map {A B : CommRingCat.{0}} (f : A ⟶ B) (u : (A : Type)ˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.map f.hom.toMonoidHom u) =
      Matrix.GeneralLinearGroup.map f.hom (Matrix.GeneralLinearGroup.scalar (Fin 1) u) := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

variable (D) in
theorem lineFun_res {U V : Scheme.{0}} {k : ℕ} (g : V ⟶ U) (y : Fin (k + 1) → (U ⟶ D.Y))
    (hy : ∀ i j, y i ≫ D.f = y j ≫ D.f) (y' : Fin (k + 1) → (V ⟶ D.Y))
    (hy' : ∀ i j, y' i ≫ D.f = y' j ≫ D.f) (e : ∀ i, y' i = g ≫ y i) :
    lineFun D y' hy' = (show Fin (k + 1) ⥤ (glCat 1).obj Γ(U, ⊤) from lineFun D y hy) ⋙
      ((glCat 1).map (Scheme.Γ.map g.op)).toFunctor := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j _ => ?_)
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  change Matrix.GeneralLinearGroup.scalar (Fin 1) (D.u (y' i) (y' j) (hy' i j)) =
    Matrix.GeneralLinearGroup.map (Scheme.Γ.map g.op).hom
      (Matrix.GeneralLinearGroup.scalar (Fin 1) (D.u (y i) (y j) (hy i j)))
  rw [← scalar_map]
  congr 1
  rw [u_congr D (e i) (e j) (hy' i j) (by rw [Category.assoc, Category.assoc, hy i j]),
    D.nat g (y i) (y j) (hy i j)]
  rfl


variable (D) in
def lineMap (hC : CechPt) : cech D.f ⟶ ofCat (glCat 1) where
  app n :=
    { app := fun U => TypeCat.ofHom fun z =>
        lineFun D (pts hC (show Sx (cech D.f) n.unop.len U.unop from z)) (pts_eq hC _)
      naturality := fun U U' g => by
        ext z
        exact lineFun_res D g.unop _ (pts_eq hC _) _ (pts_eq hC _) (fun i => pts_res hC g.unop _ i) }
  naturality n m θ := by
    ext U z
    change lineFun D (pts hC (Sx.along (show Sx (cech D.f) n.unop.len U.unop from z) θ.unop)) (pts_eq hC _) =
      (SimplexCategory.toCat.map θ.unop).toFunctor ⋙ lineFun D (pts hC (show Sx (cech D.f) n.unop.len U.unop from z)) (pts_eq hC _)
    refine CategoryTheory.Functor.hext (fun _ => rfl) (fun i j p => heq_of_eq ?_)
    exact congrArg (Matrix.GeneralLinearGroup.scalar (Fin 1))
      (u_congr D (pts_along hC _ θ.unop i) (pts_along hC _ θ.unop j) _ _)

theorem lineMap_exists : CrystallineSemistableComparison.E.CechPt → CrystallineSemistableComparison.E.LineMap := by
  intro hC X D
  refine ⟨lineMap D hC, ?_⟩
  unfold CrystallineSemistableComparison.E.LineData.IsMap
  intro V x a h
  have hp := pts_cechPt (D := D) hC x a h
  change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1)
    (D.u (pts hC (cechPt D.f 1 x a h) 0) (pts hC (cechPt D.f 1 x a h) 1) (pts_eq hC _ 0 1))) = _
  rw [u_congr D (congrFun hp 0) (congrFun hp 1) _ ((h 0).trans (h 1).symm)]
  ext
  simp [Matrix.GeneralLinearGroup.scalar]

end GlobalTheory.CompanionTheory.CechLine
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtRoot

open CochainComplex CochainComplex.HomComplex

theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (primRes g ζ) := by
  unfold twGen Sec.res ofRings.sec
  have h := NatTrans.naturality_apply (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) g.op
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Scheme.Γ ⋙ twF q i).obj (op U))
  have h2 : ((Scheme.Γ ⋙ twF q i).map g.op).hom (Submodule.Quotient.mk (Finsupp.single ζ 1)) =
      (Submodule.Quotient.mk (Finsupp.single (primRes g ζ) 1) : (Scheme.Γ ⋙ twF q i).obj (op V)) := by
    simp only [Functor.comp_map, twF, ModuleCat.hom_ofHom]
    erw [Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    unfold primRes
    rw [Scheme.Γ_map_op]
  exact h.symm.trans (congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V))) h2)

theorem resGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (resGen i ζ) = resGen i (primRes g ζ) := by
  unfold resGen
  rw [← twGen_res i g ζ]
  unfold Sec.res Sec.map
  exact (NatTrans.naturality_apply (resι (ZMod q) (tw q i)).hom g.op (twGen i ζ)).symm

theorem repRoot : CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.ResZero → CrystallineSemistableComparison.E.RepRoot := by
  intro hC hZ q i X ζ
  refine ⟨fun V g => ⟨twGen_res i g ζ, resGen_res i g ζ⟩, ?_⟩
  have hd : Sec.map ((res (ZMod q) (tw q i)).d 0 1) (resGen i ζ) = 0 :=
    ((hZ (ZMod q) (tw q i) X).2.1 (resGen i ζ)).mpr ⟨twGen i ζ, rfl⟩
  obtain ⟨α, hα⟩ := (hC (ZMod q) (res (ZMod q) (tw q i)) X 0 (resGen i ζ)).1 hd
  obtain ⟨β, hβ1, hβ2⟩ := GlobalTheory.EtC.pick_spec
    (P := fun c => ∃ α : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res (ZMod q) (tw q i)) 0,
      CohomologyClass.mk α = c ∧
        ∀ (U : Scheme) (x : U ⟶ X), ev (R := ZMod q) (E := sch.obj X) (I := res (ZMod q) (tw q i)) (n := 0) (↑α) 0 0 (by simp) U x = Sec.res x (resGen i ζ))
    ⟨_, α, rfl, hα.1⟩
  unfold CrystallineSemistableComparison.E.Rep GlobalTheory.EtC.rootClass
  refine ⟨β, hβ1, (hβ2 X (𝟙 X)).trans ?_⟩
  unfold Sec.res
  simp

end GlobalTheory.CompanionTheory.EtRoot
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.KapMulE

theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  change ((φ.hom.app (op U) ≫ G.obj.map g.op).hom x) = ((F.obj.map g.op ≫ φ.hom.app (op V)).hom x)
  rw [φ.hom.naturality]

theorem res_kap (hKS : KapSpec) {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤))
    (f : LocallyConstant U (ZMod q)) {V : Scheme.{0}} (k : V ⟶ U) (a : ZMod q) (h : ∀ v : V, f (k v) = a) :
    Sec.res k (Sec.map (resι _ (tw q i)) (kap i ζ f)) =
      (ULift.up a : ULift.{1} (ZMod q)) • resGen i (primRes k ζ) := by
  obtain ⟨h1, -, -⟩ := hKS q i U ζ f
  unfold CrystallineSemistableComparison.E.IsLC at h1
  rw [sec_res_map, h1 V k a h]
  simp only [GlobalTheory.EtC.Sec.map, GlobalTheory.EtC.resGen, map_smul]

theorem kapMul_of : LcCover → RepRoot → KapSpec → KapMul := by
  intro hLC _ hKS hIn
  unfold CrystallineSemistableComparison.E.InTw at hIn
  intro q _ i j U ζ f g
  have hP := hIn q i j
  let fg : LocallyConstant U (ZMod q × ZMod q) :=
    ⟨fun x => (f x, g x), f.isLocallyConstant.prodMk g.isLocallyConstant⟩
  obtain ⟨W, jj, hc, -, -, hglue⟩ := hLC U (ZMod q × ZMod q) fg
  have hpt : ∀ (a : ZMod q × ZMod q) (v : W a), f (jj a v) = a.1 ∧ g (jj a v) = a.2 := by
    intro a v
    have := hc a v
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  obtain ⟨y, -, hy⟩ := hglue (ZMod q) ((res (ZMod q) (tw q (i + j))).X 0)
    (fun a => Sec.res (jj a) (Sec.map (resι (ZMod q) (tw q (i + j))) ((kap (i + j) ζ) (f * g))))
  refine (hy _ fun a => ?_).trans (hy _ fun a => rfl).symm
  rw [(twPair q i j).nat]
  rw [res_kap hKS i ζ f (jj a) a.1 fun v => (hpt a v).1,
    res_kap hKS j ζ g (jj a) a.2 fun v => (hpt a v).2,
    res_kap hKS (i + j) ζ (f * g) (jj a) (a.1 * a.2) fun v => by
      rw [LocallyConstant.mul_apply, (hpt a v).1, (hpt a v).2]]
  rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply, hP (W a) (primRes (jj a) ζ), smul_smul, mul_comm]
  rfl

end GlobalTheory.CompanionTheory.KapMulE
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.KumPowProof

theorem isKum_pow {q : ℕ} {t : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec ((res _ (tw q 1)).X 0) U} (ht : IsKum q t)
    {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (v : (Γ(U, ⊤))ˣ) (k : ℕ) :
    ∀ w : (Γ(U, ⊤))ˣ, (w : Γ(U, ⊤)) = ζ.1 ^ k * v → t U w = t U v + k • resGen 1 ζ := by
  induction k with
  | zero =>
    intro w hw
    rw [pow_zero, one_mul] at hw
    rw [Units.ext hw, zero_smul, add_zero]
  | succ k ih =>
    intro w hw
    have hw' : (w : Γ(U, ⊤)) = ζ.1 * (ζ.1 ^ k * v) := by rw [hw]; ring
    obtain ⟨z, hz⟩ : IsUnit (ζ.1 ^ k * v) := isUnit_of_mul_isUnit_right (hw' ▸ w.isUnit)
    rw [ht.2 U ζ z w (by rw [hw', hz]), ih z hz, succ_nsmul, add_assoc]

theorem res_smap {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun m => m.hom x) h).symm

theorem kumPow : LcCover → RepRoot → KapSpec → PrimAlg → KumPow := by
  intro hL _ hK _ hKum q _ U ζ f r v hr
  have ht : IsKum q (kumT q) := hKum q
  have hq : IsUnit (q : Γ(U, ⊤)) := ζ.2.1
  obtain ⟨W, j, hf, -, -, hG⟩ := hL U (ZMod q) f
  obtain ⟨y, -, huniq⟩ := hG (ZMod q) ((res _ (tw q 1)).X 0) (fun a => Sec.res (j a) (kumT q U (r * v)))
  refine (huniq _ fun a => rfl).trans (huniq _ fun a => ?_).symm
  have hra : (j a).appTop.hom r.val = (primRes (j a) ζ).1 ^ a.val := hr (W a) (j a) a (hf a)
  have hlc : Sec.res (j a) (kap 1 ζ f) = (ULift.up a : ULift.{1} (ZMod q)) • twGen 1 (primRes (j a) ζ) :=
    (hK q 1 U ζ f).1 (W a) (j a) a (hf a)
  have hup : (ULift.up a : ULift.{1} (ZMod q)) = a.val • (1 : ULift.{1} (ZMod q)) :=
    ULift.ext (by change a = a.val • (1 : ZMod q); simp)
  have hsm : Sec.res (j a) (kap 1 ζ f) = a.val • twGen 1 (primRes (j a) ζ) := by
    rw [hlc, hup, smul_assoc, one_smul]
  have hkey := isKum_pow ht (primRes (j a) ζ) (Units.map (j a).appTop.hom.toMonoidHom v) a.val
    (Units.map (j a).appTop.hom.toMonoidHom (r * v)) (by
      change (j a).appTop.hom (r.val * v.val) = _ * (j a).appTop.hom v.val
      rw [map_mul, hra])
  have e1 : Sec.res (j a) (kumT q U (r * v)) = kumT q (W a) (Units.map (j a).appTop.hom.toMonoidHom (r * v)) :=
    ht.1 _ _ (j a) _ hq
  have e2 : Sec.res (j a) (kumT q U v) = kumT q (W a) (Units.map (j a).appTop.hom.toMonoidHom v) :=
    ht.1 _ _ (j a) _ hq
  have e3 : Sec.res (j a) (Sec.map (resι _ (tw q 1)) (kap 1 ζ f)) = a.val • resGen 1 (primRes (j a) ζ) := by
    rw [res_smap, hsm]
    exact map_nsmul _ _ _
  have e0 : Sec.res (j a) (kumT q U v + Sec.map (resι _ (tw q 1)) (kap 1 ζ f)) =
      Sec.res (j a) (kumT q U v) + Sec.res (j a) (Sec.map (resι _ (tw q 1)) (kap 1 ζ f)) := map_add _ _ _
  rw [e0, e1, e2, e3, hkey]

end GlobalTheory.CompanionTheory.KumPowProof
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.CstE.KapRedP

theorem up_smul_eq {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (r : ZMod q) (c : ℕ)
    (h : (c : ZMod q) = r) (m : M) : (ULift.up r : ULift.{1} (ZMod q)) • m = c • m := by
  have e : (ULift.up r : ULift.{1} (ZMod q)) = ((c : ℕ) : ULift.{1} (ZMod q)) := by
    ext; rw [ULift.down_natCast, h]
  rw [e, Nat.cast_smul_eq_nsmul]

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have h := congrArg (fun ψ => ψ.hom x) (φ.hom.naturality g.op)
  exact h.symm

theorem map_nsmul_twGen {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (c : ℕ) :
    Sec.map (resι _ (tw q i)) (c • twGen i ζ) = c • resGen i ζ :=
  map_nsmul _ _ _

theorem kapRed : CrystallineSemistableComparison.E.LcCover → CrystallineSemistableComparison.E.RepRoot → CrystallineSemistableComparison.E.KapSpec → CrystallineSemistableComparison.E.KapRed := by
  intro hLc _ hKap hRed Q q _ _ h i U ζ ξ hξ f
  obtain ⟨W, j, hj, -, -, hG⟩ := hLc U (ZMod Q) f
  refine (hG (ZMod q) ((GlobalTheory.EtC.res _ (tw q i)).X 0)
    (fun a => Sec.res (j a) (Sec.map (resι _ _) (kap i ξ (f.map (ZMod.castHom h (ZMod q))))))).unique
    (fun a => ?_) (fun a => rfl)
  have hξ' : (primRes (j a) ξ).1 = (primRes (j a) ζ).1 ^ (Q / q) := by
    change (j a).appTop.hom ξ.1 = ((j a).appTop.hom ζ.1) ^ (Q / q)
    rw [hξ, map_pow]
  have hL : Sec.res (j a) (kap i ζ f) = a.val • twGen i (primRes (j a) ζ) := by
    rw [(hKap Q i U ζ f).1 (W a) (j a) a (hj a)]
    exact up_smul_eq a a.val (ZMod.natCast_zmod_val a) _
  have hR : Sec.res (j a) (kap i ξ (f.map (ZMod.castHom h (ZMod q)))) = a.val • twGen i (primRes (j a) ξ) := by
    rw [(hKap q i U ξ (f.map (ZMod.castHom h (ZMod q)))).1 (W a) (j a) (ZMod.castHom h (ZMod q) a)
      (fun v => by simp [hj a v])]
    exact up_smul_eq _ a.val (by rw [ZMod.castHom_apply, ZMod.natCast_val]) _
  rw [(redMap Q q i).nat (j a) 0, res_map, res_map, hL, hR, map_nsmul_twGen, map_nsmul_twGen, map_nsmul,
    hRed Q q h i (W a) (primRes (j a) ζ) (primRes (j a) ξ) hξ']

end GlobalTheory.CompanionTheory.CstE.KapRedP
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LcCoverProof

theorem lcCover : CrystallineSemistableComparison.E.LcCover := by
  intro U ι f
  let O : ι → U.Opens := fun a => ⟨f ⁻¹' {a}, f.isLocallyConstant.isOpen_fiber a⟩
  have hcov : iSup O = ⊤ :=
    eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨f x, rfl⟩
  have hval : ∀ (a : ι) (v : (O a).toScheme), f ((O a).ι v) = a := fun a v => v.2
  refine ⟨fun a => (O a).toScheme, fun a => (O a).ι, hval, ?_, ?_, ?_⟩
  · intro V g a hg
    have hr : Set.range g ⊆ Set.range (O a).ι := by
      rintro _ ⟨v, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hg v
    exact ⟨IsOpenImmersion.lift (O a).ι g hr, IsOpenImmersion.lift_fac _ _ _⟩
  · intro x y h
    refine U.sheaf.eq_of_locally_eq' O ⊤ (fun a => homOfLE le_top) hcov.ge x y fun a => ?_
    have e : O a ≤ (O a).ι ''ᵁ ⊤ := by simp
    have hm : U.presheaf.map (homOfLE le_top : O a ⟶ ⊤).op =
        U.presheaf.map (homOfLE (x := (O a).ι ''ᵁ ⊤) le_top).op ≫ U.presheaf.map (homOfLE e).op := by
      rw [← Functor.map_comp]
      rfl
    have := congrArg (U.presheaf.map (homOfLE e).op).hom (h a)
    change (U.presheaf.map (homOfLE le_top : O a ⟶ ⊤).op).hom x =
      (U.presheaf.map (homOfLE le_top : O a ⟶ ⊤).op).hom y
    rw [hm]
    exact this
  · intro R _ G x
    have hG := (isSheaf_iff_isSheaf_of_type _ _).1
      ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 G.property)
    have hS : Sieve.ofArrows (fun a => (O a).toScheme) (fun a => (O a).ι) ∈ Scheme.etaleTopology U :=
      Scheme.zariskiTopology_le_etaleTopology _
        (Scheme.Cover.mem_grothendieckTopology (U.openCoverOfIsOpenCover O hcov))
    have hsf := hG _ hS
    rw [Sieve.ofArrows, ← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff] at hsf
    refine hsf x ?_
    intro a b Z gi gj h
    by_cases hab : a = b
    · subst hab
      have : gi = gj := by rwa [cancel_mono] at h
      rw [this]
    · have hE : IsEmpty Z := ⟨fun z => hab (by
        have h1 := hval a (gi z)
        have h2 := hval b (gj z)
        rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply, h2] at h1
        exact h1.symm)⟩
      have hz := (Sheaf.isTerminalOfBotCover G Z (Scheme.bot_mem_grothendieckTopology Z)).isZero
      have := ModuleCat.subsingleton_of_isZero hz
      exact Subsingleton.elim _ _

end GlobalTheory.CompanionTheory.LcCoverProof
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.TwZeroGen

theorem sec_subsingleton (hLc : LcCover) (V : Scheme.{0}) [IsEmpty V] {R : Type} [CommRing R] (G : Shv R) :
    Subsingleton (Sec G V) := by
  let f : LocallyConstant V Empty :=
    ⟨isEmptyElim, fun s => by rw [Set.eq_empty_of_isEmpty (isEmptyElim ⁻¹' s)]; exact isOpen_empty⟩
  obtain ⟨W, j, -, -, -, hG⟩ := hLc V Empty f
  constructor
  intro a b
  exact (hG R G (fun e => e.elim)).unique (fun e => e.elim) (fun e => e.elim)

private theorem twGen_zero_eq_of_eq_pow {q : ℕ} {V : Scheme.{0}} (η θ : Prim q ↑(V.presheaf.obj (op ⊤)))
    (b : (ZMod q)ˣ) (h : η.1 = θ.1 ^ (b : ZMod q).val) : twGen 0 η = twGen 0 θ := by
  unfold twGen
  congr 1
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨θ, η, b, h, ?_⟩)
  rw [zpow_zero]
  rfl

theorem twZero : RootPow → LcCover → RepRoot → TwZero := by
  intro hR hL hP hIn q _ U ζ ξ
  obtain ⟨f, hf, hu⟩ := (hR q U ζ).2 ξ
  obtain ⟨W, j, hWf, -, -, hG⟩ := hL U (ZMod q) f
  have key : ∀ a, Sec.res (j a) (twGen 0 ζ) = Sec.res (j a) (twGen 0 ξ) := by
    intro a
    rw [((hP q 0 U ζ).1 (W a) (j a)).1, ((hP q 0 U ξ).1 (W a) (j a)).1]
    by_cases ha : IsUnit a
    · symm
      apply twGen_zero_eq_of_eq_pow _ _ ha.unit
      have hpw := hf (W a) (j a) a (hWf a)
      have e : (primRes (j a) ξ).1 = (CommRingCat.Hom.hom (Scheme.Hom.appTop (j a))) ξ.1 := rfl
      rw [IsUnit.unit_spec, e]
      exact hpw
    · haveI : IsEmpty (W a) := ⟨fun v => by
        have hv := hu (j a v)
        rw [hWf a v] at hv
        exact ha hv⟩
      exact (sec_subsingleton hL (W a) (tw q 0)).elim _ _
  obtain ⟨y, -, hy⟩ := hG (ZMod q) (tw q 0) (fun a => Sec.res (j a) (twGen 0 ζ))
  exact (hy _ (fun a => rfl)).trans (hy _ (fun a => (key a).symm)).symm

end GlobalTheory.CompanionTheory.TwZeroGen
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.cup_power_smul : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R)
    (z : CH.Cn (CH.modF A) 2) (a : R) (k : ℕ), cupPowC A (a • z) k = a ^ k • cupPowC A z k := by
  first | exact @GlobalTheory.CompanionTheory.ConePow.cupPowC_smul | exact GlobalTheory.CompanionTheory.ConePow.cupPowC_smul | (intros; apply GlobalTheory.CompanionTheory.ConePow.cupPowC_smul <;> assumption)
end
