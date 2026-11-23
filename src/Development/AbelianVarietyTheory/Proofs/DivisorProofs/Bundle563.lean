module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle510
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle457
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

namespace GlobalTheory.Obs.BC

variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]

theorem isAffine_aff {X : Scheme.{0}} (U : X.affineOpens) : IsAffineOpen U.1 := U.2

def preAff {X₀ X₁ : Scheme.{0}} (pr : X₁ ⟶ X₀) [IsAffineHom pr] : AffOp X₀ ⥤ AffOp X₁ where
  obj U := op ⟨pr ⁻¹ᵁ U.unop.1, (isAffine_aff U.unop).preimage pr⟩
  map a := (homOfLE (pr.preimage_mono (leOfHom a.unop))).op

def natCoef {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F F' : C ⥤ CommAlgCat.{0} R}
    (α : ∀ T, F.obj T →+* F'.obj T) (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b))
    (smul : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b) : CoefMap (RingHom.id R) F F' where
  G := 𝟭 C
  α := α
  naturality := nat
  smul := smul

variable {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}

def prSec (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) (U : X₀.affineOpens) (hU : IsAffineOpen (pr ⁻¹ᵁ U.1)) :
    Sec s₀ U.1 →+* Sec s₁ (pr ⁻¹ᵁ U.1) :=
  GlobalTheory.CechDR.secPull (φ := pr) s₀ s₁ ⟨(⟨pr ⁻¹ᵁ U.1, hU⟩, U), le_rfl⟩

def tensHom (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) (U : X₀.affineOpens) (hU : IsAffineOpen (pr ⁻¹ᵁ U.1)) :
    R₁ ⊗[R₀] Sec s₀ U.1 →ₐ[R₁] Sec s₁ (pr ⁻¹ᵁ U.1) :=
  letI : Algebra R₀ (Sec s₁ (pr ⁻¹ᵁ U.1)) := ((algebraMap R₁ _).comp (algebraMap R₀ R₁)).toAlgebra
  haveI : IsScalarTower R₀ R₁ (Sec s₁ (pr ⁻¹ᵁ U.1)) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  Algebra.TensorProduct.lift (Algebra.ofId R₁ _)
    { prSec w U hU with commutes' := fun r ↦ (semiHom_secPull w (⟨(⟨pr ⁻¹ᵁ U.1, hU⟩, U), le_rfl⟩ : Pair pr)).map_algebraMap r }
    (fun _ _ ↦ Commute.all _ _)

theorem tensHom_tmul (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) (U : X₀.affineOpens)
    (hU : IsAffineOpen (pr ⁻¹ᵁ U.1)) (r : R₁) (b : Sec s₀ U.1) :
    tensHom w U hU (r ⊗ₜ b) = algebraMap R₁ _ r * prSec w U hU b := by
  simp [tensHom, Algebra.ofId_apply]; rfl

variable [IsAffineHom pr]

theorem prSec_res (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) {U V : AffOp X₀} (a : U ⟶ V) (b : Sec s₀ U.unop.1) :
    prSec w V.unop ((isAffine_aff V.unop).preimage pr) (mp (OAff s₀) a b) =
      Sec.res s₁ (pr.preimage_mono (leOfHom a.unop)) (prSec w U.unop ((isAffine_aff U.unop).preimage pr) b) :=
  (pairPull w).naturality (T := op ⟨(⟨pr ⁻¹ᵁ U.unop.1, (isAffine_aff U.unop).preimage pr⟩, U.unop), le_rfl⟩)
    (T' := op ⟨(⟨pr ⁻¹ᵁ V.unop.1, (isAffine_aff V.unop).preimage pr⟩, V.unop), le_rfl⟩)
    (homOfLE (show (⟨(⟨pr ⁻¹ᵁ V.unop.1, (isAffine_aff V.unop).preimage pr⟩, V.unop), le_rfl⟩ : Pair pr) ≤
      ⟨(⟨pr ⁻¹ᵁ U.unop.1, (isAffine_aff U.unop).preimage pr⟩, U.unop), le_rfl⟩ from
        ⟨pr.preimage_mono (leOfHom a.unop), leOfHom a.unop⟩)).op b

def tensCoef (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) :
    CoefMap (RingHom.id R₁) (ext R₁ (OAff s₀)) (preAff pr ⋙ OAff s₁) :=
  natCoef (fun U ↦ (tensHom w U.unop ((isAffine_aff U.unop).preimage pr) : R₁ ⊗[R₀] Sec s₀ U.unop.1 →+* Sec s₁ (pr ⁻¹ᵁ U.unop.1)))
    (fun {U V} a b ↦ by
      change tensHom w V.unop _ (extHom R₁ (mp (OAff s₀) a) b) =
        Sec.res s₁ (pr.preimage_mono (leOfHom a.unop)) (tensHom w U.unop _ b)
      induction b using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul r x =>
        rw [Algebra.TensorProduct.map_tmul, tensHom_tmul, tensHom_tmul, map_mul, AlgHom.id_apply, prSec_res]
        congr 1
        exact ((Sec.res s₁ (pr.preimage_mono (leOfHom a.unop))).commutes r).symm
      | add x y hx hy => simp only [map_add (f := _), hx, hy])
    (fun U r b ↦ map_smul (tensHom w U.unop ((isAffine_aff U.unop).preimage pr)) r b)

variable {Y₀ Y₁ : Scheme.{0}} {pr' : Y₁ ⟶ Y₀} [IsAffineHom pr']

def pairBCObj (pr : X₁ ⟶ X₀) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}
    (e : f₁ ≫ pr = pr' ≫ f₀) (p : Pair f₀) : Pair f₁ :=
  ⟨(⟨pr' ⁻¹ᵁ p.1.1.1, (isAffine_aff p.1.1).preimage pr'⟩,
    ⟨pr ⁻¹ᵁ p.1.2.1, (isAffine_aff p.1.2).preimage pr⟩), by
    change pr' ⁻¹ᵁ p.1.1.1 ≤ f₁ ⁻¹ᵁ pr ⁻¹ᵁ p.1.2.1
    rw [← Scheme.Hom.comp_preimage, e, Scheme.Hom.comp_preimage]
    exact pr'.preimage_mono p.2⟩

def pairBC (pr : X₁ ⟶ X₀) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}
    (e : f₁ ≫ pr = pr' ≫ f₀) : (Pair f₀)ᵒᵖ ⥤ (Pair f₁)ᵒᵖ where
  obj p := op (pairBCObj pr pr' e p.unop)
  map {p q} a := (homOfLE (show pairBCObj pr pr' e q.unop ≤ pairBCObj pr pr' e p.unop from
    Subtype.coe_le_coe.1 (Prod.mk_le_mk.2 ⟨pr'.preimage_mono (Pair.le_fst (leOfHom a.unop)),
      pr.preimage_mono (Pair.le_snd (leOfHom a.unop))⟩))).op

variable {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁}

def tensPair (w' : pr' ≫ t₀ = t₁ ≫ spMap (algebraMap R₀ R₁)) {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}
    (e : f₁ ≫ pr = pr' ≫ f₀) : CoefMap (RingHom.id R₁) (ext R₁ (OPair f₀ t₀)) (pairBC pr pr' e ⋙ OPair f₁ t₁) :=
  natCoef (fun p ↦ (tensCoef w').α ((pairFst f₀).obj p)) (fun a b ↦ (tensCoef w').naturality ((pairFst f₀).map a) b)
    (fun p r b ↦ (tensCoef w').smul ((pairFst f₀).obj p) r b)

end GlobalTheory.Obs.BC
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.DiscCup

theorem sub_zero_full {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have : SimplexCategory.subinterval 0 N h = 𝟙 _ := by
    ext i; simp [SimplexCategory.subinterval]
  simp [Sx.sub, this]

theorem map_fst_sub {F : PSh} {E' : Spc} {N : ℕ} {U : Scheme.{0}} (w : Sx (disc.obj F ⨯ E') N U) (l : ℕ) (h : 0 + l ≤ N) :
    (show F.obj (op U) from Sx.map (prod.fst : disc.obj F ⨯ E' ⟶ _) (w.sub 0 l h)) =
      (show F.obj (op U) from Sx.map (prod.fst : disc.obj F ⨯ E' ⟶ _) w) := by
  unfold Sx.map Sx.sub
  have h1 := (prod.fst : disc.obj F ⨯ E' ⟶ _).naturality (SimplexCategory.subinterval 0 l h).op
  have h2 := congrArg (fun φ => φ.app (op U)) h1
  simp only [NatTrans.comp_app] at h2
  exact (congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)) h2) w)

theorem ev_vanish {E : Spc} {R : Type} [CommRing R] {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (hv : α.v (-(p : ℤ)) s h = 0) (U : Scheme.{0}) (x : Sx E p U) : _root_.GlobalTheory.EtC.ev (R := R) α p s h U x = 0 := by
  rw [_root_.GlobalTheory.EtC.ev, hv, comp_zero]
  rfl

end GlobalTheory.EtC.DiscCup

namespace GlobalTheory.EtC.DiscCup

theorem term_zero {q : ℕ} {E₁ E₂ : Spc} {i₁ i₂ n m s : ℤ} (k : ℕ)
    (a : Cochain ((chains (ZMod q)).obj E₁) (res (ZMod q) (tw q i₁)) n)
    (b : Cochain ((chains (ZMod q)).obj E₂) (res (ZMod q) (tw q i₂)) m) (V : Scheme.{0})
    (p : ℕ) (hp : p = 0) (s₁ t₁ : ℤ) (hs₁ : -(p : ℤ) + n = s₁) (ht₁ : -((k - p : ℕ) : ℤ) + m = t₁) (hw : s₁ + t₁ = s)
    (x0 : Sx E₁ p V) (x1 : Sx E₂ (k - p) V) (y0 : Sx E₁ 0 V) (y1 : Sx E₂ k V)
    (h0 : ∀ e : p = 0, e ▸ x0 = y0) (h1 : ∀ e : k - p = k, e ▸ x1 = y1) (hs' : n + (-(k : ℤ) + m) = s) :
    (twPair q i₁ i₂).mul V s₁ t₁ s hw (_root_.GlobalTheory.EtC.ev (R := ZMod q) a p s₁ hs₁ V x0) (_root_.GlobalTheory.EtC.ev (R := ZMod q) b (k - p) t₁ ht₁ V x1) =
      (twPair q i₁ i₂).mul V n (-(k : ℤ) + m) s hs' (_root_.GlobalTheory.EtC.ev (R := ZMod q) a 0 n (by simp) V y0) (_root_.GlobalTheory.EtC.ev (R := ZMod q) b k (-(k : ℤ) + m) rfl V y1) := by
  subst hp
  have e0 := h0 rfl
  have e1 := h1 rfl
  subst e0 e1
  obtain rfl : s₁ = n := by omega
  subst ht₁
  rfl

end GlobalTheory.EtC.DiscCup

open GlobalTheory.EtC.DiscCup in
theorem GlobalTheory.EtC.disc_cup_fibre : ∀ (q N : ℕ) (F : PSh) {n m i₁ i₂ : ℤ} (α : Cocycle ((chains (ZMod q)).obj (disc.obj F)) (res (ZMod q) (tw q i₁)) n) (z : Cocycle ((chains (ZMod q)).obj (fibQ q N)) (res (ZMod q) (tw q i₂)) m), (∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), α.1.v (-(p : ℤ)) s h = 0) → ∃ γ : Cocycle ((chains (ZMod q)).obj (disc.obj F ⨯ fibQ q N)) (res (ZMod q) (tw q (i₁ + i₂))) (n + m), CohomologyClass.mk γ = cup q (pull _ (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (CohomologyClass.mk α)) (pull _ (prod.snd : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (CohomologyClass.mk z)) ∧ ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + (n + m) = s) (V : Scheme.{0}) (w : Sx (disc.obj F ⨯ fibQ q N) k V), _root_.GlobalTheory.EtC.ev (R := ZMod q) γ.1 k s hs V w = (twPair q i₁ i₂).mul V n (-(k : ℤ) + m) s (by omega) (_root_.GlobalTheory.EtC.ev (R := ZMod q) α.1 0 n (by simp) V (show Sx (disc.obj F) 0 V from Sx.map (p := k) (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) w)) (_root_.GlobalTheory.EtC.ev (R := ZMod q) z.1 k (-(k : ℤ) + m) rfl V (Sx.map prod.snd w)) := by
  intro q N F n m i₁ i₂ α z hα
  let α' := zcomp (Cocycle.ofHom ((chains (ZMod q)).map (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _))) α (zero_add n)
  let z' := zcomp (Cocycle.ofHom ((chains (ZMod q)).map (prod.snd : disc.obj F ⨯ fibQ q N ⟶ _))) z (zero_add m)
  obtain ⟨γ, hγ⟩ := (twPair q i₁ i₂).aw_exists (disc.obj F ⨯ fibQ q N) rfl α' z'
  refine ⟨γ, ((twPair q i₁ i₂).cup_spec _ rfl α' z' γ hγ).symm, ?_⟩
  intro k s hs V w
  rw [hγ k s hs V w, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
  · have e1 : ((m * (((0 : Fin (k + 1)) : ℕ) : ℤ)).negOnePow) = 1 := by simp
    rw [e1, one_smul]
    change (twPair q i₁ i₂).mul V _ _ s _ (_root_.GlobalTheory.EtC.ev (R := ZMod q) ((Cochain.ofHom _).comp α.1 (zero_add n)) _ _ rfl V _)
      (_root_.GlobalTheory.EtC.ev (R := ZMod q) ((Cochain.ofHom _).comp z.1 (zero_add m)) _ _ rfl V _) = _
    rw [CupSpec.ev_pull, CupSpec.ev_pull]
    apply term_zero k α.1 z.1 V _ (by simp)
    · intro e
      exact map_fst_sub w _ _
    · intro e
      exact congrArg (Sx.map prod.snd) (sub_zero_full w _)
  · intro i _
    change _ • (twPair q i₁ i₂).mul V _ _ s _ (_root_.GlobalTheory.EtC.ev (R := ZMod q) ((Cochain.ofHom _).comp α.1 (zero_add n)) _ _ rfl V _) _ = 0
    rw [CupSpec.ev_pull, ev_vanish α.1 (i.succ : ℕ) _ _ (hα _ (by simp) _ _), map_zero, LinearMap.zero_apply, smul_zero]
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwMulOrder

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_bind {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} {Q : Scheme.{0} → Prop} (h : Loc U P)
    (hPQ : ∀ V (g : V ⟶ U), P V g → Loc V fun W _ => Q W) : Loc U fun W _ => Q W := by
  obtain ⟨S, hS, hP⟩ := h
  choose T hT hQ using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => hPQ V g (hP V g hg)
  refine ⟨Sieve.bind S.arrows (fun ⦃V⦄ ⦃g⦄ hg => T V g hg), ?_, ?_⟩
  · exact GrothendieckTopology.bind_covering _ hS (fun ⦃V⦄ ⦃g⦄ hg => hT V g hg)
  · rintro W _ ⟨V, k, g, hg, hk, -⟩
    exact hQ V g hg W k hk

def pgen (q : ℕ) (i : ℤ) {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤)) : (Scheme.Γ ⋙ twF q i).obj (op V) :=
  Submodule.Quotient.mk (Finsupp.single ζ 1)

theorem pgen_map (q : ℕ) (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    ((Scheme.Γ ⋙ twF q i).map g.op).hom (pgen q i ζ) = pgen q i (ζ.map g.appTop.hom) := by
  show Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (q := q) g.appTop.hom) (Finsupp.single ζ 1)) =
    (Submodule.Quotient.mk (Finsupp.single (ζ.map g.appTop.hom) 1) :
      (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q i Γ(V, ⊤))
  rw [Finsupp.mapDomain_single]

theorem twGen_eq (q : ℕ) (i : ℤ) {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤)) :
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom (pgen q i ζ) = twGen i ζ := rfl

theorem twGen_res (q : ℕ) (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    ((tw q i).obj.map g.op).hom (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  have h := congrArg (fun f => f.hom (pgen q i ζ))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [pgen_map] at h
  rw [← twGen_eq, ← twGen_eq]
  exact h.symm

theorem step_point (q : ℕ) [NeZero q] (i j : ℤ) (V : Scheme.{0}) [Nonempty V] (ζ : Prim q Γ(V, ⊤)) (c : ℕ)
    (h : c • (pgen q j ζ ⊗ₜ[ULift.{1} (ZMod q)] pgen q i ζ) = 0) : q ∣ c := by
  haveI : Nonempty (⊤ : V.Opens) := ⟨⟨Classical.arbitrary V, trivial⟩⟩
  haveI : Nontrivial Γ(V, ⊤) := Scheme.component_nontrivial V ⊤
  obtain ⟨fj, hfj⟩ := (GlobalTheory.TwFree.twist_free q j Γ(V, ⊤)).2 ζ
  obtain ⟨fi, hfi⟩ := (GlobalTheory.TwFree.twist_free q i Γ(V, ⊤)).2 ζ
  let fj' : (Scheme.Γ ⋙ twF q j).obj (op V) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) := fj
  let fi' : (Scheme.Γ ⋙ twF q i).obj (op V) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) := fi
  have e1 : fj' (pgen q j ζ) = 1 := hfj
  have e2 : fi' (pgen q i ζ) = 1 := hfi
  have h2 : (TensorProduct.lid (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q)))
      (TensorProduct.map fj' fi' (c • (pgen q j ζ ⊗ₜ[ULift.{1} (ZMod q)] pgen q i ζ))) = 0 := by
    rw [h, map_zero, map_zero]
  rw [map_nsmul, map_nsmul, TensorProduct.map_tmul, e1, e2, TensorProduct.lid_tmul, one_smul] at h2
  have h3 : ((c : ZMod q)) = 0 := by
    have := congrArg ULift.down h2
    simpa using this
  exact (ZMod.natCast_eq_zero_iff c q).1 h3

theorem step_swap (q : ℕ) [NeZero q] (i j : ℤ) (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)) (c : ℕ)
    (h : c • (twGen i ζ ⊗ₜ[ULift.{1} (ZMod q)] pgen q j ζ) = 0) : Loc V fun W _ => Nonempty W → q ∣ c := by
  have hφ := toSheafify_loc_bij_lift (ZMod q) (Scheme.Γ ⋙ twF q i)
  have key := (tensor_loc_bij (ZMod q) (Scheme.Γ ⋙ twF q j) (Scheme.Γ ⋙ twF q i) _
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) hφ.1 hφ.2.1 V).2
    (c • (pgen q j ζ ⊗ₜ pgen q i ζ)) (by
      rw [map_nsmul, LinearMap.lTensor_tmul, twGen_eq]
      have := congrArg (TensorProduct.comm _ _ _) h
      rwa [map_nsmul, TensorProduct.comm_tmul, map_zero] at this)
  refine loc_mono key ?_
  intro W g hg hW
  rw [map_nsmul, TensorProduct.map_tmul, pgen_map, pgen_map] at hg
  exact step_point q i j W (ζ.map g.appTop.hom) c hg

theorem tw_mul_order : ∀ (q : ℕ) [NeZero q] (i j : ℤ) (W : Scheme.{0}) (ζ : Prim q Γ(W, ⊤)) (c : ℕ),
    c • (twGen i ζ ⊗ₜ[ULift.{1} (ZMod q)] twGen j ζ) = 0 → Loc W fun V _ => Nonempty V → q ∣ c := by
  intro q _ i j W ζ c h
  have hφ := toSheafify_loc_bij_lift (ZMod q) (Scheme.Γ ⋙ twF q j)
  have key := (tensor_loc_bij (ZMod q) (tw q i).obj (Scheme.Γ ⋙ twF q j) _
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q j)) hφ.1 hφ.2.1 W).2
    (c • (twGen i ζ ⊗ₜ pgen q j ζ)) (by rw [map_nsmul, LinearMap.lTensor_tmul, twGen_eq]; exact h)
  refine loc_bind key fun V g hg => step_swap q i j V (ζ.map g.appTop.hom) c ?_
  rw [map_nsmul, TensorProduct.map_tmul, pgen_map, twGen_res] at hg
  exact hg

end GlobalTheory.TwMulOrder

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.TensZero

variable {R : Type} [CommRing R]

theorem sec_eq_zero_of_isZero {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (a : Sec F U) : a = 0 := by
  have h : 𝟙 F = 0 := hF.eq_of_src _ _
  have : Sec.map (𝟙 F) a = Sec.map (0 : F ⟶ F) a := by rw [h]
  have h1 : Sec.map (𝟙 F) a = a := rfl
  have h2 : Sec.map (0 : F ⟶ F) a = 0 := by
    simp only [Sec.map]
    rfl
  rw [h1, h2] at this
  exact this

theorem isZero_of_sec {F : Shv R} (h : ∀ (U : Scheme.{0}) (a : Sec F U), a = 0) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  refine ((GlobalTheory.EtC.mono_epi_sections R (𝟙 F)).2.2.2 0 fun U a => ?_)
  rw [h U a]
  simp

theorem tens_eq_zero {I J : Cx R} (hI : ∀ s : ℤ, s ≠ 0 → IsZero (I.X s)) (hJ : ∀ t : ℤ, t ≠ 0 → IsZero (J.X t))
    (U : Scheme.{0}) (w : ℤ) (hw : w ≠ 0) (x : Tens I J U w) : x = 0 := by
  refine DFinsupp.ext fun p => ?_
  show x p = 0
  have hp := p.2
  by_cases h1 : p.1.1 = 0
  · have h2 : p.1.2 ≠ 0 := by omega
    induction x p using TensorProduct.induction_on with
    | zero => rfl
    | tmul a b => rw [sec_eq_zero_of_isZero (hJ _ h2) b, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  · induction x p using TensorProduct.induction_on with
    | zero => rfl
    | tmul a b => rw [sec_eq_zero_of_isZero (hI _ h1) a, TensorProduct.zero_tmul]
    | add a b ha hb => rw [ha, hb, add_zero]

end GlobalTheory.EtC.TensZero

open GlobalTheory.EtC.TensZero in
theorem GlobalTheory.EtC.isZero_tensor_of_deg_zero : ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor →
    (∀ s : ℤ, s ≠ 0 → IsZero (I.X s)) → (∀ t : ℤ, t ≠ 0 → IsZero (J.X t)) → ∀ w : ℤ, w ≠ 0 → IsZero (K.X w) := by
  intro R _ I J K τ hτ hI hJ w hw
  refine isZero_of_sec fun U y => ?_
  refine (GlobalTheory.EtC.sec_ext_glue R (K.X w) U).1 y 0 ?_
  obtain ⟨S, hS, hP⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hP V g hg
  rw [tens_eq_zero hI hJ V w hw x, map_zero] at hx
  rw [← hx]
  exact (map_zero _).symm
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.TensFam

variable {R : Type} [CommRing R]

theorem tensRes_id (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens.res (I := I) (J := J) (𝟙 U) w = LinearMap.id := by
  classical
  apply DirectSum.linearMap_ext
  intro p
  apply TensorProduct.ext'
  intro a b
  simp [Tens.res, DirectSum.lmap_lof]

theorem tensRes_comp (I J : Cx R) {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (w : ℤ) :
    Tens.res (I := I) (J := J) (f ≫ g) w = (Tens.res f w).comp (Tens.res g w) := by
  classical
  apply DirectSum.linearMap_ext
  intro p
  apply TensorProduct.ext'
  intro a b
  simp [Tens.res, DirectSum.lmap_lof]

theorem lift_resL {I J K : Cx R} (τ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    (τ.lift V w).comp (Tens.res g w) = ((K.X w).obj.map g.op).hom.comp (τ.lift U w) := by
  classical
  apply DirectSum.linearMap_ext
  intro p
  apply TensorProduct.ext'
  intro a b
  have := τ.nat g p.1.1 p.1.2 w p.2 a b
  simp [Tens.res, Pair.lift, DirectSum.lmap_lof] at this ⊢
  exact this.symm

def tensP (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1} where
  obj U := AddCommGrpCat.of (Tens I J U.unop w)
  map g := AddCommGrpCat.ofHom (Tens.res g.unop w).toAddMonoidHom
  map_id U := by
    apply AddCommGrpCat.ext; intro x
    change Tens.res (I := I) (J := J) (𝟙 U.unop) w x = x
    rw [tensRes_id]; rfl
  map_comp f g := by
    apply AddCommGrpCat.ext; intro x
    change Tens.res (I := I) (J := J) (g.unop ≫ f.unop) w x = Tens.res g.unop w (Tens.res f.unop w x)
    rw [tensRes_comp]; rfl

def secP (F : Shv R) : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1} := F.obj ⋙ forget₂ _ AddCommGrpCat

def liftP {I J K : Cx R} (τ : Pair I J K) (w : ℤ) : tensP I J w ⟶ secP (K.X w) where
  app U := AddCommGrpCat.ofHom (τ.lift U.unop w).toAddMonoidHom
  naturality V U g := by
    apply AddCommGrpCat.ext; intro x
    exact LinearMap.congr_fun (lift_resL τ g.unop w) x

end GlobalTheory.EtC.TensFam


open GlobalTheory.EtC.TensFam in
theorem GlobalTheory.EtC.tens_fam : ∀ (R S : Type) [CommRing R] [CommRing S] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ (w : ℤ) (M : Shv S) (b : ∀ U : Scheme.{0}, Tens I J U w →+ Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V (Tens.res g w x)) → ∃ φ : ∀ U : Scheme.{0}, Sec (K.X w) U →+ Sec M U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y)) ∧ ∀ U x, φ U (τ.lift U w x) = b U x := by
  intro R S _ _ I J K τ hτ w M b hb
  exact GlobalTheory.T.etaleSheaf_descend_along_locallyBijective S (tensP I J w) (secP (K.X w)) (liftP τ w)
    (fun U y => hτ.1 U w y) (fun U x hx => hτ.2 U w x hx) M b hb
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.locally_equal_or_unit : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) (e u : A' ⊗[A] A'), (∀ a : A', (a ⊗ₜ[A] (1 : A') - (1 : A') ⊗ₜ[A] a) * e = 0) → algebraMap A (A' ⊗[A] A') f * u = 1 - e → ∀ (T : Scheme.{0}) (y y' : T ⟶ Spec (CommRingCat.of A')), y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A')) = y' ≫ Spec.map (CommRingCat.ofHom (algebraMap A A')) → Loc T fun V k => k ≫ y = k ≫ y' ∨ IsUnit (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (k ≫ y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))).appTop).hom f) := by
  first | (exact @GlobalTheory.EtC.PairDich.pair_dich) | (exact GlobalTheory.EtC.PairDich.pair_dich) | (intros; apply GlobalTheory.EtC.PairDich.pair_dich  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u) := by
  first | (exact @GlobalTheory.EtC.PrimLoc.prim_loc) | (exact GlobalTheory.EtC.PrimLoc.prim_loc) | (intros; apply GlobalTheory.EtC.PrimLoc.prim_loc  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.RootLoc

theorem root_loc_pow_prim : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ ω : (Γ(U, ⊤))ˣ, ω ^ q = 1 →
    Loc U fun V g => ∃ (ζ : Prim q Γ(V, ⊤)) (a : ℕ), (Units.map g.appTop.hom.toMonoidHom ω : Γ(V, ⊤)) = ζ.1 ^ a := by
  intro q _ U hq ω hω
  apply GlobalTheory.EtC.loc_trans
  refine GlobalTheory.EtC.loc_mono _ _ _ ((PrimLoc.prim_loc q U).1 hq) ?_
  rintro V g ⟨ζ⟩
  have hx : (g.appTop.hom (ω : Γ(U, ⊤))) ^ q = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hω, Units.val_one, map_one]
  refine GlobalTheory.EtC.loc_mono _ _ _ ((PrimLoc.prim_loc q V).2.2.1 ζ _ hx) ?_
  rintro W k ⟨a, ha⟩
  refine ⟨ζ.map k.appTop.hom, a, ?_⟩
  rw [Units.coe_map]
  exact (PrimLoc.appTop_comp g k _).trans ha

end GlobalTheory.EtC.RootLoc
end
