module

public import Development.EtaleCohomology.EtaleSheaves.Bundle053
public import Mathlib.Tactic.ENatToNat
public import Development.EtaleCohomology.EtaleSheaves.Bundle054
public import Development.EtaleCohomology.EtaleSheaves.Bundle055
public import Development.EtaleCohomology.EtaleSheaves.Bundle029
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open Polynomial LateralTheory.E.PartDiagCut GlobalTheory.EtC

namespace LateralTheory.E.PartCPf

def Split : Prop := ∀ (B : Type) [CommRing B] [IsDomain B] (I : Ideal B), AIC B →
  ∀ (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (p : Polynomial (PiLocalization₂ I P)), p.Monic →
    ∃ (n : ℕ) (r : Fin n → PiLocalization₂ I P), p = ∏ l, (X - C (r l))

def Idem : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (n : ℕ) (y : Fin n → PiLocalization₂ I P),
  ∏ l, y l ∈ I.map (βP I P) →
  IsUnit (Ideal.Quotient.mk (I.map (βP I P)) (∑ l, ∏ m ∈ Finset.univ.erase l, y m)) →
  ∃ f : Fin n → B, (∀ l, IsIdempotentElem (Ideal.Quotient.mk I (f l))) ∧
    (∀ l m, l ≠ m → Ideal.Quotient.mk I (f l) * Ideal.Quotient.mk I (f m) = 0) ∧
    ∑ l, Ideal.Quotient.mk I (f l) = 1 ∧ ∀ l, βP I P (f l) * y l ∈ I.map (βP I P)

def Lift : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (p : Polynomial (PiLocalization₂ I P)) (a₀ : PiLocalization₂ I P)
  (n : ℕ) (r : Fin n → PiLocalization₂ I P) (f : Fin n → B), p = ∏ l, (X - C (r l)) →
  (∀ l, IsIdempotentElem (Ideal.Quotient.mk I (f l))) →
  (∀ l m, l ≠ m → Ideal.Quotient.mk I (f l) * Ideal.Quotient.mk I (f m) = 0) →
  ∑ l, Ideal.Quotient.mk I (f l) = 1 → (∀ l, βP I P (f l) * (a₀ - r l) ∈ I.map (βP I P)) →
  ∃ (Q : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (h : P ≤ Q) (a : PiLocalization₂ I Q), (p.map (stageMap I h)).IsRoot a ∧
    a - stageMap I h a₀ ∈ I.map (βP I Q)

theorem eval_prod_lin {R : Type} [CommRing R] (n : ℕ) (r : Fin n → R) (x : R) :
    (∏ l, (X - C (r l))).eval x = ∏ l, (x - r l) := by
  simp [eval_prod]

theorem deriv_prod_lin {R : Type} [CommRing R] (n : ℕ) (r : Fin n → R) (x : R) :
    (derivative (∏ l, (X - C (r l)))).eval x = ∑ l, ∏ m ∈ Finset.univ.erase l, (x - r m) := by
  classical
  rw [derivative_prod_finset]
  simp [eval_finsetSum, eval_prod]

theorem PartC_of (hs : Split) (hi : Idem) (hl : Lift) : LateralTheory.E.PartDiagCut.PartC := by
  intro B _ _ I hB P p a₀ hm hev hder
  obtain ⟨n, r, hp⟩ := hs B I hB P p hm
  have h1 : ∏ l, (a₀ - r l) ∈ I.map (βP I P) := by
    rw [← eval_prod_lin n r a₀, ← hp]; exact hev
  have h2 : IsUnit (Ideal.Quotient.mk (I.map (βP I P)) (∑ l, ∏ m ∈ Finset.univ.erase l, (a₀ - r m))) := by
    rw [← deriv_prod_lin n r a₀, ← hp]; exact hder
  obtain ⟨f, hfi, hfo, hfs, hfy⟩ := hi B I P n (fun l => a₀ - r l) h1 h2
  exact hl B I P p a₀ n r f hp hfi hfo hfs hfy

theorem idem_of (hIP : LateralTheory.E.HensCut.IdemPart) (hA : LateralTheory.E.PartDiagCut.PartA) : Idem := by
  intro B _ I P n y hprod hsum
  let φ := RingEquiv.ofBijective (Ideal.quotientMap (I.map (βP I P)) (βP I P) Ideal.le_comap_map) (hA B I P)
  obtain ⟨e, hei, heo, hes, hey⟩ := hIP (PiLocalization₂ I P ⧸ I.map (βP I P)) n
    (fun l => Ideal.Quotient.mk (I.map (βP I P)) (y l))
    (by rw [← map_prod]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hprod)
    (by simpa [map_sum, map_prod] using hsum)
  choose f hf using fun l => Ideal.Quotient.mk_surjective (φ.symm (e l))
  refine ⟨f, fun l => ?_, fun l m hlm => ?_, ?_, fun l => ?_⟩
  · unfold IsIdempotentElem; rw [hf, ← map_mul, (hei l).eq]
  · rw [hf, hf, ← map_mul, heo l m hlm, map_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp_rw [hf]; rw [← map_sum, hes, map_one]
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    have h1 : φ (Ideal.Quotient.mk I (f l)) = e l := by rw [hf]; exact φ.apply_symm_apply _
    have h2 : Ideal.Quotient.mk (I.map (βP I P)) (βP I P (f l)) = e l := by
      rw [← h1]; simp [φ, Ideal.quotientMap_mk]
    rw [h2]; exact hey l

theorem PartC_of' (hs : Split) (hIP : LateralTheory.E.HensCut.IdemPart) (hA : LateralTheory.E.PartDiagCut.PartA) (hl : Lift) :
    LateralTheory.E.PartDiagCut.PartC :=
  PartC_of hs (idem_of hIP hA) hl

end LateralTheory.E.PartCPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing LateralTheory.E.StdChartsProof

namespace LateralTheory.E.ChartsGeom_vpaPf

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

def chartEquiv {Z : Scheme.{0}} {U : Z.Opens} (φ : Γ(Z, U) →+* K) (hi : Function.Injective φ) (B : Subalgebra A K)
    (hr : φ.range = B.toSubring) : Γ(Z, U) ≃+* B :=
  (RingEquiv.ofBijective φ.rangeRestrict ⟨fun a b h => hi (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩).trans
    (RingEquiv.subringCongr hr)

theorem chartEquiv_apply {Z : Scheme.{0}} {U : Z.Opens} (φ : Γ(Z, U) →+* K) (hi : Function.Injective φ)
    (B : Subalgebra A K) (hr : φ.range = B.toSubring) (s : Γ(Z, U)) : ((chartEquiv φ hi B hr s : B) : K) = φ s := rfl

def chartMap {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U) (φ : Γ(Z, U) →+* K) (hi : Function.Injective φ)
    (B : Subalgebra A K) (hr : φ.range = B.toSubring) : Spec (CommRingCat.of B) ⟶ Z :=
  Spec.map (CommRingCat.ofHom (chartEquiv φ hi B hr).toRingHom) ≫ hU.fromSpec

instance {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U) (φ : Γ(Z, U) →+* K) (hi : Function.Injective φ)
    (B : Subalgebra A K) (hr : φ.range = B.toSubring) : IsOpenImmersion (chartMap hU φ hi B hr) := by
  unfold chartMap
  have : IsIso (Spec.map (CommRingCat.ofHom (chartEquiv φ hi B hr).toRingHom)) := by
    have : IsIso (CommRingCat.ofHom (chartEquiv φ hi B hr).toRingHom) :=
      (RingEquiv.toCommRingCatIso (chartEquiv φ hi B hr)).isIso_hom
    infer_instance
  infer_instance

theorem chartMap_range {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U) (φ : Γ(Z, U) →+* K)
    (hi : Function.Injective φ) (B : Subalgebra A K) (hr : φ.range = B.toSubring) :
    Set.range (chartMap hU φ hi B hr).base = (U : Set Z) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (chartEquiv φ hi B hr).toRingHom)) := by
    have : IsIso (CommRingCat.ofHom (chartEquiv φ hi B hr).toRingHom) :=
      (RingEquiv.toCommRingCatIso (chartEquiv φ hi B hr)).isIso_hom
    infer_instance
  unfold chartMap
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  rw [Set.range_eq_univ.mpr (Scheme.Hom.surjective _), Set.image_univ]
  exact hU.range_fromSpec

theorem chartMap_comp {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) {U : Z.Opens} (hU : IsAffineOpen U)
    (φ : Γ(Z, U) →+* K) (hi : Function.Injective φ) (B : Subalgebra A K) (hr : φ.range = B.toSubring)
    (hA : ∀ a : A, φ (p.appLE ⊤ U le_top ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) = algebraMap A K a) :
    chartMap hU φ hi B hr ≫ p = Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
  have hp : p = Z.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop) := by
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hr2 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop ≫ Z.presheaf.map (homOfLE le_top : U ⟶ ⊤).op ≫
      CommRingCat.ofHom (chartEquiv φ hi B hr).toRingHom = CommRingCat.ofHom (algebraMap A B) := by
    ext a
    have := hA a
    simp only [Scheme.Hom.appLE, ConcreteCategory.comp_apply] at this
    simp [chartEquiv_apply]
    exact this
  rw [hp, chartMap, Category.assoc, ← Category.assoc hU.fromSpec, IsAffineOpen.fromSpec_toSpecΓ, ← Spec.map_comp,
    ← Spec.map_comp, ← hr2]
  simp only [Category.assoc]

def ChartData {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (B C : Subalgebra A K) (t : K) : Prop :=
  ∃ (U V : Z.Opens) (φU : Γ(Z, U) →+* K) (φV : Γ(Z, V) →+* K) (φW : Γ(Z, U ⊓ V) →+* K),
    IsAffineOpen U ∧ IsAffineOpen V ∧ IsAffineOpen (U ⊓ V) ∧ U ⊔ V = ⊤ ∧
    Function.Injective φU ∧ Function.Injective φV ∧ Function.Injective φW ∧
    φU.range = B.toSubring ∧ φV.range = C.toSubring ∧ φW.range = (AdjoinInv B t).toSubring ∧
    (∀ s, φW (Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s) = φU s) ∧
    (∀ s, φW (Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s) = φV s) ∧
    (∀ a : A, φU (p.appLE ⊤ U le_top ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) = algebraMap A K a) ∧
    (∀ a : A, φV (p.appLE ⊤ V le_top ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) = algebraMap A K a)

def GeoData : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → AICSch Z →
  ∃ (K : Type) (_ : Field K) (_ : Algebra A K) (B C : Subalgebra A K) (t : K), Charts B C t ∧
    (∀ x ∈ B, x ∈ C → IsIntegral A x) ∧ ChartData p B C t

def CoverOfData : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K] [Algebra A K]
  {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (B C : Subalgebra A K) (t : K),
    Charts B C t → ChartData p B C t → Cover p B C t

def Overlap : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K] [Algebra A K]
  {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (B C : Subalgebra A K) (t : K), Charts B C t →
  ∀ (U V : Z.Opens) (φU : Γ(Z, U) →+* K) (φV : Γ(Z, V) →+* K) (φW : Γ(Z, U ⊓ V) →+* K)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V), IsAffineOpen (U ⊓ V) → U ⊔ V = ⊤ →
    ∀ (iU : Function.Injective φU) (iV : Function.Injective φV), Function.Injective φW →
    ∀ (rU : φU.range = B.toSubring) (rV : φV.range = C.toSubring), φW.range = (AdjoinInv B t).toSubring →
    (∀ s, φW (Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s) = φU s) →
    (∀ s, φW (Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s) = φV s) →
    ∀ (x : PrimeSpectrum B) (y : PrimeSpectrum C),
      (chartMap hU φU iU B rU).base x = (chartMap hV φV iV C rV).base y ↔
        ∃ Q : PrimeSpectrum (AdjoinInv B t), Restr B t Q B x ∧ Restr B t Q C y

theorem coverOfData_of (hO : Overlap) : CoverOfData := by
  intro A _ _ K _ _ Z p B C t hc hd
  obtain ⟨U, V, φU, φV, φW, hU, hV, hW, hUV, iU, iV, iW, rU, rV, rW, cU, cV, aU, aV⟩ := hd
  refine ⟨⟨chartMap hU φU iU B rU, chartMap hV φV iV C rV, inferInstance, inferInstance, ?_,
    chartMap_comp p hU φU iU B rU aU, chartMap_comp p hV φV iV C rV aV,
    hO A K p B C t hc U V φU φV φW hU hV hW hUV iU iV iW rU rV rW cU cV⟩⟩
  rw [chartMap_range, chartMap_range, ← TopologicalSpace.Opens.coe_sup, hUV, TopologicalSpace.Opens.coe_top]

theorem ChartsGeom_of' (hG : GeoData) (hC : CoverOfData) : LateralTheory.E.StdChartsProof.ChartsGeom := by
  intro A _ _ Z p hIL hZ
  obtain ⟨K, hK, hA, B, C, t, hc, hint, hd⟩ := hG A p hIL hZ
  exact ⟨K, hK, hA, B, C, t, hc, hint, hC A K p B C t hc hd⟩

end LateralTheory.E.ChartsGeom_vpaPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.TwistTrivial

theorem genRes {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  unfold twGen ofRings.sec
  have h := congrArg (fun φ => φ.hom (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(U, ⊤)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at h
  refine h.symm.trans ?_
  change ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom
    (((Scheme.Γ ⋙ twF q i).map g.op).hom _) = _
  congr 1
  exact congrArg Submodule.Quotient.mk Finsupp.mapDomain_single

theorem prim_map_comp {q : ℕ} {X Y S : Scheme.{0}} (ζ : Prim q Γ(S, ⊤)) (s : X ⟶ S) (f : Y ⟶ X) :
    (ζ.map s.appTop.hom).map f.appTop.hom = ζ.map (f ≫ s).appTop.hom := by
  apply Subtype.ext
  change f.appTop.hom (s.appTop.hom ζ.1) = (f ≫ s).appTop.hom ζ.1
  rw [Scheme.Hom.comp_appTop]
  rfl

def Mul : Prop := ∀ (q : ℕ), ∃ μ : ∀ (j k l : ℤ), j + k = l → ∀ (X : Scheme.{0}), Sec (tw q k) X → (Sec (tw q j) X →+ Sec (tw q l) X),
  (∀ (j k l : ℤ) (h : j + k = l) {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Sec (tw q k) X) (x : Sec (tw q j) X),
      Sec.res f (μ j k l h X y x) = μ j k l h Y (Sec.res f y) (Sec.res f x)) ∧
  (∀ (j k l k' : ℤ) (h : j + k = l) (h' : l + k' = j) (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (x : Sec (tw q j) X),
      μ l k' j h' X (twGen k' ζ) (μ j k l h X (twGen k ζ) x) = x)

theorem TwTriv_of (hM : Mul) : LateralTheory.E.LCIsoPf.TwTriv := by
  intro q i S ζ
  obtain ⟨μ, hnat, hcan⟩ := hM q
  refine ⟨fun X s => AddEquiv.mk' ⟨μ 0 i i (zero_add i) X (twGen i (ζ.map s.appTop.hom)),
      μ i (-i) 0 (add_neg_cancel i) X (twGen (-i) (ζ.map s.appTop.hom)),
      fun x => hcan 0 i i (-i) (zero_add i) (add_neg_cancel i) X _ x,
      fun y => hcan i (-i) 0 i (add_neg_cancel i) (zero_add i) X _ y⟩ (fun a b => map_add (μ 0 i i (zero_add i) X (twGen i (ζ.map s.appTop.hom))) a b), ?_⟩
  intro X Y s t f hf x
  change Sec.res f (μ 0 i i _ X _ x) = μ 0 i i _ Y _ (Sec.res f x)
  rw [hnat, genRes, prim_map_comp, hf]

end LateralTheory.E.TwistTrivial
end
end

section

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC
namespace LateralTheory.E.BinPfChains
variable (R : Type) [CommRing R]
instance freeModPres : PreservesColimitsOfShape (Discrete WalkingPair) (ModuleCat.free.{1} (ULift.{1} R)) := by
  have := (ModuleCat.adj.{1} (ULift.{1} R)).leftAdjoint_preservesColimits
  infer_instance
instance freePres : PreservesColimitsOfShape (Discrete WalkingPair) (free R) := by unfold free freeP; infer_instance
instance whPres : PreservesColimitsOfShape (Discrete WalkingPair) ((SimplicialObject.whiskering PSh (Shv R)).obj (free R)) := by
  change PreservesColimitsOfShape (Discrete WalkingPair) ((Functor.whiskeringRight _ _ _).obj (free R))
  infer_instance
instance chainsPres : PreservesColimitsOfShape (Discrete WalkingPair) (chains R) := by
  unfold chains chainsN; infer_instance
theorem chainsCoprod : LateralTheory.E.BinPf.ChainsCoprod := by
  intro R _ U V
  have h : IsIso (coprodComparison (chains R) U V) := inferInstance
  have e : biprod.desc ((chains R).map (coprod.inl : U ⟶ U ⨿ V)) ((chains R).map (coprod.inr : V ⟶ U ⨿ V)) =
      (biprod.isoCoprod _ _).hom ≫ coprodComparison (chains R) U V := by
    apply biprod.hom_ext' <;> simp [coprodComparison, coprod.inl_desc, coprod.inr_desc]
  rw [e]; infer_instance

theorem bin_of (hD : LateralTheory.E.BinPf.DescEqv) : LateralTheory.E.ProdAcycPf.Bin :=
  LateralTheory.E.ProdAcycPf.Bin_of hD chainsCoprod

end LateralTheory.E.BinPfChains
end
end

section

noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.LZIdemSumNoetherian

def NoetherianLocalChartOverlapFiniteComplement : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : Type) [Field K]
  [Algebra A K] (B C : Subalgebra A K) (t : K), Charts B C t → B.FG → C.FG →
  ∃ N : Submodule A K, N.FG ∧ Subalgebra.toSubmodule (AdjoinInv B t) ≤
    Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C ⊔ N

def LZIdemPow : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K] [Algebra A K]
  (B C : Subalgebra A K) (t : K), Charts B C t → ∀ e f : K, IdemPair B C t e f → ∀ k : ℕ,
  ∃ b ∈ B, ∃ c ∈ C, e - b ∈ mS B ∧ c - f ∈ mS C ∧
    b - c ∈ (IsLocalRing.maximalIdeal A ^ k) • Subalgebra.toSubmodule (AdjoinInv B t)

def LZARStep : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (M : Type) [AddCommGroup M]
  [Module A M] (N P : Submodule A M), N.FG →
  ∃ k : ℕ, 1 ≤ k ∧ (IsLocalRing.maximalIdeal A ^ k) • N ⊓ P ≤ IsLocalRing.maximalIdeal A • P

theorem goal_of (h1 : NoetherianLocalChartOverlapFiniteComplement) (h2 : LZIdemPow) (h3 : LZARStep) :
    LateralTheory.E.IdempotentLiftingAlt.LZIdemSumNoeth := by
  intro A _ _ _ K _ _ B C t hc hB hC e f hp
  obtain ⟨N, hN, hD⟩ := h1 A K B C t hc hB hC
  obtain ⟨k, hk, hAR⟩ := h3 A K N (Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C) hN
  obtain ⟨b, hb, c, hcC, heb, hcf, hbc⟩ := h2 A K B C t hc e f hp k
  have hmk : IsLocalRing.maximalIdeal A ^ k ≤ IsLocalRing.maximalIdeal A := Ideal.pow_le_self (by omega)
  have hbc' := Submodule.smul_mono (le_refl (IsLocalRing.maximalIdeal A ^ k)) hD hbc
  rw [Submodule.smul_sup, Submodule.smul_sup] at hbc'
  obtain ⟨x, hx, n, hn, hxn⟩ := Submodule.mem_sup.mp hbc'
  obtain ⟨β, hβ, γ, hγ, hβγ⟩ := Submodule.mem_sup.mp hx
  have hβB : β ∈ B := Submodule.smul_le_right hβ
  have hγC : γ ∈ C := Submodule.smul_le_right hγ
  have hnP : n ∈ Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C := by
    refine Submodule.mem_sup.mpr ⟨b - β, B.sub_mem hb hβB, -(c + γ), C.neg_mem (C.add_mem hcC hγC), ?_⟩
    linear_combination -hxn - hβγ
  have hnm := hAR ⟨hn, hnP⟩
  rw [Submodule.smul_sup] at hnm
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hnm
  have hβm : β ∈ mS B := Submodule.smul_mono_left hmk hβ
  have hγm : γ ∈ mS C := Submodule.smul_mono_left hmk hγ
  have hum : u ∈ mS B := hu
  have hvm : v ∈ mS C := hv
  refine Submodule.mem_sup.mpr ⟨(e - b) + β + u, (mS B).add_mem ((mS B).add_mem heb hβm) hum,
    γ + v + (c - f), (mS C).add_mem ((mS C).add_mem hγm hvm) hcf, ?_⟩
  linear_combination hxn + hβγ + huv

end LateralTheory.E.LZIdemSumNoetherian
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.D2 LateralTheory.E.LeafGeomPf LateralTheory.E.HalfDegreeVanishing

namespace LateralTheory.E.LeafMapWPf

variable {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b))

theorem pvm_res {n : ℕ} {X Y : Scheme.{0}} (k : Y ⟶ X) (x : Sx (PB (bsumOf V W)) n X) {i j : Fin (n + 1)} (f : i ⟶ j) :
    (((pv V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x)).map f).1.2 : Scheme.Γ.obj (op Y)) =
      Scheme.Γ.map k.op (((pv V W x).map f).1.2 : Scheme.Γ.obj (op X)) := by
  let N := op (SimplexCategory.mk n)
  let projection : (PB (bsumOf V W)).obj N ⟶ (PGL (a + b)).obj N :=
    (pullback.snd (bsumOf V W) (PGL.pr (a + b))).app N
  have h := types_congr_hom (projection.naturality k.op) x
  have h2 := congrArg (fun p => (p.1.2 : Scheme.Γ.obj (op Y))) (Functor.congr_hom h f)
  refine h2.trans ?_
  have h3 := congrArg (fun p => (p.2 : Scheme.Γ.obj (op Y)))
    (um_hom_val (Functor.congr_obj h i) (Functor.congr_obj h j)
      ((((PGL (a + b)).obj N).map k.op (pv V W x)).map f))
  exact h3.trans rfl

theorem pvm_simp {n m : ℕ} {X : Scheme.{0}} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (x : Sx (PB (bsumOf V W)) n X)
    {i j : Fin (m + 1)} (f : i ⟶ j) :
    (((pv V W ((((PB (bsumOf V W)).map θ.op).app (op X)) x)).map f).1.2 : Scheme.Γ.obj (op X)) =
      (((((PGL (a + b)).map θ.op).app (op X)) (pv V W x) : Fin (m + 1) ⥤ Um (a + b) (Scheme.Γ.obj (op X))).map f).1.2 := by
  have h := types_congr_hom
    (NatTrans.congr_app ((pullback.snd (bsumOf V W) (PGL.pr (a + b))).naturality θ.op) (op X)) x
  have h2 := congrArg (fun p => (p.1.2 : Scheme.Γ.obj (op X))) (Functor.congr_hom h f)
  refine h2.trans ?_
  have h3 := congrArg (fun p => (p.2 : Scheme.Γ.obj (op X))) (um_hom_val (Functor.congr_obj h i) (Functor.congr_obj h j) (((ConcreteCategory.hom
      (((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).app (op X) ≫
        (((PGL (a + b)).map θ.op).app (op X)))) x).map f))
  exact h3.trans rfl

theorem pe_simp {n m : ℕ} {X : Scheme.{0}} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (x : Sx (PB (bsumOf V W)) n X) :
    pe V W ((((PB (bsumOf V W)).map θ.op).app (op X)) x) = ((E.map θ.op).app (op X)) (pe V W x) :=
  types_congr_hom
    (NatTrans.congr_app ((pullback.fst (bsumOf V W) (PGL.pr (a + b))).naturality θ.op) (op X)) x

theorem pw_simp {n m : ℕ} {X : Scheme.{0}} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (e : Sx E n X)
    {i j : Fin (m + 1)} (f : i ⟶ j) :
    (show GL (Fin b) (Scheme.Γ.obj (op X)) from (pw W (((E.map θ.op).app (op X)) e)).map f) =
      (show GL (Fin b) (Scheme.Γ.obj (op X)) from
        ((((ofCat (glCat b)).map θ.op).app (op X)) (pw W e) : Fin (m + 1) ⥤ SingleObj (GL (Fin b) (Scheme.Γ.obj (op X)))).map f) :=
  eq_of_heq (Functor.hcongr_hom (types_congr_hom (NatTrans.congr_app (W.naturality θ.op) (op X)) e) f)

def gX (n : SimplexCategoryᵒᵖ) (X : Scheme.{0}ᵒᵖ) (x : ((U2 V W).obj n).obj X) : ((PGL b).obj n).obj X :=
  show Fin (n.unop.len + 1) ⥤ Um b (Scheme.Γ.obj (op X.unop)) from gfun V W x.1 x.2

theorem gX_nat_X (n : SimplexCategoryᵒᵖ) {X Y : Scheme.{0}ᵒᵖ} (k : X ⟶ Y) (x : ((U2 V W).obj n).obj X) :
    gX V W n Y (((U2 V W).obj n).map k x) = ((PGL b).obj n).map k (gX V W n X x) := by
  apply um_functor_ext
  · intro i
    show wb (a := a) ((pv V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n.unop.len))).map k.unop.op x.1)).obj i).1 = _
    rw [pv_res]; rfl
  · intro i j f
    apply Prod.ext
    · show (show GL (Fin b) _ from (pw W (pe V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n.unop.len))).map k.unop.op x.1))).map f) = _
      rw [pe_res, pw_res]; rfl
    · apply Units.ext
      exact pvm_res V W k.unop x.1 f

theorem gX_nat_n {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (X : Scheme.{0}ᵒᵖ) (x : ((U2 V W).obj n).obj X) :
    gX V W m X ((((U2 V W).map θ).app X) x) = (((PGL b).map θ).app X) (gX V W n X x) := by
  apply um_functor_ext
  · intro i
    show wb (a := a) ((pv V W ((((PB (bsumOf V W)).map θ.unop.op).app (op X.unop)) x.1)).obj i).1 = _
    rw [pv_simp]; rfl
  · intro i j f
    apply Prod.ext
    · show (show GL (Fin b) _ from (pw W (pe V W ((((PB (bsumOf V W)).map θ.unop.op).app (op X.unop)) x.1))).map f) = _
      rw [pe_simp, pw_simp]; rfl
    · apply Units.ext
      exact (pvm_simp V W θ.unop x.1 f).trans rfl

def gmap : U2 V W ⟶ PGL b where
  app n :=
    { app := fun X => TypeCat.ofHom (gX V W n X)
      naturality := fun X Y k => by
        ext x
        exact gX_nat_X V W n k x }
  naturality n m θ := by
    ext X x
    exact gX_nat_n V W θ X x

theorem gmap_pr : gmap V W ≫ PGL.pr b = f2 V W ≫ PB.pr _ ≫ W := by
  ext n X x
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j f => ?_)
  erw [Category.id_comp, Category.comp_id]
  rfl

theorem gmap_line : gmap V W ≫ PGL.line b = f2 V W ≫ pullback.snd (bsumOf V W) (PGL.pr (a + b)) ≫ PGL.line (a + b) := by
  ext n X x
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j f => ?_)
  erw [Category.id_comp, Category.comp_id]
  rfl

theorem LeafMapW_of : LateralTheory.E.HalfDegreeVanishing.LeafMapW := fun V W => ⟨gmap V W, gmap_pr V W, gmap_line V W⟩

end LateralTheory.E.LeafMapWPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.StdChartsProof₂

theorem StdCharts_of : LateralTheory.E.StandardEtaleChartsMultivariableHensel.StdCharts := by
  intro A _ _ Z p hp
  obtain ⟨L, u, l, hu, ⟨hl, f, hf⟩, hul⟩ := hp
  have hf' : IsAffineHom f := MorphismProperty.of_isPullback hf.flip inferInstance
  let g : Z ⟶ P1 := u ≫ f
  have hU : ∀ i, IsAffineOpen (g ⁻¹ᵁ LateralTheory.E.ChartsPf.D i) := fun i => (LateralTheory.E.ChartsPf.D_affine i).preimage g
  refine ⟨g ⁻¹ᵁ LateralTheory.E.ChartsPf.D 0, g ⁻¹ᵁ LateralTheory.E.ChartsPf.D 1, (g ⁻¹ᵁ LateralTheory.E.ChartsPf.D 0).ι,
    (g ⁻¹ᵁ LateralTheory.E.ChartsPf.D 1).ι, inferInstance, inferInstance, hU 0, hU 1, ?_, ?_⟩
  · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    have hx : g x ∈ (⨆ i, LateralTheory.E.ChartsPf.D i : P1.Opens) := by rw [LateralTheory.E.ChartsPf.D_cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  · refine ⟨L, u, l, f, hu, hl, hf, hul, ?_, ?_⟩
    · rw [Scheme.Opens.range_ι]; rfl
    · rw [Scheme.Opens.range_ι]; rfl

end LateralTheory.E.StdChartsProof₂
end
end
