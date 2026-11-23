module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsBasisVerticalDerivations
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentGroupPullbackEpsilonLift
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatTrans

section Pull

variable {X Y Z : Scheme.{0}}

theorem pbT_pbT (T : Z ⟶ Y) (S : Y ⟶ X) {O₀ : X.Opens} {O₁ : Y.Opens} {O₂ : Z.Opens} (h₁ : O₁ ≤ S ⁻¹ᵁ O₀)
    (h₂ : O₂ ≤ T ⁻¹ᵁ O₁) (s : Γ(X, O₀)) : pbT T (pbT S s O₁) O₂ = pbT (T ≫ S) s O₂ := by
  rw [GlobalTheory.KS.pbT_of_le S h₁, GlobalTheory.KS.pbT_of_le T h₂, GlobalTheory.KS.pbT_of_le (T ≫ S) (h₂.trans (T.preimage_mono h₁))]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_comp_appLE T S O₀ O₁ O₂ h₁ h₂)

theorem pbT_id {O₀ O : Z.Opens} (h : O ≤ O₀) (s : Γ(Z, O₀)) : pbT (𝟙 Z) s O = rsT s O := by
  rw [GlobalTheory.KS.pbT_of_le (𝟙 Z) h, GlobalTheory.KS.rsT_of_le h]
  simp [Scheme.Hom.appLE]
  rfl

theorem pbT_pow (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) (s : Γ(Y, O₀)) (k : ℕ) :
    pbT f (s ^ k) O = pbT f s O ^ k := by
  rw [GlobalTheory.KS.pbT_of_le f h, GlobalTheory.KS.pbT_of_le f h, map_pow]

end Pull

def conjF {Z : Scheme.{0}} (T S : Z ⟶ Z) (d : Fld Z) : Fld Z :=
  fun O f => pbT T (d (S ⁻¹ᵁ O) (pbT S f (S ⁻¹ᵁ O))) O

section Tr

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G]

def tr (x : 𝟙_ (Over (Sp R)) ⟶ G) : G.left ⟶ G.left := (𝟙 G * (toUnit G ≫ x)).left

theorem tr_over (x : 𝟙_ (Over (Sp R)) ⟶ G) : (𝟙 G * (toUnit G ≫ x)) ≫ (𝟙 G * (toUnit G ≫ x⁻¹)) = 𝟙 G := by
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique ((𝟙 G * (toUnit G ≫ x)) ≫ toUnit G) (toUnit G),
    _root_.mul_assoc, ← MonObj.comp_mul, _root_.mul_inv_cancel, MonObj.comp_one, _root_.mul_one]

theorem tr_tr_inv (x : 𝟙_ (Over (Sp R)) ⟶ G) : tr G x ≫ tr G x⁻¹ = 𝟙 _ := by
  rw [tr, tr, ← Over.comp_left, tr_over]; rfl

theorem tr_inv_tr (x : 𝟙_ (Over (Sp R)) ⟶ G) : tr G x⁻¹ ≫ tr G x = 𝟙 _ := by
  have := tr_tr_inv G x⁻¹
  rwa [inv_inv] at this

theorem tr_hom (x : 𝟙_ (Over (Sp R)) ⟶ G) : tr G x ≫ G.hom = G.hom := by
  rw [tr]; exact (Over.w _)

end Tr

section Field

variable {Z : Scheme.{0}}

theorem rsT_natCast {O₀ O : Z.Opens} (h : O ≤ O₀) (m : ℕ) : rsT (m : Γ(Z, O₀)) O = m := by
  rw [GlobalTheory.KS.rsT_of_le h, map_natCast]

theorem rsT_ofNat {O₀ O : Z.Opens} (h : O ≤ O₀) (m : ℕ) [m.AtLeastTwo] :
    rsT (OfNat.ofNat m : Γ(Z, O₀)) O = OfNat.ofNat m := by
  rw [GlobalTheory.KS.rsT_of_le h, map_ofNat]

theorem rsT_pow {O₀ O : Z.Opens} (h : O ≤ O₀) (s : Γ(Z, O₀)) (m : ℕ) : rsT (s ^ m) O = rsT s O ^ m := by
  rw [GlobalTheory.KS.rsT_of_le h, GlobalTheory.KS.rsT_of_le h, map_pow]

theorem op_rsT {R : Type} [CommRing R] (G : Over (Sp R)) {n : ℕ} (dd : Fin n → Fld G.left)
    (hdd : ∀ a, IsField ⊤ (dd a)) (Θ : Matrix (Fin n) (Fin n) R) (u : Fin n → R) {W : G.left.Opens} (d : Fld G.left)
    (hd : IsField W d) (p p' : Γ(G.left, W)) (k : ℕ) {O O' : G.left.Opens} (h : O' ≤ O) (hO : O ≤ W)
    (f : Γ(G.left, O)) : op G dd Θ u d p p' k O' (rsT f O') = rsT (op G dd Θ u d p p' k O f) O' := by
  have e1 : ∀ a (g : Γ(G.left, O)), dd a O' (rsT g O') = rsT (dd a O g) O' := fun a g => by
    rw [GlobalTheory.KS.rsT_of_le h, GlobalTheory.KS.rsT_of_le h]; exact (hdd a).2.2 O O' h le_top g
  have e2 : ∀ g : Γ(G.left, O), d O' (rsT g O') = rsT (d O g) O' := fun g => by
    rw [GlobalTheory.KS.rsT_of_le h, GlobalTheory.KS.rsT_of_le h]; exact hd.2.2 O O' h hO g
  simp only [op, GlobalTheory.KS.rsT_add, GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_mul, GlobalTheory.KS.rsT_sum, e1, e2,
    GlobalTheory.KS.rsT_constFn _ h, GlobalTheory.KS.rsT_rsT hO h, rsT_natCast h, rsT_ofNat h, rsT_pow h]

end Field

section Conj

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]

theorem isLift_conjF (D : R → R) {T S : G.left ⟶ G.left} (hTS : T ≫ S = 𝟙 _) (hST : S ≫ T = 𝟙 _)
    (hT : T ≫ G.hom = G.hom) (hS : S ≫ G.hom = G.hom) {W : G.left.Opens} {d : Fld G.left} (hl : IsLift G D W d) :
    IsLift G D (T ⁻¹ᵁ W) (conjF T S d) := by
  have hpre : ∀ U : G.left.Opens, S ⁻¹ᵁ (T ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hST]; rfl
  have hpre' : ∀ U : G.left.Opens, T ⁻¹ᵁ (S ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hTS]; rfl
  have hSO : ∀ O, O ≤ T ⁻¹ᵁ W → S ⁻¹ᵁ O ≤ W := fun O hO => (S.preimage_mono hO).trans (hpre W).le
  have back : ∀ (O : G.left.Opens) (f : Γ(G.left, O)), pbT T (pbT S f (S ⁻¹ᵁ O)) O = f := fun O f => by
    rw [pbT_pbT T S le_rfl (hpre' O).ge, hTS, pbT_id le_rfl, GlobalTheory.KS.rsT_self]
  refine ⟨⟨fun O hO f f' => ?_, fun O hO f f' => ?_, fun O O' hle hO f => ?_⟩, fun O hO r => ?_⟩
  · simp only [conjF]
    rw [GlobalTheory.KS.pbT_add, hl.1.1 _ (hSO O hO), GlobalTheory.KS.pbT_add]
  · simp only [conjF]
    rw [GlobalTheory.KS.pbT_mul, hl.1.2.1 _ (hSO O hO), GlobalTheory.KS.pbT_add, GlobalTheory.KS.pbT_mul, GlobalTheory.KS.pbT_mul, back, back]
  · simp only [conjF]
    have hS' : S ⁻¹ᵁ O' ≤ S ⁻¹ᵁ O := S.preimage_mono hle
    rw [← GlobalTheory.KS.rsT_of_le hle, ← GlobalTheory.KS.rsT_of_le hle, GlobalTheory.KS.pbT_rsT S hle le_rfl,
      ← GlobalTheory.KS.rsT_pbT S le_rfl hS', GlobalTheory.KS.rsT_of_le hS', hl.1.2.2 _ _ hS' (hSO O hO), ← GlobalTheory.KS.rsT_of_le hS',
      GlobalTheory.KS.pbT_rsT T hS' (hpre' O').ge, GlobalTheory.KS.rsT_pbT T (hpre' O).ge hle]
  · simp only [conjF]
    rw [GlobalTheory.KS.pbT_constFn _ S le_rfl, hS, hl.2 _ (hSO O hO), GlobalTheory.KS.pbT_constFn _ T (hpre' O).ge, hT]

end Conj

section OpConj

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]

theorem pbT_natCast {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) (m : ℕ) :
    pbT f (m : Γ(Y, O₀)) O = m := by
  rw [GlobalTheory.KS.pbT_of_le f h, map_natCast]

theorem pbT_ofNat {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) (m : ℕ)
    [m.AtLeastTwo] : pbT f (OfNat.ofNat m : Γ(Y, O₀)) O = OfNat.ofNat m := by
  rw [GlobalTheory.KS.pbT_of_le f h, map_ofNat]

theorem op_conjF {n : ℕ} (dd : Fin n → Fld G.left) {T S : G.left ⟶ G.left} (hTS : T ≫ S = 𝟙 _) (hST : S ≫ T = 𝟙 _)
    (hT : T ≫ G.hom = G.hom)
    (hdd : ∀ a (O O' : G.left.Opens), O' ≤ T ⁻¹ᵁ O → ∀ f : Γ(G.left, O), dd a O' (pbT T f O') = pbT T (dd a O f) O')
    (Θ : Matrix (Fin n) (Fin n) R) (u : Fin n → R) (d : Fld G.left) {W : G.left.Opens} (p p' : Γ(G.left, W)) (k : ℕ)
    {O : G.left.Opens} (hO : O ≤ T ⁻¹ᵁ W) (f : Γ(G.left, O)) :
    op G dd Θ u (conjF T S d) (pbT T p (T ⁻¹ᵁ W)) (pbT T p' (T ⁻¹ᵁ W)) k O f =
      pbT T (op G dd Θ u d p p' k (S ⁻¹ᵁ O) (pbT S f (S ⁻¹ᵁ O))) O := by
  have hpre : ∀ U : G.left.Opens, S ⁻¹ᵁ (T ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hST]; rfl
  have hpre' : ∀ U : G.left.Opens, T ⁻¹ᵁ (S ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hTS]; rfl
  have hOO : O ≤ T ⁻¹ᵁ (S ⁻¹ᵁ O) := (hpre' O).ge
  have hSO : S ⁻¹ᵁ O ≤ W := (S.preimage_mono hO).trans (hpre W).le
  have back : pbT T (pbT S f (S ⁻¹ᵁ O)) O = f := by
    rw [pbT_pbT T S le_rfl hOO, hTS, pbT_id le_rfl, GlobalTheory.KS.rsT_self]
  have e : ∀ a (X : Γ(G.left, S ⁻¹ᵁ O)), pbT T (dd a (S ⁻¹ᵁ O) X) O = dd a O (pbT T X O) :=
    fun a X => (hdd a _ _ hOO X).symm
  have ep : ∀ q : Γ(G.left, W), pbT T (rsT q (S ⁻¹ᵁ O)) O = rsT (pbT T q (T ⁻¹ᵁ W)) O := fun q => by
    rw [GlobalTheory.KS.pbT_rsT T hSO hOO, GlobalTheory.KS.rsT_pbT T le_rfl hO]
  simp only [op, conjF, GlobalTheory.KS.pbT_add, GlobalTheory.KS.pbT_sub, GlobalTheory.KS.pbT_mul, GlobalTheory.KS.pbT_sum, e, ep, back,
    GlobalTheory.KS.pbT_constFn _ T hOO, hT, pbT_natCast T hOO, pbT_ofNat T hOO, pbT_pow T hOO]

end OpConj

section Ray

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem tr_q (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) : tr Y.H x ≫ Y.q.left = Y.q.left ≫ tr Q.P.A (x ≫ Y.q) := by
  have := Y.q_linear.isMonHom
  have e : (𝟙 Y.H * (toUnit Y.H ≫ x)) ≫ Y.q = Y.q ≫ (𝟙 Q.P.A * (toUnit Q.P.A ≫ x ≫ Y.q)) := by
    rw [MonObj.mul_comp, MonObj.comp_mul, Category.id_comp, Category.comp_id, ← Category.assoc, ← Category.assoc,
      toUnit_unique (Y.q ≫ toUnit Q.P.A) (toUnit Y.H), Category.assoc]
  exact congrArg CommaMorphism.left e

theorem preimage_tr_q (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (V : Q.P.A.left.Opens) :
    tr Y.H x ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V) = Y.q.left ⁻¹ᵁ (tr Q.P.A (x ≫ Y.q) ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, tr_q, Scheme.Hom.comp_preimage]

end Ray

end GlobalTheory.HeatTrans
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.VertCoeffRing

open TrivSqZeroExt (inl inr)

theorem existsUnique_coeff_alg {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) {dd : Fin n → Fld G.left}
    (hdd : ∀ (B : Type) [CommRing B] [Algebra R B] (e : Fin n → B) (he : ∀ i j, e i * e j = 0)
      (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O),
      ∃ h' : ⊤ ≤ (GlobalTheory.SqZero.lieExp v e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
        evalPt _ O h' f = evalPt z.left O h f + ∑ i, e i * evalPt z.left O h (dd i O f))
    {C : Type} [CommRing C] [Algebra R C] (y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) C ⟶ G)
    {V : G.left.Opens} (hV : IsAffineOpen V) (h : ⊤ ≤ y.left ⁻¹ᵁ V) (δ : Γ(G.left, V) → C)
    (hadd : ∀ f f', δ (f + f') = δ f + δ f')
    (hmul : ∀ f f', δ (f * f') = evalPt y.left V h f * δ f' + evalPt y.left V h f' * δ f)
    (hbase : ∀ r, δ (constFn G.hom V r) = 0) :
    ∃! c : Fin n → C, ∀ f, δ f = ∑ a, c a * evalPt y.left V h (dd a V f) := by
  let z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (DualNumber C) ⟶ G :=
    ReciprocityTheory.ChartRestriction.G.Chart.spMap (TrivSqZeroExt.inlAlgHom R C C) ≫ y
  have hz : ⊤ ≤ z.left ⁻¹ᵁ V := fun t _ => h (Set.mem_univ _)
  have ez : ∀ s, evalPt z.left V hz s = inl (evalPt y.left V h s) := fun s =>
    evalPt_spMap_comp (TrivSqZeroExt.inlAlgHom R C C).toRingHom y.left V h hz s
  obtain ⟨ψ, hψ⟩ := GlobalTheory.InvFieldBasis.exists_dualHom (evalPt y.left V h) δ hadd hmul
  obtain ⟨x, hx, ex⟩ := exists_evalPt_eq hV ψ
  have hxp : x ≫ G.hom = (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (DualNumber C)).hom := by
    refine (eq_spMap_of_evalPt _ (algebraMap R (DualNumber C)) fun a => ?_).trans rfl
    rw [← evalPt_constFn G.hom x V hx, ex, hψ, hbase, evalPt_constFn G.hom y.left V h a,
      GlobalTheory.InvFieldBasis.evalPt_congr (Over.w y) ⊤ le_rfl le_rfl]
    have e2 : evalPt (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) C).hom ⊤ le_rfl
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = algebraMap R C a :=
      evalPt_spMap (algebraMap R C) a
    rw [e2, TrivSqZeroExt.inr_zero, add_zero]
    exact (TrivSqZeroExt.algebraMap_eq_inl' R C C _).symm
  let w : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (DualNumber C) ⟶ G := Over.homMk x hxp
  have ext : ∀ {B : Type} [CommRing B] [Algebra R B] (u u' : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G),
      u.left = u'.left → u = u' := fun u u' e => Over.OverMorphism.ext e
  let fstR : DualNumber C →ₐ[R] C := TrivSqZeroExt.fstHom R C C
  let J : Ideal (DualNumber C) := RingHom.ker fstR
  have memJ : ∀ a : DualNumber C, a ∈ J ↔ a.fst = 0 := fun a => RingHom.mem_ker
  have hJ : J ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff]
    refine Ideal.mul_le.2 fun a ha b hb => ?_
    rw [Ideal.mem_bot]
    have ea : a = inr a.snd := TrivSqZeroExt.ext ((memJ a).1 ha) rfl
    have eb : b = inr b.snd := TrivSqZeroExt.ext ((memJ b).1 hb) rfl
    rw [ea, eb, TrivSqZeroExt.inr_mul_inr]
  let g : C →ₐ[R] DualNumber C ⧸ J := (Ideal.Quotient.mkₐ R J).comp (TrivSqZeroExt.inlAlgHom R C C)
  have hg : Ideal.Quotient.mkₐ R J = g.comp fstR := by
    refine AlgHom.ext fun a => ?_
    change Ideal.Quotient.mk J a = Ideal.Quotient.mk J (inl a.fst)
    refine Ideal.Quotient.eq.2 ((memJ _).2 ?_)
    simp
  have t1 : ReciprocityTheory.ChartRestriction.G.Chart.spMap fstR ≫ z = y := by
    rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp]
    have : fstR.comp (TrivSqZeroExt.inlAlgHom R C C) = AlgHom.id R C := AlgHom.ext fun _ => rfl
    rw [this, ReciprocityTheory.ChartRestriction.G.Chart.spMap_id, Category.id_comp]
  have t2 : ReciprocityTheory.ChartRestriction.G.Chart.spMap fstR ≫ w = y := by
    refine ext _ _ ?_
    rw [Over.comp_left]
    have h' : ⊤ ≤ (spMap fstR.toRingHom ≫ x) ⁻¹ᵁ V := fun t _ => hx (Set.mem_univ _)
    refine ext_evalPt hV h' h (RingHom.ext fun f => ?_)
    refine (evalPt_spMap_comp _ x V hx h' f).trans ?_
    rw [ex, hψ]
    exact add_zero _
  have hred : ReciprocityTheory.ChartRestriction.G.Chart.spMap (Ideal.Quotient.mkₐ R J) ≫ z =
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (Ideal.Quotient.mkₐ R J) ≫ w := by
    rw [hg, ← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, Category.assoc, t1, t2]
  obtain ⟨c, hc, hcu⟩ := GlobalTheory.SqZero.existsUnique_eq_lieExp_mul hv hJ hred
  have key : ∀ c' : Fin n → C, (w = GlobalTheory.SqZero.lieExp v (fun i => inr (c' i))
      (fun i => TrivSqZeroExt.inr_mul_inr _ _ _) * z) ↔
      ∀ f, δ f = ∑ a, c' a * evalPt y.left V h (dd a V f) := by
    intro c'
    obtain ⟨h₁, H₁⟩ := hdd (DualNumber C) (fun i => inr (c' i))
      (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _) z V hz
    constructor
    · intro e f
      have := H₁ f
      rw [← GlobalTheory.InvFieldBasis.evalPt_congr (show x = _ from congrArg (fun u => u.left) e) V hx h₁,
        ex, hψ] at this
      simp only [ez] at this
      exact (GlobalTheory.InvFieldBasis.dual_eq_iff _ _ _ _).1 this
    · intro e
      refine ext _ _ (ext_evalPt hV hx h₁ (RingHom.ext fun f => ?_))
      rw [H₁]
      change evalPt x V hx f = _
      rw [ex, hψ]
      simp only [ez]
      exact (GlobalTheory.InvFieldBasis.dual_eq_iff _ _ _ _).2 (e f)
  have hinr : ∀ a : J, (a : DualNumber C) = inr (a : DualNumber C).snd := fun a =>
    TrivSqZeroExt.ext ((memJ _).1 a.2) rfl
  refine ⟨fun i => (c i : DualNumber C).snd, (key _).1 (hc.trans ?_), fun c' hc' => ?_⟩
  · rw [GlobalTheory.SqZero.lieExp_congr v (fun i => hinr (c i)) _ (fun i => TrivSqZeroExt.inr_mul_inr _ _ _)]
  · have hmem : ∀ i, inr (c' i) ∈ J := fun i => (memJ _).2 rfl
    have := hcu (fun i => ⟨inr (c' i), hmem i⟩) ((key c').2 hc')
    funext i
    exact congrArg (fun d : Fin n → J => (d i : DualNumber C).snd) this

theorem existsUnique_coeff_affine_ring : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {n : ℕ} (v : Fin n → (epsR R ⟶ G)), IsLieBasis v → ∀ (dd : Fin n → Fld G.left),
    (∀ (B : Type) [CommRing B] [Algebra R B] (e : Fin n → B) (he : ∀ i j, e i * e j = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O),
      ∃ h' : ⊤ ≤ (GlobalTheory.SqZero.lieExp v e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
        GlobalTheory.TangentOrigin.evalPt _ O h' f = GlobalTheory.TangentOrigin.evalPt z.left O h f + ∑ i, e i * GlobalTheory.TangentOrigin.evalPt z.left O h (dd i O f)) →
    ∀ (V V' : G.left.Opens), IsAffineOpen V → IsAffineOpen V' → V' ≤ V → ∀ (δ : Γ(G.left, V) → Γ(G.left, V')),
    (∀ f f', δ (f + f') = δ f + δ f') → (∀ f f', δ (f * f') = rsT f V' * δ f' + rsT f' V' * δ f) →
    (∀ r, δ (constFn G.hom V r) = 0) →
    ∃! c : Fin n → Γ(G.left, V'), ∀ f, δ f = ∑ a, c a * rsT (dd a V f) V' := by
  intro R _ G _ _ _ n v hv dd hdd V V' hV hV' hle δ hadd hmul hbase
  obtain ⟨t, ht, et⟩ := exists_evalPt_eq (R := Γ(G.left, V')) hV' (RingHom.id _)
  letI : Algebra R Γ(G.left, V') := (Spec.preimage (t ≫ G.hom)).hom.toAlgebra
  let y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) Γ(G.left, V') ⟶ G :=
    Over.homMk t (Spec.map_preimage (t ≫ G.hom)).symm
  have h : ⊤ ≤ y.left ⁻¹ᵁ V := fun s hs => hle (ht hs)
  have ev : ∀ s, evalPt y.left V h s = rsT s V' := fun s => by
    refine (evalPt_res t hle h ht s).symm.trans ?_
    rw [et, GlobalTheory.KS.rsT, dite_eq_left hle]
    rfl
  have := existsUnique_coeff_alg hv hdd y hV h δ hadd (by simpa only [ev] using hmul) hbase
  simpa only [ev] using this

end GlobalTheory.VertCoeffRing
end
end

section

open GlobalTheory.Poinc
open Classical

namespace GlobalTheory.UPoinc

theorem classSum_norm_eq_of_unique_least : ∀ (p : ℕ) [Fact p.Prime] (X Y : Type) [AddCommGroup X] [AddCommGroup Y] (e : X ≃+ Y) (β : LinearMap.BilinForm ℤ X) (be : LinearMap.BilinForm ℤ Y) (sc sc' : ℝ), 0 < sc → (∀ a b, sc * (β a b : ℝ) = sc' * (be (e a) (e b) : ℝ)) → ∀ (m : ℕ) (t : Y → PadicAlgCl p), (∀ μ, ‖t μ‖ ≤ Real.exp (-(sc' * (be μ μ : ℝ) / 2))) → ∀ (v : PadicAlgCl p) (ν : Y), (∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset Y, ∀ S : Finset Y, (∀ μ ∈ S, CongMod m μ ν) → (∀ μ ∈ S₀, CongMod m μ ν → μ ∈ S) → ‖v - ∑ μ ∈ S, t μ‖ ≤ δ) → ∀ μ : X, CongMod m (e μ) ν → ‖t (e μ)‖ = Real.exp (-(sc' * (be (e μ) (e μ) : ℝ) / 2)) → (∀ μ' : X, CongMod m μ' μ → μ' ≠ μ → β μ μ < β μ' μ') → ‖v‖ = Real.exp (-(sc * (β μ μ : ℝ)) / 2) := by
  intro p _ X Y _ _ e β be sc sc' hsc hid m t ht v ν hv μ hμν htμ hmin
  have hR' : ‖t (e μ)‖ = Real.exp (-(sc * (β μ μ : ℝ)) / 2) := by
    rw [htμ, hid μ μ]; congr 1; ring
  have hlt1 : Real.exp (-(sc * ((β μ μ : ℝ) + 1)) / 2) < Real.exp (-(sc * (β μ μ : ℝ)) / 2) :=
    Real.exp_lt_exp.2 (by nlinarith)
  have hbound : ∀ y : Y, CongMod m y ν → y ≠ e μ →
      ‖t y‖ ≤ Real.exp (-(sc * ((β μ μ : ℝ) + 1)) / 2) := by
    intro y h1 h2
    obtain ⟨w1, hw1⟩ := h1
    obtain ⟨w2, hw2⟩ := hμν
    have hx : CongMod m (e.symm y) μ := by
      refine ⟨e.symm (w1 - w2), ?_⟩
      apply e.injective
      rw [e.apply_symm_apply, map_add (f := _), map_nsmul, e.apply_symm_apply, hw1, hw2, smul_sub]
      abel
    have hne : e.symm y ≠ μ := by
      intro h; apply h2; rw [← h, e.apply_symm_apply]
    have hlt := Int.add_one_le_of_lt (hmin (e.symm y) hx hne)
    have hle : (β μ μ : ℝ) + 1 ≤ (β (e.symm y) (e.symm y) : ℝ) := by exact_mod_cast hlt
    calc ‖t y‖ ≤ Real.exp (-(sc' * (be y y : ℝ) / 2)) := ht y
      _ = Real.exp (-(sc * (β (e.symm y) (e.symm y) : ℝ)) / 2) := by
          have h3 := hid (e.symm y) (e.symm y)
          rw [e.apply_symm_apply] at h3
          rw [h3]; congr 1; ring
      _ ≤ Real.exp (-(sc * ((β μ μ : ℝ) + 1)) / 2) := Real.exp_le_exp.2 (by nlinarith)
  have hRpos : 0 < Real.exp (-(sc * (β μ μ : ℝ)) / 2) := Real.exp_pos _
  obtain ⟨S₀, hS₀⟩ := hv (Real.exp (-(sc * (β μ μ : ℝ)) / 2) / 2) (by positivity)
  have hSc : ∀ x ∈ insert (e μ) (S₀.filter (fun x => CongMod m x ν)), CongMod m x ν := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hμν
    · exact (Finset.mem_filter.1 hx).2
  have hclose := hS₀ (insert (e μ) (S₀.filter (fun x => CongMod m x ν))) hSc
    (fun x hx hc => Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hx, hc⟩))
  set S := insert (e μ) (S₀.filter (fun x => CongMod m x ν)) with hSdef
  have hsum : ∑ x ∈ S, t x = t (e μ) + ∑ x ∈ S.erase (e μ), t x :=
    (Finset.add_sum_erase S t (Finset.mem_insert_self _ _)).symm
  have hrest : ‖∑ x ∈ S.erase (e μ), t x‖ ≤ Real.exp (-(sc * ((β μ μ : ℝ) + 1)) / 2) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.exp_pos _).le
    intro x hx
    exact hbound x (hSc x (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx)
  have hnS : ‖∑ x ∈ S, t x‖ = Real.exp (-(sc * (β μ μ : ℝ)) / 2) := by
    rw [hsum, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hR']; linarith), hR']
    exact max_eq_left (by linarith)
  have hv' : v = (v - ∑ x ∈ S, t x) + ∑ x ∈ S, t x := by abel
  rw [hv', IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hnS]; linarith), hnS]
  exact max_eq_right (by linarith)

end GlobalTheory.UPoinc
end

section

open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem det_eq_one_of_congMod (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : X ≃+ X) (m : ℕ)
    (hm : 3 ≤ m) (hk : ∀ x, CongMod m (k x) x) :
    LinearMap.det (k.toIntLinearEquiv : X →ₗ[ℤ] X) = 1 := by
  set f : X ≃ₗ[ℤ] X := k.toIntLinearEquiv
  have hu : IsUnit (LinearMap.det (f : X →ₗ[ℤ] X)) := LinearEquiv.isUnit_det' f
  let b := Module.Free.chooseBasis ℤ X
  set M := LinearMap.toMatrix b b (f : X →ₗ[ℤ] X) with hM
  have hdet : M.det = LinearMap.det (f : X →ₗ[ℤ] X) := LinearMap.det_toMatrix b _
  have hmap : (Int.castRingHom (ZMod m)).mapMatrix M = 1 := by
    ext i j
    obtain ⟨w, hw⟩ := hk (b j)
    have hfb : (f : X →ₗ[ℤ] X) (b j) = k (b j) := rfl
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hM, LinearMap.toMatrix_apply, hfb, hw, map_add (f := _), map_nsmul,
      Finsupp.add_apply, Finsupp.smul_apply, b.repr_self, Finsupp.single_apply, Matrix.one_apply]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]
  have hz : ((LinearMap.det (f : X →ₗ[ℤ] X) : ℤ) : ZMod m) = 1 := by
    rw [← hdet]
    have := RingHom.map_det (Int.castRingHom (ZMod m)) M
    rw [hmap, Matrix.det_one] at this
    simpa using this
  rcases Int.isUnit_iff.mp hu with h | h
  · exact h
  · exfalso
    rw [h] at hz
    have h2 : ((2 : ℕ) : ZMod m) = 0 := by
      have e : ((2 : ℕ) : ZMod m) = 1 - ((-1 : ℤ) : ZMod m) := by push_cast; ring
      rw [e, hz, sub_self]
    have hd := (ZMod.natCast_eq_zero_iff 2 m).mp h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

end GlobalTheory.Poinc
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tangent_group_pullback_epsilon_lift : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (x' : Sp (DualNumber K) ⟶ Xo.X) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)), IsGrpPullback A Xo.univ.t.G x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ → ∀ f g k k' : GlobalTheory.DeRham.HdR A, GlobalTheory.DeRham.IsFilLift h f k → GlobalTheory.DeRham.IsFilLift h g k' → ψ f k' + ψ k g = 0 := by
  first | exact @GlobalTheory.KSSym.ks_symm | exact GlobalTheory.KSSym.ks_symm | (intros; apply GlobalTheory.KSSym.ks_symm <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaOneMap_identity_every_normalised_family : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ i, GlobalTheory.OneMapAll.IdentityRow T R κ v₀ i := by
  first | exact @GlobalTheory.OneMapAll.identityRow_of_core | exact GlobalTheory.OneMapAll.identityRow_of_core | (intros; apply GlobalTheory.OneMapAll.identityRow_of_core <;> assumption)
end
