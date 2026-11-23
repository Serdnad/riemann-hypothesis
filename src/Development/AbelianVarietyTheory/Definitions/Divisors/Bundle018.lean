module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

abbrev Datum.VQ : Type := ℚ ⊗[ℤ] D.La

instance Datum.finVQ : FiniteDimensional ℚ D.VQ := by
  haveI := D.finLa; infer_instance

def Datum.actQ : D.O →+* Module.End ℚ D.VQ :=
  (Module.End.baseChangeHom ℤ ℚ D.La).toRingHom.comp (Module.toModuleEnd ℤ (S := D.O) D.La)

theorem Datum.actQ_tmul (b : D.O) (q : ℚ) (x : D.La) : D.actQ b (q ⊗ₜ x) = q ⊗ₜ (b • x) := rfl

def Datum.EFQ : LinearMap.BilinForm ℚ D.VQ := D.EF.baseChange ℚ

theorem Datum.EFQ_tmul (q q' : ℚ) (x y : D.La) : D.EFQ (q ⊗ₜ x) (q' ⊗ₜ y) = (D.EF x y : ℚ) * (q * q') := by
  simp [Datum.EFQ, LinearMap.BilinForm.baseChange_tmul, mul_comm]

theorem Datum.EFQ_swap (x y : D.VQ) : D.EFQ y x = - D.EFQ x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']; ring
  | tmul q x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']; ring
    | tmul q' y => rw [D.EFQ_tmul, D.EFQ_tmul, D.EF_swap x y]; push_cast; ring

theorem Datum.EFQ_actQ (b : D.O) (x y : D.VQ) : D.EFQ (D.actQ b x) y = D.EFQ x (D.actQ (D.star b).unop y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']
  | tmul q x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' h h' => simp only [map_add (f := _), h, h']
    | tmul q' y => rw [D.actQ_tmul, D.actQ_tmul, D.EFQ_tmul, D.EFQ_tmul, D.adj]

theorem Datum.exists_tmul (v : D.VQ) : ∃ (q : ℚ) (x : D.La), q ≠ 0 ∧ v = q ⊗ₜ x := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul q x =>
    by_cases h : q = 0
    · exact ⟨1, 0, one_ne_zero, by simp [h]⟩
    · exact ⟨q, x, h, rfl⟩
  | add v v' h h' =>
    obtain ⟨q, x, -, rfl⟩ := h
    obtain ⟨q', x', -, rfl⟩ := h'
    have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    have hd' : (q'.den : ℚ) ≠ 0 := by exact_mod_cast q'.den_ne_zero
    refine ⟨1 / (q.den * q'.den), (q.num * q'.den : ℤ) • x + (q'.num * q.den : ℤ) • x', by positivity, ?_⟩
    rw [TensorProduct.tmul_add, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul]
    congr 2
    · rw [zsmul_eq_mul]; push_cast; conv_lhs => rw [← Rat.num_div_den q]
      field_simp
    · rw [zsmul_eq_mul]; push_cast; conv_lhs => rw [← Rat.num_div_den q']
      field_simp

theorem Datum.eq_zero_of_EFQ {v : D.VQ} (h : ∀ w, D.EFQ v w = 0) : v = 0 := by
  obtain ⟨q, x, hq, rfl⟩ := D.exists_tmul v
  have hx : D.EF x = D.EF 0 := by
    ext y
    have := h (1 ⊗ₜ y)
    rw [D.EFQ_tmul, mul_one] at this
    have h2 : (D.EF x y : ℚ) = 0 := (mul_eq_zero.1 this).resolve_right hq
    simpa using h2
  rw [D.nondeg hx, TensorProduct.tmul_zero]

theorem Datum.EFQ_nondeg : D.EFQ.Nondegenerate :=
  ⟨fun _ h => D.eq_zero_of_EFQ h, fun v h => D.eq_zero_of_EFQ fun w => by rw [D.EFQ_swap, h, neg_zero]⟩

def Datum.adjE (g : Module.End ℚ D.VQ) : Module.End ℚ D.VQ := D.EFQ.leftAdjointOfNondegenerate D.EFQ_nondeg g

theorem Datum.EFQ_adjE_left (g : Module.End ℚ D.VQ) (x y : D.VQ) : D.EFQ (D.adjE g x) y = D.EFQ x (g y) :=
  D.EFQ.isAdjointPairLeftAdjointOfNondegenerate D.EFQ_nondeg g x y

theorem Datum.EFQ_adjE_right (g : Module.End ℚ D.VQ) (x y : D.VQ) : D.EFQ (g x) y = D.EFQ x (D.adjE g y) := by
  rw [D.EFQ_swap y, D.EFQ_swap (D.adjE g y), D.EFQ_adjE_left]

theorem Datum.end_ext {g h : Module.End ℚ D.VQ} (H : ∀ x y, D.EFQ (g x) y = D.EFQ (h x) y) : g = h := by
  refine LinearMap.ext fun x => sub_eq_zero.1 (D.eq_zero_of_EFQ fun y => ?_)
  rw [map_sub, LinearMap.sub_apply, H, sub_self]

theorem Datum.adjE_adjE (g : Module.End ℚ D.VQ) : D.adjE (D.adjE g) = g :=
  D.end_ext fun x y => by rw [D.EFQ_adjE_left, D.EFQ_adjE_right]

theorem Datum.adjE_mul (g h : Module.End ℚ D.VQ) : D.adjE (g * h) = D.adjE h * D.adjE g :=
  D.end_ext fun x y => by simp only [D.EFQ_adjE_left, Module.End.mul_apply]

theorem Datum.adjE_smul (q : ℚ) (g : Module.End ℚ D.VQ) : D.adjE (q • g) = q • D.adjE g :=
  D.end_ext fun x y => by simp only [D.EFQ_adjE_left, LinearMap.smul_apply, map_smul]

theorem Datum.adjE_one : D.adjE 1 = 1 :=
  D.end_ext fun x y => by simp only [D.EFQ_adjE_left, Module.End.one_apply]

theorem Datum.adjE_actQ (b : D.O) : D.adjE (D.actQ b) = D.actQ (D.star b).unop :=
  D.end_ext fun x y => by rw [D.EFQ_adjE_left, D.EFQ_actQ, D.star_star]

def Datum.endO : Subalgebra ℚ (Module.End ℚ D.VQ) := Subalgebra.centralizer ℚ (Set.range D.actQ)

theorem Datum.mem_endO {g : Module.End ℚ D.VQ} : g ∈ D.endO ↔ ∀ b, D.actQ b * g = g * D.actQ b := by
  simp [Datum.endO, Subalgebra.mem_centralizer_iff]

def Datum.actInt : 𝓞 D.F →+* D.endO :=
  (D.actQ.comp (algebraMap (𝓞 D.F) D.O)).codRestrict D.endO fun c => D.mem_endO.2 fun b => by
    rw [RingHom.comp_apply, ← map_mul, ← map_mul, Algebra.commutes]

theorem Datum.coe_actInt (c : 𝓞 D.F) : (D.actInt c : Module.End ℚ D.VQ) = D.actQ (algebraMap (𝓞 D.F) D.O c) := rfl

def Datum.actFL : D.F →ₗ[ℚ] D.endO :=
  (integralBasis D.F).constr ℚ fun i => D.actInt (RingOfIntegers.basis D.F i)

theorem Datum.actFL_coe (c : 𝓞 D.F) : D.actFL (c : D.F) = D.actInt c := by
  have h : (D.actFL.restrictScalars ℤ).comp (algebraMap (𝓞 D.F) D.F).toIntAlgHom.toLinearMap =
      D.actInt.toIntAlgHom.toLinearMap := by
    refine (RingOfIntegers.basis D.F).ext fun i => ?_
    show D.actFL (algebraMap (𝓞 D.F) D.F (RingOfIntegers.basis D.F i)) = D.actInt _
    rw [← integralBasis_apply, Datum.actFL, Module.Basis.constr_basis]
  exact LinearMap.congr_fun h c

def Datum.actF : D.F →ₐ[ℚ] D.endO :=
  AlgHom.ofLinearMap D.actFL (by simpa using D.actFL_coe 1) (by
    refine (LinearMap.map_mul_iff D.actFL).2 ?_
    refine (integralBasis D.F).ext fun i => (integralBasis D.F).ext fun j => ?_
    show D.actFL (integralBasis D.F i * integralBasis D.F j) = D.actFL (integralBasis D.F i) * D.actFL (integralBasis D.F j)
    rw [integralBasis_apply, integralBasis_apply, ← map_mul]
    exact (D.actFL_coe _).trans ((map_mul _ _ _).trans (by rw [← D.actFL_coe, ← D.actFL_coe])))

theorem Datum.actF_coe (c : 𝓞 D.F) : D.actF (c : D.F) = D.actInt c := D.actFL_coe c

end GlobalTheory.UPel.HT
end
end

section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

structure PreEta (b : Base D R) (N : ℕ) (s : S ⟶ Sp R) extends Pre b s where
  eta : D.La → (𝟙_ (Over S) ⟶ A)
  eta_add : ∀ x y, eta (x + y) = eta x * eta y
  eta_lin : ∀ (c : D.O) x, eta (c • x) = eta x ≫ act.act c
  eta_ker : ∀ x, eta (N • x) = 1

def PreEta.GeomAt {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : PreEta b N s) (k : Type) [Field k] (x : Sp k ⟶ S) : Prop :=
  ∃ I : TateIsoO D k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
      (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
    ∀ y, toUnit _ ≫ o.eta y = I.ev N y

end GlobalTheory.UPel.HT
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.Obs.Model

namespace GlobalTheory.LBObs.Model

section Alg

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]
variable {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R₀}

variable (hI : I ^ 2 = 0)




end Alg

section Example

end Example

section Geo

variable {X : Scheme.{0}} {C : Type} [Category.{0} C]

theorem isCoc_of_isFrame {L : LB X} (hL : L.IsLB) {V : C → X.Opens} {hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T}
    {u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ} (h : IsFrame L V hV u) : IsCoc V hV u := by
  obtain ⟨τ, -, h⟩ := h
  intro T T' T'' a b
  have k : ∀ m, res (inf_le_left : V T'' ⊓ L.U m ≤ V T'') (u T T'' (a ≫ b)) =
      res inf_le_left (res (hV b) (u T T' a) * u T' T'' b) := fun m ↦ by
    have e1 := congrArg (res (inf_le_inf_right (L.U m) (hV b))) (h T T' a m)
    rw [map_mul, h T' T'' b m, LB.res_res, LB.res_res, h T T'' (a ≫ b) m, ← mul_assoc] at e1
    rw [map_mul, LB.res_res]
    exact mul_right_cancel e1
  refine Units.ext (X.sheaf.eq_of_locally_eq' (fun m ↦ V T'' ⊓ L.U m) _ (fun m ↦ homOfLE inf_le_left) ?_ _ _
    fun m ↦ congrArg Units.val (k m))
  rw [← inf_iSup_eq, hL.cover, inf_top_eq]

def Ch (L : LB X) : Type := {p : X.affineOpens × L.ι // p.1.1 ≤ L.U p.2}

instance (L : LB X) : Preorder (Ch L) := Preorder.lift fun p ↦ OrderDual.toDual p.1.1

def chG (L : LB X) : Ch L ⥤ AffOp X where
  obj p := Opposite.op p.1.1
  map a := (homOfLE (leOfHom a)).op

theorem isFrame_ch {L : LB X} (hL : L.IsLB) : IsFrame L (opOf (chG L)) (opOf_le (chG L))
    fun T T' a ↦ res (le_inf T'.2 ((opOf_le (chG L) a).trans T.2)) (L.g T'.1.2 T.1.2) := by
  refine ⟨fun T m ↦ res (le_inf inf_le_right (inf_le_left.trans T.2)) (L.g m T.1.2), fun T m m' ↦ ?_,
    fun T T' a m ↦ ?_⟩
  · exact ((LB.res_res _ _ _).trans (LB.res_cocycle hL _ _ _ _ _ _).symm).trans
      (congrArg (_ * ·) (LB.res_res _ _ _).symm)
  · exact (((LB.res_res _ _ _).trans (LB.res_cocycle hL _ _ _ _ _ _).symm).trans
      (congrArg (_ * ·) (LB.res_res _ _ _).symm)).trans (mul_comm _ _)

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]
variable {s₀ : X ⟶ Sp R₀}

end Geo

end GlobalTheory.LBObs.Model
end
end

section

noncomputable section

namespace GlobalTheory.UPel.HT.Gen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R']
  {S S' : Scheme.{0}}

def IsGPull {b : Base D R} {gb : GBase D.toG R'} {N : ℕ} {s' : S' ⟶ Sp R'} {s : S ⟶ Sp R}
    (o' : GObj gb N s') (o : Obj b N s) (f : S' ⟶ S) : Prop :=
  ∃ (φA : o'.A.left ⟶ o.A.left) (φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left),
    IsGrpPullback o'.A o.A f φA ∧ IsSquare φA φ₂ ∧
    (∀ c : D.O, (o'.act.act c).left ≫ φA = φA ≫ (o.act.act c).left) ∧ Nonempty (LBIso o'.P (o.P.pull φ₂)) ∧
    ∀ y : D.La, (o'.eta y).left ≫ φA = f ≫ (o.eta y).left

end GlobalTheory.UPel.HT.Gen
end
end

section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU

variable {p : ℕ} [Fact p.Prime]

def Datum.inv (D : Datum p) (x : D.O) : D.O := (D.star x).unop

def Datum.plat (D : Datum p) : PLat D.O D.inv where
  La := D.La
  fin := D.finLa
  free := D.freeLa
  EF := (2 : ℤ) • D.EF
  alt x := by simp [D.alt]
  nondeg x h := D.nondeg (by
    ext y
    have := h y
    simpa using this)
  adj a x y := by simp [D.adj, Datum.inv]

def Datum.g (D : Datum p) : ℕ := D.m * D.n * Module.finrank ℚ D.F / 2

def HalfPerf {O : Type} [Ring O] {bar : O → O} (p : ℕ) (D' : PLat O bar) : Prop :=
  ∃ E₁ : LinearMap.BilinForm ℤ D'.La, D'.EF = (2 : ℤ) • E₁ ∧
    ∃ e : ℕ, e.Coprime p ∧ ∀ f : D'.La →ₗ[ℤ] ℤ, ∃ x, E₁ x = e • f

def Datum.Cls (D : Datum p) (N : ℕ) (D' : PLat D.O D.inv) (t : D.La → D'.La) : Prop :=
  Genus p N D.plat D' t ∧ HalfPerf p D'


open Classical in
def Base.IsType {D : Datum p} {R : Type} [CommRing R] (b : Base D R) (σ : R →+* ℂ)
    (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) : Prop :=
  ∀ c : 𝓞 D.F, (ρ (algebraMap (𝓞 D.F) D.O c)).trace = (D.m : ℂ) * (∑ i, σ (b.t i c) +
    ∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ σ b.ρ), (D.n : ℂ) * τ (c : D.F) -
    ∑ i, (starRingEnd ℂ) (σ (b.t i c)))

def Obj.fam {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R}
    (o : Obj b N s) (h : SmoothOfRelativeDimension D.g o.A.hom) (hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB) :
    Fam R D.O D.La D.g where
  X := S
  s := s
  A := o.A
  ab := o.ab
  dim := h
  act := o.act.act
  hom := o.act.hom
  act_one := o.act.one
  act_mul := o.act.mul
  act_add := o.act.add
  L := o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left
  isLB := hL
  ample := o.ample
  eta := o.eta

def Model.Uniformised {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} (M : Model b N) (σ : R →+* ℂ)
    (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) : Prop :=
  ∃ h hL, Nonempty (Unif (M.univ.fam h hL) σ ρ N (D.Cls N))

end GlobalTheory.UPel.HT
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField

namespace GlobalTheory.IwLevel

open GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}}

def htAct {s : S ⟶ Sp R} (o : Obj b N s) : Out.RingAct o.A D.O :=
  ⟨o.act.act, o.act.hom, o.act.one, o.act.mul, o.act.add⟩

@[simp] theorem htAct_act {s : S ⟶ Sp R} (o : Obj b N s) (c : D.O) : (htAct o).act c = o.act.act c := rfl

abbrev HTIw {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) : Type 1 :=
  Chain (htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) (Ideal.absNorm w ^ D.m) D.n

section Basic₂

end Basic₂

end GlobalTheory.IwLevel
end
end

section

noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}}

def IsHecke (g : D.La →ₗ[D.O] D.La) (c k N : ℕ) {s : S ⟶ Sp R} (o : Obj b (N * k) s) (o' : Obj b N s)
    (ψ : o.A ⟶ o'.A) : Prop :=
  IsMonHom ψ ∧ (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ o'.act.act c') ∧ (∀ x, o'.eta x = o.eta (g x) ≫ ψ) ∧
    GlobalTheory.ZM.IsGaloisCover (heckeSub o g N) (fun h => (transl h.1).left) ψ.left ∧
    Nonempty (LBIso (lbPow o.P (k ^ 2 / c)) (o'.P.pull (sq2 ψ))) ∧ c ∣ k ^ 2

def IsHeckeMap (g : D.La →ₗ[D.O] D.La) (c k N : ℕ) (F : RepFam b N) (F' : RepFam b (N * k))
    (π : F'.X ⟶ F.X) : Prop :=
  π ≫ F.s = F'.s ∧ ∃ (o' : Obj b N F'.s) (ψ : F'.univ.A ⟶ o'.A), IsHecke g c k N F'.univ o' ψ ∧
    Nonempty (ObjMap o' F.univ π)

end GlobalTheory.UPel.HT.Hecke
end
end
