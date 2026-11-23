module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle892
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle977
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle803
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.VerticalUnit

section Units

variable {X : Scheme.{0}} [IsIntegral X]

def UnitAt (x : X) (t : X.functionField) : Prop :=
  ∃ u : (X.presheaf.stalk x)ˣ, algebraMap _ X.functionField (u : X.presheaf.stalk x) = t

theorem UnitAt.mul {x : X} {s t : X.functionField} (hs : UnitAt x s) (ht : UnitAt x t) : UnitAt x (s * t) := by
  obtain ⟨u, rfl⟩ := hs
  obtain ⟨v, rfl⟩ := ht
  exact ⟨u * v, by rw [Units.val_mul, map_mul]⟩

theorem UnitAt.inv {x : X} {s : X.functionField} (hs : UnitAt x s) : UnitAt x s⁻¹ := by
  obtain ⟨u, rfl⟩ := hs
  exact ⟨u⁻¹, by rw [map_units_inv]⟩

theorem UnitAt.ne_zero {x : X} {s : X.functionField} (hs : UnitAt x s) : s ≠ 0 := by
  obtain ⟨u, rfl⟩ := hs
  exact (u.isUnit.map _).ne_zero

theorem isOpen_unitAt (t : X.functionField) : IsOpen {x : X | UnitAt x t} := by
  refine isOpen_iff_forall_mem_open.2 ?_
  rintro x ⟨u, hu⟩
  obtain ⟨V, hV, s, hs⟩ := X.presheaf.exists_germ_eq (u : X.presheaf.stalk x)
  refine ⟨X.basicOpen s, fun y hy => ?_, (X.basicOpen s).isOpen,
    (X.mem_basicOpen s x hV).2 (by rw [hs]; exact u.isUnit)⟩
  have hyV := X.basicOpen_le s hy
  refine ⟨((X.mem_basicOpen s y hyV).1 hy).unit, ?_⟩
  rw [← hu, ← hs, IsUnit.unit_spec]
  exact (X.presheaf.germ_stalkSpecializes_apply hyV _ _).trans
    (X.presheaf.germ_stalkSpecializes_apply hV _ _).symm

theorem exists_unit_eq [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (V : X.Opens) [Nonempty V]
    (t : X.functionField) (h0 : t ≠ 0) (h : ∀ x ∈ V, Order.coheight x = 1 → UnitAt x t) :
    ∃ u : Γ(X, V)ˣ, X.germToFunctionField V u = t := by
  obtain ⟨s, hs⟩ := exists_germToFunctionField_eq_of_coheight_eq_one V t fun x hx h1 =>
    let ⟨u, hu⟩ := h x hx h1; ⟨u, hu⟩
  obtain ⟨s', hs'⟩ := exists_germToFunctionField_eq_of_coheight_eq_one V t⁻¹ fun x hx h1 =>
    let ⟨u, hu⟩ := (h x hx h1).inv; ⟨u, hu⟩
  have : IsUnit s := IsUnit.of_mul_eq_one s' (X.germToFunctionField_injective V (by
    rw [map_mul, hs, hs', map_one, mul_inv_cancel₀ h0]))
  exact ⟨this.unit, hs⟩

end Units

theorem constFn_top {A : Type} [CommRing A] {X : Scheme.{0}} (q : X ⟶ Sp A) (a : A) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn q ⊤ a = q.appTop ((Scheme.ΓSpecIso (.of A)).inv a) :=
  congrArg (fun m : Γ(Sp A, ⊤) ⟶ Γ(X, ⊤) => m ((Scheme.ΓSpecIso (.of A)).inv a)) (q.appLE_eq_app (U := ⊤))

theorem app_constFn {A C : Type} [CommRing A] [CommRing C] {g : A →+* C} {X Y : Scheme.{0}} {q : X ⟶ Sp A}
    {p : Y ⟶ Sp C} {φ : Y ⟶ X} (w : φ ≫ q = p ≫ spMap g) (a : A) :
    φ.app ⊤ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn q ⊤ a) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn p ⊤ (g a) := by
  have h₁ := congrArg (fun φ : Y ⟶ Sp A ↦ φ.appTop ((Scheme.ΓSpecIso (.of A)).inv a)) w
  have h₂ := congrArg (fun φ : CommRingCat.of A ⟶ Γ(Spec (.of C), ⊤) ↦ φ a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  rw [constFn_top, constFn_top]
  exact h₁.trans (congrArg p.appTop h₂.symm)

section Transport

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (φ : Y ⟶ X) (hφ : φ (genericPoint Y) ⤳ genericPoint X)

noncomputable def ffMap : X.functionField ⟶ Y.functionField :=
  X.presheaf.stalkSpecializes hφ ≫ φ.stalkMap (genericPoint Y)

theorem ffMap_germ (V : X.Opens) [Nonempty V] (W : Y.Opens) [Nonempty W] (h : W ≤ φ ⁻¹ᵁ V) (s : Γ(X, V)) :
    ffMap φ hφ (X.germToFunctionField V s) = Y.germToFunctionField W (φ.appLE V W h s) := by
  refine (congrArg (φ.stalkMap _) (X.presheaf.germ_stalkSpecializes_apply _ hφ s)).trans
    ((φ.germ_stalkMap_apply V _ _ s).trans ?_)
  exact (Y.presheaf.germ_res_apply (homOfLE h) _ _ _).symm

variable [∀ y, IsIso (φ.stalkMap y)]

theorem ffMap_bijective : Function.Bijective (ffMap φ hφ) := by
  have : IsIso (X.presheaf.stalkSpecializes hφ) :=
    (X.presheaf.stalkCongr ((genericPoint_specializes _).antisymm hφ)).isIso_hom
  have : IsIso (ffMap φ hφ) := by unfold ffMap; infer_instance
  exact ConcreteCategory.bijective_of_isIso _

theorem unitAt_of_isUnit {W : Y.Opens} [Nonempty W] {τ : Γ(Y, W)} (hτ : IsUnit τ) {y : Y} (hy : y ∈ W)
    {t : X.functionField} (ht : ffMap φ hφ t = Y.germToFunctionField W τ) : UnitAt (φ y) t := by
  obtain ⟨σ, hσ⟩ := (ConcreteCategory.bijective_of_isIso (φ.stalkMap y)).2 (Y.presheaf.germ W y hy τ)
  have hu : IsUnit σ := (isUnit_map_iff (φ.stalkMap y).hom σ).1 (by
    rw [hσ]; exact hτ.map _)
  refine ⟨hu.unit, (ffMap_bijective φ hφ).1 ?_⟩
  rw [ht, IsUnit.unit_spec]
  obtain ⟨V, hV, s, rfl⟩ := X.presheaf.exists_germ_eq σ
  have : Nonempty V := ⟨⟨_, hV⟩⟩
  have : Nonempty (φ ⁻¹ᵁ V) := ⟨⟨y, hV⟩⟩
  refine (congrArg (ffMap φ hφ) (X.presheaf.germ_stalkSpecializes_apply hV _ s)).trans
    ((ffMap_germ φ hφ V (φ ⁻¹ᵁ V) le_rfl s).trans ?_)
  rw [φ.germ_stalkMap_apply] at hσ
  rw [φ.appLE_eq_app]
  have := congrArg (Y.presheaf.stalkSpecializes (genericPoint_specializes y)) hσ
  rwa [Y.presheaf.germ_stalkSpecializes_apply, Y.presheaf.germ_stalkSpecializes_apply] at this

end Transport

open MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

end GlobalTheory.VerticalUnit
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix
open scoped TensorProduct

namespace GlobalTheory.SmGL.RowOneCell

def sz (u v : ℕ) (i j : Bool) : ℕ := cond i (cond j v 1) (cond j u 0)

def sigTwo (b : Bool → ℕ) (x y : ℕ) (h0 : b false = x) (h1 : b true = y) :
    (Σ j, Fin (b j)) ≃ Σ j, Two (Fin x) (Fin y) j :=
  Equiv.sigmaCongrRight fun j => match j with
    | false => finCongr h0
    | true => finCongr h1

def rowPart (u v : ℕ) : ∀ i, (Σ j, Fin (sz u v i j)) ≃ Two (Fin u) (Fin (v + 1)) i
  | false => (sigTwo (sz u v false) 0 u rfl rfl).trans (two (stdSum (Nat.zero_add u)))
  | true => (sigTwo (sz u v true) 1 v rfl rfl).trans (two (stdSum (Nat.add_comm 1 v)))

def colPart (u v : ℕ) : ∀ j, (Σ i, Fin (sz u v i j)) ≃ Two (Fin 1) (Fin (u + v)) j
  | false => (sigTwo (fun i => sz u v i false) 0 1 rfl rfl).trans (two (stdSum (Nat.zero_add 1)))
  | true => (sigTwo (fun i => sz u v i true) u v rfl rfl).trans (two (stdSum rfl))

theorem eq_sz {u v : ℕ} (b : Bool → Bool → ℕ)
    (hb : (∀ i, ∑ j, b i j = Fintype.card (Two (Fin u) (Fin (v + 1)) i)) ∧
      ∀ j, ∑ i, b i j = Fintype.card (Two (Fin 1) (Fin (u + v)) j)) (h : b true false = 1) :
    b = sz u v := by
  have r0 := hb.1 false
  have r1 := hb.1 true
  have c0 := hb.2 false
  have c1 := hb.2 true
  simp only [Fintype.sum_bool] at r0 r1 c0 c1
  have e0 : Fintype.card (Two (Fin u) (Fin (v + 1)) false) = u := Fintype.card_fin u
  have e1 : Fintype.card (Two (Fin u) (Fin (v + 1)) true) = v + 1 := Fintype.card_fin _
  have e2 : Fintype.card (Two (Fin 1) (Fin (u + v)) false) = 1 := Fintype.card_fin _
  have e3 : Fintype.card (Two (Fin 1) (Fin (u + v)) true) = u + v := Fintype.card_fin _
  rw [e0] at r0
  rw [e1] at r1
  rw [e2] at c0
  rw [e3] at c1
  funext i j
  cases i <;> cases j <;> simp only [sz, cond_true, cond_false] <;> omega

def extTensorEquiv {G H V W V' W' : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ G V} {σ : Representation ℂ H W} {ρ' : Representation ℂ G V'}
    {σ' : Representation ℂ H W'} (φ : ρ.Equiv ρ') (ψ : σ.Equiv σ') :
    (extTensor ρ σ).Equiv (extTensor ρ' σ') :=
  .mk (TensorProduct.congr φ.toLinearEquiv ψ.toLinearEquiv) fun g => by
    ext v w
    exact congrArg₂ (fun a b => a ⊗ₜ[ℂ] b) (φ.toIntertwiningMap.isIntertwining _ _ g.1 v)
      (ψ.toIntertwiningMap.isIntertwining _ _ g.2 w)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def colChar (v : ℕ) (χ₂ : kˣ →* ℂˣ) (j : Bool) : kˣ →* ℂˣ :=
  χ₂ * absPow k (cond j (1 / 2) (-(v : ℂ) / 2))

def colRep (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (j : Bool) :
    Representation ℂ (Levi k fun i => Fin (sz u v i j)) (ℂ ⊗[ℂ] ℂ) :=
  (extTensor (detRep (Fin (sz u v false j)) χ₁) (detRep (Fin (sz u v true j)) (colChar v χ₂ j))).comp
    ((Pi.evalMonoidHom (fun i => GL (Fin (sz u v i j)) k) false).prod
      (Pi.evalMonoidHom (fun i => GL (Fin (sz u v i j)) k) true))

theorem isSmooth_colRep {χ₁ χ₂ : kˣ →* ℂˣ} (h₁ : IsSmoothChar χ₁) (h₂ : IsSmoothChar χ₂) (u v : ℕ) (j : Bool) :
    IsSmooth (colRep χ₁ χ₂ u v j) := by
  refine isSmooth_comp (isSmooth_extTensor ((isSmooth_ofChar_iff _).2 h₁.detChar)
    ((isSmooth_ofChar_iff _).2 (h₂.mul (GlobalTheory.LocGL.isSmoothChar_absPow _)).detChar)) _ ?_
  exact (continuous_apply false).prodMk (continuous_apply true)

end GlobalTheory.SmGL.RowOneCell
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

open Coalgebra Bialgebra WithConv

namespace GlobalTheory.SpanPow

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K]

def annPowIdeal (h : (p : K) = 0) (G : PDivGroup p K) (r : ℕ) : Ideal (G.dual.A r) where
  carrier := {χ | ∀ a : G.A r, (show CartierDual K (G.A r) from χ) (a ^ p ^ r) = 0}
  add_mem' {χ ψ} hχ hψ a := by
    have e1 := hχ a
    have e2 := hψ a
    change (χ.ofConv + ψ.ofConv) (a ^ p ^ r) = 0
    rw [LinearMap.add_apply]
    change χ.ofConv (a ^ p ^ r) = 0 at e1
    change ψ.ofConv (a ^ p ^ r) = 0 at e2
    rw [e1, e2, add_zero]
  zero_mem' a := rfl
  smul_mem' c χ hχ a := by
    change (show CartierDual K (G.A r) from c * χ) (a ^ p ^ r) = 0
    rw [CartierDual.mul_apply, ← Bialgebra.comulAlgHom_apply, map_pow, Bialgebra.comulAlgHom_apply]
    rcases subsingleton_or_nontrivial (G.A r ⊗[K] G.A r) with hs | hn
    · rw [Subsingleton.elim ((comul (R := K) a) ^ p ^ r) 0, map_zero]
    · haveI : CharP (G.A r ⊗[K] G.A r) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 (by
        rw [← map_natCast (algebraMap K (G.A r ⊗[K] G.A r)), h, map_zero])
      haveI : ExpChar (G.A r ⊗[K] G.A r) p := ExpChar.prime (Fact.out : p.Prime)
      have rep := Coalgebra.Repr.arbitrary K a

      rw [← rep.eq, sum_pow_char_pow, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Algebra.TensorProduct.tmul_pow, CartierDual.pair_tmul_tmul]
      have e := hχ (rep.right i)
      change χ.ofConv _ = 0 at e
      rw [e, mul_zero]

theorem frobKerIdeal_le_annPowIdeal (h : (p : K) = 0) (G : PDivGroup p K) (r : ℕ) :
    frobKerIdeal (p ^ r) K (G.dual.A r) ≤ annPowIdeal h G r := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨χ, hχ, rfl⟩ a
  have h1 := GlobalTheory.T.cartierDual_primePow_conv_pairing p K h G r r χ a
  have hχ' : χ.ofConv 1 = 0 := hχ
  change (χ ^ p ^ r).ofConv (a ^ p ^ r) = 0
  change (χ ^ p ^ r).ofConv (a ^ p ^ r) = χ.ofConv (mulBy K (G.A r) (p ^ r) a) ^ p ^ r at h1
  rw [h1, G.mulBy_pow_self r a, Algebra.algebraMap_eq_smul_one, map_smul, hχ', smul_zero,
    zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]

end GlobalTheory.SpanPow

open GlobalTheory.SpanPow in
theorem GlobalTheory.finrank_span_pow_le : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), ∀ r : ℕ, Module.finrank K (Submodule.span K (Set.range fun a : G.A r => a ^ p ^ r)) ≤ (p ^ r) ^ Module.finrank K G.dual.omega := by
  intro p _ K _ h G r
  set S := Submodule.span K (Set.range fun a : G.A r => a ^ p ^ r) with hS
  let D := G.dual.A r
  let ev : D →ₗ[K] Module.Dual K S := S.subtype.dualMap ∘ₗ (CartierDual.toDual K (G.A r)).toLinearMap
  have hev : Function.Surjective ev :=
    (LinearMap.dualMap_surjective_of_injective S.injective_subtype).comp
      (CartierDual.toDual K (G.A r)).surjective
  let J := frobKerIdeal (p ^ r) K D
  have hle : J.restrictScalars K ≤ LinearMap.ker ev := by
    intro χ hχ
    have hT := frobKerIdeal_le_annPowIdeal h G r hχ
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun s => ?_
    obtain ⟨s, hs⟩ := s
    change χ.ofConv s = 0
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact hT a
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  let φ : (D ⧸ J) →ₗ[K] Module.Dual K S :=
    (J.restrictScalars K).liftQ ev hle ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv K J).symm.toLinearMap
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := hev y
    refine ⟨Ideal.Quotient.mk J x, ?_⟩
    rfl
  have h1 : Module.finrank K S ≤ Module.finrank K (D ⧸ J) := by
    have := LinearMap.finrank_range_le φ
    rw [LinearMap.range_eq_top.2 hφ, finrank_top, Subspace.dual_finrank_eq] at this
    exact this
  have h2 := GlobalTheory.T.finrank_frobeniusKernelQuotient_le_pow_cotangent (p ^ r) K D (pow_pos (Fact.out : p.Prime).pos r)
  have hfin := (GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual p K h G.dual).1
  have h3 : Module.finrank K (Cot K D) ≤ Module.finrank K G.dual.omega := by
    have := LinearMap.finrank_range_le (G.dual.omegaLevel r)
    rwa [LinearMap.range_eq_top.2 (G.dual.omegaLevel_surjective r), finrank_top] at this
  exact h1.trans (h2.trans (Nat.pow_le_pow_right (pow_pos (Fact.out : p.Prime).pos r) h3))
end

section

open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

theorem units_of_divConst (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [Algebra T O]
    (h : DivConst T O)
    (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ) :
    ∃ (c d : T) (w : Oˣ), c ≠ 0 ∧ d ≠ 0 ∧
      (u : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) *
          algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))
            (algebraMap T O d) =
        algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))
            (algebraMap T O c) *
          algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (w : O) := by
  by_cases hL : Subsingleton (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))
  · exact ⟨1, 1, 1, one_ne_zero, one_ne_zero, Subsingleton.elim _ _⟩
  rw [not_subsingleton_iff_nontrivial] at hL
  obtain ⟨⟨b, s₁⟩, hb⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  obtain ⟨⟨c, s₂⟩, hc⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) ((u⁻¹ : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ) : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  obtain ⟨t₁, ht₁, hs₁⟩ := s₁.2
  obtain ⟨t₂, ht₂, hs₂⟩ := s₂.2
  have h1 : algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (b * c) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) ((s₁ : O) * (s₂ : O)) := by
    have hu : (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) * ((u⁻¹ : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ) : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) = 1 := u.mul_inv
    rw [← hb, ← hc, ← IsLocalization.mk'_mul] at hu
    have := IsLocalization.mk'_spec (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (b * c) (s₁ * s₂)
    rw [hu, one_mul] at this
    rw [← this]; rfl
  obtain ⟨m, hm⟩ := (IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))).1 h1
  obtain ⟨t₀, ht₀, hm₀⟩ := m.2
  have hmem : t₀ * t₁ * t₂ ∈ nonZeroDivisors T :=
    mul_mem (mul_mem ht₀ ht₁) ht₂
  have hne : t₀ * t₁ * t₂ ≠ 0 := nonZeroDivisors.ne_zero hmem
  obtain ⟨a, w, hbw⟩ := h b ((m : O) * c) (t₀ * t₁ * t₂) hne (by
    rw [map_mul, map_mul, hm₀, hs₁, hs₂]
    calc b * ((m : O) * c) = (m : O) * (b * c) := by ring
      _ = (m : O) * ((s₁ : O) * (s₂ : O)) := hm
      _ = (m : O) * (s₁ : O) * (s₂ : O) := by ring)
  have key : (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (s₁ : O) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) b := by
    rw [← hb]; exact IsLocalization.mk'_spec (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) b s₁
  refine ⟨a, t₁, w, ?_, nonZeroDivisors.ne_zero ht₁, ?_⟩
  · intro ha
    have h0 : (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (s₁ : O) = 0 := by
      rw [key, hbw, ha]; simp
    exact (u.isUnit.mul (IsLocalization.map_units (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) s₁)).ne_zero h0
  · rw [hs₁, key, hbw, map_mul]

theorem main_of_divConstAll (hAll : DivConstAll) : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)], (∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, ∃ (c d : T) (w : Oˣ), c ≠ 0 ∧ d ≠ 0 ∧ (u : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O d) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O c) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (w : O) := by
  intro T O _ _ _ _ _ _ _ _ _ hroot hO u
  obtain ⟨P, hP, φ, hφ, hsh⟩ :=
    GlobalTheory.StrictHensUnion.isStrictHenselisation_of_directed_union T O hO
  exact units_of_divConst T O (hAll T O hroot P φ hφ hsh) u

end GlobalTheory.VertUnits

namespace GlobalTheory.VertUnits

theorem units_eq_const_mul_unit : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)], (∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, ∃ (c d : T) (w : Oˣ), c ≠ 0 ∧ d ≠ 0 ∧ (u : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O d) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O c) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (w : O) :=
  main_of_divConstAll (GlobalTheory.T.divisorsOfConstantsAllPrimes_of_closedFibre (divConstLocal_of
    (GlobalTheory.T.divisorsOfConstantsClosedPoints_of_origin GlobalTheory.T.div_const_origin) (GlobalTheory.T.divisorsOfConstants_genericFibre_of_closedPoints (GlobalTheory.T.divisorsOfConstantsClosedPoints_of_origin GlobalTheory.T.div_const_origin))))

end GlobalTheory.VertUnits
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

private theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

private theorem sec_res_sub {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x - y) = Sec.res g x - Sec.res g y := map_sub _ x y

private theorem sec_map_sub {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x - y) = Sec.map φ x - Sec.map φ y := map_sub _ x y

theorem red_chern_deg_one : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (a : Sec ((res _ (tw Q 1)).X 1) U) (b : Sec ((res _ (tw q 1)).X 1) U), (∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g a = Sec.map ((res _ (tw Q 1)).d 0 1) (kumT Q V v)) → (∀ (V : Scheme.{0}) (g : V ⟶ U) (w : (Γ(V, ⊤))ˣ), w ^ q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g b = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V w)) → (redMap Q q 1).app U 1 a - b = Sec.map ((res _ (tw q 1)).d 0 1) (GlobalTheory.EtC.RedChern.defectSec Q q U u) := by
  intro Q q _ hqQ U u hQ a b ha hb
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ U).1 _ _ ?_
  refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).2.2.2 hQ u) ?_
  rintro V g ⟨v, hv⟩
  have hw : (v ^ (Q / q)) ^ q = Units.map g.appTop.hom.toMonoidHom u := by
    rw [← pow_mul, Nat.div_mul_cancel hqQ, hv]
  rw [sec_res_sub, (redMap Q q 1).nat, ha V g v hv, hb V g _ hw, ← (redMap Q q 1).comm, sec_res_map,
    GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u hQ V g v hv, defect, sec_map_sub]

end GlobalTheory.EtC.RedChern
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem GlobalTheory.RedChern.redMap_cocycle_sub_eq_defects : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u₁ u₂ : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (a : Sec ((res _ (tw Q 1)).X 0) U) (b : Sec ((res _ (tw q 1)).X 0) U), (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ Q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g a = kumT Q V v + kumT Q V w - kumT Q V (v * w)) → (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g b = kumT q V v + kumT q V w - kumT q V (v * w)) → (redMap Q q 1).app U 0 a - b = GlobalTheory.EtC.RedChern.defectSec Q q U u₂ - GlobalTheory.EtC.RedChern.defectSec Q q U (u₁ * u₂) + GlobalTheory.EtC.RedChern.defectSec Q q U u₁ := by
  intro Q q _ hqQ U u₁ u₂ hQ a b ha hb
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue _ ((res _ (tw q 1)).X 0) U).1 _ _ ?_
  have h1 := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).2.2.2 hQ u₁
  have h2 := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).2.2.2 hQ u₂
  refine GlobalTheory.EtC.RedChern.loc_mono (GlobalTheory.EtC.RedChern.loc_and h1 h2) ?_
  rintro V g ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
  have hvq : (v ^ (Q / q)) ^ q = Units.map g.appTop.hom.toMonoidHom u₁ := by
    rw [← pow_mul, Nat.div_mul_cancel hqQ, hv]
  have hwq : (w ^ (Q / q)) ^ q = Units.map g.appTop.hom.toMonoidHom u₂ := by
    rw [← pow_mul, Nat.div_mul_cancel hqQ, hw]
  have hvw : (v * w) ^ Q = Units.map g.appTop.hom.toMonoidHom (u₁ * u₂) := by
    rw [mul_pow, hv, hw, map_mul]
  have ea := ha V g v w hv hw
  have eb := hb V g _ _ hvq hwq
  have d1 := GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u₁ hQ V g v hv
  have d2 := GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u₂ hQ V g w hw
  have d3 := GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U (u₁ * u₂) hQ V g (v * w) hvw
  have en := (redMap Q q 1).nat g 0 a
  have hsub : ∀ x y : Sec ((res _ (tw q 1)).X 0) U, Sec.res g (x - y) = Sec.res g x - Sec.res g y := fun x y => map_sub _ x y
  have hadd : ∀ x y : Sec ((res _ (tw q 1)).X 0) U, Sec.res g (x + y) = Sec.res g x + Sec.res g y := fun x y => map_add _ x y
  rw [hsub, hadd, hsub, en, ea, eb, d1, d2, d3]
  simp only [GlobalTheory.EtC.RedChern.defect, map_sub, map_add (f := _), mul_pow]
  abel
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.projectiveBundleFormula_of_discrete_spaces : ∀ (q : ℕ) [NeZero q] (N : ℕ), (∀ (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V) → ∀ {E : Spc} (V : E ⟶ ofCat (glCat N)), Inv q E → PBF q V := by
  first | (exact @GlobalTheory.PBFg.pbf_of_disc) | (exact GlobalTheory.PBFg.pbf_of_disc) | (intros; apply GlobalTheory.PBFg.pbf_of_disc  <;> assumption)
end
