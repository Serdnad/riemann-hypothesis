module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle046
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.FirstIneq

theorem perp_anti_of_le {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    {A B : AddSubgroup S.Gam} (h : A ≤ B) : S.perp B ≤ S.perp A :=
  fun _ ha x hx => ha x (h hx)

theorem ff_mem_ring {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) : S.FF T c k ∈ S.R := by
  unfold ThetaSys.FF
  refine finsum_induction (· ∈ S.R) (zero_mem _) (fun _ _ => add_mem) fun t => ?_
  exact mul_mem (S.R.algebraMap_mem _)
    (sum_mem fun j _ => mul_mem (S.R.algebraMap_mem _) (S.ev_mem _ _))

theorem ff_div_ff_mem_of_specializes : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → ∀ (c : S.TT M z →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF (S.TT M z) c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖M.val (gPt p ≫ y) (S.FF (S.TT M z) c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → S.FF _ c k / S.FF _ c' k' ∈ M.O ξ) := by
  intro o Ω _ _ _ _ S M U₀ hO hLL hT hS hG hW hB hE z ξ c c' k k' _ hs hc _ hd'
  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  haveI : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  obtain ⟨x, hxW, hxc, hξx, hI⟩ :=
    hG.2.2.2 ξ ⟨_, M.isOpen_setOf_div (S.FF (S.TT M ξ) c') k'⟩ hd'
  have hH : S.HH M x = S.HH M ξ := by unfold ThetaSys.HH; rw [hI]
  have hTT : S.TT M ξ = S.TT M x := by unfold ThetaSys.TT; rw [hH]
  have hHz : S.HH M z ≤ S.HH M ξ := AddSubgroup.closure_mono (hG.2.1 ξ z hs)
  have hf : S.FF _ c k ∈ M.ringOn U₀ := hO.le (ff_mem_ring S _ c k)
  have hf' : S.FF _ c' k' ∈ M.ringOn U₀ := hO.le (ff_mem_ring S _ c' k')
  have hi : (S.FF _ c' k')⁻¹ ∈ M.ringOn U₀ := hO.FF_unit _ c' k' (hG.1 ξ).1 hd'.1
  refine RatModel.O_le_of_specializes hξx ((hLL.1 U₀ le_rfl hO.ne x hxc).2 _ ?_ ?_)
  · rw [div_eq_mul_inv]
    exact mul_mem hf hi
  intro p _ y hy
  obtain ⟨y₀, hAt, hint, ⟨τ⟩⟩ := hT x p y hy
  have hker : S.HH M ξ = τ.yy.ker := hH ▸ (hS x p y y₀ τ hy hAt).2
  have hperp : S.perp τ.yy.ker = S.TT M ξ := by rw [← hker]; rfl
  obtain ⟨α, hα, hwt⟩ := (hW p y₀ τ).1 (c'.comp (AddSubgroup.inclusion hperp.le))
  have h1 := (hB p y₀ τ hint (S.TT M z) c k (ff_mem_ring S _ c k) (hG.1 z).1).1
    (hperp.le.trans (perp_anti_of_le S hHz))
    (((hG.1 z).1.1.trans (hG.1 z).2.le).trans (hHz.trans hker.le)) α hα
    (fun t h₁ h₂ => by rw [hwt]; exact hc t h₁ (hperp.le h₂))
  have hE' : ∀ (T : AddSubgroup S.Gam), T = S.TT M x → ∀ (c : T →+ ZMod S.N) (k : _),
      M.Div (S.FF T c) k x →
      (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) →
      ‖M.val (gPt p ≫ y) (S.FF T c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N)) := by
    rintro T rfl c k h h'
    exact hE x p y y₀ τ hy hAt c k α h hα h'
  have h2 := hE' _ hTT c' k' hxW (fun t h₁ h₂ => by rw [hwt]; rfl)
  rw [hAt, ← h2] at h1
  set yg := gPt p ≫ y with hyg
  have w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hw : yg w ∈ (U₀ : Set M.Z) := hy.2 ⟨w, rfl⟩
  have hsp := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton yg w)
  have e1 : M.val yg (S.FF _ c' k') * M.val yg (S.FF _ c' k')⁻¹ = 1 := by
    rw [← RatModel.val_mul hsp (RatModel.ringOn_le_O hw hf') (RatModel.ringOn_le_O hw hi),
      mul_inv_cancel₀ hd'.1, RatModel.val_one]
  rw [div_eq_mul_inv, RatModel.val_mul hsp (RatModel.ringOn_le_O hw hf) (RatModel.ringOn_le_O hw hi),
    norm_mul, ← norm_one (α := PadicAlgCl p), ← e1, norm_mul]
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

end GlobalTheory.ZH.FirstIneq
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem ThetaSys.Test.FF_ne_zero {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}
    {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀)
    (hs : ∀ c : S.perp τ.yy.ker →+ ZMod S.N,
      ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c)
    (T : AddSubgroup S.Gam) (hT : T = S.perp τ.yy.ker) (c : T →+ ZMod S.N) : S.FF T c ≠ 0 := by
  subst hT
  obtain ⟨α, hα, rfl⟩ := hs c
  obtain ⟨k, hk, h⟩ := τ.eq α hα
  intro h0
  have h1 : (⟨S.FF _ (τ.wt α) k, hk⟩ : S.R) = 0 := Subtype.ext (congrFun h0 k)
  rw [h1, map_zero, norm_zero] at h
  exact (mul_pos τ.δ_pos (Real.exp_pos _)).ne h

theorem FF_TT_ne_zero : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N), S.FF (S.TT M ξ) c ≠ 0) := by
  intro o Ω _ _ _ _ S M U₀ hO hL hT hI hZ hW ξ c
  obtain ⟨x, -, hx, -, hxI⟩ := hZ.2.2.2 ξ ⊤ trivial
  obtain ⟨p, hp, y, hy⟩ := (hL.1 U₀ le_rfl hO.ne x hx).1
  obtain ⟨y₀, hA, -, ⟨τ⟩⟩ := hT x p y hy
  refine τ.FF_ne_zero (hW p y₀ τ).1 _ ?_ c
  rw [← (hI x p y y₀ τ hy hA).2]
  unfold ThetaSys.TT ThetaSys.HH
  rw [hxI]

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ

open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs

def wtZeroSubring {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X]
    (i : splitTorus S X ⟶ H) (V : H.left.Opens) : Subring Γ(H.left, V) where
  carrier := {u | HasWt i V u 0}
  one_mem' := hasWt_one i V
  zero_mem' := fun Y t g h h' => by rw [map_zero, map_zero, mul_zero]
  mul_mem' := fun {a b} ha hb Y t g h h' => by
    have h₁ := ha Y t g h h'
    have h₂ := hb Y t g h h'
    rw [charUnit_zero_val, map_one, _root_.one_mul] at h₁ h₂ ⊢
    rw [map_mul, map_mul, h₁, h₂]
  add_mem' := fun {a b} ha hb Y t g h h' => by
    rw [map_add (f := _), map_add (f := _), ha Y t g h h', hb Y t g h h', mul_add]
  neg_mem' := fun {a} ha Y t g h h' => by
    rw [map_neg, map_neg, ha Y t g h h', mul_neg]

theorem hasWt_zero_appLE_base {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X]
    (i : splitTorus S X ⟶ H) (V : H.left.Opens) (a : Γ(S, ⊤)) :
    HasWt i V ((H.hom.appLE ⊤ V le_top).hom a) 0 := by
  intro Y t g h h'
  rw [charUnit_zero_val, map_one, _root_.one_mul]
  refine (appLE_appLE _ H.hom (U := ⊤) le_top h' a).trans (Eq.trans ?_ (appLE_appLE _ H.hom (U := ⊤) le_top h a).symm)
  exact congrArg (fun ψ : Γ(S, ⊤) ⟶ Γ(Y.left, ⊤) => ψ.hom a)
    (appLE_of_eq ((Over.w _).trans (Over.w _).symm) _ _ _ _)

theorem mem_range_appLE_chart_iff {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N)
    (W : Y.Opens) (a : Fin (N + 1)) (h : W ≤ φ ⁻¹ᵁ chart R N a) (u : Γ(Y, W)) :
    u ∈ Set.range (φ.appLE (chart R N a) W h).hom ↔
      u ∈ Subring.closure (Set.range ((φ ≫ PSpace.str R N).appLE ⊤ W le_top).hom ∪
        Set.range (pullRatio φ W a h)) := by
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨p, rfl⟩ := aeval_ratio_surjective R N a v
    have e := congrArg (fun t => t p) (appLE_comp_aeval_ratio (φ := φ) (hi := h))
    refine (show _ = _ from e) ▸ ?_
    clear e
    induction p using MvPolynomial.induction_on with
    | C r =>
      rw [MvPolynomial.eval₂Hom_C]
      exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      exact mul_mem hp (Subring.subset_closure (Or.inr ⟨j, rfl⟩))
  · intro hu
    have : Subring.closure (Set.range ((φ ≫ PSpace.str R N).appLE ⊤ W le_top).hom ∪
        Set.range (pullRatio φ W a h)) ≤ (φ.appLE (chart R N a) W h).hom.range := by
      rw [Subring.closure_le]
      rintro _ (⟨v, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨_, appLE_appLE φ (PSpace.str R N) (le_top : chart R N a ≤ _) h v⟩
      · exact ⟨_, rfl⟩
    exact this hu

theorem Charts.exists_proper_image {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Sp R) (C : Charts Y)
    [Nonempty Y] : ∃ (B : Scheme.{0}) (p : B ⟶ Sp R) (q : Y ⟶ B), q ≫ p = f ∧ IsProper p ∧ IsAffineHom q ∧
      ∃ V : {i // C.wt i = C.c₀} → B.Opens, ⨆ a, V a = ⊤ ∧ ∀ a, IsAffineOpen (V a) ∧ ∃ h : C.W a = q ⁻¹ᵁ V a,
        Function.Injective (q.appLE (V a) (C.W a) h.le).hom ∧ ∀ u,
          u ∈ Set.range (q.appLE (V a) (C.W a) h.le).hom ↔
          u ∈ Subring.closure (Set.range (f.appLE ⊤ (C.W a) le_top).hom ∪
            {v | ∃ j, C.wt j = C.c₀ ∧ v = C.r a j}) := by
  have hne : Nonempty {i // C.wt i = C.c₀} := by
    obtain ⟨y⟩ := ‹Nonempty Y›
    obtain ⟨a, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (C.cover.ge (Set.mem_univ y))
    exact ⟨a⟩
  obtain ⟨n, ⟨e₀⟩⟩ := Finite.exists_equiv_fin {i // C.wt i = C.c₀}
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := by
    cases n with
    | zero => exact (e₀ hne.some).elim0
    | succ N => exact ⟨N, rfl⟩
  let e := e₀.symm
  have hC : IsCoordFamily (fun i : Fin (N + 1) => C.W (e i)) (fun i j => C.r (e i) (e j).1) :=
    { cover := (e.iSup_comp (g := C.W)).trans C.cover
      self := fun i => C.r_self _
      mul := fun i j k => (C.trans _ _ _).symm
      basicOpen_le := fun i j => (C.inter _ _).ge.trans inf_le_right }
  obtain ⟨φ, hφ, hpre, hr⟩ : ∃ φ : Y ⟶ PSpace R N, φ ≫ PSpace.str R N = f ∧
      ∃ hpre : ∀ i, φ ⁻¹ᵁ chart R N i = C.W (e i), ∀ i j,
        pullRatio φ (C.W (e i)) i (hpre i).ge j = C.r (e i) (e j).1 :=
    ⟨hC.toHom f, hC.toHom_str f, hC.toHom_preimage f, hC.pullRatio_toHom f⟩
  have haff : IsAffineHom φ := isAffineHom_of_forall_exists_isAffineOpen φ fun x => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 ((iSup_chart R N).ge (Set.mem_univ x))
    exact ⟨_, hi, isAffineOpen_chart R N i, (hpre i).symm ▸ C.aff _⟩
  have hq : ∀ i, C.W (e i) = φ.toImage ⁻¹ᵁ φ.imageι ⁻¹ᵁ chart R N i := fun i => by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toImage_imageι, hpre]
  have hV : ∀ i, IsAffineOpen (φ.imageι ⁻¹ᵁ chart R N i) := fun i => (isAffineOpen_chart R N i).preimage _
  have hcov : ⨆ i, φ.imageι ⁻¹ᵁ chart R N i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, iSup_chart, Scheme.Hom.preimage_top]
  have := isProper_str R N
  refine ⟨φ.image, φ.imageι ≫ PSpace.str R N, φ.toImage, by rw [Scheme.Hom.toImage_imageι_assoc, hφ],
    inferInstance, ?_, fun a => φ.imageι ⁻¹ᵁ chart R N (e₀ a),
    (e₀.iSup_comp (g := fun i => φ.imageι ⁻¹ᵁ chart R N i)).trans hcov, fun a => ?_⟩
  · refine isAffineHom_of_forall_exists_isAffineOpen _ fun x => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge (Set.mem_univ x))
    exact ⟨_, hi, hV i, hq i ▸ C.aff _⟩
  · obtain ⟨i, rfl⟩ := e.surjective a
    have hi : e₀ (e i) = i := e₀.apply_symm_apply i
    beta_reduce
    rw [hi]
    refine ⟨hV i, hq i, ?_, fun u => ?_⟩
    · have key : ∀ (W : Y.Opens) (h : W = φ.toImage ⁻¹ᵁ φ.imageι ⁻¹ᵁ chart R N i),
          Function.Injective (φ.toImage.appLE _ W h.le).hom := by
        rintro _ rfl
        rw [Scheme.Hom.appLE_eq_app]
        exact φ.toImage_app_injective ⟨_, isAffineOpen_chart R N i⟩
      exact key _ (hq i)
    · have hs : {v | ∃ j, C.wt j = C.c₀ ∧ v = C.r (e i) j} =
          Set.range (pullRatio φ (C.W (e i)) i (hpre i).ge) := by
        ext v
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact ⟨e₀ ⟨j, hj⟩, (hr i _).trans (by rw [show e (e₀ ⟨j, hj⟩) = ⟨j, hj⟩ from e₀.symm_apply_apply _])⟩
        · rintro ⟨j, rfl⟩
          exact ⟨_, (e j).2, hr i j⟩
      rw [hs, ← hφ, ← mem_range_appLE_chart_iff]
      have hc : ∀ v, (φ.toImage.appLE _ _ (hq i).le).hom ((φ.imageι.app (chart R N i)).hom v) =
          (φ.appLE (chart R N i) _ (hpre i).ge).hom v := fun v => by
        rw [Scheme.Hom.app_eq_appLE, appLE_appLE]
        exact congrArg (fun ψ : _ ⟶ Γ(Y, C.W (e i)) => ψ.hom v) (appLE_of_eq φ.toImage_imageι _ _ _ _)
      constructor
      · rintro ⟨w, rfl⟩
        obtain ⟨v, rfl⟩ := φ.imageι.app_surjective _ (isAffineOpen_chart R N i) w
        exact ⟨v, (hc v).symm⟩
      · rintro ⟨v, rfl⟩
        exact ⟨_, hc v⟩

theorem Charts.Torus.exists_proper_quotient :
    ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H), C.Torus c i → ∃ (B : Over (Sp K)) (q : H ⟶ B), IsProper B.hom ∧ IsAffineHom q.left ∧ ∃ V : {i // C.wt i = C.c₀} → B.left.Opens, ⨆ a, V a = ⊤ ∧ ∀ a, IsAffineOpen (V a) ∧ ∃ h : C.W a = q.left ⁻¹ᵁ V a, Function.Injective (q.left.appLE (V a) (C.W a) h.le).hom ∧ ∀ u, HasWt i (C.W a) u 0 ↔ u ∈ Set.range (q.left.appLE (V a) (C.W a) h.le).hom := by
  intro K _ H _ _ _ _ _ C d c i hT
  have : Nonempty H.left := ⟨(η : 𝟙_ (Over (Sp K)) ⟶ H).left (⊥ : PrimeSpectrum K)⟩
  obtain ⟨B, p, q, hq, hp, ha, V, hV, h⟩ := C.exists_proper_image H.hom
  refine ⟨Over.mk p, Over.homMk q hq, hp, ha, V, hV, fun a => ?_⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h a
  refine ⟨h₁, h₂, h₃, fun u => ⟨fun hu => (h₄ u).2 (hT.gen a u hu), fun hu => ?_⟩⟩
  refine (Subring.closure_le (t := wtZeroSubring i (C.W a))).2 ?_ ((h₄ u).1 hu)
  rintro _ (⟨v, rfl⟩ | ⟨j, hj, rfl⟩)
  · exact hasWt_zero_appLE_base i _ v
  · exact hT.inv a j hj

end GlobalTheory.ZJ
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH
namespace Regular

theorem nonneg_of_tendsto {X : Type} [AddCommGroup X] [Module.Free ℤ X] (q : QuadraticMap ℤ X ℝ)
    (h : Filter.Tendsto q Filter.cofinite Filter.atTop) (x : X) : 0 ≤ q x := by
  by_contra hx
  push_neg at hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hfin : {v | ¬ (0 : ℝ) ≤ q v}.Finite := Filter.eventually_cofinite.1 (h.eventually_ge_atTop 0)
  have hinj : Function.Injective fun n : ℕ => ((n : ℤ) + 1) • x := by
    intro a b hab
    have := smul_left_injective ℤ hx0 hab
    omega
  refine Set.infinite_of_injective_forall_mem hinj (fun n => ?_) hfin
  simp only [Set.mem_setOf_eq, not_le, QuadraticMap.map_smul, zsmul_eq_mul]
  refine mul_neg_of_pos_of_neg ?_ hx
  positivity

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem FF_mem (S : ThetaSys o Ω) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) : S.FF T c k ∈ S.R := by
  unfold ThetaSys.FF
  refine finsum_induction (· ∈ S.R) (zero_mem _) (fun _ _ => add_mem) fun t => ?_
  exact mul_mem (S.R.algebraMap_mem _) (sum_mem fun j _ => mul_mem (S.R.algebraMap_mem _) (S.ev_mem _ _))

theorem perp_anti (S : ThetaSys o Ω) {H H' : AddSubgroup S.Gam} (h : H ≤ H') : S.perp H' ≤ S.perp H :=
  fun _ ha x hx => ha x (h hx)

variable {M : RatModel o Ω} {K : Type} [Field K] {y : Sp K ⟶ M.Z} {z : M.Z}

theorem val_pow (h : ∀ w, y w ⤳ z) {a : Ω} (ha : a ∈ M.O z) (n : ℕ) : M.val y (a ^ n) = M.val y a ^ n :=
  map_pow (RatModel.valHomOf y z h) ⟨a, ha⟩ n

theorem val_prod (h : ∀ w, y w ⤳ z) {I : Type} (s : Finset I) {a : I → Ω} (ha : ∀ i, a i ∈ M.O z) :
    M.val y (∏ i ∈ s, a i) = ∏ i ∈ s, M.val y (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [RatModel.val_one]
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    rw [RatModel.val_mul h (ha i) (prod_mem fun j _ => ha j), ih]

theorem val_ne_zero (h : ∀ w, y w ⤳ z) {a : Ω} (h0 : a ≠ 0) (ha : a ∈ M.O z) (ha' : a⁻¹ ∈ M.O z) :
    M.val y a ≠ 0 := by
  have := RatModel.val_mul h ha ha'
  rw [mul_inv_cancel₀ h0, RatModel.val_one] at this
  exact left_ne_zero_of_mul_eq_one this.symm

theorem val_div (h : ∀ w, y w ⤳ z) {a b : Ω} (ha : a ∈ M.O z) (hb : b ∈ M.O z) (hb' : b⁻¹ ∈ M.O z) :
    M.val y (a / b) = M.val y a / M.val y b := by
  by_cases h0 : b = 0
  · simp [h0, RatModel.val_zero]
  have := RatModel.val_mul h hb hb'
  rw [mul_inv_cancel₀ h0, RatModel.val_one] at this
  rw [div_eq_mul_inv, RatModel.val_mul h ha hb', div_eq_mul_inv, eq_inv_of_mul_eq_one_right this.symm]

theorem ratio_le_one {I : Type} [Fintype I] {δ a a' f' : ℝ} {t v : I → ℝ} (hδ : 0 < δ) (hf0 : 0 ≤ f')
    (hf : f' ≤ δ * Real.exp (-a')) (ht0 : ∀ x, 0 ≤ t x) (ht : ∀ x, t x ≤ δ * Real.exp (-(v x))) {j C : ℕ}
    (h : j * a ≤ (j + 1) * a' + C * ∑ x, v x) :
    (f' / δ) ^ (j + 1) * (∏ x, t x / δ) ^ C / (δ * Real.exp (-a) / δ) ^ j ≤ 1 := by
  rw [mul_div_cancel_left₀ _ hδ.ne', div_le_one (by positivity)]
  have h1 : f' / δ ≤ Real.exp (-a') := by rwa [div_le_iff₀' hδ]
  have h2 : ∏ x, t x / δ ≤ Real.exp (-∑ x, v x) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun x _ => div_nonneg (ht0 x) hδ.le) fun x _ => ?_
    rw [div_le_iff₀' hδ]
    exact ht x
  have h3 : 0 ≤ ∏ x, t x / δ := Finset.prod_nonneg fun x _ => div_nonneg (ht0 x) hδ.le
  calc _ ≤ Real.exp (-a') ^ (j + 1) * Real.exp (-∑ x, v x) ^ C := by gcongr
    _ ≤ _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
      push_cast
      linarith

end Regular


open Regular in
theorem comparison_function_regular : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → ∀ (c : S.TT M z →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF (S.TT M z) c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖M.val (gPt p ≫ y) (S.FF (S.TT M z) c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → ∀ x₀ ∈ S.supI M z, ∀ j : ℕ, 1 ≤ j → ∃ C : ℕ, (S.FF _ c' k' / S.th x₀) ^ (j + 1) * (∏ᶠ x ∈ S.supI M ξ, S.th x / S.th x₀) ^ C / (S.FF _ c k / S.th x₀) ^ j ∈ M.O z) := by
  intro o Ω _ _ _ _ S M U₀ hO hLL hT h0 hI h01 h11 h12 z ξ c c' k k' hz hξ hcc hk hk' x₀ hx₀ j hj
  have hN : 1 ≤ S.N := le_trans one_le_two S.N_ge
  have hr := S.r_pos
  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  haveI : Fintype (S.supI M ξ) := Fintype.ofFinite _
  refine ⟨j * (j + 1) * Fintype.card (S.supI M ξ) * S.N * (S.r * S.N) ^ 2, ?_⟩
  rw [← finprod_set_coe_eq_finprod_mem, finprod_eq_prod_of_fintype]
  have hth : ∀ x, S.th x ∈ M.ringOn U₀ := fun x => hO.le (S.th_mem x)
  have hx0 : (S.th x₀)⁻¹ ∈ M.ringOn U₀ := hO.th_unit _ hx₀.1
  have hf : S.FF _ c k ∈ M.ringOn U₀ := hO.le (FF_mem S _ c k)
  have hf' : S.FF _ c' k' ∈ M.ringOn U₀ := hO.le (FF_mem S _ c' k')
  have hfi : (S.FF _ c k)⁻¹ ∈ M.ringOn U₀ := hO.FF_unit _ c k (hI.1 z).1 hk.1
  have e1 : S.FF _ c' k' / S.th x₀ ∈ M.ringOn U₀ := by
    rw [div_eq_mul_inv]; exact mul_mem hf' hx0
  have e2 : ∀ x, S.th x / S.th x₀ ∈ M.ringOn U₀ := fun x => by
    rw [div_eq_mul_inv]; exact mul_mem (hth x) hx0
  have e3 : S.FF _ c k / S.th x₀ ∈ M.ringOn U₀ := by
    rw [div_eq_mul_inv]; exact mul_mem hf hx0
  have e4 : ((S.FF _ c k / S.th x₀) ^ j)⁻¹ ∈ M.ringOn U₀ := by
    rw [← inv_pow, inv_div, div_eq_mul_inv]; exact pow_mem (mul_mem (hth _) hfi) j
  have e5 : ∏ x : S.supI M ξ, S.th x / S.th x₀ ∈ M.ringOn U₀ := prod_mem fun x _ => e2 x
  refine (hLL.1 U₀ le_rfl hO.ne z hz).2 _ ?_ fun p _ y hy => ?_
  · rw [div_eq_mul_inv]
    exact mul_mem (mul_mem (pow_mem e1 _) (pow_mem e5 _)) e4
  obtain ⟨y₀, hAt, hint, ⟨τ⟩⟩ := hT z p y hy
  obtain ⟨hsup, hH⟩ := h0 z p y y₀ τ hy hAt
  set w₀ := (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) with hw₀
  have hs : ∀ w, (gPt p ≫ y) w ⤳ w₀ :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have hle : M.ringOn U₀ ≤ M.O w₀ := RatModel.ringOn_le_O (hy.2 ⟨_, rfl⟩)
  have hTz : S.TT M z = S.perp τ.yy.ker := by rw [ThetaSys.TT, hH]
  have hTT : S.TT M ξ ≤ S.TT M z := perp_anti S (AddSubgroup.closure_mono (hI.2.1 ξ z hξ))
  have hTξ : S.TT M ξ ≤ S.perp τ.yy.ker := hTT.trans hTz.le
  obtain ⟨α, hα, hwα⟩ := (h01 p y₀ τ).1 (c.comp (AddSubgroup.inclusion hTz.ge))
  have hcα : ∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩ :=
    fun t h₁ h₂ => by rw [hwα]; rfl
  have hvf := h12 z p y y₀ τ hy hAt c k α hk hα hcα
  obtain ⟨β, -, hcβ, hvf'⟩ := (h11 p y₀ τ hint _ c' k' (FF_mem S _ c' k') (hI.1 ξ).1).2 hTξ
  rw [hAt] at hvf'
  have hex : ∀ x : S.Gam, ∃ w : τ.X, τ.yy x = QuotientAddGroup.mk w ∧ (x ∈ S.supI M ξ →
      ‖M.val (gPt p ≫ y) (S.th x)‖ ≤ τ.δ * Real.exp (-(τ.q w / ((S.r * S.N : ℕ) : ℝ) ^ 2))) := by
    intro x
    by_cases hx : x ∈ S.supI M ξ
    · obtain ⟨w, h1, h2⟩ := τ.tx x (by
        rw [hAt]
        exact val_ne_zero hs hx.1 (hle (hth x)) (hle (hO.th_unit x hx.1)))
      rw [hAt] at h2
      exact ⟨w, h1, fun _ => h2⟩
    · obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective (τ.yy x)
      exact ⟨w, hw.symm, fun h => absurd h hx⟩
  choose w hw hwv using hex
  have hmem := ((h01 p y₀ τ).2 _ (hI.1 ξ).1 hTξ w hw (S.supI M ξ) (hI.1 ξ).2.symm (α - β)).1
    (fun t h₂ h₁ => by
      rw [map_sub, AddMonoidHom.sub_apply, ← hcβ t h₁ h₂, ← hcα t (hTT h₁) h₂, hcc t (hTT h₁) h₁, sub_self])
  rw [Set.image_eq_range] at hmem
  have hNpos : (0 : ℝ) < S.N := by exact_mod_cast hN
  have hN'pos : (0 : ℝ) < ((S.r * S.N : ℕ) : ℝ) := by exact_mod_cast NeZero.pos _
  obtain ⟨v₁, hv₁⟩ := lattice_inequality τ.X τ.q (nonneg_of_tendsto τ.q τ.pos) (S.supI M ξ) S.N (S.r * S.N) j hN
    (dvd_mul_left _ _) hj (fun x => w x) (fun x => w x) (fun x => τ.q (w x) / ((S.r * S.N : ℕ) : ℝ) ^ 2) β α
    (τ.q β / S.N) (fun x => ⟨0, by simp⟩) (fun x => by rw [mul_div_cancel₀ _ (by positivity)])
    (by rw [mul_div_cancel₀ _ hNpos.ne']) hmem
  have hfin := le_trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hα v₁) hNpos.le)
    (Nat.cast_nonneg j)) hv₁
  have := ratio_le_one τ.δ_pos (norm_nonneg _) hvf' (fun x : S.supI M ξ => norm_nonneg _)
    (fun x => hwv x x.2) hfin
  rw [val_div hs (hle (mul_mem (pow_mem e1 _) (pow_mem e5 _))) (hle (pow_mem e3 _)) (hle e4),
    RatModel.val_mul hs (hle (pow_mem e1 _)) (hle (pow_mem e5 _)), val_pow hs (hle e1), val_pow hs (hle e5),
    val_pow hs (hle e3), val_prod hs _ (fun x : S.supI M ξ => hle (e2 x)),
    val_div hs (hle hf') (hle (hth _)) (hle hx0), val_div hs (hle hf) (hle (hth _)) (hle hx0)]
  simp only [fun x => val_div hs (hle (hth x)) (hle (hth _)) (hle hx0), norm_div, norm_mul, norm_pow, norm_prod]
  rw [(hsup x₀).1 hx₀, hvf]
  exact this

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_padicLift_torsionPoint_invertibleOrder : ∀ (p : ℕ) [Fact p.Prime] (B : Scheme.{0}) (G : Over B) [GrpObj G], IsSemiAbelian G → ∀ (y : Sp (OO p) ⟶ B) (n : ℕ), IsUnit (n : Γ(B, ⊤)) → ∀ t : Over.mk (spMap (IsLocalRing.residue (OO p)) ≫ y) ⟶ G, t ^ n = 1 → ∃ b : Over.mk y ⟶ G, b ^ n = 1 ∧ spMap (IsLocalRing.residue (OO p)) ≫ b.left = t.left := by
  first | exact @GlobalTheory.ZJ.exists_torsion_lift_of_residue | exact GlobalTheory.ZJ.exists_torsion_lift_of_residue | (intros; apply GlobalTheory.ZJ.exists_torsion_lift_of_residue <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

theorem _root_.GlobalTheory.T.exists_functionField_of_isDominant' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ M.Z) [IsDominant q], ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra o Ω') (φ : Ω →ₐ[o] Ω') (pt : Sp Ω' ⟶ X), Set.range pt = {genericPoint X} ∧ (∀ x : Ω', ∃ (U : X.Opens) (f : Γ(X, U)), (U : Set X).Nonempty ∧ valF pt U f = x) ∧ pt ≫ q = spMap φ.toRingHom ≫ M.pt := by
  first | exact @GlobalTheory.ZH.RatModel.exists_functionField_of_isDominant | exact GlobalTheory.ZH.RatModel.exists_functionField_of_isDominant | (intros; apply GlobalTheory.ZH.RatModel.exists_functionField_of_isDominant <;> assumption)
end
