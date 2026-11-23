module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSysFFMemFinitePerpProj
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle076
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

namespace ThetaSys

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω)

theorem supI_subset_of_specializes {ξ z : M.Z} (h : ξ ⤳ z) : S.supI M z ⊆ S.supI M ξ :=
  fun _ hx => ⟨hx.1, fun j => M.O_le_of_specializes h (hx.2 j)⟩

theorem exists_isClosed_supI_eq [JacobsonSpace M.Z] (ξ : M.Z) (W : M.Z.Opens) (hξ : ξ ∈ W) :
    ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have hV : IsOpen ((W : Set M.Z) ∩ ⋂ a ∈ S.supI M ξ, {z | M.Div S.th a z}) :=
    W.isOpen.inter ((Set.toFinite _).isOpen_biInter fun a _ => M.isOpen_setOf_div _ _)
  obtain ⟨x, ⟨⟨hxW, hxI⟩, hxc⟩, hx⟩ := nonempty_inter_closedPoints
    (Z := ((W : Set M.Z) ∩ ⋂ a ∈ S.supI M ξ, {z | M.Div S.th a z}) ∩ closure {ξ})
    ⟨ξ, ⟨hξ, Set.mem_iInter₂.mpr fun _ ha => ha⟩, subset_closure rfl⟩
    (hV.isLocallyClosed.inter isClosed_closure.isLocallyClosed)
  have hs : ξ ⤳ x := specializes_iff_mem_closure.mpr hxc
  exact ⟨x, hxW, hx, hs, (S.supI_subset_of_specializes M hs).antisymm
    fun a ha => Set.mem_iInter₂.mp hxI a ha⟩

theorem Over₀.supI_eq {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens} (h : S.Over₀ M U₀)
    {ξ : M.Z} (hξ : ξ ∈ U₀) : S.supI M ξ = {x | S.th x ≠ 0} := by
  ext x
  refine ⟨fun hx => hx.1, fun hx => ⟨hx, fun j => ?_⟩⟩
  have h1 : S.th j / S.th x ∈ M.ringOn U₀ := by
    rw [div_eq_mul_inv]
    exact mul_mem (h.le (S.th_mem j)) (h.th_unit x hx)
  exact (Algebra.mem_iInf.mp (Algebra.mem_iInf.mp h1 ξ) hξ :)

end ThetaSys

theorem isoFree_TT_and_supI_specializes :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) := by
  intro o Ω _ _ _ _ S M U₀ hO ⟨hL, hJ⟩ hT hS
  have hpp := (GlobalTheory.thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.1
  refine ⟨fun ξ => ⟨?_, hpp _⟩, fun ξ z h => S.supI_subset_of_specializes M h, fun ξ hξ => ?_,
    fun ξ W hξ => S.exists_isClosed_supI_eq M ξ W hξ⟩
  · obtain ⟨x, -, hx, -, he⟩ := S.exists_isClosed_supI_eq M ξ ⊤ trivial
    obtain ⟨p, hp, y, hy⟩ := (hL U₀ le_rfl hO.ne x hx).1
    obtain ⟨y₀, hy₀, -, ⟨τ⟩⟩ := hT x p y hy
    have h1 : S.HH M ξ = τ.yy.ker := by
      rw [← (hS x p y y₀ τ hy hy₀).2, ThetaSys.HH, ThetaSys.HH, he]
    rw [ThetaSys.TT, h1]
    exact τ.isoFree
  · have h1 : S.perp ⊥ = ⊤ := by
      refine top_unique fun a _ h hh => ?_
      rw [AddSubgroup.mem_bot.mp hh]
      simp [eStd]
    rw [ThetaSys.TT, ThetaSys.HH, hO.supI_eq hξ, S.supp, ← h1, hpp]

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory

theorem norm_val_FF_eq_of_div :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → ∀ (c : S.TT M z →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF (S.TT M z) c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖M.val (gPt p ≫ y) (S.FF (S.TT M z) c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) := by
  intro o Ω _ _ _ _ S M U₀ hO h0 h1 _ z p _ y y₀ τ hC hA
  have hT : S.TT M z = S.perp τ.yy.ker := by
    rw [ThetaSys.TT, (h0 z p y y₀ τ hC hA).2]
  obtain ⟨hmem, -, hpp, -⟩ := thetaSys_FF_mem_finite_perp_proj o Ω S
  rw [hT]
  intro c k α hdiv hα hc
  have hcw : c = τ.wt α := AddMonoidHom.ext fun t => hc t.1 t.2 t.2
  have hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a => by
    rw [hA]
    exact hC.norm_val_le_one ((M.O z).algebraMap_mem a)
  have hk : M.val (gPt p ≫ y) (S.FF _ c k) = y₀ ⟨_, hmem _ c k⟩ := (hA ⟨_, hmem _ c k⟩).symm
  refine le_antisymm ?_ ?_
  · rw [hk]
    exact (h1 p y₀ τ hint _ c k (hmem _ c k) τ.isoFree).1 le_rfl
      (τ.isoFree.1.trans (hpp _).le) α hα hc
  · subst hcw
    obtain ⟨k₁, hk₁, he⟩ := τ.eq α hα
    rw [← he, hA]
    let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
    have hw : ∀ w', (gPt p ≫ y) w' ⤳ (gPt p ≫ y) w := fun w' => by
      have : (gPt p ≫ y) w' ∈ Set.range (gPt p ≫ y) := ⟨w', rfl⟩
      rw [RatModel.range_eq_singleton _ w] at this
      rw [this]
    have hU : (gPt p ≫ y) w ∈ (U₀ : Set M.Z) := hC.2 ⟨w, rfl⟩
    have hq := hdiv.2 k₁
    have hmul := RatModel.val_mul hw
      (RatModel.O_le_of_specializes (RatModel.gPt_specializes hC.1 w) hq)
      (RatModel.ringOn_le_O hU (hO.le (hmem _ (τ.wt α) k)))
    rw [div_mul_cancel₀ _ hdiv.1] at hmul
    change ‖M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k₁)‖ ≤ _
    rw [hmul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hC.norm_val_le_one hq)

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ThetaBound

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

theorem proj_mul_proj (T T' : AddSubgroup S.Gam) (h : T' ≤ T) (hT : T ≤ S.perp T)
    (hT' : S.IsoFree T') (c : T →+ ZMod S.N) (c' : T' →+ ZMod S.N)
    (hc : ∀ t : T', c' t = c (AddSubgroup.inclusion h t)) :
    S.proj T' c' * S.proj T c = S.proj T c := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero S.N := ⟨by omega⟩
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have := Fintype.ofFinite T
  have := Fintype.ofFinite T'
  obtain ⟨d, ⟨e⟩⟩ := hT'.2
  have hζ : IsPrimitiveRoot S.ζN S.N := S.prim.pow (NeZero.pos _) (by ring)
  let χ : AddChar (ZMod S.N) o := AddChar.zmodChar S.N hζ.pow_eq_one
  have hu : IsUnit (Nat.card T' : o) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
    exact S.unit.pow _
  have h1 : S.proj T c = Ring.inverse (Nat.card T : o) • ∑ t : T, χ (-c t) • S.ρ t := by
    rw [← finsum_eq_sum_of_fintype]; rfl
  have h2 : S.proj T' c' = Ring.inverse (Nat.card T' : o) • ∑ t : T', χ (-c' t) • S.ρ t := by
    rw [← finsum_eq_sum_of_fintype]; rfl
  have h3 : ∀ u : T', (χ (-c' u) • S.ρ u) * ∑ t : T, χ (-c t) • S.ρ t
      = ∑ t : T, χ (-c t) • S.ρ t := fun u => by
    conv_rhs => rw [← Equiv.sum_comp (Equiv.addLeft (AddSubgroup.inclusion h u))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_mul_smul_comm, ← AddChar.map_add_eq_mul, S.ρ_add _ _ (by
      rw [hT (h u.2) t t.2, smul_zero]), hc]
    simp only [Equiv.coe_addLeft, map_add (f := _), neg_add]
    rfl
  have h4 : ∀ u : T', (χ (-c' u) • S.ρ u) * S.proj T c = S.proj T c := fun u => by
    rw [h1, mul_smul_comm, h3]
  rw [h2, smul_mul_assoc, Finset.sum_mul]
  simp_rw [h4]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul o,
    smul_smul, Ring.inverse_mul_cancel _ hu, one_smul]

theorem norm_FF_le {p : ℕ} [Fact p.Prime] (y : S.R →+* PadicAlgCl p)
    (hy : ∀ a : o, ‖y (algebraMap o S.R a)‖ ≤ 1) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N)
    (k : _) (hk : S.FF T c k ∈ S.R) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ t : T, ‖∑ j, y (algebraMap o S.R (S.proj T c j k.1)) * y ⟨S.ev t j, S.ev_mem _ j⟩‖ ≤ B) :
    ‖y ⟨S.FF T c k, hk⟩‖ ≤ B := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have := Fintype.ofFinite T
  have h1 : (⟨S.FF T c k, hk⟩ : S.R) = ∑ t : T, algebraMap o S.R (S.ζ ^ (k.2 t).val) *
      ∑ j, algebraMap o S.R (S.proj T c j k.1) * ⟨S.ev t j, S.ev_mem _ j⟩ := by
    apply Subtype.ext
    simp only [ThetaSys.FF, finsum_eq_sum_of_fintype, AddSubmonoidClass.coe_finsetSum,
      MulMemClass.coe_mul, SubalgebraClass.coe_algebraMap]

  rw [h1, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB fun t _ => ?_

  rw [map_mul, norm_mul, map_sum]
  simp_rw [map_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hy _)).trans (h t)

end GlobalTheory.ThetaBound

namespace GlobalTheory

open ThetaBound

theorem thetaSys_norm_FF_le_exp :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω), (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) := by
  intro o Ω _ _ _ hA S H p _ y τ hy T c k hk hT
  obtain ⟨-, -, hperp, href⟩ := thetaSys_FF_mem_finite_perp_proj o Ω S
  have hpos : ∀ α : τ.X, 0 ≤ τ.δ * Real.exp (-(τ.q α / S.N)) := fun α =>
    mul_nonneg τ.δ_pos.le (Real.exp_pos _).le
  refine ⟨fun h1 h2 α hα hc => ?_, fun h1 => ?_⟩
  · refine norm_FF_le S y hy T c k hk (hpos α) fun t => ?_
    rw [← proj_mul_proj S T _ h1 hT.1 τ.isoFree c (τ.wt α) fun u => (hc u (h1 u.2) u.2).symm]

    simp_rw [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hpos α) fun l _ => ?_
    simp_rw [mul_right_comm _ (y (algebraMap o S.R (S.proj T c l k.1)))]
    rw [← Finset.sum_mul, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hy _)).trans (τ.le α hα t (h2 t.2) l)
  · have hN := S.N_ge
    have hr := S.r_pos
    have : NeZero S.N := ⟨by omega⟩
    have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
    choose a ha hwa using (H p y τ).1
    obtain ⟨d, ⟨e⟩⟩ := hT.2
    obtain ⟨π, hπ⟩ := ThetaProj.exists_retraction T e
    have hfin : Finite (S.perp τ.yy.ker →+ ZMod S.N) := DFunLike.finite _
    set s := {c' : S.perp τ.yy.ker →+ ZMod S.N | c'.comp (AddSubgroup.inclusion h1) = c} with hs
    have hne : s.Nonempty := ⟨(c.comp π).comp (AddSubgroup.subtype _), by
      ext t
      exact congrArg c (hπ t)⟩
    obtain ⟨c₀, hc₀, hmax⟩ := Set.exists_max_image s
      (fun c' => τ.δ * Real.exp (-(τ.q (a c') / S.N))) (Set.toFinite _) hne
    refine ⟨a c₀, ha c₀, fun t h₁ h₂ => ?_, ?_⟩
    · rw [hwa, ← show _ = c from hc₀]
      rfl
    · refine norm_FF_le S y hy T c k hk (hpos _) fun t => ?_
      rw [href _ T h1 τ.isoFree hT c, finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _)]

      simp_rw [Matrix.sum_apply, map_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hpos _) fun c' hc' => ?_
      have ht : (t : S.Gam) ∈ τ.yy.ker := by
        rw [← hperp τ.yy.ker]
        exact τ.isoFree.1 (h1 t.2)
      have := τ.le (a c') (ha c') t ht k.1
      rw [hwa] at this
      exact this.trans (hmax c' ((Set.Finite.mem_toFinset _).mp hc'))

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem resG_resG_apply {X : Scheme.{0}} {U V T : X.Opens} (h : V ≤ U) (h' : T ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem exists_secOn_glue {X : Scheme.{0}} (B : LB X) (V : X.Opens) {κ : Type} (T : κ → X.Opens)
    (hT : ∀ k, T k ≤ V) (hV : ∀ x ∈ V, ∃ k, x ∈ T k) (σ : ∀ k j, Γ(X, T k ⊓ B.U j))
    (hσ : ∀ k, σ k ∈ secOn B (T k))
    (hc : ∀ k k' j, resG X (inf_le_inf_right _ inf_le_left : (T k ⊓ T k') ⊓ B.U j ≤ T k ⊓ B.U j) (σ k j) =
      resG X (inf_le_inf_right _ inf_le_right : (T k ⊓ T k') ⊓ B.U j ≤ T k' ⊓ B.U j) (σ k' j)) :
    ∃ τ ∈ secOn B V, ∀ k j, resG X (inf_le_inf_right _ (hT k)) (τ j) = σ k j := by
  have H : ∀ j, ∃ τ : Γ(X, V ⊓ B.U j), ∀ k, resG X (inf_le_inf_right _ (hT k)) τ = σ k j := fun j => by
    obtain ⟨g, hg, -⟩ := X.sheaf.existsUnique_gluing' (fun k => T k ⊓ B.U j) (V ⊓ B.U j)
      (fun k => homOfLE (inf_le_inf_right _ (hT k)))
      (fun x hx => by
        obtain ⟨k, hk⟩ := hV x hx.1
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk, hx.2⟩) (fun k => σ k j) (fun k k' => by
        have e : (T k ⊓ B.U j) ⊓ (T k' ⊓ B.U j) ≤ (T k ⊓ T k') ⊓ B.U j :=
          fun x hx => ⟨⟨hx.1.1, hx.2.1⟩, hx.1.2⟩
        have := congrArg (resG X e) (hc k k' j)
        rw [resG_resG_apply, resG_resG_apply] at this
        exact this)
    exact ⟨g, hg⟩
  choose τ hτ using H
  refine ⟨τ, fun i j => ?_, fun k j => hτ j k⟩
  refine X.sheaf.eq_of_locally_eq' (fun k => T k ⊓ B.U i ⊓ B.U j) (V ⊓ B.U i ⊓ B.U j)
    (fun k => homOfLE (inf_le_inf_right _ (inf_le_inf_right _ (hT k))))
    (fun x hx => by
      obtain ⟨k, hk⟩ := hV x hx.1.1
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, ⟨hk, hx.1.2⟩, hx.2⟩) _ _ fun k => ?_
  have h := hσ k i j
  rw [← hτ i k, ← hτ j k, resG_resG_apply, resG_resG_apply] at h
  change resG X (inf_le_inf_right _ (inf_le_inf_right _ (hT k))) _ =
    resG X (inf_le_inf_right _ (inf_le_inf_right _ (hT k))) _
  rw [map_mul, resG_resG_apply, resG_resG_apply, resG_resG_apply]
  exact h

theorem sum_mul_mem_secOn {X : Scheme.{0}} (B : LB X) (V : X.Opens) {I : Type} [Fintype I] (f : I → Γ(X, V))
    (σ : I → ∀ j, Γ(X, V ⊓ B.U j)) (hσ : ∀ i, σ i ∈ secOn B V) :
    (fun j => ∑ i, resG X inf_le_left (f i) * σ i j) ∈ secOn B V := fun j j' => by

  simp only [map_sum, map_mul, Finset.mul_sum, resG_resG_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hσ i j j', mul_left_comm]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

theorem ZHPre.genVal_res (k : ℤ) {I : Type} [Fintype I]
    (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R)))) (c : I → Ω) {V V' : Q.G.left.Opens} (e : V' ≤ V)
    (σ : ∀ j, Γ(Q.G.left, V ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U j))
    (h : GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c V σ) :
    GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c V' (fun j => resG _ (inf_le_inf_right _ e) (σ j)) := by
  intro K _ β g r jP jL h1 h2 h3 h4 h5
  rw [h K β g r jP jL h1 h2 h3 h4 (h5.trans e)]
  congr 1
  have hU : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (V' ⊓
      (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U (fun _ => jL)) :=
    fun w _ => ⟨h5 ⟨w, rfl⟩, Set.mem_iInter.2 fun _ => h4 ⟨w, rfl⟩⟩
  exact (valR_res (g ≫ Q.φ) _ hU _).symm

theorem ZHPre.genVal_of_cover (k : ℤ) {I : Type} [Fintype I]
    (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R)))) (c : I → Ω) {V : Q.G.left.Opens} {κ : Type}
    (T : κ → Q.G.left.Opens) (hT : ∀ a, T a ≤ V) (hV : ∀ x ∈ V, ∃ a, x ∈ T a)
    (σ : ∀ j, Γ(Q.G.left, V ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U j))
    (h : ∀ a, GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c (T a)
      (fun j => resG _ (inf_le_inf_right _ (hT a)) (σ j))) :
    GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t c V σ := by
  intro K _ β g r jP jL h1 h2 h3 h4 h5
  obtain ⟨a, ha⟩ := hV _ (h5 ⟨IsLocalRing.closedPoint K, rfl⟩)
  have h6 : Set.range (g ≫ Q.φ) ⊆ T a := by
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum K) w (IsLocalRing.closedPoint K)]
    exact ha
  rw [h a K β g r jP jL h1 h2 h3 h4 h6]
  congr 1
  have hU : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (T a ⊓
      (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U (fun _ => jL)) :=
    fun w _ => ⟨h6 ⟨w, rfl⟩, Set.mem_iInter.2 fun _ => h4 ⟨w, rfl⟩⟩
  exact valR_res (g ≫ Q.φ) _ hU _

theorem ZHPre.genVal_sum (k : ℤ) {I J : Type} [Fintype I] [Fintype J]
    (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R)))) (c : J → I → Ω) (W : M.Z.Opens)
    (hW : (W : Set M.Z).Nonempty) (f : J → Γ(M.Z, W))
    (σ : J → ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ W ⊓
      (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U j))
    (h : ∀ i, GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t (c i) _ (σ i)) :
    GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w k t (fun l => ∑ i, valF M.pt W (f i) * c i l) _
      (fun j => ∑ i, resG _ inf_le_left ((Q.G.hom.appLE W _ le_rfl).hom (f i)) * σ i j) := by
  intro K _ β g r jP jL h1 h2 h3 h4 h5
  have hV : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ W) := fun w _ => h5 ⟨w, rfl⟩
  have hU : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ W ⊓
      (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => k)).U (fun _ => jL)) :=
    fun w _ => ⟨h5 ⟨w, rfl⟩, Set.mem_iInter.2 fun _ => h4 ⟨w, rfl⟩⟩
  have hp : (g ≫ Q.φ) ≫ Q.G.hom = spMap β ≫ M.pt := by
    rw [Category.assoc, Q.cart.1.w, ← h1]
    rfl
  have hf : ∀ i, (valMap (g ≫ Q.φ) _ hU).hom (resG _ inf_le_left ((Q.G.hom.appLE W _ le_rfl).hom (f i))) =
      β (valF M.pt W (f i)) := fun i => by
    rw [← valR_eq, valR_res _ _ hU, valR_appLE _ _ _ hV, hp, valR_spMap_comp β M.pt W (M.top_le_preimage_pt hW),
      valF_eq_valR]
  have hi := fun i => h i K β g r jP jL h1 h2 h3 h4 h5

  rw [valF_eq_valR (g ≫ Q.φ), valR_eq _ _ hU, map_sum, Finset.mul_sum]

  simp only [map_sum, map_mul, Finset.sum_mul, hf]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, ← valR_eq, ← valF_eq_valR, ← hi i, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => mul_assoc _ _ _

end GlobalTheory.ZH

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem exists_secOn_genVal_of_bases : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀), (U₀ : Set M.Z).Nonempty → (∀ (W : M.Z.Opens) (x₀ : S.Gam) (b : Matrix S.J S.J Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range b)) → ∃ σ : S.J → ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ W ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))).U j), ∀ i, σ i ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W) ∧ GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => b i l / S.th x₀) _ (σ i)) → ∀ (W : M.Z.Opens) (x₀ : S.Gam) (v : S.J → Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ v ∈ EE.E z) → ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W), GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => v l / S.th x₀) _ σ := by
  intro o Ω _ _ _ S ρ M U₀ EE Q hU hb W x₀ v hv
  have H : ∀ z : W, ∃ T : M.Z.Opens, z.1 ∈ T ∧ T ≤ W ∧
      ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ T),
        GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => v l / S.th x₀) _ σ := by
    rintro ⟨z, hz⟩
    obtain ⟨U, b, hzU, -, hE⟩ := EE.loc z
    have h1 := (hv z hz).2
    rw [hE z hzU] at h1
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (M.O z) (v := fun i l => b i l)).1 h1
    let T : M.Z.Opens := W ⊓ U ⊓ ⟨⋂ i, {z' | (a i : Ω) ∈ M.O z'},
      isOpen_iInter_of_finite fun i => M.isOpen_setOf_mem_O _⟩
    have hzT : z ∈ T := ⟨⟨hz, hzU⟩, Set.mem_iInter.2 fun i => (a i).2⟩
    have hne : (T : Set M.Z).Nonempty := ⟨z, hzT⟩
    have h2 : ∀ i, ∃ f : Γ(M.Z, T), valF M.pt T f = a i := fun i =>
      (RatModel.mem_ringOn_iff_exists hne).1 (RatModel.mem_ringOn.2 fun z' hz' => Set.mem_iInter.1 hz'.2 i)
    choose f hf using h2
    obtain ⟨σ, hσ⟩ := hb T x₀ b fun z' hz' => ⟨(hv z' hz'.1.1).1, hE z' hz'.1.2⟩
    refine ⟨T, hzT, inf_le_left.trans inf_le_left, _,
      sum_mul_mem_secOn _ _ (fun i => (Q.G.hom.appLE T _ le_rfl).hom (f i)) σ fun i => (hσ i).1, ?_⟩
    have h3 := Q.genVal_sum S.N ρ.s (fun i l => b i l / S.th x₀) T hne f σ fun i => (hσ i).2
    have h4 : (fun l => ∑ i, valF M.pt T (f i) * (b i l / S.th x₀)) = fun l => v l / S.th x₀ := by
      funext l
      rw [← ha, Finset.sum_apply, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hf, ← mul_div_assoc]
      rfl
    rw [h4] at h3
    exact h3
  choose T hz hT σ hσ hg using H
  have hle : ∀ z, Q.G.hom ⁻¹ᵁ T z ≤ Q.G.hom ⁻¹ᵁ W := fun z x hx => hT z hx
  have hcov : ∀ x ∈ Q.G.hom ⁻¹ᵁ W, ∃ z, x ∈ Q.G.hom ⁻¹ᵁ T z := fun x hx => ⟨⟨Q.G.hom x, hx⟩, hz _⟩
  obtain ⟨τ, hτ, hr⟩ := exists_secOn_glue _ (Q.G.hom ⁻¹ᵁ W) (fun z => Q.G.hom ⁻¹ᵁ T z) hle hcov σ hσ
    fun z z' j => congrFun (Q.eq_of_genVal hU _ _ _ _ _ _ (Q.genVal_res _ _ _ inf_le_left _ (hg z))
      (Q.genVal_res _ _ _ inf_le_right _ (hg z'))) j
  refine ⟨τ, hτ, Q.genVal_of_cover _ _ _ _ hle hcov τ fun z => ?_⟩
  have h5 := hg z
  rw [← funext (hr z)] at h5
  exact h5

end GlobalTheory.ZH
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaConstantTerm_representative_dependence : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (m : ℕ), Odd m → ∀ (p p' : N.QT (m ^ 2)) (χ : N.X), (∀ z, p'.1.1.toAdd = p.1.1.toAdd + m ^ 2 • z → p'.1.2 = p.1.2 * N.io z → N.txT m p' χ = N.txT m p (χ + m • z)) ∧ (∀ t : Multiplicative N.X →* Oˣ, p'.1.1 = p.1.1 → p'.1.2 = p.1.2 * N.tor t → N.txT m p' χ = (t p.1.1 ^ ((m ^ 2 - 1) / 2) * t (Multiplicative.ofAdd (p.1.1.toAdd + m • χ)) : Oˣ) * N.txT m p χ) := by
  first | exact @GlobalTheory.Ex.txT_shift | exact GlobalTheory.Ex.txT_shift | (intros; apply GlobalTheory.Ex.txT_shift <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

theorem _root_.GlobalTheory.T.isPure_pullbackSection_mul_weightGenerator : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → ∀ α : Φ.E.X, UFib.GenWt Φ.D.i t α → ∀ (b : LB.Sec (LB.LinComb L ψ ε)) (φ : (Φ.H 1).Sec), UFib.Red Φ c t b φ → Φ.Pure α φ := by
  first | exact @GlobalTheory.ZH.UFib.pure_of_red | exact GlobalTheory.ZH.UFib.pure_of_red | (intros; apply GlobalTheory.ZH.UFib.pure_of_red <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

theorem _root_.GlobalTheory.T.universalBasis_move_baseChange : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (P : PolAV S) (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → ∀ (n : ℤ) (κ : Type) [Fintype κ] (T₀ : Over S) (τ : S' ⟶ T₀.left), τ ≫ T₀.hom = f → ∀ b₀ : κ → SecM P.A P.L n T₀, UnivBasis P n b₀ → ∃ b : κ → SecM P'.A P'.L n (baseOver S'), UnivBasis P' n b := by
  first | exact @GlobalTheory.UnivBasisMove.univBasis_move | exact GlobalTheory.UnivBasisMove.univBasis_move | (intros; apply GlobalTheory.UnivBasisMove.univBasis_move <;> assumption)
end
