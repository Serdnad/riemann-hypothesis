module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle012
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle016
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsOfLocal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiagQConjTranspose
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.EntOfMapEqZero
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.G2

theorem jordan_invariants_holds : JordanInv := by
  intro K F V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _hK hF h h' _hs _hs' X X' L L' hL hL' 𝔭 h𝔭 b a b' a'
    hJ hJ' hiso j
  obtain ⟨f⟩ := hiso
  obtain ⟨g⟩ := disc_equiv hF h𝔭 hL hJ.1 hJ.2.1 hJ.2.2.1 hJ.2.2.2.1 hJ.2.2.2.2
  obtain ⟨g'⟩ := disc_equiv hF h𝔭 hL' hJ'.1 hJ'.2.1 hJ'.2.2.1 hJ'.2.2.2.1 hJ'.2.2.2.2
  have hc := card_quot_smul_top_congr ((g.symm.trans f).trans g') (extP K 𝔭 ^ j)
  rw [card_pi_quot, card_pi_quot] at hc
  exact Nat.pow_right_injective (two_le_absNorm h𝔭) hc

end Formalism.L2.SG.Pf.Cnt
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def SummandLoc : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    ∀ X : Submodule K V, ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ Λ : Submodule (𝓞 K) V,
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) →
      ∃ π : V →ₗ[K] V, (∀ v, π v ∈ X) ∧ (∀ x ∈ X, π x = x) ∧ ∀ y ∈ Λ, π y ∈ Λ

def RieszH : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h → ∀ f : V →ₗ[K] K, ∃ x : V, ∀ y, h x y = f y

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem coe_algebraMap_OF (t : 𝓞 F) :
    ((algebraMap (𝓞 F) (𝓞 K) t : 𝓞 K) : K) = algebraMap F K (t : F) := by
  change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = _
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]

theorem form_mem_locF_of (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V}
    {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime) {v y : V}
    (hv : v ∈ locF 𝔭 (dualIn h X L)) (hy : y ∈ locF 𝔭 L) : h y v ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  have := h𝔭
  obtain ⟨t, ht, hty⟩ := (LocalSpans.mem_locF 𝔭 L y).1 hy
  obtain ⟨u, hu, huv⟩ := (LocalSpans.mem_locF 𝔭 _ v).1 hv
  have H := (mem_dual_iff.1 huv.2) _ hty
  refine (LocalSpans.mem_locF 𝔭 _ _).2 ⟨t * u, fun hm => (h𝔭.mem_or_mem hm).elim ht hu, ?_⟩
  have hst : starRingEnd K (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t)) =
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) := by
    have e := coe_algebraMap_OF (K := K) t
    change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = _ at e
    rw [e, starRingEnd_apply]
    exact (hF _).2 ⟨_, rfl⟩
  rw [form_ozmul_right, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) y, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, hst, algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) (h y v)] at H
  rw [map_mul, mul_smul, smul_comm]
  exact H

theorem riesz_hermitian_holds : RieszH := by
  intro K V _ _ _ _ _ h _ hnd f
  classical
  let b := Module.finBasis K V
  let Φ : (Fin (finrank K V) → K) →ₗ[K] Module.Dual K V :=
    { toFun := fun c => ∑ i, c i • h (b i)
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by simp [Finset.smul_sum, smul_smul] }
  have hΦ : ∀ c, h (∑ i, star (c i) • b i) = Φ c := by
    intro c

    simp [Φ, map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply, star_star]
  have hinj : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    have hx : (∑ i, star (c i) • b i) = 0 := by
      apply hnd
      intro y
      rw [hΦ, hc]
      rfl
    funext i
    have := Fintype.linearIndependent_iff.mp b.linearIndependent (fun i => star (c i)) hx i
    simpa using this
  have hsurj : Function.Surjective Φ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
    rw [Module.finrank_fin_fun, Subspace.dual_finrank_eq]
  obtain ⟨c, hc⟩ := hsurj f
  exact ⟨∑ i, star (c i) • b i, fun y => by rw [hΦ, hc]⟩

theorem mem_of_smul_mem {X : Submodule K V} {𝔭 : Ideal (𝓞 F)} {u : 𝓞 F} (hu : u ∉ 𝔭) {v : V}
    (hv : algebraMap (𝓞 F) (𝓞 K) u • v ∈ X) : v ∈ X := by
  have hu0 : (u : F) ≠ 0 := by
    intro e
    apply hu
    have : u = 0 := RingOfIntegers.ext (by simpa using e)
    rw [this]
    exact 𝔭.zero_mem
  have hc0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u) ≠ 0 := by
    have e := coe_algebraMap_OF (K := K) u
    change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u) = _ at e
    rw [e]
    exact (map_ne_zero _).2 hu0
  have h1 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u) • v ∈ X := by
    rw [algebraMap_smul]
    exact hv
  have := X.smul_mem (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u))⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this

theorem projOnto_of (hS : SummandLoc) (hR : RieszH) : ProjOnto := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd X Y hc hXY L hL 𝔭 h𝔭 Λ hΛ0 hΛd hΛX v hv
  have hp : 𝔭.IsPrime := h𝔭.isPrime
  obtain ⟨π, hπX, hπid, hπΛ⟩ := hS K F V X 𝔭 h𝔭 Λ hΛ0
  obtain ⟨x, hx⟩ := hR K V h hs hnd ((h v).comp π)
  have key : ∀ y, h y x = h (π y) v := by
    intro y
    rw [← hs.eq x y, hx y, LinearMap.comp_apply, hs.eq v (π y)]
  have hvX : v ∈ X := by
    obtain ⟨u, hu, huv⟩ := (LocalSpans.mem_locF 𝔭 _ v).1 hv
    exact mem_of_smul_mem hu huv.1
  have hxΛ : x ∈ Λ := by
    rw [← hΛd]
    show ∀ y ∈ Λ, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
    intro y hy
    rw [key]
    have : π y ∈ locF 𝔭 L := by
      rw [← hΛX]
      exact ⟨hπΛ y hy, hπX y⟩
    exact form_mem_locF_of hF hp hv this
  refine ⟨x, hxΛ, ?_⟩
  set w := X.projection Y hc x - v with hw
  have hwX : w ∈ X := X.sub_mem (Submodule.projection_apply_mem hc x) hvX
  have hw0 : w = 0 := by
    apply hnd
    intro z
    have ez := Submodule.projection_add_projection_eq_self hc z
    rw [← ez, map_add (f := _)]
    have h1 : h w (Y.projection X hc.symm z) = 0 := hXY w hwX _ (Submodule.projection_apply_mem _ z)
    have hzX : X.projection Y hc z ∈ X := Submodule.projection_apply_mem hc z
    have ex := Submodule.projection_add_projection_eq_self hc x
    have e3 : h (X.projection Y hc z) (X.projection Y hc x) = h (X.projection Y hc z) x := by
      conv_rhs => rw [← ex]
      rw [map_add (f := _), hXY _ hzX _ (Submodule.projection_apply_mem _ x), add_zero]
    have h2 : h (X.projection Y hc z) w = 0 := by
      rw [hw, map_sub, e3, key, hπid _ hzX, sub_self]
    rw [h1, add_zero, ← hs.eq (X.projection Y hc z) w, h2, map_zero]
  exact sub_eq_zero.mp hw0

end Formalism.L2.SG.Pf.G6
end
end

section

namespace Formalism.L2.SG.Pf.Cnt

theorem glueExists_of (hloc : Formalism.L2.SG.Pf.G7.GlueLocal) : GlueExists :=
  Formalism.L2.SG.Pf.G7.glueExists_of_local hloc

theorem glueExists_of_fam (hJ : JordanExists) (hV : Formalism.L2.SG.Pf.GluingBases.GlueVecs)
    (h0 : Formalism.L2.SG.Pf.GluingBases.FamTop) (h1 : Formalism.L2.SG.Pf.GluingBases.FamGram) (h2 : Formalism.L2.SG.Pf.GluingBases.FamDual) :
    GlueExists :=
  glueExists_of (Formalism.L2.SG.Pf.GluingBases.glueLocal_of_fam hJ hV h0 h1 h2 Formalism.L2.SG.Pf.FamilyMeetLattice.family_meet_holds)

end Formalism.L2.SG.Pf.Cnt
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped ENNReal

noncomputable section

namespace Formalism.L2.SG.Pf.LsNc5

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev LtPair (r : ℕ) : Type := {p : Fin r × Fin r // p.1 < p.2}

abbrev CIdx (r k : ℕ) : Type :=
  ((LtPair r × Bool) ⊕ (Fin r × Bool)) ⊕ ((Fin r × Fin k × Bool) ⊕ ((LtPair r × Bool) ⊕ Fin r))

def reim (c : ℂ) (t : Bool) : ℝ := if t then c.im else c.re

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def kapV (v : InfinitePlace X.B.I.F) (s : X.B.I.Ginf) : CIdx D.R.rS D.R.k → ℝ := fun i =>
  match i with
  | Sum.inl (Sum.inl (p, t)) => reim (xMat X v s p.1.1 p.1.2) t
  | Sum.inl (Sum.inr (b, t)) => reim (yVec X u v s b) t
  | Sum.inr (Sum.inl (b, j, t)) => reim (phiMat X u v s b j) t
  | Sum.inr (Sum.inr (Sum.inl (p, t))) =>
      reim ((mMat X v s p.1.1 p.1.2 - star (mMat X v s p.1.2 p.1.1)) / 2) t
  | Sum.inr (Sum.inr (Sum.inr a)) => (mMat X v s a a).im

def kap (s : X.B.I.Ginf) : InfinitePlace X.B.I.F × CIdx D.R.rS D.R.k → ℝ := fun i => kapV X u i.1 s i.2

def twoU : ℝ := (2 : ℝ) ^ (Fintype.card (InfinitePlace X.B.I.F) * (D.R.rS * (D.R.rS + 1) / 2))

def CoordMeas : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word),
    Measurable (kap X u) ∧ MeasurableSet (X.NinfU u) ∧ Set.InjOn (kap X u) (X.NinfU u)

def CoordHaar : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (μ : Measure X.B.I.Ginf),
    IsHaarOnSet X.B.I (X.NinfU u) μ → μ.map (kap X u) = μ (boxN X u) • volume

def CoordCovol : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (FdN : Set X.B.I.Ginf),
    IsSFund X.B.I (Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) FdN →
    MeasurableSet (kap X u '' (FdN ∩ X.NinfU u)) ∧
      volume (kap X u '' (FdN ∩ X.NinfU u)) = ENNReal.ofReal (covolN X u / twoU X)

end Formalism.L2.SG.Pf.LsNc5
end
end

section

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem gramO_apply {m : ℕ} (a : Fin m → 𝓞 F) (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (i j : Fin m) :
    jK (gramO a Y i j) = (∑ l, star (jK (Y l i)) * jK (ι (a l)) * jK (Y l j)) -
      if i = j then jK (ι (a i)) else 0 := by
  rw [gramO, Matrix.sub_apply, Matrix.mul_apply, diagonal_apply]
  simp_rw [mul_diagonal, conjTranspose_apply]
  have map_star (z : 𝓞 K) : jK (star z) = star (jK z) := rfl
  split_ifs <;> simp [map_star, map_sum]

def endoOf (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (g : V →ₗ[𝓞 K] V)
    (hA : ∀ x ∈ locF 𝔭 (dualIn h ⊤ L), g x ∈ locF 𝔭 (dualIn h ⊤ L))
    (hB : ∀ x ∈ locF 𝔭 L, g x ∈ locF 𝔭 L) : Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭) :=
  Submodule.mapQ _ _ (g.restrict hA) (fun _ hx => hB _ hx)

section

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {m : ℕ}
  {b : Fin m → V} {a : Fin m → 𝓞 F}
  (horth : ∀ i j, i ≠ j → h (b i) (b j) = 0)
  (hdiag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)) (ha : ∀ i, a i ≠ 0)
  (hbX : ∀ i, b i ∈ (⊤ : Submodule K V))
  (hloc : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L)
  (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) (hL : IsLatIn ⊤ L)
include horth hdiag ha hbX hloc hF h𝔭 hL

theorem gmap_B (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (x : V) (hx : x ∈ locF 𝔭 L) :
    gmap h b a Y x ∈ locF 𝔭 L := by
  have := h𝔭.isPrime
  rw [mem_B horth hdiag ha hbX hloc h𝔭.isPrime hL] at hx ⊢
  intro k
  rw [crd_gmap horth hdiag ha]
  exact sum_mem fun j _ => mul_mem (HU.jK_mem_SP _) (hx j)

theorem gmap_A (Y : Matrix (Fin m) (Fin m) (𝓞 K))
    (hY : ∀ i j, haveI := h𝔭.isPrime; jK (ι (a i) * Y i j) / jK (ι (a j)) ∈ HU.SP K 𝔭)
    (x : V) (hx : x ∈ locF 𝔭 (dualIn h ⊤ L)) : gmap h b a Y x ∈ locF 𝔭 (dualIn h ⊤ L) := by
  have := h𝔭.isPrime
  rw [mem_A horth hdiag ha hbX hloc hF h𝔭 hL] at hx ⊢
  intro k
  rw [crd_gmap horth hdiag ha, Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  have hd : jK (ι (a j)) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr
    ((map_ne_zero_iff ι (RingOfIntegers.algebraMap.injective F K)).mpr (ha j))
  have e : jK (ι (a k) * Y k j) / jK (ι (a j)) * (jK (ι (a j)) * crd h b a x j) =
      jK (ι (a k)) * (jK (Y k j) * crd h b a x j) := by
    rw [map_mul, div_mul_eq_mul_div, div_eq_iff hd]; ring
  rw [← e]
  exact mul_mem (hY k j) (hx j)

theorem B_le_A (x : V) (hx : x ∈ locF 𝔭 L) : x ∈ locF 𝔭 (dualIn h ⊤ L) := by
  have := h𝔭.isPrime
  rw [mem_B horth hdiag ha hbX hloc h𝔭.isPrime hL] at hx
  rw [mem_A horth hdiag ha hbX hloc hF h𝔭 hL]
  exact fun i => mul_mem (HU.jK_mem_SP _) (hx i)

theorem h_AB (x y : V) (hx : x ∈ locF 𝔭 (dualIn h ⊤ L)) (hy : y ∈ locF 𝔭 L) :
    haveI := h𝔭.isPrime; h x y ∈ HU.SP K 𝔭 ∧ h y x ∈ HU.SP K 𝔭 := by
  have := h𝔭.isPrime
  rw [mem_B horth hdiag ha hbX hloc h𝔭.isPrime hL] at hy
  rw [mem_A horth hdiag ha hbX hloc hF h𝔭 hL] at hx
  rw [h_expand horth hdiag ha hbX hloc h𝔭.isPrime hL x y,
    h_expand horth hdiag ha hbX hloc h𝔭.isPrime hL y x]
  refine ⟨sum_mem fun i _ => ?_, sum_mem fun i _ => ?_⟩
  · have hstar : star (jK (ι (a i))) = jK (ι (a i)) :=
      (hF _).2 ⟨(a i : F), rfl⟩
    have e : star (crd h b a x i) * jK (ι (a i)) * crd h b a y i =
        star (jK (ι (a i)) * crd h b a x i) * crd h b a y i := by
      rw [star_mul', hstar]; ring
    rw [e]
    exact mul_mem (star_mem_SP hF (hx i)) (hy i)
  · rw [mul_assoc]
    exact mul_mem (star_mem_SP hF (hy i)) (hx i)

theorem form_identity (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (x y : V) :
    h (gmap h b a Y x) (gmap h b a Y y) - h x y =
      ∑ i, ∑ j, star (crd h b a x i) * jK (gramO a Y i j) * crd h b a y j := by
  rw [h_expand horth hdiag ha hbX hloc h𝔭.isPrime hL x y,
    h_expand horth hdiag ha hbX hloc h𝔭.isPrime hL (gmap h b a Y x) (gmap h b a Y y)]
  simp only [crd_gmap horth hdiag ha, gramO_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · simp only [star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_comm.trans ?_
    refine (Finset.sum_congr rfl fun y _ => Finset.sum_comm).trans ?_
    refine Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => ?_
    ring
  · simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end

end Formalism.L2.SG.Pf.fibreCountingData
end
end

section

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.discriminantNormShapes

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5


open Classical in
def eQ (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ)
    (a : Fin m → 𝓞 F) : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Matrix.diagonal fun j => if a j ∈ 𝔭 then 1 else 0

def NormOnto : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k → ∀ Y : udPre K 𝔭 k a,
      ∃ Y' P W Z₀ : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k),
        Y' - Y.1 = Z₀ * diagQ K 𝔭 k a ∧ P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y' ∧
        Y'ᴴ * diagQ K 𝔭 k a * Y' - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a ∧
        Wᴴ = W ∧ eQ K 𝔭 k a * W * eQ K 𝔭 k a = W ∧
        eQ K 𝔭 k a * P = eQ K 𝔭 k a * P * eQ K 𝔭 k a ∧
        P * eQ K 𝔭 k a = eQ K 𝔭 k a * P * eQ K 𝔭 k a ∧ IsUnit P.det

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}

theorem eQ_conjTranspose (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    (eQ K 𝔭 k a)ᴴ = eQ K 𝔭 k a := by
  unfold eQ
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  rw [Pi.star_apply]
  split_ifs <;> simp

theorem eQ_mul_diagQ_mul_eQ_mem {𝔭 : Ideal (𝓞 F)} {k : ℕ} (a : Fin m → 𝓞 F) (i j : Fin m) :
    (eQ K 𝔭 k a * diagQ K 𝔭 k a * eQ K 𝔭 k a) i j ∈
      (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
  unfold eQ diagQ
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  split_ifs with hij hi
  · rw [one_mul, mul_one]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 K)) hi)
  · simp
  · exact zero_mem _

theorem solveOnto_of_norm (hN : NormOnto) : SolveOnto := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk Y
  obtain ⟨Y', P, W, Z₀, hY, hPY, hW, hWh, hEW, hEP1, hEP2, hdet⟩ := hN K F hK 𝔭 h𝔭 m a ha k hk Y
  have hEh := eQ_conjTranspose (K := K) 𝔭 k a
  have hH := diagQ_conjTranspose (K := K) 𝔭 k a

  have h2 : P * eQ K 𝔭 k a = eQ K 𝔭 k a * P := hEP2.trans hEP1.symm
  have h1 : Pᴴ * eQ K 𝔭 k a = eQ K 𝔭 k a * Pᴴ := by
    have h := congrArg Matrix.conjTranspose h2
    rw [conjTranspose_mul, conjTranspose_mul, hEh] at h
    exact h.symm
  have hu : IsUnit (Pᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact hdet.star

  obtain ⟨Z', hZ'⟩ := exists_solve_quot hK h𝔭 (k := k) (by omega)
    (H := eQ K 𝔭 k a * diagQ K 𝔭 k a * eQ K 𝔭 k a) (P := P) (Q := (Pᴴ)⁻¹) (S := W)
    (by simp only [conjTranspose_mul, hEh, hH, Matrix.mul_assoc])
    (fun i j => eQ_mul_diagQ_mul_eQ_mem a i j)
    (fun i j => by rw [Matrix.mul_nonsing_inv _ hu, sub_self]; simp)
    hWh
  refine ⟨Y', P, W, eQ K 𝔭 k a * Z' * eQ K 𝔭 k a, Z₀, hY, hPY, hW, ?_⟩
  have h2' : ∀ X : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k), X * P * eQ K 𝔭 k a = X * eQ K 𝔭 k a * P :=
    fun X => by rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc]
  have key : W + Pᴴ * (eQ K 𝔭 k a * Z' * eQ K 𝔭 k a) + (eQ K 𝔭 k a * Z' * eQ K 𝔭 k a)ᴴ * P +
      (eQ K 𝔭 k a * Z' * eQ K 𝔭 k a)ᴴ * diagQ K 𝔭 k a * (eQ K 𝔭 k a * Z' * eQ K 𝔭 k a) =
      eQ K 𝔭 k a * (W + Pᴴ * Z' + Z'ᴴ * P + Z'ᴴ * (eQ K 𝔭 k a * diagQ K 𝔭 k a * eQ K 𝔭 k a) * Z') * eQ K 𝔭 k a := by
    simp only [conjTranspose_mul, hEh, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, h2',
      ← h1, hEW] <;> abel
  rw [key, hZ', Matrix.mul_zero, Matrix.zero_mul]

theorem discOnto_of_norm (hU : UDModel) (hN : NormOnto) : DiscOnto :=
  discOnto_of_solve hU (solveOnto_of_norm hN)

end Formalism.L2.SG.Pf.discriminantNormShapes
end
end
