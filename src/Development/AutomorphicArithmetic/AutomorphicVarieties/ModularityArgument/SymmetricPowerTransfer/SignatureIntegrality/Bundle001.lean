module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.LevelTwoFiniteIndex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.UnitaryDoubleCosetIndicator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle017

@[expose] public section

section

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Z.Sym.Sig

open Classical Loc Glob

section Alg

variable {K : Type} [Field K] {Δ s : K}

def proj (hs : s * s = Δ) : Lsq K Δ →+* K where
  toFun x := x.re + s * x.im
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' x y := by simp [← hs]; ring
  map_zero' := by simp
  map_add' x y := by simp; ring

def eU (hs : s * s = Δ) : U3 Δ →* GL (Fin 3) K := (GeneralLinearGroup.map (proj hs)).comp Unitary.toUnits

def eD (hs : s * s = Δ) : DX Δ →* GL (Fin 2) K := (GeneralLinearGroup.map (proj hs)).comp (DX Δ).subtype

def ev {τ a : K} (h : a * a = τ * a - 1) : Etau K τ →+* K where
  toFun x := x.re + a * x.im
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' x y := by simp; linear_combination (-(x.im * y.im)) * h
  map_zero' := by simp
  map_add' x y := by simp; ring

def evU {τ a : K} (h : a * a = τ * a - 1) : (Etau K τ)ˣ →* Kˣ := Units.map (ev h : Etau K τ →* K)

theorem root_left (a : Kˣ) : (a : K) * a = ((a : K) + (a⁻¹ : Kˣ)) * a - 1 := by simp [add_mul]

theorem root_right (a : Kˣ) : ((a⁻¹ : Kˣ) : K) * (a⁻¹ : Kˣ) = ((a : K) + (a⁻¹ : Kˣ)) * (a⁻¹ : Kˣ) - 1 := by simp [add_mul]

end Alg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


variable (k) in
structure IsInts (O : Type) [CommRing O] [Algebra O k] : Prop where
  inj : Function.Injective (algebraMap O k)
  range : ∀ x : k, x ∈ (algebraMap O k).range ↔ valuation k x ≤ 1

namespace Lev

variable (V : Lev k)

def unitaryHeckeTestSum (Ry : Finset kˣ) (t : kˣ) (g : GL (Fin 3) k) : ℂ := ∑ y ∈ Ry, V.unitaryDoubleCosetIndicator ![t * (unif k)⁻¹, y, (unif k)⁻¹] g

def quaternionDoubleCosetIndicator (t : kˣ) (g : GL (Fin 2) k) : ℂ := one (g ∈ V.DC ![t, t⁻¹])

def twistedCentralTestFunction (χ : kˣ →* ℂˣ) (t : kˣ) (g : GL (Fin 2) k) : ℂ := (((χ t)⁻¹ : ℂˣ) : ℂ) * V.fZ χ ![t, 1] g

def data {Δ s : k} (hs : s * s = Δ) (Ry : Finset kˣ) (χ : kˣ →* ℂˣ) : SigData Δ where
  P := {t | valuation k (t : k) < valuation k (unif k : k) ^ 2}
  H := V.H
  J := (V.J 3).comap (eU hs)
  J2 := (V.J 2).comap (eD hs)
  fG t g := V.unitaryHeckeTestSum Ry t (eU hs g)
  fS t g := V.quaternionDoubleCosetIndicator t (eD hs g)
  fK t g := V.twistedCentralTestFunction χ t (eD hs g)
  cG := (V.H.relIndex (Uo k) : ℝ) * (V.H.relIndex V.H2 : ℝ)
  cS := V.H.relIndex (Uo k)
  cK := V.H.relIndex (Uo k)

end Lev

end UpperTheory.V.Z.Sym.Sig

end
end

section

noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Z.Sym.Sig

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem val_ord (x : kˣ) : valuation k (x : k) = uniformizer k ^ ord k x := by
  have h := GlAx.val_div_ord x
  rw [Units.val_div_eq_div_val, map_div₀, GlAx.val_zpow] at h
  exact (div_eq_one_iff_eq (zpow_pos GlAx.unif_pos _).ne').1 h

theorem mem_Uc {c : ℕ} {u : kˣ} : u ∈ Uc k c ↔ valuation k (u : k) = 1 ∧ valuation k ((u : k) - 1) ≤ uniformizer k ^ (c : ℤ) := by
  constructor
  · intro h
    refine ⟨Uc_le_Uo k c h, ?_⟩
    obtain ⟨v, hv, rfl⟩ := h
    have h1 : Ideal.Quotient.mk _ (v : 𝒪[k]) = 1 := congrArg Units.val hv
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq, GlAx.mem_pow] at h1
    exact h1
  · rintro ⟨h1, h2⟩
    obtain ⟨v, hv⟩ := (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers (valuation k))
      (x := (⟨u, h1.le⟩ : 𝒪[k]))).2 h1
    refine ⟨v, Units.ext ?_, Units.ext (congrArg Subtype.val hv)⟩
    change Ideal.Quotient.mk _ (v : 𝒪[k]) = Ideal.Quotient.mk _ 1
    rw [Ideal.Quotient.eq, GlAx.mem_pow, hv]
    exact h2

theorem mem_Kc_of {c : ℕ} {g : GL (Fin n) k} (h : g ∈ KO k (Fin n)) (h' : GlAx.Bd c g) : g ∈ Kc k n c := by
  obtain ⟨y, rfl⟩ := h
  exact ⟨y, (GlAx.map_eq_one c y).2 h', rfl⟩

theorem Kc_conj {c : ℕ} {g x : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) (hx : x ∈ Kc k n c) : g * x * g⁻¹ ∈ Kc k n c := by
  obtain ⟨y, rfl⟩ := hg
  obtain ⟨z, hz, rfl⟩ := hx
  exact ⟨y * z * y⁻¹, (MonoidHom.normal_ker _).conj_mem z hz y, by simp⟩

theorem dg_mem_KO {s : Fin n → kˣ} (h : ∀ i, s i ∈ Uo k) : dg s ∈ KO k (Fin n) := by
  have H : ∀ s : Fin n → kˣ, (∀ i, s i ∈ Uo k) → GlAx.Bd 0 (dg s) := fun s h => GlAx.bd_zero.2 fun i j => by
    rw [dg, val_diagT, diagonal_apply]
    split_ifs
    exacts [(show valuation k (s i : k) = 1 from h i).le, zero_mem _]
  exact GlAx.mem_KO.2 ⟨H s h, by rw [dg, ← map_inv]; exact H _ fun i => inv_mem (h i)⟩

theorem dg_mem_Kc {c : ℕ} {s : Fin n → kˣ} : dg s ∈ Kc k n c ↔ ∀ i, s i ∈ Uc k c := by
  constructor
  · intro h i
    have a := (GlAx.mem_Kc.1 h).1 i i
    have b := GlAx.bd_zero.1 (GlAx.mem_KO.1 (GlAx.Kc_le c h)).1 i i
    have b' := GlAx.bd_zero.1 (GlAx.mem_KO.1 (GlAx.Kc_le c h)).2 i i
    rw [dg, ← map_inv] at b'
    simp only [dg, Matrix.sub_apply, val_diagT, diagonal_apply_eq, one_apply_eq] at a b b'
    refine mem_Uc.2 ⟨le_antisymm b ?_, a⟩
    have b2 : valuation k ((s i : k)⁻¹) ≤ 1 := by rw [← Units.val_inv_eq_inv_val]; exact b'
    rw [map_inv₀] at b2
    exact (inv_le_one₀ (zero_lt_iff.2 (by simp))).1 b2
  · intro h
    refine mem_Kc_of (dg_mem_KO fun i => Uc_le_Uo k c (h i)) fun i j => ?_
    rw [dg, Matrix.sub_apply, val_diagT, diagonal_apply, Matrix.one_apply]
    split_ifs
    exacts [(mem_Uc.1 (h i)).2, by simp]

namespace Lev

variable (V : Lev k)

theorem levelTorus_le_torus : V.TH n ≤ (glIwa k n).T := by
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨s, fun i => V.H_le (hs i trivial), rfl⟩

theorem Tc_le_TH : (glIwa k n).Tc V.c ≤ V.TH n := by
  rintro _ ⟨⟨s, -, rfl⟩, h⟩
  exact ⟨s, fun i _ => V.le (dg_mem_Kc.1 h i), rfl⟩

theorem N_le : (glIwa k n).N ≤ V.J n := le_sup_left.trans le_sup_left

theorem TH_le : V.TH n ≤ V.J n := le_sup_right.trans le_sup_left

theorem Nm_le : (glIwa k n).Nm V.c ≤ V.J n := le_sup_right

theorem dg_mem {s : Fin n → kˣ} (h : ∀ i, s i ∈ V.H) : dg s ∈ V.J n := V.TH_le ⟨s, fun i _ => h i, rfl⟩

theorem J_le_KO : V.J n ≤ KO k (Fin n) := by
  refine sup_le (sup_le (fun _ h => h.2) ?_) fun _ h => GlAx.Kc_le _ h.2
  rintro _ ⟨s, hs, rfl⟩
  exact dg_mem_KO fun i => V.H_le (hs i trivial)

end Lev

end UpperTheory.V.Z.Sym.Sig

end
end
