module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle013
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle011
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem bin_step_gen (h : V →ₗ⋆[K] V →ₗ[K] K) (hz : ∀ x y, h x y = 0 → h y x = 0) (e₁ e₂ : V)
    (a b x y n : K) (h12 : h e₁ e₂ = 0) (h11 : h e₁ e₁ = a) (h22 : h e₂ e₂ = b) (ha : star a = a)
    (hb : star b = b) (hxy : a * (x * star x) + b * (y * star y) = n) :
    h (x • e₁ + y • e₂) (x • e₁ + y • e₂) = n ∧
      h (x • e₁ + y • e₂) ((star y * b) • e₁ - (star x * a) • e₂) = 0 ∧
      h ((star y * b) • e₁ - (star x * a) • e₂) ((star y * b) • e₁ - (star x * a) • e₂) =
        a * b * n := by
  have h21 : h e₂ e₁ = 0 := hz _ _ h12
  refine ⟨?_, ?_, ?_⟩
  · simp only [map_add (f := _), map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, h12, h21, h11, h22]
    linear_combination hxy
  · simp only [map_add (f := _), map_sub, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, h12, h21, h11, h22]
    ring
  · simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, h12, h21, h11, h22, star_mul', star_star, ha, hb]
    linear_combination (a * b) * hxy

theorem TotPos.ne_zero' {x : K} (hx : TotPos x) : x ≠ 0 := by
  intro h0
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have := hx φ
  rw [h0, map_zero] at this
  simp at this

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem exists_presc_family (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) [FiniteDimensional K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hsym : ∀ x y, star (h x y) = h y x)
    (hpos : ∀ x, x ≠ 0 → TotPos (h x x)) :
    ∀ k : ℕ, k + 1 ≤ finrank K V → ∀ t : Fin (k + 1) → K, (∀ i, star (t i) = t i) →
      (∀ i, TotPos (t i)) →
      ∃ v : Fin (k + 1) → V, (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧
        (∀ i, i ≠ Fin.last k → h (v i) (v i) = t i) ∧ v (Fin.last k) ≠ 0 := by
  have hz : ∀ x y, h x y = 0 → h y x = 0 := fun x y e => by rw [← hsym, e, star_zero]
  intro k
  induction k with
  | zero =>
    intro hk t _ _
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hsub : ∀ i j : Fin (0 + 1), i = j := fun i j => Fin.ext (by omega)
    exact ⟨fun _ => x, fun i j hij => absurd (hsub i j) hij,
      fun i hi => absurd (hsub i _) hi, hx⟩
  | succ k ih =>
    intro hk t hts htp
    obtain ⟨v, ho, h1, hl⟩ := ih (by omega) (fun i => t (Fin.castSucc i)) (fun i => hts _)
      (fun i => htp _)
    obtain ⟨z, hz0, hzv⟩ := GramDeterminantPositive.exists_ortho_ne_zero h v (by omega)
    obtain ⟨x, y, hxy⟩ := hermRepUnram K hK (h (v (Fin.last k)) (v (Fin.last k))) (h z z)
      (t (Fin.castSucc (Fin.last k))) (hsym _ _) (hsym _ _) (hts _) (hpos _ hl) (hpos _ hz0) (htp _)
    obtain ⟨b1, b2, b3⟩ := bin_step_gen h hz (v (Fin.last k)) z _ _ x y _ (hzv _) rfl rfl
      (hsym _ _) (hsym _ _) hxy
    set a := h (v (Fin.last k)) (v (Fin.last k)) with ha
    set b := h z z with hb
    set f₁ := x • v (Fin.last k) + y • z with hf₁
    set f₂ := (star y * b) • v (Fin.last k) - (star x * a) • z with hf₂
    have hf₂0 : f₂ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at b3
      exact mul_ne_zero (mul_ne_zero (TotPos.ne_zero' (hpos _ hl)) (TotPos.ne_zero' (hpos _ hz0)))
        (TotPos.ne_zero' (htp _)) b3.symm
    have c1 : ∀ i, i ≠ Fin.last k → h (v i) f₁ = 0 := by
      intro i hi
      rw [hf₁, map_add (f := _), map_smul, map_smul, ho i _ hi, hzv i, smul_zero, smul_zero, add_zero]
    have c2 : ∀ i, i ≠ Fin.last k → h (v i) f₂ = 0 := by
      intro i hi
      rw [hf₂, map_sub, map_smul, map_smul, ho i _ hi, hzv i, smul_zero, smul_zero, sub_zero]
    let u : Fin (k + 1) → V := Function.update v (Fin.last k) f₁
    have ul : u (Fin.last k) = f₁ := Function.update_self _ _ _
    have un : ∀ i, i ≠ Fin.last k → u i = v i := fun i hi => Function.update_of_ne hi _ _
    have uo : ∀ i j, i ≠ j → h (u i) (u j) = 0 := by
      intro i j hij
      by_cases hi : i = Fin.last k
      · have hj : j ≠ Fin.last k := fun e => hij (hi.trans e.symm)
        rw [hi, ul, un j hj]
        exact hz _ _ (c1 j hj)
      · by_cases hj : j = Fin.last k
        · rw [hj, ul, un i hi]; exact c1 i hi
        · rw [un i hi, un j hj]; exact ho i j hij
    have u1 : ∀ i, h (u i) (u i) = t (Fin.castSucc i) := by
      intro i
      by_cases hi : i = Fin.last k
      · rw [hi, ul]; exact b1
      · rw [un i hi]; exact h1 i hi
    have u2 : ∀ i, h (u i) f₂ = 0 := by
      intro i
      by_cases hi : i = Fin.last k
      · rw [hi, ul]; exact b2
      · rw [un i hi]; exact c2 i hi
    refine ⟨Fin.snoc u f₂, ?_, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · intro hij; exact absurd rfl hij
      · intro _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        exact hz _ _ (u2 j)
      · intro _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        exact u2 i
      · intro hij
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact uo i j (fun e => hij (by rw [e]))
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro hi; exact absurd rfl hi
      · intro _
        rw [Fin.snoc_castSucc]; exact u1 i
    · rw [Fin.snoc_last]; exact hf₂0

end Formalism.L2.SG.Pf.GluingBases
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

section Defs

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def Nondeg (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ x : V, (∀ y : V, h x y = 0) → x = 0

def orthK (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) : Submodule K V :=
  ⨅ u ∈ U, LinearMap.ker (h u)

def PosDefOn (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) : Prop :=
  ∀ x ∈ X, x ≠ 0 → ∀ φ : K →+* ℂ, 0 < (φ (h x x)).re

def IsLatIn (X : Submodule K V) (L : Submodule (𝓞 K) V) : Prop :=
  L.FG ∧ Submodule.span K (L : Set V) = X

def dualIn (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (L : Submodule (𝓞 K) V) :
    Submodule (𝓞 K) V :=
  X.restrictScalars (𝓞 K) ⊓ Formalism.HermitianLatticesTheory.dual h L

def dualF (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) V) :
    Submodule (𝓞 K) V where
  carrier := {x | ∀ y ∈ L, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)}
  zero_mem' := fun y _ => by simp
  add_mem' := by
    intro x x' hx hx' y hy
    rw [map_add (f := _)]
    exact Submodule.add_mem _ (hx y hy) (hx' y hy)
  smul_mem' := by
    intro c x hx y hy
    rw [show h y (c • x) = c • h y x by
      rw [← algebraMap_smul K c x, LinearMap.map_smul, algebraMap_smul]]
    exact Submodule.smul_mem _ c (hx y hy)

def IsJordanIn (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (b : Fin (finrank K X) → V) (a : Fin (finrank K X) → 𝓞 F) : Prop :=
  (∀ i, b i ∈ X) ∧
  locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L ∧
  (∀ i j, i ≠ j → h (b i) (b j) = 0) ∧
  (∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)) ∧
  ∀ i, a i ≠ 0

def cJof {n : ℕ} (𝔭 : Ideal (𝓞 F)) (a : Fin n → 𝓞 F) : ℕ :=
  (Finset.univ.filter fun i => vF 𝔭 (a i) ≠ 0).card

def vJof {n : ℕ} (𝔭 : Ideal (𝓞 F)) (a : Fin n → 𝓞 F) : ℕ :=
  ∑ i, vF 𝔭 (a i)

def cJ (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) : ℕ :=
  sInf {c | ∃ b a, IsJordanIn h X L 𝔭 b a ∧ c = cJof 𝔭 a}

def vJ (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) : ℕ :=
  sInf {v | ∃ b a, IsJordanIn h X L 𝔭 b a ∧ v = vJof 𝔭 a}

abbrev DiscMod (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) : Type :=
  ↥(locF 𝔭 (dualIn h X L)) ⧸ (locF 𝔭 L).comap (locF 𝔭 (dualIn h X L)).subtype

def discAut (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) : ℕ :=
  Nat.card {P : Module.End (𝓞 K) (DiscMod h X L 𝔭) //
    ∀ x y x' y' : ↥(locF 𝔭 (dualIn h X L)),
      Submodule.Quotient.mk x' = P (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = P (Submodule.Quotient.mk y) →
      h (x' : V) (y' : V) - h (x : V) (y : V) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)}

def isomFix (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | g ∈ Formalism.HermitianLatticesTheory.isom h ∧ ∀ u ∈ U, g u = u}
  one_mem' := ⟨(Formalism.HermitianLatticesTheory.isom h).one_mem, fun _ _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(Formalism.HermitianLatticesTheory.isom h).mul_mem ha hb, fun u hu => ?_⟩
    change a (b u) = u
    rw [hb' u hu, ha' u hu]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(Formalism.HermitianLatticesTheory.isom h).inv_mem ha, fun u hu => ?_⟩
    change a.symm u = u
    conv_lhs => rw [← ha' u hu]
    simp

def stabFix (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (Λ : Submodule (𝓞 K) V) :
    Set (V ≃ₗ[K] V) :=
  {g | g ∈ isomFix h U ∧ Formalism.HermitianLatticesTheory.gmap g Λ = Λ}

def GlueSet (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (M : Submodule (𝓞 K) V) :
    Set (Submodule (𝓞 K) V) :=
  {Λ | Submodule.IsLattice K Λ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ ∧ Λ ⊓ U.restrictScalars (𝓞 K) = M}

def fibP (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F))
    (M T : Submodule (𝓞 K) V) : ℕ :=
  Nat.card {Λ : Submodule (𝓞 K) V //
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) ∧
    dualF h 𝔭 Λ = Λ ∧
    Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M ∧
    Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T}

def SameGenusFix (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (T T' : Submodule (𝓞 K) V) : Prop :=
  ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∃ g ∈ isomFix h U, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 T) = locF 𝔭 T'

def nM (F : Type) [Field F] [NumberField F] [Algebra F K] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (U : Submodule K V) (M : Submodule (𝓞 K) V) : ℝ :=
  ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ vJ h U M 𝔭.1

end Defs

end Formalism.L2.SG.Pf.Cnt
end
end
