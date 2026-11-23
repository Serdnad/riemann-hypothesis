module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.StarAlgebraMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SplitAtOf
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsFracOfFixed
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle013
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G2

open Formalism.HermitianLattices.Ext.L3

theorem smul_top_pi {R : Type*} [CommRing R] {κ : Type*} [Fintype κ] [DecidableEq κ]
    {N : κ → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] (J : Ideal R) :
    (J • ⊤ : Submodule R (∀ i, N i)) =
      Submodule.pi Set.univ (fun i => J • (⊤ : Submodule R (N i))) := by
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro r hr n _
    rw [Submodule.mem_pi]
    intro i _
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro v hv
    rw [Submodule.mem_pi] at hv
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    have h1 : Pi.single i (v i) ∈ (J • (⊤ : Submodule R (N i))).map (LinearMap.single R N i) :=
      Submodule.mem_map_of_mem (hv i (Set.mem_univ i))
    rw [Submodule.map_smul''] at h1
    exact Submodule.smul_mono le_rfl le_top h1

theorem card_quot_smul_top_congr {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M ≃ₗ[R] N) (J : Ideal R) :
    Nat.card (M ⧸ (J • ⊤ : Submodule R M)) = Nat.card (N ⧸ (J • ⊤ : Submodule R N)) := by
  refine Nat.card_congr (Submodule.Quotient.equiv _ _ f ?_).toEquiv
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

theorem card_quot_quot {A : Type*} [CommRing A] (E J : Ideal A) :
    Nat.card ((A ⧸ E) ⧸ (J • ⊤ : Submodule A (A ⧸ E))) = Nat.card (A ⧸ (E ⊔ J)) := by
  have h1 : (J • ⊤ : Submodule A (A ⧸ E)) = Submodule.map E.mkQ J := by
    conv_lhs => rw [← Submodule.range_mkQ E, LinearMap.range_eq_map, ← Submodule.map_smul'',
      Ideal.smul_eq_mul, Ideal.mul_top]
  rw [h1]
  exact Nat.card_congr (Submodule.quotientQuotientEquivQuotientSup E J).toEquiv

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem two_le_absNorm {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 2 ≤ Ideal.absNorm (extP K 𝔭) := by
  have hc := Formalism.HermitianLattices.Ext.L3.MeanB.comap_extP_pow (K := K) 𝔭 1
  rw [pow_one, pow_one] at hc
  have h1 : extP K 𝔭 ≠ ⊤ := fun h => h𝔭.ne_top (by rw [← hc, h, Ideal.comap_top])
  have h0 : extP K 𝔭 ≠ ⊥ := by
    intro h
    have hne : 𝔭 ≠ ⊥ := fun h' =>
      NumberField.RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.mpr (h' ▸ h𝔭))
    apply hne
    rw [← hc, h]
    ext t
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    constructor
    · intro ht
      have h2 : algebraMap F K (t : F) = 0 := by
        have h3 := congrArg (algebraMap (𝓞 K) K) ht
        rw [map_zero] at h3
        exact h3
      have h4 : (t : F) = 0 := (algebraMap F K).injective (by rw [h2, map_zero])
      exact_mod_cast h4
    · intro ht
      rw [ht, map_zero]
  have ha0 : Ideal.absNorm (extP K 𝔭) ≠ 0 := fun h => h0 (Ideal.absNorm_eq_zero_iff.mp h)
  have ha1 : Ideal.absNorm (extP K 𝔭) ≠ 1 := fun h => h1 (Ideal.absNorm_eq_one_iff.mp h)
  omega

theorem card_pi_quot (𝔭 : Ideal (𝓞 F)) {κ : Type} [Fintype κ] [DecidableEq κ] (e : κ → ℕ) (j : ℕ) :
    Nat.card ((∀ i, 𝓞 K ⧸ extP K 𝔭 ^ e i) ⧸
        (extP K 𝔭 ^ j • ⊤ : Submodule (𝓞 K) (∀ i, 𝓞 K ⧸ extP K 𝔭 ^ e i))) =
      Ideal.absNorm (extP K 𝔭) ^ ∑ i, min (e i) j := by
  rw [smul_top_pi, Nat.card_congr (Submodule.quotientPi
    (fun i => (extP K 𝔭 ^ j • ⊤ : Submodule (𝓞 K) (𝓞 K ⧸ extP K 𝔭 ^ e i)))).toEquiv,
    Nat.card_pi, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hsup : extP K 𝔭 ^ e i ⊔ extP K 𝔭 ^ j = extP K 𝔭 ^ min (e i) j := by
    rcases le_total (e i) j with h | h
    · rw [min_eq_left h, sup_eq_left.mpr (Ideal.pow_le_pow_right h)]
    · rw [min_eq_right h, sup_eq_right.mpr (Ideal.pow_le_pow_right h)]
  rw [card_quot_quot, hsup, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, map_pow]

end Formalism.L2.SG.Pf.G2
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def prO {X Y : Submodule K V} (hc : IsCompl X Y) : V →ₗ[𝓞 K] V :=
  (X.projection Y hc).restrictScalars (𝓞 K)

theorem prO_apply {X Y : Submodule K V} (hc : IsCompl X Y) (x : V) :
    prO hc x = X.projection Y hc x := rfl

theorem prO_add {X Y : Submodule K V} (hc : IsCompl X Y) (x : V) :
    prO hc x + prO hc.symm x = x :=
  Submodule.projection_add_projection_eq_self hc x

def toDisc (h : V →ₗ⋆[K] V →ₗ[K] K) {X Y : Submodule K V} (hc : IsCompl X Y) (L Λ : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (hP : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h X L)) :
    ↥Λ →ₗ[𝓞 K] DiscMod h X L 𝔭 :=
  Submodule.mkQ _ ∘ₗ LinearMap.codRestrict _ (prO hc ∘ₗ Λ.subtype) (fun x => hP x x.2)

theorem toDisc_surj (h : V →ₗ⋆[K] V →ₗ[K] K) {X Y : Submodule K V} (hc : IsCompl X Y)
    (L Λ : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (hP : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h X L))
    (hS : ∀ v ∈ locF 𝔭 (dualIn h X L), ∃ x ∈ Λ, prO hc x = v) :
    Function.Surjective (toDisc h hc L Λ 𝔭 hP) := by
  refine (Submodule.mkQ_surjective _).comp ?_
  rintro ⟨v, hv⟩
  obtain ⟨x, hx, e⟩ := hS v hv
  exact ⟨⟨x, hx⟩, Subtype.ext e⟩

theorem mem_ker_toDisc (h : V →ₗ⋆[K] V →ₗ[K] K) {X Y : Submodule K V} (hc : IsCompl X Y)
    (L Λ : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (hP : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h X L))
    (x : ↥Λ) : x ∈ LinearMap.ker (toDisc h hc L Λ 𝔭 hP) ↔ prO hc (x : V) ∈ locF 𝔭 L := by
  rw [LinearMap.mem_ker]
  change Submodule.Quotient.mk _ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  rfl

theorem prO_mem_iff {X Y : Submodule K V} (hc : IsCompl X Y) {L Λ : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} (hX : Λ ⊓ X.restrictScalars (𝓞 K) = locF 𝔭 L) (x : V) :
    prO hc x ∈ locF 𝔭 L ↔ prO hc x ∈ Λ := by
  rw [← hX, Submodule.mem_inf]
  constructor
  · exact fun H => H.1
  · intro H
    exact ⟨H, Submodule.projection_apply_mem hc x⟩

theorem discIso_of_proj (h : V →ₗ⋆[K] V →ₗ[K] K) {U W : Submodule K V} (hc : IsCompl U W)
    {M T Λ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
    (hU : Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M) (hW : Λ ⊓ W.restrictScalars (𝓞 K) = locF 𝔭 T)
    (hPU : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h U M))
    (hSU : ∀ v ∈ locF 𝔭 (dualIn h U M), ∃ x ∈ Λ, prO hc x = v)
    (hPW : ∀ x ∈ Λ, prO hc.symm x ∈ locF 𝔭 (dualIn h W T))
    (hSW : ∀ v ∈ locF 𝔭 (dualIn h W T), ∃ x ∈ Λ, prO hc.symm x = v) :
    Nonempty (DiscMod h U M 𝔭 ≃ₗ[𝓞 K] DiscMod h W T 𝔭) := by
  have hker : LinearMap.ker (toDisc h hc M Λ 𝔭 hPU) = LinearMap.ker (toDisc h hc.symm T Λ 𝔭 hPW) := by
    ext x
    rw [mem_ker_toDisc, mem_ker_toDisc, prO_mem_iff hc hU, prO_mem_iff hc.symm hW]
    have e := prO_add hc (x : V)
    constructor
    · intro H
      have : prO hc.symm (x : V) = (x : V) - prO hc (x : V) := eq_sub_of_add_eq' e
      rw [this]
      exact Λ.sub_mem x.2 H
    · intro H
      have : prO hc (x : V) = (x : V) - prO hc.symm (x : V) := eq_sub_of_add_eq e
      rw [this]
      exact Λ.sub_mem x.2 H
  exact ⟨((LinearMap.quotKerEquivOfSurjective _ (toDisc_surj h hc M Λ 𝔭 hPU hSU)).symm.trans
    (Submodule.quotEquivOfEq _ _ hker)).trans
    (LinearMap.quotKerEquivOfSurjective _ (toDisc_surj h hc.symm T Λ 𝔭 hPW hSW))⟩

end Formalism.L2.SG.Pf.G6
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G7

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def GlueLocal : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → cJ h U M 𝔭 < finrank K (orthK h U) →
      ∃ T : Submodule (𝓞 K) V, (∃ A : Submodule (𝓞 K) V, Submodule.IsLattice K A ∧ locF 𝔭 A = T) ∧
        dualF h 𝔭 T = T ∧ T ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M

end Formalism.L2.SG.Pf.G7
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def IsomFixOfExp : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    ∀ T T' : Submodule (𝓞 K) V, IsLatIn (orthK h U) T → IsLatIn (orthK h U) T' →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a b' a',
      IsJordanIn h (orthK h U) T 𝔭 b a → IsJordanIn h (orthK h U) T' 𝔭 b' a' →
      (∀ i, vF 𝔭 (a i) = vF 𝔭 (a' i)) →
      ∃ g ∈ isomFix h U, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 T) = locF 𝔭 T'

end Formalism.L2.SG.Pf.G8
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

def NondegOn {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) : Prop :=
  ∀ x ∈ X, (∀ y ∈ X, h x y = 0) → x = 0

def JordanExists : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm →
    (∀ (X : Submodule K V) (L : Submodule (𝓞 K) V), NondegOn h X → IsLatIn X L →
      Formalism.HermitianLatticesTheory.IsIntegralLat h L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∃ b a, IsJordanIn h X L 𝔭 b a) ∧
    (∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      ∀ b a, IsJordanIn h ⊤ L 𝔭 b a → vd h L 𝔭 = vJof 𝔭 a)

def JordanInv : Prop :=
  ∀ (K F V V' : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K),
    h.IsSymm → h'.IsSymm → ∀ (X : Submodule K V) (X' : Submodule K V') (L : Submodule (𝓞 K) V)
    (L' : Submodule (𝓞 K) V'), IsLatIn X L → IsLatIn X' L' → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
    ∀ b a b' a', IsJordanIn h X L 𝔭 b a → IsJordanIn h' X' L' 𝔭 b' a' →
      Nonempty (DiscMod h X L 𝔭 ≃ₗ[𝓞 K] DiscMod h' X' L' 𝔭) →
      ∀ j : ℕ, ∑ i, min (vF 𝔭 (a i)) j = ∑ i, min (vF 𝔭 (a' i)) j

def JordanIsom : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h → ∀ L L' : Submodule (𝓞 K) V, Submodule.IsLattice K L →
    Submodule.IsLattice K L' → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a b' a',
      IsJordanIn h ⊤ L 𝔭 b a → IsJordanIn h ⊤ L' 𝔭 b' a' → (∀ i, vF 𝔭 (a i) = vF 𝔭 (a' i)) →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = locF 𝔭 L'

def AlphaDisc : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h → ∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L →
    Formalism.HermitianLatticesTheory.IsIntegralLat h L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h ⊤ L 𝔭 b a →
      alphaL h L 𝔭 = (discAut h ⊤ L 𝔭 : ℝ) * alphaStd K 𝔭 (finrank K V - cJof 𝔭 a)

def GlueLoc : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h → ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M T : Submodule (𝓞 K) V, IsLatIn U M → IsLatIn (orthK h U) T → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      (fibP h U 𝔭 M T ≠ 0 →
        Nonempty (DiscMod h U M 𝔭 ≃ₗ[𝓞 K] DiscMod h (orthK h U) T 𝔭) ∧
        fibP h U 𝔭 M T = discAut h (orthK h U) T 𝔭) ∧
      ∀ g ∈ isomFix h U, fibP h U 𝔭 M (Formalism.HermitianLatticesTheory.gmap g T) = fibP h U 𝔭 M T

def GlueExists : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h → ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    (∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → cJ h U M 𝔭 < finrank K (orthK h U)) →
      (GlueSet h U M).Nonempty

def GlueProd : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h → ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → ∀ Λ₀ ∈ GlueSet h U M,
    ∀ T : Submodule (𝓞 K) V, IsLatIn (orthK h U) T →
      ((∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → fibP h U 𝔭 M T ≠ 0) ↔
        SameGenusFix (F := F) h U (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K)) T) ∧
      Nat.card {Λ : Submodule (𝓞 K) V // Λ ∈ GlueSet h U M ∧ Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T} =
        ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, fibP h U 𝔭.1 M T

def GlueMass : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h → ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M → (GlueSet h U M).Nonempty →
    ∀ c : ℝ, MassConst K F (finrank K (orthK h U)) c →
      ∃ s : Finset (Submodule (𝓞 K) V), (∀ Λ ∈ s, Λ ∈ GlueSet h U M) ∧
        (∀ Λ ∈ GlueSet h U M, ∃! Λ₁, Λ₁ ∈ s ∧ ∃ g ∈ isomFix h U, Formalism.HermitianLatticesTheory.gmap g Λ₁ = Λ) ∧
        (∀ Λ ∈ s, (stabFix h U Λ).Finite) ∧
        ∑ Λ ∈ s, ((Nat.card (stabFix h U Λ) : ℕ) : ℝ)⁻¹ =
          c * nM F h U M ^ finrank K (orthK h U) *
            ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, alphaStd K 𝔭.1 (finrank K (orthK h U)) /
              alphaStd K 𝔭.1 (finrank K (orthK h U) - cJ h U M 𝔭.1)

end Formalism.L2.SG.Pf.Cnt
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.ProjectionDiscriminantModule

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem locF_dualF {h : V →ₗ⋆[K] V →ₗ[K] K} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (L : Submodule (𝓞 K) V) : locF 𝔭 (dualF h 𝔭 L) = dualF h 𝔭 L := by
  have hp := h𝔭.isPrime
  refine le_antisymm ?_ (LocF.le_locF 𝔭 _)
  intro x hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp _ x).1 hx
  show ∀ y ∈ L, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
  intro y hy
  have e : h y (algebraMap (𝓞 F) (𝓞 K) t • x) = algebraMap (𝓞 F) (𝓞 K) t • h y x := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x, LinearMap.map_smul, algebraMap_smul]
  have h1 := (show ∀ y ∈ L, h y (algebraMap (𝓞 F) (𝓞 K) t • x) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
    from htx) y hy
  rw [e] at h1
  obtain ⟨s, hs, hs_mem⟩ := (LocF.mem_locF_iff hp (1 : Submodule (𝓞 K) K) _).1 h1
  have hst : s * t ∉ 𝔭 := fun hm => (hp.mem_or_mem hm).elim hs ht
  refine (LocF.mem_locF_iff hp _ _).2 ⟨s * t, hst, ?_⟩
  simpa only [map_mul, mul_smul] using hs_mem

end Formalism.L2.SG.Pf.ProjectionDiscriminantModule
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

theorem local_span_holds : LocSpan := by
  intro K F V _ _ _ _ _ _ _ _ _ _ hK hF P hP n b v
  have hPp := hP.isPrime
  constructor
  · intro hv
    obtain ⟨s, hs, hsv⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hv
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hsv
    have hs0 := algebraMap_ne_zero_of_mem_hcompl hPp hs
    refine ⟨fun i => algebraMap (𝓞 K) K (c i) / algebraMap (𝓞 K) K s,
      fun i => div_mem_locRing hPp (c i) hs, ?_⟩
    have e : v = (algebraMap (𝓞 K) K s)⁻¹ • (algebraMap (𝓞 K) K s • v) := by
      rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [e, algebraMap_smul, ← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (c i) (b i), smul_smul]
    simp only [div_eq_inv_mul]
  · rintro ⟨d, hd, rfl⟩
    refine Submodule.sum_mem _ fun i _ => smul_mem_loc hPp (hd i) ?_
    exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem jordan_span_holds :
    ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
      [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
      (L : Submodule (𝓞 K) V), Submodule.IsFullLattice K L → ∀ 𝔭 : Ideal (𝓞 F),
      𝔭.IsMaximal → ∀ (n : ℕ) (b : Fin n → V),
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L →
        Submodule.span K (Set.range b) = ⊤ := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ L hL 𝔭 h𝔭 n b hb
  letI : Submodule.IsFullLattice K L := hL
  rw [eq_top_iff, ← Submodule.IsFullLattice.span_eq_top (A := K) (M := L), Submodule.span_le]
  intro x hx
  have hx' : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by
    rw [hb]
    exact LocF.le_locF 𝔭 L hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ x).mp hx'
  have ht0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
    intro h0
    apply ht
    have h1 : algebraMap (𝓞 F) (𝓞 K) t = 0 :=
      FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero])
    have h2 : t = 0 := FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K) (by rw [h1, map_zero])
    rw [h2]
    exact 𝔭.zero_mem
  have hmem := Submodule.span_le_restrictScalars (𝓞 K) K (Set.range b) htx
  have e : x = (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ •
      (algebraMap (𝓞 F) (𝓞 K) t • x) := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ hmem

end Formalism.L2.SG.Pf.G3
end
end
