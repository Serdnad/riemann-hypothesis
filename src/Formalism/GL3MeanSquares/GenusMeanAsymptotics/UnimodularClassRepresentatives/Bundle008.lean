module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle003
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle006
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle007
public import Formalism.HermitianLattices.StatementLat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix

namespace Formalism.HermitianLattices.Ext.L3.HU

variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem exists_unitary_near [CharZero K] (hS : IsLocUnif S ϖ) {H E : Matrix n n K} (hH : Hᴴ = H)
    (hHS : Ent S H) (hES : Ent S E) {e k : ℕ} (hHE : H * E = ϖ ^ e • (1 : Matrix n n K))
    (hk : e + 1 ≤ k) {X Z : Matrix n n K} (hX : Ent S X) (hZ : Ent S Z)
    (hXZ : Xᴴ * H * X = H + ϖ ^ k • Z) :
    ∃ G G' D : Matrix n n K, Ent S G ∧ Ent S G' ∧ Ent S D ∧ G * G' = 1 ∧ Gᴴ * H * G = H ∧
      G = X + ϖ ^ (k - e) • D := by
  obtain ⟨l, hl⟩ := exists_node (K := K) hS n
  obtain ⟨D1, Z1, hD1, hZ1, hX1⟩ := exists_newton hS hH hHS hES hHE hk hX hZ hXZ (k + 2 * l)
  have hpk : ϖ ^ (k - e) ∈ S := pow_mem hS _
  have hX1S : Ent S (X + ϖ ^ (k - e) • D1) := hX.add (hD1.smul hpk)
  have hk1 : e + 1 ≤ k + 2 * l := by omega
  obtain ⟨hd1, hd1S⟩ := det_unit hS hH hHS hES hHE hk1 hX1S hZ1 hX1
  obtain ⟨c, hc, hcc, W', hW', hWW⟩ := hl _ hX1S hd1 hd1S
  have hN : 2 * l + e + 1 ≤ k + 2 * l := by omega
  obtain ⟨G, D2, hD2, hG, hGe⟩ :=
    exists_cayley hS hH hHS hES hHE hN hX1S hZ1 hX1 hc hcc hW' hWW
  have hexp : k + 2 * l - 2 * l - e = k - e := by omega
  rw [hexp] at hGe
  have hGS : Ent S G := by
    rw [hGe]
    exact hX1S.add (hD2.smul hpk)
  have hG0 : Gᴴ * H * G = H + ϖ ^ k • (0 : Matrix n n K) := by
    rw [smul_zero, add_zero]
    exact hG
  obtain ⟨hd, hdS⟩ := det_unit hS hH hHS hES hHE hk hGS Ent.zero hG0
  refine ⟨G, G.det⁻¹ • G.adjugate, D1 + D2, hGS, hGS.adjugate.smul hdS, hD1.add hD2, ?_, hG, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, inv_mul_cancel₀ hd, one_smul]
  · rw [hGe, smul_add, add_assoc]

end Formalism.HermitianLattices.Ext.L3.HU
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem loc_gmap (g : V ≃ₗ[K] V) (p : Ideal (𝓞 K)) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.loc (K := K) p (Formalism.HermitianLatticesTheory.gmap g L) = Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) p L) := by
  have hsm : ∀ (s : 𝓞 K) (v : V), g (s • v) = s • g v := fun s v => by
    rw [← algebraMap_smul K s v, ← algebraMap_smul K s (g v), map_smul]
  unfold Formalism.HermitianLatticesTheory.loc Formalism.HermitianLatticesTheory.gmap Formalism.HermitianLatticesTheory.locS
  ext x
  simp only [Submodule.mem_map, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨s, hs, y, hy, hyx⟩
    refine ⟨g.symm x, ⟨s, hs, ?_⟩, by simp⟩
    have e : s • g.symm x = y := g.injective (by rw [hsm, g.apply_symm_apply]; exact hyx.symm)
    rw [e]; exact hy
  · rintro ⟨z, ⟨s, hs, hz⟩, rfl⟩
    exact ⟨s, hs, s • z, hz, hsm s z⟩

theorem gmap_injective (g : V ≃ₗ[K] V) :
    Function.Injective (Formalism.HermitianLatticesTheory.gmap g : Submodule (𝓞 K) V → Submodule (𝓞 K) V) := by
  intro L M hLM
  unfold Formalism.HermitianLatticesTheory.gmap at hLM
  exact Submodule.map_injective_of_injective (f := (g : V →ₗ[K] V).restrictScalars (𝓞 K))
    (fun a b h => g.injective h) hLM

theorem isUnimodularAt_of_loc_eq {h : V →ₗ⋆[K] V →ₗ[K] K} (p : Ideal (𝓞 K))
    {L M : Submodule (𝓞 K) V} (he : Formalism.HermitianLatticesTheory.loc (K := K) p L = Formalism.HermitianLatticesTheory.loc (K := K) p M) :
    Formalism.HermitianLatticesTheory.IsUnimodularAt h p L ↔ Formalism.HermitianLatticesTheory.IsUnimodularAt h p M := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodularAt
  rw [he]

end Formalism.HermitianLattices.Ext.L3
end
end
