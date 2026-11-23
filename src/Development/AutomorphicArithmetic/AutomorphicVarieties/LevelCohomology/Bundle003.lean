module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AdjointDiagonalRepPreservesWeightPiece
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem cont_lev {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Γ : Type} [TopologicalSpace Γ]
    (a : O) (ha : a ≠ 0) (z : Γ → O) (hz : Alg.AdicCont (maximalIdeal O) z) :
    Continuous fun g => Lev.mk a (z g) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hle : ∀ x, x ∈ maximalIdeal O ^ n → a ∣ x := by
    intro x hx
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hx
    rw [hu, Units.mul_left_dvd]
    exact hx
  have hlc := (IsLocallyConstant.iff_eventually_eq _).1 (hz n)
  refine ((IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_).continuous
  filter_upwards [hlc x] with y hy
  rw [Ideal.Quotient.eq] at hy
  rw [← sub_eq_zero, ← map_sub, Lev.mk_eq_zero]
  exact hle _ hy

private theorem lev_kill {O : Type} [CommRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ] (θ : Γ →* Oˣ) (a : O) (B : ℕ)
    (hf : Finite (H1 (scalRep (Lev a) θ))) (hB : Nat.card (H1 (scalRep (Lev a) θ)) ≤ B) (z : Γ → O) (hz : Coc θ z)
    (hc : Continuous fun g => Lev.mk a (z g)) :
    ∃ m : O, ∀ g, a ∣ (B.factorial : O) * z g - ((θ g : O) * m - m) := by
  set ρ := scalRep (Lev a) θ with hρ
  have hρg : ∀ g (x : Lev a), ρ g x = (θ g : O) • x := fun _ _ => rfl
  have hmem : (fun g => Lev.mk a (z g)) ∈ Z1 ρ := by
    rw [mem_Z1_iff_cocycle]
    refine ⟨hc, fun g h => ?_⟩
    rw [hz, hρg, map_add (f := _), ← smul_eq_mul, map_smul]
  let ζ : Z1 ρ := ⟨_, hmem⟩
  let q : H1 ρ := Submodule.Quotient.mk ζ
  have hpos : 0 < Nat.card (H1 ρ) := Nat.card_pos
  have hq : B.factorial • q = 0 := by
    obtain ⟨k, hk⟩ := Nat.dvd_factorial hpos hB
    rw [hk, mul_comm, mul_nsmul, card_nsmul_eq_zero']
  have hq2 : (Submodule.Quotient.mk (B.factorial • ζ) : H1 ρ) = 0 := by
    rw [Submodule.Quotient.mk_smul]
    exact hq
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hq2
  obtain ⟨mb, hmb⟩ := (mem_coboundaries1 ρ _).1 hq2
  obtain ⟨m, rfl⟩ := Lev.mk_surjective a mb
  refine ⟨m, fun g => ?_⟩
  rw [← Lev.mk_eq_zero]
  have := hmb g
  simp only [Submodule.subtype_apply, Submodule.coe_smul_of_tower, Pi.smul_apply] at this
  rw [map_sub, map_sub, ← nsmul_eq_mul, map_nsmul, this, hρg, ← smul_eq_mul, map_smul, sub_self]

theorem UpperTheory.V.X.So.cobLim :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (θ : Γ →* Oˣ) (p : O) (B : ℕ), p ≠ 0 → p ∈ maximalIdeal O → (∃ g, θ g ≠ 1) → (∀ r : ℕ, Finite (H1 (scalRep (Lev (p ^ r)) θ)) ∧ Nat.card (H1 (scalRep (Lev (p ^ r)) θ)) ≤ B) → ∀ z : Γ → O, Coc θ z → Alg.AdicCont (maximalIdeal O) z → CobOn θ z ⊤ := by
  intro O _ _ _ _ Γ _ _ θ p B hp0 hpm hθ hfin z hz hcont
  obtain ⟨g0, hg0⟩ := hθ
  have hcl : ∀ r : ℕ, ∃ m : O, ∀ g, p ^ r ∣ (B.factorial : O) * z g - ((θ g : O) * m - m) := fun r =>
    lev_kill θ (p ^ r) B (hfin r).1 (hfin r).2 z hz (cont_lev (p ^ r) (pow_ne_zero r hp0) z hcont)
  have hpu : ¬IsUnit p := (IsLocalRing.mem_maximalIdeal p).1 hpm
  have hkey : ∀ g, ((θ g0 : O) - 1) * ((B.factorial : O) * z g) = ((θ g : O) - 1) * ((B.factorial : O) * z g0) := by
    intro g
    by_contra hne
    obtain ⟨n, hn⟩ := FiniteMultiplicity.of_not_isUnit hpu (sub_ne_zero.2 hne)
    apply hn
    obtain ⟨m, hm⟩ := hcl (n + 1)
    have e : ((θ g0 : O) - 1) * ((B.factorial : O) * z g) - ((θ g : O) - 1) * ((B.factorial : O) * z g0)
        = ((θ g0 : O) - 1) * ((B.factorial : O) * z g - ((θ g : O) * m - m))
          - ((θ g : O) - 1) * ((B.factorial : O) * z g0 - ((θ g0 : O) * m - m)) := by ring
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_right (hm g) _) (dvd_mul_of_dvd_right (hm g0) _)
  refine ⟨((θ g0 : O) - 1) * (B.factorial : O), ?_, (B.factorial : O) * z g0, ?_⟩
  · refine mul_ne_zero (sub_ne_zero.2 fun h => hg0 (Units.val_eq_one.1 h)) ?_
    exact Nat.cast_ne_zero.2 (Nat.factorial_ne_zero B)
  · intro g _
    rw [mul_assoc, hkey g]
    ring
end

section

noncomputable section

open IsLocalRing UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.X

variable {O : Type} [CommRing O] [IsLocalRing O] {G Γ : Type} [Group G] [Group Γ] {ι : Type} (F : Frame O G Γ ι)

def etaO : Γ →* Oˣ := (Units.map (Int.castRingHom O).toMonoidHom).comp F.η

def lineChar (j : ℤ) (s : ℕ) : Γ →* Oˣ := F.Ψ ^ j * etaO F ^ s

def LineVan [TopologicalSpace Γ] (j : ℤ) (θ : Γ →* Oˣ) : Prop :=
  ∀ z : Γ → O, Coc θ z → Alg.AdicCont (maximalIdeal O) z →
    (∀ v ∉ F.Tb, ∀ s ∈ F.Nv v, z (F.loc v s) = 0) →
    (j = 0 → ∀ v ∈ F.Tb, ∀ s ∈ F.Iv v, z (F.loc v s) = 0) →
    (j < 0 → ∃ y : O, ∀ g : F.D F.vl, F.ηv F.vl g = 1 → z (F.loc _ g) = (θ (F.loc _ g) : O) * y - y) →
    CobOn θ z ⊤

end UpperTheory.V.X

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X
open scoped Pointwise

theorem UpperTheory.V.X.So.cobPlace :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (O : Type) [CommRing O] (θ : G k Ω →* Oˣ) (z : G k Ω → O), Coc θ z → ∀ (v : HeightOneSpectrum (𝓞 k)) (A A' : ValuationSubring Ω), IsPlaceOver A v → IsPlaceOver A' v → CobOn θ z (Dec (F := k) A) → CobOn θ z (Dec (F := k) A') := by
  intro k Ω _ _ _ _ _ O _ θ z hz v A A' hA hA' hcob
  obtain ⟨a, ha, m, hm⟩ := hcob
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_over hA hA'
  refine ⟨a, ha, (θ g : O) * m - a * z g, ?_⟩
  intro h hh
  obtain ⟨h0, hh0, rfl⟩ : ∃ h0 ∈ Dec (F := k) A, h = g * h0 * g⁻¹ := by
    refine ⟨g⁻¹ * h * g, ?_, by group⟩
    rw [mem_Dec] at hh ⊢
    rw [mul_smul, mul_smul, hh, inv_smul_smul]
  have e := hm h0 hh0
  have hz1 : z 1 = 0 := by
    have h11 := hz 1 1
    rw [one_mul, map_one, Units.val_one, one_mul] at h11
    linear_combination -h11
  have hinv : (θ g : O) * z g⁻¹ = - z g := by
    have h2 := hz g g⁻¹
    rw [mul_inv_cancel, hz1] at h2
    linear_combination -h2
  have hθ : θ (g * h0 * g⁻¹) = θ h0 := by
    rw [map_mul, map_mul, map_inv, mul_comm (θ g), mul_inv_cancel_right]
  rw [hθ, hz (g * h0) g⁻¹, hz g h0, map_mul, Units.val_mul]
  linear_combination (θ g : O) * e + a * (θ h0 : O) * hinv
end
