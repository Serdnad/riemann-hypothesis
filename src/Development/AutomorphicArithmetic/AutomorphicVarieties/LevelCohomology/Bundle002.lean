module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.Hypotheses.GalCoh
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
import Formalism.GaloisCohomology.StatementLoc

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.V.X

section Frame

variable {k Γ M : Type} [CommRing k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M] [TopologicalSpace M]
  [DiscreteTopology M] (F : Alg.Frame Γ) (ρ : Representation k Γ M)

def selF : Submodule k (H1 ρ) :=
  (⨅ v, LinearMap.ker (resH1 ρ (F.φ v) (F.hφ v))) ⊓
    ⨅ q, (H1ur (ρ.comp (F.ψ q)) (F.N q)).comap (resH1 ρ (F.ψ q) (F.hψ q))

def shaF : Submodule k (H2 ρ) :=
  (⨅ v, LinearMap.ker (resH2 ρ (F.φ v) (F.hφ v))) ⊓ ⨅ q, LinearMap.ker (resH2 ρ (F.ψ q) (F.hψ q))

end Frame

structure HcPublished : Prop where
  lf : LocalFiniteness
  lt : LocalTateDuality
  le : LocalEulerChar
  gf : GlobalFiniteness
  ge : GlobalEulerChar
  pt : GlobalTheory.Published.PoitouTateNormalised

section Gal

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

def cycK (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] : G ℚ Ω →* kˣ :=
  (Units.map (ZMod.castHom (dvd_pow_self l one_ne_zero) k).toMonoidHom).comp (cycMod ℚ Ω l 1)

variable {Ω}

def galFrame (SP : Set (HeightOneSpectrum (𝓞 ℚ))) (T Q : Finset ℕ) (v0 : T) (pl : ℕ → ValuationSubring Ω)
    (K : Subgroup (G ℚ Ω)) : Alg.Frame (GS Ω SP) where
  T := T
  v0 := v0
  Gv v := Dec (F := ℚ) (pl v)
  φ v := locHom SP (pl v)
  hφ v := continuous_locHom SP (pl v)
  Q := Q
  Gq q := Dec (F := ℚ) (pl q)
  ψ q := locHom SP (pl q)
  hψ q := continuous_locHom SP (pl q)
  N q := (Ine (F := ℚ) (pl q) ⊓ K).subgroupOf (Dec (F := ℚ) (pl q))

structure GalData (l : ℕ) (SP : Set (HeightOneSpectrum (𝓞 ℚ))) (T Q : Finset ℕ) (pl : ℕ → ValuationSubring Ω)
    (K : Subgroup (G ℚ Ω)) : Prop where
  l_odd : l ≠ 2
  prime : ∀ p, p ∈ T ∨ p ∈ Q → p.Prime
  disj : Disjoint T Q
  l_mem : l ∈ T
  mem : ∀ v, v ∈ SP ↔ ∃ p, (p ∈ T ∨ p ∈ Q) ∧ ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal
  isOver : ∀ p, p ∈ T ∨ p ∈ Q → (pl p).valuation (p : Ω) < 1
  idx : ∀ q ∈ Q, ¬ l ∣ K.relIndex (Ine (F := ℚ) (pl q))

def Van {k : Type} [Field k] (T : Finset ℕ) (pl : ℕ → ValuationSubring Ω) (K : Subgroup (G ℚ Ω)) (γ : G ℚ Ω →* kˣ) : Prop :=
  ∀ z : G ℚ Ω → k, IsLocallyConstant z → (∀ g h, z (g * h) = z g + (γ g : k) * z h) →
    (∀ A : ValuationSubring Ω, (∀ p ∈ T, ¬ A.valuation (p : Ω) < 1) → ∀ g ∈ Ine (F := ℚ) A, g ∈ K → z g = 0) →
    (∀ v ∈ T, ∃ m, ∀ g ∈ Dec (F := ℚ) (pl v), z g = (γ g : k) * m - m) → ∃ m, ∀ g, z g = (γ g : k) * m - m

end Gal

end UpperTheory.V.X

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem card_linearMap_zmod_eq_card (n : ℕ) [NeZero n] (N : Type) [AddCommGroup N] [Module (ZMod n) N]
    [Finite N] : Nat.card (N →ₗ[ZMod n] ZMod n) = Nat.card N := by
  classical
  have : Fintype N := Fintype.ofFinite N
  have hfinD : Finite (N →ₗ[ZMod n] ZMod n) :=
    Finite.of_injective (fun f : N →ₗ[ZMod n] ZMod n => (f : N → ZMod n)) DFunLike.coe_injective
  have hcard : Nat.card (AddChar N ℂ) = Nat.card N := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  apply le_antisymm
  · have hinj : Function.Injective
        (fun f : N →ₗ[ZMod n] ZMod n => ZMod.stdAddChar.compAddMonoidHom f.toAddMonoidHom) := by
      intro f g h
      have := AddChar.compAddMonoidHom_injective_right _ ZMod.injective_stdAddChar h
      ext x
      exact DFunLike.congr_fun this x
    rw [← hcard]
    exact Nat.card_le_card_of_injective _ hinj
  · let φ : AddChar N ℂ → N → AddChar (ZMod n) ℂ := fun ψ x =>
      ψ.compAddMonoidHom (LinearMap.toSpanSingleton (ZMod n) N x).toAddMonoidHom
    have hφ : ∀ ψ x y, φ ψ (x + y) = φ ψ x + φ ψ y := by
      intro ψ x y
      ext k
      simp [φ, smul_add, AddChar.map_add_eq_mul]
    let g : AddChar N ℂ → (N →ₗ[ZMod n] ZMod n) := fun ψ =>
      AddMonoidHom.toZModLinearMap n (AddMonoidHom.mk' (fun x => AddChar.zmodAddEquiv.symm (φ ψ x))
        (fun x y => by rw [hφ, map_add (f := _)]))
    have hg : Function.Injective g := by
      intro ψ ψ' h
      ext x
      have h1 : φ ψ x = φ ψ' x := by
        have := LinearMap.congr_fun h x
        simpa [g] using this
      have := DFunLike.congr_fun h1 1
      simpa [φ] using this
    rw [← hcard]
    exact Nat.card_le_card_of_injective g hg

theorem UpperTheory.V.X.So.locCard :
    LocalFiniteness → LocalTateDuality → ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ (v : HeightOneSpectrum (𝓞 k)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation (ZMod (l ^ r)) (Dec (F := k) A) M), ContAction ρ → ∀ (τ : Representation (ZMod (l ^ r)) (Dec (F := k) A) (TDual (ZMod (l ^ r)) M)), (∀ g φ m, τ g φ m = (cycMod k Ω l r g : ZMod (l ^ r)) * φ (ρ g⁻¹ m)) → Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ Nat.card (H2 ρ) = Nat.card (H0 τ) := by
  intro hfin hdual k Ω _ _ _ _ _ l _ r hr v A hA M _ _ _ _ _ ρ hcont τ hτ
  obtain ⟨-, h1, h2, -⟩ := hfin k Ω l r M A ρ v hr hA hcont
  obtain ⟨⟨e⟩, -, -, -, hb⟩ := hdual k Ω l r M A ρ v hr hA hcont
  refine ⟨h1, h2, ?_⟩
  have hτ' : τ = twDual ((cycMod k Ω l r).comp (Dec (F := k) A).subtype) ρ := by
    ext g φ
    apply DFunLike.ext
    intro m
    rw [hτ]
    rfl
  subst hτ'
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hfinD : Finite (TDual (ZMod (l ^ r)) M) :=
    Finite.of_injective (fun f : Module.Dual (ZMod (l ^ r)) M => (f : M → ZMod (l ^ r))) DFunLike.coe_injective
  have hA1 := Nat.card_congr (Equiv.ofBijective _ hb)
  have hA2 := Nat.card_congr (LinearEquiv.congrRight (M := ↥(H0 (MonoidHom.comp
    (twDual ((cycMod k Ω l r).comp (Dec (F := k) A).subtype) ρ) (MonoidHom.id ↥(Dec (F := k) A))))) e).toEquiv
  have hA3 := card_linearMap_zmod_eq_card (l ^ r) ↥(H0 (MonoidHom.comp
    (twDual ((cycMod k Ω l r).comp (Dec (F := k) A).subtype) ρ) (MonoidHom.id ↥(Dec (F := k) A))))
  exact hA1.trans (hA2.trans hA3)
end
