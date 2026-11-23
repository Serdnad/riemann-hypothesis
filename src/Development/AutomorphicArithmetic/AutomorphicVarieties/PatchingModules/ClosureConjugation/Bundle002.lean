module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle008
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle002
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem conj_conj_of_isQuad {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) : F.conj (F.conj g) = g := by
  have h : F.c⁻¹ = F.c := (eq_inv_of_mul_eq_one_left F.c_sq).symm
  apply Subtype.ext
  simp only [GFrame.conj, MonoidHom.coe_mk, OneHom.coe_mk, h]
  simp only [← mul_assoc, F.c_sq, one_mul]
  rw [mul_assoc, F.c_sq, mul_one]

private theorem eps_conj_eq_eps {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (g : F.G₀) : F.eps O R (F.conj g) = F.eps O R g := by
  simp only [GFrame.eps, pushCh, MonoidHom.comp_apply, Subgroup.coe_subtype, GFrame.conj, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, map_inv]
  rw [mul_right_comm, mul_inv_cancel, one_mul]

private theorem star_single_eq_single_conj_inv_mul_eps_zpow' {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) (b : R) : F.star O R n (MonoidAlgebra.single g b) = MonoidAlgebra.single (F.conj g)⁻¹ (b * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]

theorem UpperTheory.V.Pa.star_basic :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (n : ℕ) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R], (∀ y, F.star O R n (F.star O R n y) = y) ∧ (∀ y z, F.star O R n (y * z) = F.star O R n z * F.star O R n y) ∧ (∀ y z, F.star O R n (y + z) = F.star O R n y + F.star O R n z) ∧ (∀ (b : R) y, F.star O R n (b • y) = b • F.star O R n y) ∧ F.star O R n 1 = 1 ∧ (∀ y z, F.star O R n (y - z) = F.star O R n y - F.star O R n z) ∧ ∀ g b, F.star O R n (MonoidAlgebra.single g b) = MonoidAlgebra.single (F.conj g)⁻¹ (b * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  intro l _ F n O _ _ R _ _
  have hadd : ∀ y z, F.star O R n (y + z) = F.star O R n y + F.star O R n z := by
    intro y z
    simp [GFrame.star, map_add (f := _)]
  refine ⟨?_, ?_, hadd, ?_, ?_, ?_, star_single_eq_single_conj_inv_mul_eps_zpow' F O R n⟩
  · intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp [GFrame.star]
    | add y z hy hz => rw [hadd, hadd, hy, hz]
    | single g b =>
      rw [star_single_eq_single_conj_inv_mul_eps_zpow', star_single_eq_single_conj_inv_mul_eps_zpow', map_inv, inv_inv, conj_conj_of_isQuad, map_inv, eps_conj_eq_eps, _root_.inv_zpow', mul_assoc, ← Units.val_mul, ← _root_.zpow_add]
      simp
  · intro y z
    simp [GFrame.star, map_mul]
  · intro b y
    simp [GFrame.star, map_smul]
  · simp [GFrame.star, map_one]
  · intro y z
    simp [GFrame.star, map_sub]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem finite_open_homs_to_finite_group (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (h : TopFG G)
    (Z : Type) [Group Z] [Finite Z] : Finite {φ : G →* Z // IsOpen (φ.ker : Set G)} := by
  obtain ⟨s, hs, hgen⟩ := h
  rw [topGen_iff] at hgen
  have : Finite s := hs.to_subtype
  let f : {φ : G →* Z // IsOpen (φ.ker : Set G)} → (s → Z) := fun φ x => φ.1 x
  apply Finite.of_injective f
  intro φ ψ hφψ
  apply Subtype.ext
  have hK : IsOpen ((φ.1.ker ⊓ ψ.1.ker : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact φ.2.inter ψ.2
  have hle : φ.1.ker ⊓ ψ.1.ker ≤ MonoidHom.eqLocus φ.1 ψ.1 := by
    intro g hg
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hg
    show φ.1 g = ψ.1 g
    rw [hg.1, hg.2]
  have hopen := Subgroup.isOpen_mono hle hK
  have hcl := Subgroup.isClosed_of_isOpen _ hopen
  have hs' : Subgroup.closure (s : Set G) ≤ MonoidHom.eqLocus φ.1 ψ.1 := by
    rw [Subgroup.closure_le]
    intro x hx
    exact congrFun hφψ ⟨x, hx⟩
  have htop := Subgroup.topologicalClosure_minimal _ hs' hcl
  rw [hgen] at htop
  ext g
  exact htop (Subgroup.mem_top g)

theorem UpperTheory.V.Pa.phi_fg :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l),
      (∃ s : Finset F.Γ, (Subgroup.closure (s : Set F.Γ)).topologicalClosure = ⊤) →
        PhiCond (Γ := F.G₀) l := by
  intro l _ F hF
  obtain ⟨s, hs⟩ := hF
  have hΓ : TopFG F.Γ := ⟨(s : Set F.Γ), s.finite_toSet, (topGen_iff _).mpr hs⟩
  have hopen : IsOpen ((F.η.ker : Subgroup F.Γ) : Set F.Γ) := F.η_open
  have hG : TopFG F.G₀ := ((TopFG.subgroup_quot F.Γ hΓ).1 _ hopen)
  have : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ hopen).isCompact
  intro H hH
  have hH' : TopFG H := (TopFG.subgroup_quot F.G₀ hG).1 H hH
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  exact finite_open_homs_to_finite_group H hH' (Multiplicative (ZMod l))
end
