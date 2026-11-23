module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle010
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle109
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle011
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.KernelRankAlgebraicBound
public import Mathlib.RingTheory.Unramified.Basic
public import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsUnitValueSkewHermitian
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle003
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle002
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001

@[expose] public section

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.dual_family_is_basis : ∀ (V : Type) [CommRing V] (L : Type) [AddCommGroup L] [Module V L] (n : ℕ) (b : Module.Basis (Fin n) V L) (u : Fin n → L) (f : Fin n → (L →ₗ[V] V)) (N : V), IsUnit N → (∀ i j, f j (u i) = if i = j then N else 0) → LinearIndependent V u ∧ Submodule.span V (Set.range u) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.linearIndependent_span_of_dual_unit | exact GlobalTheory.CompanionTheory.CommAlg.linearIndependent_span_of_dual_unit | (intros; apply GlobalTheory.CompanionTheory.CommAlg.linearIndependent_span_of_dual_unit <;> assumption)
end

section


theorem _root_.GlobalTheory.T.saturated_lattice_quotient_count : ∀ (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (B : LinearMap.BilinForm ℤ Λ), Function.Bijective B → (∀ x, B x x = 0) → ∀ W : Submodule ℤ Λ, (∀ (k : ℤ) x, k ≠ 0 → k • x ∈ W → x ∈ W) → (∀ N : ℕ, 0 < N → ∃ T : Set (W ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : W →ₗ[ℤ] W))), Nat.card (W ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : W →ₗ[ℤ] W))) * Nat.card T = N ^ Module.finrank ℤ Λ ∧ ∀ x y : W, Submodule.Quotient.mk x ∈ T → (N : ℤ) ∣ B x y) → ∀ x, (∀ y ∈ W, B x y = 0) → x ∈ W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.mem_of_forall_card_mul_eq_pow | exact GlobalTheory.CompanionTheory.Ar.Flat.mem_of_forall_card_mul_eq_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.mem_of_forall_card_mul_eq_pow <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.lattice_kernel_rank_bound_norm : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (a : 𝓞 E), a ≠ 0 → Module.finrank k (LinearMap.ker (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ))) ≤ Module.finrank (𝓞 E) Λ * padicValNat p (Algebra.norm ℤ a).natAbs ∧ (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ)).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ Module.finrank (𝓞 E) Λ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.free_extension_kernel_bound_charpoly | exact GlobalTheory.CompanionTheory.Ar.Flat.free_extension_kernel_bound_charpoly | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.free_extension_kernel_bound_charpoly <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.characteristic_polynomial_free_generators : ∀ (E : Type) [Field E] [NumberField E] (k W : Type) [Field k] [CharZero k] [AddCommGroup W] [Module k W] [FiniteDimensional k W] (r : ℕ) (ρ : 𝓞 E →+* Module.End k W), (∀ a : 𝓞 E, (ρ a).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ r) → ∃ x : Fin r → W, LinearIndependent k (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) ∧ Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.charpoly_condition_gives_free_char_zero | exact GlobalTheory.CompanionTheory.Ar.Flat.charpoly_condition_gives_free_char_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.charpoly_condition_gives_free_char_zero <;> assumption)
end

section

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem lemF_algebra : ∀ (E : Type) [Field E] [NumberField E] (k W : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] [AddCommGroup W] [Module k W] [FiniteDimensional k W] (r : ℕ) (ρ : 𝓞 E →+* Module.End k W), (∀ a : 𝓞 E, (ρ a).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ r) → (∀ a : 𝓞 E, a ≠ 0 → Module.finrank k (LinearMap.ker (ρ a)) ≤ r * padicValNat p (Algebra.norm ℤ a).natAbs) → ∃ x : Fin r → W, LinearIndependent k (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) ∧ Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) = ⊤ :=
  @PositivityTheory.Xgn.kernel_rank_algebraic_bound

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.CommAlg

theorem skewHermitian_congr_diag : ∀ (R : Type) [CommRing R] [StarRing R] [Finite (MaximalSpectrum R)] (n : ℕ) (G : Matrix (Fin n) (Fin n) R), Gᴴ = -G → IsUnit G.det → (∀ m : Ideal R, m.IsMaximal → ∃ a : R, a - star a ∉ m) → ∃ T : Matrix (Fin n) (Fin n) R, IsUnit T.det ∧ (T * G * Tᴴ).IsDiag := by
  exact @PositivityTheory.Xgf.skew_hermitian_diagonalizable

end GlobalTheory.CompanionTheory.CommAlg
end

section

open NumberField

theorem _root_.GlobalTheory.T.representation_basis_linear_independent : ∀ (E : Type) [Field E] [NumberField E] (R k : Type) [CommRing R] [IsLocalRing R] [Field k] (f : R →+* k) [IsLocalHom f] (n : Type) [Fintype n] [DecidableEq n] (r : ℕ) (ρ : 𝓞 E →+* Matrix n n R), (∃ x : Fin r → n → k, LinearIndependent k (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ((ρ (RingOfIntegers.basis E q.2)).map f).mulVec (x q.1)) ∧ Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ((ρ (RingOfIntegers.basis E q.2)).map f).mulVec (x q.1)) = ⊤) → ∃ x : Fin r → n → R, LinearIndependent R (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => (ρ (RingOfIntegers.basis E q.2)).mulVec (x q.1)) ∧ Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => (ρ (RingOfIntegers.basis E q.2)).mulVec (x q.1)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.free_of_free_over_field | exact GlobalTheory.CompanionTheory.Ar.Flat.free_of_free_over_field | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.free_of_free_over_field <;> assumption)
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_pow_principal : ∀ (F : Type) [Field F] [NumberField F]
    (r : HeightOneSpectrum (𝓞 F) →₀ ℚ), ∃ (M : ℕ) (α : F), 0 < M ∧ α ≠ 0 ∧
      ∀ v : HeightOneSpectrum (𝓞 F), ∃ n : ℤ, (n : ℚ) = M * r v ∧
        v.valuation F α = WithZero.exp (-n) := by
  intro F _ _ r
  obtain ⟨M, α, hM, hα, h⟩ := GlobalTheory.RootIdeal.exists_count_spanSingleton_eq_mul F r
  exact ⟨M, α, hM, hα, fun v => ⟨_, h v, GlobalTheory.Idele.valuation_eq_exp_neg_count v hα⟩⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open NumberField

theorem _root_.GlobalTheory.T.statement_unavailable_one : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (emb : (E →+* C) → (𝓞 E →+* V)), (∀ s (a : 𝓞 E), algebraMap V C (emb s a) = s (a : E)) → Nat.card (E →+* C) = Module.finrank ℚ E → ∀ σ : E →+* C, ∃ π : 𝓞 E, (∀ s s' : E →+* C, (∀ a, ¬ IsUnit (emb s a - emb σ a)) → (∀ a, ¬ IsUnit (emb s' a - emb σ a)) → emb s π = emb s' π → s = s') ∧ ∀ f : (E →+* C) → V, (∀ s, (∃ a, IsUnit (emb s a - emb σ a)) → f s = 0) → ((∃ g : Polynomial V, ∀ s, (∀ a, ¬ IsUnit (emb s a - emb σ a)) → f s = g.eval (emb s π)) ↔ f ∈ Submodule.span V (Set.range fun a : 𝓞 E => fun s => emb s a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.block_monogenic_of_residual_character | exact GlobalTheory.CompanionTheory.Ar.Flat.block_monogenic_of_residual_character | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.block_monogenic_of_residual_character <;> assumption)
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.CommAlg

theorem conj_not_trivial_mod_maximal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ m : Ideal (𝓞 E), m.IsMaximal → ∃ a : 𝓞 E, a - bar a ∉ m :=
  PositivityTheory.Xgf.exists_not_mem_sub_conj

end GlobalTheory.CompanionTheory.CommAlg
end

section


theorem _root_.GlobalTheory.CompanionTheory.Relay.adic_complete_algebra_lifting_unique : ∀ (R A B : Type) [CommRing R] [IsNoetherianRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Module.Finite R A] (I : Ideal R) [IsAdicComplete I R] (f : ∀ e : ℕ, B →ₐ[R] A ⧸ (I ^ (e + 1)).map (algebraMap R A)), (∀ e (b : B) (a : A), Ideal.Quotient.mk _ a = f (e + 1) b → Ideal.Quotient.mk _ a = f e b) → ∃! g : B →ₐ[R] A, ∀ e b, Ideal.Quotient.mk _ (g b) = f e b := by
  first | exact @PositivityTheory.HtPt.Mi.algHom_of_system | exact PositivityTheory.HtPt.Mi.algHom_of_system
end

section

open TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isDomain_tensor_of_algebraically_closed_constants :
    ∀ (K Ω C : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [Field C] [Algebra K C],
      (∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) → IsDomain (Ω ⊗[K] C) :=
  @PositivityTheory.Xgn.tensor_algebraically_closed_domain

end GlobalTheory.CompanionTheory.Ar.Flat
end
