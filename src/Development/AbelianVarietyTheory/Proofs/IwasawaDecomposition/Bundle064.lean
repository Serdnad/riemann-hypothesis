module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle055
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GaloisOfPrimePowerDegree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle045
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongOfCongOnFixed
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle056
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle017
public import ReciprocityTheory.Automorphisms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle059
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle058
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

theorem _root_.GlobalTheory.T.absoluteGaloisAbelianization_eq_one_of_mem_open_subgroups : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (g : Gab E Ω), (∀ U : Subgroup (Gab E Ω), IsOpen (U : Set (Gab E Ω)) → g ∈ U) → g = 1 := by
  first | exact @GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup | exact GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup | (intros; apply GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.openKerChar_wild_eq_one_of_pow_eq_one : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (m : ℕ),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal →
    ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → (∃ N : ℕ, φ τ ^ (m ^ N) = 1) → φ τ = 1 := by
  first | exact @GlobalTheory.WildOpenKernel.eq_one_of_wild | exact GlobalTheory.WildOpenKernel.eq_one_of_wild | (intros; apply GlobalTheory.WildOpenKernel.eq_one_of_wild <;> assumption)
end

section

open Metric Filter Topology Set

namespace GlobalTheory.HyperplaneExt

theorem norm_le_of_off_hyperplane {n : ℕ} {U V : Set (Fin n → ℂ)} {k : Fin n} {F : (Fin n → ℂ) → ℂ} {M : ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContinuousOn F U)
    (hb : ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖F z‖ ≤ M) : ∀ z ∈ V, z ∈ U → ‖F z‖ ≤ M := by
  intro z hzV hzU
  by_cases hz : z k = 0
  · have hc : ContinuousAt F z := hF.continuousAt (hU.mem_nhds hzU)
    have hupd : Continuous (fun ε : ℂ => Function.update z k ε) := continuous_const.update k continuous_id
    have h0 : Function.update z k 0 = z := by rw [← hz]; exact Function.update_eq_self k z
    have ht : Tendsto (fun ε : ℂ => Function.update z k ε) (𝓝[≠] (0 : ℂ)) (𝓝 z) := by
      have := hupd.tendsto 0
      rw [h0] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hT : Tendsto (fun ε : ℂ => F (Function.update z k ε)) (𝓝[≠] (0 : ℂ)) (𝓝 (F z)) :=
      hc.tendsto.comp ht
    refine le_of_tendsto hT.norm ?_
    have hm : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), Function.update z k ε ∈ V ∩ U :=
      ht (inter_mem (hV.mem_nhds hzV) (hU.mem_nhds hzU))
    filter_upwards [hm, self_mem_nhdsWithin] with ε hε hne
    exact hb _ hε.1 hε.2 (by simpa using hne)
  · exact hb z hzV hzU hz

theorem extend_finset (hR : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z₀ ∈ U, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖f z‖ ≤ M) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, z k ≠ 0 → F z = f z) :
    ∀ (n : ℕ) (s : Finset (Fin n)) (W : Set (Fin n → ℂ)) (Φ : (Fin n → ℂ) → ℂ), IsOpen W →
      DifferentiableOn ℂ Φ {z | z ∈ W ∧ ∀ k ∈ s, z k ≠ 0} →
      (∀ z₀ ∈ W, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ W → (∀ k ∈ s, z k ≠ 0) → ‖Φ z‖ ≤ M) →
      ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F W ∧ ∀ z ∈ W, (∀ k ∈ s, z k ≠ 0) → F z = Φ z := by
  intro n s
  induction s using Finset.induction_on with
  | empty =>
    intro W Φ _ hd _
    refine ⟨Φ, ?_, fun _ _ _ => rfl⟩
    simpa using hd
  | insert j t _ ih =>
    intro W Φ hW hd hb
    have hUeq : {z : Fin n → ℂ | z ∈ W ∧ ∀ k ∈ t, z k ≠ 0} = W ∩ ⋂ k ∈ t, {z | z k ≠ 0} := by
      ext z; simp
    have hU : IsOpen {z : Fin n → ℂ | z ∈ W ∧ ∀ k ∈ t, z k ≠ 0} := by
      rw [hUeq]
      exact hW.inter (isOpen_biInter_finset fun k _ => isOpen_ne_fun (continuous_apply k) continuous_const)
    have hd1 : DifferentiableOn ℂ Φ {z | z ∈ {z : Fin n → ℂ | z ∈ W ∧ ∀ k ∈ t, z k ≠ 0} ∧ z j ≠ 0} := by
      refine hd.mono fun z hz => ⟨hz.1.1, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hz.2
      · exact hz.1.2 k hk
    obtain ⟨F1, hF1d, hF1e⟩ := hR n _ j Φ hU hd1 (by
      intro z₀ hz₀
      obtain ⟨V, hV, M, hM⟩ := hb z₀ hz₀.1
      refine ⟨V, hV, M, fun z hzV hzU hzj => hM z hzV hzU.1 ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hzj
      · exact hzU.2 k hk)
    have hall : ∀ z : Fin n → ℂ, (∀ k ∈ insert j t, z k ≠ 0) ↔ z j ≠ 0 ∧ ∀ k ∈ t, z k ≠ 0 := by
      intro z; simp
    obtain ⟨F, hFd, hFe⟩ := ih W F1 hW hF1d (by
      intro z₀ hz₀
      obtain ⟨V, hV, M, hM⟩ := hb z₀ hz₀
      refine ⟨interior V, interior_mem_nhds.mpr hV, M, ?_⟩
      intro z hzV hzW ht
      refine norm_le_of_off_hyperplane (k := j) hU isOpen_interior hF1d.continuousOn
        (fun w hwV hwU hwj => ?_) z hzV ⟨hzW, ht⟩
      rw [hF1e w hwU hwj]
      exact hM w (interior_subset hwV) hwU.1 ((hall w).2 ⟨hwj, hwU.2⟩))
    refine ⟨F, hFd, fun z hz hk => ?_⟩
    have hk' := (hall z).1 hk
    rw [hFe z hz hk'.2, hF1e z ⟨hz, hk'.2⟩ hk'.1]

theorem extension_of_parts
    (h1 : ∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t) (h2 : (∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t) → ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∀ z₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ Metric.ball (0 : Fin n → ℂ) ρ → (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Φ z‖ ≤ M) (h3 : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z₀ ∈ U, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖f z‖ ≤ M) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, z k ≠ 0 → F z = f z) :
    ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ) ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → F z = Φ z := by
  intro n a ρ Φ m hρ hd hb
  have hset : {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} =
      {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), z k ≠ 0} := by
    ext z; simp
  have hmem : ∀ z : Fin n → ℂ, (∀ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), z k ≠ 0) ↔
      ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0 := by
    intro z; simp
  obtain ⟨F, hFd, hFe⟩ := extend_finset h3 n (Finset.univ.filter (fun k : Fin n => (k : ℕ) < a))
    (Metric.ball 0 ρ) Φ isOpen_ball (hset ▸ hd) (by
      intro z₀ hz₀
      obtain ⟨V, hV, M, hM⟩ := h2 h1 n a ρ Φ m hρ hd hb z₀ hz₀
      exact ⟨V, hV, M, fun z hzV hz hk => hM z hzV hz ((hmem z).1 hk)⟩)
  exact ⟨F, hFd, fun z hz hk => hFe z hz ((hmem z).2 hk)⟩

theorem extension_across_coordinate_hyperplanes : ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ) ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → F z = Φ z :=
  extension_of_parts GlobalTheory.T.extension_across_zero_of_exp_two_pi_I_bound GlobalTheory.T.locally_bounded_off_coordinate_hyperplanes GlobalTheory.T.exists_differentiableOn_ext_of_bounded_off_hyperplane

end GlobalTheory.HyperplaneExt
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.exists_LU_decomposition_of_leading_minors_ne_zero : ∀ {n : ℕ} (B : GL (Fin n) ℂ), (∀ (k : ℕ) (hk : k ≤ n), (B.val.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) → ∃ L U : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual ∧ U.val.BlockTriangular id ∧ B = L * U := by
  first | exact @GlobalTheory.LUDecomp.lu | exact GlobalTheory.LUDecomp.lu | (intros; apply GlobalTheory.LUDecomp.lu <;> assumption)
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.lowerTriangular_GL_complex_induction : ∀ {n : ℕ} (P : GL (Fin n) ℂ → Prop), P 1 → (∀ A B, P A → P B → P (A * B)) → (∀ D : GL (Fin n) ℂ, D.val.IsDiag → P D) → (∀ (i j : Fin n) (s : ℂ) (T : GL (Fin n) ℂ), j < i → T.val = transvection i j s → P T) → ∀ L : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual → P L := by
  first | exact @GlobalTheory.lowerTriangular_GL_induction | exact GlobalTheory.lowerTriangular_GL_induction | (intros; apply GlobalTheory.lowerTriangular_GL_induction <;> assumption)
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.finite_shifts_vanishing_leading_minor : ∀ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ), Set.Finite {s : ℂ | ¬ ∀ (k : ℕ) (hk : k ≤ n), ((B + s • (1 : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0} := by
  first | exact @GlobalTheory.shift_minors_vanish_finite | exact GlobalTheory.shift_minors_vanish_finite | (intros; apply GlobalTheory.shift_minors_vanish_finite <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.InertiaTameRoot

theorem exists_inertia_moves_root : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] [CharZero W]
    (F : Type) [Field F] [Algebra (FractionRing W) F] [IsAlgClosure (FractionRing W) F] (ϖ : W), Irreducible ϖ →
    ∀ k : ℕ, IsUnit (k : W) → ∃ (O : ValuationSubring F) (φ : W →+* O) (σ : F →ₐ[FractionRing W] F) (π : F),
      IsLocalHom φ ∧ (∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w)) ∧
      (∀ x ∈ O, O.valuation (σ x - x) < 1) ∧ π ^ k = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) ϖ) ∧
      IsPrimitiveRoot (σ π / π) k := by
  intro W _ _ _ _ _ F _ _ _ ϖ hϖ k hk
  let K := FractionRing W
  letI : Algebra W F := ((algebraMap K F).comp (algebraMap W K)).toAlgebra
  haveI : IsScalarTower W K F := .of_algebraMap_eq fun _ => rfl
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (M₀ := W) (by simpa using hk)
  let f : W →+* F := algebraMap W F
  have hf : Function.Injective f := (algebraMap K F).injective.comp (IsFractionRing.injective W K)
  obtain ⟨O, hO⟩ := (LocalSubring.range f).exists_le_valuationSubring
  obtain ⟨h1, hloc⟩ := (GlobalTheory.localSubring_range_le_valuationSubring_iff_isLocalHom f O).1 hO
  have h2 := ((GlobalTheory.localSubring_range_le_valuationSubring_iff f O).1 hO).2
  haveI : CharZero K := inferInstance
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  haveI : IsAlgClosed F := IsAlgClosure.isAlgClosed K
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (f ϖ) (Nat.pos_of_ne_zero hk0)
  haveI : NeZero (k : F) := ⟨by exact_mod_cast hk0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F k
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hk0, eq_comm, map_eq_zero_iff f hf] at hπ
    exact hϖ.ne_zero hπ
  have hmin := GlobalTheory.TameKummer.minpoly_eq K hϖ hk0 (ρ := π) hπ
  have hmin' := GlobalTheory.TameKummer.minpoly_eq K hϖ hk0 (ρ := ζ * π)
    (by rw [mul_pow, hζ.pow_eq_one, _root_.one_mul]; exact hπ)
  haveI : IsGalois K F := {}
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := K) F (x := ζ * π) (y := π)).1
    (hmin'.trans hmin.symm)
  change g π = ζ * π at hg

  let S := integralClosure W F
  have hc : SMulCommClass (F ≃ₐ[K] F) W F := ⟨fun g v x => by
    rw [← IsScalarTower.algebraMap_smul K v x, ← IsScalarTower.algebraMap_smul K v (g • x)]
    simp only [AlgEquiv.smul_def, Algebra.smul_def, _root_.map_mul, AlgEquiv.commutes]⟩
  letI : TopologicalSpace S := ⊥
  haveI : DiscreteTopology S := ⟨rfl⟩
  haveI : ContinuousSMul (F ≃ₐ[K] F) S := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    have := stabilizer_isOpen_of_isIntegral (K := K) (x : F)
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact Subtype.ext_iff
  let H := MulAction.stabilizer (F ≃ₐ[K] F) π
  have hH : IsClosed (H : Set (F ≃ₐ[K] F)) :=
    H.isClosed_of_isOpen (stabilizer_isOpen_of_isIntegral (K := K) π)
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  let φ : W →+* O := f.codRestrict O h1
  letI : Algebra W O := φ.toAlgebra
  haveI : IsScalarTower W O F := .of_algebraMap_eq fun _ => rfl
  have hSO : ∀ b : F, IsIntegral W b → b ∈ O := by
    intro b hb
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := O) (K := F)).mp hb.tower_top
    rw [← hy]
    exact y.2
  let incl : S →+* O := (S.val.toRingHom).codRestrict O (fun b => hSO b b.2)
  let Q : Ideal S := (maximalIdeal O).comap incl
  have hQ : ∀ b : S, b ∈ Q ↔ O.valuation (b : F) < 1 := fun b =>
    ValuationSubring.valuation_lt_one_iff O (incl b)
  obtain ⟨a₁, ha₁, a₂, ha₂, hcong⟩ := GlobalTheory.InertiaMovesRoot.exists_cong_of_cong_on_fixed (R := W) H Q g
    (fun b hb => by
      rw [hQ]
      refine GlobalTheory.T.automorphism_congr_one_on_adjoin_root_uniformiser W F O h1 h2 ϖ hϖ k hk0 π hπ g b ?_ ((O.valuation_le_one_iff _).mpr (hSO b b.2))
      rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin K {π}),
        IntermediateField.mem_fixedField_iff]
      intro e he
      exact congrArg Subtype.val (hb e (he ⟨π, IntermediateField.mem_adjoin_simple_self K π⟩)))
  let σ := a₂ * g * a₁
  have hσπ : σ π = a₂ ζ * π := by
    have e1 : a₁ π = π := ha₁
    have e2 : a₂ π = π := ha₂
    simp only [σ, AlgEquiv.mul_apply, e1, hg, map_mul, e2]
  have hσS : ∀ b : F, IsIntegral W b → O.valuation (σ b - b) < 1 := fun b hb =>
    (hQ (σ • ⟨b, hb⟩ - ⟨b, hb⟩)).1 (hcong ⟨b, hb⟩)
  refine ⟨O, φ, σ.toAlgHom, π, hloc, fun w => rfl, fun x hx => ?_, hπ, ?_⟩
  · obtain ⟨s, t, hs, ht, hs1, e⟩ := GlobalTheory.T.exists_integral_quotient_dominating_valuationSubring W F O h1 h2 x hx
    change O.valuation (σ x - x) < 1
    have hs' := hσS s hs
    have ht' := hσS t ht
    have htv : O.valuation t ≤ 1 := (O.valuation_le_one_iff _).mpr (hSO t ht)
    have hσs : O.valuation (σ s) = 1 := by
      have : σ s = s + (σ s - s) := by ring
      rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [hs1]; exact hs'), hs1]
    have key : s * σ s * (σ x - x) = s * (σ t - t) - t * (σ s - s) := by
      rw [← e, map_mul]; ring
    have hv : O.valuation (s * σ s * (σ x - x)) < 1 := by
      rw [key]
      refine Valuation.map_sub_lt _ ?_ ?_
      · rw [map_mul, hs1, _root_.one_mul]; exact ht'
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' htv) hs'
    rwa [map_mul, map_mul, hs1, hσs, _root_.one_mul, _root_.one_mul] at hv
  · change IsPrimitiveRoot (σ π / π) k
    rw [hσπ, mul_div_cancel_right₀ _ hπ0]
    exact hζ.map_of_injective a₂.injective

end GlobalTheory.InertiaTameRoot
end

section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.exists_conductor_adicCompletion_essFiniteType : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A] [Algebra.EssFiniteType ℤ A], ∃ x : A, x ≠ 0 ∧ ∀ c : FractionRing (AdicCompletion (maximalIdeal A) A), IsIntegral (AdicCompletion (maximalIdeal A) A) c → ∃ s : AdicCompletion (maximalIdeal A) A, algebraMap _ (FractionRing (AdicCompletion (maximalIdeal A) A)) s = algebraMap _ (FractionRing (AdicCompletion (maximalIdeal A) A)) (algebraMap A (AdicCompletion (maximalIdeal A) A) x) * c := by
  first | exact @GlobalTheory.exists_conductor_adicCompletion_of_essFiniteType | exact GlobalTheory.exists_conductor_adicCompletion_of_essFiniteType | (intros; apply GlobalTheory.exists_conductor_adicCompletion_of_essFiniteType <;> assumption)
end

section

open IsLocalRing

namespace GlobalTheory

theorem finite_integralClosure_of_isLocalization {R S L : Type*} [CommRing R] [CommRing S]
    [CommRing L] [Algebra R S] [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    (M : Submonoid R) [IsLocalization M S] [Module.Finite R (integralClosure R L)] :
    Module.Finite S (integralClosure S L) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := integralClosure R L)
  let f : integralClosure R L → integralClosure S L := fun z => ⟨z, IsIntegral.tower_top z.2⟩
  refine ⟨⟨s.image f, ?_⟩⟩
  rw [eq_top_iff]
  rintro y -
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M (Rₘ := S) (y : L) y.2
  have key : ∀ z ∈ Submodule.span R (s : Set (integralClosure R L)),
      f z ∈ Submodule.span S (↑(s.image f) : Set (integralClosure S L)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem f hx))
    | zero =>
      have : f 0 = 0 := rfl
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : f (x + y) = f x + f y := rfl
      rw [this]; exact add_mem hx hy
    | smul a x _ hx =>
      have : f (a • x) = algebraMap R S a • f x := by
        apply Subtype.ext
        change a • (x : L) = algebraMap R S a • (x : L)
        rw [algebraMap_smul]
      rw [this]; exact Submodule.smul_mem _ _ hx
  have hz : (⟨m • (y : L), hm⟩ : integralClosure R L) ∈ Submodule.span R (s : Set _) :=
    hs ▸ Submodule.mem_top
  have e : y = IsLocalization.mk' S (1 : R) m • f ⟨m • (y : L), hm⟩ := by
    apply Subtype.ext
    change (y : L) = IsLocalization.mk' S (1 : R) m • ((m : R) • (y : L))
    rw [Algebra.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R S L, ← mul_assoc,
      ← map_mul, IsLocalization.mk'_spec, map_one, map_one, one_mul]
  rw [e]
  exact Submodule.smul_mem _ _ (key _ hz)

theorem finite_integralClosure_of_essFiniteType_int :
    ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D],
      Module.Finite D (integralClosure D (FractionRing D)) := by
  intro D _ _ _
  obtain ⟨S₀, M, hft, hloc⟩ := (Algebra.essFiniteType_iff_exists_subalgebra ℤ D).mp inferInstance
  let K := FractionRing D
  have hinj : Function.Injective (algebraMap S₀ D) := Subtype.val_injective
  haveI hfr : IsFractionRing S₀ K := by
    have h := IsLocalization.localization_localization_isLocalization_of_has_all_units M (nonZeroDivisors D) K
      (fun x hx => hx.mem_nonZeroDivisors)
    have e : (nonZeroDivisors D).comap (algebraMap S₀ D) = nonZeroDivisors S₀ := by
      ext x
      simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero, ne_eq]
      exact (map_eq_zero_iff _ hinj).not
    rw [e] at h
    exact h
  suffices h : Module.Finite S₀ (integralClosure S₀ K) from
    finite_integralClosure_of_isLocalization M
  rcases CharP.char_is_prime_or_zero D (ringChar D) with hp | h0
  · haveI : Fact (ringChar D).Prime := ⟨hp⟩
    haveI : CharP D (ringChar D) := ringChar.charP D
    haveI : CharP S₀ (ringChar D) := ⟨fun n => by
      rw [← map_eq_zero_iff _ hinj, map_natCast, CharP.cast_eq_zero_iff D]⟩
    letI : Algebra (ZMod (ringChar D)) S₀ := (ZMod.castHom dvd_rfl S₀).toAlgebra
    haveI : Algebra.FiniteType (ZMod (ringChar D)) S₀ :=
      .of_restrictScalars_finiteType ℤ (ZMod (ringChar D)) S₀
    exact NormFin.finite_integralClosure_of_perfectField (ZMod (ringChar D)) S₀ K K
  · haveI : CharZero D := (CharP.ringChar_zero_iff_CharZero D).mp h0
    haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective D K)
    haveI : Algebra.EssFiniteType S₀ D := .of_isLocalization D M
    haveI : Algebra.EssFiniteType D K := .of_isLocalization K (nonZeroDivisors D)
    haveI : Algebra.EssFiniteType S₀ K := .comp S₀ D K
    exact GlobalTheory.finite_integralClosure_of_essFiniteType_field ℤ S₀ K

end GlobalTheory
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.cayleyTransform_mem_rational_unitaryGroup : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (S : Matrix (Fin n) (Fin n) L), S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 → (1 - S).det ≠ 0 → ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ (γ₀ : Matrix (Fin n) (Fin n) L) = (1 + S) * (1 - S)⁻¹ := by
  first | exact @GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian | exact GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian | (intros; apply GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne


theorem _root_.GlobalTheory.T.inertia_lift_of_residual_trivial : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w → ∀ (L : IntermediateField E Ω) (ψ : G E Ω), ψ ∈ Dec (F := E) A → (∀ x ∈ L, IsIntegral ℤ x → A.valuation (ψ x - x) < 1) → ∃ ι ∈ Ine (F := E) A, ∀ x ∈ L, ι x = ψ x := by
  first | exact @GlobalTheory.InertiaLift.exists_mem_Ine_eq_on | exact GlobalTheory.InertiaLift.exists_mem_Ine_eq_on | (intros; apply GlobalTheory.InertiaLift.exists_mem_Ine_eq_on <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_inertia_tameChar_primitiveRoot_of_uniformizerRoot : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ) (ϖ : 𝓞 E) (π : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    π ^ L = algebraMap E Ω (ϖ : E) → ∃ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, IsPrimitiveRoot (σ π / π) L := by
  first | exact @GlobalTheory.TameRootSurj.main | exact GlobalTheory.TameRootSurj.main | (intros; apply GlobalTheory.TameRootSurj.main <;> assumption)
end
