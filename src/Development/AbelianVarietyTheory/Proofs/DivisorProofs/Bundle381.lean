module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle102
public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Mathlib.Topology.Algebra.Group.Units
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle221
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle082
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle109
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle317
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle314
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Mathlib.RingTheory.Norm.Transitivity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228

@[expose] public section

section

open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CovolIndep
variable {S X : Type} [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X]
  [MeasurableSMul₂ S X]

theorem measure_mul_setLIntegral_eq [MeasurableInv S] (ν : Measure S) [SFinite ν] (μ : Measure X) [SFinite μ]
    [SMulInvariantMeasure S X μ] (D : Set X) (hD : MeasurableSet D) (E : Set S)
    (hE : MeasurableSet E) (ψ : X → ℝ≥0∞) (hψ : Measurable ψ)
    (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ν E * ∫⁻ x in D, ψ x ∂μ = ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D}) ∂μ :=
  GlobalTheory.T.lintegral_mul_measure_inter_smul_preimage_of_invariant S X ν μ D hD E hE ψ hψ hinv

theorem lintegral_unfold_eq [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S) [SFinite ν]
    [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ]
    (Γ : Subgroup S) [Countable Γ] (D₁ D₂ : Set X) (hD₁ : MeasurableSet D₁)
    (hD₂ : IsFundamentalDomain Γ D₂ μ) (E : Set S) (hE : MeasurableSet E)
    (hEf : IsFundamentalDomain Γ E ν) (ψ : X → ℝ≥0∞) (hψ : Measurable ψ)
    (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D₁}) ∂μ = ∫⁻ y in D₂, ψ y * ν {s | s⁻¹ • y ∈ D₁} ∂μ :=
  GlobalTheory.T.lintegral_fundamentalDomain_unfold_refold_measure S X ν μ Γ D₁ D₂ hD₁ hD₂ E hE hEf ψ hψ hinv

theorem ae_measure_setOf_smul_mem_eq [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S) [SFinite ν]
    [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ]
    (Γ : Subgroup S) [Countable Γ] (D : Set X) (hD : MeasurableSet D)
    (hDf : IsFundamentalDomain Γ D μ) (E : Set S) (hE : IsFundamentalDomain Γ E ν) :
    ∀ᵐ y ∂μ, ν {s | s • y ∈ D} = ν E :=
  GlobalTheory.T.ae_measure_smul_preimage_fundamentalDomain_eq S X ν μ Γ D hD hDf E hE

theorem lintegral_mul_eq_of_measurable [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S)
    [SFinite ν] [ν.IsMulLeftInvariant] [ν.IsInvInvariant] (μ : Measure X) [SFinite μ]
    [SMulInvariantMeasure S X μ] (Γ₁ Γ₂ : Subgroup S) [Countable Γ₁] [Countable Γ₂]
    (D₁ D₂ : Set X) (E₁ E₂ : Set S) (hD₁m : MeasurableSet D₁) (hD₂m : MeasurableSet D₂)
    (hE₂m : MeasurableSet E₂)
    (hD₁ : IsFundamentalDomain Γ₁ D₁ μ) (hD₂ : IsFundamentalDomain Γ₂ D₂ μ)
    (hE₁ : IsFundamentalDomain Γ₁ E₁ ν) (hE₂ : IsFundamentalDomain Γ₂ E₂ ν)
    (ψ : X → ℝ≥0∞) (hψ : Measurable ψ) (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ν E₂ * ∫⁻ x in D₁, ψ x ∂μ = ν E₁ * ∫⁻ x in D₂, ψ x ∂μ := by
  rw [measure_mul_setLIntegral_eq ν μ D₁ hD₁m E₂ hE₂m ψ hψ hinv,
    lintegral_unfold_eq ν μ Γ₂ D₁ D₂ hD₁m hD₂ E₂ hE₂m hE₂ ψ hψ hinv, ← lintegral_const_mul _ hψ]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [ae_measure_setOf_smul_mem_eq ν μ Γ₁ D₁ hD₁m hD₁ E₁ hE₁] with y hy
  have : ν {s : S | s⁻¹ • y ∈ D₁} = ν {s : S | s • y ∈ D₁} := by
    change ν ({s : S | s • y ∈ D₁}⁻¹) = _
    exact Measure.measure_inv (μ := ν) _
  rw [this, hy, mul_comm]
end GlobalTheory.CovolIndep

namespace GlobalTheory.CovolIndep
variable {S X : Type} [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X]
  [MeasurableSMul₂ S X]

theorem lintegral_mul_eq [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S)
    [SFinite ν] [ν.IsMulLeftInvariant] [ν.IsInvInvariant] (μ : Measure X) [SFinite μ]
    [SMulInvariantMeasure S X μ] (Γ₁ Γ₂ : Subgroup S) [Countable Γ₁] [Countable Γ₂]
    (D₁ D₂ : Set X) (E₁ E₂ : Set S)
    (hD₁ : IsFundamentalDomain Γ₁ D₁ μ) (hD₂ : IsFundamentalDomain Γ₂ D₂ μ)
    (hE₁ : IsFundamentalDomain Γ₁ E₁ ν) (hE₂ : IsFundamentalDomain Γ₂ E₂ ν)
    (ψ : X → ℝ≥0∞) (hψ : Measurable ψ) (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ν E₂ * ∫⁻ x in D₁, ψ x ∂μ = ν E₁ * ∫⁻ x in D₂, ψ x ∂μ := by
  have a₁ := hD₁.nullMeasurableSet.toMeasurable_ae_eq
  have a₂ := hD₂.nullMeasurableSet.toMeasurable_ae_eq
  have b₂ := hE₂.nullMeasurableSet.toMeasurable_ae_eq
  have key := lintegral_mul_eq_of_measurable ν μ Γ₁ Γ₂ (toMeasurable μ D₁) (toMeasurable μ D₂)
    E₁ (toMeasurable ν E₂) (measurableSet_toMeasurable _ _) (measurableSet_toMeasurable _ _)
    (measurableSet_toMeasurable _ _) (isFundamentalDomain_of_ae_eq hD₁ a₁)
    (isFundamentalDomain_of_ae_eq hD₂ a₂) hE₁ (isFundamentalDomain_of_ae_eq hE₂ b₂) ψ hψ hinv
  rwa [measure_toMeasurable, setLIntegral_congr a₁, setLIntegral_congr a₂] at key

end GlobalTheory.CovolIndep

namespace GlobalTheory

end GlobalTheory
end

section

noncomputable section

open GlobalTheory.WeilM MeasureTheory MeasureTheory.Measure
open scoped Matrix NNReal

namespace GlobalTheory.ParAvg

theorem isMulRightInvariant_of_modular {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegular]
    (h : ∀ g : G, modularCharacterFun g = 1) : μ.IsMulRightInvariant :=
  ⟨fun g => by rw [map_right_mul_eq_modularCharacterFun_smul μ g, h g, one_smul]⟩

theorem modularCharacterFun_GL {r : ℕ} {E : Type} [Field E] [TopologicalSpace E] [IsTopologicalRing E]
    [LocallyCompactSpace (GL (Fin r) E)] (a : GL (Fin r) E) : modularCharacterFun a = 1 := by
  borelize (GL (Fin r) E)
  refine GlobalTheory.SplitFlip.hom_eq_one_of_center (modularCharacter : GL (Fin r) E →* ℝ≥0) (fun z hz => ?_) a
  change modularCharacterFun z = 1
  have e : map (fun x : GL (Fin r) E => x * z) (haar : Measure (GL (Fin r) E)) = haar := by
    rw [show (fun x : GL (Fin r) E => x * z) = fun x => z * x from funext fun x => (hz x).symm,
      map_mul_left_eq_self]
  rw [modularCharacterFun_eq_haarScalarFactor (haar : Measure (GL (Fin r) E)) z]
  simp only [e, haarScalarFactor_self]

end GlobalTheory.ParAvg
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LatTrace

open Polynomial

theorem aeval_mulVec_of_eigen {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {n : Type*}
    [Fintype n] [DecidableEq n]
    (Q : Matrix n n S) (μ : S) (v : n → S) (hv : Q *ᵥ v = μ • v) (p : R[X]) :
    (aeval Q p) *ᵥ v = (aeval μ p) • v := by
  have hpow : ∀ k : ℕ, (Q ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hv, smul_smul, pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), Matrix.add_mulVec, hp, hq, add_smul]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, ← Matrix.mulVec_mulVec, hpow,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_mul_assoc, one_mul, smul_assoc]

theorem aeval_restrict_coe {S : Type*} [CommRing S] {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n S) (L : Submodule ℤ (n → S))
    (hQ : ∀ x ∈ L, (Q.mulVecLin.restrictScalars ℤ) x ∈ L) (p : ℤ[X]) (x : L) :
    ((aeval (LinearMap.restrict (Q.mulVecLin.restrictScalars ℤ) hQ) p x : L) : n → S) =
      (aeval Q p) *ᵥ (x : n → S) := by
  set f := LinearMap.restrict (Q.mulVecLin.restrictScalars ℤ) hQ
  have hpow : ∀ k : ℕ, (((f ^ k) x : L) : n → S) = (Q ^ k) *ᵥ (x : n → S) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, pow_succ',
        ← Matrix.mulVec_mulVec, ← ih]
      rfl
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, Submodule.coe_add, hp, hq,
      Matrix.add_mulVec]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul, hpow, ← Matrix.mulVec_mulVec, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.one_mulVec]

theorem isIntegral_trace_of_isIntegral {K : Type} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : IsIntegral ℤ M) : IsIntegral ℤ M.trace := by
  let φ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  obtain ⟨p, hpm, hp0⟩ := hM
  have hpM : aeval M p = 0 := by rw [aeval_def]; exact hp0
  set M' := M.map φ
  have hpM' : aeval M' p = 0 := by
    have h := Polynomial.aeval_algHom_apply (φ.mapMatrix (m := Fin n)).toIntAlgHom M p
    rw [hpM, map_zero] at h
    exact h
  have htr : φ M.trace = M'.trace := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, M', map_sum]
  have hroots : ∀ μ ∈ M'.charpoly.roots, IsIntegral ℤ μ := by
    intro μ hμ
    have h0 : M'.charpoly.eval μ = 0 := (Polynomial.mem_roots'.1 hμ).2
    rw [Matrix.eval_charpoly] at h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hev : M' *ᵥ v = μ • v := by
      have h1 : (Matrix.scalar (Fin n) μ - M') *ᵥ v = μ • v - M' *ᵥ v := by
        rw [Matrix.sub_mulVec]
        congr 1
        ext i
        simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
      rw [h1, sub_eq_zero] at hv
      exact hv.symm
    have h2 := aeval_mulVec_of_eigen M' μ v hev p
    rw [hpM', Matrix.zero_mulVec] at h2
    have hz : aeval μ p = 0 := by
      by_contra hne
      exact hv0 ((smul_eq_zero.1 h2.symm).resolve_left hne)
    exact ⟨p, hpm, by rw [← aeval_def]; exact hz⟩
  have hsum : IsIntegral ℤ M'.trace := by
    rw [Matrix.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
    have := multiset_sum_mem (M'.charpoly.roots)
      (fun x hx => ((mem_integralClosure_iff ℤ (AlgebraicClosure K)).2 (hroots x hx) : x ∈ integralClosure ℤ (AlgebraicClosure K)))
    exact (mem_integralClosure_iff ℤ (AlgebraicClosure K)).1 this
  rw [← htr] at hsum
  exact (isIntegral_algHom_iff φ.toIntAlgHom φ.injective).mp hsum

theorem isIntegral_of_preserves_lattice {E : Type} [Field E] [NumberField E] {r : ℕ}
    (Λ : Submodule (𝓞 E) (Fin r → E)) (A : Matrix (Fin r) (Fin r) E) (hfg : Λ.FG)
    (hsp : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (hA : ∀ x ∈ Λ, A *ᵥ x ∈ Λ) :
    IsIntegral ℤ A := by
  set Lz := Λ.restrictScalars ℤ
  have : Module.Finite ℤ Lz := Module.Finite.iff_fg.mpr hfg.restrictScalars
  have hAz : ∀ x ∈ Lz, (A.mulVecLin.restrictScalars ℤ) x ∈ Lz := fun x hx => hA x hx
  obtain ⟨p, hpm, hp⟩ :=
    LinearMap.exists_monic_and_aeval_eq_zero ℤ
      (LinearMap.restrict (A.mulVecLin.restrictScalars ℤ) hAz)
  have hpA : aeval A p = 0 := by
    have hker : ∀ x ∈ Λ, (aeval A p) *ᵥ x = 0 := by
      intro x hx
      have h := aeval_restrict_coe A Lz hAz p ⟨x, hx⟩
      rw [hp] at h
      rw [← h]; rfl
    have hle : Submodule.span E (Λ : Set (Fin r → E)) ≤ LinearMap.ker (aeval A p).mulVecLin :=
      Submodule.span_le.2 fun x hx => hker x hx
    rw [hsp] at hle
    ext i j
    have h := congrFun (hle (Submodule.mem_top : Pi.single j (1 : E) ∈ ⊤)) i
    simpa [Matrix.mulVec_single] using h
  exact ⟨p, hpm, by rw [← aeval_def]; exact hpA⟩

theorem trace_isIntegral_of_preserves_lattice : ∀ (E : Type) [Field E] [NumberField E] (r : ℕ)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (A : Matrix (Fin r) (Fin r) E), Λ.FG →
    Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → (∀ x ∈ Λ, A *ᵥ x ∈ Λ) →
    IsIntegral ℤ A.trace := by
  intro E _ _ r Λ A hfg hsp hA
  exact isIntegral_trace_of_isIntegral A (isIntegral_of_preserves_lattice Λ A hfg hsp hA)

end GlobalTheory.LatTrace

end
end

section

open NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.projective_of_surjective_ker_le_smul : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k), Function.Surjective π → RingHom.ker π = Ideal.span {(p : Λ)} → (p : Λ) ^ 2 = 0 → (∀ x : Λ, (p : Λ) * x = 0 → x ∈ Ideal.span {(p : Λ)}) → ∀ (M : Type 1) [AddCommGroup M] [Module Λ M] [Module (Λ ⊗[ℤ] 𝓞 F) M] [IsScalarTower Λ (Λ ⊗[ℤ] 𝓞 F) M], Module.Finite Λ M → Module.Free Λ M → ∀ (N : Type 1) [AddCommGroup N] [Module (k ⊗[ℤ] 𝓞 F) N] (f : M →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ (𝓞 F))).toRingHom] N), Function.Surjective f → (∀ m, f m = 0 → m ∈ (RingHom.ker π) • (⊤ : Submodule Λ M)) → Module.Projective (k ⊗[ℤ] 𝓞 F) N := by
  first | exact @GlobalTheory.FlatLift.projective_reduction_of_flat_lift | exact GlobalTheory.FlatLift.projective_reduction_of_flat_lift | (intros; apply GlobalTheory.FlatLift.projective_reduction_of_flat_lift <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.FixNormCls

variable {E : Type} [Field E] [NumberField E]

def ord (P : HeightOneSpectrum (𝓞 E)) (x : E) : ℤ :=
  FractionalIdeal.count E P (FractionalIdeal.spanSingleton (𝓞 E)⁰ x)

def primeMap (τ : E ≃+* E) (P : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) where
  asIdeal := P.asIdeal.comap (RingOfIntegers.mapRingEquiv τ.symm : 𝓞 E →+* 𝓞 E)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply P.ne_bot
    rw [eq_bot_iff] at h ⊢
    intro x hx
    have : (RingOfIntegers.mapRingEquiv τ) x ∈
        P.asIdeal.comap (RingOfIntegers.mapRingEquiv τ.symm : 𝓞 E →+* 𝓞 E) := by
      rw [Ideal.mem_comap]
      convert hx using 1
      exact (RingOfIntegers.mapRingEquiv τ).symm_apply_apply x
    have h2 := h this
    rw [Submodule.mem_bot, map_eq_zero_iff _ (RingOfIntegers.mapRingEquiv τ).injective] at h2
    rw [Submodule.mem_bot]; exact h2

theorem mem_primeMap (τ : E ≃+* E) (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E) :
    a ∈ (primeMap τ P).asIdeal ↔ RingOfIntegers.mapRingEquiv τ.symm a ∈ P.asIdeal :=
  Ideal.mem_comap

theorem ord_zero (P : HeightOneSpectrum (𝓞 E)) : ord P (0 : E) = 0 := by
  simp [ord, FractionalIdeal.count_zero]

theorem ord_mul (P : HeightOneSpectrum (𝓞 E)) {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord P (x * y) = ord P x + ord P y := by
  unfold ord
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
  exact FractionalIdeal.count_mul E P (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)

theorem ord_inv (P : HeightOneSpectrum (𝓞 E)) (x : E) : ord P x⁻¹ = - ord P x := by
  unfold ord
  rw [← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv]

theorem ord_div (P : HeightOneSpectrum (𝓞 E)) {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord P (x / y) = ord P x - ord P y := by
  rw [div_eq_mul_inv, ord_mul P hx (inv_ne_zero hy), ord_inv, sub_eq_add_neg]

theorem ord_one (P : HeightOneSpectrum (𝓞 E)) : ord P (1 : E) = 0 := by
  simp [ord, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]

theorem ord_primeMap (τ : E ≃+* E) (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    ord (primeMap τ P) (τ x) = ord P x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ord_zero]
  exact GlobalTheory.OrdTransport.count_spanSingleton_ringEquiv (𝓞 E) E (RingOfIntegers.mapRingEquiv τ) τ
    (fun a => rfl) P (primeMap τ P)
    (fun a => by
      rw [mem_primeMap]
      have : RingOfIntegers.mapRingEquiv τ.symm (RingOfIntegers.mapRingEquiv τ a) = a :=
        RingOfIntegers.ext (by change τ.symm (τ (a : E)) = (a : E); exact τ.symm_apply_apply _)
      rw [this]) x hx

theorem primeMap_primeMap (τ : E ≃+* E) (hτ : ∀ x, τ (τ x) = x) (P : HeightOneSpectrum (𝓞 E)) :
    primeMap τ (primeMap τ P) = P := by
  ext a
  rw [mem_primeMap, mem_primeMap]
  have : RingOfIntegers.mapRingEquiv τ.symm (RingOfIntegers.mapRingEquiv τ.symm a) = a := by
    apply RingOfIntegers.ext
    change τ.symm (τ.symm (a : E)) = (a : E)
    rw [RingEquiv.symm_apply_eq, RingEquiv.symm_apply_eq, hτ]
  rw [this]

end GlobalTheory.FixNormCls
end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.exists_prime_natCast_mem_pow_of_ringHom' : ∀ (F H : Type) [Field F] [NumberField F] [Field H] [NumberField H] (f : F →+* H) (w : HeightOneSpectrum (𝓞 F)) (p n : ℕ), (p : 𝓞 F) ∈ w.asIdeal ^ n → ∃ P : Ideal (𝓞 H), P.IsPrime ∧ P ≠ ⊥ ∧ (p : 𝓞 H) ∈ P ^ n := by
  first | exact @GlobalTheory.CMModel.exists_prime_natCast_mem_pow_of_ringHom | exact GlobalTheory.CMModel.exists_prime_natCast_mem_pow_of_ringHom | (intros; apply GlobalTheory.CMModel.exists_prime_natCast_mem_pow_of_ringHom <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

namespace GlobalTheory.QSA

theorem infinitePlace_completion_nhdsNE_neBot : ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), (𝓝[≠] (0 : w.Completion)).NeBot := by
  intro F _ _ w
  have hiso := InfinitePlace.Completion.isometry_extensionEmbedding w
  have h2 : ‖(2 : w.Completion)‖ = 2 := by
    have := (AddMonoidHomClass.isometry_iff_norm _).1 hiso (2 : w.Completion)
    rw [← this, map_ofNat]; simp
  letI : NontriviallyNormedField w.Completion :=
    { (inferInstance : NormedField w.Completion) with
      non_trivial := ⟨2, by rw [h2]; norm_num⟩ }
  exact NormedField.nhdsNE_neBot (0 : w.Completion)
end GlobalTheory.QSA
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory

theorem cm_type_normSq_prod_eq_abs_norm (E : Type) [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (d : E) :
    ‖∏ τ : Ψ, τ.1 d‖ ^ 2 = |((Algebra.norm ℚ d : ℚ) : ℝ)| := by
  classical
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
    intro τ; ext x; simp [ComplexEmbedding.conjugate_coe_eq]
  have h1 : ((Algebra.norm ℚ d : ℚ) : ℂ) = ∏ τ : E →+* ℂ, τ d := by
    have := Algebra.norm_eq_prod_embeddings ℚ ℂ d
    rw [eq_ratCast] at this
    rw [this]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)
  have hcompl : ∏ τ ∈ Ψᶜ, τ d = ∏ τ ∈ Ψ, (starRingEnd ℂ) (τ d) := by
    refine Finset.prod_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [Finset.mem_compl, Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at hτ ⊢
      rw [hΨ, hcc]; exact hτ
    · intro τ hτ
      simp only [Finset.mem_compl, Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at hτ ⊢
      exact (hΨ τ).mp hτ
    · intro τ _; exact hcc τ
    · intro τ _; exact hcc τ
    · intro τ _; simp [ComplexEmbedding.conjugate_coe_eq]
  have hsub : ∏ τ : Ψ, τ.1 d = ∏ τ ∈ Ψ, τ d := Finset.prod_coe_sort Ψ (fun τ => τ d)
  set P := ∏ τ ∈ Ψ, τ d with hP
  have h2 : ((Algebra.norm ℚ d : ℚ) : ℂ) = ((Complex.normSq P : ℝ) : ℂ) := by
    rw [h1, ← Finset.prod_mul_prod_compl Ψ, hcompl, ← map_prod, Complex.mul_conj]
  have h3 : ((Algebra.norm ℚ d : ℚ) : ℝ) = Complex.normSq P := by
    have := h2
    rw [show ((Algebra.norm ℚ d : ℚ) : ℂ) = (((Algebra.norm ℚ d : ℚ) : ℝ) : ℂ) by push_cast; rfl] at this
    exact_mod_cast this
  rw [hsub, h3, Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]

end GlobalTheory
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_finite_free_etale_lift_of_quotient_etale : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ f ∈ maximalIdeal R, ∀ (E : Type) [CommRing E] [Algebra (R ⧸ Ideal.span {f}) E] [Module.Finite (R ⧸ Ideal.span {f}) E] [Algebra.Etale (R ⧸ Ideal.span {f}) E], ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B), Module.Finite R B ∧ Module.Free R B ∧ Algebra.Etale R B ∧ Nonempty ((B ⧸ (Ideal.span {f}).map (algebraMap R B)) ≃ₐ[R ⧸ Ideal.span {f}] E) := by
  first | exact @GlobalTheory.EtaleLiftQuot.exists_finite_free_etale_lift | exact GlobalTheory.EtaleLiftQuot.exists_finite_free_etale_lift | (intros; apply GlobalTheory.EtaleLiftQuot.exists_finite_free_etale_lift <;> assumption)
end

section

open IsLocalRing GlobalTheory.FormalOrigin

theorem _root_.GlobalTheory.T.mvPowerSeries_isAdicComplete_map_C_of_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ n : ℕ, IsAdicComplete (I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R)) (MvPowerSeries (Fin n) R) := by
  first | exact @GlobalTheory.PowerSeriesComplete.isAdicComplete_map_C | exact GlobalTheory.PowerSeriesComplete.isAdicComplete_map_C | (intros; apply GlobalTheory.PowerSeriesComplete.isAdicComplete_map_C <;> assumption)
end
