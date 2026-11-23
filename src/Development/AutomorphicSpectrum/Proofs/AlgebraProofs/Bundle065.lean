module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle005
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle061
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle057
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle017
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenLocalBasisLogNorm
public import Development.WeilBound.CoreStatements.SesquilinearFractions.DBlock
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CmTypeValuationEmbedding
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle031
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle063
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle059
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle006
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.ConeBallLogGapIntegral
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle034
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle064
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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

@[expose] public section

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

theorem _root_.GlobalTheory.T.lattice_family_model_comparison : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg x) c) _) ≤ (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₂ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FamGood2.main | exact GlobalTheory.CompanionTheory.Ar.FamGood2.main | (intros; apply GlobalTheory.CompanionTheory.Ar.FamGood2.main <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.formal_data_base_change : ∀ (R R₂ : Type) [CommRing R] [CommRing R₂] (f : R →+* R₂) (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R₂ d O), IsMapOf f B B₂ → (∀ a, rho B₂ a = (rho B a).map f ∧ bil (B₂.ad a) 1 1 = (bil (B.ad a) 1 1).map f) ∧ bil B₂.sy 1 1 = (bil B.sy 1 1).map f ∧ ∀ p, hw B₂ p = (hw B p).map f ∧ am B₂ p = (am B p).map f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.map_mats_baseChange | exact GlobalTheory.CompanionTheory.Ar.Conj.map_mats_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.map_mats_baseChange <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.LmuDeg

theorem dot_bijective (K : Type) [Field K] (d : ℕ) :
    Function.Bijective
      (dotProductBilin K K : (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] K) := by
  have hi : Function.Injective
      (dotProductBilin K K : (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] K) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    funext r
    have := LinearMap.congr_fun hx (Pi.single r 1)
    simpa [dotProductBilin_apply_apply] using this
  refine ⟨hi, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    simp [Subspace.dual_finrank_eq])).1 hi

noncomputable def endAct {K : Type} [Field K] {O : Type} [CommRing O] {d : ℕ}
    (ρ : O →+* Matrix (Fin d) (Fin d) K) : O →+* Module.End K (Fin d → K) where
  toFun a := Matrix.toLin' (ρ a)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' a b := by simp [Matrix.toLin'_mul, Module.End.mul_eq_comp]
  map_zero' := by simp
  map_add' a b := by simp

theorem isHom_lie {K : Type} [Field K] {C : ACurve K} {p : ℕ} {O : Type} [CommRing O] [StarRing O]
    {d : ℕ} (D : ConjData C p O d) (a : O) : IsHom C D.lie D.lie (endAct D.ρ a) := by
  intro i x hx
  obtain ⟨y, hy, rfl⟩ := (D.hodge.2.2.2.2 i x).1 hx
  have h2 : (D.ρH a y).1 ∈ D.lie i :=
    (D.hodge.2.2.2.2 i _).2 ⟨_, D.ρH_hom a i y hy, rfl⟩
  rw [D.ρH_fst] at h2
  simpa [endAct] using h2

theorem lmuNum_nonneg_of_conjData : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (O k S T : Type) [CommRing O] [StarRing O] [Field k] [Algebra k K] [Fintype S] [Fintype T] (χ : S → (O →+* k)) (d : ℕ) (D : ConjData C p O d) (ι κ : T → S) (j q : ℕ) (μ : T → ℕ → ℝ) (W L : T → ℕ → Submodule K (Fin d → K)), 2 < p → IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → Function.Bijective (Sum.elim ι κ) → (∀ τ a, χ (κ τ) a = χ (ι τ) (star a)) → 1 ≤ j → 1 ≤ q → (∀ τ, W τ 0 = ⊥) → (∀ τ, L τ 0 = ⊥) → (∀ τ, W τ j = (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ (ι τ) a)))) → (∀ τ, L τ q = (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ (κ τ) a)))) → GapCond p j q μ → 0 ≤ lmuNum j q μ (fun τ i => (subDeg C D.lie (W τ i) : ℝ)) (fun τ i => (subDeg C D.lie (L τ i) : ℝ)) := by
  intro K _ C p _ _ O k S T _ _ _ _ _ _ χ d D ι κ j q μ W L hp hs hc hbij hconj hj hq hW0 hL0 hWj hLq hgap
  classical
  obtain ⟨hbot, W₀, hW₀⟩ := GlobalTheory.T.sub_degree_bot_and_max_exists K C (Fin d → K) D.lie D.lie_bun
  obtain ⟨he0, hC2⟩ := GlobalTheory.T.lie_sub_degree_bound_by_dual K C p O d D hp
  have hsplit : deg C D.lie = ∑ s, subDeg C D.lie
      (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) :=
    GlobalTheory.T.degree_sum_eigen_sub_degrees K C (Fin d → K) D.lie O k S χ hs hc (endAct D.ρ) D.lie_bun (isHom_lie D)
  have hdual : deg C (dotDual C D.lie) = - deg C D.lie :=
    (GlobalTheory.CompanionTheory.Ar.Crv.DegDual.deg_dual K C (Fin d → K) (Fin d → K) D.lie (dotProductBilin K K)
      D.lie_bun (dot_bijective K d)).2.1
  have hC1 : ∀ τ, subDeg C D.lie (W τ j) = subDeg C D.lie (L τ q) := by
    intro τ
    rw [hWj, hLq]
    exact GlobalTheory.T.conjugate_eigen_sub_degree_eq K C p O k S χ d D hs hc (ι τ) (κ τ) (hconj τ)
  have hsum : deg C D.lie = 2 * ∑ τ, subDeg C D.lie (W τ j) := by
    rw [hsplit, ← (Equiv.ofBijective _ hbij).sum_comp, Fintype.sum_sum_type, two_mul]
    simp only [Equiv.ofBijective_apply, Sum.elim_inl, Sum.elim_inr]
    congr 1
    · exact Finset.sum_congr rfl fun τ _ => by rw [hWj]
    · exact Finset.sum_congr rfl fun τ _ => by rw [hC1, hLq]
  refine GlobalTheory.CompanionTheory.Ar.Crv.Chain.lmuNum_nonneg T p j q μ _ _ (subDeg C D.lie W₀ : ℝ)
    (deg C (dotDual C D.lie) : ℝ) hp hj hq hgap ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro τ; simp [hW0, hbot]
  · intro τ; simp [hL0, hbot]
  · intro τ i _; exact_mod_cast hW₀ _
  · intro τ i _; exact_mod_cast hW₀ _
  · intro τ; exact_mod_cast hC1 τ
  · rw [hdual, hsum]; push_cast; ring
  · exact_mod_cast hC2 W₀
  · exact_mod_cast he0

end GlobalTheory.CompanionTheory.Ar.Crv.LmuDeg
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.stable_hopf_order_basis_colength : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) (∏ i, s i) → ∀ j : ℕ, HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : flagSub b j → N))) χ) (∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), s i) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_colength | exact GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_colength | (intros; apply GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_colength <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.stable_hopf_order_basis_lengths : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal) (r : NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) r → ∏ i, s i ≤ r := by
  first | exact @GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_lengths | exact GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_lengths | (intros; apply GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_lengths <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_quotient : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → ∀ c' c : R, idealX AA.carrier K t τ = Ideal.span {c'} → idealX AA.carrier K t (τ ^ p) = Ideal.span {c} → v (algebraMap R C c') ^ p < v (algebraMap R C c) → c ∈ idealD p AA.carrier K t (τ ^ p) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_quotient | exact GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_quotient | (intros; apply GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_quotient <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.eigen_local_basis_log_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : Nat.Primes) (K : Type) [Field K] [CharZero K] (j : K →+* ℂ_[ℓ]) (V : Subring K) (U : Type) [AddCommGroup U] [Module K U] (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K) (I J : Type) [Fintype I] [Fintype J] (u : I → U) (u' : J → U) (f : ℕ) (b : Fin f → 𝓞 E) (δ : K), (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ V) → Nat.card (E →+* K) = Module.finrank ℚ E → IsLocBasis (Algebra.adjoin ℤ {H.w0}) ℓ b → (∀ a, ρ H.rt (u a) = σ (H.rt : E) • u a) → (∀ a, ρ H.rt (u' a) = -σ (H.rt : E) • u' a) → LinearIndependent K (Sum.elim (fun q : I × Fin f => ρ (b q.2) (u q.1)) (fun q : J × Fin f => ρ (b q.2) (u' q.1))) → δ ≠ 0 → Real.log ‖j δ‖ = logIdeal ((j.comp σ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (σ (H.rt : E))‖ → LinearIndependent K (fun a => δ • HT.eigProj ρ σ (u a)) ∧ Submodule.span V (Set.range (Sum.elim (fun q : I × Fin f => ρ (b q.2) (u q.1)) (fun q : J × Fin f => ρ (b q.2) (u' q.1)))) ⊓ (HT.eigSp ρ σ).restrictScalars V = Submodule.span V (Set.range fun a => δ • HT.eigProj ρ σ (u a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.EigSubLat.eigSub_span | exact GlobalTheory.CompanionTheory.Ar.Fl.EigSubLat.eigSub_span | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.EigSubLat.eigSub_span <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem orthogonalBlock_gram_det_log_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La) (ℓ : Nat.Primes), IsLocBasis (𝓞 E) ℓ x → (∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) → (gramE D (x ∘ Sum.inr)).det ≠ 0 ∧ ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D (x ∘ Sum.inr)).det‖ = -(q : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) :=
  @PositivityTheory.Xgf.local_basis_gram_det_log_norm

end GlobalTheory.CompanionTheory.Ar.Fl
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.cm_type_valuation_embedding : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (rk : (E →+* C) → ℕ) (p q : ℕ) (ν : Valuation C NNReal), ν.Integers V → (∃ ℓ : C, 0 < ν ℓ ∧ ν ℓ < 1) → (∀ (s : E →+* C) (a : 𝓞 E), s (a : E) ∈ (algebraMap V C).range) → Nat.card (E →+* C) = Module.finrank ℚ E → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → ∃ γ : C, γ ≠ 0 ∧ ∀ (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)) (HV : Submodule V (W × Module.Dual C W)) (Lie : Submodule V W) (x : Fin (p + q) → W × Module.Dual C W) (v : Fin p → W) (w : Fin q → W) (u : Fin (p + q) → W × Module.Dual C W) (A : Matrix (Fin (p + q)) (Fin (p + q)) C), (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → HV.map ((LinearMap.fst C W (Module.Dual C W)).restrictScalars V) = Lie → (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap V C).range) → HT.IsFreeOn ρH HV x → (∀ s, Module.finrank C (HT.eigSp ρ s) = rk s) → LinearIndependent C v → Submodule.span V (Set.range v) = HT.eigSub ρ σ Lie → LinearIndependent C w → Submodule.span V (Set.range w) = HT.eigSub ρ σ' Lie → IsAdapted ρH σ v w u → LinearIndependent C (fun i => ∑ j, A i j • u j) → Submodule.span V (Set.range fun i => ∑ j, A i j • u j) = HT.eigQuot ρH σ HV → ∃ ε : Vˣ, A.det = algebraMap V C ε * γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.det_adapted_eq_unit_mul_const | exact GlobalTheory.CompanionTheory.Ar.Flat.det_adapted_eq_unit_mul_const | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.det_adapted_eq_unit_mul_const <;> assumption)
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.ae_fibre_points_card_eq_degree : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
    ∀ᵐ π : Fin (e + 1) → Fin n → ℂ, (fibrePts (coneSet h W) π).encard = δ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.ae_fibre_points_card_eq_degree | exact GlobalTheory.CompanionTheory.Relay.ae_fibre_points_card_eq_degree | (intros; apply GlobalTheory.CompanionTheory.Relay.ae_fibre_points_card_eq_degree <;> assumption)
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.CompanionTheory.Relay.cone_ball_log_gap_integral : ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) f → linForm u ∉ W →
    ∫⁻ y in coneBall h W, logGap h u y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) < ⊤ ∧
      (∫⁻ y in coneBall h W, logGap h u y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))).toReal =
        Real.log (h.norm u) * ((Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) (coneBall h W)).toReal -
          ∫ y in coneBall h W, fsLog h u (h.pointOf y) ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
  first | exact @ModelDimension.integral_coneBall_log_gap_eq | exact ModelDimension.integral_coneBall_log_gap_eq
end

section


theorem _root_.GlobalTheory.T.flag_further_term_independent_statement : GroundTheory.Heights₂.Heights.NumbersDVR.flagFurtherTerm_independent.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.flag_further_term_independent | exact GlobalTheory.CompanionTheory.Ar.Num.flag_further_term_independent | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.flag_further_term_independent <;> assumption)
end
