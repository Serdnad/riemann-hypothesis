module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle594
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle160
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsConjPrimeEqDualLabel
public import Formalism.LocalToGlobal.KernelLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle187
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle180
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMatrixOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle156
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle174
import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.FinitelyGeneratedModPow
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Bundle004
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer
import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
open Pointwise

namespace GlobalTheory

theorem trivial_on_ext_of_frob_eq_normChar : ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] (η : HChar K), UpperTheory.V.Published.IsNormChar M η → ∀ χ : _root_.Formalism.ConjugateSelfDual.G K Ω →* ℂˣ, IsOpen (χ.ker : Set (_root_.Formalism.ConjugateSelfDual.G K Ω)) → (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∀ (A : ValuationSubring Ω) (σ : _root_.Formalism.ConjugateSelfDual.G K Ω), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v → IsFrob A (normV v) σ → χ σ = η.val v) → ∀ g : _root_.Formalism.ConjugateSelfDual.G K Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) → χ g = 1 := by
  intro Ω _ K _ _ _ _ M _ _ _ _ _ _ η hη χ hχo hχ g hg
  classical
  let r : _root_.Formalism.ConjugateSelfDual.G M Ω →* _root_.Formalism.ConjugateSelfDual.G K Ω := AlgEquiv.restrictScalarsHom K
  have hr : Continuous r := GlobalTheory.WeilRes.continuous_res
  let u : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 K) := fun w => w.under (𝓞 K)
  have hu : ∀ w : HeightOneSpectrum (𝓞 M), w.asIdeal.LiesOver (u w).asIdeal := fun w => ⟨rfl⟩
  have hS := Filter.eventually_cofinite.1 hχ
  have hT₁ := Filter.eventually_cofinite.1 hη.2.2
  let T : Set (HeightOneSpectrum (𝓞 M)) :=
    {w | ¬ ∀ f : ℕ, normV w = normV (w.under (𝓞 K)) ^ f → η.val (w.under (𝓞 K)) ^ f = 1} ∪
      u ⁻¹' {v | ¬ ∀ (A : ValuationSubring Ω) (σ : _root_.Formalism.ConjugateSelfDual.G K Ω), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v → IsFrob A (normV v) σ → χ σ = η.val v}
  have hT : T.Finite := hT₁.union (hS.preimage' (f := u) fun v _ => by
    have := v.isMaximal
    refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)).preimage
      (f := fun w : HeightOneSpectrum (𝓞 M) => w.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    rintro w rfl
    exact ⟨w.isPrime, hu w⟩)
  have hdense := GlobalTheory.Published.chebotarevDegreeOne'.dense (F := M) (Ω := Ω) hT
  let H : Subgroup (_root_.Formalism.ConjugateSelfDual.G M Ω) := (χ.comp r).ker
  have hHc : IsClosed (H : Set (_root_.Formalism.ConjugateSelfDual.G M Ω)) := H.isClosed_of_isOpen (by exact hχo.preimage hr)
  have hsub : {σ : _root_.Formalism.ConjugateSelfDual.G M Ω | ∃ w : HeightOneSpectrum (𝓞 M), w ∉ T ∧ w.asIdeal.inertiaDeg ℤ = 1 ∧
      ∃ B : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver B w ∧ IsFrob B (normV w) σ} ⊆ H := by
    rintro σ ⟨w, hw, hd, B, hB, hσ⟩
    have hw1 : ∀ f : ℕ, normV w = normV (u w) ^ f → η.val (u w) ^ f = 1 := by
      by_contra h; exact hw (Or.inl h)
    have hw2 : ∀ (A : ValuationSubring Ω) (σ : _root_.Formalism.ConjugateSelfDual.G K Ω), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A (u w) → IsFrob A (normV (u w)) σ →
        χ σ = η.val (u w) := by
      by_contra h; exact hw (Or.inr h)
    have hp : (Ideal.absNorm w.asIdeal).Prime :=
      ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified M).1 w).2 hd
    have hn : Ideal.absNorm (u w).asIdeal = Ideal.absNorm w.asIdeal := by
      haveI := hu w
      have h := Ideal.absNorm_pow_inertiaDeg (u w).asIdeal w.asIdeal
      have h1 := Nat.Prime.eq_one_of_pow (h ▸ hp)
      rw [h1, pow_one] at h
      exact h
    have hnv : normV w = normV (u w) := by
      simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn
      exact hn.symm
    have hBv : _root_.Formalism.ConjugateSelfDual.IsPlaceOver B (u w) := fun x => by
      have e : algebraMap K Ω (x : K) = algebraMap M Ω ((algebraMap (𝓞 K) (𝓞 M) x : 𝓞 M) : M) := by
        rw [IsScalarTower.algebraMap_apply K M Ω]; rfl
      rw [e]
      exact hB _
    have hrσ : IsFrob B (normV (u w)) (r σ) := by
      refine ⟨?_, fun x hx => ?_⟩
      · have h : σ • B = B := hσ.1
        show (σ.restrictScalars K) • B = B
        ext x
        conv_rhs => rw [← h]
        rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
          ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
        rfl
      · rw [← hnv]; exact hσ.2 x hx
    have h1 : χ (r σ) = η.val (u w) := hw2 B (r σ) hBv hrσ
    have h2 : η.val (u w) ^ 1 = 1 := hw1 1 (by rw [pow_one]; exact hnv)
    rw [pow_one] at h2
    show χ (r σ) = 1
    rw [h1, h2]
  have hall : ∀ τ : _root_.Formalism.ConjugateSelfDual.G M Ω, τ ∈ H := fun τ => hHc.closure_subset_iff.2 hsub (hdense τ)
  let τ : _root_.Formalism.ConjugateSelfDual.G M Ω := { g.toRingEquiv with commutes' := hg }
  have hτ : r τ = g := AlgEquiv.ext fun _ => rfl
  have := hall τ
  show χ g = 1
  rw [← hτ]
  exact this

end GlobalTheory
end

section

namespace GlobalTheory.SplitLabel

open Matrix

section Alg

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem smul_mulVec_congr (ε : R) (M : Matrix n n R) {x y : n → R} (h : ε • x = ε • y) :
    ε • M *ᵥ x = ε • M *ᵥ y := by
  rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, h]

omit [DecidableEq n] in
theorem smul_mulVec_mat (ε : R) {A B B' : Matrix n n R} (h : ε • (A * B) = ε • B') (x : n → R) :
    ε • A *ᵥ (B *ᵥ x) = ε • B' *ᵥ x := by
  rw [Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, h, Matrix.smul_mulVec]


omit [DecidableEq n] in
theorem stab_of_bases (ε : R) (hε : ε * ε = ε) (Λ Z : Set (n → R)) {A B B' : Matrix n n R}
    (h : ε • (A * B) = ε • B')
    (h1 : ∀ z ∈ Z, ε • B *ᵥ z ∈ Λ) (h2 : ∀ y ∈ Λ, ∃ z ∈ Z, ε • y = ε • B *ᵥ z)
    (h1' : ∀ z ∈ Z, ε • B' *ᵥ z ∈ Λ) (h2' : ∀ y ∈ Λ, ∃ z ∈ Z, ε • y = ε • B' *ᵥ z) :
    (∀ y ∈ Λ, ε • A *ᵥ y ∈ Λ) ∧ ∀ y ∈ Λ, ∃ z ∈ Λ, ε • y = ε • A *ᵥ z := by
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨z, hz, e⟩ := h2 y hy
    rw [smul_mulVec_congr ε A e, smul_mulVec_mat ε h]
    exact h1' z hz
  · obtain ⟨z, hz, e⟩ := h2' y hy
    refine ⟨_, h1 z hz, ?_⟩
    rw [e, ← smul_mulVec_mat ε h]
    apply smul_mulVec_congr
    rw [smul_smul, hε]

theorem stab_of_div (ε : R) (Λ Z : Set (n → R)) {A B B' M M' N b : Matrix n n R}
    (t t' : n → R) (h : ε • (A * B) = ε • B') (hN : N * (A * M) = 1) (hb : b = N * M')
    (hΛ : ∀ y ∈ Λ, ε • y ∈ Λ)
    (hu : ∀ z ∈ Z, ∃ w ∈ Z, ε • (fun i => t' i * z i) = ε • fun i => t i * w i)
    (hu' : ∀ z ∈ Z, ∃ w ∈ Z, ε • (fun i => t i * z i) = ε • fun i => t' i * w i)
    (h3 : ∀ y ∈ Λ, ∃ z ∈ Z, ε • M *ᵥ y = ε • B *ᵥ fun i => t i * z i)
    (h4 : ∀ z ∈ Z, ∃ y ∈ Λ, ε • M *ᵥ y = ε • B *ᵥ fun i => t i * z i)
    (h3' : ∀ y ∈ Λ, ∃ z ∈ Z, ε • M' *ᵥ y = ε • B' *ᵥ fun i => t' i * z i)
    (h4' : ∀ z ∈ Z, ∃ y ∈ Λ, ε • M' *ᵥ y = ε • B' *ᵥ fun i => t' i * z i) :
    (∀ y ∈ Λ, ε • b *ᵥ y ∈ Λ) ∧ ∀ y ∈ Λ, ∃ z ∈ Λ, ε • y = ε • b *ᵥ z := by
  have key : ∀ y y' : n → R, ε • M' *ᵥ y' = ε • A *ᵥ (M *ᵥ y) → ε • b *ᵥ y' = ε • y := by
    intro y y' e
    rw [hb, ← Matrix.mulVec_mulVec, smul_mulVec_congr ε N e, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, hN, Matrix.one_mulVec]
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨z, hz, e⟩ := h3' y hy
    obtain ⟨w, hw, ew⟩ := hu z hz
    obtain ⟨y', hy', e'⟩ := h4 w hw
    rw [key y' y]
    · exact hΛ y' hy'
    · rw [e, smul_mulVec_congr ε B' ew, smul_mulVec_congr ε A e', smul_mulVec_mat ε h]
  · obtain ⟨z, hz, e⟩ := h3 y hy
    obtain ⟨w, hw, ew⟩ := hu' z hz
    obtain ⟨y', hy', e'⟩ := h4' w hw
    refine ⟨y', hy', (key y y' ?_).symm⟩
    rw [e', smul_mulVec_congr ε A e, smul_mulVec_mat ε h, smul_mulVec_congr ε B' ew]

omit [DecidableEq n] in
theorem smul_mul_congr_left (ε : R) {X Y : Matrix n n R} (h : ε • X = ε • Y) (Z : Matrix n n R) :
    ε • (X * Z) = ε • (Y * Z) := by
  rw [← Matrix.smul_mul, h, Matrix.smul_mul]

omit [DecidableEq n] in
theorem smul_mul_congr_right (ε : R) {X Y : Matrix n n R} (h : ε • X = ε • Y) (Z : Matrix n n R) :
    ε • (Z * X) = ε • (Z * Y) := by
  rw [← Matrix.mul_smul, h, Matrix.mul_smul]

end Alg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem change_unif {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D)
    (ϖ ϖ' : 𝓞 D.host.E) (k : Fin V.rank → ℤ) (he : IsIdemAt e P) (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2)
    (h1' : ϖ' ∈ P.asIdeal) (h2' : ϖ' ∉ P.asIdeal ^ 2)
    (z : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) (hz : IntVec z) :
    ∃ w, IntVec w ∧ finPart D e • (fun i => finPart D (incA D ((ϖ' : D.host.E) ^ k i)) * z i) =
      finPart D e • fun i => finPart D (incA D ((ϖ : D.host.E) ^ k i)) * w i := by
  have hε : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1.1]
  have h0 : (ϖ : D.host.E) ≠ 0 := by
    intro h
    have : ϖ = 0 := by exact_mod_cast h
    exact h2 (this ▸ zero_mem _)
  refine ⟨fun i => finPart D e * finPart D (incA D ((ϖ' : D.host.E) ^ k i / (ϖ : D.host.E) ^ k i)) * z i,
    fun i => GlobalTheory.SplitLatBasis.mul_mem_intAE D ((GlobalTheory.T.completedLattice_integrality V).2.1 P e ϖ ϖ' he h1 h2 h1' h2' (k i)) (hz i), ?_⟩
  funext i
  have e1 : finPart D (incA D ((ϖ' : D.host.E) ^ k i)) = finPart D (incA D ((ϖ : D.host.E) ^ k i)) *
      finPart D (incA D ((ϖ' : D.host.E) ^ k i / (ϖ : D.host.E) ^ k i)) := by
    rw [← map_mul, ← map_mul, mul_div_cancel₀ _ (zpow_ne_zero _ h0)]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [e1]
  linear_combination (-(finPart D (incA D ((ϖ : D.host.E) ^ k i)) *
      finPart D (incA D ((ϖ' : D.host.E) ^ k i / (ϖ : D.host.E) ^ k i)) * z i)) * hε

theorem split_label : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ ϖ' : 𝓞 D.host.E) (d : List ℤ) (α α' : GA D V), IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → Formalism.L2.Theta.SuppAt e V α → Formalism.L2.Theta.SuppAt e V α' → DivAt V e (ϖ : D.host.E) d α → DivAt V e (ϖ' : D.host.E) d α' → ∃ a ∈ locPart V (KsphC V ∅) e, ∃ b ∈ locPart V (KsphC V ∅) e, α' = a * α * b := by
  intro D V P e ϖ ϖ' d α α' he h1 h2 h1' h2' hα hα' hd hd'
  obtain ⟨-, B, hB1, hB2, hB3, hB4⟩ := hd
  obtain ⟨-, B', hB1', hB2', hB3', hB4'⟩ := hd'
  have hε : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1.1]
  obtain ⟨C, hBC, hCB⟩ := (GlobalTheory.T.completedLattice_integrality V).2.2 _ B hε fun y hy => (hB2 y hy).imp fun _ h => h.2
  obtain ⟨C', hBC', hCB'⟩ := (GlobalTheory.T.completedLattice_integrality V).2.2 _ B' hε fun y hy => (hB2' y hy).imp fun _ h => h.2
  have hinv : finPart D e • ((B' * C) * (B * C')) = finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) := by
    have := smul_mul_congr_right _ (smul_mul_congr_left _ hCB C') B'
    rw [Matrix.one_mul, hBC'] at this
    rw [← this]
    simp only [Matrix.mul_assoc]
  obtain ⟨a, haS, ha⟩ := GlobalTheory.T.exists_adelic_unitary_split_place_component V e he.1 _ _ hinv
  have hAB : finPart D e • (finMat D.sp.cm.sig V.gram a * B) = finPart D e • B' := by
    rw [smul_mul_congr_left _ ha B, Matrix.mul_assoc, smul_mul_congr_right _ hCB B', Matrix.mul_one]
  have hs := stab_of_bases (finPart D e) hε {y | y ∈ LamHat V} {z | IntVec z} hAB
    (fun z hz => hB1 z hz) (fun y hy => hB2 y hy) (fun z hz => hB1' z hz) (fun y hy => hB2' y hy)
  have haK : a ∈ KsphC V ∅ := GlobalTheory.T.mem_hyperspecial_of_split_place_stabilizer V e a he.1 haS hs.1 hs.2
  obtain ⟨hf1, hf2, -⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e (e + cA D e) (Or.inl ⟨he, rfl⟩)
  obtain ⟨L, hL⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 _ hf1 hf2).1
  have hbS : Formalism.L2.Theta.SuppAt e V ((a * α)⁻¹ * α') :=
    (hL _).1 (L.mul_mem (L.inv_mem (L.mul_mem ((hL _).2 haS) ((hL _).2 hα))) ((hL _).2 hα'))
  have hN : finMat D.sp.cm.sig V.gram (a * α)⁻¹ *
      (finMat D.sp.cm.sig V.gram a * finMat D.sp.cm.sig V.gram α) = 1 := by
    rw [← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, ← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, inv_mul_cancel,
      Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one]
  have ht := stab_of_div (finPart D e) {y | y ∈ LamHat V} {z | IntVec z}
    (fun i => finPart D (incA D ((ϖ : D.host.E) ^ d.getD i.1 0)))
    (fun i => finPart D (incA D ((ϖ' : D.host.E) ^ d.getD i.1 0))) hAB hN
    (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul _ _ (a * α)⁻¹ α')
    (fun y hy => (GlobalTheory.T.completedLattice_integrality V).1 _ (GlobalTheory.AdIdem.idempotent_mem_intAE D _ hε) y hy)
    (fun z hz => change_unif V P e ϖ ϖ' _ he h1 h2 h1' h2' z hz)
    (fun z hz => change_unif V P e ϖ' ϖ _ he h1' h2' h1 h2 z hz)
    (fun y hy => hB3 y hy) (fun z hz => hB4 z hz) (fun y hy => hB3' y hy) (fun z hz => hB4' z hz)
  have hbK : (a * α)⁻¹ * α' ∈ KsphC V ∅ := GlobalTheory.T.mem_hyperspecial_of_split_place_stabilizer V e _ he.1 hbS ht.1 ht.2
  exact ⟨a, ⟨haK, haS⟩, _, ⟨hbK, hbS⟩, by rw [mul_inv_cancel_left]⟩

end GlobalTheory.SplitLabel
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.elementaryDivisors_conjPrime_eq_dualLabel : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (d : List ℤ) (α : GA D V), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → DivAt V e (ϖ : D.host.E) d α → DivAt V (cA D e) (star (ϖ : D.host.E)) (dualLab d) α := by
  first | exact @GlobalTheory.DivConj.divAt_conj | exact GlobalTheory.DivConj.divAt_conj | (intros; apply GlobalTheory.DivConj.divAt_conj <;> assumption)
end

section

noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity
open Formalism.L2.Th1.F (cmTheta)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.ThLoc.LocMM

theorem cmTheta_odd (b : ℤ) (hb : Odd b) (d : ℕ) : ∃ k : ℤ, cmTheta b d = cmTheta 1 d + (k : ℂ) := by
  obtain ⟨k, rfl⟩ := hb
  refine ⟨k, ?_⟩
  simp only [cmTheta]
  push_cast
  ring

theorem stable_of_one {V : Type*} [AddCommGroup V] [Module ℂ V] (Λ : AddSubgroup V) (d : ℕ)
    (h : ∀ x ∈ Λ, cmTheta 1 d • x ∈ Λ) (b : ℤ) (hb : Odd b) : ∀ x ∈ Λ, cmTheta b d • x ∈ Λ := by
  intro x hx
  obtain ⟨k, hk⟩ := cmTheta_odd b hb d
  rw [hk, add_smul]
  refine Λ.add_mem (h x hx) ?_
  rw [Int.cast_smul_eq_zsmul]
  exact Λ.zsmul_mem hx k

theorem odd_of_cmOK {a : ℕ} {b c : ℤ} {d : ℕ} (h : CmOK a b c d) : Odd b := by
  by_contra hb
  obtain ⟨k, rfl⟩ := Int.not_odd_iff_even.1 hb
  have h1 := h.1
  have h8 := h.2.2.1
  have h2 : (d : ℤ) = 4 * ((a : ℤ) * c - k * k) := by
    have : (k + k) ^ 2 = 4 * (k * k) := by ring
    rw [this] at h1
    linarith
  generalize (a : ℤ) * c - k * k = t at h2
  omega

theorem hermitianSelfDual_of_fourfoldBlock {n : Type} [Fintype n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (hsd : IsSelfDual (matH (blk4 h)) (pow4 Λ)) : IsSelfDual (matH h) Λ := by
  have key : ∀ (x : n → ℂ) (y : Fin 4 × n → ℂ), altE (matH (blk4 h)) (CmData.embA 0 x) y = altE (matH h) x (slice 0 y) := by
    intro x y
    simp only [altE, matrixForm_fourfoldBlock, CmData.slice_embA]
    rw [Finset.sum_eq_single (0 : Fin 4)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  ext x
  constructor
  · intro hx
    have h1 : CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ) := by
      intro y hy
      obtain ⟨m, hm⟩ := hx (slice 0 y) (hy 0)
      exact ⟨m, by rw [key, hm]⟩
    rw [hsd] at h1
    have h2 := h1 0
    rwa [CmData.slice_embA, if_pos rfl] at h2
  · intro hx y hy
    have h1 : CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ) := by
      rw [hsd]
      exact CmData.embA_mem Λ 0 hx
    obtain ⟨m, hm⟩ := h1 _ (CmData.embA_mem Λ 0 hy)
    refine ⟨m, ?_⟩
    rw [key, CmData.slice_embA, if_pos rfl] at hm
    exact hm

section Base

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem selfDual_fourfold_curveIdeal_lattice (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (matH (blk4 (hOne B.L D.what₂.Tau))) (pow4 B.lamM) := by
  have h := ((B.latAll hcc hδ (base_linkage_nonempty D cc δ B)).1 2 2 _ _
    (Formalism.MainNotions.GlobalTheoryTheory.Inhab.Adm_std D 2 2 even_two even_two)).1
  rw [show TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = _ from B.areaOK, show TaylorLogMetric.La D B.tor _ _ = _ from B.lat0OK 2 2] at h
  have h2 := SO.selfDual_img _ _ (SO.reix D.what₂.Tau) (SO.reix_isom B.L D.what₂.Tau) _ h
  rw [SO.reix_pow] at h2
  exact h2

theorem selfDual_lamM (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (matH (hOne B.L D.what₂.Tau)) B.lamM :=
  hermitianSelfDual_of_fourfoldBlock _ _ (selfDual_fourfold_curveIdeal_lattice B hcc hδ)

theorem stable_lamM (b : ℤ) (hb : Odd b) : ∀ x ∈ B.lamM, cmTheta b D.host.d • x ∈ B.lamM := by
  refine stable_of_one _ _ (fun x hx => ?_) b hb
  have := SO.lamMM_smul (AR.om D) hx
  rw [← SO.theta_eq] at this
  exact this

end Base

theorem kappaAt {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) : B.KappaAt p ι := by
  by_cases hs : SplitK D p
  · exact GlobalTheory.T.kappa_norm_at_splitPrimes D cc δ B hcc hδ p ι hs
  · exact GlobalTheory.T.kappa_on_nonsplit_primes D cc δ B hcc hδ p ι hs

theorem locNormMM : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (B : Base D cc δ) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → B.IsCm a₀ b₀ ha hd lam hlam →
    ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), B.LocNormMM a₀ b₀ ha hd lam hlam p ι := by
  intro D cc δ hcc hδ B a₀ b₀ c₀ ha hd lam hlam hcm hB l _ ι
  have hK : B.KappaAt l ι := kappaAt B hcc hδ l ι
  obtain ⟨hL, hω⟩ := hB
  have hS : StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM (alphaQ B.cq (matH (hOne B.L D.what₂.Tau)))
    (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC := B.stdOK hcc hδ
  have hsd := selfDual_lamM B hcc hδ
  have hst := stable_lamM B b₀ (odd_of_cmOK hcm)
  have hspec := B.thMM_spec (B.stdOK hcc hδ)
  have h2 : tens4 B.thMM = B.kappa • kernel4 B.L B.ω₀ B.lamM
      (alphaQ (Real.sqrt D.host.d / 2) (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC := hspec.2
  have iso := hS.isom
  have i1 := hS.idx₁
  have i2 := hS.idx₂
  unfold Base.KappaAt Base.latA at hK
  unfold Base.LocNormMM LocNorm
  rw [hω] at h2
  rw [hL] at h2 hK iso i1 i2 hsd ⊢
  have hsda := CmData.selfDual_img _ _ B.gC iso _ (CmData.isSelfDual_matH_blk4_pow4 _ B.lamM hsd)
  have hsta : ∀ x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM),
      cmTheta b₀ D.host.d • x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM) := by
    rintro x ⟨x', hx', rfl⟩
    refine ⟨cmTheta b₀ D.host.d • x', fun a' => hst _ (hx' a'), ?_⟩
    simp
  obtain ⟨u, huiso, hufix, j1, jl, j2⟩ := localStandard a₀ b₀ c₀ D.host.d ha hd lam hlam hcm (Fin 4 × D.what₂.Tau) _
    hsda hsta i1 i2 l Fact.out
  have hκu := hK u huiso j1 jl j2
  rw [← KR.imgLat_trans] at j1 jl j2
  have hg₁ : IsIsom (matH (blk4 (hOne (cmL a₀ b₀ D.host.d ha hd lam hlam) D.what₂.Tau)))
      (stdH (cmL a₀ b₀ D.host.d ha hd lam hlam) (Fin 4 × D.what₂.Tau))
      ((B.gC.trans u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) :
        (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) := by
    intro x y
    have h1 := huiso (B.gC x) (B.gC y)
    have h0 := iso x y
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply] at h0 h1 ⊢
    rw [h1, h0]
  have D0 := stdDataCm a₀ b₀ c₀ D.host.d ha hd lam hlam hcm.1 hcm.2.1 hcm.2.2.1 D.what₂.Tau _ B.lamM B.gC iso hsd hst i1 i2
  have D1 := stdDataCm a₀ b₀ c₀ D.host.d ha hd lam hlam hcm.1 hcm.2.1 hcm.2.2.1 D.what₂.Tau _ B.lamM (B.gC.trans u) hg₁
    hsd hst j1 j2
  have hcomp : B.gC.symm.trans (B.gC.trans u) = u := by
    ext x
    simp
  have hfix : ∀ x, (B.gC.trans u) x = B.gC x → x = 0 := by
    intro x hx
    have h1 : B.gC x = 0 := hufix _ hx
    simpa using congrArg B.gC.symm h1
  rw [← hcomp] at hκu
  obtain ⟨c, hc8, hc⟩ := kernelRatio _ _ D.what₂.Tau _ B.lamM _ _ B.gC (B.gC.trans u) D0 D1 hfix
  refine ⟨B.gC.trans u, B.kappa * c, hg₁, jl, j2, (KR.norm_mul_eq_one ι B.kappa c _ hc8 hκu).le, ?_⟩
  rw [h2, hc, smul_smul]

end GlobalTheory.ThLoc.LocMM
end
end
