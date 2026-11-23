module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle900
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle230
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.GroupWithZero.Torsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinsetRepresentatives
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle902
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
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.TensorProduct.Pi
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle898
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535

@[expose] public section

section

set_option autoImplicit false

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory.GenSubDeg

theorem genSub_coeff_le : ∀ (O : Type) [CommRing O] (N : ℕ) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D → ∀ m, (GlobalTheory.HighWt.genSub O N f).coeff m ≠ 0 → ∀ v, m v ≤ D := by
  intro O _ N D f hf m hm v
  have hg : ∀ i : Fin N × Fin N, (∑ b : Fin N, (X (i.1, b) * C (X (b, i.2)) : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O))).totalDegree ≤ 1 := by
    intro i
    refine totalDegree_finsetSum_le fun b _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, add_zero]
    rw [X]
    exact (totalDegree_monomial_le _ _).trans (by simp)
  have hdeg := GlobalTheory.SZShift.totalDegree_aeval_le_of_deg_le_one _ hg f
  have h1 : m.degree ≤ (GlobalTheory.HighWt.genSub O N f).totalDegree := by
    rw [Finsupp.degree]
    exact le_totalDegree (mem_support_iff.mpr hm)
  have h2 : m v ≤ m.degree := by
    classical
    rw [Finsupp.degree]
    by_cases hv : v ∈ m.support
    · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv
    · simp [Finsupp.notMem_support_iff.mp hv]
  exact h2.trans (h1.trans ((hdeg.trans hf)))

end GlobalTheory.GenSubDeg
end

section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

theorem _root_.GlobalTheory.T.squarefree_monic_poly_labels_semisimple_parameter : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r : ℕ) (f : (ZMod p)[X]), f.Monic → f.natDegree = r → f.coeff 0 ≠ 0 → Squarefree f → ∃ (s : SSParam p ℂ r) (x : Cyc s.1 → Fbar p), Labels L s x f := by
  first | exact @GlobalTheory.ParamExists.param_exists | exact GlobalTheory.ParamExists.param_exists | (intros; apply GlobalTheory.ParamExists.param_exists <;> assumption)
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.isOpen_diagonalSliceLevelSubgroup : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (hr : r ≤ a) (t : GL (Fin a) (Af E)) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → IsOpen (GlobalTheory.SliceTwo.levelSub hr t L : Set (GL (Fin (a - r)) (Af E))) := by
  first | exact @GlobalTheory.SliceTwo.isOpen_levelSub | exact GlobalTheory.SliceTwo.isOpen_levelSub | (intros; apply GlobalTheory.SliceTwo.isOpen_levelSub <;> assumption)
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.constant_term_slice_continuous_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : GA E a → ℂ, Continuous φ → (∀ γ g, φ (ratGL E a γ * g) = φ g) → ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (γ : GL (Fin (a - r)) E) (g : GA E (a - r)), GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ m₁ t κ (ratGL E (a - r) γ * g) = GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ m₁ t κ g := by
  first | exact @GlobalTheory.SliceTwo.slice_ratGL_mul | exact GlobalTheory.SliceTwo.slice_ratGL_mul | (intros; apply GlobalTheory.SliceTwo.slice_ratGL_mul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_appellHumbertFrame_of_lineBundleIso : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L L' : LB A.left) (u' : HolUnif A L' g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ' : u'.Λ → ℂ), L.IsLB → L'.IsLB → LBIso L L' → GlobalTheory.TorusRM.IsFactorAH u' Hm χ' → ∃ (u : HolUnif A L g) (χ : u.Λ → ℂ), u.ex = u'.ex ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  exact @GlobalTheory.TransportFrame.exists_holUnif_isFactorAH_of_lbIso
end

section

open NumberField

open scoped Pointwise

namespace GlobalTheory.VacRead

theorem mul_smul_eq_span_absNorm {K : Type} [Field K] [NumberField K] [IsGalois ℚ K]
    (h2 : Module.finrank ℚ K = 2) (τ : K ≃ₐ[ℚ] K) (hτ : τ ≠ 1) (I : Ideal (𝓞 K)) :
    I * (τ • I) = Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 K)} := by
  classical
  by_cases hI : I = ⊥
  · subst hI; simp
  have huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {1, τ} := by
    symm; apply Finset.eq_univ_of_card
    rw [Finset.card_pair (Ne.symm hτ), ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h2]
  have hI0 : I ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero hI
  set h := Fintype.card (ClassGroup (𝓞 K)) with hh
  have hpos : h ≠ 0 := Fintype.card_ne_zero
  have hprin : (I ^ h).IsPrincipal := by
    have h1 : ClassGroup.mk0 (⟨I, hI0⟩ ^ h) = 1 := by rw [map_pow, pow_card_eq_one]
    exact (ClassGroup.mk0_eq_one_iff (pow_mem hI0 h)).1 h1
  obtain ⟨x, hx⟩ := hprin
  have hx' : I ^ h = Ideal.span {x} := hx
  have hτx : τ • (I ^ h) = Ideal.span {τ • x} := by
    rw [hx', Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
    rfl
  have hnorm : ((Algebra.norm ℤ x : ℤ) : 𝓞 K) = x * (τ • x) := by
    have hp : ((Algebra.norm ℤ x : ℤ) : 𝓞 K) = ∏ σ : K ≃ₐ[ℚ] K, σ • x := by
      apply RingOfIntegers.ext
      have h1 := Algebra.norm_eq_prod_automorphisms ℚ (x : K)
      rw [← Algebra.coe_norm_int] at h1
      change algebraMap (𝓞 K) K _ = algebraMap (𝓞 K) K _
      rw [map_prod, map_intCast]
      rw [map_intCast] at h1
      exact h1
    rw [hp, huniv, Finset.prod_pair (Ne.symm hτ), one_smul]
  have key : (I * (τ • I)) ^ h = Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 K)} ^ h := by
    rw [mul_pow, ← smul_pow', hx', ← hx', hτx, hx', Ideal.span_singleton_mul_span_singleton, ← hnorm,
      Ideal.span_singleton_pow, ← Nat.cast_pow, ← map_pow, hx', Ideal.absNorm_span_singleton]
    rcases Int.natAbs_eq (Algebra.norm ℤ x) with h4 | h4
    · conv_lhs => rw [h4]
      rw [Int.cast_natCast]
    · conv_lhs => rw [h4]
      rw [Int.cast_neg, Ideal.span_singleton_neg, Int.cast_natCast]
  exact pow_left_injective hpos key

theorem hostConj_quadraticGenerator_eq_neg (D : Formalism.BasicNotions.D7) :
    D.host.conj (D.host.sqd) = -D.host.sqd :=
  D.host.conj_sqd

theorem conj_mul_cE_absNorm (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) :
    (∀ α ∈ GlobalTheory.VacRead.cE D cc, ∀ β ∈ GlobalTheory.VacRead.cE D cc, ∃ o : 𝓞 D.host.E,
      D.host.conj α * β = (Ideal.absNorm cc : D.host.E) * (o : D.host.E)) ∧
    (Ideal.absNorm cc : D.host.E) ∈ Submodule.span (𝓞 D.host.E)
      {t | ∃ α ∈ GlobalTheory.VacRead.cE D cc, ∃ β ∈ GlobalTheory.VacRead.cE D cc, t = D.host.conj α * β} := by
  classical
  haveI : Algebra.IsQuadraticExtension ℚ D.host.K := ⟨GlobalTheory.CurveLattice.finrank_hostK D⟩
  let τ : D.host.K ≃ₐ[ℚ] D.host.K := D.host.conj.restrictNormal D.host.K
  have hτ : ∀ k : D.host.K, ((τ k : D.host.K) : D.host.E) = D.host.conj (k : D.host.E) :=
    fun k => AlgEquiv.restrictNormal_commutes D.host.conj D.host.K k
  have hτ1 : τ ≠ 1 := by
    intro h1
    have hs : D.host.sqd ∈ D.host.K :=
      IntermediateField.mem_adjoin_simple_self ℚ _
    have h2 := hτ ⟨_, hs⟩
    rw [h1, AlgEquiv.one_apply, hostConj_quadraticGenerator_eq_neg] at h2
    have h3 : D.host.sqd = 0 := by
      have : (2 : D.host.E) * D.host.sqd = 0 := by
        simp only at h2; linear_combination h2
      simpa using this
    have h4 := D.host.sqd_sq
    rw [h3] at h4
    have hd : (D.host.d : D.host.E) ≠ 0 := by exact_mod_cast D.host.hyp.2.1.pos.ne'
    exact hd (by simpa using h4.symm)
  have hI := mul_smul_eq_span_absNorm (GlobalTheory.CurveLattice.finrank_hostK D) τ hτ1 cc

  let iK : 𝓞 D.host.K →+* 𝓞 D.host.E := algebraMap (𝓞 D.host.K) (𝓞 D.host.E)
  have hiK : ∀ k : 𝓞 D.host.K, ((iK k : 𝓞 D.host.E) : D.host.E) = ((k : D.host.K) : D.host.E) := fun k => rfl
  have hsm : ∀ k : 𝓞 D.host.K, (((τ • k : 𝓞 D.host.K) : D.host.K) : D.host.E) = D.host.conj ((k : D.host.K) : D.host.E) :=
    fun k => hτ k
  set N : D.host.E := (Ideal.absNorm cc : D.host.E) with hN
  let M : Submodule (𝓞 D.host.E) D.host.E := Submodule.span (𝓞 D.host.E) {N}
  have hgen : ∀ c₁ ∈ cc, ∀ c₂ ∈ cc, D.host.conj ((c₁ : D.host.K) : D.host.E) * ((c₂ : D.host.K) : D.host.E) ∈ M := by
    intro c₁ h₁ c₂ h₂
    have hm : c₂ * (τ • c₁) ∈ cc * (τ • cc) := Ideal.mul_mem_mul h₂ (Ideal.smul_mem_pointwise_smul _ _ _ h₁)
    rw [hI, Ideal.mem_span_singleton'] at hm
    obtain ⟨k, hk⟩ := hm
    have hE : D.host.conj ((c₁ : D.host.K) : D.host.E) * ((c₂ : D.host.K) : D.host.E) = (iK k : D.host.E) * N := by
      rw [hiK, ← hsm, mul_comm, hN]
      have := congrArg (fun y : 𝓞 D.host.K => ((y : D.host.K) : D.host.E)) hk
      simp only [map_mul, map_natCast] at this
      push_cast at this ⊢
      rw [← this]
    rw [hE]
    exact Submodule.mem_span_singleton.mpr ⟨iK k, rfl⟩
  have hpart : ∀ α ∈ GlobalTheory.VacRead.cE D cc, ∀ β ∈ GlobalTheory.VacRead.cE D cc, D.host.conj α * β ∈ M := by
    intro α hα β hβ
    induction hα using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c₁, h₁, rfl⟩ := hx
      have hle : GlobalTheory.VacRead.cE D cc ≤ M.comap (LinearMap.mulLeft (𝓞 D.host.E) (D.host.conj ((c₁ : D.host.K) : D.host.E))) := by
        refine Submodule.span_le.mpr ?_
        rintro y ⟨c₂, h₂, rfl⟩
        exact hgen c₁ h₁ c₂ h₂
      exact hle hβ
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), add_mul]; exact M.add_mem hx hy
    | smul o x _ hx =>
      have : D.host.conj (o • x) * β = (RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) o) • (D.host.conj x * β) := by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
        rfl
      rw [this]
      exact M.smul_mem _ hx
  refine ⟨fun α hα β hβ => ?_, ?_⟩
  · obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.mp (hpart α hα β hβ)
    exact ⟨o, by rw [← ho, Algebra.smul_def, mul_comm]⟩
  · have hNK : ((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K) ∈ cc * (τ • cc) := by
      rw [hI]; exact Ideal.mem_span_singleton_self _
    have hcoe : N = ((((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K) : D.host.K) : D.host.E) := by
      rw [hN]; push_cast; rfl
    rw [hcoe]
    refine Submodule.mul_induction_on hNK ?_ ?_
    · intro a ha b hb
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hb
      have hb' : b = τ • (τ⁻¹ • b) := by rw [smul_inv_smul]
      refine Submodule.subset_span ⟨((τ⁻¹ • b : 𝓞 D.host.K) : D.host.K), Submodule.subset_span ⟨_, hb, rfl⟩,
        ((a : D.host.K) : D.host.E), Submodule.subset_span ⟨a, ha, rfl⟩, ?_⟩
      conv_lhs => rw [hb']
      rw [← hsm]
      push_cast
      ring
    · intro x y hx hy
      push_cast
      exact Submodule.add_mem _ hx hy

end GlobalTheory.VacRead
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AbhHeightOne

theorem closureEtaleAt_of_etale_integralClosure_localization : ∀ (A₁ R₁ D₁ : Type) [CommRing A₁] [CommRing R₁] [Algebra A₁ R₁] [CommRing D₁]
    [Algebra (GlobalTheory.LocAcyc.GenFib A₁ R₁) D₁] (P₁ : Ideal R₁) [P₁.IsPrime],
    (letI := (GlobalTheory.KeyOriginNoeth.baseHom A₁ R₁ D₁).toAlgebra;
      Algebra.Etale (Localization.AtPrime P₁)
        (integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] D₁))) →
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ R₁ D₁ P₁ := by
  intro A₁ R₁ D₁ _ _ _ _ _ P₁ _ h
  letI := (GlobalTheory.KeyOriginNoeth.baseHom A₁ R₁ D₁).toAlgebra
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A₁ R₁ D₁
  unfold GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt
  let e : GlobalTheory.KeyOriginNoeth.closure A₁ R₁ D₁ ≃ₐ[R₁] integralClosure R₁ D₁ :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hb := TensorProduct.toIntegralClosure_bijective_of_isLocalization (R := R₁)
    (S := Localization.AtPrime P₁) (B := D₁) P₁.primeCompl
  let Φ : Localization.AtPrime P₁ ⊗[R₁] GlobalTheory.KeyOriginNoeth.closure A₁ R₁ D₁ ≃ₐ[Localization.AtPrime P₁]
      integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] D₁) :=
    (Algebra.TensorProduct.congr AlgEquiv.refl e).trans (AlgEquiv.ofBijective _ hb)
  exact Algebra.Etale.of_equiv Φ.symm

theorem etale_integralClosure_of_torsor_field : ∀ (S S₁ K K₁ : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
    [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
    [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁],
    Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
    ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
    ∀ (M : Type) [CommRing M] [Algebra K M] (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)),
    GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] M)) := by
  intro S S₁ K K₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinj q hq hqu π hπ y hy M _ _ act htor
  obtain ⟨ι, _, L, _, _, hfd, hgal, hdeg, ⟨e⟩⟩ := GlobalTheory.T.zmodTorsor_field_eq_prod_galois K M q act hq htor
  have hi : ∀ i, Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] L i)) := fun i => by
    letI : Algebra S (L i) := ((algebraMap K (L i)).comp (algebraMap S K)).toAlgebra
    haveI : IsScalarTower S K (L i) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI := hfd i
    haveI := hgal i
    obtain ⟨hram, hsep⟩ := GlobalTheory.T.ramificationIdx_dvd_of_galois_degree_dvd_unit_dvr S K (L i) q hq hqu (hdeg i)
    exact GlobalTheory.T.abhyankar_etale_integralClosure_root_uniformizer S S₁ K K₁ (L i) hinj q hq hqu π hπ y hy hram hsep
  classical
  haveI := GlobalTheory.T.etale_integralClosure_pi_of_etale S₁ ι (fun i => K₁ ⊗[K] L i) hi
  let Ψ : K₁ ⊗[K] M ≃ₐ[K₁] ∀ i, K₁ ⊗[K] L i :=
    (Algebra.TensorProduct.congr AlgEquiv.refl e).trans (Algebra.TensorProduct.piRight K K₁ K₁ L)
  exact Algebra.Etale.of_equiv (Ψ.restrictScalars S₁).symm.mapIntegralClosure

theorem closureEtaleAt_of_root_of_uniformiser : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R],
    Function.Injective (algebraMap A R) →
    ∀ (A₁ R₁ : Type) [CommRing A₁] [IsDomain A₁] [CommRing R₁] [IsDomain R₁] [Algebra A₁ R₁],
    Function.Injective (algebraMap A₁ R₁) →
    ∀ (f : A →+* A₁), Function.Injective f → ∀ (φ : R →+* R₁),
    φ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp φ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA] (q : ℕ)
      (act : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    0 < q → IsUnit (q : A) → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q act →
    ∀ (P₁ : Ideal R₁) [P₁.IsPrime],
    IsDiscreteValuationRing (Localization.AtPrime P₁) →
    IsDiscreteValuationRing (Localization.AtPrime (P₁.comap φ)) →
    ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime (P₁.comap φ)) π) →
    ∀ y : R₁, y ^ q = φ (algebraMap A R π) →
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ R₁ (GlobalTheory.KeyOriginBC.BC β DA) P₁ := by
  intro A R _ _ _ _ _ hAR A₁ R₁ _ _ _ _ _ hA₁R₁ f hf φ hφ β hβ DA _ _ q act hq hqu htor P₁ _ hd₁ hd π hπ y hy
  exact closureEtaleAt_of_etale_integralClosure_localization A₁ R₁ _ P₁ (GlobalTheory.T.etale_integralClosure_torsor_of_fraction_fields etale_integralClosure_of_torsor_field A R hAR A₁ R₁ hA₁R₁ f hf φ hφ β hβ DA q act hq hqu htor P₁ hd₁ hd π hπ y hy)

end GlobalTheory.AbhHeightOne
end
end

section

open GlobalTheory GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.ker_rigExtMap_relFrob_le_range_rigOfOmega' :
    ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K),
      LinearMap.ker (rigExtMap (PDivGroup.relFrob h G)) ≤
        LinearMap.range (PDivGroup.frobTwist h G).rigOfOmega :=
  @PDivGroup.ker_rigExtMap_relFrob_le_range_rigOfOmega
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem range_rigOfOmega_le_range_rigExtMap_verschiebung :
    ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K),
      LinearMap.range (frobTwist h G).rigOfOmega ≤
        LinearMap.range (rigExtMap (verschiebung h G)) := by
  intro p _ K _ h G
  rintro _ ⟨w, rfl⟩
  obtain ⟨β, w', hβ, hd⟩ :=
    GlobalTheory.T.exists_additive_frobeniusPullback_cotangent_mod_verschiebung p K h G (-(w.1 1))
  obtain ⟨-, c, B₀, -, hB₀, -, hB₀'⟩ := exists_of_cobOne_eq_zero hβ
  obtain ⟨B, hB⟩ : cocyclesMap (verschiebung h G) c ∈ LinearMap.range (frobTwist h G).cob :=
    (Submodule.Quotient.mk_eq_zero _).1
      (LinearMap.congr_fun (vecExtMap_verschiebung h G) (Submodule.Quotient.mk c))
  have h1 : funsMap (relFrob h G) B - B₀ = 0 := G.eq_zero_of_cob_eq_zero h (by
    rw [map_sub, ← cocyclesMap_cob, hB, hB₀, ← relFrob_comp_verschiebung h G, sub_eq_zero]
    exact Subtype.ext (funext fun _ => (pullTwo_comp _ _ _).symm))
  have h2 : (relFrob h G).app 1 (B.1 1 - β) = 0 := by
    rw [map_sub, ← hB₀']
    exact congrArg (fun z : G.funs => z.1 1) h1
  obtain ⟨w'', hw''⟩ := dUnit_mem_range_of_mem_kerIdeal _
    (GlobalTheory.T.mem_kernel_ideal_of_app_eq_zero_field p K _ _ (verschiebung h G) (relFrob h G) (verschiebung_comp_relFrob h G)
      (relFrob_comp_verschiebung h G) _ h2)
  obtain ⟨u, hu⟩ := G.omegaLevel_surjective 1 (w' + w'')
  have h3 : (frobTwist h G).dFun B = omegaMap _ _ (verschiebung h G) u - w :=
    ((frobTwist h G).omegaLevel_one_bijective h).1 (by
      rw [map_sub, omegaLevel_apply, omegaLevel_apply, omegaLevel_apply, omegaMap_val,
        ← omegaLevel_apply, ← omegaLevel_apply _ _ u, hu, map_add, hw'']
      change dUnit (R := K) (B.1 1) = _
      rw [dUnit, dUnit, map_sub, ← dUnit, ← dUnit, hd]
      abel)
  refine ⟨G.rigMk (c, u), ?_⟩
  rw [rigExtMap_mk]
  refine (Submodule.Quotient.eq _).2 ⟨B, Prod.ext ?_ ?_⟩
  · exact hB.trans (sub_zero _).symm
  · exact h3

end GlobalTheory.PDivGroup
end
end

section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

theorem _root_.GlobalTheory.T.stable_lattice_chain_with_lines_matrix_form : ∀ (Γ O : Type) [Group Γ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n t R : ℕ) (r : Γ →* GL (Fin n) O) (ψ : Fin t → Γ →* Oˣ) (ϖ : O) (M : Fin (R + 1) → Submodule O (Fin n → O)) (rs : Fin t → Fin R), Irreducible ϖ → (∀ x, x ∈ M 0 ↔ ∃ y : Fin n → O, x = fun a => ϖ * y a) → M (Fin.last R) = ⊤ → Monotone M → (∀ g k x, x ∈ M k → (r g : Matrix (Fin n) (Fin n) O).mulVec x ∈ M k) → (∀ s, ∃ x ∈ M (rs s).succ, x ∉ M (rs s).castSucc ∧ M (rs s).succ = M (rs s).castSucc ⊔ Submodule.span O {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) O).mulVec x - (fun a => ((ψ s g : Oˣ) : O) * x a) ∈ M (rs s).castSucc) → ∃ (x : GalMats Γ O n t R) (dim : Fin (R + 1) → ℕ), x.Chain (residue O) r (fun s => GlobalTheory.TripleGal.rk1 (ψ s)) rs dim ∧ dim 0 = 0 ∧ dim (Fin.last R) = n ∧ ∀ s, dim (rs s).succ = dim (rs s).castSucc + 1 := by
  first | exact @GlobalTheory.WachChain.chain_of_lattices | exact GlobalTheory.WachChain.chain_of_lattices | (intros; apply GlobalTheory.WachChain.chain_of_lattices <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.fourierCoefficient_familyPullback_fractionField : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (hG : GlobalFnsSt) (k : ℕ) (s : Fam D (FractionRing R) k) (g : GtPtF D (FractionRing R)) (w : Frm D (FractionRing R) k g.b) (w' : Frm D F k (GlobalTheory.TorusExt.gtExt D (algebraMap (FractionRing R) F) (RingHom.comp_id _) g).b), w.IsGen → w'.IsGen → (∀ z J, Good D.P.L z J → val w' (𝟙 _) z J = val w (spMap (algebraMap (FractionRing R) F)) z J) → ∀ χ : D.X, coef (GlobalTheory.FieldBaseChange.famPull D (FractionRing R) F hG k s) (GlobalTheory.TorusExt.gtExt D (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) w' χ = algebraMap (FractionRing R) F (coef s g w χ) := by
  first | exact @GlobalTheory.Poinc.Tors.CoefPull.coef_famPull_frac | exact GlobalTheory.Poinc.Tors.CoefPull.coef_famPull_frac | (intros; apply GlobalTheory.Poinc.Tors.CoefPull.coef_famPull_frac <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat


theorem _root_.GlobalTheory.T.eq_of_proportional_germs_sectionsEmbedProjectively : ∀ {X Y Z : Scheme.{0}} (π : Y ⟶ Z) {N : LB Y} {κ : Type} (s : κ → LB.Sec N), GlobalTheory.AmpleSpan.EmbedsBy π s → ∀ (f₁ f₂ : X ⟶ Y), f₁ ≫ π = f₂ ≫ π → (∀ x : X, ∃ σ : κ → X.presheaf.stalk x, (∃ p, f₁ x ∈ N.U p ∧ ∃ u : (X.presheaf.stalk x)ˣ, ∀ l, gs f₁ x (N.U p) ((s l).f p) = u * σ l) ∧ (∃ p, f₂ x ∈ N.U p ∧ ∃ u : (X.presheaf.stalk x)ˣ, ∀ l, gs f₂ x (N.U p) ((s l).f p) = u * σ l)) → f₁ = f₂ := by
  first | (exact @GlobalTheory.HomFixGerm.eq_of_germs) | (exact GlobalTheory.HomFixGerm.eq_of_germs) | (intros; apply GlobalTheory.HomFixGerm.eq_of_germs  <;> assumption)
end
