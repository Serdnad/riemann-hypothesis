module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDiff
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle021
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle028
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle020
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle046
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle035
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle017
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle019
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle092
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import GroundTheory.AutomorphicForms.FiniteBruhat
public import GroundTheory.AutomorphicForms.Iwasawa
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle289
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle101
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle042
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle028
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
public import Development.WeilBound.CoreStatements.ThetaDilations.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle291
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThetaIndep

theorem thetaMeas_gram_indep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ μ' : Measure (HA (AF F) σ J)) (𝓕 𝓕' : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsHaarH F E σ M J μ' → IsFDH F E σ M J μ' 𝓕' → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), thetaMeas σ J μ 𝓕 {X | gramE σ J X = T} = thetaMeas σ J μ' 𝓕' {X | gramE σ J X = T} := by
  intro F E _ _ _ _ _ σ hcm M J hJ μ μ' 𝓕 𝓕' hμ h𝓕 hμ' h𝓕₂ n T
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)
  obtain ⟨ac, a1, a2, ag⟩ := hact n
  have hrat := (GlobalTheory.T.gram_matrix_local_global F E σ hcm M J hJ n 0 T).2
  have hl := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 n {X | gramE σ J X = T}
  have hl' := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ' 𝓕' hμ' h𝓕₂ n {X | gramE σ J X = T}
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  have hri : Function.Injective (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _) := fun X Y h =>
    funext fun a => funext fun i => hinj (congrFun (congrFun h a) i)
  have hfin := ((GlobalTheory.T.unitary_group_finite_volume F E σ hcm M J hJ).2 μ hμ).2 𝓕 h𝓕
  have : μ.IsHaarMeasure := hμ
  have : μ'.IsHaarMeasure := hμ'
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have : Countable Γ := (GlobalTheory.T.arithmetic_unitary_group_discrete F E σ hcm M J hJ).1
  have h𝓕₁ : IsFundamentalDomain Γ 𝓕 μ := h𝓕
  have h0 := (GlobalTheory.T.finite_covolume_unimodular (HA (AF F) σ J) Γ μ 𝓕 h𝓕₁ hfin).1
  have hsm : μ' = Measure.haarScalarFactor μ' μ • μ := Measure.isMulLeftInvariant_eq_smul μ' μ
  have hc0 : Measure.haarScalarFactor μ' μ ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ' μ).ne'
  set c : ℝ≥0 := Measure.haarScalarFactor μ' μ with hc
  have hac : μ ≪ μ' := by
    rw [hsm]
    exact Measure.absolutelyContinuous_smul (by exact_mod_cast hc0)
  have h𝓕₃ : IsFundamentalDomain Γ 𝓕' μ' := h𝓕₂
  have h𝓕₄ : IsFundamentalDomain Γ 𝓕' μ := h𝓕₃.mono hac
  have hmass : μ 𝓕 = μ 𝓕' := h𝓕₁.measure_eq h𝓕₄
  refine Measure.ext_of_lintegral _ fun Φ hΦ => ?_
  rw [hl _ hΦ, hl' _ hΦ]
  set f : HA (AF F) σ J → ℝ≥0∞ := fun g => ∑' X : {X | gramE σ J X = T},
    Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) with hf
  have hle : ∀ (γ : Γ) g, f (γ • g) ≤ f g := fun γ g => by
    choose t ht using fun X : {X | gramE σ J X = T} => PositivityTheory.PlacePermOperatorBicommutantSpan.act_rat (n := n) γ⁻¹ X.1
    have ht' : ∀ X, actW (AF F) σ J (γ : HA (AF F) σ J)⁻¹ (ratTup (AF F) X.1) = ratTup (AF F) (t X) := ht
    have hT : ∀ X, gramE σ J (t X) = T := fun X =>
      Matrix.map_injective hinj (by simp only [← hrat, ← ht', ag]; rw [hrat, X.2])
    have hti : Function.Injective fun X => (⟨t X, hT X⟩ : {X | gramE σ J X = T}) := fun X Y e => by
      have h1 := congrArg (actW (AF F) σ J γ) ((ht' X).trans ((congrArg (fun Z => ratTup (AF F) Z.1) e).trans (ht' Y).symm))
      simp only [← a2, mul_inv_cancel, a1] at h1
      exact Subtype.ext (hri h1)
    refine le_trans (le_of_eq (tsum_congr fun X => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hti _)
    rw [Subgroup.smul_def, smul_eq_mul, mul_inv_rev, a2, ht']
  have hinv : ∀ (γ : Γ) g, f (γ • g) = f g := fun γ g =>
    (hle γ g).antisymm (by simpa using hle γ⁻¹ (γ • g))
  have hint : ∫⁻ g in 𝓕, f g ∂μ = ∫⁻ g in 𝓕', f g ∂μ := h𝓕₁.setLIntegral_eq h𝓕₄ f hinv
  have hcE0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0
  have hcT : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  rw [hint, hsm, Measure.restrict_smul, lintegral_smul_measure, Measure.smul_apply, ← hmass]
  simp only [ENNReal.smul_def, smul_eq_mul]
  rw [ENNReal.mul_inv (Or.inl hcE0) (Or.inl hcT)]
  calc _ = ((c : ℝ≥0∞)⁻¹ * c) * ((μ 𝓕)⁻¹ * ∫⁻ g in 𝓕', f g ∂μ) := by rw [ENNReal.inv_mul_cancel hcE0 hcT, one_mul]
    _ = _ := by ring

end GlobalTheory.CompanionTheory.SW.ThetaIndep

end
end

section

open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

theorem _root_.GlobalTheory.T.arch_lie_derivative_exists : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (hs : φ.1 ∈ AutomorphicForm.archSmooth E a), IsAutForm φ → (∀ [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)]
    (μ : MeasureTheory.Measure (AutomorphicForm.archGroup E a)) [μ.IsHaarMeasure]
    (k : ℕ) (J : Fin k → Fin (CuspidalSpectrum.archDim E a)),
    ∃ D : AutomorphicForm.archGroup E a → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : AdelicGLn.AdelicGL E a,
      ((AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := E) (n := a) k J) (⟨φ.1, hs⟩ : ↥(AutomorphicForm.archSmooth E a)) :
        ↥(AutomorphicForm.archSmooth E a)) : AdelicGLn.AdelicGL E a → ℂ) g = ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * D y ∂μ) := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.uJ_eq_conv | exact GlobalTheory.CompanionTheory.HCRep.uJ_eq_conv | (intros; apply GlobalTheory.CompanionTheory.HCRep.uJ_eq_conv <;> assumption)
end

section

open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory

namespace GlobalTheory.CompanionTheory.TyFin.CuspLabel

theorem root_pow_eq_one {K : Type} [Field K] [Fintype K] {P : K[X]} (hmon : P.Monic) (hirr : Irreducible P)
    (hX : P ≠ X) {x : AlgebraicClosure K} (hx : aeval x P = 0) :
    x ^ (Fintype.card K ^ P.natDegree - 1) = 1 := by
  have hmin : P = minpoly K x := minpoly.eq_of_irreducible_of_monic hirr hx hmon
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hfr : Module.finrank K (IntermediateField.adjoin K {x}) = P.natDegree := by
    rw [hmin, IntermediateField.adjoin.finrank hint]
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hX (hmin.trans (minpoly.zero K _))
  haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin K {x}) := Module.finite_of_finite K
  letI := Fintype.ofFinite (IntermediateField.adjoin K {x})
  have hcard : Fintype.card (IntermediateField.adjoin K {x}) = Fintype.card K ^ P.natDegree := by
    rw [← hfr]; exact Module.card_eq_pow_finrank
  have hy : IntermediateField.AdjoinSimple.gen K x ≠ 0 := by
    intro h
    exact hx0 (by simpa using congrArg (algebraMap (IntermediateField.adjoin K {x}) (AlgebraicClosure K)) h)
  have h := FiniteField.pow_card_sub_one_eq_one _ hy
  rw [hcard] at h
  simpa using congrArg (algebraMap (IntermediateField.adjoin K {x}) (AlgebraicClosure K)) h

theorem rootSum_minpoly {K : Type} [Field K] [Fintype K] (θ : AlgebraicClosure K →* ℂ) {d : ℕ} (hd : 0 < d)
    {w : AlgebraicClosure K} (hw : w ^ (Fintype.card K ^ d - 1) = 1) (hdeg : (minpoly K w).natDegree = d)
    (j : ℕ) : GlobalTheory.CuspGL.rootSum θ j (minpoly K w) =
      ∑ i ∈ Finset.range d, θ (w ^ Fintype.card K ^ i) ^ j := by
  have h := (GlobalTheory.T.frobeniusTorus_minpoly_degree_rootPowerSum K θ d hd w (by
    show w ^ (Nat.card K ^ d - 1) = 1
    rw [Nat.card_eq_fintype_card]; exact hw)).2.2 j
  rw [hdeg, Nat.div_self hd, pow_one, Nat.card_eq_fintype_card] at h
  exact h

theorem exists_cuspidal_label : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) (d : ℕ), 1 ≤ d → ∀ P : K[X], P.Monic → Irreducible P → P ≠ X → P.natDegree = d →
    ∃ τ : FDRep ℂ (GL (Fin d) K), Simple τ ∧ IsCuspidal K τ ∧ HasCuspLabel C τ P := by
  intro K _ _ _ C d hd P hmon hirr hX hdeg
  have hcard : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hqd : 1 < Fintype.card K ^ d := Nat.one_lt_pow (by omega) hq
  obtain ⟨x₀, hx₀⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) P
    (by
      intro h
      have h0 : P.natDegree = 0 := natDegree_eq_of_degree_eq_some (by simpa using h)
      omega)
  have hroot : ∀ w : AlgebraicClosure K, aeval w P = 0 → w ^ (Fintype.card K ^ d - 1) = 1 := fun w hw => by
    rw [← hdeg]; exact root_pow_eq_one hmon hirr hX hw
  have hminP : ∀ w : AlgebraicClosure K, aeval w P = 0 → minpoly K w = P := fun w hw =>
    (minpoly.eq_of_irreducible_of_monic hirr hw hmon).symm
  have hprim : IsPrimitiveRoot (C.gen d) (Fintype.card K ^ d - 1) := by
    rw [← C.gen_order d hd]; exact IsPrimitiveRoot.orderOf _
  haveI : NeZero (Fintype.card K ^ d - 1) := ⟨by omega⟩
  obtain ⟨k, -, hkx⟩ := hprim.eq_pow_of_pow_eq_one (hroot x₀ hx₀)
  have hreg := GlobalTheory.T.exponent_regular_of_natDegree_minpoly_generator_pow K d k (C.gen d) hd (by rw [hcard]; exact C.gen_order d hd)
    (by rw [hkx, hminP x₀ hx₀, hdeg])
  obtain ⟨hch, hip⟩ := GlobalTheory.T.isCharacter_cuspidal_rootSum_regular K C.ι C.ι_inj d k hd hreg
  have hadd := (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow K C.ι k).1
  obtain ⟨n, ρ, hρ⟩ := (GlobalTheory.T.matrixTrace_iff_isCharacterOverSubfield_complex _ _).2 hch
  have hchar : ∀ g : GL (Fin d) K, (PI.SerBridgeGLW.repOfGL ρ).character g = (-1) ^ (d - 1) *
      GlobalTheory.CuspGL.psi (GlobalTheory.CuspGL.rootSum C.ι k) (Fin d → K)
        (Matrix.toLin' (g : Matrix (Fin d) (Fin d) K)) := fun g => by
    rw [PI.SerBridgeGLW.repOfGL_character, ← hρ]
  refine ⟨PI.SerBridgeGLW.repOfGL ρ, ?_, ?_, hmon, hirr, hX, by simpa using hdeg, ?_⟩
  · rw [FDRep.simple_iff_char_is_norm_one]
    rw [(GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties K d (fun _ => 0)).2.2.1, finsum_eq_sum_of_fintype, GlobalTheory.CuspGL.glCard] at hip
    rw [← hip]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 : ((-1 : ℂ) ^ (d - 1)) * ((-1 : ℂ) ^ (d - 1)) = 1 := by
      rw [← mul_pow]; simp
    rw [← PI.SerBridgeGLW.conjugate_character_formula _ (PI.SerBridgeGLW.repOfGL ρ) x, hchar, star_mul', star_pow,
      star_neg, star_one, mul_mul_mul_comm, h1, one_mul]
  · refine GlobalTheory.T.cuspidal_of_unipotent_sums_vanish K d _ fun a ha had => ?_
    have h := GlobalTheory.T.finsum_unipotent_radical_eq_zero_of_isPrimitive K d _ (GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse K (Fin d → K) _ hadd) a ha had
    rw [finsum_mem_def, finsum_eq_sum_of_fintype] at h
    have h2 := congrArg (fun z : ℂ => (-1 : ℂ) ^ (d - 1) * z) h
    simp only [mul_zero, Finset.mul_sum] at h2
    refine Eq.trans ?_ h2
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
        ((i : ℕ) < a ∧ a ≤ (j : ℕ))
    · rw [if_pos hu, Set.indicator_of_mem (by exact hu), hchar]
    · rw [if_neg hu, Set.indicator_of_notMem (by exact hu), mul_zero]
  · intro x hx γ hγ z hz m hm
    simp only [Fintype.card_fin] at hm ⊢
    have hQ : minpoly K z = Matrix.charpoly (γ : Matrix (Fin d) (Fin d) K) :=
      (minpoly.eq_of_irreducible_of_monic hγ hz (Matrix.charpoly_monic _)).symm
    have hQd : (minpoly K z).natDegree = d := by
      rw [hQ, Matrix.charpoly_natDegree_eq_dim]; simp
    have hz1 : z ^ (Fintype.card K ^ d - 1) = 1 := by
      rw [← hm, ← pow_mul, mul_comm, pow_mul, ← C.gen_order d hd, pow_orderOf_eq_one, one_pow]
    have hval := GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible K (Fin d → K) _ hadd
      (Matrix.toLin' (γ : Matrix (Fin d) (Fin d) K)) (by rw [Matrix.charpoly_toLin']; exact hγ)
    rw [Matrix.charpoly_toLin'] at hval
    show (PI.SerBridgeGLW.repOfGL ρ).character γ = _
    rw [hchar, hval, ← hQ, rootSum_minpoly C.ι hd hz1 hQd k]
    congr 1
    have hxd : (minpoly K x).natDegree = d := by rw [hminP x hx, hdeg]
    have hx₀d : (minpoly K x₀).natDegree = d := by rw [hminP x₀ hx₀, hdeg]
    calc ∑ i ∈ Finset.range d, C.ι (z ^ Fintype.card K ^ i) ^ k
        = ∑ i ∈ Finset.range d, C.ι (x₀ ^ Fintype.card K ^ i) ^ m := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← map_pow, ← map_pow, ← hm, ← hkx]
          congr 1
          simp only [← pow_mul]
          congr 1
          ring
      _ = GlobalTheory.CuspGL.rootSum C.ι m (minpoly K x₀) := (rootSum_minpoly C.ι hd (hroot x₀ hx₀) hx₀d m).symm
      _ = GlobalTheory.CuspGL.rootSum C.ι m (minpoly K x) := by rw [hminP x₀ hx₀, hminP x hx]
      _ = ∑ i ∈ Finset.range d, C.ι (x ^ Fintype.card K ^ i) ^ m := rootSum_minpoly C.ι hd (hroot x hx) hxd m
      _ = ∑ i ∈ Finset.range d, C.ι x ^ (m * Fintype.card K ^ i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_pow, ← pow_mul, mul_comm (Fintype.card K ^ i) m]

end GlobalTheory.CompanionTheory.TyFin.CuspLabel
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.TensorIrr

theorem nontrivial_space_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  exact bot_ne_top (α := Subrepresentation ρ)
    (Subrepresentation.ext (Subsingleton.elim _ _))

theorem nontrivial_piTensorProduct_of_nontrivial {ι : Type} [Fintype ι] {V : ι → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, Nontrivial (V i)] :
    Nontrivial (PiTensorProduct ℂ V) := by
  have hv : ∀ i, ∃ v : V i, v ≠ 0 := fun i => exists_ne 0
  choose v hv using hv
  have hf : ∀ i, ∃ f : Module.Dual ℂ (V i), f (v i) ≠ 0 := fun i => by
    by_contra hc
    exact hv i ((Module.forall_dual_apply_eq_zero_iff ℂ (v i)).1
      fun f => not_not.1 (not_exists.1 hc f))
  choose f hf using hf
  let F : (Π i, V i) →ₘₗ[ℂ] ℂ := (MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap f
  have hF : PiTensorProduct.lift F (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    rw [PiTensorProduct.lift.tprod]
    simpa [F] using Finset.prod_ne_zero_iff.2 fun i _ => hf i
  refine ⟨PiTensorProduct.tprod ℂ v, 0, fun h => hF ?_⟩
  rw [h, map_zero]

theorem nontrivial_piTensorProduct_irrGL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h : ℕ} (x : Fin h → IrrGL (k := k)), Nontrivial (PiTensorProduct ℂ (fun a => (x a).2.rep.V)) := by
  intro k _ _ _ _ h x
  have : ∀ a, Nontrivial (x a).2.rep.V := fun a =>
    nontrivial_space_of_isIrreducible _ (x a).2.rep.irr
  exact nontrivial_piTensorProduct_of_nontrivial

end GlobalTheory.CompanionTheory.TensorIrr
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.LocGL

theorem isLSeg_single (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ρ : IrrGL (k := k)) (hρ : ρ.IsCusp) : IsLSeg (Segment.single ρ hρ) ρ.rep := by
  have hterm : ((Segment.single ρ hρ).term : Fin 1 → IrrGL (k := k)) = fun _ => ρ := by
    funext a
    have ha : (a : ℕ) = 0 := by
      have h1 : (a : ℕ) < 1 := a.isLt
      omega
    show (Segment.single ρ hρ).first.nu ((a : ℕ) : ℂ) = ρ
    rw [ha, Nat.cast_zero, show (Segment.single ρ hρ).first = ρ from Segment.first_ofFirst ρ hρ 1 one_pos,
      IrrGL.nu_zero]
  have key : ∀ x : Fin 1 → IrrGL (k := k), x = (fun _ => ρ) → ∀ hd : ∑ a, (x a).1 = ρ.1,
      IsCosocle ρ.rep (prodIrr x hd) := by
    intro x hx hd
    subst hx
    obtain ⟨φ⟩ := nonempty_equiv_prodIrr_one ρ hd
    exact (isCosocle_self ρ.2.rep.irr).of_equiv (Representation.Equiv.refl _) φ
  have hd : ∑ a : Fin 1, ((Segment.single ρ hρ).term a).1 = ρ.1 := by
    rw [hterm]
    simp
  exact ⟨hd, key _ hterm hd⟩

end GlobalTheory.CompanionTheory.LocGL
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.LocGL

theorem isLSeg_of_isL_singleton : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Δ : Segment k) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsL {Δ} π → IsLSeg Δ π := by
  intro k _ _ _ _ Δ N V _ _ π h
  obtain ⟨h', x, hd, ⟨Δ', ⟨hm, -⟩, hL⟩, hc⟩ := h
  have hcard : h' = 1 := by
    have := congrArg Multiset.card hm
    simpa using this
  subst hcard
  have hΔ : Δ' 0 = Δ := by
    have hmem : Δ' 0 ∈ Finset.univ.val.map Δ' := Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)
    rw [hm] at hmem
    simpa using hmem
  have hL0 : IsLSeg Δ (x 0).rep := hΔ ▸ hL 0
  obtain ⟨y, rfl⟩ : ∃ y, x = fun _ => y := ⟨x 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hN : y.1 = N := by simpa using hd
  subst hN
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one y hd
  obtain ⟨φ⟩ := hc.unique ((isCosocle_self y.2.rep.irr).of_equiv (.refl _) ψ)
  exact hL0.of_equiv φ

end GlobalTheory.CompanionTheory.LocGL
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.WordProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open Classical in
def clOf (a : IrrGL (k := k)) (d : ℕ) : IrrCl (GL (Fin d) k) :=
  if h : a.1 = d then h ▸ a.2 else (IrrRep.det (Fin d) 1 isSmoothChar_one).cl

theorem clOf_self (a : IrrGL (k := k)) : clOf a a.1 = a.2 := by
  simp [clOf]

end GlobalTheory.CompanionTheory.WordProd

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem terms_eq_first (Γ : Segment k) {u v : IrrGL (k := k)} (hu : Γ.first = u)
    (hΓ : Γ.carrier ⊆ {u} ∪ {v}) (hv : v ≠ u.nu 1) :
    ∀ a : ℕ, a < Γ.len → Γ.first.nu a = u := by
  intro a
  induction a with
  | zero =>
    intro _
    rw [Nat.cast_zero, IrrGL.nu_zero, hu]
  | succ n ih =>
    intro hn
    have h1 : Γ.first.nu ((n + 1 : ℕ) : ℂ) = u.nu 1 := by
      rw [← ih (by omega), IrrGL.nu_nu, Nat.cast_succ]
    have hmem : Γ.first.nu ((n + 1 : ℕ) : ℂ) ∈ Γ.carrier := Segment.mem_carrier.2 ⟨n + 1, hn, rfl⟩
    rcases (Set.mem_union _ _ _).1 (hΓ hmem) with h | h
    · exact Set.mem_singleton_iff.1 h
    · exact absurd ((Set.mem_singleton_iff.1 h).symm.trans h1) hv

theorem not_linked_single {x y : IrrGL (k := k)} (hx : x.IsCusp) (hy : y.IsCusp) (h1 : y ≠ x.nu 1) (h2 : x ≠ y.nu 1) :
    ¬ (Segment.single x hx).Linked (Segment.single y hy) := by
  rintro ⟨⟨Γ, hΓ⟩, hxy, -⟩
  simp only [Segment.carrier_single] at hΓ hxy
  have hne : x ≠ y := fun h => hxy (by subst h; exact subset_rfl)
  have key : ∀ u v : IrrGL (k := k), Γ.first = u → Γ.carrier ⊆ {u} ∪ {v} → v ≠ u.nu 1 → v ∈ Γ.carrier → v = u := by
    intro u v hu hsub hv hvmem
    obtain ⟨a, ha, hav⟩ := Segment.mem_carrier.1 hvmem
    rw [← hav]
    exact terms_eq_first Γ hu hsub hv a ha
  have hfirst : Γ.first ∈ Γ.carrier :=
    Segment.mem_carrier.2 ⟨0, Γ.len_pos, by rw [Nat.cast_zero, IrrGL.nu_zero]⟩
  rw [hΓ] at hfirst
  rcases (Set.mem_union _ _ _).1 hfirst with h | h
  · refine hne (key x y (Set.mem_singleton_iff.1 h) hΓ.subset h1 ?_).symm
    rw [hΓ]
    exact Set.mem_union_right _ (Set.mem_singleton y)
  · refine hne (key y x (Set.mem_singleton_iff.1 h) ?_ h2 ?_)
    · intro z hz
      rw [hΓ] at hz
      rcases (Set.mem_union _ _ _).1 hz with hz | hz
      · exact Set.mem_union_right _ hz
      · exact Set.mem_union_left _ hz
    · rw [hΓ]
      exact Set.mem_union_left _ (Set.mem_singleton x)

end GlobalTheory.CompanionTheory.BZPair

end
end

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.double_coset_block_matrix : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ), (∀ x y, γ x < γ y ↔ blk e' x < blk e' y) → ∀ (w w' : Equiv.Perm (Fin N)), permGL k w' ∈ doubleCoset (permGL k w) (blockUpper k N β : Set (GL (Fin N) k)) (blockUpper k N γ) ↔ ∀ i j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w'.symm x) = j).card) := by
  first | exact @GlobalTheory.CompanionTheory.GeoCell.permGL_mem_doubleCoset_iff_card | exact GlobalTheory.CompanionTheory.GeoCell.permGL_mem_doubleCoset_iff_card | (intros; apply GlobalTheory.CompanionTheory.GeoCell.permGL_mem_doubleCoset_iff_card <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

theorem _root_.GlobalTheory.T.local_factor_sandwich_approx : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (C : ℝ) (g : Fv F v → ℝ), IsStdV v lam → (∀ s, 0 ≤ g s) → GoodFac v lam C g → ∀ η : ℝ, 0 < η → ∃ ψm ψp : Fv F v → ℝ, Continuous ψm ∧ HasCompactSupport ψm ∧ Continuous ψp ∧ HasCompactSupport ψp ∧ (∀ s, 0 ≤ ψm s) ∧ (∀ s, s ≠ 0 → ψm s ≤ g s ∧ g s ≤ ψp s) ∧ 1 - η ≤ ∫ s, ψm s ∂lam ∧ ∫ s, ψp s ∂lam ≤ 1 + η := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.exists_sandwich | exact GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.exists_sandwich | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.exists_sandwich <;> assumption)
end
