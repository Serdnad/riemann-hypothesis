module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle001
public import Development.AutomorphicSpectrum.PublishedTheorems.Jets₂.IsPermissibleOfCentre
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraOfLinearGroupClosed
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
public import ReciprocityTheory.Hypotheses.GalCoh
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.Transport
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle041
public import GroundTheory.GlobalFields.TateThesis.EulerFactorsFinite
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle001
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohTate
import GroundTheory.ProfiniteCohomology.LocalTateDuality.MainDefs
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle040
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import GroundTheory.AutomorphicForms.GL2.FiniteIdeleDecomp
public import GroundTheory.AutomorphicForms.GL2.Bundle003
import GroundTheory.LocalFields.Bundle001
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ExistsApplyEqOfMemDec
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Inertia
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.MemRangeOfAevalRatEqZero
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Bundle001

@[expose] public section

section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.InvBasis

variable {n : ℕ}

def vecOf : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℝ] EuclideanSpace ℂ (Fin n × Fin n) where
  toFun X := WithLp.toLp 2 (fun p => X p.1 p.2)
  invFun x := Matrix.of fun i j => x (i, j)
  map_add' X Y := by ext p; simp
  map_smul' r X := by ext p; simp
  left_inv X := by ext i j; simp
  right_inv x := by ext p; simp

theorem inner_vecOf (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⟪vecOf X, vecOf Y⟫_ℝ = (Xᴴ * Y).trace.re := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [vecOf, Complex.inner]
  ring

theorem inner_conj {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⟪vecOf (k * X * k⁻¹), vecOf (k * Y * k⁻¹)⟫_ℝ = ⟪vecOf X, vecOf Y⟫_ℝ := by
  have h1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hk
  have h2 : k * kᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hk
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_right_inv h2
  rw [inner_vecOf, inner_vecOf, hinv]
  have : (k * X * kᴴ)ᴴ * (k * Y * kᴴ) = k * (Xᴴ * Y) * kᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc k * (Xᴴ * kᴴ) * (k * Y * kᴴ) = k * Xᴴ * (kᴴ * k) * Y * kᴴ := by
          simp only [Matrix.mul_assoc]
      _ = k * (Xᴴ * Y) * kᴴ := by rw [h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem exists_orthonormal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (W : Submodule ℝ E)
    [FiniteDimensional ℝ W] :
    ∃ (d : ℕ) (e : Fin d → E), (∀ i, e i ∈ W) ∧ Orthonormal ℝ e ∧ ∀ x ∈ W, x = ∑ i, ⟪e i, x⟫_ℝ • e i := by
  let B := stdOrthonormalBasis ℝ W
  refine ⟨_, fun i => (B i : E), fun i => (B i).2, ?_, ?_⟩
  · exact B.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  · intro x hx
    have := congrArg (Subtype.val) (B.sum_repr' ⟨x, hx⟩)
    simpa [Submodule.coe_sum] using this.symm

theorem orthogonal_of_preserves {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ} {e : Fin d → E}
    (he : Orthonormal ℝ e) (f : Fin d → E) (hexp : ∀ i, f i = ∑ l, ⟪e l, f i⟫_ℝ • e l)
    (hf : ∀ i j, ⟪f i, f j⟫_ℝ = ⟪e i, e j⟫_ℝ) :
    (Matrix.of fun l i => ⟪e l, f i⟫_ℝ : Matrix (Fin d) (Fin d) ℝ)ᵀ * Matrix.of (fun l i => ⟪e l, f i⟫_ℝ) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  have h : ⟪f i, f j⟫_ℝ = ∑ l, ⟪e l, f i⟫_ℝ * ⟪e l, f j⟫_ℝ := by
    conv_lhs => rw [hexp j]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [inner_smul_right, mul_comm, real_inner_comm (e l) (f i)]
  rw [← h, hf, orthonormal_iff_ite.1 he, Matrix.one_apply]

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.InvBasis


open GlobalTheory.CompanionTheory.Hypotheses₂.HCA.InvBasis in
theorem GlobalTheory.CompanionTheory.Hypotheses₂.HCA.exists_basis_lieOf_orthogonal : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} (_hG : IsLinRed G), ∃ (d : ℕ) (b : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i, b i ∈ HCSS.lieOf G) ∧ LinearIndependent ℝ b ∧ (∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i) ∧ ∀ k ∈ maxCpt G, ∃ O : Matrix (Fin d) (Fin d) ℝ, Oᵀ * O = 1 ∧ ∀ i, k * b i * k⁻¹ = ∑ l, O l i • b l := by
  open GlobalTheory.CompanionTheory.Hypotheses₂.HCA.InvBasis in
    intro n G hG
    obtain ⟨hadd, hsmul, -, hAd⟩ := lieOf_isLieSubalgebra hG
    let L : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
      { carrier := HCSS.lieOf G
        add_mem' := fun {X Y} hX hY => hadd X Y hX hY
        zero_mem' := fun t => by simpa using hG.one_mem
        smul_mem' := fun r X hX => hsmul r X hX }
    let W : Submodule ℝ (EuclideanSpace ℂ (Fin n × Fin n)) := L.map (vecOf (n := n)).toLinearMap
    have : FiniteDimensional ℝ (EuclideanSpace ℂ (Fin n × Fin n)) :=
      FiniteDimensional.complexToReal _
    obtain ⟨d, e, heW, hon, hexp⟩ := exists_orthonormal W
    have hmemW : ∀ X ∈ HCSS.lieOf G, vecOf X ∈ W := fun X hX => ⟨X, hX, rfl⟩
    have hbL : ∀ i, vecOf.symm (e i) ∈ HCSS.lieOf G := by
      intro i
      obtain ⟨X, hX, hXe⟩ := heW i
      have : vecOf.symm (e i) = X := by
        rw [← hXe]; simp
      rw [this]; exact hX
    have hexpM : ∀ X ∈ HCSS.lieOf G, X = ∑ i, ⟪e i, vecOf X⟫_ℝ • vecOf.symm (e i) := by
      intro X hX
      have h := hexp _ (hmemW X hX)
      have h2 := congrArg (vecOf (n := n)).symm h

      rw [map_sum] at h2
      simpa using h2
    refine ⟨d, fun i => vecOf.symm (e i), hbL, ?_, ?_, ?_⟩
    · exact hon.linearIndependent.map' (vecOf (n := n)).symm.toLinearMap
        (LinearMap.ker_eq_bot.2 (vecOf (n := n)).symm.injective)
    · intro X hX
      exact ⟨_, hexpM X hX⟩
    · intro k hk
      have hkG : k ∈ G := hk.1
      have hkU : k ∈ Matrix.unitaryGroup (Fin n) ℂ := hk.2
      let f : Fin d → EuclideanSpace ℂ (Fin n × Fin n) := fun i => vecOf (k * vecOf.symm (e i) * k⁻¹)
      have hfW : ∀ i, f i ∈ W := fun i => hmemW _ (hAd k hkG _ (hbL i))
      have hO := orthogonal_of_preserves hon f (fun i => hexp _ (hfW i)) (fun i j => by
        have := inner_conj hkU (vecOf.symm (e i)) (vecOf.symm (e j))
        simpa [f] using this)
      refine ⟨_, hO, fun i => ?_⟩
      have h := hexp _ (hfW i)
      have h2 := congrArg (vecOf (n := n)).symm h

      rw [map_sum] at h2
      simpa [f] using h2

end
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.lie_algebra_of_linear_group_closed : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G), (∀ X Y, X ∈ HCSS.lieOf G → Y ∈ HCSS.lieOf G → X + Y ∈ HCSS.lieOf G) ∧ (∀ (r : ℝ) X, X ∈ HCSS.lieOf G → r • X ∈ HCSS.lieOf G) ∧ (∀ X Y, X ∈ HCSS.lieOf G → Y ∈ HCSS.lieOf G → X * Y - Y * X ∈ HCSS.lieOf G) ∧ (∀ k ∈ G, ∀ X ∈ HCSS.lieOf G, k * X * k⁻¹ ∈ HCSS.lieOf G) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

namespace GlobalTheory.CompanionTheory.HeckeBridge.GaussSum

variable {E : Type} [Field E] [NumberField E]

theorem dvd_conductor (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) {m : ℕ} (hm : m ≠ 0)
    (h : ExpAt χ v m) : v.asIdeal ∣ (toHecke χ hu).conductor := by
  by_contra hv
  refine h.not_unrAt hm fun x hx => ?_
  have hx' : Valued.v (x : v.adicCompletion E) = 1 := hx
  have hmem : x ∈ (Submonoid.ofClass (v.adicCompletionIntegers E)).units := by
    refine Submonoid.mem_units_iff _ _ |>.2 ⟨(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx'.le,
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_⟩
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx', inv_one]
  have h1 := (toHecke χ hu).localComponent_eq_one_of_not_dvd hv hmem
  have h2 := coe_localComponent χ hu v x
  rw [h1] at h2
  exact Units.ext (by simpa using h2.symm)

theorem hval (v : HeightOneSpectrum (𝓞 E)) (x : E) :
    Valued.v (algebraMap E (v.adicCompletion E) x) = v.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem valued_eq_one {v : HeightOneSpectrum (𝓞 E)} {y : 𝓞 E} (hy : y ∉ v.asIdeal) :
    Valued.v (algebraMap E (v.adicCompletion E) (y : E)) = 1 := by
  exact (hval v _).trans ((v.valuation_eq_one_iff_notMem (K := E)).2 hy)

theorem valued_ne_one {v : HeightOneSpectrum (𝓞 E)} {y : 𝓞 E} (hy : y ∈ v.asIdeal) :
    Valued.v (algebraMap E (v.adicCompletion E) (y : E)) ≠ 1 := by
  exact fun h => (v.valuation_eq_one_iff_notMem (K := E)).1 ((hval v _).symm.trans h) hy

theorem term_of_notMem (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E))
    (hv : v.asIdeal ∣ (toHecke χ hu).conductor) (c : Eˣ) {y : 𝓞 E} (hy : y ∉ v.asIdeal) :
    (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) (y : E)) *
        psiAt v (((atFin v c : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ * algebraMap E (v.adicCompletion E) (y : E)) =
      gaussTerm χ v c (y : E) := by
  have hy0 : (y : E) ≠ 0 := by
    intro h0
    have : y = 0 := by exact_mod_cast h0
    exact hy (this ▸ v.asIdeal.zero_mem)
  have h1 := (toHecke χ hu).finiteTest_of_dvd hv (atFin v (Units.mk0 (y : E) hy0)) (valued_eq_one hy)
  have h2 : ((atFin v (Units.mk0 (y : E) hy0) : (v.adicCompletion E)ˣ) : v.adicCompletion E) = algebraMap E (v.adicCompletion E) (y : E) := rfl
  rw [h2] at h1
  rw [h1, coe_localComponent, gaussTerm, dite_eq_right hy0, Units.val_inv_eq_inv_val]
  have h3 : ((atFin v c : (v.adicCompletion E)ˣ) : v.adicCompletion E) = algebraMap E (v.adicCompletion E) (c : E) := rfl
  rw [h3, map_div₀, div_eq_mul_inv, mul_comm (algebraMap E _ _)]
  rfl

theorem finiteTest_sum_eq_gaussSumAt (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ)
    (v : HeightOneSpectrum (𝓞 E)) (m : ℕ) (hm : m ≠ 0) (hE : ExpAt χ v m) :
    ∑ᶠ r : 𝓞 E ⧸ v.asIdeal ^ m, (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) *
      psiAt v (((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ *
        algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) =
      gaussSumAt χ v m (unif v ^ (m + diffExp v)) := by
  have hv := dvd_conductor χ hu v hm hE
  rw [gaussSumAt]
  have hG : ∀ y : (𝓞 E ⧸ v.asIdeal ^ m)ˣ, gaussTerm χ v (unif v ^ (m + diffExp v)) ((Quotient.out (y : 𝓞 E ⧸ v.asIdeal ^ m) : 𝓞 E) : E) =
      (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) ((Quotient.out (y : 𝓞 E ⧸ v.asIdeal ^ m) : 𝓞 E) : E)) *
      psiAt v (((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ *
        algebraMap E (v.adicCompletion E) ((Quotient.out (y : 𝓞 E ⧸ v.asIdeal ^ m) : 𝓞 E) : E)) :=
    fun y => (term_of_notMem χ hu v hv _ (out_notMem v hm y)).symm
  rw [finsum_congr hG, ← finsum_mem_range (g := ((↑) : (𝓞 E ⧸ v.asIdeal ^ m)ˣ → 𝓞 E ⧸ v.asIdeal ^ m)) Units.val_injective
    (f := fun r : 𝓞 E ⧸ v.asIdeal ^ m => (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) *
      psiAt v (((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ *
        algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E))), finsum_mem_def]
  refine finsum_congr fun r => ?_
  by_cases hr : r ∈ Set.range ((↑) : (𝓞 E ⧸ v.asIdeal ^ m)ˣ → 𝓞 E ⧸ v.asIdeal ^ m)
  · rw [Set.indicator_of_mem hr]
  · rw [Set.indicator_of_notMem hr]
    have hmem : (Quotient.out r : 𝓞 E) ∈ v.asIdeal := by
      by_contra hn
      have h1 := Ideal.Quotient.isUnit_mk_pow_of_notMem v.asIdeal (n := m) hn
      rw [Ideal.Quotient.mk_out] at h1
      exact hr ⟨h1.unit, rfl⟩
    rw [(toHecke χ hu).finiteTest_eq_zero_of_dvd hv (valued_ne_one hmem), zero_mul]

end GlobalTheory.CompanionTheory.HeckeBridge.GaussSum
end
end

section


theorem _root_.GlobalTheory.T.parabolic_induction_finite_length : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.InductionFiniteLength k := by
  first | exact @GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength | exact GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength | (intros; apply GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength <;> assumption)
end

section

open CategoryTheory MonoidalCategory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel NumberField IsDedekindDomain Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.Hypotheses₂

attribute [local instance 2000] Rep.hV2

theorem dualityFor_absGal (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (hK : FiniteDimensional ℚ_[p] K) (l : ℕ) [Fact l.Prime] (r : ℕ)
    (χ : (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) →* (ZMod (l ^ r))ˣ)
    (hχ : ∀ (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (ζ : PadicAlgCl p), ζ ^ (l ^ r) = 1 →
      σ ζ = ζ ^ ((χ σ : ZMod (l ^ r)).val))
    (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) M)
    (hrho : ContAction rho) : ReciprocityTheory.Neutral.Bridge.DualityFor χ rho hrho := by
  obtain ⟨hsep, _, _, hloc, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcField p K hK
  have hl : (l ^ r : ℕ) ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ r) := ⟨hl⟩
  have : CharZero K := algebraRat.charZero K
  have hn : ((l ^ r : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hl
  obtain ⟨e⟩ := nonempty_addEquiv_galRootsOfUnity (K := K) (Ksep := PadicAlgCl p) hn
  have hD : ∀ (g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (m : ZMod (l ^ r)),
      e.symm ((χ g : ZMod (l ^ r)) * m) =
        (galRootsOfUnity.{0} K (PadicAlgCl p) (l ^ r)).ρ g (e.symm m) := by
    intro g m
    have key : ∀ x : Additive (rootsOfUnity (l ^ r) (PadicAlgCl p)),
        (galRootsOfUnity.{0} K (PadicAlgCl p) (l ^ r)).ρ g x =
          (χ g : ZMod (l ^ r)).val • x := by
      intro x
      rw [galRootsOfUnity_ρ_apply]
      apply Additive.toMul.injective
      rw [toMul_ofMul, toMul_nsmul]
      apply Subtype.ext
      apply Units.ext
      rw [coe_galRootsOfUnityHom_apply, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val]
      refine hχ g _ ?_
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 x.toMul.2, Units.val_one]
    refine Eq.trans ?_ (key _).symm
    refine Eq.trans ?_ (map_nsmul e.symm _ m)
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
  exact PositivityTheory.LocalTateOrthogonality.Gcoh.tate_core PositivityTheory.LocalTateOrthogonality.Gcoh.gcRep PositivityTheory.LocalTateOrthogonality.Gcoh.gc0
    PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 (galRootsOfUnity.{0} K (PadicAlgCl p) (l ^ r))
    (localDualityHypotheses hn)
    (fun A _ _ hA => finite_cohomology_galois_top K (PadicAlgCl p) hn A hA 1)
    χ e.symm hD M rho hrho

theorem localTateDuality : ReciprocityTheory.Gal.LocalTateDuality := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ A rho v _ hA hrho
  obtain ⟨p, hp, hpv⟩ := exists_prime_mem_asIdeal v
  haveI : Fact p.Prime := ⟨hp⟩
  have hval : A.valuation ((p : ℕ) : Ω) < 1 := by
    have := (hA ((p : ℕ) : 𝓞 F)).2 hpv
    simpa using this
  obtain ⟨ι, h⟩ := ReciprocityTheory.Neutral.Cmp.exists_compat F A hval
  let E : ReciprocityTheory.Neutral.Cmp.GK F ι ≃ₜ* Dec (F := F) A := ReciprocityTheory.Neutral.Cmp.equiv h
  let χ : Dec (F := F) A →* (ZMod (l ^ r))ˣ := (cycMod F Ω l r).comp (Dec (F := F) A).subtype
  have hχ : ∀ (σ : ReciprocityTheory.Neutral.Cmp.GK F ι) (ζ : PadicAlgCl p), ζ ^ (l ^ r) = 1 →
      σ ζ = ζ ^ (((χ.comp (E : ReciprocityTheory.Neutral.Cmp.GK F ι →* Dec (F := F) A)) σ :
        (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
    intro σ ζ hζ
    have e1 := ReciprocityTheory.Neutral.Cmp.cycZ_res (F := F) ι l σ
    have e3 : (χ.comp (E : ReciprocityTheory.Neutral.Cmp.GK F ι →* Dec (F := F) A)) σ =
        Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom
          (cyclotomicCharacter (PadicAlgCl p) l (σ : PadicAlgCl p ≃+* PadicAlgCl p)) := by
      rw [← e1]
      rfl
    rw [e3]
    exact cyclotomicCharacter.spec (L := PadicAlgCl p) l (σ : PadicAlgCl p ≃+* PadicAlgCl p) ζ hζ
  have hD := dualityFor_absGal p (ReciprocityTheory.Neutral.Cmp.Kloc F ι)
    (ReciprocityTheory.Neutral.Cmp.finiteDimensional_Kloc ι) l r
    (χ.comp (E : ReciprocityTheory.Neutral.Cmp.GK F ι →* Dec (F := F) A)) hχ M
    (rho.comp (E : ReciprocityTheory.Neutral.Cmp.GK F ι →* Dec (F := F) A))
    (ReciprocityTheory.Neutral.Bridge.contAction_comp E hrho)
  exact ReciprocityTheory.Neutral.Bridge.DualityFor.of_comp E χ hrho hD

end GlobalTheory.CompanionTheory.Hypotheses₂
end
