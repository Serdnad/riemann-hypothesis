module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle021
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle102
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle046
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle103
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimeDvdNotUnit
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle104
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle101
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle084
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

open PositivityTheory.Rg.Mass HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LatFix

section Gen

variable {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]

theorem repr_mul {d : ℕ} (b : Module.Basis (Fin d) F E) (x y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (x * y) k =
      ∑ i, ∑ j, (Algebra.TensorProduct.basis R b).repr x i *
        (Algebra.TensorProduct.basis R b).repr y j * algebraMap F R (b.repr (b i * b j) k) := by
  classical
  set B := Algebra.TensorProduct.basis R b with hB
  conv_lhs => rw [← B.sum_repr x, ← B.sum_repr y]

  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul,
  Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hB, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.basis_repr_tmul]
  simp

end Gen

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem eventually_integral (c : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      algebraMap F (Fv F v) c ∈ v.adicCompletionIntegers F := by
  exact (algebraMap F (FiniteAdeleRing (𝓞 F) F) c).2

theorem eventually_mul_closed {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ x y : Fv F v ⊗[F] E,
      (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr x k ∈ v.adicCompletionIntegers F) →
      (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) →
      ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (x * y) k ∈
        v.adicCompletionIntegers F := by
  classical
  have h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ i j k : Fin d,
      algebraMap F (Fv F v) (b.repr (b i * b j) k) ∈ v.adicCompletionIntegers F := by
    simp only [Filter.eventually_all]
    exact fun i j k => eventually_integral _
  filter_upwards [h] with v hv x y hx hy k
  rw [repr_mul]
  exact sum_mem fun i _ => sum_mem fun j _ => mul_mem (mul_mem (hx i) (hy j)) (hv i j k)

end Adelic

end GlobalTheory.CompanionTheory.SW.LatFix
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.Mass.MeanV

theorem eventually_valued_algebraMap_eq_one (F : Type) [Field F] [NumberField F] (β : F) (hβ : β ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v (algebraMap F (Fv F v) β) = 1 := by
  rw [Filter.eventually_cofinite]
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) β).union
    (HeightOneSpectrum.Support.finite (𝓞 F) β⁻¹)).subset ?_
  intro v hv
  have e : Valued.v (algebraMap F (Fv F v) β) = v.valuation F β :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) β
  rw [Set.mem_ofPred_eq, e] at hv
  rcases lt_or_gt_of_ne hv with h | h
  · refine Set.mem_union_right _ ?_
    show 1 < v.valuation F β⁻¹
    exact ((v.valuation F).one_lt_val_iff (inv_ne_zero hβ)).mpr (by rwa [inv_inv])
  · exact Set.mem_union_left _ h

theorem multipliable_localFactors :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), (∀ v, v ∉ S → ∀ s : Fv F v, Valued.v s = 1 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) → ∀ β : F, β ≠ 0 → Multipliable fun v => g v (algebraMap F (Fv F v) β) := by
  intro F _ _ S C g hg β hβ
  have hsum : Summable fun v : HeightOneSpectrum (𝓞 F) => C * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) :=
    (GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F).mul_left C
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ‖g v (algebraMap F (Fv F v) β) - 1‖ ≤ C * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) := by
    filter_upwards [eventually_valued_algebraMap_eq_one F β hβ,
      Set.Finite.compl_mem_cofinite S.finite_toSet] with v hv hvS
    rw [Real.norm_eq_abs, mul_one_div]
    exact hg v hvS _ hv
  have hf : Summable fun v : HeightOneSpectrum (𝓞 F) => g v (algebraMap F (Fv F v) β) - 1 :=
    Summable.of_norm_bounded_eventually hsum hev
  simpa using Real.multipliable_one_add_of_summable hf

end GlobalTheory.CompanionTheory.Mass.MeanV
end

section

namespace GlobalTheory.CompanionTheory.Counting

theorem card_comap_mul_card_ker_mul_card_eq :
    ∀ (n : ℕ) [NeZero n] (H H' P P' : Type) [AddCommGroup H] [Module (ZMod n) H] [Finite H] [AddCommGroup H'] [Module (ZMod n) H'] [Finite H'] [AddCommGroup P] [Module (ZMod n) P] [Finite P] [AddCommGroup P'] [Module (ZMod n) P'] [Finite P'] (B : P' →ₗ[ZMod n] P →ₗ[ZMod n] ZMod n), Function.Injective B → Function.Injective B.flip → ∀ (loc : H →ₗ[ZMod n] P) (loc' : H' →ₗ[ZMod n] P'), LinearMap.range loc = (⨅ y ∈ LinearMap.range loc', LinearMap.ker (B y)) → ∀ L : Submodule (ZMod n) P, Nat.card ↥(L.comap loc) * Nat.card ↥(LinearMap.ker loc') * Nat.card P = Nat.card ↥((⨅ x ∈ L, LinearMap.ker (B.flip x)).comap loc') * Nat.card H * Nat.card ↥L := by
  intro n _ H H' P P' _ _ _ _ _ _ _ _ _ _ _ _ B hB hB' loc loc' hR L
  have e1 := card_comap_eq_card_ker_mul_card_range_inf (ZMod n) H P loc L
  have e2 := card_comap_eq_card_ker_mul_card_range_inf (ZMod n) H' P' loc'
    (⨅ x ∈ L, LinearMap.ker (B.flip x))
  have e3 := card_eq_card_ker_mul_card_range (ZMod n) H P loc
  have hflip : B.flip.flip = B := LinearMap.flip_flip B
  have hdd := GlobalTheory.T.double_annihilator_eq_self n P' P B.flip hB' (by rw [hflip]; exact hB) (LinearMap.range loc')
  rw [hflip, ← hR] at hdd
  have e4 := GlobalTheory.T.annihilator_intersection_card n P P' B hB hB' (LinearMap.range loc) L
  rw [hdd] at e4
  rw [e1, e2, e3]
  have key : Nat.card ↥(LinearMap.ker loc) * Nat.card ↥(LinearMap.ker loc') *
      (Nat.card P * Nat.card ↥(LinearMap.range loc ⊓ L)) =
      Nat.card ↥(LinearMap.ker loc) * Nat.card ↥(LinearMap.ker loc') *
      (Nat.card ↥(LinearMap.range loc' ⊓ ⨅ x ∈ L, LinearMap.ker (B.flip x)) *
        Nat.card ↥(LinearMap.range loc) * Nat.card ↥L) := by
    rw [e4]
  linarith [key]

end GlobalTheory.CompanionTheory.Counting
end

section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

theorem _root_.GlobalTheory.T.additive_character_sum_orthogonality : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ) (ψ₀ : AddChar K ℂ), ψ₀ ≠ 1 → ∀ x : Fin j → K,
    (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹) = if x = 0 then (Fintype.card K : ℂ) ^ j else 0 := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.Orth.orth | exact GlobalTheory.CompanionTheory.TyFin.Orth.orth | (intros; apply GlobalTheory.CompanionTheory.TyFin.Orth.orth <;> assumption)
end

section


theorem _root_.GlobalTheory.T.continuous_unitary_multiplicative_eq_arg_pow : ∀ φ : ℂ → ℂ, (∀ z w : ℂ, z ≠ 0 → w ≠ 0 → φ (z * w) = φ z * φ w) → ContinuousOn φ {z : ℂ | z ≠ 0} → (∀ z : ℂ, z ≠ 0 → ‖φ z‖ = 1) → (∀ r : ℝ, 0 < r → φ (r : ℂ) = 1) → ∃ k : ℤ, ∀ z : ℂ, z ≠ 0 → φ z = (z / (‖z‖ : ℂ)) ^ k := by
  first | exact @GlobalTheory.CompanionTheory.KlocOp.cstar_char_eq_zpow | exact GlobalTheory.CompanionTheory.KlocOp.cstar_char_eq_zpow | (intros; apply GlobalTheory.CompanionTheory.KlocOp.cstar_char_eq_zpow <;> assumption)
end

section

open scoped Matrix SchwartzMap

theorem _root_.GlobalTheory.T.schwartz_quadratic_phase_multiplication : ∀ (m n : ℕ) (k : ℝ) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b → ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ⇑ψ = fun u => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) * φ u := by
  first | exact @GlobalTheory.CompanionTheory.QuadChirp.exists_schwartz_chirp_mul | exact GlobalTheory.CompanionTheory.QuadChirp.exists_schwartz_chirp_mul | (intros; apply GlobalTheory.CompanionTheory.QuadChirp.exists_schwartz_chirp_mul <;> assumption)
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix


theorem _root_.GlobalTheory.T.ideal_principal_element_norm_bound : ∀ (E : Type) [Field E] [NumberField E], ∃ C : ℝ, 0 < C ∧ ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ t ∈ 𝔞, t ≠ 0 ∧ (Ideal.absNorm (Ideal.span {t}) : ℝ) ≤ C * Ideal.absNorm 𝔞 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink.exists_ne_zero_mem_absNorm_le | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink.exists_ne_zero_mem_absNorm_le | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink.exists_ne_zero_mem_absNorm_le <;> assumption)
end

section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

theorem _root_.GlobalTheory.T.GL_transitive_nonzero_vectors : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ) (r r' : Fin j → K), r ≠ 0 → r' ≠ 0 →
    ∃ g : GL (Fin j) K, Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K) = r' := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.RowTrans.gl_transitive_rows | exact GlobalTheory.CompanionTheory.TyFin.RowTrans.gl_transitive_rows | (intros; apply GlobalTheory.CompanionTheory.TyFin.RowTrans.gl_transitive_rows <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SmGL

theorem exists_compact_open_subgroup_subset (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k),
      IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧
        (K : Set (GL (Fin n) k)) ⊆ U := by
  intro U hU
  obtain ⟨J, hJo, hJU, hJK, -⟩ := exists_open_normalised_subgroup_subset k (Fin n) U hU
  exact ⟨J, hJo, (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin n)).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ hJo) hJK, hJU⟩

end GlobalTheory.CompanionTheory.SmGL
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Counting


open GroundTheory.Automorphic.CuspidalSpectrum in
theorem exists_ncard_entrywiseBox_le (K : Type) [Field K] [NumberField K] (n : ℕ)
    (𝒦 : Set (FiniteAdeleRing (𝓞 K) K)) (h𝒦 : IsCompact 𝒦) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : Fin n → Fin n → ℝ, (∀ i j, 0 ≤ T i j) →
      (setOf fun γ : GL (Fin n) K => (∀ i j,
        algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) ∈ 𝒦 ∧
        ∀ w : InfinitePlace K, w ((γ : Matrix (Fin n) (Fin n) K) i j) ≤ T i j)).Finite ∧
      ((Set.ncard (setOf fun γ : GL (Fin n) K => (∀ i j,
        algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) ∈ 𝒦 ∧
        ∀ w : InfinitePlace K, w ((γ : Matrix (Fin n) (Fin n) K) i j) ≤ T i j)) : ℕ) : ℝ) ≤
        ∏ i, ∏ j, C * (1 + T i j) ^ Module.finrank ℚ K := by
  obtain ⟨m, hm, hint⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_natCast_mul_integral_of_isCompact K h𝒦
  obtain ⟨C₀, hC₀, hcount⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_ncard_integers_le K
  have hw : ∀ (w : InfinitePlace K) (x : K), w ((m : K) * x) = (m : ℝ) * w x := by
    intro w x
    rw [← w.norm_embedding_eq, map_mul, norm_mul, w.norm_embedding_eq, w.norm_embedding_eq, w.map_natCast]
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmK : (m : K) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨C₀ * (m : ℝ) ^ Module.finrank ℚ K, mul_nonneg hC₀ (by positivity), ?_⟩
  intro T hT
  have hA : ∀ p : Fin n × Fin n,
      (((↑) : 𝓞 K → K) '' {z | ∀ w : InfinitePlace K, w (z : K) ≤ (m : ℝ) * T p.1 p.2}).Finite ∧
      ((((↑) : 𝓞 K → K) '' {z | ∀ w : InfinitePlace K, w (z : K) ≤ (m : ℝ) * T p.1 p.2}).ncard : ℝ) ≤
        C₀ * (1 + (m : ℝ) * T p.1 p.2) ^ Module.finrank ℚ K := by
    intro p
    obtain ⟨hf, hc⟩ := hcount ((m : ℝ) * T p.1 p.2) (mul_nonneg (by positivity) (hT p.1 p.2))
    exact ⟨hf.image _, le_trans (by exact_mod_cast Set.ncard_image_le hf) hc⟩
  let F : GL (Fin n) K → (Fin n × Fin n → K) := fun γ p => (m : K) * (γ : Matrix (Fin n) (Fin n) K) p.1 p.2
  obtain ⟨t, ht⟩ : ∃ t : Finset (Fin n × Fin n → K), t = Fintype.piFinset fun p => (hA p).1.toFinset := ⟨_, rfl⟩
  have key : ∀ γ : GL (Fin n) K, (∀ i j, algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) ∈ 𝒦 ∧
      ∀ w : InfinitePlace K, w ((γ : Matrix (Fin n) (Fin n) K) i j) ≤ T i j) → F γ ∈ (t : Set (Fin n × Fin n → K)) := by
    intro γ hγ
    rw [Finset.mem_coe, ht, Fintype.mem_piFinset]
    intro p
    rw [Set.Finite.mem_toFinset]
    obtain ⟨z, hz⟩ := hint _ (hγ p.1 p.2).1
    refine ⟨z, fun w => ?_, hz⟩
    rw [hz, hw]
    exact mul_le_mul_of_nonneg_left ((hγ p.1 p.2).2 w) (by positivity)
  have inj : ∀ γ γ' : GL (Fin n) K, F γ = F γ' → γ = γ' := by
    intro γ γ' h
    ext i j
    exact mul_left_cancel₀ hmK (congrFun h (i, j))
  refine ⟨?_, ?_⟩
  · exact Set.Finite.of_finite_image ((t.finite_toSet).subset (Set.image_subset_iff.mpr fun γ hγ => key γ hγ))
      (fun γ _ γ' _ h => inj γ γ' h)
  · refine le_trans (Nat.cast_le.mpr (Set.ncard_le_ncard_of_injOn F (fun γ hγ => key γ hγ)
      (fun γ _ γ' _ h => inj γ γ' h) t.finite_toSet)) ?_
    rw [Set.ncard_coe_finset, ht, Fintype.card_piFinset, Nat.cast_prod, Fintype.prod_prod_type]
    apply Finset.prod_le_prod₀ (fun _ _ => Finset.prod_nonneg fun _ _ => by positivity)
    intro i _
    apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
    intro j _
    rw [← Set.ncard_eq_toFinset_card _ (hA (i, j)).1]
    refine le_trans (hA (i, j)).2 ?_
    rw [mul_assoc, ← mul_pow]
    apply mul_le_mul_of_nonneg_left _ hC₀
    apply pow_le_pow_left₀ (by nlinarith [hT i j])
    nlinarith [hT i j]

end GlobalTheory.CompanionTheory.Counting
end

section

set_option backward.isDefEq.respectTransparency false
open MvPolynomial

namespace GlobalTheory.CompanionTheory.TraceJac

theorem det_completed_eq_minor {L : Type*} [Field L] {d m : ℕ} (κ : Fin m ↪ Fin d)
    (E : Fin d → L → L) (τ : Fin d → L) (hE : ∀ k j, E k (τ j) = if k = j then 1 else 0)
    (β : Fin m → L) :
    let e : Fin m ⊕ ↥(Set.range κ)ᶜ ≃ Fin d :=
      (Equiv.sumCongr (Equiv.ofInjective κ κ.injective) (Equiv.refl _)).trans
        (Equiv.Set.sumCompl (Set.range κ))
    (Matrix.of fun k l => E k ((Sum.elim β (fun j : ↥(Set.range κ)ᶜ => τ j)) (e.symm l))).det =
      (Matrix.of fun k l => E (κ k) (β l)).det := by
  classical
  intro e
  have he1 : ∀ i, e (Sum.inl i) = κ i := fun i => by simp [e]
  have he2 : ∀ j : ↥(Set.range κ)ᶜ, e (Sum.inr j) = j := fun j => by simp [e]
  rw [← Matrix.det_submatrix_equiv_self e]
  have hblock : (Matrix.of fun k l =>
      E k ((Sum.elim β (fun j : ↥(Set.range κ)ᶜ => τ j)) (e.symm l))).submatrix e e =
      Matrix.fromBlocks (Matrix.of fun k l => E (κ k) (β l)) 0
        (Matrix.of fun (j : ↥(Set.range κ)ᶜ) l => E j (β l)) 1 := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Equiv.symm_apply_apply]
    rcases x with i | j <;> rcases y with i' | j'
    · simp [he1]
    · have hne : κ i ≠ (j' : Fin d) := fun h => j'.2 ⟨i, h⟩
      simp [he1, hE, hne]
    · simp [he2]
    · have : ((j : Fin d) = j') ↔ j = j' := Subtype.ext_iff.symm
      simp [he2, hE, Matrix.one_apply, this]
  rw [hblock, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]

theorem trace_minor_mem : ∀ (K : Type) [Field K] [CharZero K] (d : ℕ) (A : Type) [CommRing A] [IsDomain A] [Algebra K A] (t : Fin d → A), Function.Injective (MvPolynomial.aeval t : MvPolynomial (Fin d) K →ₐ[K] A) → (∀ a : A, ∃ f g : MvPolynomial (Fin d) K, IsUnit (MvPolynomial.aeval t g) ∧ a * MvPolynomial.aeval t g = MvPolynomial.aeval t f) → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [Module.Finite A B], Function.Injective (algebraMap A B) → ∀ (F L : Type) [Field F] [Field L] [Algebra A F] [IsFractionRing A F] [Algebra B L] [IsFractionRing B L] [Algebra F L] [Algebra A L] [IsScalarTower A F L] [IsScalarTower A B L] [Algebra K L] [IsScalarTower K B L] (D : Fin d → Derivation K L L), (∀ k j, D k (algebraMap A L (t j)) = if k = j then 1 else 0) → ∀ (m : ℕ) (κ : Fin m ↪ Fin d) (c : B) (b : Fin m → B), ∃ a : A, algebraMap A F a = Algebra.trace F L (algebraMap B L c * (Matrix.of fun k l => D (κ k) (algebraMap B L (b l))).det) := by
  intro K _ _ d A _ _ _ t ht hloc B _ _ _ _ _ _ hB F L _ _ _ _ _ _ _ _ _ _ _ _ D hD m κ c b
  classical
  let e : Fin m ⊕ ↥(Set.range κ)ᶜ ≃ Fin d :=
    (Equiv.sumCongr (Equiv.ofInjective κ κ.injective) (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range κ))
  let b' : Fin d → B := fun l =>
    (Sum.elim b (fun j : ↥(Set.range κ)ᶜ => algebraMap A B (t j))) (e.symm l)
  obtain ⟨a, ha⟩ := trace_jacobian_mem K d A t ht hloc B hB F L D hD c b'
  refine ⟨a, ha.trans ?_⟩
  have hdet := det_completed_eq_minor κ (fun k x => D k x) (fun j => algebraMap A L (t j)) hD
    (fun l => algebraMap B L (b l))
  have hmat : (Matrix.of fun k l => D k (algebraMap B L (b' l))) =
      Matrix.of fun k l => D k ((Sum.elim (fun l => algebraMap B L (b l))
        (fun j : ↥(Set.range κ)ᶜ => algebraMap A L (t j))) (e.symm l)) := by
    ext k l
    simp only [Matrix.of_apply, b']
    rcases e.symm l with i | j
    · simp
    · simp [← IsScalarTower.algebraMap_apply A B L]
  rw [hmat]
  exact congrArg (fun x => Algebra.trace F L (algebraMap B L c * x)) hdet

end GlobalTheory.CompanionTheory.TraceJac
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix


theorem _root_.GlobalTheory.T.tsum_comp_bounded_fibres_le : ∀ (A B : Type) (π : A → B) (k : ℕ), (∀ b, Finite {a // π a = b} ∧ Nat.card {a // π a = b} ≤ k) → ∀ (g : B → ℝ), (∀ b, 0 ≤ g b) → Summable g → Summable (fun a => g (π a)) ∧ ∑' a, g (π a) ≤ k * ∑' b, g b := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumFibre.summable_comp_of_bounded_fibres | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumFibre.summable_comp_of_bounded_fibres | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumFibre.summable_comp_of_bounded_fibres <;> assumption)
end
