module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle457
import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentForm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentMatrix
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureExtensionByScalar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle460
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle437
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle462
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle469
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle444
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle463
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle449
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle061
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core


theorem _root_.GlobalTheory.T.delta_conj_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (c : Matrix (Fin n) (Fin n) E), delta (c.map σ) = delta c := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap.delta_map | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap.delta_map | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap.delta_map <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core


theorem _root_.GlobalTheory.T.delta_ne_zero' : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (c : Matrix (Fin n) (Fin n) E),
    delta c ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Fin.delta_pos_index | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Fin.delta_pos_index | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Fin.delta_pos_index <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.siegelWeilFree_of_congruent_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (g : GL (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), J' = cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * g → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), SWFree σ J' T hT → SWFree σ J T hT := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.Iso.swFree_of_isometry | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.Iso.swFree_of_isometry | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.Iso.swFree_of_isometry <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.siegelWeilFree_of_congruent_matrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (g : GL (Fin n) E) (T' : Matrix (Fin n) (Fin n) E) (hT' : ∀ a b, σ (T' b a) = T' a b), T' = cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * T * g → SWFree σ J T' hT' → SWFree σ J T hT := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.sw_free_scale | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.sw_free_scale | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.sw_free_scale <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.theta_measure_extension_by_scalar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (μ : Measure (HA (AF F) σ (blockOne (algebraMap F E t) J))) 𝓕, IsHaarH F E σ (M + 1) _ μ → IsFDH F E σ (M + 1) _ μ 𝓕 → ∀ (μ₁ : Measure (HA (AF F) σ J)) 𝓕₁, IsHaarH F E σ M J μ₁ → IsFDH F E σ M J μ₁ 𝓕₁ → ∀ (Φ : (Fin (n + 1) → Fin (M + 1) → AF F ⊗[F] E) → ℝ≥0∞) (Ψ : (Fin 1 → Fin (M + 1) → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → Measurable Ψ → (∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J), Ψ (actW (AF F) σ _ h (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, Φ (actW (AF F) σ _ h (consTup X)) ∂(thetaMeas σ J μ₁ 𝓕₁ (framesE σ J T))) → ∫⁻ X, Φ X ∂(thetaMeas σ _ μ 𝓕 (framesE σ (blockOne (algebraMap F E t) J) (blockOne (algebraMap F E t) T))) = ∫⁻ y, Ψ y ∂(thetaMeas σ _ μ 𝓕 {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t}) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.FrameTheta.theta_stage_frames | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.FrameTheta.theta_stage_frames | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.FrameTheta.theta_stage_frames <;> assumption)
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.covolume_one_column_join_product : ∀ (D : D7) (m r s : ℕ) (μr : Measure (Mx D m r)) (𝓕r : Set (Mx D m r)) (μs : Measure (Mx D m s))
    (𝓕s : Set (Mx D m s)), IsCovolOne (ratMx D m r) μr 𝓕r → IsCovolOne (ratMx D m s) μs 𝓕s →
    IsCovolOne (ratMx D m (r + s)) ((μr.prod μs).map fun z => colJoin z.1 z.2)
      ((fun z : Mx D m r × Mx D m s => colJoin z.1 z.2) '' (𝓕r ×ˢ 𝓕s)) := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.ProdCovol.isCovolOne_colJoin | exact GlobalTheory.CompanionTheory.EisUnfold.ProdCovol.isCovolOne_colJoin | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.ProdCovol.isCovolOne_colJoin <;> assumption)
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.sharp_epsilon_root_idempotent_sum : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l) (ρ : ℕ → ((base l).cont ℤ_[l]).A),
  (∀ (m : ℕ) (z : ℤ_[l]), Hom.f ((base l).evCont z) (ρ 0) - (base l).s (ε.e 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {(base l).pi ^ (l ^ m)}) →
  (∀ m, ρ (m + 1) ^ l = ρ m) → ∀ m, ((base l).cont ℤ_[l]).sharp (ρ m) =
    ∑ c : ZMod (l ^ m), ((base l).cont ℤ_[l]).sharp (GlobalTheory.CompanionTheory.ContUniv.ind (base l) m c) *
      ((base l).cont ℤ_[l]).sharp (((base l).cont ℤ_[l]).s (ε.e m)) ^ c.val := by
  first | exact @GlobalTheory.CompanionTheory.ContUniv.sharp_roots_universal | exact GlobalTheory.CompanionTheory.ContUniv.sharp_roots_universal | (intros; apply GlobalTheory.CompanionTheory.ContUniv.sharp_roots_universal <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

theorem coi_eq_of_mul_eq_zero {R I : Type} [CommRing R] [Fintype I] {e e' : I → R}
    (h : CompleteOrthogonalIdempotents e) (h' : CompleteOrthogonalIdempotents e')
    (hz : ∀ c c', c ≠ c' → e c * e' c' = 0) : e = e' := by
  classical
  funext c
  have h1 : e c = e c * e' c := by
    calc e c = e c * ∑ b, e' b := by rw [h'.complete, mul_one]
      _ = e c * e' c := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_single c (fun b _ hb => hz c b hb.symm) (by simp)
  have h2 : e' c = e c * e' c := by
    calc e' c = (∑ b, e b) * e' c := by rw [h.complete, one_mul]
      _ = e c * e' c := by
        rw [Finset.sum_mul]
        exact Finset.sum_eq_single c (fun b _ hb => hz b c hb) (by simp)
  rw [h1, ← h2]

theorem one_sub_pow_dvd {O : Type} [CommRing O] [IsDomain O] {ζ : O} {n d : ℕ}
    (hζ : IsPrimitiveRoot ζ n) (hd : 0 < d) (hdn : d < n) : 1 - ζ ^ d ∣ (n : O) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h := hζ.prod_one_sub_pow_eq_order
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
  have hd' : (1 - ζ ^ (j + 1)) ∣ ∏ i ∈ Finset.range k, (1 - ζ ^ (i + 1)) :=
    Finset.dvd_prod_of_mem (fun i => 1 - ζ ^ (i + 1)) (Finset.mem_range.2 (by omega))
  rw [h] at hd'
  simpa using hd'

theorem pow_sub_pow_dvd {O : Type} [CommRing O] [IsDomain O] {ζ : O} {n a b : ℕ}
    (hζ : IsPrimitiveRoot ζ n) (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    ζ ^ a - ζ ^ b ∣ (n : O) := by
  have hu : ∀ i : ℕ, IsUnit (ζ ^ i) := fun i =>
    (hζ.isUnit (by omega)).pow i
  have key : ∀ {a b : ℕ}, a < b → b < n → ζ ^ a - ζ ^ b ∣ (n : O) := by
    intro a b h1 h2
    have e : ζ ^ a - ζ ^ b = ζ ^ a * (1 - ζ ^ (b - a)) := by
      rw [mul_sub, mul_one, ← pow_add]
      congr 2
      omega
    rw [e]
    exact (hu a).mul_left_dvd.2 (one_sub_pow_dvd hζ (by omega) (by omega))
  rcases lt_or_gt_of_ne hab with h | h
  · exact key h hb
  · rw [← neg_sub, neg_dvd]
    exact key h ha

theorem mul_eq_zero_of_pow {O U : Type} [CommRing O] [IsDomain O] [CommRing U] (g : O →+* U)
    {ζ : O} {n a b : ℕ} (hζ : IsPrimitiveRoot ζ n) (ha : a < n) (hb : b < n) (hab : a ≠ b)
    (hn : (n : U) ∈ nonZeroDivisors U) {x S S' : U}
    (h : S * (x - g ζ ^ a) = 0) (h' : S' * (x - g ζ ^ b) = 0) : S * S' = 0 := by
  obtain ⟨w, hw⟩ := pow_sub_pow_dvd hζ ha hb hab
  have e : (n : U) = (g ζ ^ a - g ζ ^ b) * g w := by
    rw [← map_natCast g, hw, map_mul, map_sub, map_pow, map_pow]
  have h0 : S * S' * (g ζ ^ a - g ζ ^ b) = 0 := by
    linear_combination S * h' * 1 - S' * h
  have h1 : (S * S') * (n : U) = 0 := by
    rw [e, ← mul_assoc, h0, zero_mul]
  exact (mem_nonZeroDivisors_iff_right.1 hn) _ h1

variable {l : ℕ} [Fact l.Prime]

theorem sharp_s_eq (t : PAlg l) (x : Ob l) :
    t.sharp (t.s x) = t.oC (theta0 l (WittVector.teichmuller l x)) := by
  rw [oC_theta0, sW, WittVector.map_teichmuller]
  rfl

theorem eq_zero_of_sharp (t : PAlg l) {e : t.A} (he : IsIdempotentElem e) (h : t.sharp e = 0) :
    e = 0 :=
  (RL.idem_au t 0 IsIdempotentElem.zero).unique ⟨he, h⟩ ⟨IsIdempotentElem.zero, sharp_zero t⟩

theorem idem_unique : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l) (t : PAlg l) (m : ℕ) (x : t.U)
    (e e' : ZMod (l ^ m) → t.A),
    CompleteOrthogonalIdempotents e → CompleteOrthogonalIdempotents e' →
    (∀ c, t.sharp (e c) * (x - t.sharp (t.s (ε.e m)) ^ c.val) = 0) →
    (∀ c, t.sharp (e' c) * (x - t.sharp (t.s (ε.e m)) ^ c.val) = 0) → e = e' := by
  intro l _ ε t m x e e' he he' h h'
  have hζ := (GlobalTheory.T.epsilon_cyclotomic_element_properties ε).2.2.2.2 m
  refine coi_eq_of_mul_eq_zero he he' fun c c' hc => ?_
  have hn : ((l ^ m : ℕ) : t.U) ∈ nonZeroDivisors t.U := by
    rw [Nat.cast_pow]
    exact pow_mem t.l_mem_nzd_U m
  have h1 := h c
  have h2 := h' c'
  rw [sharp_s_eq] at h1 h2
  have h3 := mul_eq_zero_of_pow t.oC hζ (ZMod.val_lt c) (ZMod.val_lt c')
    (fun hv => hc (ZMod.val_injective _ hv)) hn h1 h2
  refine eq_zero_of_sharp t ((he.idem c).mul (he'.idem c')) ?_
  rw [map_mul, h3]

end GlobalTheory.CompanionTheory.ContUniv
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.singular_hermitian_congruent_block_normal_form : ∀ (D : D7) (r : ℕ) (β : HermE D r), β.1.det = 0 → ∃ (a : Matrix (Fin r) (Fin r) D.host.E) (t : ℕ) (γ : HermE D r), a.det ≠ 0 ∧ GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t γ ∧ β = GlobalTheory.CompanionTheory.WeilSiegel.Deg.congrH a γ := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Deg.exists_congrH_isBlockNF | exact GlobalTheory.CompanionTheory.WeilSiegel.Deg.exists_congrH_isBlockNF | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Deg.exists_congrH_isBlockNF <;> assumption)
end

section

open Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.PairMult

variable {n : ℕ}

def AdFamL (lev : Fin n → ℕ) {ι : Type} [Fintype ι] (w : ι → FreeAlgebra ℂ (Bool × Fin n × Fin n))
    (M : Fin n → Fin n → Matrix ι ι ℂ) : Prop :=
  (∀ c d i j, star (M c d j i) = M d c i j) ∧
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (X1 X2 : Fin n → Fin n → Module.End ℂ W), LRel lev X1 X2 →
    ∀ c d, lev c = lev d → ∀ i, (X1 c d + X2 c d) * evB lev X1 X2 (w i) - evB lev X1 X2 (w i) * (X1 c d + X2 c d) =
      ∑ j, M c d j i • evB lev X1 X2 (w j)

theorem ad_letter {lev : Fin n → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] {X1 X2 : Fin n → Fin n → Module.End ℂ W}
    (hX : LRel lev X1 X2) {c d : Fin n} (hcd : lev c = lev d) (s : Bool) (a b : Fin n) :
    (X1 c d + X2 c d) * evB lev X1 X2 (FreeAlgebra.ι ℂ (s, a, b)) -
        evB lev X1 X2 (FreeAlgebra.ι ℂ (s, a, b)) * (X1 c d + X2 c d) =
      (if d = a then evB lev X1 X2 (FreeAlgebra.ι ℂ (s, c, b)) else 0) -
        (if b = c then evB lev X1 X2 (FreeAlgebra.ι ℂ (s, a, d)) else 0) := by
  obtain ⟨h1, h2, h3⟩ := hX
  simp only [evB, FreeAlgebra.lift_ι_apply]
  by_cases hab : lev a = lev b
  · have e1 : d = a → lev c = lev b := fun h => by rw [hcd, h, hab]
    have e2 : b = c → lev a = lev d := fun h => by rw [hab, h, hcd]
    have k1 : (if d = a then (if lev c = lev b then (if s = true then X1 c b else X2 c b) else 0) else 0) =
        if d = a then (if s = true then X1 c b else X2 c b) else 0 := by
      split_ifs with h h' <;> first | rfl | exact absurd (e1 h) h'
    have k2 : (if b = c then (if lev a = lev d then (if s = true then X1 a d else X2 a d) else 0) else 0) =
        if b = c then (if s = true then X1 a d else X2 a d) else 0 := by
      split_ifs with h h' <;> first | rfl | exact absurd (e2 h) h'
    rw [k1, k2, if_pos hab]
    cases s
    · have e := h2 c d a b hcd hab
      have k := (h3 c d a b hcd hab).eq
      simp only [Bool.false_eq_true, if_false, add_mul, mul_add]
      rw [k, ← e]
      abel
    · have e := h1 c d a b hcd hab
      have k := (h3 a b c d hab hcd).eq
      simp only [if_true, add_mul, mul_add]
      rw [k, ← e]
      abel
  · have e1 : d = a → ¬ lev c = lev b := fun h => by rw [hcd, h]; exact hab
    have e2 : b = c → ¬ lev a = lev d := fun h => by rw [← hcd, ← h]; exact hab
    have k1 : (if d = a then (if lev c = lev b then (if s = true then X1 c b else X2 c b) else 0) else 0) = 0 := by
      split_ifs with h h' <;> first | rfl | exact absurd h' (e1 h)
    have k2 : (if b = c then (if lev a = lev d then (if s = true then X1 a d else X2 a d) else 0) else 0) = 0 := by
      split_ifs with h h' <;> first | rfl | exact absurd h' (e2 h)
    rw [k1, k2, if_neg hab]
    simp

theorem exists_adFamL (lev : Fin n → ℕ) (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → FreeAlgebra ℂ (Bool × Fin n × Fin n)) (M : Fin n → Fin n → Matrix ι ι ℂ)
      (t : ι → ℂ), AdFamL lev w M ∧ a = ∑ i, t i • w i := by
  classical
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    refine ⟨Unit, inferInstance, fun _ => 1, fun _ _ => 0, fun _ => r, ⟨?_, ?_⟩, ?_⟩
    · intro c d i j; simp
    · intro W _ _ X1 X2 _ c d _ i; simp
    · simp [Algebra.algebraMap_eq_smul_one]
  | grade1 x =>
    refine ⟨Bool × Fin n × Fin n, inferInstance, fun p => FreeAlgebra.ι ℂ p,
      fun c d => Matrix.of fun j i => (if d = i.2.1 ∧ j = (i.1, c, i.2.2) then 1 else 0) -
        (if i.2.2 = c ∧ j = (i.1, i.2.1, d) then 1 else 0),
      Pi.single x 1, ⟨?_, ?_⟩, ?_⟩
    · rintro c d ⟨s, i1, i2⟩ ⟨t, j1, j2⟩
      simp only [Matrix.of_apply, star_sub, Prod.mk.injEq, apply_ite star, star_one, star_zero]
      congr 1
      · apply if_congr _ rfl rfl
        constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h3.symm, h2.symm, h1.symm, h4.symm⟩
      · apply if_congr _ rfl rfl
        constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h4, h2.symm, h3.symm, h1⟩
    · rintro W _ _ X1 X2 hX c d hcd ⟨s, a, b⟩
      have h := ad_letter hX hcd s a b
      simp only [Matrix.of_apply, sub_smul, Finset.sum_sub_distrib]
      rw [h]
      congr 1
      · by_cases h1 : d = a <;> simp [h1]
      · by_cases h1 : b = c <;> simp [h1]
    · simp [Pi.single_apply]
  | mul a b ha hb =>
    obtain ⟨ι, _, w, M, t, ⟨h1, h2⟩, rfl⟩ := ha
    obtain ⟨ι', _, w', M', t', ⟨h1', h2'⟩, rfl⟩ := hb
    refine ⟨ι × ι', inferInstance, fun p => w p.1 * w' p.2,
      fun c d => Matrix.of fun j i => (if j.2 = i.2 then M c d j.1 i.1 else 0) + (if j.1 = i.1 then M' c d j.2 i.2 else 0),
      fun p => t p.1 * t' p.2, ⟨?_, ?_⟩, ?_⟩
    · rintro c d ⟨i1, i2⟩ ⟨j1, j2⟩
      simp only [Matrix.of_apply, star_add, apply_ite star, star_zero, h1, h1', eq_comm]
    · rintro W _ _ X1 X2 hX c d hcd ⟨i, i'⟩
      have e1 := h2 W X1 X2 hX c d hcd i
      have e2 := h2' W X1 X2 hX c d hcd i'
      have : (X1 c d + X2 c d) * evB lev X1 X2 (w i * w' i') - evB lev X1 X2 (w i * w' i') * (X1 c d + X2 c d) =
          ((X1 c d + X2 c d) * evB lev X1 X2 (w i) - evB lev X1 X2 (w i) * (X1 c d + X2 c d)) * evB lev X1 X2 (w' i') +
            evB lev X1 X2 (w i) *
              ((X1 c d + X2 c d) * evB lev X1 X2 (w' i') - evB lev X1 X2 (w' i') * (X1 c d + X2 c d)) := by
        rw [map_mul]; noncomm_ring
      simp only []
      rw [this, e1, e2]
      simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, Fintype.sum_prod_type, ite_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
        mul_smul_comm]
      congr 1
      rw [Finset.sum_comm]
      simp
    · rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
      simp only [smul_mul_smul_comm]
  | add a b ha hb =>
    obtain ⟨ι, _, w, M, t, ⟨h1, h2⟩, rfl⟩ := ha
    obtain ⟨ι', _, w', M', t', ⟨h1', h2'⟩, rfl⟩ := hb
    refine ⟨ι ⊕ ι', inferInstance, Sum.elim w w', fun c d => Matrix.fromBlocks (M c d) 0 0 (M' c d),
      Sum.elim t t', ⟨?_, ?_⟩, ?_⟩
    · rintro c d (i | i) (j | j) <;> simp [← h1 d c, ← h1' d c]
    · rintro W _ _ X1 X2 hX c d hcd (i | i)
      · simp [Fintype.sum_sum_type, h2 W X1 X2 hX c d hcd]
      · simp [Fintype.sum_sum_type, h2' W X1 X2 hX c d hcd]
    · simp [Fintype.sum_sum_type]

theorem AdFamL.comm {lev : Fin n → ℕ} {ι : Type} [Fintype ι] {w : ι → FreeAlgebra ℂ (Bool × Fin n × Fin n)}
    {M : Fin n → Fin n → Matrix ι ι ℂ} (h : AdFamL lev w M) {W : Type} [AddCommGroup W] [Module ℂ W]
    {X1 X2 : Fin n → Fin n → Module.End ℂ W} (hX : LRel lev X1 X2) {c d : Fin n} (hcd : lev c = lev d) (t : ι → ℂ) :
    (X1 c d + X2 c d) * evB lev X1 X2 (∑ i, t i • w i) - evB lev X1 X2 (∑ i, t i • w i) * (X1 c d + X2 c d) =
      evB lev X1 X2 (∑ j, (M c d *ᵥ t) j • w j) := by

  simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
  ← Finset.sum_sub_distrib, ← smul_sub, h.2 W X1 X2 hX c d hcd, Finset.smul_sum, Matrix.mulVec, dotProduct,
  Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem invL : InvL := by
  classical
  intro n lev V _ _ X1 X2 L a hX hL ha
  obtain ⟨ι, _, w, M, t, hM, rfl⟩ := exists_adFamL lev a
  let N : Submodule ℂ (EuclideanSpace ℂ ι) :=
    { carrier := {x | ∀ s ∈ L, evB lev X1 X2 (∑ i, x i • w i) s = 0}
      add_mem' := by
        intro x y hx hy s hs
        have := hx s hs
        have := hy s hs
        simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib, map_add (f := _), LinearMap.add_apply, *, add_zero]
      zero_mem' := by intro s hs; simp
      smul_mem' := by
        intro r x hx s hs
        have := hx s hs
        simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smul, LinearMap.smul_apply, this,
          smul_zero] }
  have hN : ∀ x, x ∈ N ↔ ∀ s ∈ L, evB lev X1 X2 (∑ i, x i • w i) s = 0 := fun x => Iff.rfl
  let D : Fin n → Fin n → Module.End ℂ (EuclideanSpace ℂ ι) := fun c d => Matrix.toEuclideanLin (M c d)
  have hD : ∀ c d x, (D c d x).ofLp = M c d *ᵥ x.ofLp := fun c d x => rfl
  have hadj : ∀ c d x y, ⟪x, D c d y⟫_ℂ = ⟪D d c x, y⟫_ℂ := by
    intro c d x y
    have : M d c = (M c d)ᴴ := by ext i j; simp [Matrix.conjTranspose_apply, ← hM.1 c d]
    simp only [D]
    rw [this, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
  have hDN : ∀ c d, lev c = lev d → ∀ x ∈ N, D c d x ∈ N := by
    intro c d hcd x hx
    rw [hN] at hx ⊢
    intro s hs
    rw [hD, ← hM.comm hX hcd]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hx s hs, hx _ (hL c d hcd s hs), map_zero, sub_zero]
  have ht : ∀ c d, lev c = lev d → D c d (WithLp.toLp 2 t) ∈ N := by
    intro c d hcd
    rw [hN]
    intro s hs
    rw [hD, ← hM.comm hX hcd]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, ha c d hcd s hs, sub_self]
  obtain ⟨k, hk, t', ht', e⟩ := N.exists_add_mem_mem_orthogonal (WithLp.toLp 2 t)
  have h0 : ∀ c d, lev c = lev d → D c d t' = 0 := by
    intro c d hcd
    have h1 : D c d t' ∈ N := by
      have := N.sub_mem (ht c d hcd) (hDN c d hcd k hk)
      rwa [e, map_add, add_sub_cancel_left] at this
    rw [← inner_self_eq_zero (𝕜 := ℂ), hadj]
    exact (Submodule.mem_orthogonal _ _).1 ht' _ (hDN d c hcd.symm _ h1)
  refine ⟨∑ i, t' i • w i, ?_, ?_⟩
  · intro V' _ _ Y1 Y2 hY c d hcd
    have := hM.comm hY hcd t'.ofLp
    rw [← hD, h0 c d hcd] at this
    have h2 : evB lev Y1 Y2 (∑ j, (0 : EuclideanSpace ℂ ι).ofLp j • w j) = 0 := by simp
    rw [h2] at this
    exact sub_eq_zero.1 this
  · intro s hs
    have e' : ∀ i, t i = k i + t' i := fun i => congrArg (fun x : EuclideanSpace ℂ ι => x i) e
    have := (hN k).1 hk s hs
    simp only [e', add_smul, Finset.sum_add_distrib, map_add (f := _), LinearMap.add_apply, this, zero_add]

end GlobalTheory.CompanionTheory.PairMult
end
end

section


theorem _root_.GlobalTheory.T.mixed_cycle_codimension_one : GlobalTheory.CompanionTheory.MixZ.CodimOne := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.codimOne_holds | exact GlobalTheory.CompanionTheory.MixZ.codimOne_holds | (intros; apply GlobalTheory.CompanionTheory.MixZ.codimOne_holds <;> assumption)
end
