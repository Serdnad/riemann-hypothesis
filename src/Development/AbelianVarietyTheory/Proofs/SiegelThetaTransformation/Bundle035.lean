module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFourierExpansionHolomorphicTube
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormLeTsumOfCubeFourierCoeffLe
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle251
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker.LevelTheta

theorem exists_fourier_entire {ι : Type} [Fintype ι] (f : (ι → ℂ) → ℂ) (hf : Differentiable ℂ f)
    (hper : ∀ z, ∀ m : ι → ℤ, f (z + fun i => (m i : ℂ)) = f z) :
    ∃ a : (ι → ℤ) → ℂ,
      (∀ z, HasSum (fun ν : ι → ℤ => a ν * cexp (2 * π * I * ∑ i, (ν i : ℂ) * z i)) (f z)) ∧
      ∀ (w : ι → ℂ) (ν : ι → ℤ), a ν = ∫ x in Set.Icc (0 : ι → ℝ) 1,
        f ((fun i => (x i : ℂ)) + w) *
          cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * ((x i : ℂ) + w i))) := by
  obtain ⟨a, h1, h2⟩ := exists_fourier_expansion_tube ι Set.univ f isOpen_univ convex_univ
    hf.differentiableOn (fun z _ m => hper z m)
  refine ⟨a, fun z => h1 z trivial, fun w ν => ?_⟩
  have key := Koecher.setIntegral_unitCube_tube (U := Set.univ)
    (f := fun z => f z * cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * z i))) isOpen_univ
    isPreconnected_univ (fun _ _ _ => trivial)
    (hf.differentiableOn.mul (Differentiable.differentiableOn (by fun_prop))) (fun z hz i => ?_)
    (Set.mem_univ (fun i => I * (((0 : ι → ℝ) i : ℝ) : ℂ))) (Set.mem_univ w)
  · rw [h2 0 trivial ν]
    refine Eq.trans ?_ key
    exact (setIntegral_congr_set (μ := volume) (Measure.univ_pi_Ico_ae_eq_Icc
      (f := (0 : ι → ℝ)) (g := 1)))
  · have e0 : (Pi.single i 1 : ι → ℂ) = fun j => (((Pi.single i 1 : ι → ℤ) j : ℤ) : ℂ) := by
      funext j
      by_cases hij : j = i
      · subst hij; simp
      · simp [hij]
    have e : ∑ j, (ν j : ℂ) * (z + (Pi.single i 1 : ι → ℂ)) j
        = ∑ j, (ν j : ℂ) * z j + ν i := by
      simp [mul_add, Finset.sum_add_distrib, Pi.single_apply]
    rw [e, e0, hper z, mul_add, neg_add, Complex.exp_add]
    have : cexp (-(2 * π * I * (ν i : ℂ))) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I (-ν i)]
      congr 1
      push_cast
      ring
    rw [this, mul_one]

theorem quad_add {ι : Type} [Fintype ι] {τ : Matrix ι ι ℂ} (h : τ.IsSymm) (u v : ι → ℂ) :
    (u + v) ⬝ᵥ τ *ᵥ (u + v) = u ⬝ᵥ τ *ᵥ u + 2 * (u ⬝ᵥ τ *ᵥ v) + v ⬝ᵥ τ *ᵥ v := by
  have : v ⬝ᵥ τ *ᵥ u = u ⬝ᵥ τ *ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, h.eq, dotProduct_comm]
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, this]
  ring

theorem exists_thS_eq : ∀ (n g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ Siegel (Fin g) → ∀ (N : ℕ), 0 < N → ∀ Θ : (Fin n → Fin g → ℂ) → ℂ, Differentiable ℂ Θ → (∀ (a : Fin n → Fin g → ℤ) ζ, Θ (fun k i => ζ k i + N * a k i) = Θ ζ) → (∀ (b : Fin n → Fin g → ℤ) ζ, cexp (π * I * ∑ k, ((fun i => (N * b k i : ℂ)) ⬝ᵥ τ *ᵥ (fun i => (N * b k i : ℂ)) + 2 * ((fun i => (N * b k i : ℂ)) ⬝ᵥ ζ k))) * Θ (fun k => ζ k + τ *ᵥ fun i => (N * b k i : ℂ)) = Θ ζ) → ∃ φ : TF n g, IsSB φ ∧ ∀ ζ, thS φ τ ζ = Θ ζ := by
  intro n g τ hτ N hN Θ hΘ hp hq
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨a, hs, ha⟩ := exists_fourier_entire (ι := Fin n × Fin g)
    (fun z => Θ fun k i => N * z (k, i)) (hΘ.comp (by fun_prop)) (fun z m => by
      rw [← hp (fun k i => m (k, i)) fun k i => N * z (k, i)]
      congr 1
      funext k i
      simp [mul_add])
  let e : (Fin n × Fin g → ℤ) → Matrix (Fin n) (Fin g) ℚ :=
    fun ν => Matrix.of fun k i => (ν (k, i) : ℚ) / N
  have he : Function.Injective e := by
    intro m m' hmn
    funext ⟨k, i⟩
    have h1 : (m (k, i) : ℚ) / N = (m' (k, i) : ℚ) / N := congrFun (congrFun hmn k) i
    exact_mod_cast (div_left_inj' hNq).1 h1
  let Q : Matrix (Fin n) (Fin g) ℚ → ℂ := fun x => ∑ k, qv (x k) ⬝ᵥ τ *ᵥ qv (x k)
  let φ : TF n g := fun x => Function.extend e a 0 x * cexp (-(π * I * Q x))
  have hφe : ∀ ν, φ (e ν) = a ν * cexp (-(π * I * Q (e ν))) := fun ν => by
    simp only [φ, he.extend_apply]
  have hφ0 : ∀ x, x ∉ Set.range e → φ x = 0 := fun x hx => by
    simp only [φ]
    rw [Function.extend_apply' _ _ _ hx]
    simp
  have hshift : ∀ (ν : Fin n × Fin g → ℤ) (b : Fin n → Fin g → ℤ),
      e ν + (N : ℚ) • (Matrix.of fun k i => (b k i : ℚ)) =
        e (fun p => ν p + N ^ 2 * b p.1 p.2) := by
    intro ν b
    ext k i
    simp only [e, of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    field_simp
  have hlaw : ∀ (ν : Fin n × Fin g → ℤ) (b : Fin n → Fin g → ℤ),
      φ (e ν + (N : ℚ) • (Matrix.of fun k i => (b k i : ℚ))) = φ (e ν) := by
    intro ν b
    have hQ : Q (e ν + (N : ℚ) • (Matrix.of fun k i => (b k i : ℚ))) =
        Q (e ν) + 2 * ∑ k, ∑ i, (ν (k, i) : ℂ) * (τ *ᵥ fun j => (b k j : ℂ)) i +
          ∑ k, (fun i => (N * b k i : ℂ)) ⬝ᵥ τ *ᵥ (fun i => (N * b k i : ℂ)) := by
      simp only [Q, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 : qv ((e ν + (N : ℚ) • (Matrix.of fun k i => (b k i : ℚ))) k) =
          qv (e ν k) + fun i => (N * b k i : ℂ) := by
        funext i
        simp [qv]
      rw [h1, quad_add hτ.1]
      congr 2
      have h2 : (fun i => (N * b k i : ℂ)) = (N : ℂ) • fun i => (b k i : ℂ) := by
        funext i; simp
      rw [h2, mulVec_smul, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [qv, e, of_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      field_simp
    have h := hφe (fun p => ν p + N ^ 2 * b p.1 p.2)
    rw [← hshift] at h
    rw [h, hφe, hQ, ha 0, ha (fun p => (τ *ᵥ fun j => (b p.1 j : ℂ)) p.2) ν,
      ← integral_mul_const, ← integral_mul_const]
    congr 1
    funext x
    rw [← hq b]
    have h3 : (fun k => (fun k i => (N : ℂ) * ((fun p : Fin n × Fin g => (x p : ℂ)) + 0) (k, i)) k +
        τ *ᵥ fun i => (N * b k i : ℂ)) =
        fun k i => (N : ℂ) * ((fun p : Fin n × Fin g => (x p : ℂ)) +
          fun p : Fin n × Fin g => (τ *ᵥ fun j => (b p.1 j : ℂ)) p.2) (k, i) := by
      funext k i
      have h2 : (fun i => (N * b k i : ℂ)) = (N : ℂ) • fun i => (b k i : ℂ) := by
        funext i; simp
      rw [h2, mulVec_smul]
      simp [mul_add]
    rw [h3, mul_comm (cexp _) (Θ _)]
    simp only [mul_assoc (Θ _), ← Complex.exp_add]
    congr 2
    have h4 : ∑ k, (fun i => (N * b k i : ℂ)) ⬝ᵥ
        (fun i => (N : ℂ) * ((fun p : Fin n × Fin g => (x p : ℂ)) + 0) (k, i)) =
        ∑ k, ∑ i, (N : ℂ) ^ 2 * b k i * x (k, i) := by
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply, Pi.zero_apply]
      ring
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, h4]
    simp only [Fintype.sum_prod_type, Pi.zero_apply, add_zero, mul_add, add_mul,
      Finset.sum_add_distrib, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    ring
  refine ⟨φ, ⟨N, hN, fun x hx => ?_, fun x y hy => ?_⟩, fun ζ => ?_⟩
  · obtain ⟨ν, rfl⟩ : x ∈ Set.range e := by
      by_contra h
      exact hx (hφ0 x h)
    intro k i
    have : ((N : ℚ) • e ν) k i = algebraMap ℤ ℚ (ν (k, i)) := by
      simp only [e, of_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast]
      field_simp
    rw [this]
    exact isIntegral_algebraMap
  · have : ∀ k i, ∃ m : ℤ, (m : ℚ) = y k i := fun k i => by
      simpa using IsIntegrallyClosed.isIntegral_iff.1 (hy k i)
    choose b hb using this
    obtain rfl : y = Matrix.of fun k i => (b k i : ℚ) := by
      ext k i
      simp [hb]
    by_cases hx : x ∈ Set.range e
    · obtain ⟨ν, rfl⟩ := hx
      exact hlaw ν b
    · rw [hφ0 x hx]
      refine hφ0 _ ?_
      rintro ⟨ν, hν⟩
      refine hx ⟨fun p => ν p + N ^ 2 * (-b) p.1 p.2, ?_⟩
      rw [← hshift, hν]
      ext k i
      simp
  · have h1 := hs fun p => ζ p.1 p.2 / N
    have h2 : (fun k i => (N : ℂ) * (ζ k i / N)) = ζ := by
      funext k i
      field_simp
    simp only [h2] at h1
    refine HasSum.tsum_eq ?_
    refine (he.hasSum_iff fun x hx => by rw [hφ0 x hx, zero_mul]).1 ?_
    convert h1 using 2 with ν
    simp only [Function.comp_apply]
    rw [hφe, mul_assoc, ← Complex.exp_add]
    congr 2
    have h3 : ∑ k, qv (e ν k) ⬝ᵥ ζ k = ∑ p : Fin n × Fin g, (ν p : ℂ) * (ζ p.1 p.2 / N) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      simp only [qv, e, of_apply]
      push_cast
      ring
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, h3]
    simp only [Q]
    ring

end GlobalTheory.Ker.LevelTheta
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker

theorem exists_infFam_and_stdChar : ∀ D : D7, (∃ θ : InfFam D, IsInfFam θ) ∧ ∃ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) :=
  fun D => ⟨GlobalTheory.DualPairCompare.exists_infFam D, GlobalTheory.StdAdelicChar.exists_isStdChar D⟩

end GlobalTheory.Ker
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker

section DoubleCoset
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]


open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
theorem _root_.GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen (Γ K : Subgroup G) (hK : IsOpen (K : Set G)) (a : G) :
    IsOpen {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} := by
  have hunion : {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} =
      ⋃ γ ∈ Γ, (fun k => γ * a * k) '' (K : Set G) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]
    constructor
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨γ, hγ, k, hk, rfl⟩
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨γ, hγ, k, hk, rfl⟩
  rw [hunion]
  exact isOpen_biUnion fun γ _ => isOpenMap_mul_left (γ * a) _ hK


open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem _root_.GlobalTheory.Ker.tsum_indicator_coset (Γ K : Subgroup G) (a : G)
    (hfin : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.Finite) (x : G) :
    ∑' γ : Γ, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ • x)
      = ({γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.ncard : ENNReal) *
        {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k}.indicator 1 x := by
  by_cases hx : x ∈ {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k}
  · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    obtain ⟨γ₀, hγ₀, k₀, hk₀, rfl⟩ := hx
    set T : Set Γ := {γ | a⁻¹ * ((γ : G) * (γ₀ * a * k₀)) ∈ K} with hT
    have hterm : ∀ γ : Γ, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal)
        (γ • (γ₀ * a * k₀)) = T.indicator (1 : Γ → ENNReal) γ := by
      intro γ
      by_cases hγ : γ ∈ T
      · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem]
        · rfl
        · exact hγ
      · rw [Set.indicator_of_notMem hγ, Set.indicator_of_notMem]
        exact hγ
    simp_rw [hterm]
    rw [← tsum_subtype T (1 : Γ → ENNReal)]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    have hinj : Function.Injective (fun γ : Γ => (γ : G) * γ₀) :=
      fun γ δ hγδ => Subtype.ext (mul_right_cancel hγδ)
    have himg : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K} = (fun γ : Γ => (γ : G) * γ₀) '' T := by
      ext δ
      constructor
      · rintro ⟨hδ, hδK⟩
        refine ⟨⟨δ * γ₀⁻¹, Γ.mul_mem hδ (Γ.inv_mem hγ₀)⟩, ?_, by simp⟩
        show a⁻¹ * (δ * γ₀⁻¹ * (γ₀ * a * k₀)) ∈ K
        have heq : a⁻¹ * (δ * γ₀⁻¹ * (γ₀ * a * k₀)) = a⁻¹ * δ * a * k₀ := by group
        rw [heq]
        exact K.mul_mem hδK hk₀
      · rintro ⟨γ, hγ, rfl⟩
        refine ⟨Γ.mul_mem γ.2 hγ₀, ?_⟩
        have hγ' : a⁻¹ * ((γ : G) * (γ₀ * a * k₀)) ∈ K := hγ
        have heq : a⁻¹ * ((γ : G) * γ₀) * a = a⁻¹ * ((γ : G) * (γ₀ * a * k₀)) * k₀⁻¹ := by group
        rw [heq]
        exact K.mul_mem hγ' (K.inv_mem hk₀)
    rw [← hinj.encard_image, ← himg, ← hfin.cast_ncard_eq, ENat.toENNReal_coe]
  · rw [Set.indicator_of_notMem hx, mul_zero]
    refine tsum_eq_zero_iff.2 fun γ => Set.indicator_of_notMem ?_ _
    intro hmem
    have hk : a⁻¹ * ((γ : G) * x) ∈ K := hmem
    exact hx ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, _, hk, by group⟩

variable [MeasurableSpace G] [BorelSpace G]

end DoubleCoset

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
private theorem measure_fd_inter_doubleCoset_mul_ncard_eq {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsMulLeftInvariant] (Γ K : Subgroup G) [Countable Γ] (D : Set G)
    (hD : IsFundamentalDomain Γ D ν) (hK : IsOpen (K : Set G)) (a : G)
    (hfin : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.Finite) :
    ν ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} ∩ D) *
      ({γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.ncard : ENNReal) = ν K := by
  have hC : MeasurableSet {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} :=
    (_root_.GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen Γ K hK a).measurableSet
  have hmeasK : MeasurableSet ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)) :=
    hK.measurableSet.preimage (measurable_const_mul _)
  have hwhole : ∫⁻ x, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator 1 x ∂ν = ν K := by
    rw [lintegral_indicator_one hmeasK, measure_preimage_mul]
  have hinv := (Equiv.inv Γ).tsum_eq (fun γ : Γ =>
    ∫⁻ x in D, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ⁻¹ • x) ∂ν)
  simp only [Equiv.inv_apply, inv_inv] at hinv
  rw [← hwhole, hD.lintegral_eq_tsum', ← hinv, ← lintegral_tsum]
  · simp_rw [_root_.GlobalTheory.Ker.tsum_indicator_coset Γ K a hfin]
    rw [lintegral_const_mul _ (measurable_one.indicator hC), lintegral_indicator_one hC,
      Measure.restrict_apply hC, mul_comm]
  · intro γ
    exact ((measurable_one.indicator hmeasK).comp (measurable_const_smul γ)).aemeasurable


open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
theorem _root_.GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ K : Subgroup G) [Countable Γ] (𝓖 : Set G), IsFundamentalDomain Γ 𝓖 ν → IsOpen (K : Set G) → ν K ≠ ⊤ → ∀ (ι : Type) [Fintype ι] (h : ι → G), (∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k) → (∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.Finite) → ∀ F : G → ℂ, (∀ γ ∈ Γ, ∀ x, F (γ * x) = F x) → (∀ k ∈ K, ∀ x, F (x * k) = F x) → ν 𝓖 ≠ ⊤ ∧ IntegrableOn F 𝓖 ν ∧ ∫ x in 𝓖, F x ∂ν = ((ν K).toReal : ℂ) * ∑ i, (({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard : ℕ) : ℂ)⁻¹ * F (h i) := by
  intro G _ _ _ _ _ ν _ Γ K _ 𝓖 h𝓖 hK hKtop ι _ h huniq hfin F hFΓ hFK
  have hCmeas : ∀ i, MeasurableSet {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} := fun i =>
    (_root_.GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen Γ K hK (h i)).measurableSet
  have hpos : ∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard ≠ 0 := fun i =>
    ((Set.ncard_pos (hfin i)).2 ⟨1, Γ.one_mem, by simpa using K.one_mem⟩).ne'
  have hCG : ∀ i, ν ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} ∩ 𝓖) =
      ν K / ({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard : ENNReal) := by
    intro i
    rw [ENNReal.eq_div_iff (by exact_mod_cast hpos i) (ENNReal.natCast_ne_top _), mul_comm]
    exact measure_fd_inter_doubleCoset_mul_ncard_eq ν Γ K 𝓖 h𝓖 hK (h i) (hfin i)
  have hCGtop : ∀ i, ν ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} ∩ 𝓖) ≠ ⊤ := by
    intro i
    rw [hCG i]
    exact (ENNReal.div_lt_top hKtop (by exact_mod_cast hpos i)).ne
  have h𝓖top : ν 𝓖 ≠ ⊤ := by
    have hsub : 𝓖 ⊆ ⋃ i, ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} ∩ 𝓖) := fun x hx =>
      Set.mem_iUnion.2 ⟨(huniq x).exists.choose, (huniq x).exists.choose_spec, hx⟩
    refine ne_top_of_le_ne_top ?_ ((measure_mono hsub).trans (measure_iUnion_fintype_le _ _))
    exact ENNReal.sum_ne_top.2 fun i _ => hCGtop i
  have hdecomp : ∀ x, F x =
      ∑ i, {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k}.indicator (fun _ => F (h i)) x := by
    intro x
    obtain ⟨i, hi, hiuniq⟩ := huniq x
    rw [Finset.sum_eq_single i]
    · rw [Set.indicator_of_mem (show x ∈ {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} from hi)]
      obtain ⟨γ, hγ, k, hk, rfl⟩ := hi
      rw [hFK k hk, hFΓ γ hγ]
    · intro j _ hj
      exact Set.indicator_of_notMem
        (show x ∉ {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h j * k} from fun hx => hj (hiuniq j hx)) _
    · intro hi'
      exact absurd (Finset.mem_univ i) hi'
  have hint : ∀ i, IntegrableOn
      ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k}.indicator (fun _ => F (h i))) 𝓖 ν := by
    intro i
    refine (integrable_indicator_iff (hCmeas i)).2 ?_
    refine integrableOn_const ?_
    rw [Measure.restrict_apply (hCmeas i)]
    exact hCGtop i
  refine ⟨h𝓖top, ?_, ?_⟩
  · exact (integrable_finsetSum _ fun i _ => hint i).congr
      (ae_of_all _ fun x => (hdecomp x).symm)
  · refine (congrArg (fun f : G → ℂ => ∫ x in 𝓖, f x ∂ν) (funext hdecomp)).trans ?_
    rw [integral_finsetSum _ fun i _ => hint i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_indicator_const _ (hCmeas i), measureReal_def, Measure.restrict_apply (hCmeas i),
      hCG i, ENNReal.toReal_div, ENNReal.toReal_natCast, Complex.real_smul]
    push_cast
    ring

end GlobalTheory.Ker
end
