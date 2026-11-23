module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle197
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle167
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle241
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle262
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle242
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle131
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle179
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedEisensteinProductValueNeZeroOfRankin
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalLev
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle232
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle263
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle264
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle265
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle266
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle221

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem exists_uniformiser_max (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ∃ ϖ : k, ϖ ≠ 0 ∧ valuation k ϖ < 1 ∧ ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ := by
  set e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  obtain ⟨x, hx⟩ := valuation_surjective (e.symm (WithZero.exp (-1 : ℤ)))
  have hx' : e (valuation k x) = WithZero.exp (-1 : ℤ) := by rw [hx]; simp
  refine ⟨x, ?_, ?_, ?_⟩
  · intro h0
    rw [h0, map_zero, map_zero] at hx'
    exact WithZero.zero_ne_coe hx'
  · rw [← e.strictMono.lt_iff_lt, hx', map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  · intro y hy
    rw [← e.strictMono.le_iff_le, hx']
    have hlt : e (valuation k y) < 1 := by rw [← map_one e]; exact e.strictMono hy
    rcases eq_or_ne (e (valuation k y)) 0 with h | h
    · rw [h]; exact zero_le'
    · rw [← WithZero.exp_log h] at hlt ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      rw [WithZero.exp_le_exp]; omega

theorem eig_jacquet_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V), IsSmooth π → (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → Cut ψ r → ∀ v ∈ twKer π (unipRad k (two (stdSum (rfl : r + t = r + t)))) 1, IsEig π (grp ψ) (theta ψ) v → v = 0 := by
  intro k _ _ _ _ r t ψ V _ _ π hπ hψ hord hcut v hv heig
  obtain ⟨ϖ, hϖ0, hϖ1, hϖmax⟩ := exists_uniformiser_max k
  let z : GL (Fin (r + t)) k := diagT k (Fin (r + t)) (fun i => if (i : ℕ) < r then Units.mk0 ϖ hϖ0 else 1)
  have hz : z.val = Matrix.diagonal (fun i : Fin (r + t) => if (i : ℕ) < r then ϖ else 1) := by
    simp only [z]; rw [val_diagT]; congr 1; funext i; split_ifs <;> simp
  obtain ⟨hD, -⟩ := GlobalTheory.T.principalSeriesCongruenceSubgroup_smoothCharacterDatum k (r + t) ψ hψ hord
  obtain ⟨hSD, hSmono⟩ := GlobalTheory.T.compactSubgroupSmoothCharacterDatum_monotone k (r + t) ψ r ϖ hψ hϖ0 hϖ1 hϖmax
  obtain ⟨h0J, hθ1, h1KO, hconj⟩ := GlobalTheory.T.principalSeriesUnipotentStrip_properties k (r + t) ψ r ϖ hϖ0 hϖ1 hϖmax hcut
  obtain ⟨m, hm⟩ := GlobalTheory.T.twistedJacquetKernel_mem_twistedSpan_finite_stage _ V π _ (strip ψ r ϖ) hSmono (GlobalTheory.T.strips_exhaust_parabolicUnipotentRadical k r t ψ ϖ hψ hϖ0 hϖ1 hϖmax) v hv
  refine GlobalTheory.T.eigenvector_eq_zero_of_mem_twistedSpan_chain (GL (Fin (r + t)) k) V π hπ (grp ψ) (strip ψ r ϖ) (theta ψ) z hD hSD hSmono
    (fun y hy => ⟨h0J y hy, hθ1 0 y hy⟩) (hconj z hz) ?_ ?_ m v hm heig
  · intro y hy
    by_cases hyJ : y ∈ grp ψ
    · exact Or.inl ⟨hyJ, hθ1 1 y hy⟩
    · exact Or.inr (GlobalTheory.T.principalSeriesType_not_intertwine_outside k (r + t) ψ hord y (h1KO y hy) hyJ)
  · intro j hj
    obtain ⟨y, hy, hblk⟩ := GlobalTheory.T.exists_strip_clearing_upperRight_principalSeriesCongruence k (r + t) ψ r ϖ hord hcut j hj
    have hyJ : y ∈ grp ψ := h0J y hy
    have hyinv : y⁻¹ ∈ grp ψ := hD.inv y hyJ
    have hg : y⁻¹ * j ∈ grp ψ := hD.mul _ hyinv _ hj
    obtain ⟨h1, h2⟩ := GlobalTheory.T.conj_blockLower_mem_principalSeriesCongruence k (r + t) ψ r ϖ hϖ0 hϖ1 z hz (y⁻¹ * j) hg hblk
    refine ⟨y, hy, h1, ?_⟩
    rw [h2, GlobalTheory.T.principalSeriesTypeCharacter_mul k (r + t) ψ hord _ hyinv _ hj, hθ1 0 _ ((hSD 0).inv y hy), one_mul]

end GlobalTheory.PsType
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.halfPeterssonIntegral_heckeT_adjoint : ∀ (k L N q : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (h a : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → q.Prime → ¬ q ∣ L → Wt L ρ → CF k L (ch ε) h → MF k L (ch ε) a → pet k ρ (qs h) (qs (To k (ch ε q) q a)) = ch ε q * pet k ρ (qs (To k (ch ε q) q h)) (qs a) := by
  first | exact @GlobalTheory.EisM.pet_To_adjoint | exact GlobalTheory.EisM.pet_To_adjoint | (intros; apply GlobalTheory.EisM.pet_To_adjoint <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.halfPeterssonIntegral_self_ne_zero_cuspForm : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (h : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → Wt L ρ → CF k L (ch ε) h → h ≠ 0 → pet k ρ (qs h) (qs h) ≠ 0 := by
  first | exact @GlobalTheory.EisM.PetPos.pet_self_ne_zero | exact GlobalTheory.EisM.PetPos.pet_self_ne_zero | (intros; apply GlobalTheory.EisM.PetPos.pet_self_ne_zero <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.halfPeterssonIntegralWeighted_linear_forms : ∀ (k L L' N : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ), 1 ≤ k → 0 < L' → N ∣ L' → Wt L ρ → (∀ (h a b : ℕ → ℂ) (x y : ℂ), CF k L' (ch ε) h → PolyB a → PolyB b → pet k ρ (qs h) (qs (x • a + y • b)) = x * pet k ρ (qs h) (qs a) + y * pet k ρ (qs h) (qs b)) ∧ ∀ (h h' a : ℕ → ℂ) (x y : ℂ), CF k L' (ch ε) h → CF k L' (ch ε) h' → PolyB a → pet k ρ (fun τ => x * qs h τ + y * qs h' τ) (qs a) = conj x * pet k ρ (qs h) (qs a) + conj y * pet k ρ (qs h') (qs a) := by
  first | exact @GlobalTheory.EisM.pet_linear | exact GlobalTheory.EisM.pet_linear | (intros; apply GlobalTheory.EisM.pet_linear <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.depletedEisensteinProduct_value_ne_zero_of_rankin : ∀ (e N l : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (φ : DirichletCharacter ℂ (N * l)) (t : ℕ → ℂ) (α c₀ c₁ : ℂ) (B : ℕ) (c : ℕ → ℂ), 1 ≤ e → 0 < N → l.Prime → ¬ l ∣ N → α ≠ 0 → EigF (2 * e + 1) N l χ⁻¹ t α B c → θ (-1) = (-1) ^ e * ψ (-1) → χ (-1) = -1 → θ * χ ≠ 1 → (∀ d : ℤ, ch φ d = ch (θ * χ) d * ch ψ d) → MF e (N * l) (fun d => ch ψ d * ch θ d) (eis e c₀ (ch ψ) (ch θ)) → MF (e + 1) (N * l) (ch φ⁻¹) (eis (e + 1) c₁ (hat φ) fun _ => 1) → lam B c (mul (eis e c₀ (ch ψ) (ch θ)) (eis (e + 1) c₁ (hat φ) fun _ => 1)) ≠ 0 → α ≠ θ l → α ≠ (l : ℂ) ^ e * χ⁻¹ l → val B c l α 1 (Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)) ≠ 0 := by
  first | exact @GlobalTheory.EisM.val_depleted_ne_zero | exact GlobalTheory.EisM.val_depleted_ne_zero | (intros; apply GlobalTheory.EisM.val_depleted_ne_zero <;> assumption)
end

section

open scoped MatrixGroups

theorem _root_.GlobalTheory.T.finiteDimensional_lev_of_gamma_le : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (M : ℕ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ' → letI := GlobalTheory.K4.algRat X Γ'; FiniteDimensional (RatFunc Ω) (GlobalTheory.K4.lev X Γ') := by
  first | exact @GlobalTheory.K4.finiteDimensional_lev | exact GlobalTheory.K4.finiteDimensional_lev | (intros; apply GlobalTheory.K4.finiteDimensional_lev <;> assumption)
end

section

noncomputable section

open scoped MatrixGroups UpperHalfPlane
open Polynomial

namespace GlobalTheory.K4.TopUnits

open GlobalTheory.KZ GlobalTheory.Sieg

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def holSub (X : Tower Ω ε) : Subring X.K where
  carrier := {f | ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an f = (φ : Mero)}
  mul_mem' := by
    rintro f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩
    exact ⟨φ * ψ, h1.mul h3, by rw [map_mul, h2, h4, Filter.Germ.coe_mul]⟩
  one_mem' := ⟨1, differentiableOn_const 1, by rw [map_one, Filter.Germ.coe_one]⟩
  add_mem' := by
    rintro f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩
    exact ⟨φ + ψ, h1.add h3, by rw [map_add (f := _), h2, h4, Filter.Germ.coe_add]⟩
  zero_mem' := ⟨0, differentiableOn_const 0, by rw [map_zero, Filter.Germ.coe_zero]⟩
  neg_mem' := by
    rintro f ⟨φ, h1, h2⟩
    exact ⟨-φ, h1.neg, by rw [map_neg, h2, Filter.Germ.coe_neg]⟩

theorem siegel_hol [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {c : ℕ} {y : Fin 2 → ℚ} (hy : admitted c y) :
    siegel X c y ∈ holSub X ∧ (siegel X c y)⁻¹ ∈ holSub X := by
  have hd : DifferentiableOn ℂ (sgC c y) Hs :=
    UpperHalfPlane.mdifferentiable_iff.1 (GlobalTheory.Sieg.mdifferentiable_sg c y hy)
  have hne : ∀ z, sgC c y z ≠ 0 := fun z => GlobalTheory.Sieg.sg_ne_zero c y _ hy
  have ha := SiegelMem.an_siegel_eq Ω ε X c y hy
  refine ⟨⟨_, hd, ha⟩, (sgC c y)⁻¹, hd.inv fun z _ => hne z, ?_⟩
  have h1 : X.an (siegel X c y)⁻¹ * X.an (siegel X c y) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (GlobalTheory.T.siegelUnitInTower_ne_zero Ω ε X c y hy), map_one]
  have h2 : X.an (siegel X c y) * (((sgC c y)⁻¹ : ℂ → ℂ) : Mero) = 1 := by
    rw [ha, ← Filter.Germ.coe_mul, ← Filter.Germ.coe_one]
    congr 1
    funext z
    exact mul_inv_cancel₀ (hne z)
  rw [← mul_one (X.an _), ← h2, ← mul_assoc, h1, one_mul]

def IsTopUnit (X : Tower Ω ε) (M : ℕ) (f : X.K) : Prop :=
  f ≠ 0 ∧ f ∈ topF X M ∧ ∃ hf : f ∈ topL X M,
    letI := algPoly X (CongruenceSubgroup.Gamma M)
    (⟨f, hf⟩ : topL X M) ∈ FunctionField.ringOfIntegers Ω (topL X M) ∧
      (⟨f, hf⟩ : topL X M)⁻¹ ∈ FunctionField.ringOfIntegers Ω (topL X M)

end GlobalTheory.K4.TopUnits

namespace GlobalTheory.K4

open GlobalTheory.KZ

end GlobalTheory.K4
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem dvd_pow_prod_sub {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ] (d : R) (a : ι → R)
    (b : κ → R) (ha : d ∣ (∏ i, a i) ^ 2) (hb : d ∣ ∏ j, b j) :
    ∃ N : ℕ, d ∣ (∏ i, ∏ j, (b j - a i)) ^ N := by
  have h : (∏ i, ∏ j, (b j - a i)) ∈ (Ideal.span {d}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hle, hP⟩
    have h1 : (∏ i, a i) ∈ P := hP.mem_of_pow_mem 2 (hle (Ideal.mem_span_singleton.2 ha))
    have h2 : (∏ j, b j) ∈ P := hle (Ideal.mem_span_singleton.2 hb)
    obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.1 h1
    obtain ⟨j, -, hj⟩ := Ideal.IsPrime.prod_mem_iff.1 h2
    exact Ideal.IsPrime.prod_mem_iff.2 ⟨i, Finset.mem_univ _,
      Ideal.IsPrime.prod_mem_iff.2 ⟨j, Finset.mem_univ _, P.sub_mem hj hi⟩⟩
  obtain ⟨N, hN⟩ := h
  exact ⟨N, Ideal.mem_span_singleton.1 hN⟩

noncomputable def bddSubring (p : ℕ) [Fact p.Prime] : Subring (PowerSeries ℂ_[p]) where
  carrier := {f | BddSer f}
  mul_mem' ha hb := ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.1 _ _ ha hb).2.2
  add_mem' ha hb := ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.1 _ _ ha hb).1
  one_mem' := by simpa using ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.2.1 1).1
  zero_mem' := by simpa using ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.2.1 0).1
  neg_mem' {x} hx := by
    obtain ⟨B, hB⟩ := hx
    exact ⟨B, fun n => by simpa using hB n⟩

theorem intSer_of_common_divisor (p : ℕ) [Fact p.Prime] (m n : ℕ) (e Ψ A B : PowerSeries ℂ_[p])
    (y : Fin m → ℂ_[p]) (y' : Fin n → ℂ_[p]) (he : BddSer e) (hΨ : BddSer Ψ) (hA : BddSer A)
    (hB : BddSer B) (h1 : PowerSeries.constantCoeff Ψ = 1)
    (hΨA : Ψ * A = (∏ i, lineSer e (y i)) ^ 2) (hΨB : Ψ * B = ∏ j, lineSer e (y' j))
    (hy : ∀ i j, y i ≠ y' j) : IntSer Ψ := by
  have hl : ∀ x : ℂ_[p], lineSer e x ∈ bddSubring p := fun x =>
    (bddSubring p).sub_mem he ((bddSubring p).mul_mem ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.2.1 x).1
      ((bddSubring p).pow_mem (show BddSer _ from ⟨1, (GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.2.2.1⟩) 2))
  obtain ⟨N, H, hH⟩ := dvd_pow_prod_sub (R := bddSubring p) ⟨Ψ, hΨ⟩
    (fun i => ⟨lineSer e (y i), hl _⟩) (fun j => ⟨lineSer e (y' j), hl _⟩)
    ⟨⟨A, hA⟩, Subtype.ext (by simpa using hΨA.symm)⟩
    ⟨⟨B, hB⟩, Subtype.ext (by simpa using hΨB.symm)⟩
  set c : ℂ_[p] := (∏ i, ∏ j, (y i - y' j)) ^ N with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun i _ =>
    Finset.prod_ne_zero_iff.2 fun j _ => sub_ne_zero.2 (hy i j))
  have key : Ψ * (H : PowerSeries ℂ_[p]) = PowerSeries.monomial (2 * n * m * N) c := by
    have h := congrArg Subtype.val hH
    have e1 : ∀ i j, lineSer e (y' j) - lineSer e (y i) =
        PowerSeries.C (y i - y' j) * PowerSeries.X ^ 2 := fun i j => by
      simp only [lineSer, map_sub]; ring
    simp only [SubmonoidClass.coe_pow, Subring.coe_mul, SubmonoidClass.coe_finsetProd,
      AddSubgroupClass.coe_sub, e1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, mul_pow, ← pow_mul] at h
    rw [← h, PowerSeries.monomial_eq_C_mul_X_pow, hc]
    simp only [map_pow, map_prod, mul_assoc]
  have hHc : PowerSeries.coeff (2 * n * m * N) (H : PowerSeries ℂ_[p]) = c := by
    have hinv : Ψ⁻¹ * Ψ = 1 := PowerSeries.inv_mul_cancel _ (by simp [h1])
    have : (H : PowerSeries ℂ_[p]) = PowerSeries.X ^ (2 * n * m * N) * (PowerSeries.C c * Ψ⁻¹) := by
      have h2 := congrArg (Ψ⁻¹ * ·) key
      simp only [← mul_assoc, hinv, one_mul, PowerSeries.monomial_eq_C_mul_X_pow] at h2
      rw [h2]; ring
    rw [this, PowerSeries.coeff_X_pow_mul']
    simp [h1]
  intro i
  have := GlobalTheory.T.powerSeries_supNorm_mul_padicComplex p Ψ H ‖c‖ hΨ H.2 (fun k => by
    rw [key, PowerSeries.coeff_monomial]
    split_ifs <;> simp) i (2 * n * m * N)
  rw [hHc] at this
  exact le_of_mul_le_mul_right (by simpa using this) (norm_pos_iff.2 hc0)

end GlobalTheory.EvenTheta
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.U1_two_mul_th0_mul_th0_eq : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ s, s ∉ Λ → ∀ z, U1 Λ s (sgStar Λ) 0 ^ 2 * (U1 Λ (2 * s) (GL3Theta.th0 Λ t₀) z * GL3Theta.th0 Λ t₀ z) = U1 Λ s (sgStar Λ) 0 ^ 2 * U1 Λ s (GL3Theta.th0 Λ t₀) 0 ^ 2 * U1 Λ s (GL3Theta.th0 Λ t₀) z ^ 2 + (U1 Λ (2 * s) (GL3Theta.th0 Λ t₀) 0 - U1 Λ s (GL3Theta.th0 Λ t₀) 0 ^ 4) * U1 Λ s (sgStar Λ) z ^ 2 := by
  first | exact @GlobalTheory.EvenTheta.Double.evenTheta_double_translate_mul | exact GlobalTheory.EvenTheta.Double.evenTheta_double_translate_mul | (intros; apply GlobalTheory.EvenTheta.Double.evenTheta_double_translate_mul <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.evenTheta_eq_prod_sigmaStarSquareQuotient : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (k : ℕ) (F : ℂ → ℂ), Differentiable ℂ F → (∀ z, F (-z) = F z) → F 0 = 1 → (∀ ω ∈ Λ, ∀ z, F (z + ω) * sgStar Λ z ^ (2 * k) = F z * sgStar Λ (z + ω) ^ (2 * k)) → ∃ Q : Fin k → ℂ, (∀ i, Q i ∉ Λ) ∧ ∀ z, F z = ∏ i, sqTh Λ (Q i) z := by
  first | exact @GlobalTheory.EvenTheta.exists_eq_prod_sqTh | exact GlobalTheory.EvenTheta.exists_eq_prod_sqTh | (intros; apply GlobalTheory.EvenTheta.exists_eq_prod_sqTh <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.weierstrassP_formalGroupLog_uniformises : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq P : PowerSeries ℂ_[p]), IsWq W wq → IsWpSer (W.c₄ / 12) (W.c₆ / 216) P → PowerSeries.X ^ 2 * (PowerSeries.subst (flog W wq) P : PowerSeries ℂ_[p]) = flog W wq ^ 2 * lineSer wq⁻¹ (-(W.b₂ / 12)) := by
  first | exact @GlobalTheory.WpForm.wp_flog | exact GlobalTheory.WpForm.wp_flog | (intros; apply GlobalTheory.WpForm.wp_flog <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

theorem _root_.GlobalTheory.T.algebraicTaylorCombination_parameterSeries_algebraic : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (ι : Type) [Fintype ι] (φ : ι → ℂ → ℂ) (c : ι → ℂ)
    (E : ℂ → ℂ), AlgEnt E → (∀ k, AlgEnt (φ k)) → (∀ z, E z = ∑ k, c k * φ k z) →
      ∃ a : ι → ℂ, (∀ k, a k ∈ Qbar) ∧ g.atU E = ∑ k, PowerSeries.C (lamC g.lam (a k)) * g.atU (φ k) := by
  first | exact @GlobalTheory.TranslLin.transl_lin | exact GlobalTheory.TranslLin.transl_lin | (intros; apply GlobalTheory.TranslLin.transl_lin <;> assumption)
end
