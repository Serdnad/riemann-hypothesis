module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle070
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedInductionProductParabolicPiTensor
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

theorem _root_.GlobalTheory.T.finiteIntegers_topology : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), CompactSpace (OPart F S) ∧ SecondCountableTopology (OPart F S) ∧ T2Space (OPart F S) := by
  first | exact @GlobalTheory.ModuLR.finiteIntegers_compact_secondCountable_t2 | exact GlobalTheory.ModuLR.finiteIntegers_compact_secondCountable_t2 | (intros; apply GlobalTheory.ModuLR.finiteIntegers_compact_secondCountable_t2 <;> assumption)
end

section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

theorem _root_.GlobalTheory.T.isOpenEmbedding_pairOfTuplesToTupleOfPairs : ∀ (κ X Y : Type) [Fintype κ] [AddCommGroup X] [TopologicalSpace X] [AddCommGroup Y] [TopologicalSpace Y], IsOpenEmbedding (zipHom κ X Y) := by
  first | exact @GlobalTheory.ModuLR.zipHom_isOpenEmbedding | exact GlobalTheory.ModuLR.zipHom_isOpenEmbedding | (intros; apply GlobalTheory.ModuLR.zipHom_isOpenEmbedding <;> assumption)
end

section

open GlobalTheory.RegSS

noncomputable section

open Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.RegSS.IdemDet

theorem exists_factor {F m : Type} [Field F] [Fintype m] [DecidableEq m] (p : Matrix m m F)
    (h0 : p ≠ 0) (hp : p * p = p) :
    ∃ (d : ℕ) (A : Matrix m (Fin d) F) (B : Matrix (Fin d) m F), 0 < d ∧ A * B = p ∧ B * A = 1 := by
  let f := Matrix.toLin' p
  let c := Module.finBasis F (LinearMap.range f)
  let e := Pi.basisFun F m
  have hAB : LinearMap.toMatrix c e (LinearMap.range f).subtype *
      LinearMap.toMatrix e c f.rangeRestrict = p := by
    rw [← LinearMap.toMatrix_comp, show (LinearMap.range f).subtype ∘ₗ f.rangeRestrict = f from rfl]
    simp [e, f]
  refine ⟨_, _, _, ?_, hAB, ?_⟩
  · refine Nat.pos_of_ne_zero fun h => h0 ?_
    haveI : IsEmpty (Fin (Module.finrank F (LinearMap.range f))) := by rw [h]; infer_instance
    rw [← hAB]; ext i j; simp [Matrix.mul_apply]
  · rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_id c]
    congr 1
    ext ⟨_, v, rfl⟩ : 2
    simp [f, hp]

theorem det_smul_idem {R m : Type} [CommRing R] [Fintype m] [DecidableEq m] {d : ℕ}
    (A : Matrix m (Fin d) R) (B : Matrix (Fin d) m R) (h : B * A = 1) (t : R) :
    (t • (A * B) + 1 - A * B).det = t ^ d := by
  have e : t • (A * B) + 1 - A * B = 1 + ((t - 1) • A) * B := by
    rw [Matrix.smul_mul, sub_smul, one_smul]; abel
  rw [e, Matrix.det_one_add_mul_comm, Matrix.mul_smul, h, sub_smul, one_smul, add_sub_cancel]
  simp

section Rep

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {ι : Type} [Fintype ι] [DecidableEq ι]

def regRep (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R] :
    E ⊗[F] R →ₐ[F] Matrix ι ι R :=
  Algebra.TensorProduct.lift
    ((AlgHom.mapMatrix (Algebra.ofId F R)).comp (Algebra.leftMulMatrix b))
    (IsScalarTower.toAlgHom F R (Matrix ι ι R))
    (fun _ a => (Algebra.commutes a _).symm)

theorem regRep_tmul (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R] (x : E) (t : R) :
    regRep b R (x ⊗ₜ t) = t • (Algebra.leftMulMatrix b x).map (algebraMap F R) := by
  refine (Algebra.TensorProduct.lift_tmul _ _ _ x t).trans ?_
  rw [IsScalarTower.toAlgHom_apply, ← Algebra.commutes, ← Algebra.smul_def]
  rfl

theorem continuous_regRep (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] :
    @Continuous _ _ (Formalism.BasicNotions.tensTopL (F := F) (E := E) R) _ (regRep b R) := by
  letI : Algebra R (E ⊗[F] R) := Algebra.TensorProduct.rightAlgebra
  letI := moduleTopology R (E ⊗[F] R)
  haveI : IsModuleTopology R (E ⊗[F] R) := ⟨rfl⟩
  refine IsModuleTopology.continuous_of_ringHom (R := R) (regRep b R).toRingHom ?_
  have : ⇑((regRep b R).toRingHom.comp (algebraMap R (E ⊗[F] R))) =
      fun t : R => t • (Algebra.leftMulMatrix b 1).map (algebraMap F R) :=
    funext fun t => regRep_tmul b R 1 t
  rw [this]
  fun_prop

variable {n : Type} [Fintype n] [DecidableEq n]

def blockRep (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R] :
    Matrix n n (E ⊗[F] R) →+* Matrix (n × ι) (n × ι) R :=
  (Matrix.compRingEquiv n ι R).toRingHom.comp (regRep b R).toRingHom.mapMatrix

def blockRat (b : Module.Basis ι F E) : Matrix n n E →+* Matrix (n × ι) (n × ι) F :=
  (Matrix.compRingEquiv n ι F).toRingHom.comp (Algebra.leftMulMatrix b).toRingHom.mapMatrix

theorem blockRep_apply (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R]
    (g : Matrix n n (E ⊗[F] R)) (i j : n × ι) :
    blockRep b R g i j = regRep b R (g i.1 j.1) i.2 j.2 := rfl

theorem blockRat_apply (b : Module.Basis ι F E) (g : Matrix n n E) (i j : n × ι) :
    blockRat b g i j = Algebra.leftMulMatrix b (g i.1 j.1) i.2 j.2 := rfl

theorem blockRat_injective (b : Module.Basis ι F E) :
    Function.Injective (blockRat (n := n) b) := by
  intro g h e
  ext i j
  apply Algebra.leftMulMatrix_injective b
  ext k l
  exact congrFun (congrFun e (i, k)) (j, l)

theorem blockRep_map (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R]
    (g : Matrix n n E) :
    blockRep b R (g.map (inclE (F := F) R)) = (blockRat b g).map (algebraMap F R) := by
  ext i j
  rw [blockRep_apply, Matrix.map_apply, Matrix.map_apply, blockRat_apply]
  change regRep b R (g i.1 j.1 ⊗ₜ 1) _ _ = _
  rw [regRep_tmul, one_smul, Matrix.map_apply]

theorem blockRep_smul (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R]
    (t : R) (g : Matrix n n (E ⊗[F] R)) :
    blockRep b R (((1 : E) ⊗ₜ[F] t) • g) = t • blockRep b R g := by
  ext i j
  rw [blockRep_apply, Matrix.smul_apply, Matrix.smul_apply, blockRep_apply, smul_eq_mul, map_mul,
    regRep_tmul, map_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.smul_mul,
    Matrix.one_mul, Matrix.smul_apply]

end Rep

end GlobalTheory.RegSS.IdemDet

namespace GlobalTheory.RegSS

open IdemDet

theorem idempotentDet : IdempotentDet := by
  intro F E _ _ _ _ n _ _ ε h0 hε R _ _ _ _
  letI : TopologicalSpace (E ⊗[F] R) := Formalism.BasicNotions.tensTopL (F := F) (E := E) R
  let b := Module.finBasis F E
  have hq : blockRat b ε * blockRat b ε = blockRat b ε := by rw [← map_mul, hε]
  obtain ⟨d, A, B, hd, hAB, hBA⟩ := exists_factor (blockRat b ε)
    (fun h => h0 (blockRat_injective b (by rw [h, map_zero]))) hq
  set p := blockRep b R (ε.map (inclE (F := F) R)) with hp
  have hpq : p = (blockRat b ε).map (algebraMap F R) := blockRep_map b R ε
  have hpp : p * p = p := by rw [hpq, ← Matrix.map_mul, hq]
  refine ⟨d, fun g => (blockRep b R g * p + 1 - p).det, hd, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : Continuous (blockRep (n := n) b R) := by
      refine continuous_matrix fun i j => ?_
      exact ((continuous_regRep b R).comp (continuous_id.matrix_elem i.1 j.1)).matrix_elem i.2 j.2
    exact (((hc.matrix_mul continuous_const).add continuous_const).sub continuous_const).matrix_det
  · simp
  · intro g h hh
    have hc : blockRep b R h * p = p * blockRep b R h := by
      rw [hp, ← map_mul, ← map_mul, hh]
    have h1 : p * (blockRep b R h * p) = blockRep b R h * p := by
      rw [← mul_assoc, ← hc, mul_assoc, hpp]
    simp only
    rw [← Matrix.det_mul, map_mul]
    congr 1
    simp only [mul_sub, sub_mul, mul_add, add_mul, mul_assoc, h1, hpp, mul_one, one_mul]
    abel
  · intro g
    refine ⟨(blockRat b g * blockRat b ε + 1 - blockRat b ε).det, ?_⟩
    simp only
    rw [RingHom.map_det, map_sub, map_add (f := _), map_mul, map_one, blockRep_map, hpq]
    rfl
  · intro g t hg
    have h1 : blockRep b R g * p = t • p := by
      rw [hp, ← map_mul, hg, blockRep_smul]
    simp only
    rw [h1, hpq, ← hAB, Matrix.map_mul]
    refine det_smul_idem _ _ ?_ t
    rw [← Matrix.map_mul, hBA, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.RegSS
end
end

section

open GlobalTheory.RegSS GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem exists_sq_of_not_isField_tensor {F E K : Type} [Field F] [CommRing E] [Algebra F E]
    [Field K] [Algebra F K] (b : Module.Basis (Fin 2) F E) (d : F) (h0 : b 0 = 1)
    (h1 : b 1 * b 1 = algebraMap F E d) (h : ¬ IsField (K ⊗[F] E)) :
    ∃ c : K, c * c = algebraMap F K d := by
  by_contra hc
  push_neg at hc
  apply h
  let B := Algebra.TensorProduct.basis K b
  have hB0 : B 0 = 1 := by simp [B, h0, Algebra.TensorProduct.one_def]
  have hB1 : B 1 * B 1 = algebraMap F K d • (1 : K ⊗[F] E) := by
    simp only [B, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, h1,
      mul_one, algebraMap_smul]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, Algebra.TensorProduct.one_def]
  refine ⟨⟨0, 1, ?_⟩, mul_comm, fun {x} hx => ?_⟩
  · rw [← hB0]; exact (B.ne_zero 0).symm
  · have hs := B.sum_repr x
    rw [Fin.sum_univ_two, hB0] at hs
    set s := B.repr x 0
    set t := B.repr x 1
    have hn : s * s - algebraMap F K d * (t * t) ≠ 0 := by
      intro hn
      by_cases ht : t = 0
      · have hs0 : s = 0 := by simpa [ht] using hn
        exact hx (by rw [← hs, hs0, ht]; simp)
      · refine hc (s / t) ?_
        field_simp
        linear_combination hn
    refine ⟨(s * s - algebraMap F K d * (t * t))⁻¹ • (s • (1 : K ⊗[F] E) - t • B 1), ?_⟩
    have : x * (s • (1 : K ⊗[F] E) - t • B 1) =
        (s * s - algebraMap F K d * (t * t)) • (1 : K ⊗[F] E) := by
      rw [← hs]
      simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hB1, one_mul, mul_one]
      module
    rw [mul_smul_comm, this, smul_smul, inv_mul_cancel₀ hn, one_smul]

theorem splitIdempotents : SplitIdempotents := by
  intro F E _ _ _ _ σ hσ P _ _ k K _ _ ⟨e⟩
  classical
  obtain ⟨b, d, h0, hb, hd, h1⟩ := quad_exists_basis hσ
  have hc : ∀ i : {i : Fin k // ¬ IsField (K i ⊗[F] E)}, ∃ c : K i, c * c * algebraMap F _ d = 1 := by
    intro i
    obtain ⟨c, hc⟩ := exists_sq_of_not_isField_tensor b d h0 h1 i.2
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hd ((algebraMap F (K i)).injective (by simpa using hc.symm))
    exact ⟨c⁻¹, by rw [← hc]; field_simp⟩
  choose c hc using hc
  let u : {i : Fin k // ¬ IsField (K i ⊗[F] E)} → P := fun i => e.symm (Pi.single i.1 1)
  let v : {i : Fin k // ¬ IsField (K i ⊗[F] E)} → P := fun i => e.symm (Pi.single i.1 (c i))
  have same : ∀ (i : Fin k) (x y : K i), e.symm (Pi.single i x) * e.symm (Pi.single i y) =
      e.symm (Pi.single i (x * y)) := fun i x y => by rw [← map_mul, Pi.single_mul]
  have diff : ∀ (i j : Fin k) (x : K i) (y : K j), i ≠ j →
      e.symm (Pi.single i x) * e.symm (Pi.single j y) = 0 := fun i j x y hij => by
    rw [← map_mul, ← map_zero e.symm]
    congr 1
    ext l
    by_cases hl : l = i
    · subst hl; simp [Pi.single_eq_of_ne hij]
    · simp [Pi.single_eq_of_ne hl]
  have hUU : ∀ i, (u i ⊗ₜ[F] (1 : E)) * (u i ⊗ₜ[F] (1 : E)) = u i ⊗ₜ[F] (1 : E) := fun i => by
    simp [u, same]
  have hUV : ∀ i, (u i ⊗ₜ[F] (1 : E)) * (v i ⊗ₜ[F] b 1) = v i ⊗ₜ[F] b 1 := fun i => by
    simp [u, v, same]
  have hVV : ∀ i, (v i ⊗ₜ[F] b 1) * (v i ⊗ₜ[F] b 1) = u i ⊗ₜ[F] (1 : E) := fun i => by
    rw [Algebra.TensorProduct.tmul_mul_tmul, h1, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    simp only [u, v, same]
    rw [← map_smul, ← Pi.single_smul, Algebra.smul_def, mul_comm, hc]
  have hconj : ∀ j, tConj P σ ((2⁻¹ : F) • (u j ⊗ₜ[F] (1 : E) + v j ⊗ₜ[F] b 1)) =
      (2⁻¹ : F) • (u j ⊗ₜ[F] (1 : E) - v j ⊗ₜ[F] b 1) := fun j => by
    simp [tConj, hb, TensorProduct.tmul_neg, sub_eq_add_neg]
  refine ⟨fun i => (2⁻¹ : F) • (u i ⊗ₜ[F] (1 : E) + v i ⊗ₜ[F] b 1), fun i hi => ?_, fun i => ?_,
    fun i j hij => ?_, fun i j => ?_⟩
  · have hi' : u i ⊗ₜ[F] (b 0) + v i ⊗ₜ[F] b 1 = 0 := by
      rw [h0]; exact (smul_eq_zero.1 hi).resolve_left (inv_ne_zero two_ne_zero)
    have h2 := congrArg (fun x => (Algebra.TensorProduct.basis P b).repr x 0) hi'
    simp only [map_add (f := _), Finsupp.add_apply, Algebra.TensorProduct.basis_repr_tmul] at h2
    have h3 : u i = 0 := by simpa using h2
    have h4 := congrFun (e.symm.injective (h3.trans (map_zero e.symm).symm)) i.1
    simp at h4
  · simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, hUU, hVV, hUV,
      mul_comm (v i ⊗ₜ[F] b 1) (u i ⊗ₜ[F] (1 : E))]
    module
  · have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    simp [add_mul, mul_add, u, v, diff _ _ _ _ hij']
  · rw [hconj]
    by_cases hij : i = j
    · subst hij
      simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_sub, hUU, hVV, hUV,
        mul_comm (v i ⊗ₜ[F] b 1) (u i ⊗ₜ[F] (1 : E))]
      module
    · have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      simp [add_mul, mul_sub, u, v, diff _ _ _ _ hij']

end GlobalTheory.RegSS
end

section

open GlobalTheory.RegSS

noncomputable section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS.SplitRankBound

theorem zpow_sum_eq {M : Type} [CommGroup M] (a : M) {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, _root_.zpow_add, ih]

theorem two_zpow_eq_one {F : Type} [Field F] [CharZero F] {m : ℤ} (h : (2:F) ^ m = 1) : m = 0 := by
  have h2 : ((2:ℚ) ^ m : ℚ) = (2:ℚ) ^ (0:ℤ) := by
    rw [zpow_zero]
    apply (algebraMap ℚ F).injective
    rw [map_zpow₀, map_ofNat, h, map_one]
  exact (zpow_right_strictMono₀ one_lt_two).injective h2


theorem splitRankUpper (hL : SubtorusLaurent) (hM : CharacterMonomial) (hP : SeparatingPoints) :
    SplitRankUpper := by
  intro F E _ _ _ _ n _ _ σ J γ hR hPl hPC k K _ _ he s hA
  classical
  obtain ⟨A⟩ := hA
  haveI : Module.Finite F (plusAlg σ J (γ : Matrix n n E)) := Module.Finite.of_basis hPl.2.1.some
  obtain ⟨ψ, hsep, hfield⟩ := hP F E σ hR.quad (plusAlg σ J (γ : Matrix n n E)) k K he
  have hinj := (hPC F).1
  have hcent := (hPC F).2.2
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective
    (toMat σ J (γ : Matrix n n E) F).toLinearMap (LinearMap.ker_eq_bot.2 hinj)
  have hρT : ∀ x, ρ (toMat σ J (γ : Matrix n n E) F x) = x := fun x => LinearMap.congr_fun hρ x
  have hex : ∀ t : Fin s → Fˣ, ∃ u ∈ normOne σ J (γ : Matrix n n E) F,
      toMat σ J (γ : Matrix n n E) F (u : LPts σ J (γ : Matrix n n E) F) =
        ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)) :=
    fun t => (hcent _).1 (A.mem F t)
  have hTu : ∀ t : Fin s → Fˣ, toMat σ J (γ : Matrix n n E) F
      (ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F))) =
        ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)) := by
    intro t; obtain ⟨u, -, hu⟩ := hex t; rw [← hu, hρT]
  have hnorm : ∀ t : Fin s → Fˣ,
      ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)) *
        lConj σ J (γ : Matrix n n E) F (ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)))
          = 1 := by
    intro t; obtain ⟨u, hu, hu'⟩ := hex t; rw [← hu', hρT]; exact hu
  let uu : (Fin s → Fˣ) →* LPts σ J (γ : Matrix n n E) F :=
    { toFun := fun t => ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F))
      map_one' := hinj (by rw [hTu, map_one, Units.val_one, map_one])
      map_mul' := fun a b => hinj (by
        rw [map_mul (toMat σ J (γ : Matrix n n E) F), hTu a, hTu b, ← Units.val_mul, ← map_mul, hTu]) }
  have huu : ∀ t, uu t = ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)) := fun _ => rfl
  clear_value uu
  obtain ⟨S, C, hC⟩ := hL F E n σ J γ s A
  have hmono : ∀ i, ∃ a : Fin s → ℤ, ∀ t : Fin s → Fˣ,
      ψ i (uu t) = algebraMap F (AlgebraicClosure F) ((∏ j, t j ^ a j : Fˣ) : F) := by
    intro i
    refine hM F (AlgebraicClosure F) s ((ψ i : _ →+* AlgebraicClosure F).toMonoidHom.comp uu) S
      (fun a => ψ i (ρ (C a))) (fun t => ?_)

    simp only [MonoidHom.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, RingHom.coe_coe, huu, hC t, map_sum, map_smul]
  choose a ha using hmono
  have hconj : ∀ i t, ψ i (uu t) * ψ i (lConj σ J (γ : Matrix n n E) F (uu t)) = 1 := by
    intro i t; rw [← map_mul, huu, hnorm, map_one]
  have hlc : tConj3 (plusAlg σ J (γ : Matrix n n E)) σ F = lConj σ J (γ : Matrix n n E) F := rfl
  have hsq : ∀ i, IsField (K i ⊗[F] E) → ∀ t : Fin s → Fˣ,
      ((∏ j, t j ^ a i j : Fˣ) : F) * ((∏ j, t j ^ a i j : Fˣ) : F) = 1 := by
    intro i hi t
    have h0 : ψ i (uu t - algebraMap F _ ((∏ j, t j ^ a i j : Fˣ) : F)) = 0 := by
      rw [map_sub, AlgHom.commutes, ha, sub_self]
    have h1 := hfield i hi _ h0
    rw [hlc, map_sub, AlgHom.commutes, map_sub, AlgHom.commutes, sub_eq_zero] at h1
    have h2 := hconj i t
    rw [ha, h1, ← map_mul] at h2
    exact (algebraMap F (AlgebraicClosure F)).injective (h2.trans (map_one _).symm)
  let M : Matrix {i : Fin k // ¬ IsField (K i ⊗[F] E)} (Fin s) ℤ := Matrix.of fun i j => a i.1 j
  have hfinj : Function.Injective M.mulVecLin := by
    refine (injective_iff_map_eq_zero M.mulVecLin).2 fun w hw => ?_
    have hw' : ∀ i : {i : Fin k // ¬ IsField (K i ⊗[F] E)}, ∑ j, a i.1 j * w j = 0 := by
      intro i
      have := congrFun hw i
      simpa [M, Matrix.mulVec, dotProduct] using this
    let u2 : Fˣ := Units.mk0 2 two_ne_zero
    let t : Fin s → Fˣ := fun j => u2 ^ w j
    have hprod : ∀ i, ((∏ j, t j ^ a i j : Fˣ) : F) = (2:F) ^ (∑ j, a i j * w j) := by
      intro i
      have : (∏ j, t j ^ a i j : Fˣ) = u2 ^ (∑ j, a i j * w j) := by
        rw [zpow_sum_eq]
        refine Finset.prod_congr rfl fun j _ => ?_
        simp only [t]
        rw [← _root_.zpow_mul, mul_comm]
      rw [this, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    have hone : ∀ i, ((∏ j, t j ^ a i j : Fˣ) : F) = 1 := by
      intro i
      by_cases hi : IsField (K i ⊗[F] E)
      · have h := hsq i hi t
        rw [hprod, ← zpow_add₀ (two_ne_zero)] at h
        have h0 := two_zpow_eq_one h
        rw [hprod, show ∑ j, a i j * w j = 0 by omega, zpow_zero]
      · rw [hprod, hw' ⟨i, hi⟩, zpow_zero]
    have hψ1 : ∀ i, ψ i (uu t) = 1 := fun i => by rw [ha, hone, map_one]
    have hψc : ∀ i, ψ i (lConj σ J (γ : Matrix n n E) F (uu t)) = 1 := fun i => by
      have h := hconj i t; rwa [hψ1, one_mul] at h
    have hut : uu t = 1 := by
      have := hsep (uu t - 1) fun i => ⟨by rw [map_sub, hψ1, map_one, sub_self],
        by rw [hlc, map_sub, map_sub, hψc, map_one, map_one, sub_self]⟩
      rwa [sub_eq_zero] at this
    have hhom : A.hom F t = A.hom F 1 := by
      refine Units.ext ?_
      rw [(A.hom F).map_one, Units.val_one, ← hTu t, ← huu, hut,
        map_one]
    have ht1 : t = 1 := A.inj F hhom
    funext j
    have hj := congrFun ht1 j
    have hj' : ((u2 ^ w j : Fˣ) : F) = 1 := by
      have := congrArg Units.val hj
      simpa [t] using this
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0] at hj'
    exact two_zpow_eq_one hj'
  have hle := LinearMap.finrank_le_finrank_of_injective hfinj
  rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card] at hle
  rw [Nat.card_eq_fintype_card]
  exact hle

end GlobalTheory.RegSS.SplitRankBound
end
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.normalised_induction_product_parabolic_piTensor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] [LinearOrder β] (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) (Z : α → Type) [∀ i, AddCommGroup (Z i)] [∀ i, Module ℂ (Z i)] (σ : ∀ i, Representation ℂ (GlobalTheory.SmGL.Levi k (c i)) (Z i)), (∀ i, GlobalTheory.PRep.IsSmooth (σ i)) → Nonempty ((GlobalTheory.SmGL.relInd f (GlobalTheory.SmGL.piTensor σ)).Equiv (GlobalTheory.SmGL.piTensor fun i => GlobalTheory.SmGL.parInd (f i) (σ i))) := by
  first | exact @GlobalTheory.SmGL.IndTensor.relInd_piTensor | exact GlobalTheory.SmGL.IndTensor.relInd_piTensor | (intros; apply GlobalTheory.SmGL.IndTensor.relInd_piTensor <;> assumption)
end
