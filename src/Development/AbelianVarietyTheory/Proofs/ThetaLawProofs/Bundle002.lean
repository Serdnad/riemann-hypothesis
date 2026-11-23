module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic.Continuity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

section

open Polynomial
namespace GlobalTheory.LineThrough

theorem exists_common_nonroot (d : ℕ) (S : Set (MvPolynomial (Fin d) ℂ)) (hS : S.Countable)
    (h0 : (0 : MvPolynomial (Fin d) ℂ) ∉ S) :
    ∃ c : Fin d → ℂ, ∀ f ∈ S, MvPolynomial.eval c f ≠ 0 := by
  have hd : Dense (⋂ f ∈ S, {c : Fin d → ℂ | MvPolynomial.eval c f ≠ 0}) := by
    refine dense_biInter_of_isOpen (fun f _ => ?_) hS (fun f hf => ?_)
    · exact isOpen_ne_fun (MvPolynomial.continuous_eval f) continuous_const
    · rw [Metric.dense_iff]
      intro x r hr
      by_contra hne
      apply h0
      have : f = 0 := by
        refine MvPolynomial.funext_set (fun i => Metric.ball (x i) r)
          (fun i => (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)) |> infinite_of_mem_nhds (x i)) ?_
        intro y hy
        by_contra hy0
        apply hne
        refine ⟨y, ?_, by simpa using hy0⟩
        rw [ball_pi _ hr]
        exact hy
      exact this ▸ hf
  obtain ⟨c, hc⟩ := hd.nonempty
  exact ⟨c, fun f hf => by simpa using Set.mem_iInter₂.1 hc f hf⟩

noncomputable def lineMap {d : ℕ} (a c : Fin d → ℂ) : MvPolynomial (Fin d) ℂ →ₐ[ℂ] ℂ[X] :=
  MvPolynomial.aeval fun i => C (a i) + C (c i - a i) * X

theorem eval_zero_lineMap {d : ℕ} (a c : Fin d → ℂ) (f : MvPolynomial (Fin d) ℂ) :
    (lineMap a c f).eval 0 = MvPolynomial.eval a f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [lineMap]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => rw [map_mul, eval_mul, hp]; simp [lineMap]

theorem eval_one_lineMap {d : ℕ} (a c : Fin d → ℂ) (f : MvPolynomial (Fin d) ℂ) :
    (lineMap a c f).eval 1 = MvPolynomial.eval c f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [lineMap]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => rw [map_mul, eval_mul, hp]; simp [lineMap]

theorem lineMap_self {d : ℕ} (a : Fin d → ℂ) (f : MvPolynomial (Fin d) ℂ) :
    lineMap a a f = C (MvPolynomial.eval a f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [lineMap]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => rw [map_mul, hp]; simp [lineMap]

theorem lineMap_surjective {d : ℕ} {a c : Fin d → ℂ} (h : c ≠ a) :
    Function.Surjective (lineMap a c) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  have hi' : c i - a i ≠ 0 := sub_ne_zero.2 hi
  have hX : (X : ℂ[X]) ∈ (lineMap a c).range := by
    refine ⟨MvPolynomial.C (c i - a i)⁻¹ * (MvPolynomial.X i - MvPolynomial.C (a i)), ?_⟩
    simp only [lineMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_sub,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [add_sub_cancel_left, ← mul_assoc, ← C_sub, ← C_mul, inv_mul_cancel₀ hi', C_1, one_mul]
  rw [← AlgHom.range_eq_top, eq_top_iff, ← Polynomial.adjoin_X]
  exact Algebra.adjoin_le (by simpa using hX)

theorem isMaximal_of_ker_lineMap_lt {d : ℕ} (a c : Fin d → ℂ)
    (P : Ideal (MvPolynomial (Fin d) ℂ)) [hP : P.IsPrime] (h : RingHom.ker (lineMap a c) < P) :
    P.IsMaximal := by
  by_cases hc : c = a
  · subst hc
    have hk : RingHom.ker (lineMap c c) = RingHom.ker (MvPolynomial.eval c) := by
      ext f
      simp [RingHom.mem_ker, lineMap_self]
    have hm : (RingHom.ker (MvPolynomial.eval c)).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (fun z => ⟨MvPolynomial.C z, by simp⟩)
    rw [hk] at h
    exact absurd (hm.1.2 P h) hP.ne_top
  · have hs := lineMap_surjective hc
    have hp : (P.map (lineMap a c)).IsPrime := Ideal.map_isPrime_of_surjective hs h.le
    have hcm : (P.map (lineMap a c)).comap (lineMap a c) = P := by
      rw [Ideal.comap_map_of_surjective _ hs, sup_eq_left]
      exact h.le
    have hne : P.map (lineMap a c) ≠ ⊥ := by
      intro hb
      rw [hb] at hcm
      exact h.ne hcm
    have hm : (P.map (lineMap a c)).IsMaximal := Ring.DimensionLEOne.maximalOfPrime hne hp
    rw [← hcm]
    exact Ideal.comap_isMaximal_of_surjective _ hs

theorem exists_prime_dimensionLEOne_avoiding
    (E : Type) [CommRing E] [IsDomain E] [Algebra ℂ E] [Algebra.FiniteType ℂ E]
    (e : E →ₐ[ℂ] ℂ) (T : Set E) (hT : T.Countable) (h0 : (0 : E) ∉ T) :
    ∃ Q : Ideal E, Q.IsPrime ∧ Q ≤ RingHom.ker e ∧ (∀ r ∈ T, r ∉ Q) ∧
      Ring.DimensionLEOne (E ⧸ Q) := by
  obtain ⟨d, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℂ E
  letI : Algebra (MvPolynomial (Fin d) ℂ) E := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) E := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin d) ℂ) E :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have hn : ∀ r : T, ∃ n : MvPolynomial (Fin d) ℂ, n ≠ 0 ∧
      algebraMap _ E n ∈ Ideal.span {(r : E)} := by
    intro r
    have hr : (r : E) ≠ 0 := fun h => h0 (h ▸ r.2)
    have := Ideal.comap_ne_bot_of_integral_mem (R := MvPolynomial (Fin d) ℂ) hr
      (Ideal.mem_span_singleton_self (r : E)) (Algebra.IsIntegral.isIntegral _)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
    exact ⟨n, hn0, hn⟩
  choose n hn0 hn using hn
  haveI : Countable T := hT.to_subtype
  obtain ⟨c, hc⟩ := exists_common_nonroot d (Set.range n) (Set.countable_range n)
    (by rintro ⟨r, hr⟩; exact hn0 r hr)
  let a : Fin d → ℂ := fun i => e (g (MvPolynomial.X i))
  have hea : ∀ f, e (g f) = MvPolynomial.eval a f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r =>
      have : g (MvPolynomial.C r) = algebraMap ℂ E r := g.commutes r
      simp [this]
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp, a]
  haveI hpp : (RingHom.ker (lineMap a c)).IsPrime := RingHom.ker_isPrime _
  haveI hM : (RingHom.ker e).IsPrime := RingHom.ker_isPrime _
  have hle : RingHom.ker (lineMap a c) ≤ (RingHom.ker e).under (MvPolynomial (Fin d) ℂ) := by
    intro f hf
    change e (g f) = 0
    rw [hea, ← eval_zero_lineMap a c, RingHom.mem_ker.1 hf, eval_zero]
  obtain ⟨Q, hQ, hQp, hQo⟩ := Ideal.exists_ideal_le_liesOver_of_le
    (p := RingHom.ker (lineMap a c)) (RingHom.ker e) hle
  have hQc : Q.comap (algebraMap (MvPolynomial (Fin d) ℂ) E) = RingHom.ker (lineMap a c) :=
    hQo.over.symm
  refine ⟨Q, hQp, hQ, fun r hr hrQ => ?_, ⟨fun {P} hP0 hP => ?_⟩⟩
  · have h1 : n ⟨r, hr⟩ ∈ RingHom.ker (lineMap a c) := by
      rw [← hQc]
      exact (Ideal.span_singleton_le_iff_mem _).2 hrQ (hn ⟨r, hr⟩)
    apply hc _ ⟨⟨r, hr⟩, rfl⟩
    rw [← eval_one_lineMap a c, RingHom.mem_ker.1 h1, eval_zero]
  · have hs : Function.Surjective (Ideal.Quotient.mk Q) := Ideal.Quotient.mk_surjective
    have hlt : Q < P.comap (Ideal.Quotient.mk Q) := by
      refine lt_of_le_of_ne (fun x hx => ?_) (fun h => hP0 ?_)
      · simp [Ideal.Quotient.eq_zero_iff_mem.2 hx]
      · rw [← Ideal.map_comap_of_surjective _ hs P, ← h, Ideal.map_quotient_self]
    have hlt' := Ideal.IsIntegral.comap_lt_comap (R := MvPolynomial (Fin d) ℂ) hlt
    change Q.comap (algebraMap (MvPolynomial (Fin d) ℂ) E) < _ at hlt'
    rw [hQc] at hlt'
    have hm := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := MvPolynomial (Fin d) ℂ) _
      (isMaximal_of_ker_lineMap_lt a c _ hlt')
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hs hm with h | h
    · rw [Ideal.map_comap_of_surjective _ hs] at h
      exact absurd h hP.ne_top
    · rwa [Ideal.map_comap_of_surjective _ hs] at h

end GlobalTheory.LineThrough
end

section

open Module

namespace GlobalTheory

theorem card_hom_vanishing_of_diag_basis {M A ι : Type} [AddCommGroup M] [AddCommGroup A]
    [Fintype ι] (N : Submodule ℤ M) (b : Basis ι ℤ M) (c : Basis ι ℤ N) (a : ι → ℤ)
    (h : ∀ i, (c i : M) = a i • b i) :
    Nat.card {f : M →ₗ[ℤ] A // ∀ x ∈ N, f x = 0} = ∏ i, Nat.card {y : A // a i • y = 0} := by
  rw [← Nat.card_pi, ← Nat.card_congr (Equiv.subtypePiEquivPi (p := fun i (y : A) => a i • y = 0))]
  symm
  refine Nat.card_congr ((b.constr ℤ).toEquiv.subtypeEquiv fun y => ?_)
  constructor
  · intro hy x hx
    have : (b.constr ℤ y) ∘ₗ N.subtype = 0 := c.ext fun i => by
      simp [h, hy, -Basis.constr_apply_fintype]
    exact LinearMap.congr_fun this ⟨x, hx⟩
  · intro hy i
    have := hy _ (c i).2
    simpa [h, -Basis.constr_apply_fintype] using this

theorem card_ker_int_matrix_four (G : Type) [CommGroup G] (m r : ℕ)
    (al : Matrix (Fin 4) (Fin 4) ℤ) (hm : 1 ≤ m)
    (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hG : ∀ k : ℕ, k ∣ m → Nat.card {x : G // x ^ k = 1} = k ^ r) :
    Nat.card {ξ : Fin 4 → G // ∀ c, ∏ r', ξ r' ^ al r' c = 1} = m ^ (2 * r) := by
  classical
  have hdet : al.det.natAbs = m ^ 2 := by
    have h1 := congrArg Matrix.det hal
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin] at h1
    have h2 := congrArg Int.natAbs h1
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at h2
    exact Nat.mul_self_inj.mp (by rw [h2]; ring)
  have hdet0 : al.det ≠ 0 := by
    intro h0
    rw [h0] at hdet
    have : 0 < m ^ 2 := by positivity
    simp at hdet
    omega
  have hal' : al * al.transpose = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    have hreg := Matrix.isRegular_of_isLeftRegular_det (A := al)
      (IsRegular.of_ne_zero hdet0).left
    apply hreg.right
    simp only [Matrix.mul_assoc, hal]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  set f : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) := Matrix.toLin' al with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet0 (by simpa [hf] using hv)
  set N := LinearMap.range f with hN
  have hrank : finrank ℤ N = finrank ℤ (Fin 4 → ℤ) :=
    (LinearEquiv.ofInjective f hinj).finrank_eq.symm
  let b0 := Pi.basisFun ℤ (Fin 4)
  let a := Submodule.smithNormalFormCoeffs b0 hrank
  let b := Submodule.smithNormalFormTopBasis b0 hrank
  let c := Submodule.smithNormalFormBotBasis b0 hrank
  have hc : ∀ i, (c i : Fin 4 → ℤ) = a i • b i := Submodule.smithNormalFormBotBasis_def b0 hrank
  have hprod : ∏ i, (a i).natAbs = m ^ 2 := by
    have h1 := Submodule.natAbs_det_equiv N (LinearEquiv.ofInjective f hinj)
    rw [Nat.card_congr (Submodule.quotientEquivPiZMod N b0 hrank).toEquiv, Nat.card_pi] at h1
    simp_rw [Nat.card_zmod] at h1
    rw [← h1, ← hdet, ← LinearMap.det_toLin']
    congr 2
  have hdvd : ∀ i, (a i).natAbs ∣ m := by
    intro i
    have hmem : (m : ℤ) • b i ∈ N := ⟨al.transpose.mulVec (b i), by
      simp [hf, Matrix.mulVec_mulVec, hal', Matrix.smul_mulVec]⟩
    have h1 := congrArg (fun x : N => b.repr (x : Fin 4 → ℤ) i) (c.sum_repr ⟨_, hmem⟩)

    simp only [Submodule.coe_sum, Submodule.coe_smul, hc, map_sum, map_smul, Basis.repr_self,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    exact Int.natAbs_dvd_natAbs.mpr (Dvd.intro_left _ h1)
  have key := card_hom_vanishing_of_diag_basis (A := Additive G) N b c a hc
  have h3 : ∀ i, Nat.card {y : Additive G // a i • y = 0} = (a i).natAbs ^ r := by
    intro i
    rw [← hG _ (hdvd i)]
    refine Nat.card_congr (Additive.toMul.subtypeEquiv fun y => ?_)
    rw [pow_natAbs_eq_one, ← toMul_zsmul, toMul_eq_one]
  simp_rw [h3] at key
  rw [Finset.prod_pow, hprod, ← pow_mul] at key
  rw [← key]
  refine Nat.card_congr (Equiv.subtypeEquiv
    ((Equiv.piCongrRight fun _ => Additive.ofMul).trans (b0.constr ℤ).toEquiv) fun ξ => ?_)
  have h4 : ∀ j, (b0.constr ℤ (fun i => Additive.ofMul (ξ i))) (f (b0 j)) =
      Additive.ofMul (∏ r', ξ r' ^ al r' j) := by
    intro j
    rw [Basis.constr_apply_fintype, ofMul_prod]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [b0, hf, ofMul_zpow]
  constructor
  · rintro hξ _ ⟨x, rfl⟩
    have : (b0.constr ℤ (fun i => Additive.ofMul (ξ i))) ∘ₗ f = 0 :=
      b0.ext fun j => by
        rw [LinearMap.comp_apply, h4, hξ]; rfl
    exact LinearMap.congr_fun this x
  · intro hξ j
    have := hξ (f (b0 j)) ⟨_, rfl⟩
    exact ofMul_eq_zero.mp ((h4 j).symm.trans this)

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericValue

open MvPolynomial

variable {K : Type} [Field K]

theorem exists_algHom_of_isTranscendenceBasis {E Ω ι : Type} [Field E] [Algebra K E] [Field Ω] [IsAlgClosed Ω]
    [Algebra K Ω] {v : ι → E} (hv : IsTranscendenceBasis K v) {T : ι → Ω} (hT : AlgebraicIndependent K T) :
    ∃ j : E →ₐ[K] Ω, ∀ i, j (v i) = T i := by
  let A := Algebra.adjoin K (Set.range v)
  let g : A →ₐ[K] Ω := (aeval T).comp hv.1.aevalEquiv.symm.toAlgHom
  have hg : Function.Injective g := fun p q h =>
    hv.1.aevalEquiv.symm.injective (algebraicIndependent_iff_injective_aeval.1 hT h)
  letI : Algebra A Ω := g.toRingHom.toAlgebra
  haveI : IsScalarTower K A Ω := IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm
  haveI : FaithfulSMul A Ω := (faithfulSMul_iff_algebraMap_injective A Ω).2 hg
  haveI := hv.isAlgebraic
  let j : E →ₐ[A] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨j.restrictScalars K, fun i => ?_⟩
  have h := j.commutes (hv.1.aevalEquiv (X i))
  have e : algebraMap A E (hv.1.aevalEquiv (X i)) = v i := by
    rw [hv.1.algebraMap_aevalEquiv, aeval_X]
  rw [e] at h
  refine h.trans ?_
  show aeval T (hv.1.aevalEquiv.symm (hv.1.aevalEquiv (X i))) = T i
  rw [AlgEquiv.symm_apply_apply, aeval_X]

theorem algebraicIndependent_add_one {E ι : Type} [CommRing E] [Algebra K E] {v : ι → E}
    (hv : AlgebraicIndependent K v) : AlgebraicIndependent K fun i => v i + 1 := by
  have h₁ : AlgebraicIndependent K fun i : ι => (X i + 1 : MvPolynomial ι K) := by
    refine AlgebraicIndependent.of_comp (aeval fun i : ι => (X i - 1 : MvPolynomial ι K)) ?_
    convert algebraicIndependent_X ι K using 1
    ext i
    simp
  convert h₁.map' (algebraicIndependent_iff_injective_aeval.1 hv) using 1
  ext i
  simp

theorem mem_range_of_fixed [IsAlgClosed K] {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (a : Ω)
    (h : ∀ j : Ω →ₐ[K] Ω, j a = a) : a ∈ Set.range (algebraMap K Ω) := by
  by_contra ha
  have ht : Transcendental K a := fun hal => ha <| by
    have := minpoly.mem_range_of_degree_eq_one K a
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hal.isIntegral))
    exact this
  have hi : AlgebraicIndepOn K id ({a} : Set Ω) := by
    unfold AlgebraicIndepOn
    exact (algebraicIndependent_singleton_iff (⟨a, rfl⟩ : ({a} : Set Ω))).2 ht
  obtain ⟨t, hst, hb⟩ := exists_isTranscendenceBasis_superset hi
  obtain ⟨j, hj⟩ := exists_algHom_of_isTranscendenceBasis hb (algebraicIndependent_add_one hb.1)
  have := (h j).symm.trans (hj ⟨a, hst rfl⟩)
  simp at this

abbrev Gen (F I : Type) [Field F] : Type := AlgebraicClosure (FractionRing (MvPolynomial I F))

def genX (F I : Type) [Field F] : I → Gen F I := fun i => algebraMap (MvPolynomial I F) _ (X i)

theorem isTranscendenceBasis_genX (F I : Type) [Field F] : IsTranscendenceBasis F (genX F I) := by
  haveI : Algebra.IsAlgebraic (MvPolynomial I F) (FractionRing (MvPolynomial I F)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  haveI : Algebra.IsAlgebraic (MvPolynomial I F) (Gen F I) :=
    Algebra.IsAlgebraic.trans _ (FractionRing (MvPolynomial I F)) _
  haveI : FaithfulSMul (MvPolynomial I F) (Gen F I) := (faithfulSMul_iff_algebraMap_injective _ _).2 <| by
    rw [IsScalarTower.algebraMap_eq _ (FractionRing (MvPolynomial I F))]
    exact (algebraMap (FractionRing (MvPolynomial I F)) (Gen F I)).injective.comp (IsFractionRing.injective _ _)
  exact (IsTranscendenceBasis.mvPolynomial I F).algebraMap_comp

theorem exists_generization {F I : Type} [Field F] [Algebra K F] (T : I → F) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Algebra K O)
      (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra K Ω) (r : O →ₐ[K] Ω) (e : F →ₐ[K] Ω) (S : I → O),
      RingHom.ker r = IsLocalRing.maximalIdeal O ∧ AlgebraicIndependent K S ∧ r ∘ S = e ∘ T := by
  let Ω := Gen F I
  let P : I → Polynomial Ω := fun i => Polynomial.C (algebraMap F Ω (T i)) +
    Polynomial.C (genX F I i - algebraMap F Ω (T i)) * Polynomial.X
  have hX : AlgebraicIndependent K (genX F I) :=
    (isTranscendenceBasis_genX F I).1.restrictScalars (algebraMap K F).injective
  have hP : AlgebraicIndependent K P := by
    refine AlgebraicIndependent.of_comp ((Polynomial.aeval (1 : Ω)).restrictScalars K) ?_
    convert hX using 1
    ext i
    simp [P]
  let c : Polynomial Ω →ₐ[K] PowerSeries Ω := (Polynomial.coeToPowerSeries.algHom Ω).restrictScalars K
  have hc : Function.Injective c := by
    intro p q h
    apply Polynomial.coe_injective Ω
    simpa [c] using h
  let r : PowerSeries Ω →ₐ[K] Ω :=
    { PowerSeries.constantCoeff (R := Ω) with commutes' := fun a => by simp [PowerSeries.algebraMap_apply] }
  refine ⟨PowerSeries Ω, inferInstance, inferInstance, inferInstance, inferInstance, Ω, inferInstance, inferInstance,
    inferInstance, r, IsScalarTower.toAlgHom K F Ω, c ∘ P, ?_, hP.map' hc, ?_⟩
  · exact PowerSeries.ker_coeff_eq_max_ideal
  · ext i
    simp [r, c, P]

theorem exists_value [IsAlgClosed K] {I : Type}
    (V : ∀ (R : Type) [CommRing R] [Algebra K R], (I → R) → R → Prop)
    (bc : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] [IsLocalRing R']
      [Algebra K R] [Algebra K R'] (j : R →ₐ[K] R') (T : I → R) (a : R), V R T a → V R' (j ∘ T) (j a))
    (uniq : ∀ (F : Type) [Field F] [Algebra K F] (T : I → F) (a a' : F), V F T a → V F T a' → a = a')
    (ex : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (T : I → Ω), AlgebraicIndependent K T → ∃ a, V Ω T a)
    (gg : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (T T' : I → Ω) (a a' : Ω),
      AlgebraicIndependent K (Sum.elim T T') → V Ω T a → V Ω T' a' → a = a')
    (lift : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra K O] (Ω : Type) [Field Ω]
      [IsAlgClosed Ω] [Algebra K Ω] (r : O →ₐ[K] Ω) (T : I → O) (a : Ω),
      RingHom.ker r = IsLocalRing.maximalIdeal O → V Ω (r ∘ T) a →
      ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (_ : Algebra K O')
        (j : O →ₐ[K] O') (r' : O' →ₐ[K] Ω) (u : O'), Function.Injective j ∧ r'.comp j = r ∧ V O' (j ∘ T) u) :
    ∃ κ : K, (∀ (F : Type) [Field F] [Algebra K F] (T : I → F) (a : F), V F T a → a = algebraMap K F κ) ∧
      V (Gen K I) (genX K I) (algebraMap K _ κ) := by
  have hA : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (T T' : I → Ω) (a a' : Ω),
      AlgebraicIndependent K T → AlgebraicIndependent K T' → V Ω T a → V Ω T' a' → a = a' := by
    intro Ω _ _ _ T T' a a' hT hT' h h'
    let j := IsScalarTower.toAlgHom K Ω (Gen Ω I)
    have hX := (isTranscendenceBasis_genX Ω I).1
    obtain ⟨b, hb⟩ := ex (Gen Ω I) _ (hX.restrictScalars (algebraMap K Ω).injective)
    have key : ∀ (S : I → Ω) (c : Ω), AlgebraicIndependent K S → V Ω S c → b = j c := fun S c hS hc =>
      gg (Gen Ω I) _ _ _ _ (hS.sumElim_comp hX) hb (bc Ω _ j S c hc)
    exact j.toRingHom.injective ((key T a hT h).symm.trans (key T' a' hT' h'))
  have hB := isTranscendenceBasis_genX K I
  obtain ⟨a₁, ha₁⟩ := ex (Gen K I) _ hB.1
  obtain ⟨κ, rfl⟩ := mem_range_of_fixed (K := K) a₁ fun j =>
    hA _ _ _ _ _ (hB.1.map' j.toRingHom.injective) hB.1 (bc _ _ j _ _ ha₁) ha₁
  refine ⟨κ, fun F _ _ T a h => ?_, ha₁⟩
  obtain ⟨O, _, _, _, _, Ω, _, _, _, r, e, S, hr, hS, hT⟩ := exists_generization (K := K) T
  have h₁ := bc _ _ e T a h
  rw [← hT] at h₁
  obtain ⟨O', _, _, _, _, j, r', u, hj, hr', hu⟩ := lift O Ω r S _ hr h₁
  have h₂ := bc _ _ r' _ _ hu
  rw [← Function.comp_assoc, ← AlgHom.coe_comp, hr'] at h₂
  have h₃ := uniq _ _ _ _ h₁ h₂
  let Ω' := AlgebraicClosure (FractionRing O')
  let i := IsScalarTower.toAlgHom K O' Ω'
  have hi : Function.Injective i := by
    show Function.Injective (algebraMap O' Ω')
    rw [IsScalarTower.algebraMap_eq _ (FractionRing O')]
    exact (algebraMap (FractionRing O') Ω').injective.comp (IsFractionRing.injective _ _)
  obtain ⟨m, hm⟩ := exists_algHom_of_isTranscendenceBasis hB ((hS.map' hj).map' hi)
  have h₄ := bc _ _ m _ _ ha₁
  rw [show m ∘ genX K I = i ∘ j ∘ S from funext hm] at h₄
  have h₅ : u = algebraMap K O' κ := hi ((uniq _ _ _ _ (bc _ _ i _ _ hu) h₄).trans (by simp))
  apply e.toRingHom.injective
  simpa [h₅] using h₃

end GlobalTheory.GenericValue
end
end
