module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle062
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OmFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

section

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem cardZ {k D M : Type} [CommRing k] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module k M]
    [Finite M] [TopologicalSpace M] [DiscreteTopology M] (σ : Representation k D M) (hσ : ContAction σ)
    [Finite (H1 σ)] : Finite (Z1 σ) ∧ Nat.card (Z1 σ) * Nat.card (H0 σ) = Nat.card (H1 σ) * Nat.card M := by
  have hle : ReciprocityTheory.Gal.B1 σ ≤ Z1 σ := by
    rintro _ ⟨m, rfl⟩
    refine ⟨(hσ.comp (continuous_id.prodMk continuous_const)).sub continuous_const, fun g h => ?_⟩
    simp only [amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]
    abel
  have hker : LinearMap.ker (d0 σ) = H0 σ := by
    ext m
    rw [LinearMap.mem_ker, mem_riemannRochSpace_iff_regularAt_everywhere, funext_iff]
    simp only [amitsur_d0_apply, Pi.zero_apply, sub_eq_zero]
  have h1 : Nat.card M = Nat.card (H0 σ) * Nat.card (ReciprocityTheory.Gal.B1 σ) := by
    rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (d0 σ)), hker.symm,
      Nat.card_congr (d0 σ).quotKerEquivRange.toEquiv]
    rfl
  have h2 : Nat.card (Z1 σ) = Nat.card (ReciprocityTheory.Gal.B1 σ) * Nat.card (H1 σ) := by
    rw [Submodule.card_eq_card_quotient_mul_card ((ReciprocityTheory.Gal.B1 σ).comap (Z1 σ).subtype),
      Nat.card_congr (Submodule.comapSubtypeEquivOfLe hle).toEquiv]
  have hM : Nat.card M ≠ 0 := Nat.card_pos.ne'
  refine ⟨Nat.finite_of_card_ne_zero ?_, by rw [h1, h2]; ring⟩
  rw [h2]
  exact mul_ne_zero (right_ne_zero_of_mul (h1 ▸ hM)) Nat.card_pos.ne'

private theorem cardInv {n : ℕ} [NeZero n] {D M M' : Type} [Group D] [AddCommGroup M] [Module (ZMod n) M]
    [AddCommGroup M'] [Module (ZMod n) M'] [Finite M] [Finite M'] (χ : D →* (ZMod n)ˣ)
    (σ : Representation (ZMod n) D M) (τ : D → M' → M') (b : M →+ M' →+ ZMod n)
    (hl : ∀ x, (∀ y, b x y = 0) → x = 0) (hr : ∀ y, (∀ x, b x y = 0) → y = 0)
    (he : ∀ g x y, b (σ g x) (τ g y) = χ g * b x y) :
    Nat.card (H0 ((twDual χ σ).comp (MonoidHom.id D))) = Nat.card {y : M' // ∀ g, τ g y = y} := by
  let f : M' → Module.Dual (ZMod n) M := fun y => (b.flip y).toZModLinearMap n
  have hb : Function.Bijective f := (dualZ n M).2.2 M' b hl hr
  have hf := hb.1
  have key : ∀ g y x, twDual χ σ g (f y) x = b x (τ g y) := fun g y x => by
    have := he g (σ g⁻¹ x) y
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    exact this.symm
  refine (Nat.card_congr ((Equiv.ofBijective f hb).subtypeEquiv fun y => ?_)).symm
  constructor
  · intro h g
    refine LinearMap.ext fun x => (key g y x).trans ?_
    rw [h]; rfl
  · intro h g
    refine hf (LinearMap.ext fun x => (key g y x).symm.trans ?_)
    exact congrArg (fun φ : TDual (ZMod n) M => φ x) (h g)

private def zRep (n : ℕ) {R D M : Type} [CommRing R] [Group D] [AddCommGroup M] [Module R M] [Module (ZMod n) M]
    (ρ : Representation R D M) : Representation (ZMod n) D M where
  toFun g := (ρ g).toAddMonoidHom.toZModLinearMap n
  map_one' := LinearMap.ext fun m => by
    show ρ 1 m = m
    rw [map_one]; rfl
  map_mul' g h := LinearMap.ext fun m => by
    show ρ (g * h) m = ρ g (ρ h m)
    rw [map_mul]; rfl

theorem UpperTheory.V.Th.locCntBare :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → (((l : ℕ) : 𝓞 F) ∈ v.asIdeal → LocCnt (Dec (F := F) A) ((cycZ F Ω l).comp (Dec (F := F) A).subtype) (locDeg v)) ∧ (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → LocCnt (Dec (F := F) A) ((cycZ F Ω l).comp (Dec (F := F) A).subtype) 0) := by
  intro hF hT hE l _ F Ω _ _ _ _ _ A v hA
  suffices H : ∀ d, ((((l : ℕ) : 𝓞 F) ∈ v.asIdeal ∧ d = locDeg v) ∨ (((l : ℕ) : 𝓞 F) ∉ v.asIdeal ∧ d = 0)) →
      LocCnt (Dec (F := F) A) ((cycZ F Ω l).comp (Dec (F := F) A).subtype) d from
    ⟨fun h => H _ (.inl ⟨h, rfl⟩), fun h => H _ (.inr ⟨h, rfl⟩)⟩
  intro d hd k hk R M M' _ _ _ _ _ _ _ ρ ρ' b hρ hb
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hl0 : ∀ z : ZMod (l ^ k), l ^ k • z = 0 := fun z => by
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ k)) M) := ⟨AddCommGroup.zmodModule fun x => hb.left _ fun y => by
    rw [map_nsmul, AddMonoidHom.nsmul_apply, hl0]⟩
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ k)) M') := ⟨AddCommGroup.zmodModule fun y => hb.right _ fun x => by
    rw [map_nsmul, hl0]⟩
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  let σ : Representation (ZMod (l ^ k)) (Dec (F := F) A) M := zRep (l ^ k) ρ
  have hσ : ContAction σ := continuous_prod_of_discrete_right.2 fun m => (hρ m).continuous
  obtain ⟨-, f1, -, -⟩ := hF F Ω l k M A σ v hk hA hσ
  obtain ⟨⟨inv⟩, -, -, -, h20⟩ := hT F Ω l k M A σ v hk hA hσ
  have hE' := hE F Ω l k M A σ v hk hA hσ
  have e1 : Nat.card (H1 σ) = Nat.card (H0 σ) * Nat.card (H2 σ) * Nat.card M ^ d := by
    rcases hd with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · exact hE'.1 h
    · rw [pow_zero, mul_one]; exact hE'.2 h
  obtain ⟨fz, e2⟩ := cardZ σ hσ
  let EZ : Zl ρ ≃ Z1 σ := Equiv.subtypeEquivRight fun z =>
    and_congr (IsLocallyConstant.iff_continuous z) Iff.rfl
  let χ := (cycMod F Ω l k).comp (Dec (F := F) A).subtype
  have e3 := cardInv χ σ (fun g y => ρ' g y) b hb.left hb.right (fun g x y => hb.equiv g x y)
  haveI : Finite (TDual (ZMod (l ^ k)) M) := (DFunLike.finite _ : Finite (M →ₗ[ZMod (l ^ k)] ZMod (l ^ k)))
  let B : Type := H0 ((twDual χ σ).comp (MonoidHom.id _))
  let E : H2 σ ≃ Module.Dual (ZMod (l ^ k)) B :=
    (Equiv.ofBijective _ h20).trans (LinearEquiv.congrRight inv).toEquiv
  haveI : Finite B := Subtype.finite
  have e4 : Nat.card (H2 σ) = Nat.card ρ'.invariants := by
    rw [Nat.card_congr E, (dualZ (l ^ k) B).1]
    exact e3
  refine ⟨Finite.of_equiv _ EZ.symm, ?_⟩
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H0 σ))
  rw [Nat.card_congr EZ, e2, e1, e4]
  ring
end

section

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem card_lt' (n : ℕ) : Fintype.card {p : Fin n × Fin n // p.1 < p.2} = n.choose 2 := by
  rw [Fintype.card_subtype]
  have := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n)))
  simpa using this

private theorem card_le' (n : ℕ) : Fintype.card {p : Fin n × Fin n // p.1 ≤ p.2} = n + n.choose 2 := by
  rw [← card_lt' n]
  have e : {p : Fin n × Fin n // p.1 ≤ p.2} ≃ Fin n ⊕ {p : Fin n × Fin n // p.1 < p.2} :=
    { toFun := fun p => if h : p.1.1 < p.1.2 then .inr ⟨p.1, h⟩ else .inl p.1.1
      invFun := Sum.elim (fun i => ⟨(i, i), le_rfl⟩) fun p => ⟨p.1, p.2.le⟩
      left_inv := fun p => by
        by_cases h : p.1.1 < p.1.2
        · simp [h]
        · simp only [h, dite_false, Sum.elim_inl]
          exact Subtype.ext (Prod.ext rfl (le_antisymm p.2 (not_lt.1 h)))
      right_inv := by
        rintro (i | p)
        · simp
        · simp [p.2] }
  rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_fin]

private theorem red_mul {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem red_one {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) : red m (1 : Matrix (Fin n) (Fin n) O) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

private theorem card_up (X : Type) [Zero X] (n : ℕ) :
    Nat.card {Z : Matrix (Fin n) (Fin n) X // ∀ i j, j < i → Z i j = 0} = Nat.card X ^ (n + n.choose 2) := by
  rw [← card_le', ← Nat.card_eq_fintype_card, ← Nat.card_fun]
  exact Nat.card_congr
    { toFun := fun Z p => Z.1 p.1.1 p.1.2
      invFun := fun f => ⟨Matrix.of fun i j => if h : i ≤ j then f ⟨(i, j), h⟩ else 0, fun i j h => by simp [not_le.2 h]⟩
      left_inv := fun Z => Subtype.ext (Matrix.ext fun i j => by
        by_cases h : i ≤ j
        · simp [h]
        · simp [h, Z.2 i j (not_le.1 h)])
      right_inv := fun f => funext fun p => by simp [p.2] }

theorem UpperTheory.V.Th.borCard :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ) (v : L.Vl), Nat.card (bor y m v) = Nat.card (ResidueField O) ^ (m * (n + n.choose 2)) := by
  intro l _ L G0 O _ _ _ _ _ n y m v
  have i1 : red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * red m (y.w v : Matrix (Fin n) (Fin n) O) = 1 := by
    rw [← red_mul, Units.inv_mul, red_one]
  have i2 : red m (y.w v : Matrix (Fin n) (Fin n) O) * red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = 1 := by
    rw [← red_mul, Units.mul_inv, red_one]
  rw [pow_mul, ← ((omFacts l O).2 m).2.1, ← card_up]
  generalize hw : red m (y.w v : Matrix (Fin n) (Fin n) O) = w at i1 i2
  generalize hwi : red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = wi at i1 i2
  have hm : ∀ Z, Z ∈ bor y m v ↔ ∀ i j, j < i → (wi * Z * w) i j = 0 := fun Z => by rw [← hw, ← hwi]; rfl
  exact Nat.card_congr
    { toFun := fun Z => ⟨wi * Z.1 * w, (hm _).1 Z.2⟩
      invFun := fun U => ⟨w * U.1 * wi, (hm _).2 (by
        rw [← mul_assoc, ← mul_assoc, i1, one_mul, mul_assoc, i1, mul_one]; exact U.2)⟩
      left_inv := fun Z => Subtype.ext (by
        show w * (wi * Z.1 * w) * wi = Z.1
        rw [← mul_assoc, ← mul_assoc, i2, one_mul, mul_assoc, i2, mul_one])
      right_inv := fun U => Subtype.ext (by
        show wi * (w * U.1 * wi) * w = U.1
        rw [← mul_assoc, ← mul_assoc, i1, one_mul, mul_assoc, i1, mul_one]) }
end

section

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem dO_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.S6.norm_le_one_of_isIntegral l x hx

private theorem dO_small {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (y : A →+* PadicAlgCl l) (hle : ∀ x, ‖y x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ z ∈ maximalIdeal A ^ n, ‖y z‖ < ε := by
  have hl0 : ((l : ℕ) : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hl : (l : A) ≠ 0 := fun h => hl0 (by simpa using congrArg y h)
  have hl1 : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hϖ
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hl1
  refine ⟨e * n, fun z hz => ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hz
  have hd : (l : A) ^ n ∣ z := by
    refine Dvd.dvd.trans ?_ hz
    rw [pow_mul, hu]
    exact pow_dvd_pow_of_dvd (Units.mul_left_dvd.2 dvd_rfl) n
  obtain ⟨w, rfl⟩ := hd
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (hle w)) hn

private theorem dO_desc {O Q : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field Q] [Algebra O Q]
    (hinj : Function.Injective (algebraMap O Q)) {n : ℕ} (Y : Matrix (Fin n) (Fin n) Q) :
    ∃ (a : O) (Y0 : Matrix (Fin n) (Fin n) O), a ≠ 0 ∧ ∀ (e : O) (A B Z : Matrix (Fin n) (Fin n) O),
      Z.map (algebraMap O Q) = algebraMap O Q e • (A.map (algebraMap O Q) * Y * B.map (algebraMap O Q)) - Y →
      a • Z = e • (A * Y0 * B) - Y0 := by
  haveI : FaithfulSMul O Q := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  let N : Submodule O Q := Submodule.span O (insert 1 (Set.range fun p : Fin n × Fin n => Y p.1 p.2))
  haveI : Module.Finite O N := Module.Finite.span_of_finite O ((Set.finite_range _).insert _)
  let one : N := ⟨1, Submodule.subset_span (Set.mem_insert _ _)⟩
  let Yn : Fin n → Fin n → N := fun i j => ⟨Y i j, Submodule.subset_span (Set.mem_insert_of_mem _ ⟨(i, j), rfl⟩)⟩
  have h1 : one ≠ 0 := fun h => one_ne_zero (congrArg Subtype.val h)
  obtain ⟨π, hπ⟩ := Module.Projective.exists_dual_ne_zero O h1
  refine ⟨π one, Matrix.of fun i j => π (Yn i j), hπ, fun e A B Z h => ?_⟩
  ext i j
  have h2 : Z i j • one = e • (∑ k, ∑ m, (A i m * B k j) • Yn m k) - Yn i j := by
    apply Subtype.ext
    have := congrFun (congrFun h i) j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul] at this
    simp only [one, Yn, Submodule.coe_smul, Submodule.coe_sub, Submodule.coe_sum, Algebra.smul_def, mul_one, this, map_mul,
      Finset.sum_mul]
    congr 2
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
  have h3 := congrArg π h2

  simp only [map_smul, map_sub, map_sum, smul_eq_mul] at h3
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Matrix.of_apply, Finset.sum_mul]
  rw [mul_comm, h3]
  congr 2
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring

private theorem dO_pol {O : Type} [CommRing O] {n : ℕ} (P P' A A' B B' Y Z W : Matrix (Fin n) (Fin n) O) (s s' e a : O)
    (hP : P * P' = 1) (hP' : P' * P = 1) (hA : A * A' = 1) (hA' : A' * A = 1) (hs : s * s' = 1)
    (h1 : Aᵀ * P * B = s • P) (h2 : A'ᵀ * P * B' = s' • P) (hz : P * W = Zᵀ * P)
    (hc : a • Z = e • (A * Y * A') - Y) :
    a • W = e • (B * (P' * Yᵀ * P) * B') - P' * Yᵀ * P := by
  have e1 : P * B = s • (A'ᵀ * P) := by
    rw [← Matrix.mul_smul, ← h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hA]; simp
  have e2 : P * B' = s' • (Aᵀ * P) := by
    rw [← Matrix.mul_smul, ← h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hA']; simp
  have e3 : P * (a • W) = P * (e • (B * (P' * Yᵀ * P) * B') - P' * Yᵀ * P) := by
    have f1 : P * (B * (P' * Yᵀ * P) * B') = (P * B) * P' * Yᵀ * (P * B') := by simp only [Matrix.mul_assoc]
    have f2 : P * (P' * Yᵀ * P) = Yᵀ * P := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP, Matrix.one_mul]
    have f3 : A'ᵀ * P * P' = A'ᵀ := by rw [Matrix.mul_assoc, hP, Matrix.mul_one]
    rw [Matrix.mul_smul, hz, ← Matrix.smul_mul, ← Matrix.transpose_smul, hc, Matrix.mul_sub, Matrix.mul_smul, f1, f2, e1, e2,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul s, hs, one_smul, f3]
    simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.mul_assoc]
  have := congrArg (P' * ·) e3
  simpa only [← Matrix.mul_assoc, hP', Matrix.one_mul] using this

private theorem dO_sym {O : Type} [CommRing O] {n : ℕ} (P P' Y : Matrix (Fin n) (Fin n) O)
    (hP : P * P' = 1) (hP' : P' * P = 1) (hs : Pᵀ = P ∨ Pᵀ = -P) :
    P * (Y + P' * Yᵀ * P) = (Y + P' * Yᵀ * P)ᵀ * P := by
  have f2 : P * (P' * Yᵀ * P) = Yᵀ * P := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP, Matrix.one_mul]
  have f0 : P'ᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, hP, Matrix.transpose_one]
  have f3 : (P' * Yᵀ * P)ᵀ * P = P * Y := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rcases hs with h | h
    · rw [h] at f0
      rw [f0, h, Matrix.mul_one]
    · rw [h, Matrix.mul_neg, neg_eq_iff_eq_neg] at f0
      rw [f0, h]; simp
  rw [Matrix.mul_add, Matrix.transpose_add, Matrix.add_mul, f2, f3, add_comm]

theorem UpperTheory.V.Th.detO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (c : Coef l) (n : ℕ) (y : Pt G0.frame c.O n) (S : Set G0.G₀), l ≠ 2 → DetQ G0.frame c.O (pushRep (algebraMap c.O (Qbar l)) y.ρ) (GeneralLinearGroup.map (algebraMap c.O (Qbar l)) y.P) S → DetO y S := by
  intro l _ L G0 c n y S _ hQ z hcont hcoc hpol htr
  set f := algebraMap c.O (Qbar l) with hf
  have hinj : Function.Injective f := Subtype.val_injective
  have hle : ∀ x : c.O, ‖f x‖ ≤ 1 := fun x =>
    dO_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map c.O.val)
  have hm : ∀ g, mat (pushRep f y.ρ) g = (mat y.ρ g).map f := fun g => rfl
  have hP : ((GeneralLinearGroup.map f y.P : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
    (y.P : Matrix (Fin n) (Fin n) c.O).map f := rfl
  have he : ∀ g : G0.G₀, ((G0.frame.eps c.O (Qbar l) g : (Qbar l)ˣ) : Qbar l) =
    f (algebraMap ℤ_[l] c.O (G0.ε g : ℤ_[l])) := fun g => rfl
  obtain ⟨Y, hY⟩ := hQ (fun g => (z g).map f) (by
      refine continuous_matrix fun a b => continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_
      obtain ⟨k, hk⟩ := dO_small f hle hε
      filter_upwards [(hcont a b k).eventually_eq g] with g' hg'
      rw [dist_eq_norm, Matrix.map_apply, Matrix.map_apply, ← map_sub]
      exact hk _ (Ideal.Quotient.eq.1 hg'))
    (fun g g' => by
      rw [hcoc, hm, hm, he, Matrix.map_add _ (map_add f), ← Matrix.map_mul, ← Matrix.map_mul]
      congr 1
      all_goals (ext i j; simp))
    (fun g => by rw [hP, ← Matrix.map_mul, hpol, Matrix.map_mul, Matrix.transpose_map])
    (fun σ hσ k => by
      rw [← map_pow, hm, ← Matrix.map_mul, ← AddMonoidHom.map_trace, map_pow, htr σ hσ k, map_zero])
  obtain ⟨a, Y0, ha, hY0⟩ := dO_desc hinj Y
  have hc : ∀ g : G0.G₀, a • z g = algebraMap ℤ_[l] c.O (G0.ε g : ℤ_[l]) • (mat y.ρ g * Y0 * mat y.ρ g⁻¹) - Y0 :=
    fun g => hY0 _ _ _ _ (hY g)
  have hP1 : (y.P : Matrix (Fin n) (Fin n) c.O) * (y.P⁻¹ : GL (Fin n) c.O) = 1 := Units.mul_inv _
  have hP2 : ((y.P⁻¹ : GL (Fin n) c.O) : Matrix (Fin n) (Fin n) c.O) * y.P = 1 := Units.inv_mul _
  refine ⟨a + a, Y0 + (y.P⁻¹ : GL (Fin n) c.O) * Y0ᵀ * y.P, ?_, dO_sym _ _ _ hP1 hP2 y.sgn, fun g => ?_⟩
  · rw [← two_mul]
    exact mul_ne_zero two_ne_zero ha
  have hcc : G0.frame.conj (G0.frame.conj g) = g := by
    apply Subtype.ext
    have h2 : G0.c⁻¹ = G0.c := inv_eq_of_mul_eq_one_right G0.c_sq
    show G0.c * (G0.c * g * G0.c⁻¹) * G0.c⁻¹ = g
    rw [h2, ← mul_assoc, ← mul_assoc, G0.c_sq, one_mul, mul_assoc, G0.c_sq, mul_one]
  have hε : G0.ε (G0.frame.conj g : G0.G₀) = G0.ε g := by
    show G0.ε (G0.c * g * G0.c⁻¹) = _
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  have h5 := dO_pol _ _ _ _ _ _ Y0 _ _ _ _ _ a hP1 hP2 (by rw [← map_mul, mul_inv_cancel, map_one])
    (by rw [← map_mul, inv_mul_cancel, map_one])
    (by rw [← Units.val_mul, ← mul_zpow, ← map_mul, mul_inv_cancel, map_one, _root_.one_zpow, Units.val_one])
    (y.form (G0.frame.conj g)) (y.form (G0.frame.conj g)⁻¹) (hpol (G0.frame.conj g)) (hc (G0.frame.conj g))
  rw [map_inv, hcc, hε] at h5
  rw [add_smul, Matrix.mul_add, Matrix.add_mul, smul_add]
  conv_lhs => rw [hc g]; arg 2; rw [← hc g, h5]
  abel
end

section

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem pairO_lin (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (φ : ℤ_[l] →+* R) (k : ℕ)
    (hk : ∀ x : R, l ^ k • x = 0) (τ : R →+ ZMod (l ^ k)) (a : ℤ_[l]) (x : R) :
    τ (φ a * x) = PadicInt.toZModPow k a * τ x := by
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set n : ℕ := (PadicInt.toZModPow k a).val with hn
  have h1 : a - (n : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow k : ℤ_[l] →+* ZMod (l ^ k)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, hn, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
  obtain ⟨b, hb⟩ := h1
  have h2 : a = (n : ℤ_[l]) + (l : ℤ_[l]) ^ k * b := by rw [← hb]; ring
  have h3 : φ a * x = n • x := by
    have := hk (φ b * x)
    rw [nsmul_eq_mul, Nat.cast_pow] at this
    rw [h2, map_add (f := _), map_mul, map_pow, map_natCast, map_natCast, add_mul, mul_assoc, this, add_zero, nsmul_eq_mul]
  rw [h3, map_nsmul, nsmul_eq_mul, hn, ZMod.natCast_zmod_val]

private theorem pairO_dvd (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (t : O) (ht : Irreducible t)
    (m : ℕ) (x : Om O (m + 1)) (hx : x ≠ 0) : ∃ z, x * z = Ideal.Quotient.mk _ (t ^ m) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hy : y ≠ 0 := by
    rintro rfl
    exact hx (map_zero _)
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy ht
  have hn : n ≤ m := by
    by_contra h
    apply hx
    rw [Ideal.Quotient.eq_zero_iff_mem, ht.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact Dvd.dvd.mul_left (pow_dvd_pow t (by omega)) _
  refine ⟨Ideal.Quotient.mk _ ((u⁻¹ : Oˣ) * t ^ (m - n)), ?_⟩
  rw [← map_mul]
  congr 1
  rw [mul_mul_mul_comm, Units.mul_inv, one_mul, ← pow_add]
  congr 1
  omega

theorem UpperTheory.V.Th.pairO :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (m : ℕ), ∃ (k : ℕ) (τ : Om O m →+ ZMod (l ^ k)), 0 < k ∧ (∀ x, (∀ z, τ (x * z) = 0) → x = 0) ∧ ∀ (a : ℤ_[l]) x, τ (algebraMap O (Om O m) (algebraMap ℤ_[l] O a) * x) = PadicInt.toZModPow k a * τ x := by
  intro l _ O _ _ _ _ _ m
  obtain ⟨hfin, -, hkill, -⟩ := (UpperTheory.V.Th.omFacts l O).2 m
  have hk : ∀ x : Om O m, l ^ (m + 1) • x = 0 := fun x => by
    rw [pow_succ, mul_smul, hkill]
  have main : ∃ τ : Om O m →+ ZMod (l ^ (m + 1)), ∀ x, (∀ z, τ (x * z) = 0) → x = 0 := by
    cases m with
    | zero =>
      refine ⟨0, fun x _ => ?_⟩
      simpa using hkill x
    | succ m =>
      obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible O
      haveI : NeZero (l ^ (m + 1 + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
      letI : Module (ZMod (l ^ (m + 1 + 1))) (Om O (m + 1)) := AddCommGroup.zmodModule hk
      have h0 : (Ideal.Quotient.mk _ (t ^ m) : Om O (m + 1)) ≠ 0 := by
        rw [Ne, Ideal.Quotient.eq_zero_iff_mem, ht.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
          pow_dvd_pow_iff ht.ne_zero ht.not_isUnit]
        omega
      have h1 := (UpperTheory.V.Th.dualZ (l ^ (m + 1 + 1)) (Om O (m + 1))).2.1 (Ideal.Quotient.mk _ (t ^ m))
      obtain ⟨f, hf⟩ := not_forall.mp (mt h1 h0)
      refine ⟨f.toAddMonoidHom, fun x hx => ?_⟩
      by_contra hx0
      obtain ⟨z, hz⟩ := pairO_dvd O t ht m x hx0
      have := hx z
      rw [hz] at this
      exact hf this
  obtain ⟨τ, hτ⟩ := main
  exact ⟨m + 1, τ, Nat.succ_pos m, hτ, fun a x =>
    pairO_lin l (Om O m) ((algebraMap O (Om O m)).comp (algebraMap ℤ_[l] O)) (m + 1) hk τ a x⟩
end
