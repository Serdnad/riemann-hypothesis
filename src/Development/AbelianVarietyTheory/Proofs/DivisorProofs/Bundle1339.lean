module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapFOneInjectiveOfSectionsSurjective
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.exists_norm_of_classOfFixedUnits_eq : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (x y : {x : B.Aˣ // B.σ (x : B.A) = x}), (Quot.mk _ x : B.Cl) = Quot.mk _ y → ∃ a : B.Aˣ, (y.1 : B.A) = x.1 * (a * B.σ a) := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.ClRel.eq_of_mk_eq | exact GlobalTheory.UnitLemma.InvAlg.ClRel.eq_of_mk_eq | (intros; apply GlobalTheory.UnitLemma.InvAlg.ClRel.eq_of_mk_eq <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_norm_of_equal_gram_traceForms : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∀ (a : ℕ) (β β' : B.Aˣ), B.σ (β : B.A) = β * (ε * B.g) → B.σ (β' : B.A) = β' * (ε * B.g) → ∀ b b' : Module.Basis (Fin a) K.E B.A, (∀ i j, B.herm β (b i) (b j) = B.herm β' (b' i) (b' j)) → ∃ t : B.Aˣ, (β' : B.A) = β * (t * B.σ t) := by
  first | exact @GlobalTheory.UnitLemma.IsometryUnit.isometry_unit | exact GlobalTheory.UnitLemma.IsometryUnit.isometry_unit | (intros; apply GlobalTheory.UnitLemma.IsometryUnit.isometry_unit <;> assumption)
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.charpoly_mulLeft_generator_eq_map_symm : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (R : Type) [Field R] (e : K.E ≃+* R) (u : B.A) (Q : R[X]), Q.Monic → Algebra.adjoin K.E {u} = ⊤ → aeval u (Q.map e.symm.toRingHom) = 0 → Module.finrank K.E B.A = Q.natDegree → (LinearMap.mulLeft K.E u).charpoly = Q.map e.symm.toRingHom := by
  first | exact @GlobalTheory.charpoly_mulLeft_eq_map_symm | exact GlobalTheory.charpoly_mulLeft_eq_map_symm | (intros; apply GlobalTheory.charpoly_mulLeft_eq_map_symm <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

theorem _root_.GlobalTheory.T.isIntegral_matrix_iff_bounded_powers : ∀ (K : UQ) {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (e : K.E ≃+* L), (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) K.E), IsIntegral K.O M ↔ ∃ m : ℤ, ∀ k : ℕ, ∀ i j, Valued.v (e ((M ^ k) i j)) ≤ WithZero.exp m := by
  first | exact @GlobalTheory.IntMatBound.isIntegral_iff_bounded | exact GlobalTheory.IntMatBound.isIntegral_iff_bounded | (intros; apply GlobalTheory.IntMatBound.isIntegral_iff_bounded <;> assumption)
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat.Lv

open IsDedekindDomain.HeightOneSpectrum

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

def col (Z : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (j : Fin m) : B.A := ∑ i, e.symm (Z i j) • b i

theorem repr_col (Z : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (j i : Fin m) :
    b.repr (col e b Z j) i = e.symm (Z i j) := by
  rw [col, Module.Basis.repr_sum_self]

theorem repr_sum_smul_col (Z : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (c : Fin m → K.E) (i : Fin m) :
    b.repr (∑ l, c l • col e b Z l) i = e.symm ((Z *ᵥ fun l => e (c l)) i) := by

  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, repr_col,
  smul_eq_mul, Matrix.mulVec, dotProduct, map_mul, RingEquiv.symm_apply_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem mul_col (a : B.A) (Z : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (j : Fin m) :
    a * col e b Z j = col e b (GlobalTheory.TwLat.mulMat e b a * Z) j := by
  apply b.repr.injective
  ext i
  rw [repr_col]
  have h2 := congrFun (LinearMap.toMatrix_mulVec_repr b b (LinearMap.mulLeft K.E a) (col e b Z j)) i
  simp only [LinearMap.mulLeft_apply] at h2
  rw [← h2]

  simp only [Matrix.mulVec, dotProduct, GlobalTheory.TwLat.mulMat, Matrix.mul_apply, Matrix.map_apply, repr_col, map_sum,
  map_mul, RingEquiv.symm_apply_apply]

theorem mulMat_one_add (t : K.E) (x : B.A) :
    GlobalTheory.TwLat.mulMat e b (1 + algebraMap K.E B.A t * x) = 1 + e t • GlobalTheory.TwLat.mulMat e b x := by
  ext i j
  simp only [GlobalTheory.TwLat.mulMat, Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply, add_mul, one_mul,
    mul_assoc, ← Algebra.smul_def, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, map_mul,
    Matrix.add_apply, Matrix.smul_apply, Module.Basis.repr_self, Matrix.one_apply, Finsupp.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem sum_smul_col_inj (g : GLw m w) (c c' : Fin m → K.E)
    (h : ∑ l, c l • col e b g.val l = ∑ l, c' l • col e b g.val l) : c = c' := by
  have h1 : g.val *ᵥ (fun l => e (c l)) = g.val *ᵥ (fun l => e (c' l)) := by
    funext i
    have := congrArg (fun x => b.repr x i) h
    simp only [repr_sum_smul_col] at this
    exact e.symm.injective this
  have h2 := congrArg (fun v => (g⁻¹).val *ᵥ v) h1
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h2
  funext l
  exact e.injective (congrFun h2 l)

theorem mul_le_self_iff (a b : WithZero (Multiplicative ℤ)) (ha : a ≠ 0) : a * b ≤ a ↔ b ≤ 1 := by
  constructor
  · intro h
    have : a⁻¹ * (a * b) ≤ a⁻¹ * a := by gcongr
    rwa [← mul_assoc, inv_mul_cancel₀ ha, one_mul] at this
  · intro h
    exact mul_le_of_le_one_right' h

end GlobalTheory.TwLat.Lv

namespace GlobalTheory.TwLat.Lv

open IsDedekindDomain.HeightOneSpectrum

theorem valued_uniformizerPower_completion_eq_exp_neg {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
    (e : K.E ≃+* w.adicCompletion E) (hval : ∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) (t : K.O) (k : ℕ)
    (ht : t ≠ 0) (hk : GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k) :
    Valued.v (e (algebraMap K.O K.E t)) = WithZero.exp (-(k : ℤ)) := by
  have hne : e (algebraMap K.O K.E t) ≠ 0 := by
    intro h
    apply ht
    have h1 : algebraMap K.O K.E t = 0 := e.injective (h.trans (map_zero e).symm)
    exact IsFractionRing.injective K.O K.E (h1.trans (map_zero _).symm)
  have hv : Valued.v (e (algebraMap K.O K.E t)) ≠ 0 := (Valuation.ne_zero_iff _).mpr hne
  rw [hval, ordL, dite_eq_right hv] at hk
  rw [← WithZero.coe_unzero hv, WithZero.exp]
  congr 1
  rw [← ofAdd_toAdd (WithZero.unzero hv)]
  congr 1
  omega

theorem level_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (t : K.O) (k : ℕ), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ g N : GLw m w, N.val = GlobalTheory.TwLat.mulMat e b (1 + algebraMap K.O B.A t * B.g) → ((g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v ((g⁻¹ * N * g).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))) ↔ ∀ y ∈ GlobalTheory.TwLat.lat e b g, B.g * y ∈ GlobalTheory.TwLat.lat e b g) := by
  intro E _ _ _ _ w _ K e he hint hval B m b t k hs hk g N hN
  have hv := valued_uniformizerPower_completion_eq_exp_neg e hval t k hs.1 hk
  obtain ⟨c, hc⟩ : ∃ c, c = e (algebraMap K.O K.E t) := ⟨_, rfl⟩
  rw [← hc] at hv
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin m) (Fin m) (w.adicCompletion E),
      Y = (g⁻¹).val * GlobalTheory.TwLat.mulMat e b B.g * g.val := ⟨_, rfl⟩
  have hA : (g⁻¹ * N * g).val = 1 + c • Y := by
    rw [Units.val_mul, Units.val_mul, hN, IsScalarTower.algebraMap_apply K.O K.E B.A, mulMat_one_add, ← hc, hY,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  have hent : ∀ i j, (g⁻¹ * N * g).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j = c * Y i j := by
    intro i j
    rw [hA]
    simp
  have hexp : WithZero.exp (-(k : ℤ)) ≠ 0 := WithZero.exp_ne_zero
  have hcoef : (∀ i j, Valued.v ((g⁻¹ * N * g).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤
      WithZero.exp (-(k : ℤ))) ↔ ∀ i j, Valued.v (Y i j) ≤ 1 := by
    simp only [hent, map_mul, hv]
    exact forall_congr' fun i => forall_congr' fun j => mul_le_self_iff _ _ hexp

  have hgY : g.val * Y = GlobalTheory.TwLat.mulMat e b B.g * g.val := by
    rw [hY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hgcol : ∀ j, B.g * col e b g.val j = ∑ l, e.symm (Y l j) • col e b g.val l := by
    intro j
    rw [mul_col, ← hgY]
    apply b.repr.injective
    ext i
    rw [repr_sum_smul_col, repr_col]
    simp only [RingEquiv.apply_symm_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have hlat : (∀ y ∈ GlobalTheory.TwLat.lat e b g, B.g * y ∈ GlobalTheory.TwLat.lat e b g) ↔ ∀ i j, Valued.v (Y i j) ≤ 1 := by
    constructor
    · intro hst i j
      have hmem : B.g * col e b g.val j ∈ GlobalTheory.TwLat.lat e b g :=
        hst _ (Submodule.subset_span ⟨j, rfl⟩)
      obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun K.O).mp hmem
      have ho' : ∑ l, algebraMap K.O K.E (o l) • col e b g.val l = ∑ l, e.symm (Y l j) • col e b g.val l := by
        rw [← hgcol j, ← ho]
        exact Finset.sum_congr rfl fun l _ => algebraMap_smul K.E (o l) _
      have := congrFun (sum_smul_col_inj e b g _ _ ho') i
      have hi := (hint (algebraMap K.O K.E (o i))).mp ⟨o i, rfl⟩
      rw [this, RingEquiv.apply_symm_apply] at hi
      exact hi
    · intro hYi y hy
      have hle : GlobalTheory.TwLat.lat e b g ≤ (GlobalTheory.TwLat.lat e b g).comap (LinearMap.mulLeft K.O B.g) := by
        rw [GlobalTheory.TwLat.lat, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        show B.g * col e b g.val j ∈ GlobalTheory.TwLat.lat e b g
        rw [hgcol j]
        refine Submodule.sum_mem _ fun l _ => ?_
        obtain ⟨o, ho⟩ := (hint (e.symm (Y l j))).mpr (by rw [RingEquiv.apply_symm_apply]; exact hYi l j)
        rw [← ho, algebraMap_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
      exact hle hy

  have hK : (∀ i j, Valued.v (Y i j) ≤ 1) → g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w (n := m) := by
    intro hYi
    haveI : IsLocalRing (Ov E w) := inferInstanceAs (IsLocalRing (w.adicCompletionIntegers E))
    have hcS : c ∈ Ov E w := by
      show c ∈ w.adicCompletionIntegers E
      rw [mem_adicCompletionIntegers, hv]
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    let c' : Ov E w := ⟨c, hcS⟩
    let Y' : Matrix (Fin m) (Fin m) (Ov E w) := fun i j =>
      ⟨Y i j, by show Y i j ∈ w.adicCompletionIntegers E; rw [mem_adicCompletionIntegers]; exact hYi i j⟩
    let A' : Matrix (Fin m) (Fin m) (Ov E w) := 1 + c' • Y'
    have hmap : A'.map (Ov E w).subtype = (g⁻¹ * N * g).val := by
      rw [hA]
      ext i j
      simp only [A', Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        map_add, map_mul]
      split_ifs <;> simp [c', Y']
    have hc'nu : ¬ IsUnit c' := by
      rintro ⟨u, hu⟩
      have h1 : c * ((u⁻¹ : (Ov E w)ˣ) : Ov E w) = 1 := by
        have := congrArg Subtype.val (Units.mul_inv u)
        rw [hu] at this
        exact this
      obtain ⟨o, ho⟩ := (hint (e.symm ((u⁻¹ : (Ov E w)ˣ) : Ov E w))).mpr (by
        rw [RingEquiv.apply_symm_apply]
        exact (mem_adicCompletionIntegers _ _ _).mp ((u⁻¹ : (Ov E w)ˣ) : Ov E w).2)
      have h2 : algebraMap K.O K.E (t * o) = 1 := by
        apply e.injective
        rw [map_mul, map_mul, ho, RingEquiv.apply_symm_apply, ← hc, h1, map_one]
      have h3 : t * o = 1 := IsFractionRing.injective K.O K.E (h2.trans (map_one _).symm)
      exact (IsLocalRing.mem_maximalIdeal t).mp hs.2.1 ⟨⟨t, o, h3, by rw [mul_comm]; exact h3⟩, rfl⟩
    have hres0 : IsLocalRing.residue (Ov E w) c' = 0 :=
      (IsLocalRing.residue_eq_zero_iff c').mpr ((IsLocalRing.mem_maximalIdeal c').mpr hc'nu)
    have hdet : IsUnit A'.det := by
      apply (isUnit_map_iff (IsLocalRing.residue (Ov E w)) _).mp
      rw [RingHom.map_det]
      have : (IsLocalRing.residue (Ov E w)).mapMatrix A' = 1 := by
        ext i j
        simp [A', hres0, Matrix.one_apply]
      rw [this, Matrix.det_one]
      exact isUnit_one
    have hU : IsUnit A' := (Matrix.isUnit_iff_isUnit_det A').mpr hdet
    refine ⟨hU.unit, ?_⟩
    apply Units.ext
    rw [← hmap]
    rfl
  constructor
  · rintro ⟨-, h⟩
    exact hlat.2 (hcoef.1 h)
  · intro h
    have h' := hlat.1 h
    exact ⟨hK h', hcoef.2 h'⟩

end GlobalTheory.TwLat.Lv
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie IsDedekindDomain
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LatticeIndex

theorem intersected_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.LevOK N M → ℓ.Prime → ∀ (A : GlobalTheory.PlaceInt.Adapt Λ N ℓ) (s : c.F), Submodule.span (𝓞 c.F) {s} * ∏ τ : E →+* ℂ, idealAt c Λ.Ln τ ^ Dw.mult τ ≤ ∏ τ : E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ → ∀ (T : CDVR) (io : c.F →+* T.Fr), ¬ IsUnit (ℓ : T.V) → ∀ e : ℕ, 0 ≤ nval T.V e (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ)) := by
  intro E _ _ _ H Dw l c n Λ N M ℓ hL hl A s hs T io hu e
  have hN : N ≠ 0 := by rintro rfl; exact absurd hL.1 (by decide)
  let w := (valV (K' := T.Fr) T.V).comap io
  have hwi : ∀ x : c.F, IsIntegral ℤ x → w x ≤ 1 := fun x hx => valV_integral T
    (by convert map_isIntegral_int io hx; exact Subsingleton.elim _ _)
  have hw : ∀ r : 𝓞 c.F, w (algebraMap (𝓞 c.F) c.F r) ≤ 1 := fun r => hwi _ r.isIntegral_coe
  have hwτ : ∀ τ, ∀ r : 𝓞 E, w.comap (embF c τ) (algebraMap (𝓞 E) E r) ≤ 1 := fun τ r =>
    hwi _ (map_isIntegral_int (embF c τ) r.isIntegral_coe)
  have hnat : ∀ τ (k : ℕ), Nat.Coprime k ℓ → w.comap (embF c τ) (k : E) = 1 := fun τ k hk => by
    simp only [w, Valuation.comap_apply, map_natCast]
    exact valV_nat T hk hu
  have hn : ∀ τ, HasMax w (idealAt c Λ.Ln τ) (w.comap (embF c τ) (algebraMap (𝓞 E) E A.g.det)) := fun τ => by
    obtain ⟨a, b⟩ := detSet_Ln A _ (hwτ τ) (hnat τ _ A.cop₁)
    refine hasMax_span hw ?_ ⟨_, ⟨_, b, rfl⟩, rfl⟩
    rintro _ ⟨y, hy, rfl⟩
    exact a y hy
  have ha : ∀ τ, HasMax w (idealAt c Λ.La τ) (w.comap (embF c τ) A.ga.det)⁻¹ := fun τ => by
    obtain ⟨-, a, y, hy, b⟩ := detSet_La A _ (hwτ τ) (hnat τ _ A.cop)
    refine hasMax_span hw ?_ ⟨_, ⟨_, hy, rfl⟩, b⟩
    rintro _ ⟨y, hy, rfl⟩
    exact a y hy
  have h0 : ∀ τ, w.comap (embF c τ) A.ga.det ≠ 0 := fun τ => (detSet_La A _ (hwτ τ) (hnat τ _ A.cop)).1
  have hp : ∀ τ, w (embK c τ A.p.det) * (w.comap (embF c τ) A.ga.det)⁻¹ =
      w.comap (embF c τ) (algebraMap (𝓞 E) E A.g.det) := fun τ => by
    have := congrArg (w.comap (embF c τ)) (det_p A hN)
    simp only [map_mul, map_pow, hnat τ _ A.cop, hnat τ _ A.cop₁, _root_.one_pow, _root_.mul_one, _root_.one_mul] at this
    rw [mul_inv_eq_iff_eq_mul₀ (h0 τ), mul_comm]
    exact this
  have hb : HasMax w (Submodule.span (𝓞 c.F) {s}) (w s) := hasMax_span hw (by simp) (by simp)
  have e1 := hb.mul (hasMax_prod hw Finset.univ _ _ fun τ => (hn τ).pow hw (Dw.mult τ))
  have e2 := hasMax_prod hw Finset.univ _ _ fun τ => (ha τ).pow hw (Dw.mult τ)
  obtain ⟨y, hy, hyv⟩ := e1.2
  have hle := e2.1 y (hs hy)
  rw [hyv] at hle
  simp only [← hp, mul_pow, Finset.prod_mul_distrib, ← _root_.mul_assoc] at hle
  have hpos : 0 < ∏ τ : E →+* ℂ, (w.comap (embF c τ) A.ga.det)⁻¹ ^ Dw.mult τ :=
    zero_lt_iff.2 (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (inv_ne_zero (h0 τ)))
  have hw1 : w (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ) ≤ 1 := by
    rw [map_mul, map_prod]
    simp only [map_pow]
    refine le_of_mul_le_mul_right ?_ hpos
    rw [_root_.one_mul]
    exact hle
  have hv : valV T.V (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ)) ≤ 1 := hw1
  by_cases hx : io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ) = 0
  · rw [hx, nval_zero]; exact le_top
  rw [nval_of_ne hx]
  have hlog : WithZero.log (valV T.V (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ))) ≤ 0 := by
    rw [← WithZero.log_one]
    exact (WithZero.log_le_log (valV_ne_zero hx) one_ne_zero).2 hv
  have h0v : (0 : ℝ) ≤ (vV T.V (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ)) : ℝ) := by
    simp only [vV]; exact_mod_cast (by omega)
  exact EReal.coe_nonneg.2 (div_nonneg h0v (Nat.cast_nonneg _))

end GlobalTheory.LatticeIndex
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open Opposite

namespace GlobalTheory.TwoOpens

theorem sections_inter_eq_sub_of_subsingleton_cohOn : ∀ (Y : Scheme.{0}) (F : Y.Modules) (W₁ W₂ : Y.Opens), Subsingleton (cohOn F (W₁ ⊔ W₂) 1) → ∀ t : sectionsOn F (W₁ ⊓ W₂), ∃ (a : sectionsOn F W₁) (b : sectionsOn F W₂), t = sectionsOn.res Γ(Y, ⊤) F inf_le_right b - sectionsOn.res Γ(Y, ⊤) F inf_le_left a := by
  intro Y F W₁ W₂ h t
  let A := (GlobalTheory.toAbSheaf Y).obj F
  let S := Flasque.injectiveShortComplex A
  have hS : S.ShortExact := Flasque.injectiveShortComplex_shortExact A
  have hfl : TopCat.Sheaf.IsFlasque S.X₂ := Flasque.isFlasque_injectiveShortComplex_X₂ A
  have hinj : ∀ W : Y.Opens, Function.Injective (S.f.hom.app (op W)) := by
    intro W x y hxy
    obtain ⟨x, rfl⟩ := (SheafLES.equivZero.{0} S.X₁ W).surjective x
    obtain ⟨y, rfl⟩ := (SheafLES.equivZero.{0} S.X₁ W).surjective y
    rw [← SheafLES.equivZero_map, ← SheafLES.equivZero_map] at hxy
    rw [SheafLES.injective_zero hS W ((SheafLES.equivZero.{0} S.X₂ W).injective hxy)]
  have hex : ∀ W : Y.Opens, Function.Exact (S.f.hom.app (op W)) (S.g.hom.app (op W)) := by
    intro W x
    obtain ⟨x, rfl⟩ := (SheafLES.equivZero.{0} S.X₂ W).surjective x
    rw [← SheafLES.equivZero_map, AddEquiv.map_eq_zero_iff, SheafLES.exact₂ hS 0 W x]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, (SheafLES.equivZero_map S.f W y).symm⟩
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := (SheafLES.equivZero.{0} S.X₁ W).surjective y
      exact ⟨y, (SheafLES.equivZero.{0} S.X₂ W).injective
        ((SheafLES.equivZero_map S.f W y).trans hy)⟩

  have natf : ∀ {U V : Y.Opens} (hUV : V ≤ U) x,
      S.f.hom.app (op V) (S.X₁.obj.map (homOfLE hUV).op x) =
        S.X₂.obj.map (homOfLE hUV).op (S.f.hom.app (op U) x) := fun hUV x =>
    NatTrans.naturality_apply S.f.hom (homOfLE hUV).op x
  have natg : ∀ {U V : Y.Opens} (hUV : V ≤ U) x,
      S.g.hom.app (op V) (S.X₂.obj.map (homOfLE hUV).op x) =
        S.X₃.obj.map (homOfLE hUV).op (S.g.hom.app (op U) x) := fun hUV x =>
    NatTrans.naturality_apply S.g.hom (homOfLE hUV).op x
  have resres : ∀ {U V V' : Y.Opens} (h₁ : V ≤ U) (h₂ : V' ≤ V) x,
      S.X₂.obj.map (homOfLE h₂).op (S.X₂.obj.map (homOfLE h₁).op x) =
        S.X₂.obj.map (homOfLE (h₂.trans h₁)).op x := fun h₁ h₂ x => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have resres3 : ∀ {U V V' : Y.Opens} (h₁ : V ≤ U) (h₂ : V' ≤ V) x,
      S.X₃.obj.map (homOfLE h₂).op (S.X₃.obj.map (homOfLE h₁).op x) =
        S.X₃.obj.map (homOfLE (h₂.trans h₁)).op x := fun h₁ h₂ x => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

  obtain ⟨b', hb'⟩ := (AddCommGrpCat.epi_iff_surjective
    (S.X₂.obj.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op)).1 (hfl.epi _)
    (S.f.hom.app (op (W₁ ⊓ W₂)) (sectionsOn.toΓ F _ t))

  let U : Bool → Y.Opens := fun b => cond b W₂ W₁
  let sf : ∀ b : Bool, ToType (S.X₃.obj.obj (op (U b))) := fun b =>
    match b with
    | true => S.g.hom.app (op W₂) b'
    | false => 0
  have h0 : S.X₃.obj.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op (S.g.hom.app (op W₂) b') = 0 := by
    rw [← natg, hb']
    exact (hex _).apply_apply_eq_zero _
  have h0' : S.X₃.obj.map (homOfLE (inf_le_left : W₂ ⊓ W₁ ≤ W₂)).op (S.g.hom.app (op W₂) b') = 0 := by
    have e := resres3 (inf_le_right : W₁ ⊓ W₂ ≤ W₂) (inf_comm W₂ W₁).le (S.g.hom.app (op W₂) b')
    rw [h0, map_zero] at e
    exact e.symm
  have hcomp : TopCat.Presheaf.IsCompatible S.X₃.obj U sf := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact (map_zero _).trans h0.symm
    · exact h0'.trans (map_zero _).symm
    · rfl
  obtain ⟨q, hq, -⟩ := TopCat.Sheaf.existsUnique_gluing' (X := Y.toPresheafedSpace.carrier) S.X₃ U (W₁ ⊔ W₂)
    (fun b => homOfLE (by cases b; exacts [le_sup_left, le_sup_right]))
    (sup_le (le_iSup U false) (le_iSup U true)) sf hcomp

  obtain ⟨i, hi⟩ := SheafLES.sections_surjective_of_subsingleton.{0} hS (W₁ ⊔ W₂) h q
  obtain ⟨bb, hbb⟩ := (hex W₂ (b' - S.X₂.obj.map (homOfLE (le_sup_right : W₂ ≤ W₁ ⊔ W₂)).op i)).1 (by
    rw [map_sub, natg, hi]
    exact sub_eq_zero.2 (hq true).symm)
  obtain ⟨aa, haa⟩ := (hex W₁ (- S.X₂.obj.map (homOfLE (le_sup_left : W₁ ≤ W₁ ⊔ W₂)).op i)).1 (by
    rw [map_neg, natg, hi]
    exact neg_eq_zero.2 (hq false))
  refine ⟨(sectionsOn.toΓ F W₁).symm aa, (sectionsOn.toΓ F W₂).symm bb, ?_⟩
  apply (sectionsOn.toΓ F _).injective
  rw [map_sub, sectionsOn.toΓ_res, sectionsOn.toΓ_res]
  simp only [AddEquiv.apply_symm_apply]
  apply hinj
  change _ = S.f.hom.app _ (S.X₁.obj.map _ bb - S.X₁.obj.map _ aa)
  erw [map_sub]
  rw [natf, natf, hbb, haa, map_sub, map_neg, resres, resres, hb']
  abel

end GlobalTheory.TwoOpens
end
