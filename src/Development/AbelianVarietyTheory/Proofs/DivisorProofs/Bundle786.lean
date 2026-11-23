module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle180
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.ReesAlgebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle748
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle237
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle751
public import ReciprocityTheory.GaloisValuations.Global
public import ReciprocityTheory.NeutralLocalFields.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle750
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHolomorphicMorseInequalityUniform
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle749
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLoc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.InertiaGood

theorem not_dvd_discr_of_inertia_fix (E N : Type) [Field E] [NumberField E] [Field N] [NumberField N]
    [Algebra E N] [IsGalois ℚ N] (q : ℕ) (hq : q.Prime)
    (h : ∀ Q : Ideal (𝓞 N), Q.IsMaximal → (q : 𝓞 N) ∈ Q → ∀ τ : N ≃ₐ[ℚ] N, (∀ x : 𝓞 N, τ • x - x ∈ Q) →
      ∀ y : E, τ (algebraMap E N y) = algebraMap E N y) : ¬ (q : ℤ) ∣ discr E := by
  have hqz : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  refine (not_dvd_discr_iff_forall_mem E (𝓞 E) hqz).2 fun P hP hqP => ?_
  have hqP' : (q : 𝓞 E) ∈ P := by simpa using hqP
  have hne : P ≠ ⊥ := fun h0 => by
    rw [h0, Ideal.mem_bot] at hqP'
    exact hq.ne_zero (Nat.cast_eq_zero.1 hqP')
  have hPm : P.IsMaximal := hP.isMaximal hne
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 N) P
  have hqQ : (q : 𝓞 N) ∈ Q := by
    have := (Ideal.mem_of_liesOver Q P _).1 hqP'
    rwa [map_natCast] at this
  have h1 := (GlobalTheory.UnramCompositum.ramificationIdx_eq_one_iff_fix ℚ E N Q).2 (h Q hQ hqQ)
  rw [← Ideal.over_def Q P] at h1
  have hu : Algebra.IsUnramifiedAt ℤ (P.under (𝓞 ℚ)) :=
    (not_dvd_discr_iff_forall_mem ℚ (𝓞 ℚ) hqz).1 (by
      rw [Rat.numberField_discr]; exact hqz.not_dvd_one) _ inferInstance (by
      rw [Ideal.under, Ideal.mem_comap, map_intCast]; exact hqP)
  have h2 : P.ramificationIdx ℤ = (P.under (𝓞 ℚ)).ramificationIdx ℤ * P.ramificationIdx (𝓞 ℚ) :=
    Ideal.ramificationIdx_tower (P.under (𝓞 ℚ)) P
  rw [h1, Ideal.ramificationIdx_eq_one (P.under (𝓞 ℚ)) ℤ, Nat.mul_one] at h2
  exact Ideal.ramificationIdx_eq_one_iff.1 h2

theorem exists_unramified_field_good : ∀ (N : IntermediateField ℚ ℂ) [NumberField N] [IsGalois ℚ N] (q : ℕ), q.Prime → ∀ Good : (ℂ ≃+* ℂ) → Prop, (∀ τ τ', Good τ → Good τ' → Good (τ.trans τ')) → (∀ (τ : ℂ ≃+* ℂ) (𝔮 : Ideal (𝓞 N)), 𝔮.IsMaximal → (q : 𝓞 N) ∈ 𝔮 → (∀ x : 𝓞 N, ∃ y : 𝓞 N, ((y : N) : ℂ) = τ ((x : N) : ℂ) ∧ y - x ∈ 𝔮) → Good τ) → ∃ (F' : IntermediateField ℚ ℂ) (_ : NumberField F'), ¬ (q : ℤ) ∣ discr F' ∧ ∀ τ : ℂ ≃+* ℂ, (∀ x ∈ F', τ x = x) → Good τ := by
  intro N _ _ q hq Good hmul hin
  have : Countable N := (Module.finBasis ℚ N).equivFun.injective.countable
  let T : Set (N ≃ₐ[ℚ] N) :=
    {σ | ∃ 𝔮 : Ideal (𝓞 N), 𝔮.IsMaximal ∧ (q : 𝓞 N) ∈ 𝔮 ∧ σ ∈ 𝔮.inertia (N ≃ₐ[ℚ] N)}
  let S : (N ≃ₐ[ℚ] N) → Prop := fun σ => ∀ τ : ℂ ≃+* ℂ, (∀ x : N, τ (x : ℂ) = (σ x : ℂ)) → Good τ
  have hT : ∀ σ ∈ T, S σ := by
    rintro σ ⟨𝔮, h1, h2, h3⟩ τ hτ
    exact hin τ 𝔮 h1 h2 fun x => ⟨σ • x, (hτ x).symm, AddSubgroup.mem_inertia.1 h3 x⟩
  have h1 : (1 : N ≃ₐ[ℚ] N) ∈ T := by
    have hp : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
    have : (Ideal.span {(q : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 N) (Ideal.span {(q : ℤ)})
    refine ⟨Q, hQ, ?_, one_mem _⟩
    have := (Ideal.mem_of_liesOver Q (Ideal.span {(q : ℤ)}) _).1 (Ideal.mem_span_singleton_self _)
    rwa [map_natCast] at this
  have hSmul : ∀ σ σ', S σ → S σ' → S (σ * σ') := by
    intro σ σ' hσ hσ' τ hτ
    obtain ⟨τ', hτ'⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq N (algebraMap N ℂ)
      ((algebraMap N ℂ).comp (σ' : N →+* N))
    have hτ'' : ∀ x : N, τ' (x : ℂ) = (σ' x : ℂ) := hτ'
    have g2 : Good (τ'.symm.trans τ) := hσ _ fun x => by
      have e : τ'.symm (x : ℂ) = (σ'.symm x : ℂ) := by
        rw [RingEquiv.symm_apply_eq, hτ'', AlgEquiv.apply_symm_apply]
      rw [RingEquiv.trans_apply, e, hτ, AlgEquiv.mul_apply, AlgEquiv.apply_symm_apply]
    have e : τ'.trans (τ'.symm.trans τ) = τ := RingEquiv.ext fun z => by simp
    exact e ▸ hmul _ _ (hσ' τ' hτ'') g2
  have hIS : ∀ σ ∈ Subgroup.closure T, S σ := fun σ hσ =>
    Subgroup.closure_induction'' (p := fun σ _ => S σ) hT
      (fun x ⟨𝔮, a, b, c⟩ => hT _ ⟨𝔮, a, b, inv_mem c⟩) (hT _ h1) (fun x y _ _ => hSmul x y) hσ
  let F₀ := IntermediateField.fixedField (Subgroup.closure T)
  have : NumberField (IntermediateField.lift F₀) :=
    have : FiniteDimensional ℚ (IntermediateField.lift F₀) :=
      (IntermediateField.liftAlgEquiv F₀).toLinearEquiv.finiteDimensional
    ⟨⟩
  refine ⟨IntermediateField.lift F₀, this, ?_, fun τ hτ => ?_⟩
  · rw [← discr_eq_discr_of_algEquiv F₀ (IntermediateField.liftAlgEquiv F₀)]
    exact not_dvd_discr_of_inertia_fix F₀ N q hq fun Q a b σ c y =>
      (IntermediateField.mem_fixedField_iff _ _).1 y.2 σ
        (Subgroup.subset_closure ⟨Q, a, b, AddSubgroup.mem_inertia.2 c⟩)
  · let τa : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := τ) fun x => by simp
    have hr : ∀ x : N, τ (x : ℂ) = (τa.restrictNormal N x : ℂ) := fun x =>
      (AlgEquiv.restrictNormal_commutes τa N x).symm
    refine hIS (τa.restrictNormal N) ?_ τ hr
    rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.closure T),
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact Subtype.ext ((hr x).symm.trans (hτ _ ((IntermediateField.mem_lift x).2 hx)))

end GlobalTheory.InertiaGood
end

section

open MvPolynomial

namespace GlobalTheory.UniformCocycle

variable {R : Type} [CommRing R] {σ : Type}

noncomputable def proj (I : Ideal R) (e : ℕ) (P : MvPolynomial σ (reesAlgebra I)) :
    MvPolynomial σ R :=
  ∑ m ∈ P.support, monomial m (((AddMonoidAlgebra.coeff P m : reesAlgebra I) : Polynomial R).coeff e)

theorem coeff_proj (I : Ideal R) (e : ℕ) (P : MvPolynomial σ (reesAlgebra I)) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (proj I e P) m = ((AddMonoidAlgebra.coeff P m : reesAlgebra I) : Polynomial R).coeff e := by
  classical
  simp only [proj, coeff_sum, coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not] at h
    simp [h]

theorem proj_add (I : Ideal R) (e : ℕ) (P Q : MvPolynomial σ (reesAlgebra I)) :
    proj I e (P + Q) = proj I e P + proj I e Q := by
  ext m; simp [coeff_proj]

theorem proj_sub (I : Ideal R) (e : ℕ) (P Q : MvPolynomial σ (reesAlgebra I)) :
    proj I e (P - Q) = proj I e P - proj I e Q := by
  ext m; simp [coeff_proj]

theorem proj_X_mul (I : Ideal R) (e : ℕ) (i : σ) (P : MvPolynomial σ (reesAlgebra I)) :
    proj I e (X i * P) = X i * proj I e P := by
  classical
  ext m
  rw [coeff_proj, coeff_X_mul', coeff_X_mul']
  split_ifs <;> simp [coeff_proj]

theorem proj_Xpow_mul (I : Ideal R) (e : ℕ) (i : σ) (k : ℕ) (P : MvPolynomial σ (reesAlgebra I)) :
    proj I e (X i ^ k * P) = X i ^ k * proj I e P := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, proj_X_mul, ih, ← mul_assoc, ← pow_succ']


open Classical in
noncomputable def liftCoeff (I : Ideal R) (e : ℕ) (r : R) : reesAlgebra I :=
  if h : r ∈ I ^ e then ⟨Polynomial.monomial e r, reesAlgebra.monomial_mem.mpr h⟩ else 0

theorem liftCoeff_zero (I : Ideal R) (e : ℕ) : liftCoeff I e 0 = 0 := by
  unfold liftCoeff
  rw [dite_eq_left (zero_mem _)]
  apply Subtype.ext; simp

noncomputable def liftE (I : Ideal R) (e : ℕ) (F : MvPolynomial σ R) :
    MvPolynomial σ (reesAlgebra I) :=
  ∑ m ∈ F.support, monomial m (liftCoeff I e (AddMonoidAlgebra.coeff F m))

theorem coeff_liftE (I : Ideal R) (e : ℕ) (F : MvPolynomial σ R) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (liftE I e F) m = liftCoeff I e (AddMonoidAlgebra.coeff F m) := by
  classical
  simp only [liftE, coeff_sum, coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not] at h
    rw [h, liftCoeff_zero]

theorem proj_liftE {I : Ideal R} {e : ℕ} {F : MvPolynomial σ R} (h : ∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e)
    (e' : ℕ) : proj I e' (liftE I e F) = if e' = e then F else 0 := by
  ext m
  rw [coeff_proj, coeff_liftE, liftCoeff, dite_eq_left (h m)]
  simp only [Polynomial.coeff_monomial]
  by_cases h1 : e' = e
  · subst h1; simp
  · rw [Finsupp.single_eq_of_ne h1, ite_eq_right h1]
    simp

theorem isHomogeneous_liftE {I : Ideal R} {e t : ℕ} {F : MvPolynomial σ R}
    (hF : F.IsHomogeneous t) : (liftE I e F).IsHomogeneous t := by
  intro m hm
  apply hF
  intro h0
  apply hm
  rw [coeff_liftE, h0, liftCoeff_zero]

theorem isHomogeneous_proj {I : Ideal R} {e t : ℕ} {P : MvPolynomial σ (reesAlgebra I)}
    (hP : P.IsHomogeneous t) : (proj I e P).IsHomogeneous t := by
  intro m hm
  apply hP
  intro h0
  apply hm
  rw [coeff_proj, h0]
  simp

end GlobalTheory.UniformCocycle

namespace GlobalTheory


open UniformCocycle in
theorem uniformSerre_cocycle : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (n : ℕ) (J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t → (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ e : ℕ, ∀ (N : ℕ) (F : Fin (n + 1) → Fin (n + 1) → MvPolynomial (Fin (n + 1)) R), (∀ i j, (F i j).IsHomogeneous (d + 2 * N)) → (∀ i j m, AddMonoidAlgebra.coeff (F i j) m ∈ I ^ e) → (∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) R) * X j * X l) ^ L * (X l ^ N * F i j + X i ^ N * F j l - X j ^ N * F i l) ∈ J e) → ∃ (N' : ℕ) (G : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R), (∀ i, (G i).IsHomogeneous (d + N')) ∧ (∀ i m, AddMonoidAlgebra.coeff (G i) m ∈ I ^ e) ∧ ∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) R) * X j) ^ L * ((X i * X j) ^ N' * F i j - (X i * X j) ^ N * (X j ^ N' * G i - X i ^ N' * G j)) ∈ J e := by
  open UniformCocycle in
  intro R _ _ I n J hJ
  obtain ⟨𝔞, h𝔞h, h𝔞⟩ := GlobalTheory.T.exists_homogeneous_ideal_over_reesAlgebra R I n J hJ
  obtain ⟨d₀, hd₀⟩ := GlobalTheory.T.exists_coboundary_of_fraction_cocycle_homogeneous_ideal (reesAlgebra I) n 𝔞 h𝔞h
  refine ⟨d₀, fun d hd e N F hFh hFc hcoc => ?_⟩
  have hF'h : ∀ i j, (liftE I e (F i j)).IsHomogeneous (d + 2 * N) :=
    fun i j => isHomogeneous_liftE (hFh i j)
  have hF'p : ∀ e' i j, proj I e' (liftE I e (F i j)) = if e' = e then F i j else 0 :=
    fun e' i j => proj_liftE (hFc i j) e'
  have hcoc' : ∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) (reesAlgebra I)) * X j * X l) ^ L *
      (X l ^ N * liftE I e (F i j) + X i ^ N * liftE I e (F j l) - X j ^ N * liftE I e (F i l)) ∈ 𝔞 := by
    intro i j l
    obtain ⟨L, hL⟩ := hcoc i j l
    refine ⟨L, ?_⟩
    have hh := ((((isHomogeneous_X _ i).mul (isHomogeneous_X _ j)).mul (isHomogeneous_X _ l)).pow L).mul
      ((((isHomogeneous_X_pow l N).mul (hF'h i j)).add ((isHomogeneous_X_pow i N).mul (hF'h j l))).sub
        ((isHomogeneous_X_pow j N).mul (hF'h i l)))
    rw [h𝔞 _ _ hh]
    intro e' G hG
    have hGe : G = proj I e' (((X i : MvPolynomial (Fin (n + 1)) (reesAlgebra I)) * X j * X l) ^ L *
      (X l ^ N * liftE I e (F i j) + X i ^ N * liftE I e (F j l) - X j ^ N * liftE I e (F i l))) := by
      ext m; rw [hG, coeff_proj]
    rw [hGe]
    simp only [mul_pow, mul_assoc, proj_add, proj_sub, proj_Xpow_mul, hF'p]
    by_cases he : e' = e
    · subst he
      simp only [↓reduceIte]
      simpa only [mul_pow, mul_assoc] using hL
    · simp [he]
  obtain ⟨N', G', hG'h, hG'⟩ := hd₀ d hd N (fun i j => liftE I e (F i j)) hF'h hcoc'
  refine ⟨N', fun i => proj I e (G' i), fun i => isHomogeneous_proj (hG'h i), fun i m => ?_, fun i j => ?_⟩
  · rw [coeff_proj]
    exact (mem_reesAlgebra_iff I _).mp (AddMonoidAlgebra.coeff (G' i) m).2 e
  · obtain ⟨L, hL⟩ := hG' i j
    refine ⟨L, ?_⟩
    have h2 : (1 + 1) * N + (N' + (d + N')) = (1 + 1) * N' + (d + 2 * N) := by ring
    have hh := (((isHomogeneous_X _ i).mul (isHomogeneous_X _ j)).pow L).mul
      ((((isHomogeneous_X _ i).mul (isHomogeneous_X _ j)).pow N').mul (hF'h i j) |>.sub
        (h2 ▸ (((isHomogeneous_X _ i).mul (isHomogeneous_X _ j)).pow N).mul
          (((isHomogeneous_X_pow j N').mul (hG'h i)).sub ((isHomogeneous_X_pow i N').mul (hG'h j)))))
    rw [h𝔞 _ _ hh] at hL
    have := hL e (proj I e _) (fun m => coeff_proj I e _ m)
    simp only [mul_pow, mul_assoc, proj_add, proj_sub, proj_Xpow_mul, hF'p, ↓reduceIte] at this
    simpa only [mul_pow, mul_assoc] using this

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.weaklyRegular_relations_eq_koszulRelations : ∀ (O : Type) [CommRing O] (g : ℕ) (f : Fin g → O), RingTheory.Sequence.IsWeaklyRegular O (List.ofFn f) → ∀ a : Fin g → O, ∑ i, a i * f i = 0 → ∃ c : Matrix (Fin g) (Fin g) O, (∀ i, c i i = 0) ∧ (∀ i j, c i j = - c j i) ∧ a = c.mulVec f := by
  first | exact @GlobalTheory.weaklyRegular_relations_koszul | exact GlobalTheory.weaklyRegular_relations_koszul | (intros; apply GlobalTheory.weaklyRegular_relations_koszul <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_span_maximalIdeal_map_of_flat_regular : ∀ (O' O : Type) [CommRing O'] [IsRegularLocalRing O'] [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (σ : O' →+* O), IsLocalHom σ → σ.Flat → IsArtinianRing (O ⧸ (IsLocalRing.maximalIdeal O').map σ) → ∀ g : ℕ, ringKrullDim O = g → ∃ f : Fin g → O, Ideal.span (Set.range f) = (IsLocalRing.maximalIdeal O').map σ := by
  first | exact @GlobalTheory.maximalIdeal_map_span_of_flat_of_isArtinianRing_fibre | exact GlobalTheory.maximalIdeal_map_span_of_flat_of_isArtinianRing_fibre | (intros; apply GlobalTheory.maximalIdeal_map_span_of_flat_of_isArtinianRing_fibre <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.inertia_restrict_finiteAbelian_unramified_eq_one : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L) (v : HeightOneSpectrum (𝓞 K)), IsUnramifiedIn K v L → ∀ (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G K Ω, σ ∈ ReciprocityTheory.Gal.Ine (F := K) A → haveI := h.isGalois; AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) = 1 := by
  first | exact @GlobalTheory.InertiaRestrict.restrict_eq_one | exact GlobalTheory.InertiaRestrict.restrict_eq_one | (intros; apply GlobalTheory.InertiaRestrict.restrict_eq_one <;> assumption)
end

section

open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.local_holomorphic_morse_inequality_uniform : ∀ (n : ℕ) (U K : Set (V n)) (φ g : V n → ℝ) (ε : ℝ), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 2 φ U → (∀ z ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => (φ v : ℂ)) z ξ).re) → ContinuousOn g U → (∀ z ∈ U, 0 < g z) → 0 < ε → ∃ δ : ℝ, 0 < δ ∧ (∀ z ∈ K, closedBall z δ ⊆ U) ∧ ∀ᶠ m : ℕ in atTop, ∀ z ∈ K, ∀ f : V n → ℂ, DifferentiableOn ℂ f U → ‖f z‖ ^ 2 * Real.exp (-(m * φ z)) * g z ≤ ((cHess n (fun v => (φ v : ℂ)) z).det.re / Real.pi ^ n + ε) * (m : ℝ) ^ n * ∫ w in ball z δ, ‖f w‖ ^ 2 * Real.exp (-(m * φ w)) * g w := by
  first | exact @GlobalTheory.morse_local | exact GlobalTheory.morse_local | (intros; apply GlobalTheory.morse_local <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY.LeviLarge

theorem contDiffAt_ph {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (la : La) (i : ι) {y : Y} (hy : y ∈ (A.chart i).source) :
    ContDiffAt ℝ 2 (A.ph la i ∘ (A.chart i).symm) (A.chart i y) :=
  ((A.smooth_ph la i).contDiffAt
    ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hy))).of_le (WithTop.coe_le_coe.2 le_top)

theorem leviAt_ph_nsmul {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (G H : La) (i : ι) {y : Y} (hy : y ∈ (A.chart i).source)
    (ξ : Fin n → ℂ) : ∀ k : ℕ,
    A.leviAt i (A.ph (G + k • H) i) y ξ = A.leviAt i (A.ph G i) y ξ + k * A.leviAt i (A.ph H i) y ξ
  | 0 => by simp
  | k + 1 => by
    have e : A.ph (G + (k + 1) • H) i =ᶠ[𝓝 y] fun x => A.ph (G + k • H) i x + A.ph H i x := by
      filter_upwards [(A.chart i).open_source.mem_nhds hy] with x hx
      rw [succ_nsmul, ← add_assoc, A.ph_add _ _ i x hx]
    rw [leviAt_congr A i _ _ y hy e ξ,
      leviAt_add A i _ _ y (contDiffAt_ph A _ i hy) (contDiffAt_ph A _ i hy) ξ,
      leviAt_ph_nsmul A G H i hy ξ k]
    push_cast; ring

theorem re_leviV_lower {n : ℕ} (g : V n → ℂ) (u : V n) (B : ℝ)
    (hFu : ∑ j, ∑ k, ‖wd n j (wdb n k g) u‖ ≤ B) (ξ : Fin n → ℂ) :
    -(2 * B) * ∑ j, ‖ξ j‖ ^ 2 ≤ (leviV n g u ξ).re := by
  have hS0 : 0 ≤ ∑ j, ‖ξ j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS : ∀ j k, ‖ξ j‖ * ‖ξ k‖ ≤ 2 * ∑ j, ‖ξ j‖ ^ 2 := by
    intro j k
    have h1 : ‖ξ j‖ ^ 2 ≤ ∑ j, ‖ξ j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖ξ j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    have h2 : ‖ξ k‖ ^ 2 ≤ ∑ j, ‖ξ j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖ξ j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
    nlinarith [sq_nonneg (‖ξ j‖ - ‖ξ k‖), norm_nonneg (ξ j), norm_nonneg (ξ k)]
  have hnorm : ‖leviV n g u ξ‖ ≤ ∑ j, ∑ k, ‖wd n j (wdb n k g) u‖ * (2 * ∑ j, ‖ξ j‖ ^ 2) := by
    unfold leviV
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_))
    rw [norm_mul, norm_mul, RCLike.norm_conj, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hS j k) (norm_nonneg _)
  have h3 : ∑ j, ∑ k, ‖wd n j (wdb n k g) u‖ * (2 * ∑ j, ‖ξ j‖ ^ 2) =
      (∑ j, ∑ k, ‖wd n j (wdb n k g) u‖) * (2 * ∑ j, ‖ξ j‖ ^ 2) := by
    rw [Finset.sum_mul]; simp_rw [Finset.sum_mul]
  have h4 := Complex.abs_re_le_norm (leviV n g u ξ)
  have h5 := neg_abs_le (leviV n g u ξ).re
  have h6 := mul_le_mul_of_nonneg_right hFu (by positivity : (0:ℝ) ≤ 2 * ∑ j, ‖ξ j‖ ^ 2)
  linarith

theorem curv_large : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ H G : La, (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ (i : ι) (K : Set (V n)) (t : ℝ), IsCompact K → K ⊆ (A.chart i).target → ∃ k0 : ℕ, ∀ k ≥ k0, ∀ v ∈ K, ∀ ξ : Fin n → ℂ, t * ∑ j, ‖ξ j‖ ^ 2 ≤ A.leviAt i (A.ph (G + k • H) i) ((A.chart i).symm v) ξ := by
  intro n Y _ _ _ _ _ ι La _ A H G hH i K t hK hKU
  have hU : IsOpen (A.chart i).target := (A.chart i).open_target
  have hsm : ∀ la : La, ContDiffOn ℝ ∞ (fun v => ((A.ph la i ((A.chart i).symm v) : ℝ) : ℂ))
      (A.chart i).target :=
    fun la => Complex.ofRealCLM.contDiff.comp_contDiffOn (A.smooth_ph la i)
  obtain ⟨c, hc, hcK⟩ := levi_pos_compact hU (hsm H) hK hKU (fun u hu ζ hζ => by
    have hyu := (A.chart i).map_target (hKU hu)
    have hne : ζ.ofLp ≠ 0 := by simpa using hζ
    have := hH i _ hyu ζ.ofLp hne
    simpa [WeightedAtlas.leviAt, (A.chart i).right_inv (hKU hu)] using this)
  have hF : ContinuousOn (fun u => ∑ j, ∑ k,
      ‖wd n j (wdb n k (fun v => ((A.ph G i ((A.chart i).symm v) : ℝ) : ℂ))) u‖) K :=
    continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ =>
      ((continuousOn_wd_wdb hU (hsm G) j k).mono hKU).norm
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hF
  refine ⟨⌈(t + 2 * B) / c⌉₊, fun k hk v hv ξ => ?_⟩
  have hy := (A.chart i).map_target (hKU hv)
  rw [leviAt_ph_nsmul A G H i hy ξ k]
  simp only [WeightedAtlas.leviAt, (A.chart i).right_inv (hKU hv)]
  have hFu := (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hB v hv)
  have hG := re_leviV_lower _ v B hFu ξ
  have hc' := hcK v hv (WithLp.toLp 2 ξ)
  rw [EuclideanSpace.norm_sq_eq] at hc'
  simp only [PiLp.toLp_apply, WithLp.ofLp_toLp] at hc'
  have hk' : (t + 2 * B) / c ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hkc : t + 2 * B ≤ k * c := by rwa [div_le_iff₀ hc] at hk'
  have hS0 : 0 ≤ ∑ j, ‖ξ j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hc' (Nat.cast_nonneg (α := ℝ) k)
  have h2 := mul_le_mul_of_nonneg_right hkc hS0
  nlinarith

end GlobalTheory.OTY.LeviLarge
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.supportedIdele_eq_localIdele : ∀ {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)} {a : Ideles K}, IsSupportedAt K a v → ∃ x : (v.adicCompletion K)ˣ, (x : v.adicCompletion K) = (a : AdeleRing (𝓞 K) K).2 v ∧ localIdele K v x = a := by
  first | exact @GlobalTheory.Div.SuppIdele.supported_eq_localIdele | exact GlobalTheory.Div.SuppIdele.supported_eq_localIdele | (intros; apply GlobalTheory.Div.SuppIdele.supported_eq_localIdele <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG

noncomputable section
namespace GlobalTheory.ClassCover

variable {L : Type} [Field L] [NumberField L]

def toIdeles : (FiniteAdeleRing (𝓞 L) L)ˣ →* Neutral.B1.Ideles L :=
  Units.map (MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

theorem eq_diag_mul_of_classOf (y : (FiniteAdeleRing (𝓞 L) L)ˣ)
    (hc : ReciprocityTheory.Neutral.Bridge.HCFR.classOf L (toIdeles y) = 1) :
    ∃ (k : Lˣ) (u : (FiniteAdeleRing (𝓞 L) L)ˣ),
      (∀ P : HeightOneSpectrum (𝓞 L), Valued.v ((u : FiniteAdeleRing (𝓞 L) L) P) = 1) ∧
      y = Units.map (algebraMap L (FiniteAdeleRing (𝓞 L) L)).toMonoidHom k * u := by
  obtain ⟨k, u, hu, he⟩ := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff L _).1 hc
  refine ⟨k, ⟨(u : AdeleRing (𝓞 L) L).2, ((u⁻¹ : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2, ?_, ?_⟩,
    fun P => (hu.2 P).1, ?_⟩
  · exact congrArg Prod.snd u.mul_inv
  · exact congrArg Prod.snd u.inv_mul
  · apply Units.ext
    have h2 : ((toIdeles y : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2 =
        ((Neutral.B1.diagUnits L k * u : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2 := by rw [he]
    exact h2

end GlobalTheory.ClassCover
end
end
