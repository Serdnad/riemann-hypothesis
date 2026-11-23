module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle851
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle850
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle637
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIntegralityRamifiedOfExpansion
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD cWt risingFactor DerivFormula)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt upIdele IsLatOf)
open GlobalTheory.ToricTransport (coordIn)
open scoped Classical

namespace GlobalTheory.LatConjOne

theorem exists_list_count {I : Type} [Fintype I] [DecidableEq I] (κ : I → ℕ) : ∃ u : List I, ∀ i, u.count i = κ i := by
  refine ⟨(∑ j, κ j • ({j} : Multiset I)).toList, fun i => ?_⟩
  rw [← Multiset.coe_count, Multiset.coe_toList, Multiset.count_sum']
  simp [Multiset.count_singleton]

theorem exists_perm {K E : Type} [Field K] [Field E] [NumberField E] [Algebra K E] {I : Type} [Fintype I]
    (ι : K →+* ℂ) (φ : I → E →+* ℂ) (g : ℂ ≃+* ℂ) (hφ : IsCMType φ) (hK : ∀ i, (φ i).comp (algebraMap K E) = ι)
    (hg : ∀ x, g (ι x) = ι x) (hr : ∃ x, starRingEnd ℂ (ι x) ≠ ι x) :
    ∃ π : I ≃ I, ∀ i, (g : ℂ →+* ℂ).comp (φ i) = φ (π i) := by
  have e : ∀ i x, φ i (algebraMap K E x) = ι x := fun i x => by rw [← RingHom.comp_apply, hK]
  have h1 : ∀ i, ∃ j, (g : ℂ →+* ℂ).comp (φ i) = φ j := by
    intro i
    obtain ⟨j, hj, -⟩ := hφ ((g : ℂ →+* ℂ).comp (φ i))
    rcases hj with hj | hj
    · exact ⟨j, hj⟩
    · exfalso
      obtain ⟨x, hx⟩ := hr
      have := congrArg (fun f : E →+* ℂ => f (algebraMap K E x)) hj
      simp only [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq, Function.comp_apply, e] at this
      rw [RingEquiv.coe_toRingHom, hg] at this
      exact hx this.symm
  choose π hπ using h1
  have hinj : Function.Injective π := by
    intro i i' h
    have h2 : φ i = φ i' := by
      have h3 := (hπ i).trans ((congrArg φ h).trans (hπ i').symm)
      ext x
      have := congrArg (fun f : E →+* ℂ => f x) h3
      simpa using g.injective this
    obtain ⟨j, -, hj⟩ := hφ (φ i)
    rw [hj i (Or.inl rfl), hj i' (Or.inl h2)]
  exact ⟨Equiv.ofBijective π (Finite.injective_iff_bijective.mp hinj), hπ⟩

end GlobalTheory.LatConjOne

namespace GlobalTheory.LatConjOne

theorem two_le_finrank_of_unramFin (E : Type) [Field E] [NumberField E] [IsCMField E] (h : UnramFin E) :
    2 ≤ Module.finrank ℚ (maximalRealSubfield E) := by
  by_contra hlt
  have hpos : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
  have h1 : Module.finrank ℚ (maximalRealSubfield E) = 1 := by omega
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hE : Module.finrank ℚ E = 2 := by
    rw [← (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E), h1, h2]
  have hgt := NumberField.abs_discr_gt_two (K := E) (by omega)
  have hbt : (⊥ : Subalgebra ℚ (maximalRealSubfield E)) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h1
  let f : (maximalRealSubfield E) ≃ₐ[ℚ] ℚ :=
    AlgEquiv.trans (Subalgebra.topEquiv (R := ℚ) (A := maximalRealSubfield E)).symm
      ((Subalgebra.equivOfEq _ _ hbt.symm).trans (Algebra.botEquiv ℚ (maximalRealSubfield E)))
  have hF : NumberField.discr (maximalRealSubfield E) = 1 := by
    rw [NumberField.discr_eq_discr_of_algEquiv _ f, Rat.numberField_discr]
  have key := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (K := maximalRealSubfield E) (𝒪 := 𝓞 (maximalRealSubfield E)) E (𝓞 E)
  have hU : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := h
  rw [hU, Ideal.absNorm_top, hF] at key
  simp at key
  rw [Int.abs_eq_natAbs, key] at hgt
  norm_num at hgt

end GlobalTheory.LatConjOne

namespace GlobalTheory.LatConjOne

theorem gamma_nat_add (k m : ℕ) (hk : 1 ≤ k) :
    Real.Gamma ((k : ℝ) + m) = ((k - 1).factorial : ℝ) * ∏ j ∈ Finset.range m, ((k : ℝ) + j) := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, add_zero, Finset.range_zero, Finset.prod_empty, mul_one]
    have := Real.Gamma_nat_eq_factorial (k - 1)
    rwa [Nat.cast_sub hk, Nat.cast_one, sub_add_cancel] at this
  | succ m ih =>
    have h0 : (k : ℝ) + m ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have : (0 : ℝ) ≤ m := m.cast_nonneg
      exact ne_of_gt (by linarith)
    rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc, Real.Gamma_add_one h0, ih]; ring

theorem cmPeriodConstant_eq_of_card_cmType (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] (d : ℕ) {k : ℕ} (hk : 1 ≤ k)
    (hcard : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E)) (κ : I → ℕ) :
    (C0 E d k κ : ℂ) = (cWt E k : ℂ) * risingFactor k κ * (-1) ^ (∑ i, κ i) *
      ((2 * Real.pi / Real.sqrt d : ℝ) : ℂ) ^ (∑ i, κ i) := by
  rw [cmValueConst_eq]
  simp only [cWt, risingFactor, gamma_nat_add _ _ hk, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard,
    Finset.prod_pow_eq_pow_sum]
  have h1 : ((-1 : ℂ)) ^ (∑ i, κ i) * (-1) ^ (∑ i, κ i) = 1 := by rw [← mul_pow]; norm_num
  push_cast
  linear_combination (-(((|(discr (maximalRealSubfield E) : ℝ)| ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) *
    ((k - 1).factorial : ℂ) ^ Module.finrank ℚ (maximalRealSubfield E) * (∏ x, ∏ j ∈ Finset.range (κ x), ((k : ℂ) + j)) *
    (Real.pi : ℂ) ^ (∑ i, κ i) * ((Real.sqrt d : ℝ) : ℂ)⁻¹ ^ (∑ i, κ i) * 2 ^ (∑ i, κ i))) * h1

end GlobalTheory.LatConjOne

namespace GlobalTheory.LatConjOne

end GlobalTheory.LatConjOne
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet

namespace GlobalTheory.LatAlgebraic

theorem natAbs_discr_of_finrank_one (F : Type) [Field F] [NumberField F] (h : Module.finrank ℚ F = 1) :
    (discr F).natAbs = 1 := by
  have hb : (⊥ : Subalgebra ℚ F) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h
  let e : ℚ ≃ₐ[ℚ] F := (Algebra.botEquiv ℚ F).symm.trans ((Subalgebra.equivOfEq _ _ hb).trans Subalgebra.topEquiv)
  rw [← NumberField.discr_eq_discr_of_algEquiv (f := e), NumberField.discr_rat]
  rfl

theorem two_le_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] (h : UnramFin E) :
    2 ≤ Module.finrank ℚ (maximalRealSubfield E) := by
  by_contra hlt
  have h1 : Module.finrank ℚ (maximalRealSubfield E) = 1 := by
    have := Module.finrank_pos (R := ℚ) (M := maximalRealSubfield E)
    omega
  have hE := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (maximalRealSubfield E)
    (𝓞 (maximalRealSubfield E)) E (𝓞 E)
  have hU : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := h
  rw [hU, Ideal.absNorm_top, one_mul, natAbs_discr_of_finrank_one _ h1, one_pow] at hE
  have h2 : Module.finrank ℚ E = 2 := by
    rw [← (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E),
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, h1]
  have h3 := NumberField.abs_discr_gt_two (K := E) (by omega)
  have h4 : |(discr E : ℤ)| = 1 := by rw [Int.abs_eq_natAbs, hE]; rfl
  omega

theorem card_eq_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    {φ : I → E →+* ℂ} (h : IsCMType φ) : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E) := by
  apply _root_.GlobalTheory.LatValRam.card_eq_finrank <;> assumption

theorem gamma_nat_add (k n : ℕ) (hk : 1 ≤ k) :
    Real.Gamma ((k : ℝ) + n) = ((k - 1).factorial : ℝ) * ∏ j ∈ Finset.range n, ((k : ℝ) + j) := by
  apply _root_.GlobalTheory.LatValRam.gamma_nat_add <;> assumption

theorem exists_list_count {I : Type} [Fintype I] [DecidableEq I] (κ : I → ℕ) :
    ∃ u : List I, ∀ i, u.count i = κ i := by
  refine ⟨(∑ i, Multiset.replicate (κ i) i).toList, fun i => ?_⟩
  rw [← Multiset.coe_count, Multiset.coe_toList, Multiset.count_sum', Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Multiset.count_replicate]
    simp [hj]
  · simp

theorem cmPeriodConstant_eq_of_card_cmType {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
    (hcard : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E)) (d s : ℕ) (hs : 1 ≤ s) (κ : I → ℕ) :
    C0 E d (2 * s) κ = GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) *
      (∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) * (2 * Real.pi / Real.sqrt d) ^ (∑ i, κ i) := by
  have hk : 1 ≤ 2 * s := by omega
  rw [cmValueConst_eq, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt, Finset.prod_congr rfl (fun i _ => gamma_nat_add (2 * s) (κ i) hk),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]
  ring

theorem risingFactor_eq {I : Type} [Fintype I] (k : ℕ) (κ : I → ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor k κ =
      (-1) ^ (∑ i, κ i) * (((∏ i, ∏ j ∈ Finset.range (κ i), ((k : ℝ) + j)) : ℝ) : ℂ) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  push_cast
  rfl

end GlobalTheory.LatAlgebraic
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.form_on_tangent_eq_derivative_bounding_function : ∀ {A : Over (Sp ℂ)} {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (r : Real K (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol F.V))) (k : K.K) (p : Tot I g), p ∈ K.W k → ∀ (w : Fin g → ℂ) (ρ : Hol (K.W k) →ₐ[ℂ] DualNumber ℂ), (∀ h, (ρ h).fst = h.fn p ∧ (ρ h).snd = fderiv ℂ h.fn p (0, w)) → ∀ (v : epsR ℂ ⟶ A), v.left = spMap ρ.toRingHom ≫ r.x k → ∀ (f : Form (A.hom ≫ 𝟙 _)) (per : Λ →+ Hol F.V) (q : GlobalTheory.CatCoh.C0 K.Oc), GlobalTheory.CatCoh.d0 K.Oc q = (r.coef.pullbackOneCocycle f.1).1 - (K.perZ per).1 → tanVal v f = fderiv ℂ (Hol.fn (W := K.W k) (q (K.triv k))) p (0, w) := by
  first | exact @GlobalTheory.AnPer.LieVal.main | exact GlobalTheory.AnPer.LieVal.main | (intros; apply GlobalTheory.AnPer.LieVal.main <;> assumption)
end

section

noncomputable section

open MeasureTheory MvPolynomial
open Formalism.REAL (KG toMK muK)
open GlobalTheory.PsCo.Pc1
open ReciprocityTheory.ChartRestriction.DS (IsURepOn UJset)

namespace GlobalTheory.PsCo.PolyAvg

variable {n : ℕ}

theorem totalDegree_bind_le {α β : Type} (g : α → MvPolynomial β ℂ) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (Q : MvPolynomial α ℂ) : (bind₁ g Q).totalDegree ≤ Q.totalDegree := by
  classical

  conv_lhs => rw [Q.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hs)
  refine (Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left _ (hg i))).trans ?_
  simp [Finsupp.sum]

theorem exists_translate (a : Mat n) (P : Poly n) :
    ∃ Q : Poly n, Q.totalDegree ≤ P.totalDegree ∧ ∀ g, ev (a * g) P = ev g Q := by
  let f : (Fin n × Fin n) ⊕ (Fin n × Fin n) → Poly n := Sum.elim
    (fun x => ∑ c, C (a x.1 c) * X (Sum.inl (c, x.2))) (fun x => ∑ c, C (star (a x.1 c)) * X (Sum.inr (c, x.2)))
  refine ⟨bind₁ f P, totalDegree_bind_le f ?_ P, fun g => ?_⟩
  · rintro (x | x) <;>
    · refine totalDegree_finsetSum_le fun l _ => (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X, totalDegree_C]
  · have h : ev (a * g) = (ev g).comp (bind₁ f : Poly n →ₐ[ℂ] Poly n).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) ?_
      · simp [ev]
      · rintro (x | x) <;> simp [ev, f, Matrix.mul_apply, bind₁_X_right]
    rw [h]; rfl

def varWt : (Fin n × Fin n) ⊕ (Fin n × Fin n) → Fin n → ℝ :=
  Sum.elim (fun x => -Pi.single x.1 1) (fun x => Pi.single x.1 1)

def monWt (s : (Fin n × Fin n) ⊕ (Fin n × Fin n) →₀ ℕ) : Fin n → ℝ := fun a => ∑ i, (s i : ℝ) * varWt i a

theorem ev_diag_monomial (θ : Fin n → ℝ) (g : Mat n) (s : (Fin n × Fin n) ⊕ (Fin n × Fin n) →₀ ℕ) :
    ev (Matrix.diagonal (fun a => Complex.exp (-((θ a : ℂ) * Complex.I))) * g) (monomial s 1) =
      Complex.exp (((∑ a, monWt s a * θ a : ℝ) : ℂ) * Complex.I) * ev g (monomial s 1) := by
  have h1 : (∑ a, monWt s a * θ a : ℝ) = ∑ i, (s i : ℝ) * ∑ a, varWt i a * θ a := by
    simp only [monWt, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  rw [h1]
  simp only [ev, eval_monomial, one_mul]
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Complex.ofReal_sum, Finset.sum_mul,
    Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc, Complex.exp_nat_mul, ← mul_pow]
  congr 1
  rcases i with x | x
  · simp [varWt, Pi.single_apply, ite_mul]
  · simp [varWt, Pi.single_apply, ite_mul, ← Complex.exp_conj]

theorem continuous_toMK (ε : Fin n → Bool) : Continuous fun k : KG ε => toMK k :=
  (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.continuous.comp continuous_subtype_val

theorem continuous_ev (P : Poly n) : Continuous fun g : Mat n => ev g P := by
  refine (MvPolynomial.continuous_eval P).comp (continuous_pi ?_)
  rintro (x | x)
  · simp only [Sum.elim_inl]; fun_prop
  · simp only [Sum.elim_inr]; fun_prop

theorem toMK_mem (ε : Fin n → Bool) (k : KG ε) : toMK k ∈ UJset ε := (k : Formalism.REAL.UJ ε).2

theorem toMK_mul (ε : Fin n → Bool) (a b : KG ε) : toMK (a * b) = toMK a * toMK b := rfl

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Mat n → (H →L[ℂ] H)}

omit [CompleteSpace H] in
theorem integrable_avg (hσ : IsURepOn (UJset ε) σ) (u : H) (P : Poly n) :
    Integrable (fun k : KG ε => ev (toMK k) P • σ (toMK k) u) (muK ε) := by
  have h : Continuous fun k : KG ε => ev (toMK k) P • σ (toMK k) u :=
    ((continuous_ev P).comp (continuous_toMK ε)).smul
      ((hσ.2.2 u).comp_continuous (continuous_toMK ε) (toMK_mem ε))
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def avg (hσ : IsURepOn (UJset ε) σ) (u : H) : Poly n →ₗ[ℂ] H where
  toFun P := ∫ k : KG ε, ev (toMK k) P • σ (toMK k) u ∂(muK ε)
  map_add' P Q := by
    rw [← integral_add (integrable_avg hσ u P) (integrable_avg hσ u Q)]
    simp only [map_add (f := _), add_smul]
  map_smul' c P := by
    rw [RingHom.id_apply, ← integral_smul]
    simp [ev, smul_eq_C_mul, mul_smul]

theorem apply_avg (hσ : IsURepOn (UJset ε) σ) (u : H) (P : Poly n) (g : KG ε) :
    σ (toMK g) (avg hσ u P) = ∫ k : KG ε, ev (toMK g⁻¹ * toMK k) P • σ (toMK k) u ∂(muK ε) := by
  change σ (toMK g) (∫ k : KG ε, ev (toMK k) P • σ (toMK k) u ∂(muK ε)) = _
  rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_avg hσ u P),
    ← integral_mul_left_eq_self (fun k : KG ε => ev (toMK g⁻¹ * toMK k) P • σ (toMK k) u) g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only
  rw [← toMK_mul, inv_mul_cancel_left, toMK_mul, hσ.1.2 _ (toMK_mem ε g) _ (toMK_mem ε k), map_smul]
  rfl

theorem isWtOn_avg (hσ : IsURepOn (UJset ε) σ) (u : H) (s : (Fin n × Fin n) ⊕ (Fin n × Fin n) →₀ ℕ) :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ (monWt s) (avg hσ u (monomial s 1)) := by
  intro θ hθ
  rw [← Formalism.REAL.range_toMK] at hθ
  obtain ⟨g, hg⟩ := hθ
  simp only at hg
  have hinv : toMK g⁻¹ = Matrix.diagonal (fun a => Complex.exp (-((θ a : ℂ) * Complex.I))) := by
    have h1 : toMK g * Matrix.diagonal (fun a => Complex.exp (-((θ a : ℂ) * Complex.I))) = 1 := by
      rw [hg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have h2 : toMK g⁻¹ * toMK g = 1 := by rw [← toMK_mul, inv_mul_cancel]; rfl
    rw [← Matrix.mul_one (toMK g⁻¹), ← h1, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [← hg, apply_avg, hinv]
  simp only [ev_diag_monomial, mul_smul]
  rw [integral_smul]
  rfl

theorem polyAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ), ∃ A : Set (Fin n → ℝ), A.Finite ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ → ∀ u : H, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Formalism.MainNotions.S.IsKStableOn ε σ S ∧ (∀ P : GlobalTheory.PsCo.Pc1.Poly n, P.totalDegree ≤ d → ∫ k : Formalism.REAL.KG ε, GlobalTheory.PsCo.Pc1.ev (Formalism.REAL.toMK k) P • σ (Formalism.REAL.toMK k) u ∂(Formalism.REAL.muK ε) ∈ S) ∧ ∀ (μ : Fin n → ℝ) (s : H), s ∈ S → s ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s → μ ∈ A := by
  intro n ε d
  refine ⟨monWt '' {s | s.degree ≤ d}, (Finsupp.finite_of_degree_le d).image _, ?_⟩
  intro H _ _ _ σ hσ u
  refine ⟨(restrictTotalDegree _ ℂ d).map (avg hσ u), inferInstance, ?_, ?_, ?_⟩
  · rintro g hg v ⟨P, hP, rfl⟩
    rw [← Formalism.REAL.range_toMK] at hg
    obtain ⟨g, rfl⟩ := hg
    obtain ⟨Q, hQ, hQ'⟩ := exists_translate (toMK g⁻¹) P
    refine ⟨Q, (mem_restrictTotalDegree _ _ _).2 (hQ.trans ((mem_restrictTotalDegree _ _ _).1 hP)), ?_⟩
    simp only
    rw [apply_avg]
    simp only [hQ']
    rfl
  · intro P hP
    exact ⟨P, (mem_restrictTotalDegree _ _ _).2 hP, rfl⟩
  · rintro μ v ⟨P, hP, rfl⟩ hv hw
    by_contra hμ
    apply hv
    have hP' : P.totalDegree ≤ d := (mem_restrictTotalDegree _ _ _).1 hP
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    have e : avg hσ u P = ∑ s ∈ P.support, AddMonoidAlgebra.coeff P s • avg hσ u (monomial s 1) := by

      conv_lhs => rw [P.as_sum, map_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]
    generalize avg hσ u P = v at e hw
    have : inner ℂ v (∑ s ∈ P.support, AddMonoidAlgebra.coeff P s • avg hσ u (monomial s 1)) = 0 := by
      rw [inner_sum]
      refine Finset.sum_eq_zero fun s hs => ?_
      rw [inner_smul_right, ReciprocityTheory.ChartRestriction.DS.kfin_wt_orth hσ hw (isWtOn_avg hσ u s), mul_zero]
      rintro rfl
      exact hμ ⟨s, (le_totalDegree hs).trans hP', rfl⟩
    rwa [← e] at this

end GlobalTheory.PsCo.PolyAvg

end
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem kills_prod_comp_surj : ∀ (P G₁ G₂ : Type) [Group P] [Finite P] [Group G₁] [Group G₂] (π : P →* G₁ × G₂), Function.Surjective π → ∀ (φ₁ Y₁ : G₁ → ℂ) (φ₂ Y₂ : G₂ → ℂ), IsChar ℂ ℂ Y₁ → IsChar ℂ ℂ Y₂ → Kills φ₁ Y₁ → Kills φ₂ Y₂ → Kills (fun p => φ₁ (π p).1 * φ₂ (π p).2) (fun p => Y₁ (π p).1 * Y₂ (π p).2) := by
  intro P G₁ G₂ _ _ _ _ π hπ φ₁ Y₁ φ₂ Y₂ hY₁ hY₂ h₁ h₂
  haveI : Finite G₁ := Finite.of_surjective (fun p => (π p).1) (fun g => by
    obtain ⟨p, hp⟩ := hπ (g, 1); exact ⟨p, by simp [hp]⟩)
  haveI : Finite G₂ := Finite.of_surjective (fun p => (π p).2) (fun g => by
    obtain ⟨p, hp⟩ := hπ (1, g); exact ⟨p, by simp [hp]⟩)
  haveI := Fintype.ofFinite P
  haveI := Fintype.ofFinite G₁
  haveI := Fintype.ofFinite G₂
  have hY : IsChar ℂ ℂ (fun p => Y₁ (π p).1 * Y₂ (π p).2) := by
    obtain ⟨n, ρ, hρ⟩ := hY₁
    obtain ⟨m, σ, hσ⟩ := hY₂
    exact isChar_mul_complex (a := fun p => Y₁ (π p).1) (b := fun p => Y₂ (π p).2)
      ⟨n, ρ.comp ((MonoidHom.fst G₁ G₂).comp π), fun p => hρ _⟩
      ⟨m, σ.comp ((MonoidHom.snd G₁ G₂).comp π), fun p => hσ _⟩
  obtain ⟨k₁, hk₁⟩ := (GlobalTheory.T.isInCharacterIsotypicPart_iff_convolution G₁ φ₁ Y₁ hY₁).1 h₁
  obtain ⟨k₂, hk₂⟩ := (GlobalTheory.T.isInCharacterIsotypicPart_iff_convolution G₂ φ₂ Y₂ hY₂).1 h₂
  apply (GlobalTheory.T.isInCharacterIsotypicPart_iff_convolution P _ _ hY).2
  set c : ℕ := (Finset.univ.filter fun q : P => π q = 1).card with hcdef
  have hc : (c : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    apply Finset.card_ne_zero_of_mem (a := (1 : P))
    simp
  refine ⟨fun p => k₁ (π p).1 * k₂ (π p).2 / c, fun x => ?_⟩
  rw [hk₁, hk₂]
  simp only [finsum_eq_sum_of_fintype]
  set F : G₁ × G₂ → ℂ := fun g => Y₁ g.1 * Y₂ g.2 * (k₁ (g.1⁻¹ * (π x).1) * k₂ (g.2⁻¹ * (π x).2)) with hF
  have hR : ∀ q : P, Y₁ (π q).1 * Y₂ (π q).2 * (k₁ (π (q⁻¹ * x)).1 * k₂ (π (q⁻¹ * x)).2 / c) = F (π q) / c := by
    intro q
    simp only [hF, map_mul, map_inv, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
    ring
  simp only [hR]
  rw [← Finset.sum_div]
  have hfib : ∑ q : P, F (π q) = ∑ g : G₁ × G₂, (c : ℂ) * F g := by
    rw [← Finset.sum_fiberwise Finset.univ (fun q => π q) (fun q => F (π q))]
    refine Finset.sum_congr rfl fun g _ => ?_
    have e : ∀ q ∈ Finset.univ.filter (fun q : P => π q = g), F (π q) = F g := by
      intro q hq; rw [(Finset.mem_filter.1 hq).2]
    rw [Finset.sum_congr rfl e, Finset.sum_const, nsmul_eq_mul, hcdef,
      MonoidHom.card_fiber_eq_of_mem_range π (hπ g) (hπ 1)]
  rw [hfib, ← Finset.mul_sum, mul_div_cancel_left₀ _ hc, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [hF]
  ring

end GlobalTheory.Shin
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleCohomologyEquivalence_baseChange_cechAugmentation : ∀ (R : Type) [CommRing R] (F : Shv R) (S W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W), Etale f → Surjective f → ∀ U : Over S, Eqv R ((bcMap (cechAug f) (sch.map r)).app U) F := by
  first | (exact @GlobalTheory.EtC.bc_cechAug_eqv) | (exact GlobalTheory.EtC.bc_cechAug_eqv) | (intros; apply GlobalTheory.EtC.bc_cechAug_eqv  <;> assumption)
end
