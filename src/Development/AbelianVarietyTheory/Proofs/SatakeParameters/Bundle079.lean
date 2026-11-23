module

public import Formalism.GradedWeylDivisibility.StatementA
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle002
public import Formalism.LocalRingCardinality.DataDIV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle072
public import Formalism.SatakeDualWeyl.Bundle001
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle073
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.PowerSeries.Inverse
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle003
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

@[expose] public section

section

open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylRowAll

def coeffMap {R S σ : Type} [CommRing R] [CommRing S] (c : S →+ R) (F : MvPolynomial σ S) :
    MvPolynomial σ R :=
  ∑ m ∈ F.support, monomial m (c (AddMonoidAlgebra.coeff F m))

theorem coeff_coeffMap {R S σ : Type} [CommRing R] [CommRing S] (c : S →+ R)
    (F : MvPolynomial σ S) (m : σ →₀ ℕ) : AddMonoidAlgebra.coeff (coeffMap c F) m = c (AddMonoidAlgebra.coeff F m) := by
  classical
  simp only [coeffMap, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, map_zero]

theorem coeffMap_mem_weyl {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (c : S →+ R)
    (hc : ∀ (s : S) (a : R), c (s * φ a) = c s * a) {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (F : MvPolynomial (Fin r × Fin n) S) (hF : F ∈ Formalism.GradedWeylDivisibility.weyl S r n hn ν) :
    coeffMap c F ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  have key : ∀ s : S, coeffMap c (s • F) ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
    unfold Formalism.GradedWeylDivisibility.weyl at hF
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      intro s
      have : coeffMap c (s • Formalism.GradedWeylDivisibility.applyWord S w (Formalism.GradedWeylDivisibility.hw S hn ν)) =
          c s • Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν) := by
        ext m
        rw [coeff_coeffMap, ← Formalism.GradedWeylDivisibility.lclosedeq_hw_map φ, Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map,
          MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, coeff_map, smul_eq_mul, smul_eq_mul, hc]
      show coeffMap c (s • Formalism.GradedWeylDivisibility.applyWord S w (Formalism.GradedWeylDivisibility.hw S hn ν)) ∈ _
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩)
    | zero =>
      intro s
      have : coeffMap c (s • (0 : MvPolynomial (Fin r × Fin n) S)) = 0 := by
        ext m; simp [coeff_coeffMap]
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      intro s
      have : coeffMap c (s • (x + y)) = coeffMap c (s • x) + coeffMap c (s • y) := by
        ext m; simp [coeff_coeffMap, mul_add]
      rw [this]; exact Submodule.add_mem _ (hx s) (hy s)
    | smul a x _ hx =>
      intro s
      rw [smul_smul]; exact hx _
  simpa using key 1

theorem map_mem_weyl {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ} (hn : n ≤ r)
    (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) :
    map φ f ∈ Formalism.GradedWeylDivisibility.weyl S r n hn ν := by
  unfold Formalism.GradedWeylDivisibility.weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    show map φ (Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)) ∈ _
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
    exact Submodule.subset_span ⟨w, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

theorem map_rowAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (g : Matrix (Fin r) (Fin r) R) (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (Formalism.GradedWeylDivisibility.rowAct R g f) = Formalism.GradedWeylDivisibility.rowAct S (g.map φ) (map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp [Formalism.GradedWeylDivisibility.rowAct]

def toInv (R : Type) [CommRing R] : Polynomial R →+* HahnSeries ℤ R :=
  Polynomial.eval₂RingHom HahnSeries.C (HahnSeries.single (-1 : ℤ) (1 : R))

theorem coeff_zero_toInv (R : Type) [CommRing R] (p : Polynomial R) :
    (toInv R p).coeff 0 = p.eval 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k a =>
    simp only [toInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
      Polynomial.eval_monomial, HahnSeries.single_pow, HahnSeries.C_apply,
      HahnSeries.single_mul_single]
    rcases k with _ | k
    · simp
    · rw [HahnSeries.coeff_single_of_ne]
      · simp
      · simp; omega

theorem isUnit_shift (R : Type) [CommRing R] {r : ℕ} (M : Matrix (Fin r) (Fin r) R) :
    IsUnit ((M.map Polynomial.C + (Polynomial.X : Polynomial R) • (1 : Matrix (Fin r) (Fin r) _)).map
      (toInv R)) := by
  set A : Matrix (Fin r) (Fin r) (PowerSeries R) :=
    1 + (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C with hA
  have h1 : IsUnit A.det := by
    rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
    have : (PowerSeries.constantCoeff (R := R)).mapMatrix A = 1 := by
      ext i j
      by_cases h : i = j <;> simp [hA, Matrix.one_apply, h]
    rw [this]; simp
  have h2 : IsUnit (A.map (HahnSeries.ofPowerSeries ℤ R)).det := by
    have := h1.map (HahnSeries.ofPowerSeries ℤ R)
    rwa [RingHom.map_det] at this
  have hT : (HahnSeries.single (-1 : ℤ) (1 : R)) * HahnSeries.single (1 : ℤ) (1 : R) = 1 := by
    rw [HahnSeries.single_mul_single]; simp
  have h3 : ((M.map Polynomial.C + (Polynomial.X : Polynomial R) • (1 : Matrix (Fin r) (Fin r) _)).map
      (toInv R)) = (HahnSeries.single (-1 : ℤ) (1 : R)) • A.map (HahnSeries.ofPowerSeries ℤ R) := by
    refine Matrix.ext fun i j => ?_
    simp only [hA, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _),
      map_mul, HahnSeries.ofPowerSeries_X, HahnSeries.ofPowerSeries_C, mul_add, ← mul_assoc, hT,
      one_mul, toInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X,
      Matrix.one_apply]
    rw [add_comm]
    split_ifs <;> simp
  rw [Matrix.isUnit_iff_isUnit_det, h3, Matrix.det_smul]
  exact ((IsUnit.of_mul_eq_one _ hT).pow _).mul h2

theorem rowAct_mem_weyl (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (M : Matrix (Fin r) (Fin r) R) (f : MvPolynomial (Fin r × Fin n) R)
    (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) : Formalism.GradedWeylDivisibility.rowAct R M f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  set B : Matrix (Fin r) (Fin r) (Polynomial R) :=
    M.map Polynomial.C + (Polynomial.X : Polynomial R) • (1 : Matrix (Fin r) (Fin r) _) with hB
  obtain ⟨u, hu⟩ := isUnit_shift R M
  have h1 := Formalism.UG.Final.WeylGLStable (HahnSeries ℤ R) r n hn ν u⁻¹ _
    (map_mem_weyl (toInv R) hn ν _ (map_mem_weyl Polynomial.C hn ν f hf))
  rw [Formalism.UG.dwAct, inv_inv, hu, ← hB, ← map_rowAct] at h1
  have h2 := coeffMap_mem_weyl (HahnSeries.C : R →+* HahnSeries ℤ R)
    (HahnSeries.coeff.addMonoidHom (0 : ℤ)) (by
      intro s a
      simp [HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero]) hn ν _ h1
  have h3 : coeffMap (HahnSeries.coeff.addMonoidHom (0 : ℤ))
      (map (toInv R) (Formalism.GradedWeylDivisibility.rowAct (Polynomial R) B (map Polynomial.C f))) =
      map (Polynomial.evalRingHom (0 : R)) (Formalism.GradedWeylDivisibility.rowAct (Polynomial R) B (map Polynomial.C f)) := by
    ext m
    rw [coeff_coeffMap, coeff_map, coeff_map]
    exact coeff_zero_toInv R _
  have h4 : B.map (Polynomial.evalRingHom (0 : R)) = M := by
    ext i j
    simp [hB]
  have h5 : map (Polynomial.evalRingHom (0 : R)) (map Polynomial.C f) = f := by
    ext m
    simp [coeff_map]
  rwa [h3, map_rowAct, h4, h5] at h2

theorem rowAct_mem_weyl_square : ∀ (R : Type) [CommRing R] (n : ℕ) (ν : Fin n → ℕ), Antitone ν →
    ∀ (M : Matrix (Fin n) (Fin n) R), ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν,
      Formalism.GradedWeylDivisibility.rowAct R M f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν :=
  fun R _ _ ν _ M f hf => rowAct_mem_weyl R le_rfl ν M f hf

end GlobalTheory.WeylRowAll
end
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.FrobSign

theorem frobG_isArithFrob_and_sign : ∀ (D : D7) (l : ℕ) [Fact l.Prime], l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d →
    (∀ (Q : Ideal (𝓞 D.host.E)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(l : ℤ)})],
      IsArithFrobAt ℤ (D.host.sigmaOf (DV.frobG D l)) Q) ∧
    ((((DV.frobG D l).1.2 : ℤˣ) : ℤ) = jacobiSym (-(D.host.d : ℤ)) l) := by
  intro D l hl h2 hq hd
  have hlN : ¬ l ∣ D.host.condN := fun h => by
    rcases (D.host.dvd_condN_iff_small Fact.out).1 h with h | h | h
    exacts [h2 h, hq h, hd h]
  have hall : ∀ (Q : Ideal (𝓞 D.host.E)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(l : ℤ)})],
      IsArithFrobAt ℤ (D.host.sigmaOf (DV.frobG D l)) Q :=
    fun Q _ _ => GlobalTheory.FrobEmb.isArithFrobAt_frobG D l hl.out Q
  refine ⟨hall, ?_⟩
  have hlZ : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
  have hlI : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hlZ.ne_zero).2 hlZ
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((Ideal.span {(l : ℤ)}).primesOver (𝓞 D.host.E)) := inferInstance
  have hg : D.host.gal (D.host.sigmaOf (DV.frobG D l)) = DV.frobG D l := MulEquiv.apply_symm_apply _ _
  have h := ((D.host.der.frob l hlN P).2.2.1 _ (hall P)).2.1
  rw [hg] at h
  exact h

end GlobalTheory.FrobSign
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.thinSize_dominates_at_large_scale : ∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), L.sc.eps = eps → x0 ≤ L.sc.x → (100 : ℝ) ≤ L.sc.w'' D.R.n ∧ 100 * (L.etaSz + L.Sc + D.R.t + 2) ≤ L.sc.w'' D.R.n ∧ L.sc.w'' D.R.n ≤ L.sc.b' := by
  first | exact @GlobalTheory.HTW.thinSize_dominates | exact GlobalTheory.HTW.thinSize_dominates | (intros; apply GlobalTheory.HTW.thinSize_dominates <;> assumption)
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.topSize_add_le_three_halves_scale : ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), 4 ≤ L.sc.x → ∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ 3 / 2 * L.sc.b' := by
  first | exact @GlobalTheory.Ggeo.bT_add_div_le_three_halves | exact GlobalTheory.Ggeo.bT_add_div_le_three_halves | (intros; apply GlobalTheory.Ggeo.bT_add_div_le_three_halves <;> assumption)
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.scale_log_mul_le_size_ratio : ∀ eps C A : ℝ, 0 < eps → 0 ≤ C → 0 ≤ A → ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x → C * (A * Real.log s.x + 1) * s.b' ≤ s.b := by
  first | exact @GlobalTheory.scale_log_mul_b'_le_b | exact GlobalTheory.scale_log_mul_b'_le_b | (intros; apply GlobalTheory.scale_log_mul_b'_le_b <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.twistedDual_continuous_integral_over_enlarged_coeff : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (LL' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ LL'.1) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) → Continuous (fun g => mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)) g) ∧ ∀ g a b, ‖((mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)) g a b : ↥LL'.1) : Om (D.nd.l i))‖ ≤ 1 := by
  first | exact @GlobalTheory.TwistedDualLoc.continuous_and_integral | exact GlobalTheory.TwistedDualLoc.continuous_and_integral | (intros; apply GlobalTheory.TwistedDualLoc.continuous_and_integral <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

theorem _root_.GlobalTheory.T.complexHeckeEigenvector_descends_to_coefficientField : ∀ (D : D7) (M : Formalism.L2.MtFam D) (B : Formalism.L2.NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) (μ : D.what₂.Tup) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), μ = D.what₂.muTw w → ∀ (φ : FractionRing (B.Oc j w) →+* ℂ), (∀ x, φ (B.ec j w x) = D.what₂.embLL x) → ∀ (κ : PlE D.host → ℕ → FractionRing (B.Oc j w)) (y : D.what₂.Mt μ j), y ≠ 0 → (∀ v k, Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∃ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ Formalism.AUTREP.IsUnif D.host.E s.v ϖ ∧ (∀ (c : ℂ) (f f' : Formalism.AUTREP.GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W), Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k (c • f + f') = c • Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k f + Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k f') ∧ Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k ((M μ j h1 h2).real y) = φ (κ v k) • (M μ j h1 h2).real y) → ∃ e : B.V j w, e ≠ 0 ∧ ∀ v k, Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → B.hK j w v k e = κ v k • e := by
  exact @GlobalTheory.PtLocalEig.eig_descends
end

section

open IsDedekindDomain NumberField

namespace GlobalTheory

theorem antitone_zero_one_eq_of_sum_eq {n : ℕ} (d e : Fin n → ℤ) (hd : Antitone d) (he : Antitone e)
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1) (he0 : ∀ i, 0 ≤ e i) (he1 : ∀ i, e i ≤ 1)
    (hs : ∑ i, d i = ∑ i, e i) : d = e := by
  have key : (∀ i, d i ≤ e i) ∨ (∀ i, e i ≤ d i) := by
    by_contra h
    push Not at h
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := h
    have := hd0 j; have := hd1 i; have := he0 i; have := he1 j
    rcases le_total i j with hij | hij
    · have := he hij; omega
    · have := hd hij; omega
  rcases key with h | h
  · funext i
    exact (Finset.sum_eq_sum_iff_of_le (fun i _ => h i)).1 hs i (Finset.mem_univ i)
  · funext i
    exact ((Finset.sum_eq_sum_iff_of_le (fun i _ => h i)).1 hs.symm i (Finset.mem_univ i)).symm

section

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem glint_entry_mem_Ov {k : GL (Fin n) (v.adicCompletion F)}
    (hk : k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v)) (i j : Fin n) :
    (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v := by
  obtain ⟨g, rfl⟩ := hk
  have : ((Formalism.UG.bc (n := Fin n) (Formalism.UG.Ov F v).subtype g : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j
      = (((g : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v)) i j : Formalism.UG.Ov F v) : v.adicCompletion F) := by
    simp [Formalism.UG.bc, Units.coe_map]
  rw [this]
  exact Subtype.property _

theorem mul_mul_entry_mem_Ov {A B C : Matrix (Fin n) (Fin n) (v.adicCompletion F)}
    (hA : ∀ i j, A i j ∈ Formalism.UG.Ov F v) (hB : ∀ i j, B i j ∈ Formalism.UG.Ov F v)
    (hC : ∀ i j, C i j ∈ Formalism.UG.Ov F v) (i j : Fin n) : (A * B * C) i j ∈ Formalism.UG.Ov F v := by
  simp only [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _
    (Subring.sum_mem _ fun m _ => Subring.mul_mem _ (hA _ _) (hB _ _)) (hC _ _)

theorem valued_det_le_one_of_entries {A : Matrix (Fin n) (Fin n) (v.adicCompletion F)}
    (hA : ∀ i j, A i j ∈ Formalism.UG.Ov F v) : Valued.v A.det ≤ 1 := by
  have : A.det ∈ Formalism.UG.Ov F v := by
    rw [Matrix.det_apply']
    exact Subring.sum_mem _ fun σ _ => Subring.mul_mem _ (intCast_mem _ _)
      (Subring.prod_mem _ fun i _ => hA _ _)
  exact this

theorem valued_det_eq_one_of_glint {k : GL (Fin n) (v.adicCompletion F)}
    (hk : k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v)) :
    Valued.v (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = 1 := by
  have h1 := valued_det_le_one_of_entries (glint_entry_mem_Ov hk)
  have h2 := valued_det_le_one_of_entries (glint_entry_mem_Ov (Subgroup.inv_mem _ hk))
  have h3 : Valued.v (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det *
      Valued.v ((k⁻¹ : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
    _ ≤ _ * 1 := mul_le_mul_right h2 _
    _ = _ := mul_one _

theorem cartan_minuscule (k : ℕ) (ϖ ϖ' : v.adicCompletion F)
    (hϖ : Formalism.UG.IsUnifV F v ϖ) (hϖ' : Formalism.UG.IsUnifV F v ϖ') (a : GL (Fin n) (v.adicCompletion F))
    (h1 : ∀ i j, (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v)
    (h2 : ∀ i j, ϖ' * ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v)
    (h3 : Valued.v (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = Valued.v ϖ' ^ k) :
    ∃ d : Fin n → ℤ, Antitone d ∧ (∀ i, 0 ≤ d i) ∧ (∀ i, d i ≤ 1) ∧ ∑ i, d i = k ∧
      ∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v),
        ((k₁⁻¹ * a * k₂⁻¹ : GL (Fin n) (v.adicCompletion F)) :
          Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Formalism.UG.diagPow F v ϖ d := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hv' : Valued.v ϖ' = WithZero.exp (-1 : ℤ) := hϖ'
  have hϖO : ϖ ∈ Formalism.UG.Ov F v := by
    show Valued.v ϖ ≤ 1
    rw [hv]
    exact (WithZero.exp_le_exp.mpr (by norm_num : (-1:ℤ) ≤ 0)).trans (le_of_eq WithZero.exp_zero)
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hpow : ∀ m : ℤ, Valued.v (ϖ ^ m) = WithZero.exp (-m) := by
    intro m
    rw [map_zpow₀, hv, ← WithZero.exp_zsmul]
    simp
  have hsum : ∀ d : Fin n → ℤ, ∏ i, ϖ ^ d i = ϖ ^ ∑ i, d i := by
    intro d
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => simp
    | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, zpow_add₀ hϖ0]
  obtain ⟨d, hd, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp F v n ϖ hϖO hϖ a
  have hD : ((k₁⁻¹ * a * k₂⁻¹ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Formalism.UG.diagPow F v ϖ d := by
    simp only [Units.val_mul, e, mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, mul_one]
  have hDinv : ((k₂ * a⁻¹ * k₁ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Formalism.UG.diagPow F v ϖ (-d) := by
    have e1 : (k₂ * a⁻¹ * k₁ : GL (Fin n) (v.adicCompletion F)) = (k₁⁻¹ * a * k₂⁻¹)⁻¹ := by group
    rw [e1, Matrix.coe_units_inv, hD]
    apply Matrix.inv_eq_left_inv
    unfold Formalism.UG.diagPow
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ0]
    simp
  refine ⟨d, hd, fun i => ?_, fun i => ?_, ?_, k₁, hk₁, k₂, hk₂, hD⟩
  · have := mul_mul_entry_mem_Ov (glint_entry_mem_Ov (Subgroup.inv_mem _ hk₁)) h1
      (glint_entry_mem_Ov (Subgroup.inv_mem _ hk₂)) i i
    rw [← Units.val_mul, ← Units.val_mul, hD] at this
    have h : Valued.v (Formalism.UG.diagPow F v ϖ d i i) ≤ 1 := this
    rw [Formalism.UG.diagPow, Matrix.diagonal_apply_eq, hpow, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at h
    omega
  · have := mul_mul_entry_mem_Ov (B := ϖ' • ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F))) (glint_entry_mem_Ov hk₂) h2
      (glint_entry_mem_Ov hk₁) i i
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Units.val_mul, ← Units.val_mul, hDinv] at this
    have h : Valued.v (ϖ' * Formalism.UG.diagPow F v ϖ (-d) i i) ≤ 1 := this
    rw [Formalism.UG.diagPow, Matrix.diagonal_apply_eq, map_mul, hpow, hv', ← WithZero.exp_add,
      ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    simp only [Pi.neg_apply] at h
    omega
  · rw [e, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, valued_det_eq_one_of_glint hk₁,
      valued_det_eq_one_of_glint hk₂, one_mul, mul_one, Formalism.UG.diagPow, Matrix.det_diagonal,
      hsum, hpow, hv', ← WithZero.exp_nsmul, WithZero.exp_inj] at h3
    simp only [nsmul_eq_mul] at h3
    omega

end

theorem glint_doubleCoset_of_minuscule : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n k : ℕ) (ϖ ϖ' : v.adicCompletion F), Formalism.UG.IsUnifV F v ϖ → Formalism.UG.IsUnifV F v ϖ' → ∀ a a' : GL (Fin n) (v.adicCompletion F), (∀ i j, (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v) → (∀ i j, ϖ * ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v) → Valued.v (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = Valued.v ϖ ^ k → (∀ i j, (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v) → (∀ i j, ϖ' * ((a'⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v) → Valued.v (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = Valued.v ϖ' ^ k → ∃ x ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∃ y ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), a' = x * a * y := by
  intro F _ _ v n k ϖ ϖ' hϖ hϖ' a a' h1 h2 h3 h1' h2' h3'
  obtain ⟨d, hd, hd0, hd1, hs, k₁, hk₁, k₂, hk₂, hD⟩ := cartan_minuscule k ϖ ϖ hϖ hϖ a h1 h2 h3
  obtain ⟨e, he, he0, he1, ht, l₁, hl₁, l₂, hl₂, hE⟩ :=
    cartan_minuscule k ϖ ϖ' hϖ hϖ' a' h1' h2' h3'
  obtain rfl : d = e := antitone_zero_one_eq_of_sum_eq d e hd he hd0 hd1 he0 he1 (hs.trans ht.symm)
  have h : k₁⁻¹ * a * k₂⁻¹ = l₁⁻¹ * a' * l₂⁻¹ := Units.ext (hD.trans hE.symm)
  refine ⟨l₁ * k₁⁻¹, Subgroup.mul_mem _ hl₁ (Subgroup.inv_mem _ hk₁), k₂⁻¹ * l₂,
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hk₂) hl₂, ?_⟩
  calc a' = l₁ * (l₁⁻¹ * a' * l₂⁻¹) * l₂ := by group
    _ = l₁ * (k₁⁻¹ * a * k₂⁻¹) * l₂ := by rw [h]
    _ = _ := by group

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.LiftTypePrime

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions

def StdAt (D : D7) (g : ℕ) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  ∃ L₀ : Submodule (𝓞 D.host.E) (Fin N → D.host.E), (∀ x, x ∈ L₀ ↔ ∀ k, IsIntegral ℤ (x k)) ∧ EqAt D g L L₀


end GlobalTheory.LiftTypePrime

end
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.absIrrSub_map_of_irredOn_map_Fbar : ∀ {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {k k' : Type} [Field k] [Field k'] {r : ℕ}, 1 ≤ r → ∀ (rb : Γ →* GL (Fin r) k) (ι : k →+* Formalism.CyclotomicNorms.Fbar l), Formalism.CyclotomicNorms.IrredOn (mapRep ι rb) ⊤ → ∀ φ : k →+* k', AbsIrrSub (mapRep φ rb) ⊤ := by
  first | exact @GlobalTheory.StringRepresentationDecomposition.irr_transfer_absIrr | exact GlobalTheory.StringRepresentationDecomposition.irr_transfer_absIrr | (intros; apply GlobalTheory.StringRepresentationDecomposition.irr_transfer_absIrr <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.local_h1f_finite_dimensional : Formalism.GaloisCohomology.LocalFinitenessK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (k : ℕ) (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1), Continuous (fun g => M g) → (∀ g a b, ‖((M g a b : ↥LL.1) : Om l)‖ ≤ 1) → Module.Finite ↥LL.1 (FiniteCohomology (P.PD K) (matRep M)) := by
  first | exact @GlobalTheory.LocalH1Finiteness.finite_H1fV_matRep | exact GlobalTheory.LocalH1Finiteness.finite_H1fV_matRep | (intros; apply GlobalTheory.LocalH1Finiteness.finite_H1fV_matRep <;> assumption)
end
