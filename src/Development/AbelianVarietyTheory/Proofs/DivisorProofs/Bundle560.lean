module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Mathlib.RingTheory.PowerSeries.Log
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle506
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle491
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle476
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.SqZero

theorem mvPolynomialEval_truncFinsupp_eq_sum_coeff_mul_prod {R σ : Type} [CommRing R] [Fintype σ] [DecidableEq σ] (w : σ → R)
    (n : σ →₀ ℕ) (f : MvPowerSeries σ R) :
    MvPolynomial.eval w (trunc' R n f) = ∑ β ∈ Finset.Iic n, coeff β f * ∏ i ∈ β.support, w i ^ β i := by
  have hsub : (trunc' R n f).support ⊆ Finset.Iic n := by
    intro m hm
    rw [MvPolynomial.mem_support_iff, coeff_trunc'] at hm
    split_ifs at hm with h
    · exact Finset.mem_Iic.mpr h
    · exact absurd rfl hm
  rw [MvPolynomial.eval_eq, Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [coeff_trunc', if_pos (Finset.mem_Iic.mp hm)]
  · intro m _ hm
    rw [MvPolynomial.notMem_support_iff.mp hm, zero_mul]

theorem hasVal_log_of_mul_self_eq_zero :
    ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] (p : ℕ) (x : B), x * x = 0 → HasVal p (fun _ : Unit => x) (PowerSeries.log Q : MvPowerSeries Unit Q) (algebraMap B Q x) := by
  intro B Q _ _ _ _ p x hx
  set y : Q := algebraMap B Q x with hy
  have hyy : y * y = 0 := by rw [hy, ← map_mul, hx, map_zero]
  have hcoeff : ∀ β : Unit →₀ ℕ, coeff β (PowerSeries.log Q : MvPowerSeries Unit Q) =
      PowerSeries.coeff (β ()) (PowerSeries.log Q) := by
    intro β
    rw [PowerSeries.coeff_def (by rfl)]
  intro m
  refine ⟨1, fun N' hN' => ⟨0, ?_⟩⟩
  rw [mul_zero, map_zero, sub_eq_zero, mvPolynomialEval_truncFinsupp_eq_sum_coeff_mul_prod]
  rw [Finset.sum_eq_single (Finsupp.single () 1)]
  · rw [hcoeff]
    simp [PowerSeries.coeff_log, hy]
  · intro β _ hβ
    rw [hcoeff, PowerSeries.coeff_log]
    by_cases h0 : β () = 0
    · simp [h0]
    · have h1 : β () ≠ 1 := by
        intro h1; apply hβ; ext u; simp [h1]
      have hsupp : β.support = {()} := by
        ext u; simp [h0]
      rw [hsupp, Finset.prod_singleton]
      obtain ⟨k, hk⟩ : ∃ k, β () = k + 2 := ⟨β () - 2, by omega⟩
      have hp : (algebraMap B Q) ((fun _ : Unit => x) ()) ^ (k + 2) = 0 := by
        show y ^ (k + 2) = 0
        rw [pow_add, pow_two, hyy, mul_zero]
      rw [hk, hp, mul_zero]
  · intro h
    exfalso; apply h
    rw [Finset.mem_Iic]
    intro u
    simpa using hN'

end GlobalTheory.QLog.SqZero
end
end

section

open Matrix

theorem _root_.GlobalTheory.T.weil_rep_bijection_schwartz : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    {β : Type} [Fintype β] [DecidableEq β] {Xt : Type} [AddCommGroup Xt] [Module ℂ Xt] (V : Submodule ℂ Xt)
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι₁ : Xt →ₗ[ℂ] (Matrix (Fin n) β k → ℂ)) (ι₂ : Xt → Matrix (Fin n) β k → ℂ),
    Set.BijOn ι₁ (V : Set Xt) (GlobalTheory.WeilM.SB (Matrix (Fin n) β k) : Set _) →
    (∀ x ∈ V, ∀ y ∈ V, ∀ c : ℂ, ι₂ (c • x + y) = c • ι₂ x + ι₂ y) →
    ∀ (Tr : Matrix (Fin n) β k → Xt → Xt) (Mu : (Matrix (Fin n) β k →ₗ[k] k) → Xt → Xt),
    (∀ C, ∀ x ∈ V, Tr C x ∈ V ∧ ι₁ (Tr C x) = (fun Y => ι₁ x (Y + C)) ∧ ι₂ (Tr C x) = fun Y => ι₂ x (Y + C)) →
    (∀ l, ∀ x ∈ V, Mu l x ∈ V ∧ ι₁ (Mu l x) = (fun Y => ψ0 (l Y) * ι₁ x Y) ∧ ι₂ (Mu l x) = fun Y => ψ0 (l Y) * ι₂ x Y) →
    ∃ c : ℂ, ∀ x ∈ V, ι₂ x = c • ι₁ x := by
  first | exact @GlobalTheory.schur_heisenberg_linearModel_fintype | exact GlobalTheory.schur_heisenberg_linearModel_fintype | (intros; apply GlobalTheory.schur_heisenberg_linearModel_fintype <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

open MvPolynomial in
theorem mvPolynomial_map_pderiv_lift {κ R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (i : κ)
    (f : MvPolynomial κ R) :
    MvPolynomial.map π (pderiv i f) = pderiv i (MvPolynomial.map π f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add (f := _), hp, map_X, pderiv_X]
    congr 1
    by_cases h : i = j
    · subst h; simp
    · simp [Pi.single_apply, Ne.symm h]

theorem isUnit_of_isUnit_map_of_sqZero_ker {A A₀ : Type} [CommRing A] [CommRing A₀] (p : A →+* A₀)
    (hp : Function.Surjective p) (K : Ideal A) (hK : K ^ 2 = 0) (hker : ∀ a, p a = 0 → a ∈ K)
    (x : A) (hx : IsUnit (p x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := hx.exists_right_inv
  obtain ⟨y, rfl⟩ := hp u
  have hn : x * y - 1 ∈ K := hker _ (by simp [hu])
  have hsq : (x * y - 1) * (x * y - 1) = 0 := by
    have : (x * y - 1) * (x * y - 1) ∈ K ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hn hn
    rw [hK] at this; simpa using this
  have hnil : IsNilpotent (x * y - 1) := ⟨2, by rw [pow_two, hsq]⟩
  have : IsUnit (x * y) := by simpa using hnil.isUnit_one_add
  exact isUnit_of_mul_isUnit_left this


open MvPolynomial in
theorem standardSmooth_lift_of_sqZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀], Algebra.IsStandardSmooth R₀ B₀ → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  intro R R₀ _ _ I hI π hπ hk B₀ _ _ hB₀
  obtain ⟨κ, τ, _, _, ⟨P⟩⟩ := hB₀.out
  classical
  have : Fintype τ := Fintype.ofFinite τ
  have hmap : Function.Surjective (MvPolynomial.map (σ := κ) π) := MvPolynomial.map_surjective π hπ
  let v : τ → MvPolynomial κ R := fun j => Function.surjInv hmap (P.relation j)
  have hv : ∀ j, MvPolynomial.map π (v j) = P.relation j := fun j => Function.surjInv_eq hmap _
  let J : Ideal (MvPolynomial κ R) := Ideal.span (Set.range v)
  let φ : MvPolynomial κ R →+* B₀ := (aeval P.val).toRingHom.comp (MvPolynomial.map π)
  have hφ : ∀ f, φ f = aeval P.val (MvPolynomial.map π f) := fun _ => rfl
  have hJ : J ≤ RingHom.ker φ := by
    rw [Ideal.span_le]; rintro _ ⟨j, rfl⟩
    simp [RingHom.mem_ker, hφ, hv, Algebra.Presentation.aeval_val_relation]
  let p : (MvPolynomial κ R ⧸ J) →+* B₀ := Ideal.Quotient.lift J φ hJ
  have hp : ∀ f, p (Ideal.Quotient.mk J f) = φ f := fun _ => rfl
  have halg : ∀ r : R, p (algebraMap R _ r) = algebraMap R₀ B₀ (π r) := by
    intro r
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial κ R) (MvPolynomial κ R ⧸ J)]
    simp [Ideal.Quotient.algebraMap_eq, hp, hφ]
  have hsemi : SemiHom π p := by
    intro r b
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, halg]
  have hsurj : Function.Surjective p := by
    intro b
    obtain ⟨g, rfl⟩ := P.aeval_val_surjective b
    obtain ⟨f, rfl⟩ := hmap g
    exact ⟨Ideal.Quotient.mk J f, rfl⟩
  have hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R (MvPolynomial κ R ⧸ J)) := by
    intro b
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
    constructor
    · intro h0
      rw [hp, hφ] at h0
      have hmem : MvPolynomial.map π f ∈ Ideal.span (Set.range P.relation) := by
        rw [P.span_range_relation_eq_ker]
        first
          | exact h0
          | exact RingHom.mem_ker.mpr h0
          | (rw [Algebra.Generators.ker_eq_ker_aeval_val]; exact h0)
      obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hmem
      let c' : τ → MvPolynomial κ R := fun j => Function.surjInv hmap (c j)
      have hc' : ∀ j, MvPolynomial.map π (c' j) = c j := fun j => Function.surjInv_eq hmap _
      have hg : f - ∑ j, c' j * v j ∈ RingHom.ker (MvPolynomial.map (σ := κ) π) := by

        rw [RingHom.mem_ker, map_sub, map_sum, ← hc]
        simp [hc', hv]
      rw [MvPolynomial.ker_map, hk] at hg
      have hs : ∑ j, c' j * v j ∈ J :=
        Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
      have : Ideal.Quotient.mk J f = Ideal.Quotient.mk J (f - ∑ j, c' j * v j) := by
        rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.2 hs, sub_zero]
      rw [this]
      have hmm := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hg
      rwa [Ideal.map_map] at hmm
    · intro hb
      have : I.map (algebraMap R (MvPolynomial κ R ⧸ J)) ≤ RingHom.ker p := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        simp only [Ideal.mem_comap, RingHom.mem_ker, halg]
        have : π x = 0 := by rw [← RingHom.mem_ker, hk]; exact hx
        simp [this]
      exact this hb
  let Q := Algebra.PreSubmersivePresentation.naive (v := v) P.map P.map_inj
  have hjac : p Q.jacobian = P.jacobian := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
      Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    have h1 : ∀ f : MvPolynomial κ R, algebraMap Q.Ring (MvPolynomial κ R ⧸ Ideal.span (Set.range v)) f =
        Ideal.Quotient.mk J f := fun _ => rfl
    rw [h1, hp, hφ, Algebra.Generators.algebraMap_apply]
    congr 1
    rw [RingHom.map_det]
    refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    show MvPolynomial.map π (pderiv (P.map i) (v j)) = pderiv (P.map i) (P.relation j)
    rw [mvPolynomial_map_pderiv_lift, hv]
  have hunit : IsUnit Q.jacobian := by
    refine isUnit_of_isUnit_map_of_sqZero_ker p hsurj (I.map (algebraMap R _)) ?_ (fun a ha => (hker a).1 ha) _
      (by rw [hjac]; exact P.jacobian_isUnit)
    rw [← Ideal.map_pow, hI]; simp
  let Q' : Algebra.SubmersivePresentation R (MvPolynomial κ R ⧸ J) κ τ :=
    { Q with jacobian_isUnit := hunit }
  have := Q'.isStandardSmooth
  exact ⟨_, inferInstance, inferInstance, p, hsemi, hsurj, hker, inferInstance⟩

end GlobalTheory.Obs
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.freeEtaleSheaf_biprodDesc_isIso_of_res_bijective : ∀ (R : Type) [CommRing R] {Y₁ Y₂ X : Scheme.{0}} (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X), (∀ F : Shv R, Function.Bijective fun s : Sec F X => (Sec.res f₁ s, Sec.res f₂ s)) → IsIso (biprod.desc ((free R).map (yoneda.map f₁)) ((free R).map (yoneda.map f₂))) := by
  first | exact @GlobalTheory.EtC.freeYoneda_desc_isIso | exact GlobalTheory.EtC.freeYoneda_desc_isIso | (intros; apply GlobalTheory.EtC.freeYoneda_desc_isIso <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistRingFunctor_preservesFilteredColimits : ∀ (q : ℕ) (i : ℤ), PreservesFilteredColimitsOfSize.{0, 0} (twF q i) := by
  first | (exact @GlobalTheory.EtC.TwistFiltered.twF_preservesFilteredColimits) | (exact GlobalTheory.EtC.TwistFiltered.twF_preservesFilteredColimits) | (intros; apply GlobalTheory.EtC.TwistFiltered.twF_preservesFilteredColimits  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

theorem _root_.GlobalTheory.T.alexanderWhitney_cup_degree_zero_support_cochain : ∀ {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {S : Spc} {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj S) I n) (β : Cochain ((chains R).obj S) J m) (γ : Cochain ((chains R).obj S) K k), μ.IsAW hk α β γ → (∀ (s : ℕ) (t : ℤ) (h : -(s : ℤ) + n = t) (U : Scheme.{0}) (x : Sx S s U), 0 < s → ev α s t h U x = 0) → ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (U : Scheme.{0}) (x : Sx S N U), ev γ N w h U x = μ.mul U n (-(N : ℤ) + m) w (by omega) (ev α 0 n (by simp) U (x.sub 0 0 (by omega))) (ev β N _ rfl U x) := by
  first | (exact @GlobalTheory.AWFront.ev_of_front) | (exact GlobalTheory.AWFront.ev_of_front) | (intros; apply GlobalTheory.AWFront.ev_of_front  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FreeCofan

theorem pieces {U : Scheme.{0}} {ι : Type} {V : ι → Scheme.{0}} (j : ∀ i, V i ⟶ U)
    (hc : IsColimit (Cofan.mk U j)) :
    (∀ i, IsOpenImmersion (j i)) ∧ (∀ u : U, ∃ i, ∃ v : V i, j i v = u) ∧
      (∀ i k (v : V i) (w : V k), j i v = j k w → i = k) := by
  let e : ∐ V ≅ U := (colimit.isColimit (Discrete.functor V)).coconePointUniqueUpToIso hc
  have he : ∀ i, Sigma.ι V i ≫ e.hom = j i := fun i =>
    (colimit.isColimit (Discrete.functor V)).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩
  have hinv : ∀ u : U, e.hom (e.inv u) = u := fun u => by
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl
  have hinv' : ∀ z : (∐ V : Scheme.{0}), e.inv (e.hom z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, e.hom_inv_id]; rfl
  refine ⟨fun i => ?_, fun u => ?_, fun i k v w h => ?_⟩
  · rw [← he i]; infer_instance
  · obtain ⟨⟨i, v⟩, hv⟩ := (sigmaMk V).surjective (e.inv u)
    refine ⟨i, v, ?_⟩
    rw [← he i, Scheme.Hom.comp_apply, ← sigmaMk_mk, hv, hinv]
  · rw [← he i, ← he k, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h
    have h2 := congrArg e.inv h
    rw [hinv', hinv'] at h2
    exact congrArg Sigma.fst ((sigmaι_eq_iff V i k v w).1 h2)

theorem pullback_isColimit {U : Scheme.{0}} {ι : Type} {V : ι → Scheme.{0}} (j : ∀ i, V i ⟶ U)
    (hc : IsColimit (Cofan.mk U j)) {T : Scheme.{0}} (y : T ⟶ U) :
    Nonempty (IsColimit (Cofan.mk T (fun i => pullback.fst y (j i)))) := by
  obtain ⟨ho, hcov, hdis⟩ := pieces j hc
  refine nonempty_isColimit_cofanMk_of _ ?_ ?_
  · rw [eq_top_iff]
    rintro z -
    obtain ⟨i, v, hv⟩ := hcov (y z)
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := y) (g := j i) z v hv.symm
    exact (TopologicalSpace.Opens.mem_iSup (s := fun i => (pullback.fst y (j i)).opensRange)).2 ⟨i, w, hw⟩
  · intro i k hik
    rw [Function.onFun, disjoint_iff, eq_bot_iff]
    rintro z ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    apply hik
    refine hdis i k (pullback.snd y (j i) p) (pullback.snd y (j k) q) ?_
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← pullback.condition, ← pullback.condition,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    change y ((pullback.fst y (j i)) p) = y ((pullback.fst y (j k)) q)
    rw [hp, hq]

theorem sec_subsingleton_of_isEmpty {R : Type} [CommRing R] (G : Shv R) (W : Scheme.{0}) [IsEmpty W] :
    Subsingleton (Sec G W) := by
  haveI : ∀ e : PEmpty.{1}, IsOpenImmersion (PEmpty.elim e : (PEmpty.elim e : Scheme.{0}) ⟶ W) :=
    fun e => e.elim
  obtain ⟨hc⟩ := nonempty_isColimit_cofanMk_of (X := fun e : PEmpty.{1} => (PEmpty.elim e : Scheme.{0})) (S := W)
    (fun e => PEmpty.elim e) (by rw [eq_top_iff]; rintro z -; exact isEmptyElim z) (fun e => PEmpty.elim e)
  have hb := GlobalTheory.T.etaleModuleSheaf_sections_coprod_bijective R G W PEmpty.{1} _ _ hc
  exact ⟨fun x y => hb.1 (funext fun e => PEmpty.elim e)⟩

end GlobalTheory.EtC.FreeCofan

namespace GlobalTheory.EtC.FreeCofan

theorem res_res {R : Type} [CommRing R] {G : Shv R} {W W' T : Scheme.{0}} (g : W ⟶ W') (f : W' ⟶ T)
    (z : Sec G T) : Sec.res g (Sec.res f z) = Sec.res (g ≫ f) z := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem main : ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → ∀ (P : PSh) (t : P ⟶ yoneda.obj U) (Q : ι → PSh) (a : ∀ i, Q i ⟶ P) (b : ∀ i, Q i ⟶ yoneda.obj (V i)), (∀ i, IsPullback (a i) (b i) t (yoneda.map (j i))) → Nonempty (IsColimit (Cofan.mk ((free R).obj P) (fun i ↦ (free R).map (a i)))) := by
  intro R _ U ι V j hc P t Q a b hpb
  obtain ⟨ho, -, hdis⟩ := pieces j hc
  have FH := fun (P' : PSh) (G : Shv R) => GlobalTheory.T.freeEtaleModuleSheaf_hom_equiv_natural_sections R P' G
  let y : ∀ T : Scheme.{0}, P.obj (op T) → (T ⟶ U) := fun T x => t.app (op T) x
  have hy : ∀ (T T' : Scheme.{0}) (g : T' ⟶ T) (x : P.obj (op T)), y T' (P.map g.op x) = g ≫ y T x :=
    fun T T' g x => NatTrans.naturality_apply t g.op x
  have hw : ∀ i (W : Scheme.{0}) (q0 : (Q i).obj (op W)), y W ((a i).app _ q0) = ((b i).app _ q0 : W ⟶ V i) ≫ j i :=
    fun i W q0 => ConcreteCategory.congr_hom (congr_app (hpb i).w (op W)) q0
  have hcol : ∀ (T : Scheme.{0}) (x : P.obj (op T)), IsColimit (Cofan.mk T (fun i => pullback.fst (y T x) (j i))) :=
    fun T x => (pullback_isColimit j hc (y T x)).some
  have SC := fun (G : Shv R) (T : Scheme.{0}) (x : P.obj (op T)) => GlobalTheory.T.etaleModuleSheaf_sections_coprod_bijective R G T ι _ _ (hcol T x)
  have hex : ∀ i (W : Scheme.{0}) (x : P.obj (op W)) (σ : W ⟶ V i), y W x = σ ≫ j i →
      ∃ q : (Q i).obj (op W), (a i).app _ q = x ∧ (b i).app _ q = σ := fun i W x σ h =>
    Types.exists_of_isPullback ((hpb i).map ((evaluation _ _).obj (op W))) x σ h
  have huq : ∀ i (W : Scheme.{0}) (q q' : (Q i).obj (op W)), (a i).app _ q = (a i).app _ q' →
      (b i).app _ q = (b i).app _ q' → q = q' := fun i W q q' h1 h2 =>
    Types.ext_of_isPullback ((hpb i).map ((evaluation _ _).obj (op W))) h1 h2
  have hq : ∀ (T : Scheme.{0}) (x : P.obj (op T)) i, ∃ q : (Q i).obj (op (pullback (y T x) (j i))),
      (a i).app _ q = P.map (pullback.fst (y T x) (j i)).op x ∧ (b i).app _ q = pullback.snd (y T x) (j i) :=
    fun T x i => hex i _ _ _ (by rw [hy]; exact pullback.condition)
  choose q hqa hqb using hq
  have key : ∀ (G : Shv R) (m : (free R).obj P ⟶ G) T x i,
      Sec.res (pullback.fst (y T x) (j i)) (val m T x) = val ((free R).map (a i) ≫ m) _ (q T x i) := by
    intro G m T x i
    rw [(FH P G).2.2.2.1 (Q i) (a i) m, hqa, (FH P G).2.2.1 m]
  let φ : ∀ (G : Shv R) (c : ∀ i, (free R).obj (Q i) ⟶ G) (T : Scheme.{0}), P.obj (op T) → Sec G T :=
    fun G c T x => Function.surjInv (SC G T x).2 (fun i => val (c i) _ (q T x i))
  have hφ : ∀ G c T x i, Sec.res (pullback.fst (y T x) (j i)) (φ G c T x) = val (c i) _ (q T x i) :=
    fun G c T x i => congrFun (Function.surjInv_eq (SC G T x).2 _) i
  have nat : ∀ G c (T' T : Scheme.{0}) (g : T' ⟶ T) (x : P.obj (op T)),
      φ G c T' (P.map g.op x) = Sec.res g (φ G c T x) := by
    intro G c T' T g x
    apply (SC G T' (P.map g.op x)).1
    refine funext fun i => ?_
    dsimp only
    rw [hφ, res_res]
    have hw2 : (pullback.fst (y T' (P.map g.op x)) (j i) ≫ g) ≫ y T x = pullback.snd _ (j i) ≫ j i := by
      rw [Category.assoc, ← hy, pullback.condition]
    have h1 : pullback.lift _ _ hw2 ≫ pullback.fst (y T x) (j i) = pullback.fst (y T' (P.map g.op x)) (j i) ≫ g :=
      pullback.lift_fst _ _ _
    have h2 : pullback.lift _ _ hw2 ≫ pullback.snd (y T x) (j i) = pullback.snd (y T' (P.map g.op x)) (j i) :=
      pullback.lift_snd _ _ _
    rw [← h1, ← res_res, hφ, ← (FH (Q i) G).2.2.1 (c i)]
    congr 1
    apply huq
    · rw [hqa, NatTrans.naturality_apply, hqa, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
        ← op_comp, ← op_comp, h1]
    · rw [hqb, NatTrans.naturality_apply, hqb]
      exact h2.symm
  let d : ∀ s : Cofan (fun i => (free R).obj (Q i)), (free R).obj P ⟶ s.pt := fun s =>
    ((FH P s.pt).2.1 (φ s.pt s.inj) (fun T' T g x => nat s.pt s.inj T' T g x)).choose
  have hd : ∀ s T x, val (d s) T x = φ s.pt s.inj T x := fun s =>
    ((FH P s.pt).2.1 (φ s.pt s.inj) (fun T' T g x => nat s.pt s.inj T' T g x)).choose_spec
  refine ⟨mkCofanColimit _ d ?_ ?_⟩
  · intro s i
    change (free R).map (a i) ≫ d s = s.inj i
    apply (FH (Q i) s.pt).1
    intro W q0
    rw [(FH P s.pt).2.2.2.1 (Q i) (a i), hd]
    obtain ⟨x, hx⟩ : ∃ x, x = (a i).app (op W) q0 := ⟨_, rfl⟩
    have hwx : y W x = ((b i).app _ q0 : W ⟶ V i) ≫ j i := hx ▸ hw i W q0
    rw [← hx]
    apply (SC s.pt W x).1
    refine funext fun k => ?_
    dsimp only
    rw [hφ, ← (FH (Q i) s.pt).2.2.1]
    by_cases hki : k = i
    · subst hki
      congr 1
      apply huq
      · rw [hqa, NatTrans.naturality_apply, ← hx]
      · rw [hqb, NatTrans.naturality_apply]
        change _ = pullback.fst (y W x) (j k) ≫ ((b k).app _ q0 : W ⟶ V k)
        haveI := ho k
        rw [← cancel_mono (j k), Category.assoc, ← pullback.condition, hwx]
    · haveI : IsEmpty ((pullback (y W x) (j k) : Scheme.{0}) : Type) := by
        refine ⟨fun z => hki (hdis k i (pullback.snd (y W x) (j k) z)
          ((pullback.fst (y W x) (j k) ≫ ((b i).app _ q0 : W ⟶ V i)) z) ?_)⟩
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← pullback.condition, Category.assoc, ← hwx]
      exact (sec_subsingleton_of_isEmpty s.pt _).elim _ _
  · intro s m hm
    have hm' : ∀ i, (free R).map (a i) ≫ m = s.inj i := hm
    apply (FH P s.pt).1
    intro T x
    rw [hd]
    apply (SC s.pt T x).1
    refine funext fun i => ?_
    dsimp only
    rw [hφ, key, hm']

end GlobalTheory.EtC.FreeCofan
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
theorem _root_.GlobalTheory.T.alexanderWhitney_cup_leibniz_etale : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k) (γ₁ γ₂ : Cochain ((chains R).obj E) K (k + 1)), μ.IsAW hk α β γ → μ.IsAW (by omega) (δ n (n + 1) α) β γ₁ → μ.IsAW (by omega) α (δ m (m + 1) β) γ₂ → δ k (k + 1) γ = γ₁ + n.negOnePow • γ₂ := by
  first | exact @GlobalTheory.EtC.aw_leibniz_rule | exact GlobalTheory.EtC.aw_leibniz_rule | (intros; apply GlobalTheory.EtC.aw_leibniz_rule <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem Pair.cup_spec_full : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k), (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m), ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧ ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ :=
  fun _ _ _ _ _ μ E _ _ _ hk => ⟨fun α β => μ.aw_exists E hk α β, fun α β γ h => μ.cup_spec E hk α β γ h⟩

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections : ∀ (R : Type) [CommRing R] {F G : Shv R} (φ : F ⟶ G), (Mono φ ↔ ∀ U, Function.Injective (Sec.map φ (U := U))) ∧ (Mono φ ↔ ∀ U (a : Sec F U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0) ∧ (Epi φ ↔ ∀ U (b : Sec G U), Loc U fun V g => ∃ a : Sec F V, Sec.map φ a = Sec.res g b) ∧ (∀ ψ : F ⟶ G, (∀ U (a : Sec F U), Sec.map φ a = Sec.map ψ a) → φ = ψ) := by
  first | (exact @GlobalTheory.EtC.mono_epi_sections) | (exact GlobalTheory.EtC.mono_epi_sections) | (intros; apply GlobalTheory.EtC.mono_epi_sections  <;> assumption)
end
