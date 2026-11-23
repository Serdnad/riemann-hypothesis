module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantEigenbasisTangentArc
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BetaAtAddLeftAndDiagEqTwoOrder
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisation
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle124
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle123
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle041
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEqSmulOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle047
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle043
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle121
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle079
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle005
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

noncomputable section

namespace GlobalTheory.PeriodLaws

section Valued

open Formalism.MainNotions.DIV.Cons

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem norm_le_one_of_integral {x : C} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨q, hq, hqx⟩ := hx
  have hx0 : 0 < ‖x‖ := one_pos.trans h
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hq.coeff_natDegree, map_one, one_mul] at hqx
  have h1 : ‖∑ i ∈ Finset.range q.natDegree, algebraMap ℤ C (q.coeff i) * x ^ i‖ < ‖x‖ ^ q.natDegree := by
    rcases Finset.eq_empty_or_nonempty (Finset.range q.natDegree) with he | he
    · rw [he]; simpa using pow_pos hx0 _
    · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty he
        (fun i => algebraMap ℤ C (q.coeff i) * x ^ i)
      refine hle.trans_lt ?_
      rw [norm_mul, norm_pow]
      refine (mul_le_of_le_one_left (by positivity) (IsUltrametricDist.norm_intCast_le_one C _)).trans_lt ?_
      exact pow_lt_pow_right₀ h (Finset.mem_range.1 hi)
  rw [eq_neg_of_add_eq_zero_left hqx, norm_neg, norm_pow] at h1
  exact lt_irrefl _ h1

theorem dvd_of_norm_le {a b : intO C} (ha : a ≠ 0) (h : ‖(b : C)‖ ≤ ‖(a : C)‖) : a ∣ b := by
  have ha' : (a : C) ≠ 0 := fun e => ha (Subtype.ext e)
  refine ⟨⟨(b : C) / a, ?_⟩, Subtype.ext ?_⟩
  · change ‖(b : C) / a‖ ≤ 1
    rw [norm_div]
    exact div_le_one_of_le₀ h (norm_nonneg _)
  · change (b : C) = a * (b / a)
    field_simp

theorem isFractionRing_intO : IsFractionRing (intO C) C := by
  refine IsFractionRing.of_field _ _ fun z => ?_
  by_cases h : ‖z‖ ≤ 1
  · exact ⟨⟨z, h⟩, 1, by rw [map_one, div_one]; rfl⟩
  · push_neg at h
    refine ⟨1, ⟨z⁻¹, ?_⟩, by rw [map_one, one_div]; exact (inv_inv z).symm⟩
    change ‖z⁻¹‖ ≤ 1
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ h.le

end Valued

section Geometry

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre GlobalTheory.EigenSplit GlobalTheory.LieEigen Matrix
open Formalism.MainNotions.DIV.Cons GlobalTheory.ToricRank
open scoped CategoryTheory.Obj


open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out in
theorem finrank_le_of_lieMult_valued {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {D : DegData R (maximalIdeal R)} {P : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D P G) {O : Type} [CommRing O] [IsDomain O] [StarRing O] [Module.Finite ℤ O]
    [Module O D.toPre.X] {oD : D.OAct O} {oP : P.OAct O} {aG : OAct O G} (hl : U.OLinear O oD oP aG.toRingAct)
    {F : Type} [NormedField F] [IsUltrametricDist F] (f : R →+* intO F)
    (hf : ∀ a ∈ maximalIdeal R, ‖((f a : intO F) : F)‖ < 1) {τ : O →+* F}
    (hτ : Function.Injective τ) {N : ℕ} (hN : LieMult aG (spMap ((intO F).subtype.comp f)) τ N) :
    Module.finrank O D.toPre.X ≤ N := by
  classical
  have := U.smooth
  obtain ⟨g, v, hv⟩ := Chart.exists_isLieBasis G U.smooth
  obtain ⟨ρ, hρ⟩ := exists_action hv aG
  obtain ⟨v', ρ', hv', hρ', hM⟩ := exists_action_pullback hv hρ ((intO F).subtype.comp f)
  have hk := isLinearPullback_pullback aG (spMap ((intO F).subtype.comp f))
  rw [← finrank_of_lieMult hk.1 hv' hk.2 hρ' hN]
  let V := intO F
  have : IsFractionRing V F := isFractionRing_intO
  let : Algebra R V := f.toAlgebra
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ1 : ‖((f π : intO F) : F)‖ < 1 := hf π hπ.not_isUnit
  let τV : O →+* V := τ.codRestrict V fun a =>
    norm_le_one_of_integral (map_isIntegral_int τ (Algebra.IsIntegral.isIntegral a))
  let b := Module.finBasis ℤ D.toPre.X
  have : Module.Finite O D.toPre.X := .of_restrictScalars_finite ℤ _ _
  obtain ⟨φ⟩ := ConstBasis.nonempty_basis_eigenHom (X := D.toPre.X) (τ.comp (starRingEnd O))
    (hτ.comp star_injective)
  refine le_finrank_eigenSub (V := V) π (fun h => ?_) (fun c hc => ?_) τV
    (fun a => (LinearMap.toMatrix' (ρ a))ᵀ) ρ' hM star b (fun k => (φ k).1)
    (φ.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _))
    (fun k a x => ((φ k).2 _ x).trans (congrArg (τ · * _) (star_star a))) fun n => ?_
  · obtain ⟨w, hw⟩ := h.exists_right_inv
    have h₁ : ‖((f π : intO F) : F)‖ * ‖(w : F)‖ = 1 := by
      rw [← norm_mul]
      exact (congrArg (fun z : V => ‖(z : F)‖) hw).trans norm_one
    have h₂ : ‖(w : F)‖ ≤ 1 := w.2
    exact ((mul_le_of_le_one_right (norm_nonneg _) h₂).trans_lt hπ1).ne' h₁.symm
  · have hc' : 0 < ‖(c : F)‖ := norm_pos_iff.2 fun e => hc (Subtype.ext e)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hc' hπ1
    exact ⟨n, dvd_of_norm_le hc ((norm_pow _ n).trans_le hn.le)⟩
  · obtain ⟨C, D', hCD, hC⟩ := exists_matrix_level U hl hv hρ b n
    refine ⟨C, D', hCD, fun a k j => Ideal.mem_span_singleton.1 ?_⟩
    rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq]
    exact hC a k j

end Geometry

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rank_le_of_dvr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C} (A : DatAt Y P) [IsDiscreteValuationRing A.R] :
    ∃ ρ : ℕ, Module.finrank ℤ A.Ylat = 2 * (Module.finrank ℚ E / 2) * ρ ∧ ρ ≤ Dw.p ∧ ρ ≤ Dw.q := by
  let := H.starRing
  let F : Type := ↥C.S
  obtain ⟨b, hb⟩ := Spec.map_surjective (P.y ≫ pullback.fst _ _ ≫ Xo.s)
  have hdet := (Y.oF.geom F P.y b.hom hb.symm).1
  have key : ∀ (τ : 𝓞 E →+* F) (n : ℕ), Function.Injective τ → LieMult Y.oF.t.act P.y τ n →
      Module.finrank (𝓞 E) A.U.D.toPre.X ≤ n := fun τ n hτ hn => by
    refine finrank_le_of_lieMult_valued A.U.U.toUnifPre A.U.lin A.f A.f_loc hτ ?_
    rw [LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ Y.m.cart Y.m.act] at hn
    rw [LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ A.m.cart A.m.act]
    have e : spMap ((intO F).subtype.comp A.f) ≫ A.ι = P.y ≫ Y.jQ ≫ pullback.fst _ _ := by
      refine Eq.trans ?_ P.ext
      rw [← A.fac, ← Category.assoc]
      exact congrArg (· ≫ A.ι) (Spec.map_comp (CommRingCat.ofHom A.f) (CommRingCat.ofHom (intO F).subtype))
    rw [e]
    exact hn
  let τ₀ : 𝓞 E →+* F := (IsAlgClosed.lift (R := ℚ) (S := E) (M := F)).toRingHom.comp (algebraMap _ E)
  have h₀ : Function.Injective τ₀ :=
    (IsAlgClosed.lift (R := ℚ) (S := E) (M := F)).injective.comp RingOfIntegers.coe_injective
  have h₁ : Function.Injective (τ₀.comp H.bar.toRingHom) := h₀.comp H.bar.injective
  have e₁ : τ₀.comp H.bar.toRingHom H.rt = -τ₀ H.rt := by
    rw [← map_neg, ← HostModel.bar_rt]; rfl
  have hsq : τ₀ H.rt ^ 2 = b.hom (baseKA l).ρ ^ 2 := by
    rw [← map_pow, ← map_pow, H.rt_sq, (baseKA l).ρ_sq]; simp
  have hne : -τ₀ H.rt ≠ τ₀ H.rt := fun h => by
    have h2 : τ₀ H.rt ^ 2 = 0 := by rw [neg_eq_self.1 h]; simp
    rw [← map_pow, H.rt_sq] at h2
    exact H.d_prime.ne_zero (by simpa using h2)
  refine ⟨Module.finrank (𝓞 E) A.U.D.toPre.X, ?_, ?_⟩
  · have h1 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h1
    rw [ToricRank.finrank_int_eq E]
    congr 1
    omega
  · rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact ⟨key _ _ h₀ ((hdet _).1 h), key _ _ h₁ ((hdet _).2 (by rw [e₁, ← h]; exact hne))⟩
    · have h' : -τ₀ H.rt = b.hom (baseKA l).ρ := by rw [h, neg_neg]
      exact ⟨key _ _ h₁ ((hdet _).1 (e₁.trans h')), key _ _ h₀ ((hdet _).2 (by rw [← h']; exact hne.symm))⟩

theorem period_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : ℕ) (C : SCF p) (P : PointsOfFlagModel.PtC Y C), p.Prime → ∀ (T : CDVR) (g : T.V →+* intO ↥C.S) (ιT : Sp T.V ⟶ Y.X), T.FinRes → Function.Injective g → (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥C.S) : ↥C.S)‖ < 1) → spMap g ≫ ιT = P.yt → ∀ A : DatAt Y P, (∀ a a' b, A.beta (a + a') b = A.beta a b + A.beta a' b) ∧ (∀ (x : 𝓞 E) a b, A.beta (x • a) b = A.beta a (H.bar x • b)) ∧ (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ A.Ylat), ∀ x : ι → ℝ, x ≠ 0 → 0 < ∑ i, ∑ k, x i * x k * A.beta (b i) (b k)) ∧ ∃ ρ : ℕ, Module.finrank ℤ A.Ylat = 2 * (Module.finrank ℚ E / 2) * ρ ∧ ρ ≤ Dw.p ∧ ρ ≤ Dw.q := by
  intro E _ _ _ H Dw l Xo c O _ β Y p C P hp T g ιT hT hg hloc hfac A
  obtain ⟨A₀, ⟨_, -⟩, -⟩ := GlobalTheory.T.exists_degeneration_data_algebraic_point_model E H Dw l Xo c O β Y p C P hp T g ιT hT hg hloc hfac
  obtain ⟨hψ₀, e, he⟩ := GlobalTheory.T.degenerationData_coords_ne_zero_lattices_isomorphic E H Dw l Xo c O β Y p C P hp T g ιT hT hg hloc hfac A₀ A
  obtain ⟨hψ, -⟩ := GlobalTheory.T.degenerationData_coords_ne_zero_lattices_isomorphic E H Dw l Xo c O β Y p C P hp T g ιT hT hg hloc hfac A A
  let e' : A₀.Ylat ≃ₗ[ℤ] A.Ylat := e.toAddEquiv.toIntLinearEquiv
  refine ⟨(BetaAdd.main A.R A.U.D _ _ p A.normal (fun a => (A.f a).2) hψ).1,
    PeriodBalance.betaAt_balanced E H A.R A.t A.U _ _ p A.normal (fun a => (A.f a).2) hψ, ?_, ?_⟩
  · obtain ⟨ι, _, b, hb⟩ := PeriodFormPos.betaAt_pos A₀.R A₀.U.D _ ((intO ↥C.S).subtype.comp A₀.f) p hp.one_lt
      A₀.f_loc (fun a => (A₀.f a).2) hψ₀
    refine ⟨ι, inferInstance, b.map e', fun x hx => (hb x hx).trans_eq ?_⟩
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    exact congrArg (x i * x k * ·) (he (b i) (b k)).symm
  · rw [← e'.finrank_eq]
    exact rank_le_of_dvr A₀

end GlobalTheory.PeriodLaws
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj
open Formalism.MainNotions Formalism.MainNotions.DIV.Cons

namespace GlobalTheory.ModelIndep

theorem norm_unit_eq_one {V C : Type} [CommRing V] [NormedField C] [IsUltrametricDist C] (f : V →+* intO C) (u : Vˣ) :
    ‖((f u : intO C) : C)‖ = 1 := by
  have h1 : ‖((f u : intO C) : C)‖ ≤ 1 := (f u).2
  have h2 : ‖((f (u⁻¹ : Vˣ) : intO C) : C)‖ ≤ 1 := (f (u⁻¹ : Vˣ)).2
  have h3 : ‖((f u : intO C) : C)‖ * ‖((f (u⁻¹ : Vˣ) : intO C) : C)‖ = 1 := by
    rw [← norm_mul, ← Subring.coe_mul, ← map_mul, Units.mul_inv, map_one, Subring.coe_one, norm_one]
  refine le_antisymm h1 ?_
  nlinarith [norm_nonneg ((f u : intO C) : C)]

theorem norm_eq_of_dvr {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] {p : ℕ}
    (hp : p.Prime) (C C' : SCF p) (f : V →+* intO ↥C.S) (f' : V →+* intO ↥C'.S) (r : V) :
    ‖((f r : intO ↥C.S) : ↥C.S)‖ = ‖((f' r : intO ↥C'.S) : ↥C'.S)‖ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have key : ∀ (C : SCF p) (f : V →+* intO ↥C.S) (n : ℕ) (u : Vˣ),
      ‖((f (u * ϖ ^ n) : intO ↥C.S) : ↥C.S)‖ = ‖((f ϖ : intO ↥C.S) : ↥C.S)‖ ^ n := by
    intro C f n u
    rw [map_mul, map_pow, Subring.coe_mul, Subring.coe_pow, norm_mul, norm_pow, norm_unit_eq_one, one_mul]
  have hp0 : (p : V) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have hpe : ∀ (C : SCF p) (f : V →+* intO ↥C.S), ‖((f ϖ : intO ↥C.S) : ↥C.S)‖ ^ e = (p : ℝ)⁻¹ := by
    intro C f
    rw [← key C f e w, ← hw, map_natCast, ← C.norm_p]
    simp
  have he : e ≠ 0 := by
    rintro rfl
    have h := hpe C f
    rw [pow_zero] at h
    have h2 : (p : ℝ) = 1 := inv_eq_one.1 h.symm
    exact hp.ne_one (by exact_mod_cast h2)
  have hϖ' : ‖((f ϖ : intO ↥C.S) : ↥C.S)‖ = ‖((f' ϖ : intO ↥C'.S) : ↥C'.S)‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) he).1 ((hpe C f).trans (hpe C' f').symm)
  by_cases hr : r = 0
  · subst hr; simp
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  rw [key, key, hϖ']

theorem betaAt_eq_of_dvr {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] {p : ℕ}
    (hp : p.Prime) (C C' : SCF p) (f : V →+* intO ↥C.S) (f' : V →+* intO ↥C'.S) (D : DegPre V) (a b : D.X) :
    betaAt D ((intO ↥C.S).subtype.comp f) p a b = betaAt D ((intO ↥C'.S).subtype.comp f') p a b := by
  have h : ∀ χ, vPsiAt D ((intO ↥C.S).subtype.comp f) p χ = vPsiAt D ((intO ↥C'.S).subtype.comp f') p χ := by
    intro χ
    unfold vPsiAt
    split_ifs with h
    · exact congrArg (fun x => -Real.logb p x) (norm_eq_of_dvr hp C C' f f' h.choose)
    · rfl
  simp only [betaAt, h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_extension {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {la : HeightOneSpectrum (𝓞 c.F)} (hB : PointsOfFlagModel.BaseAt la β) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ)
    (ho : OverLa la T.V io e) (x : Sp T.Fr ⟶ Xo.X)
    (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    {p : ℕ} {C : SCF p} (Pc : PointsOfFlagModel.PtC Y C) (eF : T.Fr →+* ↥C.S) (g : T.V →+* intO ↥C.S)
    (h1' : eF.comp io = Pc.fK) (h2' : Pc.y ≫ pullback.fst _ _ = spMap eF ≫ x)
    (h3' : ∀ a, ((g a : intO ↥C.S) : ↥C.S) = eF (algebraMap T.V T.Fr a)) :
    ∃ yt : Sp T.V ⟶ Y.X, spMap g ≫ yt = Pc.yt ∧ Nonempty (SABMap G Y.t yt) := by
  obtain ⟨b, hb⟩ := GlobalTheory.EtaVal.exists_base_map_of_overLa (fun a => (hB.2 (β a)).1 ⟨a, rfl⟩) T io e ho
  have hcond : x ≫ Xo.s = spMap io ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [hxs, GlobalTheory.EtaVal.spMap_comp_spMap]
  let z : Sp T.Fr ⟶ Xo.XF c := pullback.lift x (spMap io) hcond
  have hzs : z ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
  have hzf : z ≫ pullback.fst _ _ = x := pullback.lift_fst _ _ _
  have hx : z ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b := by
    show z ≫ (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb]
  obtain ⟨yt, h1, h2⟩ := extPt Y T b z hx
  obtain ⟨PP', cub, sym, adj, prim, mP, -⟩ := sabPull Out.CubePf.cubePull yt Y.t
  obtain ⟨mF, -⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Y.oF.t t' (pullback.fst _ _) z Y.m0.toSABMap
    (PullbackSections.sabMapCast m1 hzf.symm)
  obtain ⟨mJ, -⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t t' (Y.jQ ≫ pullback.fst _ _) z Y.m mF
  have hj : z ≫ Y.jQ ≫ pullback.fst _ _ = Out.jK T.V ≫ yt := h1.symm
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t _ t' yt (Out.jK T.V) mP (PullbackSections.sabMapCast mJ hj)
  obtain ⟨-, ψ, -⟩ := GlobalTheory.sab_extensions_iso E H Dw l Xo T.V T.Fr x G _ t' t' m1 m2 m1 mK
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ Y.t _ G yt (𝟙 _) mP ψ
  have hprY : IsProper Y.s := projProper O Y.X Y.s Y.proj
  have hr : (intO ↥C.S).subtype.comp g = eF.comp (algebraMap T.V T.Fr) := RingHom.ext h3'
  have hy : Pc.y = spMap eF ≫ z := by
    apply pullback.hom_ext
    · rw [h2', Category.assoc, hzf]
    · rw [Pc.y_over, Category.assoc, hzs, GlobalTheory.EtaVal.spMap_comp_spMap, h1']
  have halg : g.comp b = Pc.alg := by
    refine RingHom.ext fun a => Subtype.ext ?_
    have q1 := DFunLike.congr_fun Pc.compat a
    have q2 := DFunLike.congr_fun hb a
    have q3 := DFunLike.congr_fun h1' (β a)
    simp only [RingHom.comp_apply] at q1 q2 q3 ⊢
    rw [h3', q2, q3]; exact q1.symm
  refine ⟨yt, ?_, ⟨PullbackSections.sabMapCast n (Category.id_comp yt)⟩⟩
  refine GlobalTheory.EtaVal.point_ext_of_injective (intO ↥C.S).subtype Subtype.val_injective Y.s _ _ ?_ ?_
  · rw [Pc.ext, hy, Category.assoc, ← h1, ← Category.assoc, GlobalTheory.EtaVal.spMap_comp_spMap, hr,
      ← GlobalTheory.EtaVal.spMap_comp_spMap, Category.assoc]
  · rw [Pc.yt_over, Category.assoc, h2, GlobalTheory.EtaVal.spMap_comp_spMap, halg]

theorem exists_equiv_of_uniformisation {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {la : HeightOneSpectrum (𝓞 c.F)} (hB : PointsOfFlagModel.BaseAt la β) (T : CDVR) (hT : T.FinRes) (io : c.F →+* T.Fr) (e : ℕ)
    (ho : OverLa la T.V io e) (x : Sp T.Fr ⟶ Xo.X)
    (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    (T' : CDVR) (φ : T.V →+* T'.V) (hφ : Function.Injective φ) (hφf : φ.Finite) (G' : SAB H (Sp T'.V))
    (mG : SABMap G' G (spMap φ)) (U : PELUnif (maximalIdeal T'.V) G')
    (hU : ∀ χ, PsiUnitOn U.D.toPre χ (abLocus G'.G)) (hTo : U.TorsionIso)
    {p : ℕ} (hp : p.Prime) {C : SCF p} (Pc : PointsOfFlagModel.PtC Y C) (eF : T.Fr →+* ↥C.S)
    (h1' : eF.comp io = Pc.fK) (hle : ∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1)
    (hlt : ∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1)
    (h2' : Pc.y ≫ pullback.fst _ _ = spMap eF ≫ x) (A : DatAt Y Pc) :
    ∃ (f : T'.V →+* intO ↥C.S) (q : U.D.toPre.X ≃ₗ[𝓞 E] A.Ylat),
      ∀ a b, A.beta (q a) (q b) = betaAt U.D.toPre ((intO ↥C.S).subtype.comp f) p a b := by
  let g : T.V →+* intO ↥C.S := (eF.comp (algebraMap T.V T.Fr)).codRestrict _ hle
  have hg : Function.Injective g := fun a b h =>
    IsFractionRing.injective T.V T.Fr (eF.injective (congrArg Subtype.val h))
  obtain ⟨yt, hyt, ⟨n⟩⟩ := exists_extension Y hB T io e ho x hxs G t' m1 m2 Pc eF g h1' h2' (fun _ => rfl)
  have hpm : (p : T.V) ∈ maximalIdeal T.V := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h := norm_unit_eq_one g u
    rw [hu, map_natCast] at h
    have h' : ‖(p : ↥C.S)‖ = 1 := by simpa using h
    rw [C.norm_p] at h'
    exact hp.ne_one (by exact_mod_cast inv_eq_one.1 h')
  obtain ⟨f, hf, -, hfl⟩ := (GlobalTheory.T.exists_embedding_completeAlgClosed_fixedCarrier T p hp hT hpm).2 C g T' φ hg hlt hφ hφf
  obtain ⟨n2, -⟩ := sabComp pullCubComp E H _ _ _ Y.t G G' yt (spMap φ) n mG
  have hab : (spMap φ ≫ yt) ⁻¹' abLocus Y.t.G = abLocus G'.G :=
    Set.ext fun q => abLocus_pullback abLocusOne Y.t.semi n2.cart.1 q
  let A₀ : DatAt Y Pc :=
    { R := T'.V
      noeth := inferInstance
      normal := inferInstance
      complete := inferInstance
      «ι» := spMap φ ≫ yt
      f := f
      f_loc := hfl
      fac := by rw [← Category.assoc, GlobalTheory.EtaVal.spMap_comp_spMap, hf, hyt]
      t := G'
      m := n2
      U := U
      unitOn := fun χ => by rw [hab]; exact hU χ
      tors := hTo }
  obtain ⟨-, q, hq⟩ := GlobalTheory.T.degenerationData_coords_ne_zero_lattices_isomorphic E H Dw l Xo c O β Y p C Pc hp T g yt hT hg hlt hyt A₀ A
  exact ⟨f, q, hq⟩

theorem exists_equiv_two_models {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
    (Y : Model Xo c β) (Y' : Model Xo c β') {la : HeightOneSpectrum (𝓞 c.F)} (hB : PointsOfFlagModel.BaseAt la β)
    (hB' : PointsOfFlagModel.BaseAt la β') (T : CDVR) (hT : T.FinRes) (io : c.F →+* T.Fr) (e : ℕ)
    (ho : OverLa la T.V io e) (x : Sp T.Fr ⟶ Xo.X)
    (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    {p : ℕ} (hp : p.Prime) {C C' : SCF p} (P : PointsOfFlagModel.PtC Y C) (P' : PointsOfFlagModel.PtC Y' C')
    (eF : T.Fr →+* ↥C.S) (a1 : eF.comp io = P.fK) (a2 : ∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1)
    (a3 : ∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1)
    (a4 : P.y ≫ pullback.fst _ _ = spMap eF ≫ x)
    (eF' : T.Fr →+* ↥C'.S) (b1 : eF'.comp io = P'.fK) (b2 : ∀ a : T.V, ‖eF' (algebraMap T.V T.Fr a)‖ ≤ 1)
    (b3 : ∀ a ∈ maximalIdeal T.V, ‖eF' (algebraMap T.V T.Fr a)‖ < 1)
    (b4 : P'.y ≫ pullback.fst _ _ = spMap eF' ≫ x) (A : DatAt Y P) (A' : DatAt Y' P') :
    ∃ f : A.Ylat ≃ₗ[𝓞 E] A'.Ylat, ∀ a b, A'.beta (f a) (f b) = A.beta a b := by
  obtain ⟨T', φ, G', mG, hφ, hφf, -, -, U, hU, hTo⟩ :=
    GlobalTheory.UnifAfterExt.exists_finite_ext_uniformised E H Dw l Xo T G t' m2 x m1 hT
  obtain ⟨f, q, hq⟩ := exists_equiv_of_uniformisation Y hB T hT io e ho x hxs G t' m1 m2
    T' φ hφ hφf G' mG U hU hTo hp P eF a1 a2 a3 a4 A
  obtain ⟨f', q', hq'⟩ := exists_equiv_of_uniformisation Y' hB' T hT io e ho x hxs G t' m1 m2
    T' φ hφ hφf G' mG U hU hTo hp P' eF' b1 b2 b3 b4 A'
  refine ⟨q.symm.trans q', fun a b => ?_⟩
  have h1 := hq (q.symm a) (q.symm b)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
  exact (hq' (q.symm a) (q.symm b)).trans ((betaAt_eq_of_dvr hp _ _ f' f _ _ _).trans h1.symm)

theorem datIndep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), DatIndep Xo c := by
  intro E _ _ _ H Dw l Xo c la Tw Tw' hTw hTw' T io e y ho hy z z' hz hz' A A'
  letI := io.toAlgebra
  obtain ⟨y, hy1, G, t', m1, m2, hy2⟩ := y
  obtain ⟨v, C, P, Fl⟩ := z
  obtain ⟨v', C', P', Fl'⟩ := z'
  obtain ⟨hv, eF, a1, a2, a3, a4, -⟩ := hz
  obtain ⟨hv', eF', b1, b2, b3, b4, -⟩ := hz'
  obtain rfl : v = lamOf la := hv
  obtain rfl : v' = lamOf la := hv'
  exact exists_equiv_two_models (Tw.Y (lamOf la)) (Tw'.Y (lamOf la)) (hTw.1 (lamOf la)).1 (hTw'.1 (lamOf la)).1 T hy
    io e ho y.x y.x_over G t' m1 m2 (resCh_prime la) P P' eF a1 a2 a3 a4 eF' b1 b2 b3 b4 A A'

end GlobalTheory.ModelIndep
end
