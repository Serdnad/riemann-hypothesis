module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle003
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle023
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ChartCoordinatesHasSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle024
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.ArcQ

theorem tsum_mem_range_of_norm_cut (T : CDVR) {K : Type} [NormedField K] [CompleteSpace K] (i' : T.Fr →+* K)
    (hn : ∀ x : T.Fr, ‖i' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V T.Fr)) (t : T.V)
    (ht : ‖i' (algebraMap T.V T.Fr t)‖ < 1) (a : ℕ → T.V) :
    ∃ L : T.V, i' (algebraMap T.V T.Fr L) =
      ∑' k : ℕ, i' (algebraMap T.V T.Fr (a k)) * i' (algebraMap T.V T.Fr t) ^ k := by
  set φ : T.V →+* K := i'.comp (algebraMap T.V T.Fr) with hφ
  have hle : ∀ v : T.V, ‖φ v‖ ≤ 1 := fun v => (hn _).2 ⟨v, rfl⟩
  change ‖φ t‖ < 1 at ht
  change ∃ L : T.V, φ L = ∑' k : ℕ, φ (a k) * φ t ^ k
  have htm : t ∈ IsLocalRing.maximalIdeal T.V := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, rfl⟩
    have h1 : ‖φ u‖ * ‖φ (u⁻¹ : T.Vˣ)‖ = 1 := by
      rw [← norm_mul, ← map_mul]; simp
    have h2 := hle (u⁻¹ : T.Vˣ)
    nlinarith [norm_nonneg (φ u), norm_nonneg (φ (u⁻¹ : T.Vˣ))]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hπ0 : algebraMap T.V T.Fr π ≠ 0 := by
    simpa using hπ.ne_zero
  have hπn : ‖φ π‖ < 1 := by
    by_contra hc
    push_neg at hc
    have h1 : ‖i' (algebraMap T.V T.Fr π)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hc
    obtain ⟨v, hv⟩ := (hn _).1 h1
    apply hπ.not_isUnit
    refine IsUnit.of_mul_eq_one v ?_
    apply IsFractionRing.injective T.V T.Fr
    rw [map_mul, hv, map_one, mul_inv_cancel₀ hπ0]
  have hpow : ∀ (n : ℕ) (x : T.V), x ∈ IsLocalRing.maximalIdeal T.V ^ n → ‖φ x‖ ≤ ‖φ π‖ ^ n := by
    intro n x hx
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hx
    obtain ⟨b, rfl⟩ := hx
    rw [map_mul, norm_mul, map_pow, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hle b)
  let S : ℕ → T.V := fun n => ∑ k ∈ Finset.range n, a k * t ^ k
  have hS : ∀ {m n : ℕ}, m ≤ n →
      S m ≡ S n [SMOD (IsLocalRing.maximalIdeal T.V ^ m • ⊤ : Submodule T.V T.V)] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
    simp only [S]
    rw [← Finset.sum_Ico_eq_sub _ hmn]
    refine Ideal.sum_mem _ fun k hk => Ideal.mul_mem_left _ _ ?_
    exact Ideal.pow_le_pow_right (Finset.mem_Ico.1 hk).1 (Ideal.pow_mem_pow htm k)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := IsLocalRing.maximalIdeal T.V) (M := T.V) inferInstance hS
  refine ⟨L, ?_⟩
  have hsum : Summable fun k : ℕ => φ (a k) * φ t ^ k := by
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) ht) fun k => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hle _)
  have h1 := hsum.hasSum.tendsto_sum_nat
  have h2 : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, φ (a k) * φ t ^ k) Filter.atTop (nhds (φ L)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hπn)
    have h3 := hL n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h3
    have h4 := hpow n _ h3

    simpa [S, map_sub, map_sum] using h4
  exact tendsto_nhds_unique h2 h1

theorem exists_factor_of_mem_range {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* C) (g : B →+* C)
    (hg : Function.Injective g) (h : ∀ a, ∃ b, g b = f a) : ∃ e : A →+* B, g.comp e = f := by
  choose e he using h
  refine ⟨{ toFun := e, map_one' := hg ?_, map_mul' := fun x y => hg ?_, map_zero' := hg ?_,
            map_add' := fun x y => hg ?_ }, RingHom.ext he⟩ <;> simp [he]

theorem eval_factors_through_cdvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv T' : CDVR) (ϖ : Tv.V) (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (ιT : Tv.Fr →+* K) (j : Tv.V →+* T'.V) (i' : T'.Fr →+* K), ϖ ≠ 0 → (∀ v, i' (algebraMap T'.V T'.Fr (j v)) = ιT (algebraMap Tv.V Tv.Fr v)) → (∀ x : T'.Fr, ‖i' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T'.V T'.Fr)) → ∀ (t : T'.V) (Y : ArcLt Dw → T'.V) (ev : ArcSR Dw Tv.V ϖ →+* K), ‖i' (algebraMap T'.V T'.Fr t)‖ < 1 → (∀ p : PowerSeries Tv.V, ev (arcιR Dw Tv.V ϖ p) = ∑' k : ℕ, ιT (algebraMap Tv.V Tv.Fr (PowerSeries.coeff k p)) * i' (algebraMap T'.V T'.Fr t) ^ k) → (∀ x, ev (arcXR Dw Tv.V ϖ x) = i' (algebraMap T'.V T'.Fr (Y x))) → ∃ (e₀ : PowerSeries Tv.V →+* T'.V) (e₁ : ArcSR Dw Tv.V ϖ →+* T'.Fr), e₀.comp (PowerSeries.C (R := Tv.V)) = j ∧ e₁.comp (arcιR Dw Tv.V ϖ) = (algebraMap T'.V T'.Fr).comp e₀ ∧ (∀ x, e₁ (arcXR Dw Tv.V ϖ x) = algebraMap T'.V T'.Fr (Y x)) ∧ i'.comp e₁ = ev := by
  intro E _ _ _ H Dw Tv T' ϖ K _ _ _ ιT j i' _ hj hn t Y ev ht hp hX
  have hinj : Function.Injective (i'.comp (algebraMap T'.V T'.Fr)) :=
    i'.injective.comp (IsFractionRing.injective T'.V T'.Fr)
  have h0 : ∀ p : PowerSeries Tv.V,
      ∃ b, (i'.comp (algebraMap T'.V T'.Fr)) b = (ev.comp (arcιR Dw Tv.V ϖ)) p := by
    intro p
    obtain ⟨L, hL⟩ := tsum_mem_range_of_norm_cut T' i' hn t ht (fun k => j (PowerSeries.coeff k p))
    refine ⟨L, ?_⟩
    simp only [RingHom.comp_apply]
    rw [hL, hp]
    simp only [hj]
  obtain ⟨e₀, he₀⟩ := exists_factor_of_mem_range _ _ hinj h0
  have hpoly : ∀ a : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V),
      ev (algebraMap _ (ArcSR Dw Tv.V ϖ) a) ∈ i'.fieldRange := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C p =>
      obtain ⟨b, hb⟩ := h0 p
      exact ⟨_, hb⟩
    | add p q hp' hq' => rw [map_add (f := _), map_add (f := _)]; exact add_mem hp' hq'
    | mul_X p x hp' =>
      rw [map_mul (algebraMap _ (ArcSR Dw Tv.V ϖ)) p, map_mul ev]
      exact mul_mem hp' ⟨_, (hX x).symm⟩
  have h1 : ∀ z : ArcSR Dw Tv.V ϖ, ∃ b, i' b = ev z := by
    intro z
    obtain ⟨⟨a, s⟩, hz⟩ := IsLocalization.surj
      (Submonoid.powers (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw Tv.V)) z
    have hu := (IsLocalization.map_units (ArcSR Dw Tv.V ϖ) s).map ev
    have hz' := congrArg ev hz
    rw [map_mul ev] at hz'
    have : ev z ∈ i'.fieldRange := by
      rw [eq_div_of_mul_eq hu.ne_zero hz']
      exact div_mem (hpoly _) (hpoly _)
    exact this
  obtain ⟨e₁, he₁⟩ := exists_factor_of_mem_range _ _ i'.injective h1
  refine ⟨e₀, e₁, ?_, ?_, fun x => ?_, he₁⟩
  · refine RingHom.ext fun v => hinj ?_
    have h2 := RingHom.congr_fun he₀ (PowerSeries.C v)
    simp only [RingHom.comp_apply] at h2 ⊢
    rw [h2, hp, tsum_eq_single 0, hj]
    · simp
    · intro k hk
      simp [PowerSeries.coeff_C, hk]
  · refine RingHom.ext fun p => i'.injective ?_
    have h2 := RingHom.congr_fun he₀ p
    have h3 := RingHom.congr_fun he₁ (arcιR Dw Tv.V ϖ p)
    simp only [RingHom.comp_apply] at h2 h3 ⊢
    rw [h2, h3]
  · apply i'.injective
    rw [← hX x]
    exact RingHom.congr_fun he₁ _

end GlobalTheory.ArcQ
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ

theorem nonempty_unfWit_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U → Nonempty (UnfWit U) := by
  intro E _ _ _ H Dw l Xo c σ r U h
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hiso, hP⟩ := h
  choose Pm h1 h2 h3 h4 h5 using hP
  exact ⟨⟨g, e, F, ik, φ, hiso, Pm, h1, h2, fun k x => ⟨h3 k x, h4 k x⟩, h5⟩⟩

end GlobalTheory.ArcQ
end

section

noncomputable section

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FreeQuotientRank Formalism.L2.Pj Formalism.L2.Pj.QAt

section Norm

variable {V F C : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F]
  [Algebra V F] [IsFractionRing V F] [NormedField C] (f : F →+* C)
  (hf : ∀ v : V, ‖f (algebraMap V F v)‖ ≤ 1)

include hf

omit [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V F] in
theorem norm_map_unit_eq_one (u : Vˣ) : ‖f (algebraMap V F u)‖ = 1 := by
  have h : ‖f (algebraMap V F u)‖ * ‖f (algebraMap V F (u⁻¹ : Vˣ))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
  exact le_antisymm (hf _) (h.ge.trans (mul_le_of_le_one_right (norm_nonneg _) (hf _)))

theorem norm_map_eq_zpow_vV {π : V} (hπ : Irreducible π) {x : F} (hx : x ≠ 0) :
    ‖f x‖ = ‖f (algebraMap V F π)‖ ^ vV V x := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hx
  have hv : vV V (u • algebraMap V F π ^ n) = n := by
    rw [vV, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀,
      PlaceCompletion.valV_algebraMap_of_isUnit u.isUnit,
      PlaceCompletion.valV_algebraMap_of_irreducible hπ, one_mul, ← WithZero.exp_zsmul,
      WithZero.log_exp]
    simp
  rw [hv, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, norm_mul, norm_zpow,
    norm_map_unit_eq_one f hf, one_mul]

theorem norm_map_le_one_iff {π : V} (hπ : Irreducible π) (h1 : ‖f (algebraMap V F π)‖ < 1) (x : F) :
    ‖f x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V F) := by
  refine ⟨fun h => ?_, by rintro ⟨v, rfl⟩; exact hf v⟩
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have h0 : 0 < ‖f (algebraMap V F π)‖ := norm_pos_iff.2 ((map_ne_zero f).2
    ((map_ne_zero_iff _ (IsFractionRing.injective V F)).2 hπ.ne_zero))
  rw [norm_map_eq_zpow_vV f hf hπ hx, zpow_le_one_iff_right_of_lt_one₀ h0 h1] at h
  refine PlaceCompletion.exists_algebraMap_eq_of_valV_le_one ?_
  rw [← WithZero.exp_log (valV_ne_zero (V := V) hx), ← WithZero.exp_zero, WithZero.exp_le_exp]
  rw [vV] at h
  omega

end Norm


open DiscEval in
theorem exists_finSite_siteAlg :
    ∀ (K₁ : Type) [Field K₁] [NumberField K₁] (w : HeightOneSpectrum (𝓞 K₁)),
      (∃ (Tv : CDVR) (io : K₁ →+* Tv.Fr), Tv.FinRes ∧ OverLa w Tv.V io 1) ∧
      ∀ (Tv : CDVR) (io : K₁ →+* Tv.Fr) (e : ℕ), Tv.FinRes → OverLa w Tv.V io e →
        ∃ (Z : FinSite K₁ w) (ιT : Tv.Fr →+* Z.K), ιT.comp io = Z.ι ∧
          (∀ x : Tv.Fr, ‖ιT x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap Tv.V Tv.Fr)) ∧ SiteAlg Z Tv ιT := by
  intro K₁ _ _ w
  refine ⟨?_, fun Tv io e hfin ho => ?_⟩
  · obtain ⟨T, io, h1, h2, -⟩ := PlaceCompletion.exists_initial_completion K₁ w
    exact ⟨T, io, h2, h1⟩
  haveI : Finite (IsLocalRing.ResidueField Tv.V) := hfin
  obtain ⟨p, _, _, _⟩ := exists_padicInt_algebra_finite Tv.V
  obtain ⟨i, hinj, hi⟩ := exists_injective_norm_le_one (p := p) Tv.V
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  let ιT : Tv.Fr →+* ℂ_[p] := IsFractionRing.lift hinj
  have hι : ∀ v, ιT (algebraMap Tv.V Tv.Fr v) = i v := fun v => IsFractionRing.lift_algebraMap hinj v
  have hf : ∀ v, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1 := fun v => by rw [hι]; exact hi v
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible Tv.V
  have h0 : 0 < ‖i π‖ := norm_pos_iff.2 ((map_ne_zero_iff i hinj).2 hπ.ne_zero)
  have h1 : ‖i π‖ < 1 :=
    (hi π).lt_of_ne fun h => hπ.not_isUnit ((norm_map_eq_one_iff i hi hinj π).1 h)
  let Z : FinSite K₁ w :=
    { K := ℂ_[p]
      ι := ιT.comp io
      r := ‖i π‖ ^ e
      r_pos := pow_pos h0 e
      r_lt := pow_lt_one₀ h0.le h1 ho.1.ne'
      norm_ι := fun x hx => by
        rw [RingHom.comp_apply, norm_map_eq_zpow_vV ιT hf hπ ((map_ne_zero io).2 hx), hι, ho.2 x,
          zpow_mul, zpow_natCast]
        rfl
      K₀ := algField p
      res := residueFieldInfiniteOn_algField p
      S := algDisc p
      S_disc := fun _ ht => ht.2
      S_dense := algDisc_dense p
      S_units := mul_mem_algDisc p }
  refine ⟨Z, ιT, rfl, norm_map_le_one_iff ιT hf hπ (by rw [hι]; exact h1), ?_⟩
  intro (s : Finset ℂ_[p]) hs
  have hsK : (s : Set ℂ_[p]) ⊆ algField p := fun x hx => (hs x hx).1.elim id fun h => h.1
  haveI := finiteDimensional_genField i hi s.finite_toSet
  set L := genField i (s : Set ℂ_[p])
  haveI : CharZero (integralClosure ℤ_[p] L) := RingHom.charZero (intEmb L)
  let T' : CDVR := { V := integralClosure ℤ_[p] L, cpl := isAdicComplete_integralClosure L }
  obtain ⟨j, hj⟩ := exists_comp_eq_of_mem_range _ (intEmb_injective L) i fun a =>
    (mem_range_intEmb_iff _ _).2 ⟨map_mem_genField i hi hsK a, hi a⟩
  let i' : FractionRing (integralClosure ℤ_[p] L) →+* ℂ_[p] := IsFractionRing.lift (intEmb_injective L)
  have hi' : ∀ v, i' (algebraMap _ _ v) = intEmb L v := fun v =>
    IsFractionRing.lift_algebraMap (intEmb_injective L) v
  obtain ⟨π', hπ'⟩ := IsDiscreteValuationRing.exists_irreducible (integralClosure ℤ_[p] L)
  refine ⟨T', j, i', finite_residueField_integralClosure L, isLocalHom_of_intEmb_eq i hi L hinj hj,
    fun v => (hi' _).trans ((hj v).trans (hι v).symm),
    norm_map_le_one_iff i' (fun v => by rw [hi']; exact norm_intEmb_le_one L v) hπ' (by
      rw [hi', ← mem_maximalIdeal_iff_norm]
      exact hπ'.not_isUnit), fun x hx => ?_⟩
  obtain ⟨v, hv⟩ := (mem_range_intEmb_iff L x).2 ⟨mem_genField_of_mem i hi hsK hx, (hs x hx).2⟩
  exact ⟨v, (hi' v).trans hv⟩

end GlobalTheory.ArcQ
end
end

section

namespace GlobalTheory.LetterEval

open GlobalTheory.DiscEval

section General

variable {K : Type} [NormedField K] [CompleteSpace K] {V F : Type} [CommRing V] [Field F]
  (a : V →+* F) (ι : F →+* K) (hi : ∀ v, ‖(ι.comp a) v‖ ≤ 1) {ϖ : V} (hϖ : a ϖ ≠ 0)
  {t : K} (ht0 : t ≠ 0) (ht : ‖t‖ < 1)


include hϖ ht0 in
theorem hasSum_laurent_of_mul_eq {q : LaurentSeries F} {g : PowerSeries V} {N : ℕ}
    (h : q * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (R := F) (a ϖ) * PowerSeries.X)) ^ N =
      HahnSeries.ofPowerSeries ℤ F (PowerSeries.map a g)) :
    HasSum (fun k : ℤ => ι (q.coeff k) * t ^ k)
      (((ι (a ϖ) * t) ^ N)⁻¹ * discEval (ι.comp a) hi ht g) := by
  have h2 : (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (R := F) (a ϖ) * PowerSeries.X)) ^ N =
      HahnSeries.single (N : ℤ) (a ϖ ^ N) := by
    rw [← map_pow, mul_pow, ← map_pow PowerSeries.C, map_mul, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_X_pow, HahnSeries.C_apply, HahnSeries.single_mul_single]
    simp
  have h4 : a ϖ ^ N ≠ 0 := pow_ne_zero _ hϖ
  have hc : ∀ n : ℤ, q.coeff n = if n + N < 0 then 0 else
      (a ϖ ^ N)⁻¹ * a (PowerSeries.coeff (n + N).natAbs g) := fun n => by
    have h3 := congrArg (fun g : LaurentSeries F => g.coeff (n + N)) h
    simp only [h2, HahnSeries.coeff_mul_single_add] at h3
    rw [PowerSeries.coeff_coe, PowerSeries.coeff_map] at h3
    split_ifs at h3 ⊢
    · exact (mul_eq_zero.1 h3).resolve_right h4
    · rw [← h3]
      field_simp
  have hinj : Function.Injective fun k : ℕ => (k : ℤ) - N := fun k l hkl => by simpa using hkl
  rw [← hinj.hasSum_iff]
  · refine Eq.mpr (congrArg (HasSum · _) (funext fun k => ?_))
      ((hasSum_discEval (ι.comp a) hi ht g).mul_left (((ι (a ϖ) * t) ^ N)⁻¹))
    rw [Function.comp_apply, hc, sub_add_cancel, if_neg (by omega), Int.natAbs_natCast,
      zpow_sub₀ ht0, zpow_natCast, zpow_natCast, map_mul, map_inv₀, map_pow, RingHom.comp_apply,
      mul_pow, mul_inv]
    ring
  · intro n hn
    rw [hc, if_pos, map_zero, zero_mul]
    by_contra h0
    exact hn ⟨(n + N).toNat, by simp only; omega⟩


include hϖ ht0 in
theorem hasSum_lcoeffPoly {σ : Type} (Y : σ → K) {P : MvPolynomial σ (LaurentSeries F)}
    {G : MvPolynomial σ (PowerSeries V)} {N : ℕ}
    (h : P * MvPolynomial.C
        (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (R := F) (a ϖ) * PowerSeries.X)) ^ N =
      MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ F).comp (PowerSeries.map a)) G) :
    HasSum (fun k : ℤ => MvPolynomial.eval Y (MvPolynomial.map ι (GlobalTheory.ArcQ.lcoeffPoly P k)) * t ^ k)
      (((ι (a ϖ) * t) ^ N)⁻¹ * MvPolynomial.eval₂ (discEval (ι.comp a) hi ht) Y G) := by
  classical
  have hμ : ∀ μ, P.coeff μ *
      (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (R := F) (a ϖ) * PowerSeries.X)) ^ N =
      HahnSeries.ofPowerSeries ℤ F (PowerSeries.map a (G.coeff μ)) := fun μ => by
    have := congrArg (AddMonoidAlgebra.coeff · μ) h
    rwa [← map_pow, mul_comm, MvPolynomial.coeff_C_mul, mul_comm, MvPolynomial.coeff_map] at this
  set s := P.support ∪ G.support
  have hP : ∀ k : ℤ, GlobalTheory.ArcQ.lcoeffPoly P k =
      ∑ μ ∈ s, MvPolynomial.monomial μ ((P.coeff μ).coeff k) := fun k =>
    Finset.sum_subset Finset.subset_union_left fun μ _ hμ => by
      simp [MvPolynomial.notMem_support_iff.1 hμ]
  have hG : MvPolynomial.eval₂ (discEval (ι.comp a) hi ht) Y G =
      ∑ μ ∈ s, discEval (ι.comp a) hi ht (G.coeff μ) * ∏ k ∈ μ.support, Y k ^ μ k := by
    rw [MvPolynomial.eval₂_eq]
    exact Finset.sum_subset Finset.subset_union_right fun μ _ hμ => by
      simp [MvPolynomial.notMem_support_iff.1 hμ]
  rw [hG, Finset.mul_sum]
  simp_rw [← mul_assoc]
  refine Eq.mpr (congrArg (HasSum · _) (funext fun m => ?_))
    (hasSum_sum fun μ (_ : μ ∈ s) =>
      (hasSum_laurent_of_mul_eq a ι hi hϖ ht0 ht (hμ μ)).mul_right (∏ k ∈ μ.support, Y k ^ μ k))

  rw [hP, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.map_monomial, MvPolynomial.eval_monomial, Finsupp.prod]
  ring

end General

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem exists_eval : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv : CDVR) (ϖ : Tv.V) (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (ιT : Tv.Fr →+* K), ϖ ≠ 0 → (∀ v : Tv.V, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1) → ∀ (t : K) (Y : ArcLt Dw → K), 0 < ‖t‖ → ‖t‖ < 1 → (∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => Y ⟨τ, i, k⟩).det) ≠ 0 → ∃ ev : ArcSR Dw Tv.V ϖ →+* K, (∀ p : PowerSeries Tv.V, ev (arcιR Dw Tv.V ϖ p) = ∑' k : ℕ, ιT (algebraMap Tv.V Tv.Fr (PowerSeries.coeff k p)) * t ^ k) ∧ (∀ x, ev (arcXR Dw Tv.V ϖ x) = Y x) ∧ ∀ (f : ArcSR Dw Tv.V ϖ) (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)) (P : MvPolynomial (ArcLt Dw) (LaurentSeries Tv.Fr)), f * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw Tv.V ϖ) G → P * MvPolynomial.C (HahnSeries.ofPowerSeries ℤ Tv.Fr (PowerSeries.C (R := Tv.Fr) (algebraMap Tv.V Tv.Fr ϖ) * PowerSeries.X)) ^ N = MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr))) G → Filter.Tendsto (fun k : ℤ => ‖MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k‖) Filter.cofinite (nhds 0) ∧ ev f = ∑' k : ℤ, MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k := by
  intro E _ _ _ H Dw Tv ϖ K _ _ _ ιT hϖ hi t Y ht0 ht hY
  have ht0' : t ≠ 0 := norm_pos_iff.1 ht0
  have hϖ' : algebraMap Tv.V Tv.Fr ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Tv.V Tv.Fr)).2 hϖ
  have hϖ'' : ιT (algebraMap Tv.V Tv.Fr ϖ) ≠ 0 := (map_ne_zero ιT).2 hϖ'
  have hi' : ∀ v, ‖(ιT.comp (algebraMap Tv.V Tv.Fr)) v‖ ≤ 1 := hi
  let g : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V) →+* K :=
    MvPolynomial.eval₂Hom (discEval _ hi' ht) Y
  have hgC : ∀ p, g (MvPolynomial.C p) = discEval _ hi' ht p := fun p =>
    MvPolynomial.eval₂Hom_C _ _ _
  have hgX : ∀ x, g (MvPolynomial.X x) = Y x := fun x => MvPolynomial.eval₂Hom_X' _ _ _
  have hϖX : discEval _ hi' ht (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) =
      ιT (algebraMap Tv.V Tv.Fr ϖ) * t := by
    rw [map_mul, discEval_C, discEval_X, RingHom.comp_apply]
  have hu : IsUnit (g (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw Tv.V)) := by
    rw [isUnit_iff_ne_zero, map_mul, hgC, hϖX]
    refine mul_ne_zero (mul_ne_zero hϖ'' ht0') ?_
    convert hY using 1
    rw [arcDetR, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext i k
    exact hgX _
  let ev : ArcSR Dw Tv.V ϖ →+* K := IsLocalization.Away.lift _ hu
  have hev : ∀ G, ev (algebraMap _ (ArcSR Dw Tv.V ϖ) G) = g G := fun G =>
    IsLocalization.Away.lift_eq _ hu G
  have hevι : ∀ p, ev (arcιR Dw Tv.V ϖ p) = discEval _ hi' ht p := fun p =>
    (hev _).trans (hgC p)
  refine ⟨ev, fun p => ?_, fun x => (hev _).trans (hgX x), fun f N G P hf hP => ?_⟩
  · rw [hevι, ← (hasSum_discEval _ hi' ht p).tsum_eq]
    rfl
  · have hs := hasSum_lcoeffPoly _ ιT hi' hϖ' ht0' ht Y hP
    refine ⟨by simpa using hs.summable.tendsto_cofinite_zero.norm, ?_⟩
    rw [hs.tsum_eq]
    have h1 := congrArg ev hf
    rw [map_mul, map_pow, hevι, hϖX, hev] at h1
    have h2 : (ιT (algebraMap Tv.V Tv.Fr ϖ) * t) ^ N ≠ 0 := pow_ne_zero _ (mul_ne_zero hϖ'' ht0')
    rw [eq_inv_mul_iff_mul_eq₀ h2, mul_comm]
    exact h1

end GlobalTheory.LetterEval
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.exp_eq_of_isometry_matching_markings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (P P' : (Fu.Di i).La →+ (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (inferInstance : StarRing (𝓞 E)) = H.starRing → IsPeriod (Fu.Di i) ty P → IsPeriod (Fu.Di i) ty P' → (∀ u v, (Fu.Di i).EF (gam u) (gam v) = (Fu.Di i).EF u v) → (∀ v ∈ idealPart D l, ∃ e, gam (Fu.t i v) = Fu.t i v + l.M • e) → (∀ v, ∃ e, gam (Fu.t i v) = Fu.t i v + l.A • e) → (∀ u, P' (gam u) = h (P u)) → Fu.u i P = Fu.u i P' ∧ ∀ z, (Fu.ex i P' (h z)).left = (Fu.ex i P z).left := by
  first | exact @GlobalTheory.ArcPts.exp_eq_of_matching_markings | exact GlobalTheory.ArcPts.exp_eq_of_matching_markings | (intros; apply GlobalTheory.ArcPts.exp_eq_of_matching_markings <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

theorem _root_.GlobalTheory.T.isTangent_genericFibre_of_thetaSections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (A : AnArc (𝓞 E)) (t : SAB H (Sp ℂ⟦X⟧)) (Φ : GenPts A t gen) (L : RigLB t.G) (x : A.V → (Sp ℂ⟦X⟧ ⟶ t.G.left)) (τ : A.V → L.L.ι → ℂ⟦X⟧) (z : A.V) (v : Sp (DualNumber ℂ⟦X⟧) ⟶ t.G.left) (k₀ : L.L.ι) (τ₁ : DualNumber ℂ⟦X⟧) (ρ : DualNumber ℂ⟦X⟧ →+* DualNumber ℂ⸨X⸩) (νK : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t.G.hom gen), L = t.PP → (∀ u, (Φ.x u).left = gen ≫ x u ∧ ∀ (k : L.L.ι) (k' : t.PP.L.ι), HEq k k' → ⊤ ≤ x u ⁻¹ᵁ L.L.U k → Φ.τ u k' = algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (τ u k)) → spMap (TrivSqZeroExt.fstHom ℂ⟦X⟧ ℂ⟦X⟧ ℂ⟦X⟧).toRingHom ≫ v = x 0 → ⊤ ≤ v ⁻¹ᵁ L.L.U k₀ → IsUnit τ₁ → (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (algebraMap ℂ⟦X⟧ ℂ⸨X⸩ r)) → ρ DualNumber.eps = DualNumber.eps → νK ≫ pullback.fst _ _ = spMap ρ ≫ v → νK ≫ pullback.snd _ _ = spMap (algebraMap ℂ⸨X⸩ (DualNumber ℂ⸨X⸩)) → (∀ (j : ℕ) [NeZero j] (α : A.X), ∀ th ∈ A.Theta j α, ∀ F, IsDFSum A j α th z F → ∃ (m : ℕ) (σ : Out.H0 L.L j), (∀ u k, ⊤ ≤ x u ⁻¹ᵁ L.L.U k → algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (valR (x u) (LB.wchart L.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k)) (σ.f (fun _ => k))) = HahnSeries.single (m : ℤ) (1 : ℂ) * A.FSum j α th u * algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (τ u k) ^ j) ∧ ρ (valR v (LB.wchart L.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k₀)) (σ.f (fun _ => k₀))) = TrivSqZeroExt.inl (HahnSeries.single (m : ℤ) (1 : ℂ)) * (TrivSqZeroExt.inl (A.FSum j α th 0) + TrivSqZeroExt.inr F) * ρ τ₁ ^ j) → Φ.IsTan z νK := by
  first | exact @GlobalTheory.GenericTan.isTan_of_sections | exact GlobalTheory.GenericTan.isTan_of_sections | (intros; apply GlobalTheory.GenericTan.isTan_of_sections <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.holArc_chart_coordinates_hasSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) [Algebra c.F ℂ⸨X⸩] (p : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (φ : p.R →ₐ[c.F] ℂ⸨X⸩), (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → IsOpenImmersion j → j ≫ pullback.snd _ _ = spMap (algebraMap c.F p.R) → spMap φ.toRingHom ≫ j ≫ Y.j = spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∃ ψ : p.R →ₐ[c.F] CAt σ, spMap ψ.toRingHom ≫ j ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) ∧ ∀ f : p.R, HasSum (fun m : ℤ => (φ f).coeff m * eTwoPi w ^ m) (toC (ψ f)) := by
  first | exact @GlobalTheory.ArcPoint.chart_coordinates_hasSum | exact GlobalTheory.ArcPoint.chart_coordinates_hasSum | (intros; apply GlobalTheory.ArcPoint.chart_coordinates_hasSum <;> assumption)
end

section

alias GlobalTheory.T.degenerationData_baseChanges_exist_pid := GlobalTheory.ArcQBC.baseChanges
end
