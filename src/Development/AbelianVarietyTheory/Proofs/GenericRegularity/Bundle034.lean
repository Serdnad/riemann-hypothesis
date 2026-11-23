module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle240
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankOfIsSecBasis
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsOfH0EqOneClosedFields
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle061
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueScaledBaseChangeFibreSection
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle056
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle044
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle048
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.GenSectT
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Valuation.LocalSubring
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
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem exists_valuationSubring_comap_eq_nonunits {K L : Type} [Field K] [Field L] (f : K →+* L)
    (U : ValuationSubring K) :
    ∃ W : ValuationSubring L, W.comap f = U ∧ ∀ x ∈ U.nonunits, f x ∈ W.nonunits := by
  classical
  obtain ⟨W, hW, hloc⟩ := IsLocalRing.exists_factor_valuationRing (f.comp U.subtype)
  refine ⟨W, ?_, ?_⟩
  · ext x
    rw [ValuationSubring.mem_comap]
    constructor
    · intro hx
      by_contra hxU
      have hx0 : x ≠ 0 := fun h => hxU (h ▸ U.zero_mem)
      have hinv : x⁻¹ ∈ U := (U.mem_or_inv_mem x).resolve_left hxU
      have hnu : ¬ IsUnit (⟨x⁻¹, hinv⟩ : U) := by
        intro hu
        obtain ⟨⟨y, hy⟩, hyx⟩ := isUnit_iff_exists_inv.mp hu
        have hyx' : x⁻¹ * y = 1 := congrArg Subtype.val hyx
        have : y = x := by
          calc y = x * (x⁻¹ * y) := by rw [← _root_.mul_assoc, mul_inv_cancel₀ hx0, _root_.one_mul]
            _ = x := by rw [hyx', _root_.mul_one]
        exact hxU (this ▸ hy)
      apply hnu
      apply (hloc.map_nonunit (⟨x⁻¹, hinv⟩ : U))
      refine isUnit_iff_exists_inv.mpr ⟨⟨f x, hx⟩, ?_⟩
      apply Subtype.ext
      change f x⁻¹ * f x = 1
      rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    · intro hx
      exact hW ⟨x, hx⟩
  · intro x hx
    obtain ⟨hxU, hmax⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mp hx
    have hfx : f x ∈ W := hW ⟨x, hxU⟩
    have key : (⟨f x, hfx⟩ : W) ∈ IsLocalRing.maximalIdeal W := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      apply (IsLocalRing.mem_maximalIdeal _).mp hmax
      exact hloc.map_nonunit (⟨x, hxU⟩ : U) hu
    exact (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mpr ⟨hfx, key⟩

theorem exists_prime_natCast_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ la.asIdeal := by
  apply GlobalTheory.Mem.FewPrimes.exists_prime_mem <;> assumption

theorem modelAt_of_good_level : PartI → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (Xo : ∀ l : Level H, Moduli Dw l) (l : Level H) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)), (∀ p : ℕ, p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p) → ModelAt (Xo l) c la := by
  intro hI E _ _ _ H Dw hpq Xo l c la hgood
  obtain ⟨-, hI⟩ := hI
  obtain ⟨Y, hY, -⟩ := hI E H Dw hpq Xo
  unfold ModelAt
  obtain ⟨p, hp, hpla⟩ := exists_prime_natCast_mem la
  obtain ⟨W, hcomap, hnon⟩ :=
    exists_valuationSubring_comap_eq_nonunits c.F.val.toRingHom (la.valuation c.F).valuationSubring
  have hlt : la.valuation c.F (p : c.F) < 1 := by
    have h := (la.valuation_lt_one_iff_mem (K := c.F) (p : 𝓞 c.F)).mpr hpla
    exact_mod_cast h
  have hp0 : (p : c.F) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpU : (p : c.F) ∈ (la.valuation c.F).valuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    intro hinv
    rw [Valuation.mem_valuationSubring_iff, map_inv₀] at hinv
    have hpos : 0 < la.valuation c.F (p : c.F) :=
      zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hp0)
    exact absurd ((inv_le_one₀ hpos).mp hinv) (not_le.mpr hlt)
  have hW : (p : ℂ) ∈ W.nonunits := by
    have h := hnon _ hpU
    rwa [map_natCast] at h
  let i : Idx H p := ⟨l, c, hgood p hp hpla⟩
  rw [← hcomap]
  exact ⟨Y p W hp hW i, ((hY p W hp hW).1.1 i).2.2.1⟩

end GlobalTheory.Reg
end

section

noncomputable section

namespace GlobalTheory.CurveRecord

open Formalism.L2.Pj NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

theorem finite_reduced_of_eq {K Ω Kl K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K'] [Algebra K Kl]
    [Algebra Kl K'] [Algebra K K'] [IsScalarTower K Kl K'] [CharZero K] {Dd m : ℕ}
    (hfg : (⊤ : IntermediateField K Ω).FG) (htr : Algebra.trdeg K Ω = Dd)
    (v : Fin m → Ω) (k₀ : Fin m) (hv₀ : v k₀ ≠ 0)
    (hbig : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun k => v k / v k₀)) = Dd)
    (t : Fin (Dd + 1) × Fin m → K') (ht : AlgebraicIndependent K t)
    (a : Fin (Dd + 1) → K' ⊗[Kl] (Kl ⊗[K] Ω)) (ha : ∀ i, a i = ∑ k, t (i, k) ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] v k)) :
    FiniteDimensional K' (Localization.Away (a 0) ⧸ Ideal.span (Set.range fun i : Fin Dd =>
        algebraMap _ (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0))) ∧
      IsReduced (Localization.Away (a 0) ⧸ Ideal.span (Set.range fun i : Fin Dd =>
        algebraMap _ (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0))) := by
  have e : a = GenSect.tsec K Kl t v := funext fun i => ha i
  subst e
  have := GenSect.s1T (Kl := Kl) hfg htr v k₀ hv₀ hbig t ht
  unfold GenSect.tJ at this
  exact this



theorem tv_indep {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) [Algebra B.KO (Kp X la N)]
    [IsScalarTower B.KO (X.Kl la) (Kp X la N)] :
    AlgebraicIndependent B.KO (fun p : Idx D j N => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p)) := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom (X.Ol la) (Pol X la N) (Op X la N)) :=
    IsLocalization.injective (Op X la N) (Ideal.primeCompl_le_nonZeroDivisors (gI X la N))
  have h0 := (MvPolynomial.algebraicIndependent_X (Idx D j N) (X.Ol la)).map' hinj
  have h1 := h0.map' (f := IsScalarTower.toAlgHom (X.Ol la) (Op X la N) (Kp X la N))
    (IsFractionRing.injective (Op X la N) (Kp X la N))
  have : Algebra.IsAlgebraic (X.Ol la) (X.Kl la) := IsLocalization.isAlgebraic _ (nonZeroDivisors (X.Ol la))
  have h2 := (Algebra.IsAlgebraic.algebraicIndependent_iff (X.Ol la) (X.Kl la)).mp h1
  have h3 := h2.restrictScalars (R := B.KO) (algebraMap B.KO (X.Kl la)).injective
  have hfun : (fun p : Idx D j N => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p)) =
      ⇑(IsScalarTower.toAlgHom (X.Ol la) (Op X la N) (Kp X la N)) ∘
        (⇑(IsScalarTower.toAlgHom (X.Ol la) (Pol X la N) (Op X la N)) ∘ MvPolynomial.X) := by
    funext p
    rw [Function.comp_apply, Function.comp_apply, IsScalarTower.toAlgHom_apply, IsScalarTower.toAlgHom_apply, Tv]
  rw [hfun]
  exact h3

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) {wL : WeightFamilies.Wt D j}
  (w : Fin N → B.Cusp j wL)

theorem rzMap_sec_eq (i : Fin (WeightFamilies.dimY D j + 1)) :
    rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i) =
      ∑ k, @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N (i, k)) ⊗ₜ[X.Kl la]
        ((1 : X.Kl la) ⊗ₜ[B.KO] gF (X.inc wL (w k))) := by

  rw [Formalism.MainNotions.Gaps.EtaleWeightGaps.sec, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, rzMap_emb, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem map_Jid_eq : Ideal.map (phiZ X la N Ω gF w) (Jid X la w) =
    Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i.succ)) *
        IsLocalization.Away.invSelf (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))) := by
  have key : ∀ {R : Type} [CommRing R] {a b c : R}, a * b = 1 → a * c = 1 → b = c :=
    fun {_} _ {_} {b} {c} h1 h2 => by linear_combination c * h1 - b * h2
  rw [Jid, Ideal.map_span, ← Set.range_comp]
  refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
  show phiZ X la N Ω gF w (sfr X la w i.succ) = _
  rw [phiZ_apply, coe_sfr, frac_apply, pow_one, map_mul, lwZ_alg]
  congr 1
  have h1 := congrArg (lwZ X la N Ω gF w) (section_mul_inverse_eq_one X la w)
  rw [map_mul, lwZ_alg, map_one] at h1
  exact key h1 (IsLocalization.Away.mul_invSelf _)

theorem finite_reduced_record
    (hfg : (⊤ : IntermediateField B.KO Ω).FG) (htr : Algebra.trdeg B.KO Ω = WeightFamilies.dimY D j)
    (v : Fin N → Ω) (hv : ∀ k, gF (X.inc wL (w k)) = v k) (k₀ : Fin N) (hv₀ : v k₀ ≠ 0)
    (hbig : Algebra.trdeg B.KO (IntermediateField.adjoin B.KO (Set.range fun k => v k / v k₀)) =
      WeightFamilies.dimY D j) :
    FiniteDimensional (Kp X la N) (RZs X la N Ω gF w ⧸ Ideal.map (phiZ X la N Ω gF w) (Jid X la w)) ∧
      IsReduced (RZs X la N Ω gF w ⧸ Ideal.map (phiZ X la N Ω gF w) (Jid X la w)) := by
  let iK : Algebra B.KO (Kp X la N) :=
    ((algebraMap (X.Kl la) (Kp X la N)).comp (algebraMap B.KO (X.Kl la))).toAlgebra
  have : IsScalarTower B.KO (X.Kl la) (Kp X la N) := IsScalarTower.of_algebraMap_eq' rfl
  rw [map_Jid_eq]
  exact finite_reduced_of_eq hfg htr v k₀ hv₀ hbig _ (tv_indep X la N)
    (fun i => rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i)) (fun i => by rw [rzMap_sec_eq]; simp only [hv])

end Rec

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)




theorem finite_reduced_section (hfg : FnFG (T.Q.Xo j) T.Q.c) (htr : FnTrdeg (T.Q.Xo j) T.Q.c (WeightFamilies.dimY D j)) :
    ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 → ∀ Z,
      FiniteDimensional (Kp (recPlus h j hj) la G.N)
          (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
            Ideal.map (phiI h j hj hG hT la G Z) (Jid (recPlus h j hj) la G.w)) ∧
        IsReduced (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
          Ideal.map (phiI h j hj hG hT la G Z) (Jid (recPlus h j hj) la G.w)) := by
  intro ka wL wF G S g0 la hH Z
  obtain ⟨-, ⟨-, hB2⟩, -, -⟩ := hH
  obtain ⟨k₀, hk₀, htrZ⟩ := hB2 Z
  exact finite_reduced_record (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w (hfg Z) (htr Z)
    (fun k => evC hG Z ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j))
    (fun k => formsEvR_single j hG hT Z _ _) k₀ hk₀ htrZ

end GlobalTheory.CurveRecord
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.Frames

namespace GlobalTheory.LocalFrame

theorem secBaseChange_of_secTwist (hT : Out.SecTwistSt) : Out.SecBaseChangeSt := by
  refine (GlobalTheory.AbLaw.AllLaws.laws_of_h0_eq_one fun K _ _ P => ?_).1.secBaseChange
  obtain ⟨b, hb⟩ := GlobalTheory.PowBasis.exists_basis_pow hT P 1 le_rfl K (𝟙 _)
  have : Nontrivial Γ((Over.mk (𝟙 (Spec (CommRingCat.of K)))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  exact (GlobalTheory.SecTwist.finrank_of_isSecBasis P.A P.L _ _ b hb).trans (one_pow _)

theorem exists_away_isDomain {R : Type} [CommRing R] [IsNoetherianRing R] (q : Ideal R) [q.IsPrime]
    [IsDomain (Localization.AtPrime q)] : ∃ g ∉ q, IsDomain (Localization.Away g) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (RingHom.ker (algebraMap R (Localization.AtPrime q))))
  have h1 : ∀ a : s, ∃ m : q.primeCompl, (m : R) * a = 0 := fun a =>
    (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) (a : R)).1
      (by rw [← RingHom.mem_ker, ← hs]; exact Submodule.subset_span a.2)
  choose m hm using h1
  let g : q.primeCompl := ∏ a, m a
  have hg : ∀ a ∈ RingHom.ker (algebraMap R (Localization.AtPrime q)), (g : R) * a = 0 := by
    intro a ha
    rw [← hs] at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨r, hr⟩ : (m ⟨a, ha⟩ : R) ∣ (g : R) := by
        obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ ⟨a, ha⟩)
        exact ⟨b, congrArg (fun x : q.primeCompl => (x : R)) hb⟩
      rw [hr, mul_right_comm, hm ⟨a, ha⟩, zero_mul]
    | zero => exact mul_zero _
    | add a b _ _ ha hb => rw [mul_add, ha, hb, add_zero]
    | smul r a _ ha => rw [smul_eq_mul, mul_left_comm, ha, mul_zero]
  refine ⟨g, g.2, ?_⟩
  have hu : IsUnit (algebraMap R (Localization.AtPrime q) g) := IsLocalization.map_units _ g
  let f : Localization.Away (g : R) →+* Localization.AtPrime q := IsLocalization.Away.lift (g : R) hu
  refine Function.Injective.isDomain f ((injective_iff_map_eq_zero f).2 fun x hx => ?_)
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (g : R) x
  have h2 : algebraMap R (Localization.AtPrime q) a = 0 := by
    rw [← IsLocalization.Away.lift_eq (S := Localization.Away (g : R)) (g : R) hu a, ← ha, map_mul]
    exact (congrArg (· * _) hx).trans (zero_mul _)
  have hu' : IsUnit (algebraMap R (Localization.Away (g : R)) g) := IsLocalization.Away.algebraMap_isUnit _
  have h3 : algebraMap R (Localization.Away (g : R)) a = 0 := by
    rw [← hu'.mul_right_eq_zero, ← map_mul, hg a h2, map_zero]
  rw [h3] at ha
  exact (hu'.pow n).mul_left_eq_zero.1 ha

theorem isTypeFn_fst {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : IsTypeFn H Dw.p Dw.q (fun j => (e j).1) := by
  intro τ
  have hcard : Nat.card {i // (e i).1 = τ} = Dw.mult τ := by
    have e2 : {i // (e i).1 = τ} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ} :=
      e.subtypeEquiv (fun _ => Iff.rfl)
    have e3 : {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ} ≃ Fin (Dw.mult τ) := Equiv.sigmaSubtype τ
    rw [Nat.card_congr (e2.trans e3), Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine hcard.trans ?_
    unfold Datum.mult
    rw [if_pos h]
  · refine hcard.trans ?_
    unfold Datum.mult
    rw [if_neg h]

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem dualMap_comp_epsMul {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (dualMap ψ) := by
  ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem isEigAt_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (ψ : S →+* T) (hψ : ∀ a, ψ (algebraMap c.F S a) = algebraMap c.F T a) (τ : E →+* ℂ)
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsEigAt c τ v) :
    IsEigAt c τ (spMap (dualMap ψ) ≫ v) := by
  intro a
  rw [Category.assoc, hv a, ← Category.assoc, spMap_spMap, dualMap_comp_epsMul, ← spMap_spMap,
    Category.assoc, hψ]

theorem smooth_of_chart {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {R : Type} [CommRing R] [Algebra c.F R] (j : Sp R ⟶ Xo.XF c)
    [IsOpenImmersion j] (hs : j ≫ pullback.snd _ _ = spMap (algebraMap c.F R)) : Algebra.Smooth c.F R := by
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have h : Smooth (spMap (algebraMap c.F R)) := by rw [← hs]; infer_instance
  have h' := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 h
  exact RingHom.smooth_algebraMap.1 h'

theorem exists_integral_chart_frame : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ p : Xo.XF c, ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : Algebra c.F A) (j : Sp A ⟶ Xo.XF c) (y : FrPt Xo c A), IsOpenImmersion j ∧ p ∈ Set.range j ∧ j ≫ pullback.snd _ _ = spMap (algebraMap c.F A) ∧ Algebra.Smooth c.F A ∧ y.x = j ≫ pullback.fst _ _ := by
  intro hT E _ _ _ H Dw l Xo c z
  classical
  have hS := secBaseChange_of_secTwist hT
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))).symm
  obtain ⟨R, _, _, jR, o, v, th, hft, hred, hjR, ⟨q, hq⟩, hs, ⟨m⟩, hv, hev, hth, -⟩ :=
    GlobalTheory.ModuliChart.exists_chart_eigenframe hS E H Dw l Xo c _ _ (isTypeFn_fst Dw e) z
  let x : Sp R ⟶ Xo.X := jR ≫ pullback.fst _ _
  have hb : TanBasis x (fun i => (v i).left ≫ m.cm.F) :=
    ((GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo R x o.t.G m.cm.F m.cart).2 _ v).1 hv
  let u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left) :=
    fun τ i => (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F
  have heig : ∀ τ i, IsEigAt c τ (u τ i) := by
    intro τ i a
    have h := hev (e.symm ⟨τ, i⟩) a
    simp only [Equiv.apply_symm_apply] at h
    have h' : (v (e.symm ⟨τ, i⟩)).left ≫ (o.t.act.act a).left =
      spMap (epsMul (algebraMap c.F R (embK c τ a))) ≫ (v (e.symm ⟨τ, i⟩)).left := h
    show ((v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F) ≫ _ = _ ≫ (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F
    rw [Category.assoc, ← m.act a, ← Category.assoc, h', Category.assoc]
  obtain ⟨s, hsn⟩ := GlobalTheory.SecTransport.exists_sec_nonzero E H Dw l Xo R x o.t m.toSABMap th hth
  have hsm : Algebra.Smooth c.F R := smooth_of_chart jR hs
  have hreg : IsRegularRing R := GlobalTheory.isRegularRing_of_smooth c.F R
  have hq' : q.asIdeal.IsPrime := q.isPrime
  have hdom : IsDomain (Localization.AtPrime q.asIdeal) := GlobalTheory.isDomain_of_isRegularLocalRing _
  obtain ⟨g, hg, hA⟩ := exists_away_isDomain q.asIdeal
  let A := Localization.Away g
  let ψ : R →+* A := algebraMap R A
  have hψ : ∀ a, ψ (algebraMap c.F R a) = algebraMap c.F A a := fun a =>
    (IsScalarTower.algebraMap_apply c.F R A a).symm
  have hopen : IsOpenImmersion (spMap ψ) := inferInstanceAs
    (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))))
  have hsA : (spMap ψ ≫ jR) ≫ pullback.snd _ _ = spMap (algebraMap c.F A) := by
    rw [Category.assoc, hs, spMap_spMap]
  let x' : Sp A ⟶ Xo.X := spMap ψ ≫ x
  let u' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber A) ⟶ Xo.univ.t.G.left) :=
    fun τ i => spMap (dualMap ψ) ≫ u τ i
  have hbA := GlobalTheory.Frames.tanBasis_baseChange E H Dw l Xo R A ψ x _ _ hb
  have htan : ∀ τ i, IsTanAt x' (u' τ i) := fun τ i => hbA.1 _
  have heig' : ∀ τ i, IsEigAt c τ (u' τ i) := fun τ i => isEigAt_pull ψ hψ τ (heig τ i)
  have hb' : TanBasis x' (fun j => u' (e j).1 (e j).2) := by
    have : (fun j => u' (e j).1 (e j).2) = fun i => spMap (dualMap ψ) ≫ (v i).left ≫ m.cm.F := by
      funext j
      show _ ≫ (v (e.symm (e j))).left ≫ m.cm.F = _
      rw [Equiv.symm_apply_apply]
    rw [this]; exact hbA
  have hbasis := (GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c A x' u' _ e htan heig').2 hb'
  obtain ⟨s', hs', -⟩ := GlobalTheory.Frames.SecPull.existsUnique_secBC E H Dw l Xo R A ψ 1 x x' rfl s
  have hgen := GlobalTheory.FrameGenerator.secGen_of_secNZ_baseChange hS E H Dw l Xo R x s hsn A ψ x' s' rfl hs'
  have hx : x' ≫ Xo.s = sOf c A := by
    have h1 : x' ≫ Xo.s =
        ((spMap ψ ≫ jR) ≫ pullback.snd _ _) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
      simp only [x', x, Category.assoc]
      rw [pullback.condition]
    rw [h1, hsA, sOf, spMap_spMap]
  refine ⟨A, inferInstance, hA, inferInstance, spMap ψ ≫ jR, ⟨x', hx, u', htan, heig', hbasis, s', hgen⟩,
    inferInstance, ?_, hsA, smooth_of_chart _ hsA, (Category.assoc _ _ _).symm⟩
  have hr : q ∈ Set.range (PrimeSpectrum.comap ψ) := by
    rw [PrimeSpectrum.localization_away_comap_range A g]
    exact hg
  obtain ⟨q', hq''⟩ := hr
  refine ⟨q', ?_⟩
  exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg jR hq'').trans hq)

end GlobalTheory.LocalFrame
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD CompSplitPfB

namespace GlobalTheory.Reg.GenericFrameDensity

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}


theorem lact_mem_dom (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact γ x ∈ X.dom := by
  have h2 : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  show ∀ τ : X.Ψ, (mat (lact γ x) τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (lact γ x) τ i).re
  intro τ
  refine ⟨?_, fun i => by rw [dmin_lact X hγ]; exact (h2 τ).2 i⟩
  show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ).det ≠ 0
  rw [Matrix.det_mul]
  refine mul_ne_zero ?_ (h2 τ).1
  have e : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det :=
    (RingHom.map_det τ.1 _).symm
  rw [e]
  exact (map_ne_zero τ.1).2 (Matrix.GeneralLinearGroup.det_ne_zero γ)

end Gen

end GlobalTheory.Reg.GenericFrameDensity
end
end
