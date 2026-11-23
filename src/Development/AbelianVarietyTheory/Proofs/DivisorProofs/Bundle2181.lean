module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeDegreeGrowthChowFormIntegrality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2071
public import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuAllData
public import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open AlgebraicGeometry Filter GlobalTheory.Twist GlobalTheory.Points

namespace GlobalTheory.SecGrowth

section Ratio

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

def ratioSub (ev : V →ₗ[K] Ω) : Subfield Ω where
  carrier := {r | ∃ (e : ℕ) (h : Ω), h ∈ ((LinearMap.range ev) ^ e : Submodule K Ω) ∧ h ≠ 0 ∧
    r * h ∈ ((LinearMap.range ev) ^ e : Submodule K Ω)}
  mul_mem' := by
    rintro a c ⟨e1, h1, m1, n1, p1⟩ ⟨e2, h2, m2, n2, p2⟩
    refine ⟨e1 + e2, h1 * h2, ?_, mul_ne_zero n1 n2, ?_⟩
    · rw [pow_add]; exact Submodule.mul_mem_mul m1 m2
    · rw [pow_add, show a * c * (h1 * h2) = (a * h1) * (c * h2) by ring]; exact Submodule.mul_mem_mul p1 p2
  one_mem' := ⟨0, 1, by rw [pow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩, one_ne_zero,
    by rw [one_mul, pow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩⟩
  add_mem' := by
    rintro a c ⟨e1, h1, m1, n1, p1⟩ ⟨e2, h2, m2, n2, p2⟩
    refine ⟨e1 + e2, h1 * h2, ?_, mul_ne_zero n1 n2, ?_⟩
    · rw [pow_add]; exact Submodule.mul_mem_mul m1 m2
    · rw [pow_add, show (a + c) * (h1 * h2) = (a * h1) * h2 + h1 * (c * h2) by ring]
      exact add_mem (Submodule.mul_mem_mul p1 m2) (Submodule.mul_mem_mul m1 p2)
  zero_mem' := ⟨0, 1, by rw [pow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩, one_ne_zero,
    by rw [zero_mul]; exact zero_mem _⟩
  neg_mem' := by
    rintro a ⟨e, h, m, n, p⟩
    exact ⟨e, h, m, n, by rw [neg_mul]; exact neg_mem p⟩
  inv_mem' := by
    rintro a ⟨e, h, m, n, p⟩
    by_cases ha : a = 0
    · refine ⟨e, h, m, n, ?_⟩
      rw [ha, inv_zero, zero_mul]; exact zero_mem _
    · exact ⟨e, a * h, p, mul_ne_zero ha n, by rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]; exact m⟩

theorem algebraMap_mem_ratioSub (ev : V →ₗ[K] Ω) (c : K) : algebraMap K Ω c ∈ ratioSub ev :=
  ⟨0, 1, by rw [pow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩, one_ne_zero,
    by rw [mul_one, pow_zero]; exact Submodule.mem_one.2 ⟨c, rfl⟩⟩

theorem div_mem_ratioSub (ev : V →ₗ[K] Ω) (v w : V) : ev v / ev w ∈ ratioSub ev := by
  by_cases hw : ev w = 0
  · rw [hw, div_zero]; exact zero_mem _
  · refine ⟨1, ev w, by rw [pow_one]; exact LinearMap.mem_range_self ev w, hw, ?_⟩
    rw [div_mul_cancel₀ _ hw, pow_one]; exact LinearMap.mem_range_self ev v

theorem isRatio_of_mem {ev : V →ₗ[K] Ω} {τ : ℕ} {t w : Ω} (hw : w ∈ LinearMap.range ev) (hw0 : w ≠ 0)
    (ht : t / w ^ τ ∈ ratioSub ev) : DegCmp.IsRatio ev τ t := by
  obtain ⟨e, h, m, n, p⟩ := ht
  refine ⟨e, h, m, n, ?_⟩
  have : t * h = w ^ τ * (t / w ^ τ * h) := by field_simp
  rw [this, pow_add]
  exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ hw τ) p

end Ratio

section Integral

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

theorem eval₂_mem_coneAlg (ev : V →ₗ[K] Ω) {r : ℕ} (v : Fin r → V) (g : MvPolynomial (Fin r) K) :
    eval₂ (Polynomial.C.comp (algebraMap K Ω)) (fun i => Polynomial.C (ev (v i)) * Polynomial.X) g ∈
      DegCmp.coneAlg ev := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [eval₂_C, RingHom.comp_apply, ← Polynomial.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq => rw [eval₂_add]; exact add_mem hp hq
  | mul_X p i hp =>
    rw [eval₂_mul, eval₂_X]
    refine mul_mem hp ?_
    rw [mul_comm]
    exact Algebra.subset_adjoin ⟨v i, rfl⟩

theorem isIntDeg_of_eq {ev : V →ₗ[K] Ω} {r : ℕ} (v : Fin r → V) {τ : ℕ} {t : Ω} {n : ℕ}
    (c : Fin n → MvPolynomial (Fin r) K)
    (h : (Polynomial.C t * Polynomial.X ^ τ) ^ n + ∑ k, eval₂ (Polynomial.C.comp (algebraMap K Ω))
      (fun i => Polynomial.C (ev (v i)) * Polynomial.X) (c k) * (Polynomial.C t * Polynomial.X ^ τ) ^ (k : ℕ) = 0) :
    DegCmp.IsIntDeg ev τ t := by
  let c' : Fin n → DegCmp.coneAlg ev := fun k => ⟨_, eval₂_mem_coneAlg ev v (c k)⟩
  refine ⟨Polynomial.X ^ n + ∑ k : Fin n, Polynomial.C (c' k) * Polynomial.X ^ (k : ℕ),
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt c'), ?_⟩
  rw [mul_comm (Polynomial.X ^ τ)]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow]
  exact h

end Integral

variable {k : Type} [Field k] (S : LinSys k)

theorem comb_single (i : Fin S.N) : S.comb (Pi.single i 1) = S.b i := by
  rw [LinSys.comb, Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero, zero_smul])
    (fun h => (h (Finset.mem_univ i)).elim), Pi.single_eq_same, map_one, one_smul]

theorem sec_eq_zero_of_generic [IsReduced S.Y] {η : S.Y} (hη : IsGenericPoint η Set.univ) {m : ℤ}
    (s : (lbZPow S.L m).Sec) (h : η ∉ nonzeroLocus s) : s = 0 := by
  refine zglobal_ext fun i => ?_
  rw [zfun_zero, ← basicOpen_eq_bot_iff, basicOpen_zfun, eq_bot_iff]
  intro y hy
  exact (h ((hη.mem_open_set_iff (nonzeroLocus s).isOpen).2 ⟨y, trivial, hy.2⟩)).elim

theorem growth_mono (D : ℕ) {r r' : ℕ → ℕ∞} (h : ∀ τ, r τ ≤ r' τ) : growth D r ≤ growth D r' :=
  limsup_le_limsup (Eventually.of_forall fun τ => by
    gcongr
    exact h τ)

theorem finrank_le_toENat (R M : Type) [Field R] [AddCommGroup M] [Module R M] :
    (Module.finrank R M : ℕ∞) ≤ Cardinal.toENat (Module.rank R M) := by
  by_cases h : Module.Finite R M
  · rw [← Module.finrank_eq_rank]; simp
  · rw [Module.finrank_of_not_finite h]; simp

def powValLin {Ω : Type} [Field Ω] [Algebra k Ω] (x : S.Pt Ω) (m : ℕ) :
    letI : Module k (lbPow S.L m).Sec := Module.compHom _ (algebraMap k Γ(S.Y, ⊤))
    (lbPow S.L m).Sec →ₗ[k] Ω :=
  letI : Module k (lbPow S.L m).Sec := Module.compHom _ (algebraMap k Γ(S.Y, ⊤))
  { toFun := fun s => S.powVal (m := (m : ℤ)) x.1 s
    map_add' := fun s t => by
      change S.powVal x.1 (s + t) = S.powVal x.1 s + S.powVal x.1 t
      rw [LinSys.powVal, LinSys.powVal, LinSys.powVal, zfun_add]
      exact valR_add x.1 _ (S.le_chartAt x.1) _ _
    map_smul' := fun c s => by
      rw [RingHom.id_apply, Algebra.smul_def]
      have e : c • s = algebraMap k Γ(S.Y, ⊤) c • s := rfl
      change S.powVal x.1 (c • s) = _
      rw [e]
      rw [LinSys.powVal, LinSys.powVal, zfun_smul]
      exact (valR_mul x.1 _ (S.le_chartAt x.1) _ _).trans (congrArg (· * _)
        ((valR_res x.1 le_top (S.le_chartAt x.1) _).trans ((S.valR_algebraMap x.1 c).trans
          (congrFun (congrArg DFunLike.coe (LinSys.baseHom_ptOver x)) c)))) }

theorem rankGrowth_lineBundleSections_le_image_forms : ∀ (k : Type) [Field k] [CharZero k] (S : LinSys k), S.IsVariety → S.BasePointFree →
    S.Birational → growth S.D (fun m => (lbH0 k (lbPow S.L m) : ℕ∞)) ≤
      growth S.D (fun m => (Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) := by
  intro k _ _ S hS hb hbir
  obtain ⟨η, hη, hrat⟩ := hbir
  have : IsIntegral S.Y := HeightExists.isIntegral hS
  letI : Algebra k (S.Y.residueField η) := (S.baseHom (resPt η)).toAlgebra
  let x : S.Pt (S.Y.residueField η) := ⟨resPt η, S.comp_str _⟩
  have hx : IsGenericPoint (ptOf x.1) Set.univ := by rw [ptOf_resPt]; exact hη
  let b := Pi.basisFun k (Fin S.N)
  let ev := b.constr k (S.coords (resPt η))
  have hev : ∀ j, ev (b j) = S.coords (resPt η) j := fun j => b.constr_basis k _ j
  have hI : S.imageIdeal = imageIdeal ev b := by
    rw [imageIdeal_eq_coneIdeal_of_generic k _ S x hx 1 (S.coords (resPt η)) one_ne_zero (one_smul _ _).symm,
      CompHt.imageIdeal]
    exact congrArg _ (funext fun j => (hev j).symm)
  have hR : (fun m : ℕ => (Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) =
      fun m => DegCmp.hilb ev (1 * m) := by
    funext m
    rw [one_mul, hI, DegCmp.hilb_eq_finrank_quotPiece k _ _ ev S.N b m]
  rw [hR]
  letI (m : ℕ) : Module k (lbPow S.L m).Sec := Module.compHom _ (algebraMap k Γ(S.Y, ⊤))
  haveI (m : ℕ) : IsScalarTower k Γ(S.Y, ⊤) (lbPow S.L m).Sec := IsScalarTower.of_compHom _ _ _
  have hinj : ∀ m, Function.Injective (powValLin S x m) := fun m => by
    refine (injective_iff_map_eq_zero _).2 fun s hs => sec_eq_zero_of_generic S hη (m := (m : ℤ)) s fun hm => ?_
    rw [← ptOf_resPt η] at hm
    exact (S.powVal_ne_zero_iff (resPt η) s).2 hm hs
  refine le_trans (growth_mono S.D fun m => ?_)
    (ConeDeg.growth_rank_le ev S.D 1 le_rfl (fun m => LinearMap.range (powValLin S x m)) ?_)
  · rw [rank_range_of_injective _ (hinj m), lineBundleGlobalSectionsDim_eq_finrank]
    exact finrank_le_toENat _ _
  · intro m t ht
    obtain ⟨s, rfl⟩ := ht
    rw [one_mul]
    obtain ⟨j, hj⟩ := Function.ne_iff.1 (hb.coords_ne_zero (resPt η))
    have hyj : S.coords (resPt η) j ≠ 0 := hj
    refine ⟨?_, ?_⟩
    · obtain ⟨n, c, hc⟩ := isIntegral_coneRing_of_forall_valuationSubring k (S.Y.residueField η) (algebraMap k _)
        S.N m (S.coords (resPt η)) (powValLin S x m s) fun V hV => by
          obtain ⟨i, hi, hV'⟩ := LinSys.exists_ratio_mem_of_point S hS S.N m (fun i => Pi.single i 1) s
            (fun y => by
              obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hb.ge (Set.mem_univ y))
              exact ⟨i, by rw [comb_single]; exact hi⟩) (resPt η) V hV
          have e : S.val (resPt η) (S.comb (Pi.single i 1)) = S.coords (resPt η) i := by rw [comb_single]; rfl
          rw [e] at hi hV'
          exact ⟨i, hi, hV'⟩
      exact isIntDeg_of_eq b c (by simpa only [hev] using hc)
    · refine isRatio_of_mem ⟨b j, hev j⟩ hyj ?_
      have hle : S.ratioField (resPt η) ≤ ratioSub ev := Subfield.closure_le.2 (Set.union_subset
        (by rintro _ ⟨c, rfl⟩; exact algebraMap_mem_ratioSub ev c)
        (by rintro _ ⟨i, i', rfl⟩; rw [← hev i, ← hev i']; exact div_mem_ratioSub ev _ _))
      exact hle (hrat ▸ Subfield.mem_top _)

end GlobalTheory.SecGrowth
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TateCoker

variable {l : ℕ} [hl : Fact l.Prime] {M N : Type} [CommGroup M] [CommGroup N] (φ : M →* N)

def lker (l : ℕ) : Subgroup M where
  carrier := {x | φ x = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1}
  mul_mem' := by
    rintro a b ⟨ha, m, hm⟩ ⟨hb, m', hm'⟩
    refine ⟨by rw [map_mul, ha, hb, _root_.one_mul], m + m', ?_⟩
    rw [mul_pow, pow_add, pow_mul, hm, one_pow, mul_comm (l ^ m), pow_mul, hm', one_pow, _root_.one_mul]
  one_mem' := ⟨map_one φ, 0, one_pow _⟩
  inv_mem' := by
    rintro a ⟨ha, m, hm⟩
    exact ⟨by rw [map_inv, ha, inv_one], m, by rw [inv_pow, hm, inv_one]⟩

theorem pow_pow_eq_one {x : M} {m : ℕ} (h : x ^ l ^ m = 1) (j : ℕ) : x ^ l ^ (m + j) = 1 := by
  rw [pow_add, pow_mul, h, one_pow]

variable {φ}

theorem kill [Finite φ.ker] {k : M} (hk : φ k = 1) {m : ℕ} (hm : k ^ l ^ m = 1) :
    k ^ l ^ Nat.card φ.ker = 1 := by
  have hp : l.Prime := hl.out
  have h1 : orderOf k ∣ Nat.card φ.ker := Subgroup.orderOf_dvd_natCard _ hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hm)
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos_iff.2 ⟨⟨⟨1, map_one φ⟩⟩, inferInstance⟩
  have h2 : j ≤ Nat.card φ.ker :=
    ((Nat.lt_pow_self hp.one_lt).trans_le (Nat.le_of_dvd hpos (hj ▸ h1))).le
  exact orderOf_dvd_iff_pow_eq_one.1 (hj ▸ pow_dvd_pow l h2)

theorem exists_lift (hs : Function.Surjective φ) [Finite φ.ker] (n : ℕ) (y : N) (hy : y ^ l ^ n = 1) :
    ∃ x : M, φ x = y ∧ ∃ m : ℕ, x ^ l ^ m = 1 := by
  have hp : l.Prime := hl.out
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, pow_one] at hy
    exact ⟨1, by rw [map_one, hy], 0, one_pow _⟩
  obtain ⟨x₀, rfl⟩ := hs y
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos_iff.2 ⟨⟨⟨1, map_one φ⟩⟩, inferInstance⟩
  have hk : x₀ ^ l ^ n ∈ φ.ker := by rw [MonoidHom.mem_ker, map_pow, hy]
  have hc : (x₀ ^ l ^ n) ^ Nat.card φ.ker = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard _ hk)
  obtain ⟨e, u, hu, hcu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' l hp.one_lt.ne'
  have hcop : Nat.Coprime u (l ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hu))
  obtain ⟨w, -, hw⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (Nat.one_lt_pow hn.ne' hp.one_lt)
  refine ⟨x₀ ^ (u * w), ?_, n + e, ?_⟩
  · rw [map_pow, pow_eq_pow_mod _ hy, hw, pow_one]
  · rw [← pow_mul, show u * w * l ^ (n + e) = l ^ n * Nat.card φ.ker * w by rw [hcu, pow_add]; ring,
      pow_mul, pow_mul, hc, one_pow]

theorem indep [Finite φ.ker] {x x' : M} (h : φ x = φ x') {m m' : ℕ} (hx : x ^ l ^ m = 1)
    (hx' : x' ^ l ^ m' = 1) : x ^ l ^ Nat.card φ.ker = x' ^ l ^ Nat.card φ.ker := by
  have h1 : φ (x * x'⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 : (x * x'⁻¹) ^ l ^ (m + m') = 1 := by
    rw [mul_pow, inv_pow, pow_pow_eq_one hx, add_comm, pow_pow_eq_one hx', inv_one, _root_.one_mul]
  have h3 := kill h1 h2
  rwa [mul_pow, inv_pow, mul_inv_eq_one] at h3

variable (hs : Function.Surjective φ) [Finite φ.ker]
include hs

def lift (t : Tate l N) (n : ℕ) : M := (exists_lift hs n (t.lev n) (t.lev_pow n)).choose

theorem lift_spec (t : Tate l N) (n : ℕ) : φ (lift hs t n) = t.lev n ∧ ∃ m : ℕ, lift hs t n ^ l ^ m = 1 :=
  (exists_lift hs n (t.lev n) (t.lev_pow n)).choose_spec

def del (t : Tate l N) : M := lift hs t (Nat.card φ.ker) ^ l ^ Nat.card φ.ker

theorem del_eq (t : Tate l N) {x : M} (hx : φ x = t.lev (Nat.card φ.ker)) {m : ℕ} (hm : x ^ l ^ m = 1) :
    del hs t = x ^ l ^ Nat.card φ.ker := by
  obtain ⟨h1, m', h2⟩ := lift_spec hs t (Nat.card φ.ker)
  exact indep (h1.trans hx.symm) h2 hm

theorem del_mem (t : Tate l N) : del hs t ∈ lker φ l := by
  obtain ⟨h1, m, h2⟩ := lift_spec hs t (Nat.card φ.ker)
  refine ⟨by rw [del, map_pow, h1, t.lev_pow], m, ?_⟩
  rw [del, ← pow_mul, mul_comm, pow_mul, h2, one_pow]

def delta : Tate l N →+ Additive (lker φ l) where
  toFun t := Additive.ofMul ⟨del hs t, del_mem hs t⟩
  map_zero' := by
    show Additive.ofMul _ = Additive.ofMul (1 : lker φ l)
    congr 1
    exact Subtype.ext ((del_eq hs 0 (x := 1) (m := 0) (by rw [map_one, Tate.lev_zero]) (one_pow _)).trans
      (one_pow _))
  map_add' s t := by
    show Additive.ofMul _ = Additive.ofMul (_ * _)
    congr 1
    apply Subtype.ext
    obtain ⟨hs1, m, hs2⟩ := lift_spec hs s (Nat.card φ.ker)
    obtain ⟨ht1, m', ht2⟩ := lift_spec hs t (Nat.card φ.ker)
    refine (del_eq hs (s + t) (x := lift hs s _ * lift hs t _) (m := m + m')
      (by rw [map_mul, hs1, ht1, Tate.lev_add]) ?_).trans ?_
    · rw [mul_pow, pow_pow_eq_one hs2, add_comm, pow_pow_eq_one ht2, _root_.one_mul]
    · rw [mul_pow]; rfl

theorem delta_surjective (hd : ∀ x : M, ∃ y, y ^ l = x) : Function.Surjective (delta (l := l) hs) := by
  intro k0
  set a := Nat.card φ.ker
  obtain ⟨⟨k, hk1, m, hm⟩, rfl⟩ : ∃ z : lker φ l, Additive.ofMul z = k0 := ⟨Additive.toMul k0, rfl⟩
  obtain ⟨s, hsa⟩ := GlobalTheory.Published.tate_lev_surj l M hd a k (kill hk1 hm)
  let t : Tate l N := Tate.mk (fun n => φ (s.lev (n + a))) fun n =>
    ⟨by rw [← map_pow, add_comm, s.lev_add_pow, hsa, hk1], by rw [← map_pow, add_right_comm, s.lev_succ]⟩
  refine ⟨t, ?_⟩
  show Additive.ofMul _ = Additive.ofMul _
  congr 1
  apply Subtype.ext
  exact (del_eq hs t (x := s.lev (a + a)) (m := a + a) rfl (s.lev_pow _)).trans
    ((s.lev_add_pow a a).trans hsa)

theorem delta_ker : (delta hs).ker = (LinearMap.range (Tate.map l φ)).toAddSubgroup := by
  set a := Nat.card φ.ker
  ext t
  have e0 : t ∈ (delta hs).ker ↔ del hs t = 1 := by
    rw [AddMonoidHom.mem_ker]
    constructor
    · intro h; exact congrArg Subtype.val (congrArg Additive.toMul h)
    · intro h
      show Additive.ofMul _ = Additive.ofMul (1 : lker φ l)
      exact congrArg Additive.ofMul (Subtype.ext h)
  rw [e0, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
  constructor
  · intro h
    have lv : ∀ n, (lift hs t (n + a) ^ l ^ n) ^ l ^ a = 1 := fun n => by
      obtain ⟨h1, m, h2⟩ := lift_spec hs t (n + a)
      rw [← h, del_eq hs t (x := lift hs t (n + a) ^ l ^ n) (m := m)
        (by rw [map_pow, h1, add_comm, t.lev_add_pow]) (by rw [← pow_mul, mul_comm, pow_mul, h2, one_pow])]
    let y : Tate l M := Tate.mk (fun n => lift hs t (n + a) ^ l ^ a) fun n => by
      refine ⟨by rw [← pow_mul, mul_comm, pow_mul]; exact lv n, ?_⟩
      obtain ⟨h1, m, h2⟩ := lift_spec hs t (n + 1 + a)
      obtain ⟨h1', m', h2'⟩ := lift_spec hs t (n + a)
      rw [← pow_mul, mul_comm, pow_mul]
      refine indep (m := m) (m' := m') ?_ (by rw [← pow_mul, mul_comm, pow_mul, h2, one_pow]) h2'
      rw [map_pow, h1, h1', show n + 1 + a = (n + a) + 1 by omega, t.lev_succ]
    refine ⟨y, Tate.ext fun n => ?_⟩
    rw [Tate.lev_map, Tate.lev_mk, map_pow, (lift_spec hs t (n + a)).1, t.lev_add_pow]
  · rintro ⟨y, rfl⟩
    exact (del_eq hs _ (x := y.lev a) (m := a) rfl (y.lev_pow a)).trans (y.lev_pow a)

omit hs in
theorem map_injective' : Function.Injective (Tate.map l φ) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => Tate.ext fun n => ?_
  have h1 : ∀ k, φ (y.lev k) = 1 := fun k => congrArg (·.lev k) hy
  rw [Tate.lev_zero, ← y.lev_add_pow n (Nat.card φ.ker)]
  exact kill (h1 _) (y.lev_pow _)

end GlobalTheory.TateCoker

namespace GlobalTheory


open GlobalTheory.TateCoker in
theorem tate_map_coker_card : ∀ (l : ℕ) [Fact l.Prime] (M N : Type) [CommGroup M] [CommGroup N] (φ : M →* N), (∀ x : M, ∃ y, y ^ l = x) → Function.Surjective φ → Finite φ.ker → Function.Injective (Tate.map l φ) ∧ Nat.card (Tate l N ⧸ LinearMap.range (Tate.map l φ)) = Nat.card {x : M // φ x = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1} := by
  intro l _ M N _ _ φ hd hs hf
  refine ⟨map_injective', ?_⟩
  have e1 : (Tate l N ⧸ LinearMap.range (Tate.map l φ)) ≃
      (Tate l N ⧸ (LinearMap.range (Tate.map l φ)).toAddSubgroup) := Equiv.refl _
  rw [Nat.card_congr e1, Nat.card_congr (QuotientAddGroup.quotientAddEquivOfEq (delta_ker hs)).symm.toEquiv,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ (delta_surjective hs hd)).toEquiv]
  exact Nat.card_congr (Additive.toMul.trans (Equiv.refl _))

end GlobalTheory
end
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevGeo.MassLev

theorem mass_components_le : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (x0 : ∀ k, Frame ((U σ).X k).Ψ D.R.r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), (∀ k, IsOrth ((U σ).X k) (x0 k) ∧ IsFundSet ((U σ).X k) (x0 k) (FF k)) → ∑ k, muF ((U σ).X k) (x0 k) (FF k) ≤ ENNReal.ofReal (massLev D.host.E D.R.r l.M) := by
  intro hMB hTB D j H Dw l Xo c U dict hL σ hσ x0 FF hF
  obtain ⟨G, Λ, g, Λk, u, hSD, hk, hdist⟩ := GlobalTheory.T.principalLevel_components_doubleCosets_congruence D j H Dw l Xo c U dict hL σ hσ
  have hX' := fun k => GlobalTheory.T.exists_flagDomainData_principalCongruenceLevel D.host.E D.R.r l.M ((U σ).X k) (Λk k) l.three_le (hk k).2.2.2.1 (hk k).2.2.2.2.1
  choose X' hX'Gm hX'Ψ hX'p0 hX'Λ hX'Γ using hX'
  have hfm : ∀ k, ∃ y, IsOrth (X' k) y ∧ ∃ FF', IsFundSet (X' k) y FF' ∧ muF (X' k) y FF' < ⊤ :=
    fun k => GlobalTheory.finMu_all_data D.host.E D.R.r (X' k)
  choose y hy FF' hFF' _ using hfm
  have hμ : ∀ k, muF ((U σ).X k) (x0 k) (FF k) = muF (X' k) (y k) (FF' k) := by
    intro k
    obtain ⟨hGm, -, -, -, -, hgram, hfw, hbw⟩ := hk k
    refine GlobalTheory.T.covolume_eq_of_realUnitary_conj D.host.E D.R.r ((U σ).X k) (X' k) (hX'Ψ k) (u k) (x0 k) (y k) (FF k) (FF' k)
      (hX'Gm k) (hX'p0 k) (by rw [hGm]; exact hgram) ?_ ?_ (hF k).1 (hy k) (hF k).2 (hFF' k)
    · intro γ hγ
      obtain ⟨γ', hγ', hc⟩ := hfw γ hγ
      exact ⟨γ', (hX'Γ k γ').2 (by rw [hGm]; exact hγ'), hc⟩
    · intro γ' hγ'
      have := (hX'Γ k γ').1 hγ'
      rw [hGm] at this
      exact hbw γ' this
  have hunf := hL.unf σ hσ
  set Ψ : Finset (D.host.E →+* ℂ) := Finset.univ.filter (fun τ => τ (H.rt : D.host.E) = H.rt0) with hΨdef
  have hΨ : ∀ k, (X' k).Ψ = Ψ := by
    intro k
    rw [hX'Ψ k]
    ext τ
    rw [(hunf.2.1 k).2 τ, hΨdef, Finset.mem_filter]
    simp
  rw [Finset.sum_congr rfl (fun k _ => hμ k)]
  set e := Fintype.equivFin (U σ).Comp
  rw [← e.symm.sum_comp]
  have hr : 2 ≤ D.R.r := Formalism.L2.Geo.two_le_r D
  have hTor := hTB D.host.E D.R.r l.M G Λ (by omega) (by have := l.three_le; omega) H.unram hSD
  exact hMB D.host.E D.R.r l.M _ _ G Λ Ψ (fun i => X' (e.symm i)) (fun i => g (e.symm i)) (fun i => y (e.symm i))
    (fun i => FF' (e.symm i)) hr l.three_le H.unram hSD hTor (fun i => (hk (e.symm i)).2.1)
    (fun i i' h => e.symm.injective (hdist _ _ h))
    (fun i => ⟨(hX'Gm _).trans (hk _).1, hΨ _, by rw [hX'Λ]; exact (hk _).2.2.1, fun γ => by rw [hX'Λ, hX'Γ, (hk _).1],
      hy _, hFF' _⟩)

end GlobalTheory.LevGeo.MassLev
end
end
