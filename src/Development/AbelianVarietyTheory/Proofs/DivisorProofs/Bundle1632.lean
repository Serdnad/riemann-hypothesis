module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle978
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiRegularAlongOfEtale
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1608
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle011
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1587
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
import Mathlib.RingTheory.Henselian
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle016
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
import ReciprocityTheory.SemistableReduction.Bundle002
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

@[expose] public section

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open AlgebraicGeometry TopologicalSpace CategoryTheory GlobalTheory.Points GlobalTheory.Twist

set_option autoImplicit false

namespace GlobalTheory.Adelic.GenericRel

theorem eval₂_mul_of_isHomogeneous {σ R A : Type} [CommSemiring R] [CommSemiring A] (φ : R →+* A)
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) (c : A) (v : σ → A) :
    eval₂ φ (fun i => c * v i) p = c ^ d * eval₂ φ v p := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have : a.degree = d := by rw [Finsupp.degree_eq_weight_one]; exact hp (mem_support_iff.1 ha)
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← this, Finsupp.degree_apply, mul_left_comm]

variable {F : Type} [Field F] (S : LinSys F)

noncomputable def relFn (c : S.L.ι) {r e : ℕ} (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (m : ℕ)
    (a : Fin m → MvPolynomial (Fin r) F) : Γ(S.Y, S.L.U c) :=
  zfun th c ^ m + ∑ k, eval₂ ((resG S.Y le_top).comp (algebraMap F Γ(S.Y, ⊤)))
    (fun i => (S.comb (u i)).f c) (a k) * zfun th c ^ (k : ℕ)

theorem valR_relFn {K : Type} [Field K] (x : Sp K ⟶ S.Y) (c : S.L.ι) (hx : ptOf x ∈ S.L.U c) {r e : ℕ}
    (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (m : ℕ) (a : Fin m → MvPolynomial (Fin r) F) :
    valR x (S.L.U c) (relFn S c u th m a) = valR x (S.L.U c) (zfun th c) ^ m + ∑ k, eval₂ (S.baseHom x)
      (fun i => valR x (S.L.U c) ((S.comb (u i)).f c)) (a k) * valR x (S.L.U c) (zfun th c) ^ (k : ℕ) := by
  have h := (le_iff_ptOf_mem x _).2 hx
  have hc : (valMap x _ h).hom.comp ((resG S.Y le_top).comp (algebraMap F Γ(S.Y, ⊤))) = S.baseHom x := by
    ext b
    exact ((valR_eq x _ h _).symm.trans (valR_res x le_top h _)).trans (S.valR_algebraMap x b)

  simp only [relFn, valR_eq x _ h, map_add (f := _), map_sum, map_mul, map_pow, eval₂_comp_left, hc]
  rfl

theorem relation_of_generic (F : Type) [Field F] (S : LinSys F) (hY : AlgebraicGeometry.IsIntegral S.Y)
    (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (η : S.Y) (hη : IsGenericPoint η Set.univ)
    (m : ℕ) (a : Fin m → MvPolynomial (Fin r) F) (ha : ∀ k, (a k).IsHomogeneous (e * (m - k)))
    (h0 : S.powVal (resPt η) th ^ m + ∑ k, MvPolynomial.eval₂ (S.baseHom (resPt η))
      (fun i => S.val (resPt η) (S.comb (u i))) (a k) * S.powVal (resPt η) th ^ (k : ℕ) = 0)
    (K : Type) [Field K] [Algebra F K] (x : S.Pt K) :
    S.powVal x.1 th ^ m + ∑ k, aeval (fun i => ∑ j, algebraMap F K (u i j) * S.coords x.1 j) (a k) *
      S.powVal x.1 th ^ (k : ℕ) = 0 := by
  have hxU : ptOf x.1 ∈ S.L.U (S.chartAt (ptOf x.1)) := S.mem_chartAt _
  have hηU : ptOf (resPt η) ∈ S.L.U (S.chartAt (ptOf x.1)) := by
    rw [ptOf_resPt]
    exact (hη.mem_open_set_iff (S.L.U _).isOpen).2 ⟨_, trivial, hxU⟩
  obtain ⟨c0, hc0, hv, hp⟩ := S.exists_frame_change (resPt η) _ hηU
  have hzero : valR (resPt η) _ (relFn S (S.chartAt (ptOf x.1)) u th m a) = 0 := by
    rw [valR_relFn S _ _ hηU, hp (e : ℤ) th]
    simp only [hv, zpow_natCast, eval₂_mul_of_isHomogeneous _ (ha _)]
    calc _ = c0 ^ (e * m) * (S.powVal (resPt η) th ^ m + ∑ k, MvPolynomial.eval₂ (S.baseHom (resPt η))
          (fun i => S.val (resPt η) (S.comb (u i))) (a k) * S.powVal (resPt η) th ^ (k : ℕ)) := by
          rw [mul_add, Finset.mul_sum, mul_pow, ← pow_mul]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_pow, ← pow_mul, show e * m = e * (m - k) + e * k by
            rw [← mul_add, Nat.sub_add_cancel k.2.le], pow_add]
          ring
      _ = 0 := by rw [h0, mul_zero]
  have hb : S.Y.basicOpen (relFn S (S.chartAt (ptOf x.1)) u th m a) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hm : η ∈ S.Y.basicOpen (relFn S (S.chartAt (ptOf x.1)) u th m a) :=
      (hη.mem_open_set_iff (S.Y.basicOpen _).isOpen).2 ⟨y, trivial, hy⟩
    rw [← ptOf_resPt η] at hm
    exact ((valR_ne_zero_iff (resPt η) hηU _).2 hm hzero).elim
  have hf : relFn S (S.chartAt (ptOf x.1)) u th m a = 0 := by
    haveI := hY
    exact (basicOpen_eq_bot_iff _).1 hb
  have key := valR_relFn S x.1 _ hxU u th m a
  rw [hf, valR_zero x.1 _ ((le_iff_ptOf_mem _ _).2 hxU)] at key
  have e2 : ∀ i, valR x.1 _ ((S.comb (u i)).f (S.chartAt (ptOf x.1))) =
      ∑ j, algebraMap F K (u i j) * S.coords x.1 j := fun i =>
    (S.val_comb x.1 (u i)).trans (by rw [LinSys.baseHom_ptOver])
  simp only [e2, LinSys.baseHom_ptOver] at key
  simp only [aeval_def]
  exact key.symm

end GlobalTheory.Adelic.GenericRel
end

section

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.Adelic.LinSys

theorem exists_ratio_mem_of_point {F K : Type} [Field F] [Field K] (S : LinSys F) (hS : S.IsVariety) (r e : ℕ)
    (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (hcov : ∀ y : S.Y, ∃ i, y ∈ nonzeroLocus (S.comb (u i)))
    (x : Sp K ⟶ S.Y) (V : ValuationSubring K) (hV : ∀ c, S.baseHom x c ∈ V) :
    ∃ i, S.val x (S.comb (u i)) ≠ 0 ∧ S.powVal x th / S.val x (S.comb (u i)) ^ e ∈ V := by
  have hpr : IsProper S.str := GlobalTheory.CommonModel.isProper_of_isProjOver hS.proj
  let φ : F →+* V := (S.baseHom x).codRestrict V hV
  have hsq : x ≫ S.str = specAlgebraMap V K ≫ spMap φ := by
    rw [S.comp_str x, ← Spec.map_comp]
    rfl
  obtain ⟨l, hl, -⟩ := exists_valuativeExtension S.str (spMap φ) x hsq
  have hx : spMap (algebraMap V K) ≫ l = x := hl
  obtain ⟨i, hi⟩ := hcov (l (IsLocalRing.closedPoint V))
  have hyc := S.mem_chartAt (l (IsLocalRing.closedPoint V))
  set c := S.chartAt (l (IsLocalRing.closedPoint V))
  have hU : ⊤ ≤ l ⁻¹ᵁ S.L.U c := (GlobalTheory.ZH.CrdCalc.top_le_iff l _).2 hyc
  have hB : ⊤ ≤ l ⁻¹ᵁ S.Y.basicOpen ((S.comb (u i)).f c) :=
    (GlobalTheory.ZH.CrdCalc.top_le_iff l _).2 ((mem_nonzeroLocus_iff_basicOpen _ hyc).1 hi)
  obtain ⟨w, hw⟩ := (GlobalTheory.ZH.CrdCalc.isUnit_valR_iff l _ hU _).2 hB
  obtain ⟨hU', hval⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (algebraMap V K) l _ hU
  rw [hx] at hU' hval
  obtain ⟨c₀, hc₀, h₁, h₂⟩ := S.exists_frame_change x c ((le_iff_ptOf_mem x _).1 hU')
  have ha := (h₁ (S.comb (u i))).symm.trans (hval _)
  have ht := (h₂ e th).symm.trans (hval _)
  rw [← hw] at ha
  have hw₀ : algebraMap V K (w : V) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 w.ne_zero
  have hv : S.val x (S.comb (u i)) ≠ 0 := fun h => hw₀ (by rw [← ha, h, mul_zero])
  refine ⟨i, hv, ?_⟩
  have key : S.powVal x th / S.val x (S.comb (u i)) ^ e =
      algebraMap V K (valR l _ (Twist.zfun th c) * ((w⁻¹ : Vˣ) : V) ^ e) := by
    have hinv : algebraMap V K ((w⁻¹ : Vˣ) : V) = (algebraMap V K (w : V))⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    rw [map_mul, map_pow, ← ht, hinv, ← ha, zpow_natCast]
    rw [inv_pow, mul_pow]
    field_simp
  rw [key]
  exact (valR l _ (Twist.zfun th c) * ((w⁻¹ : Vˣ) : V) ^ e).2

theorem exists_ratio_mem_valuationSubring : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → ∀ (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec), (∀ y : S.Y, ∃ i, y ∈ nonzeroLocus (S.comb (u i))) → ∀ η : S.Y, IsGenericPoint η Set.univ → ∀ V : ValuationSubring (S.Y.residueField η), (∀ c, S.baseHom (resPt η) c ∈ V) → ∃ i, S.val (resPt η) (S.comb (u i)) ≠ 0 ∧ S.powVal (resPt η) th / S.val (resPt η) (S.comb (u i)) ^ e ∈ V :=
  fun _ _ S hS r e u th hcov η _ V hV => exists_ratio_mem_of_point S hS r e u th hcov (resPt η) V hV

end GlobalTheory.Adelic.LinSys
end
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.exists_homogeneous_forms_quotient_birational_system : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → S.BasePointFree → S.Birational → ∀ (W : S.Y.Opens) (a : Γ(S.Y, W)), ∃ (d : ℕ) (P Q : MvPolynomial (Fin S.N) F), P.IsHomogeneous d ∧ Q.IsHomogeneous d ∧ Q ∉ S.imageIdeal ∧ (a ≠ 0 → P ∉ S.imageIdeal) ∧ ∀ (K : Type) [Field K] [Algebra F K] (x : S.Pt K), ptOf x.1 ∈ W → valR x.1 W a * aeval (S.coords x.1) Q = aeval (S.coords x.1) P := by
  first | exact @GlobalTheory.HSShort.FormRatio.exists_forms | exact GlobalTheory.HSShort.FormRatio.exists_forms | (intros; apply GlobalTheory.HSShort.FormRatio.exists_forms <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

open TopologicalSpace Opposite H0

theorem exists_local_lift_H0On : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (B : LB Y), B.IsLB → ∀ (I : Y.IdealSheafData) (g : sectionsOnClosedSubscheme p B I) (y : Y), ∃ (W : Y.Opens) (_ : y ∈ W) (b : Vanishing.H0 p B W), ∀ (z : I.subscheme) (hz : I.subschemeι z ∈ W) (j : (B.pull I.subschemeι).ι) (hj : z ∈ (B.pull I.subschemeι).U j), Vanishing.H0.germ j z (TopologicalSpace.Opens.mem_top z) hj g = (I.subschemeι.stalkMap z).hom (Vanishing.H0.germ (j PUnit.unit) (I.subschemeι z) hz (mem_pull.1 hj) b) := by
  intro k _ Y p B hB I g y
  obtain ⟨i, hi⟩ := exists_chart hB y
  obtain ⟨W, hyW, hWi⟩ := exists_affine hi
  obtain ⟨J, rfl⟩ : ∃ J : (B.pull I.subschemeι).ι, J PUnit.unit = i := ⟨fun _ => i, rfl⟩
  have hJ (z : I.subscheme) (hz : I.subschemeι z ∈ W.1) : z ∈ (B.pull I.subschemeι).U J :=
    mem_pull.2 (hWi hz)
  have hle : I.subschemeι ⁻¹ᵁ W.1 ≤ ⊤ ⊓ (B.pull I.subschemeι).U J :=
    fun z hz => ⟨trivial, hJ z hz⟩
  obtain ⟨a, ha⟩ := I.subschemeι_app_surjective W (resG I.subscheme hle (g.loc J))
  let b : H0 p B W.1 := (LB.chartEquiv hB (J PUnit.unit) hWi).symm a
  have hb (x : Y) (hx : x ∈ W.1) : germ (J PUnit.unit) x hx (hWi hx) b = ger x hx a := by
    conv_rhs =>
      rw [← (LB.chartEquiv hB (J PUnit.unit) hWi).apply_symm_apply a, LB.chartEquiv_apply,
        ger_resG]
    rfl
  refine ⟨W.1, hyW, b, fun z hz j hj => ?_⟩
  have h0 : germ J z (Opens.mem_top z) (hJ z hz) g =
      (I.subschemeι.stalkMap z).hom (germ (J PUnit.unit) (I.subschemeι z) hz (hWi hz) b) := by
    rw [hb, germ_apply, ← ger_resG hle z hz, ← ha]
    exact (Scheme.Hom.germ_stalkMap_apply _ _ z hz a).symm
  rw [germ_change j J z _ hj (hJ z hz), h0,
    germ_change (j PUnit.unit) (J PUnit.unit) _ hz (mem_pull.1 hj) (hWi hz), map_mul,
    tr_pull B I.subschemeι z hj (hJ z hz), Units.coe_map]
  rfl

end GlobalTheory.Vanishing
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RestrProd

theorem twOrb_restrProd : ∀ (ι G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, T2Space (H i)] (p : ∀ i, G →* H i) (K : Subgroup G) (KH : ∀ i, Subgroup (H i)) (δ : G) (f : ∀ i, H i → ℂ), (∀ i, Continuous (p i)) → (∀ x y : G, (∀ i, p i x = p i y) → x = y) → (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) → (∀ C : ∀ i, Set (H i), (∀ i, IsCompact (C i)) → (∀ᶠ i in cofinite, C i = KH i) → IsCompact {x : G | ∀ i, p i x ∈ C i}) → (∀ i, IsCompact (KH i : Set (H i))) → (∀ i, ∀ a ∈ twCent (MonoidHom.id (H i)) (p i δ), ∀ b ∈ twCent (MonoidHom.id (H i)) (p i δ), a * b = b * a) → (∀ i (x : H i), twCent (MonoidHom.id (H i)) (p i δ) ⊓ (KH i).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id (H i)) (p i δ)) ∧ (twCent (MonoidHom.id (H i)) (p i δ) ⊓ (KH i).map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) ≠ 0) → (∀ i (x : H i), (rStab fun k : KH i => f i ((x * k)⁻¹ * p i δ * (x * k))).index ≠ 0) → (∀ i, {q : DoubleCoset.Quotient (twCent (MonoidHom.id (H i)) (p i δ) : Set (H i)) (KH i : Set (H i)) | ∃ k ∈ KH i, f i ((Quotient.out q * k)⁻¹ * p i δ * (Quotient.out q * k)) ≠ 0}.Finite) → (∀ᶠ i in cofinite, p i δ ∈ KH i ∧ f i = (KH i : Set (H i)).indicator 1 ∧ (∀ g : H i, g⁻¹ * p i δ * g ∈ KH i → ∃ t ∈ twCent (MonoidHom.id (H i)) (p i δ), t⁻¹ * g ∈ KH i) ∧ cptPart (twCent (MonoidHom.id (H i)) (p i δ)) ≤ KH i) → twOrb (MonoidHom.id G) K δ (fun x => ∏ᶠ i, f i (p i x)) = ∏ᶠ i, twOrb (MonoidHom.id (H i)) (KH i) (p i δ) (f i) := by
  intro ι G _ _ _ H _ _ _ _ p K KH δ f hpc hinj hglue hfin hK hcpt hKc hcomm hloc hstab hsupp hgood
  have hT : ∀ x, x ∈ twCent (MonoidHom.id G) δ ↔ ∀ i, p i x ∈ twCent (MonoidHom.id (H i)) (p i δ) := by
    intro x
    simp only [GlobalTheory.TwOrbConj.mem_twCent, MonoidHom.id_apply]
    constructor
    · intro h i
      rw [← map_mul, h, map_mul]
    · intro h
      apply hinj
      intro i
      rw [map_mul, h i, map_mul]
  have hC := GlobalTheory.T.mem_compactPart_centralizer_iff_local ι G H p KH _ _ hpc hfin hcpt hKc hT hcomm
  have hCT : ∀ i, cptPart (twCent (MonoidHom.id (H i)) (p i δ)) ≤ twCent (MonoidHom.id (H i)) (p i δ) :=
    fun i => (Subgroup.closure_le _).2 (fun t ht => ht.1)
  have havg1 : ∀ (M : Type) [Group M], avg (fun _ : M => (1 : ℂ)) = 1 := by
    intro M _
    have hR : rStab (fun _ : M => (1 : ℂ)) = ⊤ := by
      ext k
      simp [GlobalTheory.TwOrbConj.mem_rStab]
    unfold avg
    rw [hR, Subgroup.index_top]
    haveI : Subsingleton (M ⧸ (⊤ : Subgroup M)) := QuotientGroup.subsingleton_quotient_top
    haveI : Unique (M ⧸ (⊤ : Subgroup M)) := uniqueOfSubsingleton (QuotientGroup.mk 1)
    simp [finsum_unique]
  have hs : ∀ g, GlobalTheory.TwOrbConj.summand (MonoidHom.id G) K δ (fun x => ∏ᶠ i, f i (p i x)) g =
      ∏ᶠ i, GlobalTheory.TwOrbConj.summand (MonoidHom.id (H i)) (KH i) (p i δ) (f i) (p i g) := by
    intro g
    have hrel := GlobalTheory.T.relIndex_inf_conj_eq_finprod_restrictedProduct ι G H p K _ _ KH _ _ g hglue hfin hK hT hC hCT (fun i => hloc i (p i g))
      (hgood.mono fun i h => h.2.2.2)
    have hu1 : ∀ᶠ i in cofinite, ∀ k : KH i, f i ((p i g * k)⁻¹ * p i δ * (p i g * k)) = 1 := by
      filter_upwards [hgood, hfin g] with i h hg k
      rw [h.2.1]
      apply Set.indicator_of_mem
      exact (KH i).mul_mem ((KH i).mul_mem ((KH i).inv_mem ((KH i).mul_mem hg k.2)) h.1) ((KH i).mul_mem hg k.2)
    have havg := GlobalTheory.T.groupAverage_componentwiseSubgroup_eq_prod ι G H p K KH hK (fun i k => f i ((p i g * k)⁻¹ * p i δ * (p i g * k))) hglue
      (fun i => hstab i (p i g)) hu1
    have hr1 : ∀ᶠ i in cofinite, (((twCent (MonoidHom.id (H i)) (p i δ) ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) : ℕ) : ℂ) = 1 := by
      filter_upwards [hgood, hfin g] with i h hg
      rw [GlobalTheory.TwOrbConj.map_conj_self _ hg, Subgroup.relIndex_eq_one.2 (le_inf (hCT i) h.2.2.2), Nat.cast_one]
    have ha1 : ∀ᶠ i in cofinite, avg (fun k : KH i => f i ((p i g * k)⁻¹ * p i δ * (p i g * k))) = 1 := by
      filter_upwards [hu1] with i h
      rw [show (fun k : KH i => f i ((p i g * k)⁻¹ * p i δ * (p i g * k))) = fun _ => 1 from funext h]
      exact havg1 _
    have e1 : avg (fun k : K => ∏ᶠ i, f i (p i ((g * ↑k)⁻¹ * δ * (MonoidHom.id G) (g * ↑k)))) =
        ∏ᶠ i, avg (fun k : KH i => f i ((p i g * k)⁻¹ * p i δ * (p i g * k))) := by
      rw [← havg]
      congr 1
      funext k
      simp [map_mul, map_inv]
    unfold GlobalTheory.TwOrbConj.summand
    simp only [MonoidHom.id_apply] at e1 ⊢
    have hN : Function.HasFiniteMulSupport fun i => (twCent (MonoidHom.id (H i)) (p i δ) ⊓
        (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) := by
      have : ∀ᶠ i in cofinite, (twCent (MonoidHom.id (H i)) (p i δ) ⊓
          (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) = 1 := by
        filter_upwards [hgood, hfin g] with i h hg
        rw [GlobalTheory.TwOrbConj.map_conj_self _ hg, Subgroup.relIndex_eq_one.2 (le_inf (hCT i) h.2.2.2)]
      exact Filter.eventually_cofinite.1 this
    have hcast := map_finprod (Nat.castRingHom ℂ) hN
    simp only [eq_natCast] at hcast
    rw [e1, hrel, hcast, ← finprod_mul_distrib (Filter.eventually_cofinite.1 hr1) (Filter.eventually_cofinite.1 ha1)]
  rw [GlobalTheory.TwOrbConj.twOrb_eq]
  simp only [GlobalTheory.TwOrbConj.twOrb_eq]
  refine GlobalTheory.T.finsum_doubleCoset_eq_finprod_local_sums ι G H p _ K _ KH _ _ hglue hfin hK hT ?_ ?_ ?_ hs
  · intro i t ht k hk x
    exact GlobalTheory.TwOrbConj.summand_rep _ _ _ _ x ht hk
  · intro i
    refine (hsupp i).subset ?_
    intro q hq
    by_contra hcon
    apply hq
    have h0 : (fun k : KH i => f i ((Quotient.out q * k)⁻¹ * p i δ * (MonoidHom.id (H i)) (Quotient.out q * k))) =
        fun _ => 0 := by
      funext k
      by_contra hk
      exact hcon ⟨k, k.2, hk⟩
    unfold GlobalTheory.TwOrbConj.summand
    rw [h0]
    simp [avg]
  · filter_upwards [hgood] with i h x
    rw [h.2.1]
    exact GlobalTheory.T.twistedOrbitalIntegralSummand_goodPlace_indicator (H i) (KH i) (p i δ) h.1 h.2.2.2 h.2.2.1 x

end GlobalTheory.RestrProd
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_productGroup : ∀ (G G' : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [T2Space G'] (θ : G →* G) (θ' : G' →* G') (K : Subgroup G) (K' : Subgroup G') (δ : G) (δ' : G') (f : G → ℂ) (f' : G' → ℂ), (∀ x : G, (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0) → (∀ x : G', (rStab fun k : K' => f' ((x * k)⁻¹ * δ' * θ' (x * k))).index ≠ 0) → {q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G) | ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k)) ≠ 0}.Finite → {q : DoubleCoset.Quotient (twCent θ' δ' : Set G') (K' : Set G') | ∃ k ∈ K', f' ((Quotient.out q * k)⁻¹ * δ' * θ' (Quotient.out q * k)) ≠ 0}.Finite → twOrb (θ.prodMap θ') (K.prod K') (δ, δ') (fun y => f y.1 * f' y.2) = twOrb θ K δ f * twOrb θ' K' δ' f' := by
  first | exact @GlobalTheory.BCT.OrbProd.twOrb_prod | exact GlobalTheory.BCT.OrbProd.twOrb_prod | (intros; apply GlobalTheory.BCT.OrbProd.twOrb_prod <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.heckeCharCM_eta_local_eq_neg_one_pow_val_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ μ : HChar E,
    (∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x) →
    (∀ (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ), ¬ IsSplitAt w → Valued.v (u : w.adicCompletion E) = 1 →
      μ.1 (Neutral.B1.localIdele E w u) = 1) →
    ∀ w : Pl E, ¬ IsSplitAt w → μ.loc w = GlobalTheory.SmGL.unrChar (w.adicCompletion E) (-1) := by
  first | exact @GlobalTheory.MuInert.loc_eq_unrChar_neg_one | exact GlobalTheory.MuInert.loc_eq_unrChar_neg_one | (intros; apply GlobalTheory.MuInert.loc_eq_unrChar_neg_one <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB mulN)
open GlobalTheory.PDiv (SpAlg)
open GlobalTheory.DeRham (spOver)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulNDiv

theorem hom_ext_of_spAlg {R : Type} [CommRing R] {T B : Over (Sp R)} (a b : T ⟶ B)
    (h : ∀ (S : Type) [CommRing S] [Algebra R S] (g : SpAlg R S ⟶ T), g ≫ a = g ≫ b) : a = b := by
  ext1
  apply T.left.affineOpenCover.openCover.hom_ext
  intro j
  let C : CommRingCat := T.left.affineOpenCover.X j
  let φ : CommRingCat.of R ⟶ C := Spec.preimage (T.left.affineOpenCover.f j ≫ T.hom)
  letI : Algebra R C := φ.hom.toAlgebra
  let g : SpAlg R C ⟶ T := Over.homMk (T.left.affineOpenCover.f j) (by
    show _ = Spec.map (CommRingCat.ofHom (algebraMap R C))
    rw [← Spec.map_preimage (T.left.affineOpenCover.f j ≫ T.hom)]
    rfl)
  have := congrArg CommaMorphism.left (h C g)
  simp only [g, Over.comp_left, Over.homMk_left] at this
  exact this

theorem exists_factor_mulN : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (n : ℕ), 0 < n → ∀ (F : A ⟶ B), IsMonHom F → (∀ (S : Type) [CommRing S] [Algebra R S] (z : SpAlg R S ⟶ A), z ^ n = 1 → z ≫ F = 1) → ∃ f : A ⟶ B, IsMonHom f ∧ F = mulN A n ≫ f := by
  intro R _ A B _ _ hA _ n hn F hF hker
  haveI := hA.comm
  obtain ⟨hfin, hflat, hsurj⟩ := GlobalTheory.T.abelianScheme_mulN_finite_flat_surjective R A hA n hn
  haveI : IsMonHom (mulN A n) := GlobalTheory.MulEtaleDvr.isMonHom_mulN A n
  have hqc : QuasiCompact (mulN A n).left := inferInstance
  have h : ∀ (T : Over (Sp R)) (x : T ⟶ A), x ≫ mulN A n = 1 → x ≫ F = 1 := by
    intro T x hx
    apply hom_ext_of_spAlg
    intro S _ _ g
    have hxn : x ^ n = 1 := by
      rw [← hx, GlobalTheory.MulEtaleDvr.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]
    have hz : (g ≫ x) ^ n = 1 := by
      rw [← MonObj.comp_pow, hxn, MonObj.comp_one]
    rw [← Category.assoc, hker S (g ≫ x) hz, MonObj.comp_one]
  obtain ⟨⟨ψ, hψ, hc⟩, -⟩ := exists_monHom_factor_of_flat_surjective _ A A B (mulN A n) F inferInstance hF
    hflat hsurj hqc h
  exact ⟨ψ, hψ, hc.symm⟩

end GlobalTheory.MulNDiv
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.levelMove_lift_congruent_mod_ideal : ∀ {D : D7} (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), Formalism.L2.Pj.LatEmb V ι → ∀ (M : ℕ) (Mb Mh : Ideal (𝓞 D.host.E)), Mb ⊔ Mh = ⊤ → ((M : ℕ) : 𝓞 D.host.E) ∈ Mb → ∀ (κ : Formalism.L2.Theta.GA D V), GlobalTheory.Member.FinCong V 1 κ → ∀ (f : La →ₗ[𝓞 D.host.E] La), (∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ Formalism.L2.Pj.latGHat V 1, Formalism.L2.Pj.finVec V (ι (f a)) - (Formalism.L2.Theta.finHom V κ).1 *ᵥ Formalism.L2.Pj.finVec V (ι a) = M • w) → (∀ x, f x - x ∈ Mb • (⊤ : Submodule (𝓞 D.host.E) La)) → ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)), (Formalism.L2.Theta.finHom V κ).1 *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F ((Mb • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) := by
  first | exact @GlobalTheory.LevelMoveCong.mulVec_sub_mem_hat_smul | exact GlobalTheory.LevelMoveCong.mulVec_sub_mem_hat_smul | (intros; apply GlobalTheory.LevelMoveCong.mulVec_sub_mem_hat_smul <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CuspRep.UnitaryParam

theorem map_star_eq_map_inv_of_form : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ), (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) → (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) → (∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) → ∀ (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w (π.locRep w) B → B.map star = B.map (·⁻¹) := by
  intro E _ _ _ a π H hH hpos hinv w B hB
  obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec hB
  refine GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv E w a π.V (π.locRep w) x B ?_ hx
  refine ⟨H.flip, fun v u => ?_, fun v hv => ?_, fun g v u => ?_⟩
  · simp only [LinearMap.flip_apply]
    exact (hH u v).symm
  · simpa only [LinearMap.flip_apply] using hpos v hv
  · simp only [LinearMap.flip_apply]
    exact hinv _ u v

end GlobalTheory.CuspRep.UnitaryParam
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.twistedCentralizer_equiv_normOneTorus_nonsplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ u β : B.A, IsUnit β → B.σ β = β * ((-1) ^ (m - 1) * u) → Algebra.adjoin K.E {u} = ⊤ → IsUnit (GlobalTheory.TwLat.gram e b β) → ∃ φ : twCent (thL m w) (GlobalTheory.TwLat.dlt e b β) ≃* B.T, (∀ t : twCent (thL m w) (GlobalTheory.TwLat.dlt e b β), (t : GLw m w).val = GlobalTheory.TwLat.mulMat e b (((φ t : B.T) : B.Aˣ) : B.A)) ∧ ∀ t : twCent (thL m w) (GlobalTheory.TwLat.dlt e b β), ((t : GLw m w) ∈ cptPart (twCent (thL m w) (GlobalTheory.TwLat.dlt e b β)) ↔ ((φ t : B.T) : B.Aˣ) ∈ GlobalTheory.UnitLemma.intUnits K.O B.A) := by
  first | exact @GlobalTheory.TwLat.twCent_equiv_torus | exact GlobalTheory.TwLat.twCent_equiv_torus | (intros; apply GlobalTheory.TwLat.twCent_equiv_torus <;> assumption)
end
