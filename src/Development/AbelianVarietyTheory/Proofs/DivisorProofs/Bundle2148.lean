module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle165
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle243
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle298
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle224
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle238
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle308
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle252
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle219
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle164
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle008
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle030
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationNonnegIffSpanMultiplicationTranslates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle099
public import Formalism.RealPlaceAnalysis.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraCapelliUniformDiagonalBlocks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2121
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.CarriedHecke

theorem exists_sys_of_mem_span {K V H I J : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup H] [Module ℂ H]
    (σ : K →+* ℂ) (op : I → Module.End K V) (j : V →ₛₗ[σ] H) (h : J → Module.End ℂ H) (ι : J → I)
    (hj : ∀ i f, j (op (ι i) f) = h i (j f)) (hc : Formalism.L2.Col.PairComm h) (C : (I → K) → Prop) (v : H)
    (hv : v ∈ Submodule.span ℂ (j '' (Formalism.L2.Col.eigSum op C : Set V))) (hv0 : v ≠ 0) (l : J → ℂ)
    (he : ∀ i, h i v = l i • v) : ∃ x, C x ∧ ∀ i, σ (x (ι i)) = l i := by
  classical

  have hstep : ∀ (i : J) (a : K) (k : ℕ) (g : V),
      ((h i - σ a • 1) ^ k) (j g) = j (((op (ι i) - a • 1) ^ k) g) := by
    intro i a k
    induction k with
    | zero => intro g; simp
    | succ k ih =>
      intro g
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
      simp [hj, map_smulₛₗ]
  have himg : ∀ x, ∀ f ∈ Formalism.L2.Col.eigAt op x, j f ∈ Formalism.L2.Col.eigAt h (fun i => σ (x (ι i))) := by
    intro x f hf
    rw [Formalism.L2.Col.eigAt, Submodule.mem_iInf] at hf ⊢
    intro i
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 (hf (ι i))
    exact (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, by rw [hstep, hk, map_zero]⟩
  set T : Submodule ℂ H := ⨆ (x : I → K) (_ : C x), Formalism.L2.Col.eigAt h (fun i => σ (x (ι i))) with hT
  have hle : Formalism.L2.Col.eigSum op C ≤ T.comap j := by
    refine iSup₂_le fun x hx f hf => ?_
    exact (le_iSup₂_of_le (f := fun (x : I → K) (_ : C x) => Formalism.L2.Col.eigAt h (fun i => σ (x (ι i)))) x hx le_rfl)
      (himg x f hf)
  have hvT : v ∈ T := by
    refine (Submodule.span_le.2 ?_) hv
    rintro _ ⟨f, hf, rfl⟩
    exact hle hf
  have hvl : v ∈ Formalism.L2.Col.eigAt h l := Formalism.L2.Col.mem_eigAt_of_forall_apply he
  by_contra hno
  push_neg at hno
  have hT' : T ≤ ⨆ (y : J → ℂ) (_ : y ≠ l), Formalism.L2.Col.eigAt h y := by
    refine iSup₂_le fun x hx => ?_
    obtain ⟨i, hi⟩ := hno x hx
    exact le_iSup₂_of_le (f := fun (y : J → ℂ) (_ : y ≠ l) => Formalism.L2.Col.eigAt h y) (fun i => σ (x (ι i)))
      (fun e => hi (congrFun e i)) le_rfl
  exact hv0 ((Submodule.disjoint_def.1 (Formalism.L2.Col.iSupIndep_eigAt hc l)) v hvl (hT' hvT))

theorem dualLab_dualLab (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse, List.map_map]



theorem hecke_polys_of_carries : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) → ∀ p c, R.Carries p c → ∀ P ∈ A3.A.ok A3.A.μ0, RealDat.polE (A := A3.A) p.1.1 P = Formalism.L2.Col.heckePolyOf D.R.r (A3.A.q P) (fun k => c (R.pl P) (dualLab (splitLab D.R.r k))) ∧ RealDat.polW (A := A3.A) p.1.1 P = Formalism.L2.Col.heckePolyOf D.R.r (A3.A.q P) (fun k => c (R.pl P) (splitLab D.R.r k)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hI hok hW hEx hS hinj p c hcar P hP
  obtain ⟨hC, hSF, hEE, -⟩ := GlobalTheory.T.core_clauses_of_weak_characterisation R F hW hEx
  obtain ⟨hG, hcj, hq⟩ := (GlobalTheory.T.theta_lift_levels_good_primes_properties R.toRealDat F.lv2 hC.lev).2.2.2 hC.fam A3.A.μ0 P hP
  have hq0 : (A3.A.q P : ℂ) ≠ 0 := by
    rw [hq, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact (R.pl P).ne_bot
  obtain ⟨_, _, _, htie⟩ := hC.fam.tie
  obtain ⟨-, hr, ht⟩ := htie.ranks
  have hrX : D.sp.X'.rank = A3.A.r + D.R.m * A3.A.t := by rw [D.sp.X'_rank, hr, ht]; rfl
  have hrY : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _), Nat.zero_min]; simp [Ranks.rankY]
  have hr0 : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hm0 : 0 < D.R.m := by have := D.R.two_le_m; omega

  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcar.1
  have hwp : w ∈ R.EEp3 p :=
    (le_iSup₂ (f := fun c (_ : R.Carries p c) => R.EEc c) c hcar) hw
  have hv0 : LinearMap.adjoint (R.Th A3.A.μ0) w ≠ 0 := fun h0 => hw0 (hinj p w hwp h0)
  have hwE : w ∈ EEc R.toRealDat R.SF c := (hEE c) ▸ hw
  obtain ⟨hX, hXo, hXn⟩ := (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hC.lev hC.fam hC.models).1 A3.A.μ0
  obtain ⟨zE, hmE, hpE⟩ := GlobalTheory.T.exists_splitPrime_heckeTransfer_compositeLift R.toRealDat F.lv2 hI hC hS A3.A.μ0 ⟨P, hP⟩
  have heig : ∀ k : Fin (D.sp.X'.rank + 1), hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1)
      (LinearMap.adjoint (R.Th A3.A.μ0) w) = GlobalTheory.Hk3.evC (Yc D 0) (R.pl P) (fun d => c (R.pl P) (dualLab d))
        (GlobalTheory.Hk3.splitC (Yc D 0).rank (zE k)) • LinearMap.adjoint (R.Th A3.A.μ0) w := fun k =>
    (GlobalTheory.T.matched_spherical_pairs_commute_composite_lift R.toRealDat F.lv2 hC hS R.SF hSF A3.A.μ0 (R.pl P) hG _ _ (hmE k (Nat.lt_succ_iff.1 k.2)) hX hXo).2 c w hwE
  obtain ⟨x, hx, hxe⟩ := exists_sys_of_mem_span D.what₂.embLL (A3.rowI A3.A.μ0).opAll (R.jX A3.A.μ0)
    (fun k : Fin (D.sp.X'.rank + 1) => hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1))
    (fun k => Sum.inl ((⟨P, hP⟩ : A3.A.ok A3.A.μ0), (k : ℕ)))
    (fun k f => (GlobalTheory.T.familySplitOperators_eq_labelOperators_models R.toRealDat F.lv2 hC.lev hC.fam hC.models).1 A3.A.μ0 hX hXo ⟨P, hP⟩ k
      (Nat.lt_succ_iff.1 k.2) f)
    (fun k k' => hXn.1 _ _ hG hG _ _) _ _ (hcar.2 (Submodule.mem_map_of_mem hw)) hv0 _ heig

  have hE : (p.1.1 P).map D.what₂.embLL =
      (Formalism.L2.Col.heckePolyOf D.R.r (A3.A.q P) fun j => c (R.pl P) (dualLab (splitLab D.R.r j))).comp
        (C ((A3.A.q P : ℂ) ^ (D.R.m / 2 * D.R.t)) * X) := by
    have h1 := hpE fun j => c (R.pl P) (dualLab (splitLab (Yc D 0).rank j))
    have h2 : (Formalism.L2.Col.heckePolyOf (A3.A.r + D.R.m * A3.A.t) (A3.A.q P) fun k => x (Sum.inl (⟨P, hP⟩, k))) =
        p.1.1 P * (A3.A.fam.R A3.A.μ0).blockProd ⟨P, hP⟩ := hx.1 ⟨P, hP⟩
    have h3 := congrArg (Polynomial.map D.what₂.embLL) h2
    rw [Formalism.L2.Col.map_heckePolyOf, Polynomial.map_mul, ← hrX] at h3
    rw [GlobalTheory.Hk3.Link.heckePolyOf_congr _ _ (b := fun k => D.what₂.embLL (x (Sum.inl (⟨P, hP⟩, k)))) ?_, h3, hrY] at h1
    · refine mul_right_cancel₀ ?_ h1
      rw [Ne, Polynomial.map_eq_zero]
      unfold BlockDat.blockProd
      refine List.prod_ne_zero fun h => ?_
      obtain ⟨ν, -, hν⟩ := List.mem_map.1 h
      exact GlobalTheory.Hk3.Link.blockPoly_ne_zero _ _ _ hν
    · intro k hk
      have h5 := hxe ⟨k, Nat.lt_succ_iff.2 hk⟩
      exact (h5.trans (GlobalTheory.Hk3.Link.evC_splitC (Yc D 0) (R.pl P) hcj _ _)).symm

  obtain ⟨h, hEo, -, -, hev, -⟩ := GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R.toRealDat F.lv2 hC hS R.SF hSF
  have hne : R.HE.e w ≠ 0 := fun h0 => hw0 ((hC.models.HE).1 (h0.trans (map_zero _).symm))
  obtain ⟨v, hv⟩ : ∃ v, R.HE.e w v ≠ 0 := by
    by_contra hcon
    exact hne (MultilinearMap.ext fun v => not_not.1 fun hv => hcon ⟨v, hv⟩)
  obtain ⟨cc, hβ⟩ := hC.lev.βY 0 hm0
  have hlev := (GlobalTheory.T.level_operators_at_prime_off_level_datum (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hβ (R.pl P)
    (by
      have hN := ((GlobalTheory.T.theta_lift_levels_good_primes_properties R.toRealDat F.lv2 hC.lev).2.1 A3.A.μ0 (R.pl P) hG).1
      rw [Nat.cast_pow]
      intro hmem
      rcases Nat.eq_zero_or_pos cc with h0 | h0
      · rw [h0, pow_zero] at hmem
        exact (R.pl P).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hmem)
      · exact hN ((R.pl P).isPrime.mem_of_pow_mem _ hmem))
    (fun PP hPP => hG PP (Or.inl (hPP.resolve_right (Finset.notMem_empty _))))).1
  have hm := (Submodule.mem_inf.1 (Submodule.mem_comap.1 hwE)).1
  have hrel := GlobalTheory.Hk3.Link.eig_rel (Yc D 0) (R.pl P) hcj _ hv (fun k hk g =>
      (GlobalTheory.Hk3.Link.mult_lev R.θ _ _ _ _ hm v k (hlev k hk).1 g).trans
        ((congrArg (fun z : ℂ => z * R.HE.e w v g) (hlev k hk).2).trans (one_mul _)))
      (fun d => c (R.pl P) (dualLab d)) (fun d hd => by
      have h5 := (hEo (R.pl P) hG (Finsupp.single d 1) w).symm.trans
        ((congrArg R.HE.e (hev c _ hG (Finsupp.single d 1) w hwE)).trans (map_smul _ _ _))
      exact congrArg (fun U : MMap (R.MY 0) => U v) (h5.trans
        (congrArg (fun z : ℂ => z • R.HE.e w) (GlobalTheory.Hk3.Link.evC_single (Yc D 0) (R.pl P) _ d hd))))
  rw [hrY] at hrel
  simp only [dualLab_dualLab] at hrel
  obtain ⟨hb0, hab⟩ := hrel
  have hrr : c (R.pl P) (splitLab D.R.r D.R.r) * c (R.pl P) (dualLab (splitLab D.R.r D.R.r)) = 1 := by
    rw [hab D.R.r le_rfl, Nat.sub_self, hb0]
  have hbr : c (R.pl P) (dualLab (splitLab D.R.r D.R.r)) ≠ 0 := right_ne_zero_of_mul_eq_one hrr
  have ha0 : c (R.pl P) (splitLab D.R.r 0) = 1 := by
    have := hab 0 (Nat.zero_le _)
    rw [Nat.sub_zero] at this
    exact mul_right_cancel₀ hbr (this.trans (one_mul _).symm)
  have hba : ∀ j, j ≤ D.R.r → c (R.pl P) (dualLab (splitLab D.R.r j)) * c (R.pl P) (splitLab D.R.r D.R.r) =
      c (R.pl P) (splitLab D.R.r (D.R.r - j)) := by
    intro j hj
    have := hab (D.R.r - j) (Nat.sub_le _ _)
    rw [Nat.sub_sub_self hj] at this
    rw [← this, mul_assoc, mul_comm _ (c (R.pl P) (splitLab D.R.r D.R.r)), hrr, mul_one]
  have hdual := GlobalTheory.T.dualPoly_twistedHeckePoly_eq_contragredient ℂ D.R.r (A3.A.q P) (fun j => c (R.pl P) (splitLab D.R.r j))
    (fun j => c (R.pl P) (dualLab (splitLab D.R.r j))) ((A3.A.q P : ℂ) ^ (D.R.m / 2 * D.R.t)) 1 hq0
    (pow_ne_zero _ hq0) hr0 ha0 hba
  have hs0 : ((A3.A.q P : ℂ) ^ (D.R.m / 2 * D.R.t)) ≠ 0 := pow_ne_zero _ hq0
  constructor
  · unfold RealDat.polE
    rw [hE, Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ hs0, C_1, one_mul, Polynomial.comp_X]
  · unfold RealDat.polW
    rw [GlobalTheory.Hk3.Link.dualPoly_map, hE, map_pow, map_natCast]
    have hsc : (A3.A.q P : ℂ) ^ (D.R.r - 1 + D.R.m / 2 * D.R.t) =
        (A3.A.q P : ℂ) ^ (D.R.m / 2 * D.R.t) * 1 * (A3.A.q P : ℂ) ^ (D.R.r - 1) := by
      rw [pow_add]; ring
    rw [hsc, hdual, C_1, one_mul, Polynomial.comp_X]

end GlobalTheory.CarriedHecke
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AbLaw

theorem sec_eq_zero_of_local {X : Scheme.{0}} {L : LB X} {I : Type} (V : I → X.Opens)
    (hc : ⨆ a, V a = ⊤) (c : I → L.ι) (hV : ∀ a, V a ≤ L.U (c a)) (s : LB.Sec L)
    (h : ∀ a, rs X (hV a) (s.f (c a)) = 0) : s = 0 := by
  apply GlobalTheory.LB.f_injective
  funext i
  refine finSec_eq_zero_of_cover V hc (s.f i) fun a => ?_
  have h₁ : rs X (inf_le_left : L.U i ⊓ V a ≤ L.U i) (s.f i) =
      rs X (inf_le_inf le_rfl (hV a) : L.U i ⊓ V a ≤ L.U i ⊓ L.U (c a)) (L.g i (c a)).val *
        rs X (inf_le_right : L.U i ⊓ V a ≤ V a) (rs X (hV a) (s.f (c a))) := by
    have h := congrArg (rs X (inf_le_inf le_rfl (hV a) : L.U i ⊓ V a ≤ L.U i ⊓ L.U (c a)))
      (s.compat i (c a))
    rw [map_mul] at h
    simp only [rs_rs] at h ⊢
    exact h
  rw [h₁, h a, map_zero, mul_zero]

theorem sec_eq_of_local {X : Scheme.{0}} {L : LB X} {I : Type} (V : I → X.Opens)
    (hc : ⨆ a, V a = ⊤) (c : I → L.ι) (hV : ∀ a, V a ≤ L.U (c a)) (s t : LB.Sec L)
    (h : ∀ a, rs X (hV a) (s.f (c a)) = rs X (hV a) (t.f (c a))) : s = t :=
  sub_eq_zero.1 (sec_eq_zero_of_local V hc c hV _ fun a => by rw [GlobalTheory.LB.sub_f, map_sub, h a, sub_self])

section PerfSec

variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
  {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (Q : Perf f M) {g : R →+* R'} {π : X' ⟶ X}
  {f' : X' ⟶ Spec (CommRingCat.of R')}
  (E : {v : Fin Q.a → R' // (Q.D₀.map g).mulVec v = 0} ≃ LB.Sec (M.pull π))

theorem Perf.iSup_preimage : ⨆ i, π ⁻¹ᵁ Q.W i = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, Q.cover]
  exact top_unique fun _ _ => trivial


include Q in
theorem Perf.sec_add
    (hE : ∀ v i, rs X' (le_pull M π (Q.le i)) ((E v).f (fun _ => Q.ch i)) =
        ∑ k, cst f' (π ⁻¹ᵁ Q.W i) (v.1 k) * (π.app (Q.W i)).hom (Q.u k i))
    (v w : {v : Fin Q.a → R' // (Q.D₀.map g).mulVec v = 0}) :
    E ⟨v.1 + w.1, by rw [Matrix.mulVec_add, v.2, w.2, add_zero]⟩ = E v + E w := by
  refine sec_eq_of_local (fun i => π ⁻¹ᵁ Q.W i) Q.iSup_preimage (fun i => fun _ => Q.ch i)
    (fun i => le_pull M π (Q.le i)) _ _ fun i => ?_
  refine (hE _ i).trans (Eq.trans ?_ ((map_add (rs X' (le_pull M π (Q.le i))) ((E v).f fun _ => Q.ch i)
    ((E w).f fun _ => Q.ch i)).trans (congrArg₂ (· + ·) (hE v i) (hE w i))).symm)
  simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]


include Q in
theorem Perf.sec_smul
    (hE : ∀ v i, rs X' (le_pull M π (Q.le i)) ((E v).f (fun _ => Q.ch i)) =
        ∑ k, cst f' (π ⁻¹ᵁ Q.W i) (v.1 k) * (π.app (Q.W i)).hom (Q.u k i))
    (r : R') (v : {v : Fin Q.a → R' // (Q.D₀.map g).mulVec v = 0}) :
    E ⟨r • v.1, by rw [Matrix.mulVec_smul, v.2, smul_zero]⟩ = cst f' ⊤ r • E v := by
  refine sec_eq_of_local (fun i => π ⁻¹ᵁ Q.W i) Q.iSup_preimage (fun i => fun _ => Q.ch i)
    (fun i => le_pull M π (Q.le i)) _ _ fun i => ?_
  have key : rs X' (le_pull M π (Q.le i)) (resG X' le_top (cst f' ⊤ r)) = cst f' (π ⁻¹ᵁ Q.W i) r := by
    change rs X' _ (rs X' le_top _) = _
    rw [rs_rs, rs_cst]
  refine (hE _ i).trans (Eq.trans ?_ ((map_mul (rs X' (le_pull M π (Q.le i))) (resG X' le_top (cst f' ⊤ r))
    ((E v).f fun _ => Q.ch i)).trans (congrArg₂ (· * ·) key (hE v i))).symm)
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, _root_.mul_assoc]

end PerfSec

theorem finSecPullId_add {X : Scheme.{0}} {M : LB X} (s t : LB.Sec M) :
    finSecPullId (s + t) = finSecPullId s + finSecPullId t := by
  apply GlobalTheory.LB.f_injective
  funext j
  exact map_add _ _ _

theorem finSecPullId_smul {X : Scheme.{0}} {M : LB X} (a : Γ(X, ⊤)) (s : LB.Sec M) :
    finSecPullId (a • s) = a • finSecPullId s := by
  apply GlobalTheory.LB.f_injective
  funext j
  exact (map_mul _ _ _).trans (congrArg (· * _) (rs_rs _ _ _))

theorem eq_zero_of_finSecPullId {X : Scheme.{0}} {R : Type} [CommRing R]
    {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (Q : Perf f M) (s : LB.Sec M)
    (hs : finSecPullId s = 0) : s = 0 := by
  refine sec_eq_zero_of_local Q.W Q.cover Q.ch Q.le s fun j => ?_
  have hle : Q.W j ≤ (M.pull (𝟙 X)).U (fun _ => Q.ch j) :=
    le_trans (show Q.W j ≤ (𝟙 X) ⁻¹ᵁ Q.W j from fun _ hx => hx) (le_pull M (𝟙 X) (Q.le j))
  have h := congrArg (fun σ : LB.Sec (M.pull (𝟙 X)) => rs X hle (σ.f (fun _ => Q.ch j))) hs
  refine Eq.trans ?_ (h.trans (map_zero (rs X hle)))
  exact (rs_rs _ _ _).symm

end GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem exists_basis_sec_of_isDiscreteValuationRing : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of W)) (M : LB X), Flat f → GlobalTheory.AbLaw.IsProjBy f → M.IsLB → ∃ (n : ℕ) (t : Fin n → LB.Sec M), ∀ u : LB.Sec M, ∃! c : Fin n → W, u = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (c j) • t j := by
  intro W _ _ _ X f M hf hp hM
  obtain ⟨Q⟩ := nonempty_perf_of_noetherian W X f hf hp M hM
  have hpb : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id W))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.id_horiz f
  obtain ⟨E, hE⟩ := Q.sec W (RingHom.id W) X (𝟙 X) f hpb
  let φ : LB.Sec M → Fin Q.a → W := fun s => (E.symm (finSecPullId s)).1
  have hadd : ∀ s t, φ (s + t) = φ s + φ t := by
    intro s t
    have h := Q.sec_add E hE (E.symm (finSecPullId s)) (E.symm (finSecPullId t))
    rw [E.apply_symm_apply, E.apply_symm_apply, ← finSecPullId_add, ← E.eq_symm_apply] at h
    exact (congrArg Subtype.val h).symm
  have hsmul : ∀ (r : W) s, φ (cst f ⊤ r • s) = r • φ s := by
    intro r s
    have h := Q.sec_smul E hE r (E.symm (finSecPullId s))
    rw [E.apply_symm_apply, ← finSecPullId_smul, ← E.eq_symm_apply] at h
    exact (congrArg Subtype.val h).symm
  have φ0 : φ 0 = 0 := by
    have h := hsmul 0 0
    rwa [smul_zero, zero_smul] at h
  have hinj : ∀ s t, φ s = φ t → s = t := by
    intro s t h
    have hst : finSecPullId s = finSecPullId t := E.symm.injective (Subtype.ext h)
    have e := finSecPullId_add (s - t) t
    rw [sub_add_cancel, hst] at e
    have h2 : finSecPullId (s - t) = 0 := add_right_cancel (e.symm.trans (zero_add _).symm)
    exact sub_eq_zero.1 (eq_zero_of_finSecPullId Q _ h2)
  let N : Submodule W (Fin Q.a → W) :=
    { carrier := Set.range φ
      add_mem' := by
        rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
        exact ⟨s + t, hadd s t⟩
      zero_mem' := ⟨0, φ0⟩
      smul_mem' := by
        rintro r _ ⟨s, rfl⟩
        exact ⟨cst f ⊤ r • s, hsmul r s⟩ }
  have memN : ∀ s, φ s ∈ N := fun s => ⟨s, rfl⟩
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun W (Fin Q.a)) N
  have hb : ∀ j, ∃ s, φ s = (b j).1 := fun j => (b j).2
  choose t ht using hb
  let φh : LB.Sec M →+ (Fin Q.a → W) := { toFun := φ, map_zero' := φ0, map_add' := hadd }
  have hsum : ∀ c : Fin n → W, φ (∑ j, cst f ⊤ (c j) • t j) = ∑ j, c j • (b j).1 := by
    intro c
    change φh _ = _

    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => (hsmul (c j) (t j)).trans (by rw [ht])
  refine ⟨n, t, fun u => ⟨fun j => b.repr ⟨φ u, memN u⟩ j, ?_, ?_⟩⟩
  · apply hinj
    rw [hsum]
    have h := congrArg Subtype.val (b.sum_repr ⟨φ u, memN u⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  · intro c hc
    have h : (⟨φ u, memN u⟩ : N) = ∑ j, c j • b j := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [← hsum, ← hc]
    funext j
    rw [h, Module.Basis.repr_sum_self]

end GlobalTheory.AbLaw
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
noncomputable section

namespace GlobalTheory.Poinc.Origin
open GlobalTheory.UT.CoefBasic

theorem exists_sec_value_ne_zero : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ k : ℕ, 4 ≤ k → ∃ (t : SecA A F k) (c : F), c ≠ 0 ∧ ∀ z J, Good A.L z J → sA t (ptSecT A.A 1).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J).val := by
  intro hL R _ _ A F _ _ ρ hρ k hk
  obtain ⟨M, s, hcov⟩ := (hL.1.ample _ A k hk).1 ⊤ (isAffineOpen_top _)
  obtain ⟨i', hi⟩ : ∃ i' : A.A.left ⟶ (A.A.hom ⁻¹ᵁ ⊤).toScheme, i' ≫ (A.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨A.A.left.topIso.inv, A.A.left.topIso.inv_hom_id⟩
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  let χ : (TFK (R := R) F).left ⟶ (A.A.hom ⁻¹ᵁ ⊤).toScheme :=
    (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left ≫ i'
  have hmem : χ z ∈ (⨆ j, nonzeroLocus (s j)) := by rw [hcov]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  obtain ⟨t, ht⟩ := exists_sec A.isLB (φ := fun _ : Fin k => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => 1)
      (φ' := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε' := fun _ => (k : ℤ))
      (fun U _ f => by
        simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, zpow_natCast])
      (VVRank.pullTo (L := A.L) (φ := fun _ : Fin k => (A.A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
        ((snd (TFK (R := R) F) A.A).left ≫ i') (fun _ => by rw [Category.assoc, hi, Category.comp_id]))
  obtain ⟨c, hc⟩ := ThetaSpan.exists_value A hρ (F := F) (k := k) t
  refine ⟨t, c, ?_, hc⟩
  rintro rfl
  obtain ⟨J, hJ⟩ := exists_good' A.isLB (Z := (TFK (R := R) F).left) z
  have h1 := hc z J hJ
  have h0 : @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z 0) = 0 := by
    show cst (R := R) F z 0 = 0
    rw [cst_eq, map_zero]
  rw [h0, zero_mul] at h1
  have h2 : sA t (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left z J = sval (s j) χ z J :=
    (ht _ _ z J hJ).trans ((VVRank.sval_pullTo _ _ _ _ z hJ).trans (by simp only [χ, Category.assoc]))
  have hu : IsUnit (sval (s j) χ z J) :=
    (AmpleSpan.mem_nonzeroLocus_iff_gs (s j) χ z (hJ.mem (fun _ : Fin k => (A.A.hom ⁻¹ᵁ ⊤).ι) χ)).1 hj
  rw [← h2, h1] at hu
  exact not_isUnit_zero hu

end GlobalTheory.Poinc.Origin

end
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.harishChandra_capelli_uniform_diagonalBlocks : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (a r : ℕ) (hr : r ≤ a) (X : Fin a → Fin a → Module.End ℂ M), Formalism.REAL.GlRel X → ∀ M' K : Submodule ℂ M, (∀ i j, ∀ x ∈ M', X i j x ∈ M') → (∀ i j : Fin a, (i : ℕ) < r → r ≤ (j : ℕ) → ∀ x ∈ M', X i j x ∈ K) → (∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) → ∀ x ∈ K, X i j x ∈ K) → ∀ Q : ℂ → Polynomial ℂ, (∀ u, Q u ≠ 0) → ∃ q : ℂ → Polynomial ℂ, (∀ u, q u ≠ 0) ∧ ∀ v ∈ M', (∀ u, Polynomial.aeval (Formalism.REAL.qdet X u) (Q u) v = 0) → ∀ u, Polynomial.aeval (Formalism.REAL.qdet (fun p p' : Fin r => X (GlobalTheory.LeviGA.blkEquiv hr (Sum.inl p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inl p'))) u) (q u) v ∈ K ∧ Polynomial.aeval (Formalism.REAL.qdet (fun p p' : Fin (a - r) => X (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p'))) u) (q u) v ∈ K := by
  first | exact @GlobalTheory.LeviHC.CapAlg.capalg | exact GlobalTheory.LeviHC.CapAlg.capalg | (intros; apply GlobalTheory.LeviHC.CapAlg.capalg <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertPlace_stabilizer_two_factor_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∃ k₁ ∈ GlobalTheory.InertSph.KAt σ G.W v, ∃ k₂ ∈ GlobalTheory.InertSph.KAt σ G.W v,
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 + mat k₁) * M = 1 ∧ M * (1 + mat k₁) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 + mat k₂) * M = 1 ∧ M * (1 + mat k₂) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧ k = k₁ * k₂ := by
  first | exact @GlobalTheory.InertTwoFac.twoFac | exact GlobalTheory.InertTwoFac.twoFac | (intros; apply GlobalTheory.InertTwoFac.twoFac <;> assumption)
end
