module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle015
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle001
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem cos_bij {G : Type} [Group G] (K V U : Subgroup G) (hVK : V ≤ K) (hUV : U ≤ V) :
    Function.Bijective (fun p : (K ⧸ V.subgroupOf K) × (V ⧸ U.subgroupOf V) =>
      (((⟨(p.1.out : G) * (p.2.out : G), K.mul_mem p.1.out.2 (hVK p.2.out.2)⟩ : K)) : K ⧸ U.subgroupOf K)) := by
  constructor
  · rintro ⟨c, y⟩ ⟨c', y'⟩ h
    have h1 : ((c.out : G) * (y.out : G))⁻¹ * ((c'.out : G) * (y'.out : G)) ∈ U := by
      have := QuotientGroup.eq.1 h
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    have hc : c = c' := by
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : (((c.out)⁻¹ * c'.out : K) : G) =
          (y.out : G) * (((c.out : G) * (y.out : G))⁻¹ * ((c'.out : G) * (y'.out : G))) * (y'.out : G)⁻¹ := by
        push_cast; group
      rw [e]
      exact V.mul_mem (V.mul_mem y.out.2 (hUV h1)) (V.inv_mem y'.out.2)
    subst hc
    have hy : y = y' := by
      rw [← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' y']
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : (((y.out)⁻¹ * y'.out : V) : G) =
          ((c.out : G) * (y.out : G))⁻¹ * ((c.out : G) * (y'.out : G)) := by
        push_cast; group
      rw [e]; exact h1
    rw [hy]
  · intro a
    induction a using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul (V.subgroupOf K) a
      have hvV : ((v : K) : G) ∈ V := Subgroup.mem_subgroupOf.1 v.2
      let b : V := ⟨((v : K) : G)⁻¹, V.inv_mem hvV⟩
      obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf V) b
      have hwU : ((w : V) : G) ∈ U := Subgroup.mem_subgroupOf.1 w.2
      refine ⟨((a : K ⧸ V.subgroupOf K), (b : V ⧸ U.subgroupOf V)), ?_⟩
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : ((((⟨(((a : K ⧸ V.subgroupOf K).out : K) : G) * (((b : V ⧸ U.subgroupOf V).out : V) : G),
          K.mul_mem (a : K ⧸ V.subgroupOf K).out.2 (hVK (b : V ⧸ U.subgroupOf V).out.2)⟩ : K))⁻¹ * a : K) : G) =
          ((w : V) : G)⁻¹ := by
        simp only [hv, hw, b]
        push_cast
        group
      rw [e]; exact U.inv_mem hwU
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo PositivityTheory.AutomorphicGaloisHodgeTate.G8
universe u v

private theorem isTr_transport {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {Z Y : Scheme.{0}} {p : Z ⟶ B}
    {q q' : Y ⟶ B} (e : q = q') {s : Y ⟶ Z} {tr : T.H q →ₗ[R] T.H p} (h : T.IsTr p q s tr) :
    ∃ tr' : T.H q' →ₗ[R] T.H p, T.IsTr p q' s tr' ∧
      ∀ {X : Scheme.{0}} {r : X ⟶ B} (t : Y ⟶ X) (h₁ : t ≫ r = q) (h₂ : t ≫ r = q') (y : T.H r),
        tr' (T.pull t h₂ y) = tr (T.pull t h₁ y) := by
  subst e
  exact ⟨tr, h, fun _ _ _ _ => rfl⟩

private theorem low_square {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : GlobalTheory.GalV.HTower k}
    {θ : H.Γ → L} {C : Cover H θ O} (D : LowData C) (g : H.Γ) :
    IsPullback (pullback.fst (D.s g ≫ C.p) (gen O k)) ((low D).s g) (D.s g) (pullback.fst C.p (gen O k)) := by
  have hls : (low D).s g ≫ pullback.snd C.p (gen O k) = pullback.snd (D.s g ≫ C.p) (gen O k) :=
    bcMap_snd (gen O k) (D.s g) rfl
  have hlf : (low D).s g ≫ pullback.fst C.p (gen O k) = pullback.fst (D.s g ≫ C.p) (gen O k) ≫ D.s g :=
    bcMap_fst (gen O k) (D.s g) rfl
  refine IsPullback.of_bot ?_ hlf.symm (IsPullback.of_hasPullback C.p (gen O k))
  convert IsPullback.of_hasPullback (D.s g ≫ C.p) (gen O k) using 2
  exact hls

theorem UpperTheory.Gal.G3.jLowHodge :
    HodgeGood → BcGood.{0} → FEtBasic → HodgeOpBc → CoverInv.{0} → LiesOp.{0} → PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowHodge := by
  intro hHG hBG hFB hOB hCI hLO k L F _ _ _ _ φ ψ H θ O _ _ C D hN hO a hH
  unfold HOcc at hH ⊢
  unfold Nice at hN
  obtain ⟨b, x, hx, he⟩ := hH
  unfold IsHEig at he
  set T' := (hodge F a b).bc (Spec.map (CommRingCat.ofHom φ)) with hT'
  have hgood : T'.Good := hBG _ _ (hHG F a b)
  obtain ⟨hinj, hsurj⟩ := hCI C hO T' hgood
  have hH' : ∀ g : H.Γ, ∃ trg : T'.H (H.s g ≫ H.q) →ₗ[F] T'.H H.q,
      T'.IsTr H.q (H.s g ≫ H.q) (H.s g) trg ∧ trg (T'.pull (H.t g) (H.comm g) x) = ψ (θ g) • x := by
    intro g
    obtain ⟨d, hd⟩ := hN.2.2 g
    haveI : IsFinite (H.s g) := hd.1
    haveI : Etale (H.s g) := hd.2.1
    obtain ⟨i1, i2, tr, htr, heq⟩ := hOB k F φ H g a b
    obtain ⟨j1, j2, hg⟩ := he g
    exact ⟨tr, htr, (heq j1 j2 x).symm.trans hg⟩
  obtain ⟨z, hz⟩ := hsurj x (fun g _ hθ => by
    obtain ⟨trg, htr, heq⟩ := hH' g
    exact ⟨trg, htr, by rw [heq, hθ, map_one, one_smul]⟩)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hx (by rw [← hz]; exact map_zero _)
  refine ⟨b, z, hz0, ?_⟩
  unfold IsHEig
  intro g
  have hfet : FEt ((low D).s g) (D.d g) := hFB.1 _ _ _ _ _ (low_square D g) (D.fet g)
  haveI : IsFinite ((low D).s g) := hfet.1
  haveI : Etale ((low D).s g) := hfet.2.1
  obtain ⟨i1, i2, trL, htrL, heqL⟩ := hOB k F φ (low D) g a b
  refine ⟨i1, i2, ?_⟩
  rw [heqL i1 i2 z]
  obtain ⟨tr', htr', htrans⟩ := isTr_transport T' (q := (low D).s g ≫ (low D).q)
    (q' := pullback.snd (D.s g ≫ C.p) (gen O k)) (bcMap_snd (gen O k) (D.s g) rfl) htrL
  obtain ⟨trg, htrg, hgeq⟩ := hH' g
  have hlies := hLO C g (D.s g) (D.t g) (D.comm g) (D.m g) (D.d g) (D.lies g) hfet T' hgood tr' trg htr' htrg z
  rw [hz, hgeq, ← hz, ← map_smul] at hlies
  have h := hinj ((map_smul (T'.pull (piK C) _) (ψ (θ g)) z).trans hlies)
  have h₂ : bcMap (gen O k) (D.t g) (D.comm g) ≫ (low D).q = pullback.snd (D.s g ≫ C.p) (gen O k) :=
    ((low D).comm g).trans (bcMap_snd (gen O k) (D.s g) rfl)
  have h3 : tr' (T'.pull (bcMap (gen O k) (D.t g) (D.comm g)) h₂ z) =
      trL (T'.pull ((low D).t g) ((low D).comm g) z) := htrans ((low D).t g) ((low D).comm g) h₂ z
  have h' : ψ (θ g) • z = ((D.m g : ℕ) : F) • trL (T'.pull ((low D).t g) ((low D).comm g) z) :=
    h.trans (congrArg (fun w => ((D.m g : ℕ) : F) • w) h3)
  have hm : ((D.m g : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (D.lies g).1.ne'
  have hw : trL (T'.pull ((low D).t g) ((low D).comm g) z) = ψ (θ g / (D.m g : L)) • z := by
    rw [map_div₀, map_natCast, div_eq_inv_mul, mul_smul, h']
    exact (inv_smul_smul₀ hm _).symm
  exact hw
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

theorem UpperTheory.Gal.G3.jTrBc :
    BcSplits → TrBc.{u} := by
  intro hbc B B' R _ T g Z Y p q s _ _ hs tr htr W r c hc J _ σ hσ hspl x
  have key := (hbc g p q r s hs c hc J σ hσ).2.2 hspl
  exact htr (pullback r g) (pullback.snd r g) (bcMap g c hc) (bcMap_snd g c hc) J
    (fun j => bcMap g (σ j) (hσ j)) (fun j => bcMap_snd g (σ j) (hσ j)) key x
end
