module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem mem_lev {G : Type} [Group G] {K : Subgroup G} {h u : G} :
    u ∈ lev K h ↔ u ∈ K ∧ h * u * h⁻¹ ∈ K := (Iff.rfl)

private theorem ind_eq_one {G : Type} [Group G] (R : Type) [Field R] {K : Subgroup G} {g x : G}
    (hx : x ∈ DoubleCoset.doubleCoset g (K : Set G) K) : ind R K g x = 1 := by
  simp [ind, Set.indicator_of_mem hx]

private theorem ind_eq_zero {G : Type} [Group G] (R : Type) [Field R] {K : Subgroup G} {g x : G}
    (hx : x ∉ DoubleCoset.doubleCoset g (K : Set G) K) : ind R K g x = 0 := by
  simp [ind, Set.indicator_of_notMem hx]

private theorem class_eq {G : Type} [Group G] {K : Subgroup G} {h : G}
    (p : K) (b : K ⧸ (lev K h).subgroupOf K) (e : (QuotientGroup.mk p : K ⧸ (lev K h).subgroupOf K) = b) :
    (QuotientGroup.mk ((p : G) * h⁻¹) : G ⧸ K) = QuotientGroup.mk (((b.out : K) : G) * h⁻¹) := by
  subst e
  have h0 : (p⁻¹ * (QuotientGroup.mk p : K ⧸ (lev K h).subgroupOf K).out : K) ∈ (lev K h).subgroupOf K :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm
  have h1 := (mem_lev.mp (Subgroup.mem_subgroupOf.mp h0)).2
  rw [QuotientGroup.eq]
  convert h1 using 1
  push_cast
  group

private theorem fib_inj {G : Type} [Group G] {K : Subgroup G} {h : G}
    (b b' : K ⧸ (lev K h).subgroupOf K)
    (e : (QuotientGroup.mk (((b.out : K) : G) * h⁻¹) : G ⧸ K) = QuotientGroup.mk (((b'.out : K) : G) * h⁻¹)) :
    b = b' := by
  rw [QuotientGroup.eq] at e
  rw [← QuotientGroup.out_eq' b, ← QuotientGroup.out_eq' b', QuotientGroup.eq, Subgroup.mem_subgroupOf, mem_lev]
  refine ⟨(b.out⁻¹ * b'.out).2, ?_⟩
  convert e using 1
  push_cast
  group

private theorem count {G : Type} [Group G] {R : Type} {M : Type v} [Field R] [AddCommGroup M] [Module R M]
    (K K' : Subgroup G) (h : G) (hle : K' ≤ lev K h) [Finite (K ⧸ K'.subgroupOf K)] [Fintype (K ⧸ K'.subgroupOf K)]
    (φ : G ⧸ K → M) :
    ∑ a : K ⧸ K'.subgroupOf K, φ (QuotientGroup.mk (((a.out : K) : G) * h⁻¹)) =
      K'.relIndex (lev K h) • ∑ᶠ y : G ⧸ K, (ind R K h⁻¹ y.out) • φ y := by
  classical
  have hLK : lev K h ≤ K := inf_le_left
  have hle' : K'.subgroupOf K ≤ (lev K h).subgroupOf K := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_subgroupOf.mp hx))
  let e := Subgroup.quotientEquivProdOfLE hle'
  haveI : Finite ((K ⧸ (lev K h).subgroupOf K) ×
      ((lev K h).subgroupOf K ⧸ (K'.subgroupOf K).subgroupOf ((lev K h).subgroupOf K))) :=
    Finite.of_equiv _ e
  haveI : Nonempty ((lev K h).subgroupOf K ⧸ (K'.subgroupOf K).subgroupOf ((lev K h).subgroupOf K)) :=
    ⟨QuotientGroup.mk 1⟩
  haveI : Nonempty (K ⧸ (lev K h).subgroupOf K) := ⟨QuotientGroup.mk 1⟩
  haveI : Finite (K ⧸ (lev K h).subgroupOf K) :=
    Finite.prod_left ((lev K h).subgroupOf K ⧸ (K'.subgroupOf K).subgroupOf ((lev K h).subgroupOf K))
  haveI : Finite ((lev K h).subgroupOf K ⧸ (K'.subgroupOf K).subgroupOf ((lev K h).subgroupOf K)) :=
    Finite.prod_right (K ⧸ (lev K h).subgroupOf K)
  letI := Fintype.ofFinite (K ⧸ (lev K h).subgroupOf K)
  letI := Fintype.ofFinite ((lev K h).subgroupOf K ⧸ (K'.subgroupOf K).subgroupOf ((lev K h).subgroupOf K))
  have key : ∀ a, (e a).1 = QuotientGroup.mk (a.out : K) := by
    intro a
    conv_lhs => rw [← QuotientGroup.out_eq' a]
    rfl
  have hcard : Fintype.card ((lev K h).subgroupOf K ⧸ (K'.subgroupOf K).subgroupOf ((lev K h).subgroupOf K)) =
      K'.relIndex (lev K h) := by
    rw [← Nat.card_eq_fintype_card]
    exact Subgroup.relIndex_subgroupOf hLK
  have hψ : Function.Injective
      (fun b : K ⧸ (lev K h).subgroupOf K => (QuotientGroup.mk (((b.out : K) : G) * h⁻¹) : G ⧸ K)) :=
    fun b b' hb => fib_inj b b' hb
  have hR : ∑ᶠ y : G ⧸ K, (ind R K h⁻¹ y.out) • φ y =
      ∑ b : K ⧸ (lev K h).subgroupOf K, φ (QuotientGroup.mk (((b.out : K) : G) * h⁻¹)) := by
    rw [finsum_eq_sum_of_support_subset (s := Finset.univ.image
      (fun b : K ⧸ (lev K h).subgroupOf K => (QuotientGroup.mk (((b.out : K) : G) * h⁻¹) : G ⧸ K))) _ ?sub]
    · rw [Finset.sum_image (fun b _ b' _ hb => hψ hb)]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (((b.out : K) : G) * h⁻¹)
      have hm : (QuotientGroup.mk (((b.out : K) : G) * h⁻¹) : G ⧸ K).out ∈
          DoubleCoset.doubleCoset h⁻¹ (K : Set G) K := by
        rw [hk, DoubleCoset.mem_doubleCoset]
        exact ⟨b.out, b.out.2, k, k.2, rfl⟩
      rw [ind_eq_one R hm, one_smul]
    · intro y hy
      rw [Function.mem_support] at hy
      have hm : y.out ∈ DoubleCoset.doubleCoset h⁻¹ (K : Set G) K := by
        by_contra hn
        rw [ind_eq_zero R hn, zero_smul] at hy
        exact hy rfl
      obtain ⟨k1, hk1, k2, hk2, he⟩ := DoubleCoset.mem_doubleCoset.mp hm
      refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨QuotientGroup.mk ⟨k1, hk1⟩, Finset.mem_univ _, ?_⟩)
      show (QuotientGroup.mk ((((QuotientGroup.mk ⟨k1, hk1⟩ : K ⧸ (lev K h).subgroupOf K).out : K) : G) * h⁻¹) :
        G ⧸ K) = y
      rw [← class_eq ⟨k1, hk1⟩ _ rfl, ← QuotientGroup.out_eq' y, he, QuotientGroup.eq]
      have hk2' : k2 ∈ K := hk2
      show (k1 * h⁻¹)⁻¹ * (k1 * h⁻¹ * k2) ∈ K
      simpa [mul_assoc] using hk2'
  calc ∑ a : K ⧸ K'.subgroupOf K, φ (QuotientGroup.mk (((a.out : K) : G) * h⁻¹))
      = ∑ a : K ⧸ K'.subgroupOf K, φ (QuotientGroup.mk ((((e a).1.out : K) : G) * h⁻¹)) :=
        Finset.sum_congr rfl (fun a _ => congrArg φ (class_eq a.out (e a).1 (key a).symm))
    _ = ∑ x : (K ⧸ (lev K h).subgroupOf K) ×
          ((lev K h).subgroupOf K ⧸ (K'.subgroupOf K).subgroupOf ((lev K h).subgroupOf K)),
          φ (QuotientGroup.mk (((x.1.out : K) : G) * h⁻¹)) :=
        Equiv.sum_comp e (fun x => φ (QuotientGroup.mk (((x.1.out : K) : G) * h⁻¹)))
    _ = Fintype.card ((lev K h).subgroupOf K ⧸ (K'.subgroupOf K).subgroupOf ((lev K h).subgroupOf K)) •
          ∑ b : K ⧸ (lev K h).subgroupOf K, φ (QuotientGroup.mk (((b.out : K) : G) * h⁻¹)) := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, Finset.smul_sum]
    _ = _ := by rw [hcard, hR]

private theorem isOp_of {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {Z Y Z' W : Scheme.{0}} (p : Z ⟶ B)
    (p' : Z' ⟶ B) (s : Y ⟶ Z) (t : Y ⟶ Z') (A : T.H p' →ₗ[R] T.H p) (r : W ⟶ B) (c : W ⟶ Z) (hc : c ≫ p = r)
    (Γ : Type) [Group Γ] [Finite Γ] (a : Γ → (W ⟶ W)) (J : Type) [Fintype J] (σ : J → (W ⟶ Y))
    (h : ∀ j, (σ j ≫ t) ≫ p' = r) (h1 : IsGalois c Γ a) (h2 : Splits s c σ)
    (h3 : ∀ x, T.pull c hc (A x) = ∑ j, T.pull (σ j ≫ t) (h j) x) : T.IsOp p p' s t A := by
  subst hc
  exact ⟨W, c, Γ, inferInstance, inferInstance, a, J, inferInstance, σ, h, h1, h2, h3⟩

private theorem pull_eq {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {Y Z : Scheme.{0}} {p : Z ⟶ B} {q : Y ⟶ B}
    {f g : Y ⟶ Z} (e : f = g) (hf : f ≫ p = q) (hg : g ≫ p = q) (x : T.H p) : T.pull f hf x = T.pull g hg x := by
  subst e
  rfl

theorem UpperTheory.Gal.G3.pHopOp :
    FnRing → HopEx.{u} → TwSplit → TwGal → HopOp.{u} := by
  intro hF hE hS hG B G _ X R _ _ T hT i j h a b
  classical
  have hij : X.K i ≤ X.K j := fun u hu => by simpa using a.2 u hu
  have hil : X.K i ≤ lev (X.K j) h := fun u hu => mem_lev.mpr ⟨hij hu, b.2 u hu⟩
  have hL : lev (X.K j) h ≤ X.K j := inf_le_left
  have hn : (X.K i).relIndex (lev (X.K j) h) ≠ 0 := by
    have := X.idx i j
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ hil hL] at this
    exact left_ne_zero_of_mul this
  refine ⟨hn, ?_⟩
  obtain ⟨m, hmj, hnorm, hS'⟩ := X.deep j {(i, (1 : G))}
  have hmi : X.K m ≤ X.K i := fun u hu => by
    simpa using hS' (i, 1) (Finset.mem_singleton_self _) u hu
  haveI : Finite (X.K j ⧸ (X.K i).subgroupOf (X.K j)) := Nat.finite_of_card_ne_zero (X.idx i j)
  letI : Fintype (X.K j ⧸ (X.K i).subgroupOf (X.K j)) := Fintype.ofFinite _
  have bm : X.admitted m j 1 := X.isAdmissibleIntegralBasisChange_one hmj
  have bmi : X.admitted m i 1 := X.isAdmissibleIntegralBasisChange_one hmi
  have admr : ∀ c : X.K j ⧸ (X.K i).subgroupOf (X.K j), X.admitted m i ((c.out : G))⁻¹ := fun c =>
    ⟨X.K_le j _ (inv_mem c.out.2), fun u hu => hmi (hnorm _ (inv_mem c.out.2) u hu)⟩
  obtain ⟨Γ, _, _, r', c', -, -, hgal⟩ := hG X m j bm hnorm
  have hsplit := hS X m i j a bm hmi hnorm (X.K j ⧸ (X.K i).subgroupOf (X.K j))
    (fun c => ((c.out : G))⁻¹) admr (fun c => inv_mem c.out.2) (by
      intro k hk
      refine ⟨QuotientGroup.mk ⟨k⁻¹, inv_mem hk⟩, ?_, ?_⟩
      · obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul ((X.K i).subgroupOf (X.K j)) (⟨k⁻¹, inv_mem hk⟩ : X.K j)
        simp only [inv_inv]
        rw [hu]
        have hu' : ((u : X.K j) : G) ∈ X.K i := Subgroup.mem_subgroupOf.mp u.2
        simpa [mul_assoc] using hu'
      · intro c hc
        simp only [inv_inv] at hc
        rw [← QuotientGroup.out_eq' c, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa [mul_inv_rev] using inv_mem hc)
  have hσ : ∀ c : X.K j ⧸ (X.K i).subgroupOf (X.K j),
      (X.tr m i ((c.out : G))⁻¹ (admr c).1 (admr c).2 ≫ X.tr i j h b.1 b.2) ≫ X.q j = X.q m := by
    intro c
    rw [Category.assoc, X.tr_q, X.tr_q]
  have hfn : X.IsFn j (ind R (X.K j) h⁻¹) := (hF X R j).1 h b.1
  have hhop := (hE X T hT j _ hfn).1
  have hadm : ∀ g : G, ind R (X.K j) h⁻¹ g ≠ 0 → X.admitted m j g⁻¹ := by
    intro g hg
    have hm : g ∈ DoubleCoset.doubleCoset h⁻¹ (X.K j : Set G) (X.K j) := by
      by_contra hn'
      exact hg (ind_eq_zero R hn')
    obtain ⟨k1, hk1, k2, hk2, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hm
    have e1 : (k1 * h⁻¹ * k2)⁻¹ = k2⁻¹ * (h * (1 * k1⁻¹)) := by group
    rw [e1]
    have hk1' : k1⁻¹ ∈ X.K j := inv_mem hk1
    have hk2' : k2⁻¹ ∈ X.K j := inv_mem hk2
    have a1 : X.admitted m m k1⁻¹ := ⟨X.K_le j _ hk1', fun u hu => hnorm _ hk1' u hu⟩
    exact Tower.admitted.mul (Tower.admitted.mul (Tower.admitted.mul a1 bmi) b) (X.tower_admissible_self hk2')
  show T.IsOp (X.q j) (X.q j) _ _ _
  refine isOp_of T _ _ _ _ _ (X.q m) (X.tr m j 1 bm.1 bm.2) (X.tr_q _ _ _ _ _) Γ _
    (X.K j ⧸ (X.K i).subgroupOf (X.K j))
    (fun c => X.tr m i ((c.out : G))⁻¹ (admr c).1 (admr c).2) hσ hgal hsplit ?_
  intro x
  have hφ : ∀ c : X.K j ⧸ (X.K i).subgroupOf (X.K j),
      T.pull (X.tr m i ((c.out : G))⁻¹ (admr c).1 (admr c).2 ≫ X.tr i j h b.1 b.2) (hσ c) x =
        X.pl T m j ((QuotientGroup.mk ((c.out : G) * h⁻¹) : G ⧸ X.K j).out)⁻¹ x := by
    intro c
    have adm1 : X.admitted m j (h * ((c.out : G))⁻¹) := Tower.admitted.mul (admr c) b
    rw [pull_eq T (X.tr_mul _ _ _ _ _ _ _ _ _ adm1.1 adm1.2) _ (X.tr_q _ _ _ _ _), ← X.pl_eq T adm1]
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (X.K j) ((c.out : G) * h⁻¹)
    rw [hu]
    have e2 : ((c.out : G) * h⁻¹ * u)⁻¹ = (u : G)⁻¹ * (h * (c.out : G)⁻¹) := by group
    rw [e2, X.pl_left T adm1 (inv_mem u.2)]
  have hc := count (R := R) (X.K j) (X.K i) h hil (fun y : G ⧸ X.K j => X.pl T m j (y.out)⁻¹ x)
  beta_reduce at hc
  rw [Finset.sum_congr rfl (fun c _ => hφ c), hc, LinearMap.smul_apply, map_smul, ← X.pl_eq T bm,
    hhop m hmj hadm x]
  simp [Nat.cast_smul_eq_nsmul]
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem bcMap_isPullback {B B' X Y : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} (f : Y ⟶ X)
    (h : f ≫ p = q) : IsPullback (pullback.fst q g) (bcMap g f h) f (pullback.fst p g) := by
  subst h
  refine IsPullback.of_bot ?_ (bcMap_fst g f rfl).symm (IsPullback.of_hasPullback p g)
  rw [bcMap_snd]
  exact IsPullback.of_hasPullback (f ≫ p) g

theorem UpperTheory.Gal.G3.pBcGal :
    BcSplits → BcGal := by
  intro hB B B' Z W g p r c hc G _ _ a ha hG
  obtain ⟨hfin, het, hsur, h1, hmul, hsp⟩ := hG
  obtain ⟨f1, f2, f3⟩ := @hB B B' Z W W g p r r c hc c hc G _ a ha hfin het
  refine ⟨f1, f2, ?_, ?_, ?_, f3 hsp⟩
  · exact MorphismProperty.of_isPullback (P := @Surjective) (bcMap_isPullback g c hc) hsur
  · apply pullback.hom_ext
    · rw [bcMap_fst, h1, Category.comp_id, Category.id_comp]
    · rw [bcMap_snd, Category.id_comp]
  · intro x y
    apply pullback.hom_ext
    · rw [bcMap_fst, Category.assoc, bcMap_fst, ← Category.assoc, bcMap_fst, Category.assoc, hmul]
    · rw [bcMap_snd, Category.assoc, bcMap_snd, bcMap_snd]
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pBcGood :
    BcSplits → BcGal → BcGood.{u} := by
  intro hS hG B B' R _ T g hT
  refine ⟨?_, ?_⟩
  · intro Z W p r c hc G _ _ a hgal
    have ha : ∀ x, a x ≫ r = r := fun x => by
      rw [← hc, ← Category.assoc, hgal.2.2.2.2.2.1 x]
    exact hT.inj (pullback.snd p g) (pullback.snd r g) (bcMap g c hc) (bcMap_snd g c hc) G
      (fun x => bcMap g (a x) (ha x)) (hG g p r c hc G a ha hgal)
  · intro Z Y p q s _ _ hs
    obtain ⟨hfin, het, -⟩ := hS g p q q s hs s hs Empty Empty.elim (fun j => j.elim)
    obtain ⟨tr, htr⟩ := hT.tr (pullback.snd p g) (pullback.snd q g) (bcMap g s hs) (bcMap_snd g s hs)
    refine ⟨tr, ?_⟩
    intro W r c hc J _ σ hσ hspl x
    exact htr (pullback r g) (pullback.snd r g) (bcMap g c hc) (bcMap_snd g c hc) J
      (fun j => bcMap g (σ j) (hσ j)) (fun j => bcMap_snd g (σ j) (hσ j))
      ((hS g p q r s hs c hc J σ hσ).2.2 hspl) x
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pEtGood :
    EtnGood → EtGood := by
  intro hE l _ B hl
  have hn := fun n => hE l B hl n 0
  refine ⟨?_, ?_⟩
  · intro Z W p r c hc G _ _ a hgal x y hxy
    refine DFinsupp.ext fun n => ?_
    have h1 := congrArg (fun v : Htot l (sch.obj W) => v n) hxy
    exact (hn n).inj p r c hc G a hgal h1
  · intro Z Y p q s _ _ hs
    choose tr htr using fun n => (hn n).tr p q s hs
    let tr' : ∀ n, HQ l (sch.obj Y) n 0 →ₗ[ℚ_[l]] HQ l (sch.obj Z) n 0 := fun n => tr n
    refine ⟨DirectSum.lmap tr', ?_⟩
    intro W r c hc J _ σ hσ hsp
    refine fun (x : Htot l (sch.obj Y)) => DFinsupp.ext fun n => ?_
    have h1 := htr n W r c hc J σ hσ hsp (x n)
    exact h1.trans (DirectSum.sum_apply Finset.univ
      (fun j => ((et l B).pull (σ j) (hσ j)) x) n).symm
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pOpEt :
    OpEt := by
  intro l _ B Z Y Z' p p' s t hst A
  constructor
  · rintro ⟨W, c, G, i1, hG, a, J, i2, σ, _hh, hrest⟩
    exact ⟨W, c, G, i1, hG, a, J, i2, σ, hrest⟩
  · rintro ⟨W, c, G, i1, hG, a, J, i2, σ, hrest⟩
    exact ⟨W, c, G, i1, hG, a, J, i2, σ,
      fun j => by rw [Category.assoc, hst, ← Category.assoc, hrest.2.1.1 j], hrest⟩
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pOpEx :
    OpTr.{u} → OpEx.{u} := by
  intro hTr B R _ T hG Z Y Z' p p' s _ _ t hcomm
  obtain ⟨tr, htr⟩ := hG.tr p (s ≫ p) s rfl
  have key := fun A => hTr T hG p (s ≫ p) p' s t rfl hcomm tr htr A
  refine ⟨fun hgs => ⟨tr ∘ₗ T.pull t hcomm, (key _).2 hgs rfl, fun A hA => (key A).1 hA⟩, ?_⟩
  intro A hA W r c hc J _ σ h hsp x
  have hσ : ∀ j, σ j ≫ (s ≫ p) = r := by
    intro j
    rw [← hcomm, ← Category.assoc]
    exact h j
  rw [(key A).1 hA, LinearMap.comp_apply, htr W r c hc J σ hσ hsp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [T.pull_comp (σ j) t (hσ j) hcomm]
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem pullIdentity_move {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {W Z Z' : Scheme.{0}}
    {p : Z ⟶ B} {p' : Z' ⟶ B} {r r' : W ⟶ B} (e : r = r') (c : W ⟶ Z) {J : Type} [Fintype J]
    (t : J → (W ⟶ Z')) (y : T.H p) (x : T.H p') (h : c ≫ p = r) (h' : c ≫ p = r')
    (k : ∀ j, t j ≫ p' = r) (k' : ∀ j, t j ≫ p' = r')
    (H : T.pull c h y = ∑ j, T.pull (t j) (k j) x) :
    T.pull c h' y = ∑ j, T.pull (t j) (k' j) x := by
  subst e
  exact H

private theorem pull_congr {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {X Y : Scheme.{0}}
    {p : X ⟶ B} {q : Y ⟶ B} {f f' : Y ⟶ X} (e : f = f') (h : f ≫ p = q) (h' : f' ≫ p = q) (x : T.H p) :
    T.pull f h x = T.pull f' h' x := by
  subst e
  rfl

private theorem bcMap_comp' {B B' X Y V : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} {r : V ⟶ B'}
    (f : Y ⟶ X) (f' : V ⟶ Y) (h : f ≫ p = q) (h' : f' ≫ q = r) (h'' : (f' ≫ f) ≫ p = r) :
    bcMap g (f' ≫ f) h'' = bcMap g f' h' ≫ bcMap g f h := by
  apply pullback.hom_ext
  · rw [bcMap_fst, Category.assoc, bcMap_fst, ← Category.assoc (bcMap g f' h'), bcMap_fst,
      Category.assoc]
  · rw [bcMap_snd, Category.assoc, bcMap_snd, bcMap_snd]

theorem UpperTheory.Gal.G3.pOpBc :
    BcSplits → BcGal → OpBc.{u} := by
  intro hS hG B B' R _ T g Z Y Z' p q p' s _ _ t hs ht A hA
  obtain ⟨W, c, G, _, _, a, J, _, σ, hh, hgal, hspl, hsum⟩ := hA
  have hσ : ∀ j, σ j ≫ q = c ≫ p := fun j => by
    rw [← hs, ← Category.assoc, hspl.1 j]
  have ha : ∀ x, a x ≫ (c ≫ p) = c ≫ p := fun x => by
    rw [← Category.assoc, hgal.2.2.2.2.2.1 x]
  refine ⟨pullback (c ≫ p) g, bcMap g c rfl, G, inferInstance, inferInstance,
    fun x => bcMap g (a x) (ha x), J, inferInstance, fun j => bcMap g (σ j) (hσ j), ?_,
    hG g p (c ≫ p) c rfl G a ha hgal, (hS g p q (c ≫ p) s hs c rfl J σ hσ).2.2 hspl, ?_⟩
  · intro j
    rw [Category.assoc, bcMap_snd, bcMap_snd, bcMap_snd]
  · intro x
    have e : T.pull (bcMap g c rfl) (bcMap_snd g c rfl) (A x) =
        ∑ j, T.pull (bcMap g (σ j ≫ t) (hh j)) (bcMap_snd g _ (hh j)) x := hsum x
    have e2 : T.pull (bcMap g c rfl) (bcMap_snd g c rfl) (A x) =
        ∑ j, T.pull (bcMap g (σ j) (hσ j) ≫ bcMap g t ht)
          (by rw [Category.assoc, bcMap_snd, bcMap_snd]) x := by
      rw [e]
      exact Finset.sum_congr rfl fun j _ =>
        pull_congr T (bcMap_comp' g t (σ j) ht (hσ j) _) _ _ x
    exact pullIdentity_move T (bcMap_snd g c rfl).symm _ _ _ _ _ _ _ _ e2
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pEtTr :
    EtTr := by
  intro l _ B hl n i Z Y p q s _ _ W r c hc J _ σ hσ hsp x
  obtain ⟨hsc, hiso⟩ := hsp
  have hT := UpperTheory.Gal.TranscendenceTraces.adic.2.2.2.2.2.2.2.2.2
  let e := Fintype.equivFin J
  have hiso' : IsIso (Sigma.desc fun k : Fin (Fintype.card J) =>
      pullback.lift (σ (e.symm k)) (𝟙 W) (by rw [hsc, Category.id_comp])) := by
    have hEq : (Sigma.desc fun k : Fin (Fintype.card J) =>
        pullback.lift (σ (e.symm k)) (𝟙 W) (by rw [hsc, Category.id_comp])) =
        (Sigma.reindex e.symm (fun _ : J => W)).hom ≫
          Sigma.desc fun j => pullback.lift (σ j) (𝟙 W) (by rw [hsc, Category.id_comp]) := by
      refine Sigma.hom_ext _ _ (fun k => ?_)
      rw [Sigma.ι_desc]
      have h4 := Sigma.ι_reindex_hom_assoc (ε := e.symm) (f := fun _ : J => W) (b := k)
        (h := Sigma.desc fun j => pullback.lift (σ j) (𝟙 W) (by rw [hsc, Category.id_comp]))
      rw [Sigma.ι_desc] at h4
      exact h4.symm
    rw [hEq]
    infer_instance
  have hlZ : IsUnit ((l : Γ(Z, ⊤))) := by
    simpa using hl.map (Scheme.Hom.appTop p).hom
  have h1 := hT l n i s hlZ W c (Fintype.card J) (fun k => σ (e.symm k)) (fun k => hsc _) hiso'
  have h2 : ∀ y : HQ l (sch.obj Y) n i, pullHQ l (sch.map c) n i
      (TranscendenceTraces.trHQ l s (TranscendenceTraces.Wt.const Y 1) n i y) = ∑ j, pullHQ l (sch.map (σ j)) n i y := by
    intro y
    have h3 := LinearMap.congr_fun h1 y
    rw [LinearMap.comp_apply, LinearMap.sum_apply] at h3
    rw [h3]
    exact Equiv.sum_comp e.symm (fun j => pullHQ l (sch.map (σ j)) n i y)
  exact h2 x
end
