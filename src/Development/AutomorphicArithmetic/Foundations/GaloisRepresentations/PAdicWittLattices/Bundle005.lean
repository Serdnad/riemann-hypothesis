module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pExtPts :
    ExtPts := by
  intro W Z B _ p _ f g hfg hpt
  let X' : Over B := Over.mk (f ≫ p)
  let Y' : Over B := Over.mk p
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g hfg.symm
  have : IsSeparated Y'.hom := ‹_›
  have hsurj : Surjective (equalizer.ι f' g').left := by
    constructor
    intro x
    let K := W.residueField x
    let Ω := AlgebraicClosure K
    let y : Spec (CommRingCat.of Ω) ⟶ W :=
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ W.fromSpecResidueField x
    have hy : y ≫ f = y ≫ g := hpt Ω y
    let U' : Over B := Over.mk (y ≫ f ≫ p)
    let y' : U' ⟶ X' := Over.homMk y
    have hy' : y' ≫ f' = y' ≫ g' := by
      ext1
      exact hy
    let pt : Spec (CommRingCat.of Ω) := IsLocalRing.closedPoint Ω
    refine ⟨(equalizer.lift y' hy').left pt, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
    show (Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ W.fromSpecResidueField x) pt = x
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have := isIso_of_isClosedImmersion_of_surjective (Y := W) (equalizer.ι f' g').left
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem exists_factor {W : Scheme.{0}} {J : Type} (Ω : Type) [Field Ω]
    (p : UpperTheory.Gal.G3.sp Ω ⟶ ∐ (fun _ : J => W)) :
    ∃ (j : J) (x : UpperTheory.Gal.G3.sp Ω ⟶ W), p = x ≫ Sigma.ι (fun _ : J => W) j := by
  haveI : Subsingleton ↑(UpperTheory.Gal.G3.sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  have pt : ↑(UpperTheory.Gal.G3.sp Ω) := show PrimeSpectrum Ω from ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨⟨j, y⟩, hq⟩ : ∃ q, (sigmaMk (fun _ : J => W)).symm (p pt) = q := ⟨_, rfl⟩
  have hy : Sigma.ι (fun _ : J => W) j y = p pt := by
    rw [← sigmaMk_mk, ← hq, Homeomorph.apply_symm_apply]
  refine ⟨j, IsOpenImmersion.lift (Sigma.ι (fun _ : J => W) j) p ?_,
    (IsOpenImmersion.lift_fac _ _ _).symm⟩
  rintro _ ⟨z, rfl⟩
  obtain rfl : z = pt := Subsingleton.elim _ _
  exact ⟨y, hy⟩

theorem UpperTheory.Gal.G3.pSplitsPts :
    IsoPts → SplitsPts := by
  intro hIso Z Y W s _ _ c J _ σ hσ hpts
  refine ⟨hσ, ?_⟩
  let e := Limits.Sigma.desc (fun j : J =>
    pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j))
  have hι : ∀ j, Sigma.ι (fun _ : J => W) j ≫ e =
      pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j) :=
    fun j => Sigma.ι_desc _ _
  have hlift : ∀ j, Etale (pullback.lift (σ j) (𝟙 W)
      (by rw [Category.id_comp]; exact hσ j) : W ⟶ pullback s c) := by
    intro j
    haveI : Etale (pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j) ≫
        pullback.snd s c) := by
      rw [pullback.lift_snd]; infer_instance
    exact Etale.of_comp _ (pullback.snd s c)
  haveI : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  haveI : Etale e := IsZariskiLocalAtSource.sigmaDesc (P := @Etale) hlift
  show IsIso e
  apply hIso e
  intro Ω _ _ z
  obtain ⟨j, hj, huniq⟩ := hpts Ω (z ≫ pullback.snd s c) (z ≫ pullback.fst s c)
    (by rw [Category.assoc, Category.assoc, pullback.condition])
  have hz : (z ≫ pullback.snd s c) ≫ Sigma.ι (fun _ : J => W) j ≫ e = z := by
    rw [hι]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rw [← Category.assoc]
      exact hj
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
  refine ⟨(z ≫ pullback.snd s c) ≫ Sigma.ι (fun _ : J => W) j,
    by rw [Category.assoc]; exact hz, fun q hq => ?_⟩
  obtain ⟨j', x', rfl⟩ := exists_factor Ω q
  rw [Category.assoc, hι] at hq
  have hs := congrArg (· ≫ pullback.snd s c) hq
  have hf := congrArg (· ≫ pullback.fst s c) hq
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id] at hs hf
  have hjj : j' = j := huniq j' (by rw [← hs]; exact hf)
  rw [hjj, hs]
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pExtGood :
    (∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) (L : Type) [Field L] [Algebra R L] {Z Y : Scheme.{0}} (p : Z ⟶ B) (q : Y ⟶ B) (s : Y ⟶ Z) (tr : T.H q →ₗ[R] T.H p), T.IsTr p q s tr → (T.ext L).IsTr p q s (tr.baseChange L)) → ExtGood.{u} := by
  intro htr B R _ T L _ _ hG
  refine ⟨?_, ?_⟩
  · intro Z W p r c hc G _ _ a hgal
    have hinj := hG.inj p r c hc G a hgal
    show Function.Injective (LinearMap.baseChange L (T.pull c hc))
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hinj
  · intro Z Y p q s _ _ hs
    obtain ⟨tr, htr'⟩ := hG.tr p q s hs
    exact ⟨tr.baseChange L, htr T L p q s tr htr'⟩
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

namespace UpperTheory.Gal.G3

private theorem sum_translate {G R M : Type*} [Group G] [Field R] [AddCommGroup M] [Module R M]
    (K : Subgroup G) (f' : G → R) (Φ : G → M) (hf' : ∀ k ∈ K, ∀ g, f' (g * k) = f' g)
    (hΦ : ∀ k ∈ K, ∀ g, Φ (g * k) = Φ g) (g : G) :
    ∑ᶠ z : G ⧸ K, f' z.out • Φ (g * z.out) = ∑ᶠ w : G ⧸ K, f' (g⁻¹ * w.out) • Φ w.out := by
  refine Eq.trans (finsum_congr fun z => ?_)
    (finsum_comp_equiv (MulAction.toPerm g : Equiv.Perm (G ⧸ K))
      (f := fun w : G ⧸ K => f' (g⁻¹ * w.out) • Φ w.out))
  have e : (MulAction.toPerm g : Equiv.Perm (G ⧸ K)) z = ((g * z.out : G) : G ⧸ K) := by
    rw [MulAction.toPerm_apply]
    conv_lhs => rw [← QuotientGroup.out_eq' z]
    rfl
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (g * z.out)
  simp only [e, hk]
  rw [show g⁻¹ * (g * z.out * (k : G)) = z.out * k by group, hf' _ k.2, hΦ _ k.2]

private theorem sum_conv {G R : Type} {M : Type*} [Group G] [Field R] [AddCommGroup M] [Module R M]
    (K : Subgroup G) (f f' : G → R) (Φ : G → M) (hf' : ∀ k ∈ K, ∀ g, f' (g * k) = f' g)
    (hΦ : ∀ k ∈ K, ∀ g, Φ (g * k) = Φ g) (sf : {y : G ⧸ K | f y.out ≠ 0}.Finite)
    (sf' : {y : G ⧸ K | f' y.out ≠ 0}.Finite) :
    ∑ᶠ y : G ⧸ K, f y.out • ∑ᶠ z : G ⧸ K, f' z.out • Φ (y.out * z.out) =
      ∑ᶠ w : G ⧸ K, conv K f f' w.out • Φ w.out := by
  classical
  let Tw : Finset (G ⧸ K) := sf.toFinset.biUnion fun y => sf'.toFinset.image fun z => y.out • z
  have hT : ∀ y ∈ sf.toFinset, ∀ w : G ⧸ K, f' (y.out⁻¹ * w.out) ≠ 0 → w ∈ Tw := by
    intro y hy w hw
    refine Finset.mem_biUnion.2 ⟨y, hy, Finset.mem_image.2 ⟨((y.out⁻¹ * w.out : G) : G ⧸ K), ?_, ?_⟩⟩
    · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (y.out⁻¹ * w.out)
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      rw [hk, hf' _ k.2]
      exact hw
    · show ((y.out * (y.out⁻¹ * w.out) : G) : G ⧸ K) = w
      rw [mul_inv_cancel_left, QuotientGroup.out_eq']
  have hin : ∀ y ∈ sf.toFinset, ∑ᶠ w : G ⧸ K, f' (y.out⁻¹ * w.out) • Φ w.out =
      ∑ w ∈ Tw, f' (y.out⁻¹ * w.out) • Φ w.out := by
    intro y hy
    refine finsum_eq_sum_of_support_subset _ fun w hw => ?_
    refine hT y hy w fun h => hw ?_
    simp [h]
  have hc : ∀ w : G ⧸ K, conv K f f' w.out = ∑ y ∈ sf.toFinset, f y.out * f' (y.out⁻¹ * w.out) := by
    intro w
    refine finsum_eq_sum_of_support_subset _ fun y hy => ?_
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h
    exact hy (by simp [h])
  have hl : ∑ᶠ y : G ⧸ K, f y.out • ∑ᶠ z : G ⧸ K, f' z.out • Φ (y.out * z.out) =
      ∑ y ∈ sf.toFinset, f y.out • ∑ᶠ w : G ⧸ K, f' (y.out⁻¹ * w.out) • Φ w.out := by
    refine (finsum_congr fun y => by rw [sum_translate K f' Φ hf' hΦ y.out]).trans ?_
    refine finsum_eq_sum_of_support_subset _ fun y hy => ?_
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h
    exact hy (by simp [h])
  have hs : Function.support (fun w : G ⧸ K => conv K f f' w.out • Φ w.out) ⊆ (Tw : Set (G ⧸ K)) := by
    intro w hw
    have h0 : conv K f f' w.out ≠ 0 := fun h => hw (by simp [h])
    rw [hc w] at h0
    obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
    exact Finset.mem_coe.2 (hT y hy w (right_ne_zero_of_mul hne))
  rw [hl, finsum_eq_sum_of_support_subset _ hs]
  calc ∑ y ∈ sf.toFinset, f y.out • ∑ᶠ w : G ⧸ K, f' (y.out⁻¹ * w.out) • Φ w.out
      = ∑ y ∈ sf.toFinset, f y.out • ∑ w ∈ Tw, f' (y.out⁻¹ * w.out) • Φ w.out :=
        Finset.sum_congr rfl fun y hy => by rw [hin y hy]
    _ = ∑ w ∈ Tw, (∑ y ∈ sf.toFinset, f y.out * f' (y.out⁻¹ * w.out)) • Φ w.out := by
        simp only [Finset.smul_sum, Finset.sum_smul, mul_smul]
        exact Finset.sum_comm
    _ = ∑ w ∈ Tw, conv K f f' w.out • Φ w.out :=
        Finset.sum_congr rfl fun w _ => by rw [hc w]

private theorem pl_left_all {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R]
    (T : Th.{u} B R) {i j : X.ι} {k : G} (hk : k ∈ X.K j) (h : G) (x : T.H (X.q j)) :
    X.pl T i j (k * h) x = X.pl T i j h x := by
  by_cases a : X.admitted i j h
  · exact X.pl_left T a hk x
  · have b : ¬ X.admitted i j (k * h) := fun b => a (by
      simpa using b.mul (X.tower_admissible_self ((X.K j).inv_mem hk)))
    simp [Tower.pl, a, b]

end UpperTheory.Gal.G3

theorem UpperTheory.Gal.G3.pHopMul :
    FnRing → HopDeep.{u} → HopEx.{u} → HopMul.{u} := by
  intro hR hD hE B G _ X R _ _ T hT j f f' hf hf'
  have hF : X.IsFn j (conv (X.K j) f f') := ((hR X R j).2.2.1 f f' hf hf').2
  have hA := (hE X T hT j f hf).1
  have hA' := (hE X T hT j f' hf').1
  refine ((hE X T hT j _ hF).2 _ ?_).symm
  obtain ⟨m1, l1, a1⟩ := (hD X T hT j f hf).1
  obtain ⟨m2, l2, a2⟩ := (hD X T hT j f' hf').1
  obtain ⟨m3, l3, a3⟩ := (hD X T hT j _ hF).1
  classical
  let S : Finset (X.ι × G) :=
    {(m1, 1), (m2, 1), (m3, 1)} ∪ hf.2.2.toFinset.image fun y => (m2, y.out⁻¹)
  obtain ⟨m, lm, -, hm⟩ := X.deep j S
  have le1 : X.K m ≤ X.K m1 := fun u hu => by simpa using hm (m1, 1) (by simp [S]) u hu
  have le3 : X.K m ≤ X.K m3 := fun u hu => by simpa using hm (m3, 1) (by simp [S]) u hu
  have ad1 : ∀ g, f g ≠ 0 → X.admitted m j g⁻¹ := fun g hg => by
    simpa using (X.isAdmissibleIntegralBasisChange_one le1).mul (a1 g hg)
  have ad3 : ∀ g, conv (X.K j) f f' g ≠ 0 → X.admitted m j g⁻¹ := fun g hg => by
    simpa using (X.isAdmissibleIntegralBasisChange_one le3).mul (a3 g hg)
  refine (hD X T hT j _ hF).2 _ m lm ad3 fun x => ?_
  have step : ∀ y : G ⧸ X.K j, f y.out • X.pl T m j y.out⁻¹ (X.hecke T j f' x) =
      f y.out • ∑ᶠ z : G ⧸ X.K j, f' z.out • X.pl T m j (y.out * z.out)⁻¹ x := by
    intro y
    by_cases h : f y.out = 0
    · simp [h]
    have ad : X.admitted m m2 y.out⁻¹ := ⟨hf.2.1 _ h, fun u hu => hm (m2, y.out⁻¹)
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y, by simpa using h, rfl⟩)) u hu⟩
    have e : X.pl T m j y.out⁻¹ (X.hecke T j f' x) =
        X.pl T m m2 y.out⁻¹ (X.pl T m2 j 1 (X.hecke T j f' x)) := by
      rw [X.pl_pl T ad (X.isAdmissibleIntegralBasisChange_one l2), one_mul]
    have fin : (Function.support fun z : G ⧸ X.K j => f' z.out • X.pl T m2 j z.out⁻¹ x).Finite :=
      hf'.2.2.subset fun z hz h0 => hz (by simp [h0])
    rw [e, hA' m2 l2 a2 x, map_finsum _ fin]
    congr 1
    refine finsum_congr fun z => ?_
    by_cases h' : f' z.out = 0
    · simp [h']
    rw [map_smul, X.pl_pl T ad (a2 _ h'), mul_inv_rev]
  rw [Module.End.mul_apply, hA m lm ad1, finsum_congr step]
  exact sum_conv (X.K j) f f' (fun g => X.pl T m j g⁻¹ x) (fun k hk g => (hf'.1 k hk g).2)
    (fun k hk g => by
      simp only [mul_inv_rev]
      exact pl_left_all X T ((X.K j).inv_mem hk) _ x) hf.2.2 hf'.2.2
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pTwGal :
    TwSplit → TwGal := by
  intro hS B G _ X m j b hnorm
  classical
  haveI hN : ((X.K m).subgroupOf (X.K j)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    push_cast
    exact hnorm g g.2 n hn⟩
  haveI : Finite (X.K j ⧸ (X.K m).subgroupOf (X.K j)) := Nat.finite_of_card_ne_zero (X.idx m j)
  have admr : ∀ c : X.K j ⧸ (X.K m).subgroupOf (X.K j), X.admitted m m ((c.out : X.K j) : G)⁻¹ := fun c =>
    ⟨X.K_le j _ (inv_mem c.out.2), fun u hu => hnorm _ (inv_mem c.out.2) u hu⟩
  have uniq : ∀ k ∈ X.K j, ∃! c : X.K j ⧸ (X.K m).subgroupOf (X.K j),
      k * (((c.out : X.K j) : G))⁻¹⁻¹ ∈ X.K m := by
    intro k hk
    refine ⟨QuotientGroup.mk ⟨k⁻¹, inv_mem hk⟩, ?_, ?_⟩
    · obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul ((X.K m).subgroupOf (X.K j)) (⟨k⁻¹, inv_mem hk⟩ : X.K j)
      simp only [inv_inv]
      rw [hu]
      have hu' : ((u : X.K j) : G) ∈ X.K m := Subgroup.mem_subgroupOf.mp u.2
      simpa [mul_assoc] using hu'
    · intro c hc
      simp only [inv_inv] at hc
      rw [← QuotientGroup.out_eq' c, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa [mul_inv_rev] using inv_mem hc
  have trc : ∀ (g1 g2 : G) (e : g1 = g2) (p1 : X.admitted m m g1) (p2 : X.admitted m m g2),
      X.tr m m g1 p1.1 p1.2 = X.tr m m g2 p2.1 p2.2 := by
    intro g1 g2 e p1 p2
    subst e
    rfl
  have tl : ∀ (g k : G) (hg : X.admitted m m g) (hk : k ∈ X.K m) (hkg : X.admitted m m (k * g)),
      X.tr m m (k * g) hkg.1 hkg.2 = X.tr m m g hg.1 hg.2 := by
    intro g k hg hk hkg
    rw [← X.tr_mul m m m g k hg.1 hg.2 (X.K_le m k hk) (X.tower_admissible_self hk).2 hkg.1 hkg.2,
      X.tr_self m k _ _ hk, Category.comp_id]
  refine ⟨X.K j ⧸ (X.K m).subgroupOf (X.K j), inferInstance, inferInstance,
    fun c => ((c.out : X.K j) : G)⁻¹, admr, fun c => inv_mem c.out.2, uniq, ?_⟩
  unfold GlobalTheory.GalV.IsGalois
  refine ⟨X.fin m j b.1 b.2, X.etale m j b.1 b.2, X.onto m j b.1 b.2, ?_, ?_,
    hS X m m j b b le_rfl hnorm _ _ admr (fun c => inv_mem c.out.2) uniq⟩
  · have h1 : ((1 : X.K j ⧸ (X.K m).subgroupOf (X.K j)).out : G) ∈ X.K m :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp (QuotientGroup.out_eq' 1))
    exact X.tr_self m _ _ _ (inv_mem h1)
  · intro g g'
    set w : X.K j := ((g.out : X.K j) * g'.out)⁻¹ * (g * g').out with hwdef
    have hw : w ∈ (X.K m).subgroupOf (X.K j) := by
      rw [hwdef, ← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq',
        QuotientGroup.out_eq']
    have hw' : ((w : X.K j) : G) ∈ X.K m := Subgroup.mem_subgroupOf.mp hw
    have e : (((g * g').out : X.K j) : G)⁻¹ =
        ((w : X.K j) : G)⁻¹ * ((((g'.out : X.K j) : G))⁻¹ * (((g.out : X.K j) : G))⁻¹) := by
      simp only [hwdef, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hA : X.admitted m m ((((g'.out : X.K j) : G))⁻¹ * (((g.out : X.K j) : G))⁻¹) :=
      Tower.admitted.mul (admr g) (admr g')
    have hB : X.admitted m m (((w : X.K j) : G)⁻¹ * ((((g'.out : X.K j) : G))⁻¹ * (((g.out : X.K j) : G))⁻¹)) :=
      Tower.admitted.mul hA (X.tower_admissible_self (inv_mem hw'))
    exact ((trc _ _ e (admr (g * g')) hB).trans (tl _ _ hA (inv_mem hw') hB)).trans
      (X.tr_mul m m m _ _ (admr g).1 (admr g).2 (admr g').1 (admr g').2 hA.1 hA.2).symm
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pHodgeGood :
    HodgeTr → HodgeInj → HodgeGood := by
  intro hT hI k _ _ i j
  refine ⟨?_, ?_⟩
  · intro Z W p r c hc G _ _ a h
    obtain ⟨h1, h2, h3, -⟩ := h
    haveI := h1
    haveI := h2
    haveI := h3
    exact hI k i j p r c hc
  · intro Z Y p q s _ _ hs
    exact ⟨hodgeTrace hs i j, hT k i j p q s hs⟩
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem hop_summand {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R]
    (T : Th.{u} B R) {m j : X.ι} {f : G → R} (hf : X.IsFn j f) (had : ∀ g, f g ≠ 0 → X.admitted m j g⁻¹) (g : G)
    (x : T.H (X.q j)) :
    f (g : G ⧸ X.K j).out • X.pl T m j (g : G ⧸ X.K j).out⁻¹ x = f g • X.pl T m j g⁻¹ x := by
  obtain ⟨⟨k, hk⟩, hkeq⟩ := QuotientGroup.mk_out_eq_mul (X.K j) g
  rw [hkeq, (hf.1 k hk g).2]
  by_cases h0 : f g = 0
  · simp [h0]
  · rw [mul_inv_rev, X.pl_left T (had g h0) (inv_mem hk)]

theorem UpperTheory.Gal.G3.pHopEx :
    PlInv.{u} → HopDeep.{u} → HopEx.{u} := by
  intro hPl hD B G _ X R _ _ T hT j f hf
  obtain ⟨⟨m0, hm0j, had0⟩, hiso⟩ := hD X T hT j f hf
  have huniq : ∀ A A' : Module.End R (T.H (X.q j)), X.IsHop T j f A → X.IsHop T j f A' → A = A' := by
    intro A A' hA hA'
    ext x
    apply (hPl X T hT m0 j hm0j).1
    rw [hA m0 hm0j had0 x, hA' m0 hm0j had0 x]
  obtain ⟨m, hmj, hnorm, hS⟩ := X.deep j {(m0, 1)}
  have hmm0 : X.K m ≤ X.K m0 := fun u hu => by simpa using hS (m0, 1) (by simp) u hu
  have had : ∀ g, f g ≠ 0 → X.admitted m j g⁻¹ := fun g hg => by
    simpa using (X.isAdmissibleIntegralBasisChange_one hmm0).mul (had0 g hg)
  set S := hf.2.2.toFinset with hSdef
  have hsub : ∀ (w : G ⧸ X.K j → T.H (X.q m)),
      Function.support (fun z => f z.out • w z) ⊆ (S : Set (G ⧸ X.K j)) := by
    intro w z hz
    simp only [S, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h0
    exact hz (by simp [h0])
  let Y : T.H (X.q j) →ₗ[R] T.H (X.q m) := ∑ z ∈ S, f z.out • X.pl T m j z.out⁻¹
  have hYS : ∀ x, Y x = ∑ z ∈ S, f z.out • X.pl T m j z.out⁻¹ x := by
    intro x
    simp [Y, LinearMap.sum_apply]
  have hY : ∀ x, Y x = ∑ᶠ z : G ⧸ X.K j, f z.out • X.pl T m j z.out⁻¹ x := by
    intro x
    rw [finsum_eq_sum_of_support_subset _ (hsub _), hYS]
  have hinv : ∀ x, ∀ k ∈ X.K j, X.pl T m m k (Y x) = Y x := by
    intro x k hk
    have hadk : X.admitted m m k := ⟨X.K_le j k hk, fun u hu => hnorm k hk u hu⟩
    have key : ∀ z : G ⧸ X.K j, X.pl T m m k (f z.out • X.pl T m j z.out⁻¹ x) =
        f (k⁻¹ • z).out • X.pl T m j (k⁻¹ • z).out⁻¹ x := by
      intro z
      have hz : k⁻¹ • z = ((k⁻¹ * z.out : G) : G ⧸ X.K j) := by
        conv_lhs => rw [← QuotientGroup.out_eq' z]
        rfl
      rw [hz, hop_summand X T hf had, (hf.1 k⁻¹ (inv_mem hk) z.out).1, map_smul]
      by_cases h0 : f z.out = 0
      · simp [h0]
      · rw [X.pl_pl T hadk (had _ h0), mul_inv_rev, inv_inv]
    have hsub2 : Function.support (fun z : G ⧸ X.K j => X.pl T m m k (f z.out • X.pl T m j z.out⁻¹ x))
        ⊆ (S : Set (G ⧸ X.K j)) := by
      intro z hz
      simp only [S, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
      intro h0
      exact hz (by simp [h0])

    rw [hYS, map_sum, ← finsum_eq_sum_of_support_subset _ hsub2, ← hYS, hY]
    simp_rw [key]
    exact finsum_comp_equiv (MulAction.toPerm k⁻¹ : Equiv.Perm (G ⧸ X.K j))
      (f := fun z : G ⧸ X.K j => f z.out • X.pl T m j z.out⁻¹ x)
  have hinj := (hPl X T hT m j hmj).1
  have hrange : ∀ x, Y x ∈ LinearMap.range (X.pl T m j 1) := by
    intro x
    obtain ⟨w, hw⟩ := (hPl X T hT m j hmj).2 hnorm (Y x) (hinv x)
    exact ⟨w, hw⟩
  let A : Module.End R (T.H (X.q j)) :=
    (LinearEquiv.ofInjective (X.pl T m j 1) hinj).symm.toLinearMap ∘ₗ Y.codRestrict _ hrange
  have hA : ∀ x, X.pl T m j 1 (A x) = Y x := by
    intro x
    have h := congrArg Subtype.val
      ((LinearEquiv.ofInjective (X.pl T m j 1) hinj).apply_symm_apply ⟨Y x, hrange x⟩)
    rw [LinearEquiv.ofInjective_apply] at h
    exact h
  have hex : ∃ A, X.IsHop T j f A := ⟨A, hiso A m hmj had (fun x => by rw [hA, hY])⟩
  have hh : X.IsHop T j f (X.hecke T j f) := by
    unfold Tower.hecke
    rw [dite_eq_left hex]
    exact hex.choose_spec
  exact ⟨hh, fun A' hA' => huniq _ _ hA' hh⟩
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pExtTr :
    ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) (L : Type) [Field L] [Algebra R L] {Z Y : Scheme.{0}} (p : Z ⟶ B) (q : Y ⟶ B) (s : Y ⟶ Z) (tr : T.H q →ₗ[R] T.H p), T.IsTr p q s tr → (T.ext L).IsTr p q s (tr.baseChange L) := by
  intro B R _ T L _ _ Z Y p q s tr h W r c hc J _ σ hσ hs x
  change LinearMap.baseChange L (T.pull c hc) (LinearMap.baseChange L tr x) =
    ∑ j, LinearMap.baseChange L (T.pull (σ j) (hσ j)) x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    simp only [LinearMap.baseChange_tmul]
    rw [h W r c hc J σ hσ hs y, TensorProduct.tmul_sum]
  | add x y hx hy =>
    simp only [map_add (f := _), hx, hy, ← Finset.sum_add_distrib]
end
