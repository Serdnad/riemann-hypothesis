module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem sp_subsingleton (Ω : Type) [Field Ω] : Subsingleton ↑(UpperTheory.Gal.G3.sp Ω) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum Ω))

private theorem exists_factor_ι {J : Type} {W : Scheme.{0}} (Ω : Type) [Field Ω]
    (u : UpperTheory.Gal.G3.sp Ω ⟶ ∐ (fun _ : J => W)) :
    ∃ (j : J) (x : UpperTheory.Gal.G3.sp Ω ⟶ W), x ≫ Sigma.ι (fun _ : J => W) j = u := by
  haveI := sp_subsingleton Ω
  have p : ↑(UpperTheory.Gal.G3.sp Ω) := show PrimeSpectrum Ω from ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨⟨j, y⟩, hq⟩ : ∃ q, (sigmaMk (fun _ : J => W)).symm (u p) = q := ⟨_, rfl⟩
  have hy : Sigma.ι (fun _ : J => W) j y = u p := by
    rw [← sigmaMk_mk, ← hq, Homeomorph.apply_symm_apply]
  refine ⟨j, IsOpenImmersion.lift (Sigma.ι (fun _ : J => W) j) u ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨z, rfl⟩
  obtain rfl : z = p := Subsingleton.elim _ _
  exact ⟨y, hy⟩

private theorem index_eq_of_ι {J : Type} {W : Scheme.{0}} (Ω : Type) [Field Ω] {j j' : J}
    {x x' : UpperTheory.Gal.G3.sp Ω ⟶ W}
    (h : x ≫ Sigma.ι (fun _ : J => W) j = x' ≫ Sigma.ι (fun _ : J => W) j') : j = j' := by
  by_contra hne
  have he := isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : J => W) ⟨h⟩ hne
  exact he.false (show PrimeSpectrum Ω from ⟨⊥, Ideal.isPrime_bot⟩)

theorem UpperTheory.Gal.G3.pPtsOfSplits :
    PtsOfSplits := by
  intro Z Y W s c J σ hs Ω _ x y hxy
  obtain ⟨hσ, hiso⟩ := hs
  haveI := hiso
  let e := Limits.Sigma.desc (fun j : J =>
    pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j))
  have hι : ∀ j, Sigma.ι (fun _ : J => W) j ≫ e =
      pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j) :=
    fun j => Sigma.ι_desc _ _
  obtain ⟨j, x', hx'⟩ := exists_factor_ι Ω (pullback.lift y x hxy ≫ inv e)
  have h1 : x' ≫ Sigma.ι (fun _ : J => W) j ≫ e = pullback.lift y x hxy := by
    rw [← Category.assoc, hx', Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hι] at h1
  have hsnd := congrArg (· ≫ pullback.snd s c) h1
  have hfst := congrArg (· ≫ pullback.fst s c) h1
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id] at hsnd hfst
  rw [hsnd] at hfst
  refine ⟨j, hfst, fun j' hj' => ?_⟩
  have hj'' : x ≫ σ j' = y := hj'
  apply index_eq_of_ι Ω (x := x) (x' := x')
  rw [hx']
  apply (cancel_mono e).mp
  rw [Category.assoc, hι, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hj'']
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private lemma supp_fin {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R] (T : Th.{u} B R)
    {j m : X.ι} {f : G → R} (hf : X.IsFn j f) (x : T.H (X.q j)) :
    (Function.support fun y : G ⧸ X.K j => f y.out • X.pl T m j y.out⁻¹ x).Finite := by
  refine hf.2.2.subset ?_
  intro y hy h0
  exact hy (by simp only [h0, zero_smul])

theorem UpperTheory.Gal.G3.pHopLin :
    FnRing → HopDeep.{u} → HopEx.{u} → HopLin.{u} := by
  intro hR hD hE B G _ X R _ _ T hT j f f' c hf hf'
  obtain ⟨⟨m1, hm1, ha1⟩, -⟩ := hD X T hT j f hf
  obtain ⟨⟨m2, hm2, ha2⟩, -⟩ := hD X T hT j f' hf'
  obtain ⟨m, hmm1, -, hS⟩ := X.deep m1 {(m2, 1)}
  have hmm2 : X.K m ≤ X.K m2 := by
    intro u hu
    simpa using hS (m2, 1) (by simp) u hu
  have hmj : X.K m ≤ X.K j := hmm1.trans hm1
  have hA1 : ∀ g, f g ≠ 0 → X.admitted m j g⁻¹ := fun g hg => by
    simpa using (X.isAdmissibleIntegralBasisChange_one hmm1).mul (ha1 g hg)
  have hA2 : ∀ g, f' g ≠ 0 → X.admitted m j g⁻¹ := fun g hg => by
    simpa using (X.isAdmissibleIntegralBasisChange_one hmm2).mul (ha2 g hg)
  have e1 := (hE X T hT j f hf).1 m hmj hA1
  have e2 := (hE X T hT j f' hf').1 m hmj hA2
  have hsum := ((hR X R j).2.2.1 f f' hf hf').1
  have hc := (hR X R j).2.2.2 c f hf
  constructor
  · symm
    apply (hE X T hT j (f + f') hsum).2
    apply (hD X T hT j (f + f') hsum).2 _ m hmj
    · intro g hg
      by_cases h1 : f g = 0
      · apply hA2 g
        intro h2
        apply hg
        simp [h1, h2]
      · exact hA1 g h1
    · intro x
      rw [LinearMap.add_apply, map_add (f := _), e1 x, e2 x,
        ← finsum_add_distrib (supp_fin (m := m) X T hf x) (supp_fin (m := m) X T hf' x)]
      apply finsum_congr
      intro y
      simp [add_smul]
  · symm
    apply (hE X T hT j (c • f) hc).2
    apply (hD X T hT j (c • f) hc).2 _ m hmj
    · intro g hg
      apply hA1 g
      intro h
      apply hg
      simp [h]
    · intro x
      rw [LinearMap.smul_apply, map_smul, e1 x, smul_finsum]
      apply finsum_congr
      intro y
      simp [smul_smul]
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pHopDeep :
    PlInv.{u} → HopDeep.{u} := by
  classical
  intro hPl B G _ X R _ _ T hT j f hf
  have hfin := hf.2.2
  have hpush : ∀ (n n' : X.ι), X.K n' ≤ X.K n → (∀ g, f g ≠ 0 → X.admitted n j g⁻¹) → ∀ x : T.H (X.q j),
      X.pl T n' n 1 (∑ᶠ z : G ⧸ X.K j, f z.out • X.pl T n j z.out⁻¹ x) =
        ∑ᶠ z : G ⧸ X.K j, f z.out • X.pl T n' j z.out⁻¹ x := by
    intro n n' hn'n hadn x
    rw [map_finsum _ (hfin.subset ?_)]
    · refine finsum_congr fun z => ?_
      rw [map_smul]
      by_cases h0 : f z.out = 0
      · simp [h0]
      · rw [X.pl_pl T (X.isAdmissibleIntegralBasisChange_one hn'n) (hadn _ h0), mul_one]
    · intro z hz
      simp only [Set.mem_setOf_eq]
      intro h0
      exact hz (by simp [h0])
  constructor
  · obtain ⟨m, hmj, -, hS⟩ := X.deep j (hfin.toFinset.image fun z => (j, (Quotient.out z)⁻¹))
    refine ⟨m, hmj, fun g hg => ⟨hf.2.1 g hg, fun u hu => ?_⟩⟩
    obtain ⟨⟨h, hh⟩, hheq⟩ := QuotientGroup.mk_out_eq_mul (X.K j) g
    have hz : (g : G ⧸ X.K j) ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hheq, (hf.1 h hh g).2]
      exact hg
    have hc := hS (j, (Quotient.out (g : G ⧸ X.K j))⁻¹) (Finset.mem_image_of_mem _ hz) u hu
    simp only [hheq] at hc
    have hmem := mul_mem (mul_mem hh hc) (inv_mem hh)
    convert hmem using 1
    group
  · intro A m hmj hadm hA m' hm'j hadm' x
    obtain ⟨n, -, -, hS⟩ := X.deep j {(m, 1), (m', 1)}
    have hnm : X.K n ≤ X.K m := fun u hu => by simpa using hS (m, 1) (by simp) u hu
    have hnm' : X.K n ≤ X.K m' := fun u hu => by simpa using hS (m', 1) (by simp) u hu
    apply (hPl X T hT n m' hnm').1
    rw [hpush m' n hnm' hadm', X.pl_pl T (X.isAdmissibleIntegralBasisChange_one hnm') (X.isAdmissibleIntegralBasisChange_one hm'j), ← hpush m n hnm hadm, ← hA,
      X.pl_pl T (X.isAdmissibleIntegralBasisChange_one hnm) (X.isAdmissibleIntegralBasisChange_one hmj)]
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem pull_congr {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {X Y : Scheme.{0}}
    {p : X ⟶ B} {q : Y ⟶ B} {f f' : Y ⟶ X} (e : f = f') (h : f ≫ p = q) (h' : f' ≫ p = q) (x : T.H p) :
    T.pull f h x = T.pull f' h' x := by
  subst e; rfl

theorem UpperTheory.Gal.G3.pGalInv :
    GalInv.{u} := by
  intro B R _ _ T hT Z W p r c hc G _ _ a ha hgal y
  obtain ⟨hac, -⟩ := hgal.2.2.2.2.2
  constructor
  · rintro ⟨x, rfl⟩ g
    have hcomp : (a g ≫ c) ≫ p = r := by rw [hac g, hc]
    rw [← T.pull_comp (a g) c (ha g) hc hcomp x]
    exact pull_congr T (hac g) hcomp hc x
  · intro hy
    haveI := hgal.1
    haveI := hgal.2.1
    haveI := Fintype.ofFinite G
    obtain ⟨tr, htr⟩ := hT.tr p r c hc
    have key := htr W r c hc G a ha hgal.2.2.2.2.2 y
    have hsum : ∑ g, T.pull (a g) (ha g) y = (Fintype.card G : R) • y := by
      rw [Finset.sum_congr rfl fun g _ => hy g, Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul R]
    refine ⟨(Fintype.card G : R)⁻¹ • tr y, ?_⟩
    rw [map_smul, key, hsum, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_smul]
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pPlInv :
    GalInv.{u} → TwGal → PlInv.{u} := by
  intro hG hT B G _ X R _ _ T hgood m j hmj
  constructor
  · obtain ⟨m', hm'j, hnorm, hS⟩ := X.deep j {(m, 1)}
    have hm'm : X.K m' ≤ X.K m := fun u hu => by simpa using hS (m, 1) (by simp) u hu
    obtain ⟨Γ, _, _, r, c, hr, huniq, hgal⟩ := hT X m' j (X.isAdmissibleIntegralBasisChange_one hm'j) hnorm
    have hinj := hgood.inj (X.q j) (X.q m') _ (X.tr_q m' j 1 _ _) Γ _ hgal
    have key : ∀ z, X.pl T m' j 1 z = X.pl T m' m 1 (X.pl T m j 1 z) := fun z => by
      rw [X.pl_pl T (X.isAdmissibleIntegralBasisChange_one hm'm) (X.isAdmissibleIntegralBasisChange_one hmj), one_mul]
    intro x y hxy
    apply hinj
    rw [← X.pl_eq T (X.isAdmissibleIntegralBasisChange_one hm'j), key, key, hxy]
  · intro hnorm y hy
    obtain ⟨Γ, _, _, r, c, hr, huniq, hgal⟩ := hT X m j (X.isAdmissibleIntegralBasisChange_one hmj) hnorm
    have ha : ∀ g : Γ, X.tr m m (r g) (c g).1 (c g).2 ≫ X.q m = X.q m := fun g => X.tr_q _ _ _ _ _
    have hsurj := (hG T hgood (X.q j) (X.q m) _ (X.tr_q m j 1 _ _) Γ _ ha hgal y).2
    obtain ⟨x, hx⟩ := hsurj (fun g => by rw [← X.pl_eq T (c g)]; exact hy _ (hr g))
    exact ⟨x, by rw [X.pl_eq T (X.isAdmissibleIntegralBasisChange_one hmj)]; exact hx⟩
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem tr_left {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {i j : X.ι} {h k : G} (hk : k ∈ X.K j)
    (a : X.admitted i j h) (p q) : X.tr i j (k * h) p q = X.tr i j h a.1 a.2 := by
  rw [← X.tr_mul i j j h k a.1 a.2 (X.K_le j k hk) (X.tower_admissible_self hk).2 p q,
    X.tr_self j k _ _ hk, Category.comp_id]

private theorem tower_tr_eq_of_eq_mul_of_mem_K {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {i j : X.ι} {h k g : G}
    (hk : k ∈ X.K j) (a : X.admitted i j h) (hg : g = k * h) (p q) : X.tr i j g p q = X.tr i j h a.1 a.2 := by
  subst hg
  exact tr_left X hk a p q

private theorem tower_tr_comp_tr_eq_tr_mul {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {i j m : X.ι} {h h' : G}
    (p : h ∈ X.Δ) (q : ∀ u ∈ X.K i, h * u * h⁻¹ ∈ X.K j) (p' : h' ∈ X.Δ)
    (q' : ∀ u ∈ X.K j, h' * u * h'⁻¹ ∈ X.K m) :
    X.tr i j h p q ≫ X.tr j m h' p' q' =
      X.tr i m (h' * h) (Tower.admitted.mul (X := X) ⟨p, q⟩ ⟨p', q'⟩).1
        (Tower.admitted.mul (X := X) ⟨p, q⟩ ⟨p', q'⟩).2 :=
  X.tr_mul _ _ _ _ _ _ _ _ _ _ _

theorem UpperTheory.Gal.G3.pTwSplit :
    SplitsPts → TwSplit := by
  intro hS B G _ X m i j a b hmi hnorm J _ r c hr huniq
  have hij : ∀ u ∈ X.K i, u ∈ X.K j := fun u hu => by simpa using a.2 u hu
  have hmj : ∀ u ∈ X.K m, u ∈ X.K j := fun u hu => by simpa using b.2 u hu
  have Am : ∀ g ∈ X.K j, X.admitted m m g := fun g hg => ⟨X.K_le j g hg, fun u hu => hnorm g hg u hu⟩
  have hcomp : ∀ x, X.tr m i (r x) (c x).1 (c x).2 ≫ X.tr i j 1 a.1 a.2 = X.tr m j 1 b.1 b.2 := by
    intro x
    rw [X.tr_mul m i j (r x) 1 (c x).1 (c x).2 a.1 a.2 ((c x).mul a).1 ((c x).mul a).2]
    exact tower_tr_eq_of_eq_mul_of_mem_K X (hr x) b (by simp) _ _
  have U : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : sp Ω ⟶ X.Z m) (x1 x2 : J),
      x ≫ X.tr m i (r x1) (c x1).1 (c x1).2 = x ≫ X.tr m i (r x2) (c x2).1 (c x2).2 → x1 = x2 := by
    intro Ω _ _ x x1 x2 h12
    have p1 := X.isAdmissibleIntegralBasisChange_one hmi
    have e1 : (x ≫ X.tr m m (r x1) (Am _ (hr x1)).1 (Am _ (hr x1)).2) ≫ X.tr m i 1 p1.1 p1.2
        = (x ≫ X.tr m m (r x2) (Am _ (hr x2)).1 (Am _ (hr x2)).2) ≫ X.tr m i 1 p1.1 p1.2 := by
      rw [Category.assoc, Category.assoc, tower_tr_comp_tr_eq_tr_mul, tower_tr_comp_tr_eq_tr_mul,
        tower_tr_eq_of_eq_mul_of_mem_K X (one_mem (X.K i)) (c x1) (rfl : (1:G) * r x1 = 1 * r x1),
        tower_tr_eq_of_eq_mul_of_mem_K X (one_mem (X.K i)) (c x2) (rfl : (1:G) * r x2 = 1 * r x2)]
      exact h12
    obtain ⟨k, hki, a', b', hk⟩ := X.trans m i p1.1 p1.2
      (fun k hk u hu => hnorm k (hij k hk) u hu) Ω _ _ e1
    have hkj := hij k hki
    have e2 : x ≫ X.tr m m (r x2) (Am _ (hr x2)).1 (Am _ (hr x2)).2
        = x ≫ X.tr m m (k * r x1) (Am _ (mul_mem hkj (hr x1))).1 (Am _ (mul_mem hkj (hr x1))).2 := by
      rw [hk, Category.assoc, tower_tr_comp_tr_eq_tr_mul]
    have hinv : (r x2)⁻¹ ∈ X.K j := inv_mem (hr x2)
    have hg : (r x2)⁻¹ * (k * r x1) ∈ X.K j := mul_mem hinv (mul_mem hkj (hr x1))
    have hfix : x ≫ X.tr m m _ (Am _ hg).1 (Am _ hg).2 = x := by
      rw [← X.tr_mul m m m (k * r x1) (r x2)⁻¹ (Am _ (mul_mem hkj (hr x1))).1 (Am _ (mul_mem hkj (hr x1))).2
        (Am _ hinv).1 (Am _ hinv).2, ← Category.assoc, ← e2, Category.assoc,
        X.tr_mul m m m (r x2) (r x2)⁻¹ (Am _ (hr x2)).1 (Am _ (hr x2)).2 (Am _ hinv).1 (Am _ hinv).2
          (Am _ (mul_mem hinv (hr x2))).1 (Am _ (mul_mem hinv (hr x2))).2,
        X.tr_self m _ _ _ (by simp), Category.comp_id]
    have hgm := X.free m j (fun u hu => hmj u hu) _ hg (Am _ hg).1 (Am _ hg).2 Ω x hfix
    have hk0 : k * r x1 ∈ X.K j := mul_mem hkj (hr x1)
    apply (huniq _ hk0).unique
    · simpa using hki
    · have := (c x2).2 _ hgm
      convert this using 1
      group
  have hpts : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : sp Ω ⟶ X.Z m) (y : sp Ω ⟶ X.Z i),
      y ≫ X.tr i j 1 a.1 a.2 = x ≫ X.tr m j 1 b.1 b.2 → ∃! x0, x ≫ X.tr m i (r x0) (c x0).1 (c x0).2 = y := by
    intro Ω _ _ x y hxy
    have p1 := X.isAdmissibleIntegralBasisChange_one hmi
    haveI := X.fin m i p1.1 p1.2
    obtain ⟨v, hv⟩ := (X.onto m i p1.1 p1.2).surj (UpperTheory.Gal.TranscendenceTraces.pt (X := X.Z i) (Ω := Ω) y)
    obtain ⟨z, hz, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds (X.tr m i 1 p1.1 p1.2) Ω y v hv
    have hzj : x ≫ X.tr m j 1 b.1 b.2 = z ≫ X.tr m j 1 b.1 b.2 := by
      rw [← hxy, ← hz, Category.assoc, tower_tr_comp_tr_eq_tr_mul,
        tower_tr_eq_of_eq_mul_of_mem_K X (one_mem (X.K j)) b (rfl : (1:G) * 1 = 1 * 1)]
    obtain ⟨k, hkj, a', b', hk⟩ := X.trans m j b.1 b.2 hnorm Ω x z hzj
    obtain ⟨x0, hx0, -⟩ := huniq k hkj
    have ex : x ≫ X.tr m i (r x0) (c x0).1 (c x0).2 = y := by
      rw [← hz, hk, Category.assoc, tower_tr_comp_tr_eq_tr_mul,
        tower_tr_eq_of_eq_mul_of_mem_K X hx0 (c x0) (show (1:G) * k = k * (r x0)⁻¹ * r x0 by group)]
    exact ⟨x0, ex, fun x2 h2 => U Ω x x2 x0 (h2.trans ex.symm)⟩
  haveI := X.fin i j a.1 a.2
  haveI := X.etale i j a.1 a.2
  exact hS _ _ J _ hcomp hpts
end
