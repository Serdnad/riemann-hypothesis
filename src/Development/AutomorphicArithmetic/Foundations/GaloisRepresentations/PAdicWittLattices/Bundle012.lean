module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle005
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle068
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem push_one_eq {W Z : Scheme.{0}} (c : W ⟶ Z) (d : ℕ) (hd : d ≠ 0) (h : FEt c d) :
    (UpperTheory.Gal.TranscendenceTraces.Wt.const W 1).push c = UpperTheory.Gal.TranscendenceTraces.Wt.const Z (d : ℤ) := by
  funext Ω _ _ x
  have hx := h.2.2 Ω x
  simp only [UpperTheory.Gal.TranscendenceTraces.Wt.push, UpperTheory.Gal.TranscendenceTraces.Wt.const]
  have hne : Nat.card {y // y ≫ c = x} ≠ 0 := by rw [hx]; exact hd
  have hfin : Finite {y // y ≫ c = x} := Nat.finite_of_card_ne_zero hne
  have hs : (UpperTheory.Gal.TranscendenceTraces.fib c x).Finite := Set.finite_coe_iff.mp hfin
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, Finset.sum_const, nsmul_eq_mul, mul_one,
    ← Set.ncard_eq_toFinset_card _ hs, ← Nat.card_coe_set_eq]
  exact_mod_cast hx

theorem UpperTheory.Gal.G3.pEtnGood :
    FEtBasic → EtTr → EtnGood := by
  intro hF hT l _ B hl n i
  obtain ⟨hW, -, hA⟩ := UpperTheory.Gal.TranscendenceTraces.all_holds
  have hFlat : UpperTheory.Gal.TranscendenceTraces.WtFlat := hW.2.2.2.2.2.2.2.2.2.1
  have hMult : UpperTheory.Gal.TranscendenceTraces.MultBasic := hW.2.2.2.2.2.2.2.1
  have hDeg : UpperTheory.Gal.TranscendenceTraces.TrDegQ := hA.2.2.2.2.1
  refine ⟨?_, ?_⟩
  · intro Z W p r c hc G _ _ a hG
    have hd : FEt c (Nat.card G) := hF.2.2 c G a hG
    have hpos : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have hpush := push_one_eq c _ hpos hd
    obtain ⟨hfin, het, -⟩ := hd
    have hwt : UpperTheory.Gal.TranscendenceTraces.IsWt c (UpperTheory.Gal.TranscendenceTraces.Wt.const W 1) := by
      have h1 := hFlat c
      rwa [hMult.2.2 c] at h1
    have hlZ : IsUnit ((l : ℕ) : Γ(Z, ⊤)) := by
      have := hl.map p.appTop.hom
      simpa using this
    have key := hDeg l n i c _ _ hwt hlZ hpush
    have hne : (((Nat.card G : ℕ) : ℤ) : ℚ_[l]) ≠ 0 := by
      exact_mod_cast hpos
    intro x y hxy
    have hxy' : pullHQ l (sch.map c) n i x = pullHQ l (sch.map c) n i y := hxy
    have e : ∀ t, UpperTheory.Gal.TranscendenceTraces.trHQ l c (UpperTheory.Gal.TranscendenceTraces.Wt.const W 1) n i (pullHQ l (sch.map c) n i t) =
        (((Nat.card G : ℕ) : ℤ) : ℚ_[l]) • t := fun t => LinearMap.congr_fun key t
    have ex := e x
    rw [hxy', e y] at ex
    exact smul_right_injective _ hne ex.symm
  · intro Z Y p q s _ _ _
    exact ⟨_, hT l B hl n i p q s⟩
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

namespace UpperTheory.Gal.G3

private theorem fibre_finite {Y Z : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] (Ω : Type) [Field Ω] (x : sp Ω ⟶ Z) :
    Finite {y : sp Ω ⟶ Y // y ≫ s = x} := by
  have h := UpperTheory.Gal.TranscendenceTraces.fibFin_of UpperTheory.Gal.TranscendenceTraces.chart_of s Ω x
  exact h.to_subtype

private theorem epi_of_field {Ω Ω' : Type} [Field Ω] [Field Ω'] (x : sp Ω' ⟶ sp Ω) : Epi x := by
  exact Flat.epi_of_flat_of_surjective x

private theorem point_over {Z : Scheme.{0}} (z : Z) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (x : sp Ω ⟶ Z), x (IsLocalRing.closedPoint Ω) = z := by
  refine ⟨AlgebraicClosure (Z.residueField z), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) (AlgebraicClosure (Z.residueField z)))) ≫
      Z.fromSpecResidueField z, ?_⟩
  exact Scheme.fromSpecResidueField_apply z _

end UpperTheory.Gal.G3

private theorem exists_comp_sigma_eq_of_comp_eq_comp {Z Y W : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] {d : ℕ}
    (hd : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ Z),
      Nat.card {y // y ≫ s = x} = d)
    (c : W ⟶ Z) (σ : Fin d → (W ⟶ Y)) (hσ : ∀ j, σ j ≫ s = c)
    (hinj : ∀ (Ω : Type) [Field Ω] (x : UpperTheory.Gal.G3.sp Ω ⟶ W), Function.Injective fun j => x ≫ σ j)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : UpperTheory.Gal.G3.sp Ω ⟶ W) (y : UpperTheory.Gal.G3.sp Ω ⟶ Y)
    (hy : y ≫ s = x ≫ c) :
    ∃ j, x ≫ σ j = y := by
  have hfin := UpperTheory.Gal.G3.fibre_finite s Ω (x ≫ c)
  let f : Fin d → {y : UpperTheory.Gal.G3.sp Ω ⟶ Y // y ≫ s = x ≫ c} :=
    fun j => ⟨x ≫ σ j, by rw [Category.assoc, hσ]⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact hinj Ω x (congrArg Subtype.val hij)
  have hb := hf.bijective_of_nat_card_le (by rw [hd Ω (x ≫ c), Nat.card_eq_fintype_card, Fintype.card_fin])
  obtain ⟨j, hj⟩ := hb.2 ⟨y, hy⟩
  exact ⟨j, congrArg Subtype.val hj⟩

theorem UpperTheory.Gal.G3.pGalClosD :
    SplitsPts → OrdEx → GalClosD := by
  intro hS hO Z Y s d hF
  obtain ⟨hfin, het, hd⟩ := hF
  obtain ⟨W, c, σ, hcf, hce, hσ, hinj, huniv⟩ := hO s d
  have hex : ∀ g : Equiv.Perm (Fin d), ∃! w : W ⟶ W, w ≫ c = c ∧ ∀ j, w ≫ σ j = σ (g j) := by
    intro g
    refine huniv W c (fun j => σ (g j)) (fun j => hσ (g j)) ?_
    intro Ω _ x i j hij
    exact g.injective (hinj Ω x hij)
  choose a ha using fun g => (hex g).exists
  have hone : a 1 = 𝟙 W :=
    (hex 1).unique (ha 1) ⟨Category.id_comp c, fun j => by simp⟩
  have hmul : ∀ g h, a (g * h) = a g ≫ a h := by
    intro g h
    refine (hex (g * h)).unique (ha (g * h)) ⟨?_, fun j => ?_⟩
    · rw [Category.assoc, (ha h).1, (ha g).1]
    · rw [Category.assoc, (ha h).2 j, (ha g).2 (h j)]
      rfl
  have hspl : Splits s c σ := by
    refine hS s c (Fin d) σ hσ ?_
    intro Ω _ _ x y hy
    obtain ⟨j, hj⟩ := exists_comp_sigma_eq_of_comp_eq_comp s hd c σ hσ hinj Ω x y hy
    exact ⟨j, hj, fun j' hj' => hinj Ω x (hj'.trans hj.symm)⟩
  have hsur : Surjective c := by
    constructor
    intro z
    obtain ⟨Ω, _, _, x, hx⟩ := UpperTheory.Gal.G3.point_over z
    have hfF := UpperTheory.Gal.G3.fibre_finite s Ω x
    have hcard : Nat.card {y : UpperTheory.Gal.G3.sp Ω ⟶ Y // y ≫ s = x} = d := hd Ω x
    let e := Finite.equivFin {y : UpperTheory.Gal.G3.sp Ω ⟶ Y // y ≫ s = x}
    let yy : Fin d → (UpperTheory.Gal.G3.sp Ω ⟶ Y) := fun j => (e.symm (Fin.cast hcard.symm j)).1
    have hyy : ∀ j, yy j ≫ s = x := fun j => (e.symm (Fin.cast hcard.symm j)).2
    have hinj' : ∀ (Ω' : Type) [Field Ω'] (x' : UpperTheory.Gal.G3.sp Ω' ⟶ UpperTheory.Gal.G3.sp Ω),
        Function.Injective fun j => x' ≫ yy j := by
      intro Ω' _ x' i j hij
      haveI := UpperTheory.Gal.G3.epi_of_field x'
      have h1 : yy i = yy j := (cancel_epi x').1 hij
      have h2 := Subtype.val_injective h1
      exact Fin.cast_injective _ (e.symm.injective h2)
    obtain ⟨w, ⟨hw, _⟩, _⟩ := huniv (UpperTheory.Gal.G3.sp Ω) x yy hyy hinj'
    refine ⟨w (IsLocalRing.closedPoint Ω), ?_⟩
    rw [← hx, ← hw]
    rfl
  have hgal : Splits c c a := by
    refine hS c c (Equiv.Perm (Fin d)) a (fun g => (ha g).1) ?_
    intro Ω _ _ x y hy
    have hpt : ∀ j, ∃ k, x ≫ σ k = y ≫ σ j := by
      intro j
      exact exists_comp_sigma_eq_of_comp_eq_comp s hd c σ hσ hinj Ω x (y ≫ σ j) (by rw [Category.assoc, hσ, hy])
    choose p hp using hpt
    have hpi : Function.Injective p := by
      intro i j hij
      apply hinj Ω y
      simp only
      rw [← hp i, ← hp j, hij]
    let g := Equiv.ofBijective p (Finite.injective_iff_bijective.1 hpi)
    have hinjy : ∀ (Ω' : Type) [Field Ω'] (x' : UpperTheory.Gal.G3.sp Ω' ⟶ UpperTheory.Gal.G3.sp Ω),
        Function.Injective fun j => x' ≫ (y ≫ σ j) := by
      intro Ω' _ x' i j hij
      apply hinj Ω' (x' ≫ y)
      simpa only [Category.assoc] using hij
    refine ⟨g, ?_, ?_⟩
    · refine (huniv (UpperTheory.Gal.G3.sp Ω) (x ≫ c) (fun j => y ≫ σ j)
        (fun j => by rw [Category.assoc, hσ, hy]) hinjy).unique ⟨?_, fun j => ?_⟩ ⟨hy, fun j => rfl⟩
      · rw [Category.assoc, (ha g).1]
      · rw [Category.assoc, (ha g).2 j]
        exact hp j
    · intro g' hg'
      refine Equiv.ext fun j => ?_
      apply hinj Ω x
      simp only
      rw [← (ha g').2 j, ← Category.assoc, hg', ← hp j]
      rfl
  exact ⟨W, c, Equiv.Perm (Fin d), inferInstance, inferInstance, a, σ,
    ⟨hcf, hce, hsur, hone, hmul, hgal⟩, hspl⟩
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem fib_finite {V U : Scheme.{0}} (r : V ⟶ U) [IsFinite r] (K : Type) [Field K]
    (x : Spec (CommRingCat.of K) ⟶ U) : Finite {y : Spec (CommRingCat.of K) ⟶ V // y ≫ r = x} :=
  (UpperTheory.Gal.TranscendenceTraces.fibFin_of UpperTheory.Gal.TranscendenceTraces.chart_of r K x).to_subtype

private theorem fEt_of_pullback {P Y Z' Z : Scheme.{0}} (v : P ⟶ Y) (s' : P ⟶ Z') (s : Y ⟶ Z) (g : Z' ⟶ Z)
    (d : ℕ) (h : IsPullback v s' s g) (hs : FEt s d) : FEt s' d := by
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) h hs.1,
    MorphismProperty.of_isPullback (P := @Etale) h hs.2.1, fun K _ _ x => ?_⟩
  let eqv : {y' : Spec (CommRingCat.of K) ⟶ P // y' ≫ s' = x} ≃
      {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ s = x ≫ g} :=
    { toFun := fun y' => ⟨y'.1 ≫ v, by rw [Category.assoc, h.w, ← Category.assoc, y'.2]⟩
      invFun := fun y => ⟨h.lift y.1 x y.2, h.lift_snd _ _ _⟩
      left_inv := fun y' => Subtype.ext (h.hom_ext (by rw [h.lift_fst]) (by rw [h.lift_snd, y'.2]))
      right_inv := fun y => Subtype.ext (h.lift_fst _ _ _) }
  rw [Nat.card_congr eqv]
  exact hs.2.2 K (x ≫ g)

private theorem fEt_comp {W Y Z : Scheme.{0}} (r : W ⟶ Y) (s : Y ⟶ Z) (d e : ℕ) (hr : FEt r e) (hs : FEt s d) :
    FEt (r ≫ s) (d * e) := by
  haveI := hr.1
  haveI := hr.2.1
  haveI := hs.1
  haveI := hs.2.1
  refine ⟨inferInstance, inferInstance, fun K _ _ x => ?_⟩
  haveI : Fintype {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ s = x} :=
    @Fintype.ofFinite _ (fib_finite s K x)
  haveI hfin : ∀ y : {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ s = x},
      Finite {w : Spec (CommRingCat.of K) ⟶ W // w ≫ r = y.1} := fun y => fib_finite r K y.1
  let eqv : {w : Spec (CommRingCat.of K) ⟶ W // w ≫ r ≫ s = x} ≃
      Σ y : {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ s = x},
        {w : Spec (CommRingCat.of K) ⟶ W // w ≫ r = y.1} :=
    { toFun := fun w => ⟨⟨w.1 ≫ r, by rw [Category.assoc]; exact w.2⟩, ⟨w.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, by rw [← Category.assoc, p.2.2, p.1.2]⟩
      left_inv := fun w => rfl
      right_inv := by
        intro p
        rcases p with ⟨⟨y, hy⟩, ⟨w, hw⟩⟩
        dsimp only at hw
        subst hw
        rfl }
  rw [Nat.card_congr eqv, Nat.card_sigma, Finset.sum_congr rfl (fun y _ => hr.2.2 K y.1),
    Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hs.2.2 K x, smul_eq_mul]

private theorem fEt_galois (hp : PtsOfSplits) {W Z : Scheme.{0}} (c : W ⟶ Z) (G : Type) [Group G] [Finite G]
    (a : G → (W ⟶ W)) (h : IsGalois c G a) : FEt c (Nat.card G) := by
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2.1
  refine ⟨inferInstance, inferInstance, fun Ω _ _ x => ?_⟩
  obtain ⟨w, hw⟩ := Surjective.surj (f := c) (UpperTheory.Gal.TranscendenceTraces.pt x)
  obtain ⟨z, hz, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_of c Ω x w hw
  have hsp := h.2.2.2.2.2
  have hac : ∀ g, a g ≫ c = c := hsp.1
  have key : ∀ y : Spec (CommRingCat.of Ω) ⟶ W, y ≫ c = x → ∃! g : G, z ≫ a g = y :=
    fun y hy => hp c c G a hsp Ω z y (by rw [hy, hz])
  let f : G → {y : Spec (CommRingCat.of Ω) ⟶ W // y ≫ c = x} :=
    fun g => ⟨z ≫ a g, by rw [Category.assoc, hac, hz]⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro g g' hgg
      have hv : z ≫ a g = z ≫ a g' := congrArg Subtype.val hgg
      obtain ⟨g0, _, hu⟩ := key (z ≫ a g) (f g).2
      exact (hu g rfl).trans (hu g' hv.symm).symm
    · rintro ⟨y, hy⟩
      obtain ⟨g, hg, _⟩ := key y hy
      exact ⟨g, Subtype.ext hg⟩
  exact (Nat.card_congr (Equiv.ofBijective f hbij)).symm

theorem UpperTheory.Gal.G3.pFEtBasic :
    PtsOfSplits → FEtBasic := by
  intro hp
  exact ⟨fun v s' s g d h hs => fEt_of_pullback v s' s g d h hs, fun r s d e hr hs => fEt_comp r s d e hr hs,
    fun c G _ _ a h => fEt_galois hp c G a h⟩
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

namespace UpperTheory.Gal.G3.AlgebraSplitting

private noncomputable def sec {A A' C J : Type} [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A C]
    (τ : J → (A' →ₐ[A] C)) : C ⊗[A] A' →ₐ[C] (J → C) :=
  Pi.algHom C (fun _ => C) fun j =>
    Algebra.TensorProduct.lift (AlgHom.id C C) (τ j) fun _ _ => Commute.all _ _

private lemma sec_tmul {A A' C J : Type} [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A C]
    (τ : J → (A' →ₐ[A] C)) (c : C) (b : A') (j : J) : sec τ (c ⊗ₜ b) j = c * τ j b := by
  simp [sec]

private lemma tensor_hom_ext {A A' C Ω : Type} [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A C]
    [CommRing Ω] {u v : C ⊗[A] A' →+* Ω} (h₁ : ∀ c : C, u (c ⊗ₜ 1) = v (c ⊗ₜ 1))
    (h₂ : ∀ b : A', u (1 ⊗ₜ b) = v (1 ⊗ₜ b)) : u = v :=
  _root_.UpperTheory.Reformulated.B.Qk54.tensor_hom_ext h₁ h₂

private lemma exists_eval {C Ω J : Type} [CommRing C] [Field Ω] [Fintype J] (f : (J → C) →+* Ω) :
    ∃ j, ∀ v : J → C, f v = f (algebraMap C (J → C) (v j)) :=
  _root_.UpperTheory.Reformulated.B.ExistsEvaluation.exists_eval f

private lemma bij_of_pts (hiso : AlgIsoPts) {C D E : Type} [CommRing C] [CommRing D] [CommRing E] [Algebra C D]
    [Algebra C E] [Algebra.Etale C D] [Algebra.Etale C E] (φ : D →ₐ[C] E)
    (pts : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : D →+* Ω), ∃! y : E →+* Ω, y.comp (φ : D →+* E) = x) :
    Function.Bijective φ := by
  letI : Algebra D E := (φ : D →+* E).toAlgebra
  haveI : IsScalarTower C D E := IsScalarTower.of_algebraMap_eq' (φ.comp_algebraMap).symm
  haveI : Algebra.Etale D E := Algebra.Etale.of_restrictScalars C D E
  exact hiso D E pts

end UpperTheory.Gal.G3.AlgebraSplitting

open UpperTheory.Gal.G3.AlgebraSplitting in
theorem UpperTheory.Gal.G3.pAlgSplit :
    AlgIsoPts → AlgSplit := by
  intro hiso A A' C _ _ _ _ _ _ J _ τ h
  refine ⟨AlgEquiv.ofBijective (sec τ) (bij_of_pts hiso (sec τ) ?_), fun b j => ?_⟩
  swap
  · simp [sec_tmul]
  intro Ω _ _ x
  let x₀ : C →+* Ω := x.comp (Algebra.TensorProduct.includeLeftRingHom)
  let y₀ : A' →+* Ω := x.comp (Algebra.TensorProduct.includeRight : A' →ₐ[A] C ⊗[A] A').toRingHom
  have hx₀ : ∀ c, x₀ c = x (c ⊗ₜ 1) := fun _ => rfl
  have hy₀ : ∀ b, y₀ b = x (1 ⊗ₜ b) := fun _ => rfl
  have compat : y₀.comp (algebraMap A A') = x₀.comp (algebraMap A C) := by
    ext a
    simp only [RingHom.comp_apply, hx₀, hy₀]
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  obtain ⟨j, hj, huniq⟩ := h Ω x₀ y₀ compat
  have hτ : ∀ b, x₀ (τ j b) = y₀ b := fun b => congrArg (fun f : A' →+* Ω => f b) hj
  refine ⟨x₀.comp (Pi.evalRingHom (fun _ => C) j), ?_, ?_⟩
  · apply tensor_hom_ext
    · intro c
      simp [sec_tmul, hx₀]
    · intro b
      have := hτ b
      simp only [RingHom.comp_apply, RingHom.coe_coe, Pi.evalRingHom_apply, sec_tmul, one_mul]
      rw [this, hy₀]
  · intro y' hy'
    have hy'd : ∀ d, y' (sec τ d) = x d := fun d => congrArg (fun f : C ⊗[A] A' →+* Ω => f d) hy'
    obtain ⟨j', hj'⟩ := exists_eval y'
    have hal : ∀ c : C, y' (algebraMap C (J → C) c) = x₀ c := by
      intro c
      rw [hx₀, ← hy'd]
      congr 1
      funext i
      simp [sec_tmul]
    have hy'e : ∀ v : J → C, y' v = x₀ (v j') := fun v => by rw [hj', hal]
    have hjj : j' = j := by
      apply huniq
      ext b
      have := hy'e (sec τ (1 ⊗ₜ b))
      rw [hy'd, sec_tmul, one_mul] at this
      simpa [hy₀] using this.symm
    subst hjj
    ext v
    simp [hy'e]
end
