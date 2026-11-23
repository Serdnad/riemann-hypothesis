module

public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamPtClauses
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle017
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

@[expose] public section

section

set_option autoImplicit false

namespace GlobalTheory.LamT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

theorem isEigAt_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (x : Sp K ⟶ Xo.X) (t₀ : SAB H (Sp K)) (B : SAB H (Sp (𝓞 K))) (m : SABMap t₀ Xo.univ.t x) (m' : SABMap t₀ B (spMap (algebraMap (𝓞 K) K))) (τ : E →+* ℂ) (w : epsR K ⟶ t₀.G), (∀ a : 𝓞 E, ∃ w' : epsR K ⟶ t₀.G, IsLieComb ![LamF.labK c K τ (a : E)] ![w] w' ∧ w.left ≫ m'.φ ≫ (B.act.act a).left = w'.left ≫ m'.φ) → IsEigAt c τ (w.left ≫ m.φ) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ x t₀ B m m' τ w h a
  obtain ⟨w', ⟨u, hu, hw'⟩, e⟩ := h a
  have h1 : w'.left = spMap (epsScaleR (LamF.labK c K τ (a : E))) ≫ w.left := by
    rw [hw']
    simpa using hu 0
  have h2 : w.left ≫ (t₀.act.act a).left = w'.left := by
    apply m'.cart.1.hom_ext
    · rw [Category.assoc, m'.act a]
      exact e
    · rw [Category.assoc, Over.w (t₀.act.act a), Over.w w, Over.w w']
  rw [Category.assoc, ← m.act a, ← Category.assoc, h2, h1, Category.assoc]
  rfl

end GlobalTheory.LamT
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section

namespace GlobalTheory.LamF.Ind

open GlobalTheory.SqZero GlobalTheory.LieComb

section General

variable {R : Type} [CommRing R] {S : Scheme.{0}} (f : Sp R ⟶ S)

def scaleOver (c : R) : Over.mk ((epsR R).hom ≫ f) ⟶ Over.mk ((epsR R).hom ≫ f) :=
  (Over.map f).map (Chart.spMap (epsTo R (TrivSqZeroExt.inr c : DualNumber R)
    (TrivSqZeroExt.inr_mul_inr _ _ _)) : epsR R ⟶ epsR R)

variable {f} {G : Over S} {G' : Over (Sp R)} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
  [IsCommMonObj G'] {φ : G'.left ⟶ G.left}

theorem push_tanExp (Φ : (epsR R ⟶ G') ≃* (Over.mk ((epsR R).hom ≫ f) ⟶ G))
    (hΦ : ∀ x, (Φ x).left = x.left ≫ φ) {n : ℕ} (v : Fin n → (epsR R ⟶ G')) (c : Fin n → R) :
    Φ (tanExp v c) = ∏ i, scaleOver f (c i) ≫ Φ (v i) := by
  refine (map_prod Φ _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  apply Over.OverMorphism.ext
  rw [hΦ, Over.comp_left, Over.comp_left, hΦ, Category.assoc]
  rfl

theorem prod_comp {T G₁ : Over S} [GrpObj G₁] [IsCommMonObj G₁] (F : G ⟶ G₁) [IsMonHom F]
    {J : Type} (s : Finset J) (x : J → (T ⟶ G)) : (∏ i ∈ s, x i) ≫ F = ∏ i ∈ s, x i ≫ F :=
  map_prod (MonoidHom.mk' (fun y : T ⟶ G => y ≫ F) fun a b => MonObj.mul_comp a b F) x s


omit [GrpObj G] [IsCommMonObj G] in
theorem eq_zero_of_pow {K : Type} [Field K] [CharZero K] {A : Over (Sp K)} [GrpObj A]
    [IsCommMonObj A] {n : ℕ} {v : Fin n → (epsR K ⟶ A)} (hv : IsLieBasis v) {c : Fin n → K}
    {N : ℕ} (hN : 0 < N) (h : tanExp v c ^ N = 1) : c = 0 := by
  have h₁ : tanExp v (N • c) = tanExp v 0 := by
    change (combHom hv.1 (N • c)).toMul = (combHom hv.1 0).toMul
    rw [map_nsmul, map_zero, toMul_nsmul]
    exact h
  have h₂ := (isLieBasisOver_self hv).1 _ _ h₁
  funext i
  have := congrFun h₂ i
  simpa [hN.ne'] using this

end General

theorem lamInd : LamIndSt := by
  intro E _ _ _ _ H l cf _ nΨ n' f o La hg L hL hdet
  obtain ⟨-, -, -, hB, hΨ, h', -, -, -, -, -, -, -, ⟨hmΨ, hm', N, ψΨ, ψ', hN, -, hsum⟩, -⟩ := hg
  obtain ⟨hsrc, -, hw, -⟩ := hL
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  choose w hw hwc using hw
  obtain ⟨ΦB, hΦB⟩ := exists_mulEquiv_points_of_isGrpPullback _ _ _ _ _ _ hB.1 (epsR o.K₁)
  obtain ⟨ΦΨ, hΦΨ⟩ := exists_mulEquiv_points_of_isGrpPullback _ _ _ _ _ _ hΨ.1 (epsR o.K₁)
  obtain ⟨Φ', hΦ'⟩ := exists_mulEquiv_points_of_isGrpPullback _ _ _ _ _ _ h'.1 (epsR o.K₁)
  let e := Equiv.ofBijective _ hsrc
  have he : ∀ q, L.src (e.symm q) = q := fun q => e.apply_symm_apply q
  have hwl : ∀ j i, ΦB (w (e.symm (.inl (j, i)))) = ΦΨ (o.xΨ.v i) ≫ o.φΨ j := fun j i => by
    have := hw (e.symm (.inl (j, i)))
    rw [LamLetters.IsLetter, he] at this
    apply Over.OverMorphism.ext
    rw [hΦB, Over.comp_left, hΦΨ, Category.assoc]
    exact this
  have hwr : ∀ j i, ΦB (w (e.symm (.inr (j, i)))) = Φ' (o.x'.v i) ≫ o.φ' j := fun j i => by
    have := hw (e.symm (.inr (j, i)))
    rw [LamLetters.IsLetter, he] at this
    apply Over.OverMorphism.ext
    rw [hΦB, Over.comp_left, hΦ', Category.assoc]
    exact this
  have hone : tanExp w c = 1 := by
    obtain rfl : w = fun k => tanExp o.xB.v (L.U k) :=
      funext fun k => (isLieComb_iff_tanExp _ _).1 (hwc k)
    refine (tanExp_tanExp o.xB.basis.1 (fun k => L.U k) c).trans ?_
    rw [← Matrix.vecMul_eq_sum, hc]
    exact lieExp_eq_one o.xB.basis.1 _ (fun _ => rfl) _
  have hpad : ∀ a b : Over.mk ((epsR o.K₁).hom ≫ gmap o.K₁) ⟶ o.B.A,
      padd _ a b = a * b := fun _ _ => rfl
  have hps : ∀ (n : ℕ) (f : Fin n → (Over.mk ((epsR o.K₁).hom ≫ gmap o.K₁) ⟶ o.B.A)),
      psumPt f = (List.ofFn f).prod := by
    intro n f
    rw [List.prod_eq_foldr]
    rfl
  have hpow : ∀ (G : Over (Sp (𝓞 o.K₁))) [GrpObj G] (n : ℕ)
      (a : Over.mk ((epsR o.K₁).hom ≫ gmap o.K₁) ⟶ G), pnsmulPt n a = a ^ n := by
    intro G _ n a
    induction n with
    | zero => rw [pow_zero]; rfl
    | succ n ih => rw [pow_succ, ← ih]; rfl
  let a := fun j => ΦΨ (tanExp o.xΨ.v fun i => c (e.symm (.inl (j, i))))
  let a' := fun j => Φ' (tanExp o.x'.v fun i => c (e.symm (.inr (j, i))))
  have hs : padd o.B.A (psumPt fun k => a k ≫ o.φΨ k) (psumPt fun k => a' k ≫ o.φ' k) = 1 := by
    rw [hpad, hps, hps, List.prod_ofFn, List.prod_ofFn, ← map_one ΦB, ← hone,
      push_tanExp ΦB hΦB, ← e.symm.prod_comp, Fintype.prod_sum_type, Fintype.prod_prod_type,
      Fintype.prod_prod_type]
    congr 1 <;> refine Finset.prod_congr rfl fun j _ => ?_
    · have := hmΨ j
      simp only [a, push_tanExp ΦΨ hΦΨ, prod_comp, hwl, Category.assoc]
    · have := hm' j
      simp only [a', push_tanExp Φ' hΦ', prod_comp, hwr, Category.assoc]
  have hs₀ : padd o.B.A
      (psumPt fun k => (1 : Over.mk ((epsR o.K₁).hom ≫ gmap o.K₁) ⟶ _) ≫ o.φΨ k)
      (psumPt fun k => (1 : Over.mk ((epsR o.K₁).hom ≫ gmap o.K₁) ⟶ _) ≫ o.φ' k) = 1 := by
    rw [hpad, hps, hps, List.prod_ofFn, List.prod_ofFn, Finset.prod_eq_one, Finset.prod_eq_one,
      _root_.mul_one]
    · intro j _
      have := hm' j
      exact MonObj.one_comp _
    · intro j _
      have := hmΨ j
      exact MonObj.one_comp _
  obtain ⟨p₁, p₂⟩ := hsum _ a a'
  obtain ⟨q₁, q₂⟩ := hsum _ (fun _ => 1) (fun _ => 1)
  rw [hs] at p₁ p₂
  rw [hs₀] at q₁ q₂
  apply hc0
  funext k
  obtain ⟨q, rfl⟩ := e.symm.surjective k
  rcases q with ⟨j, i⟩ | ⟨j, i⟩
  · have h := (p₁ j).symm.trans (q₁ j)
    rw [hpow _, hpow _, one_pow,
      ← map_pow, map_eq_one_iff _ ΦΨ.injective] at h
    exact congrFun (eq_zero_of_pow o.xΨ.basis hN h) i
  · have h := (p₂ j).symm.trans (q₂ j)
    rw [hpow _, hpow _, one_pow,
      ← map_pow, map_eq_one_iff _ Φ'.injective] at h
    exact congrFun (eq_zero_of_pow o.x'.basis hN h) i

end GlobalTheory.LamF.Ind
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LamF

theorem pnsmulPt_eq_frozen {S : Scheme.{0}} {G : Over S} [GrpObj G] {T : Over S} (n : ℕ) (x : T ⟶ G) :
    pnsmulPt n x = Formalism.L2.Pj.abelian₂.pnsmulPt n x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pnsmulPt, Formalism.L2.Pj.abelian₂.pnsmulPt, ih]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {H : Host E} {l : Level H}
  {c : Coeff l} {nΨ n' : ℕ}

@[reducible] def LamObj.toFrozen (o : LamObj c nΨ n') : Formalism.L2.Pj.abelian₂.LamObj c nΨ n' where
  K₁ := o.K₁
  B := o.B
  oa := o.oa
  AΨ := o.AΨ
  oaΨ := o.oaΨ
  A' := o.A'
  oa' := o.oa'
  φΨ := o.φΨ
  φ' := o.φ'
  hΨ := o.hΨ
  h' := o.h'
  xB := o.xB
  xΨ := o.xΨ
  x' := o.x'
  φB := o.φB
  φΨg := o.φΨg
  φ'g := o.φ'g
  τΨ := o.τΨ
  τ' := o.τ'
  ℓΨ := o.ℓΨ
  ℓ' := o.ℓ'
  Tl := o.Tl
  LamL := o.LamL

@[reducible] def LamObj.ofFrozen (o : Formalism.L2.Pj.abelian₂.LamObj c nΨ n') : LamObj c nΨ n' where
  K₁ := o.K₁
  B := o.B
  oa := o.oa
  AΨ := o.AΨ
  oaΨ := o.oaΨ
  A' := o.A'
  oa' := o.oa'
  φΨ := o.φΨ
  φ' := o.φ'
  hΨ := o.hΨ
  h' := o.h'
  xB := o.xB
  xΨ := o.xΨ
  x' := o.x'
  φB := o.φB
  φΨg := o.φΨg
  φ'g := o.φ'g
  τΨ := o.τΨ
  τ' := o.τ'
  ℓΨ := o.ℓΨ
  ℓ' := o.ℓ'
  Tl := o.Tl
  LamL := o.LamL

theorem rosatiConj_iff_frozen {K : Type} [Field K] [NumberField K] (A : PolAV (Sp (𝓞 K))) (oa : A.OAct (𝓞 E)) :
    RosatiConj A oa ↔ Formalism.L2.Pj.abelian₂.RosatiConj A oa := by
  simp only [RosatiConj, Formalism.L2.Pj.abelian₂.RosatiConj, pnsmulPt_eq_frozen]

theorem isIsogSum_toFrozen (o : LamObj c nΨ n') : Formalism.L2.Pj.abelian₂.IsIsogSum o.toFrozen ↔ IsIsogSum o := by
  simp only [IsIsogSum, Formalism.L2.Pj.abelian₂.IsIsogSum, pnsmulPt_eq_frozen]
  rfl

theorem polClause_toFrozen (o : LamObj c nΨ n') : Formalism.L2.Pj.abelian₂.PolClause o.toFrozen ↔ PolClause o := by
  simp only [PolClause, Formalism.L2.Pj.abelian₂.PolClause, pnsmulPt_eq_frozen]

theorem fixed_of_lambdaBundle_objectCondition (o : LamObj c nΨ n') (f : ℕ) (La : ℝ) :
    Formalism.L2.Pj.abelian₂.LamObjGood o.toFrozen f La ↔ LamObjGood o f La := by
  unfold LamObjGood Formalism.L2.Pj.abelian₂.LamObjGood
  rw [isIsogSum_toFrozen, polClause_toFrozen, rosatiConj_iff_frozen, rosatiConj_iff_frozen, rosatiConj_iff_frozen]
  rfl

theorem lambdaBundle_objectCondition_of_fixed (o : Formalism.L2.Pj.abelian₂.LamObj c nΨ n') (f : ℕ) (La : ℝ) :
    LamObjGood (LamObj.ofFrozen o) f La ↔ Formalism.L2.Pj.abelian₂.LamObjGood o f La :=
  (fixed_of_lambdaBundle_objectCondition (LamObj.ofFrozen o) f La).symm

@[reducible] def LamLetters.toFrozen {o : LamObj c nΨ n'} (L : LamLetters o) : Formalism.L2.Pj.abelian₂.LamLetters o.toFrozen where
  m := L.m
  e := L.e
  src := L.src
  U := L.U
  ℓ := L.ℓ

@[reducible] def LamLetters.ofFrozen {o : Formalism.L2.Pj.abelian₂.LamObj c nΨ n'} (L : Formalism.L2.Pj.abelian₂.LamLetters o) :
    LamLetters (LamObj.ofFrozen o) where
  m := L.m
  e := L.e
  src := L.src
  U := L.U
  ℓ := L.ℓ

theorem LamLetters.isLetter_toFrozen {o : LamObj c nΨ n'} (L : LamLetters o) (k : Fin o.xB.P.g)
    (w : epsR o.K₁ ⟶ o.xB.P.A) : L.toFrozen.IsLetter k w ↔ L.IsLetter k w := by
  unfold LamLetters.IsLetter Formalism.L2.Pj.abelian₂.LamLetters.IsLetter
  dsimp only
  cases L.src k <;> rfl

theorem LamLetters.isGood_toFrozen {o : LamObj c nΨ n'} (L : LamLetters o) : L.toFrozen.IsGood ↔ L.IsGood := by
  unfold LamLetters.IsGood Formalism.L2.Pj.abelian₂.LamLetters.IsGood
  refine and_congr Iff.rfl (and_congr (forall_congr' fun b => forall_congr' fun i => ?_)
    (and_congr (forall_congr' fun k => exists_congr fun w => and_congr (L.isLetter_toFrozen k w) Iff.rfl)
      (forall_congr' fun k => ?_)))
  · dsimp only
    cases L.src (L.e ⟨b, i⟩) <;> rfl
  · dsimp only
    cases L.src k <;> rfl

theorem LamLetters.isGood_ofFrozen {o : Formalism.L2.Pj.abelian₂.LamObj c nΨ n'} (L : Formalism.L2.Pj.abelian₂.LamLetters o) :
    (LamLetters.ofFrozen L).IsGood ↔ L.IsGood :=
  (LamLetters.isGood_toFrozen (LamLetters.ofFrozen L)).symm

omit [StarRing (𝓞 E)] in
theorem lambdaBundle_degree_iff (H : Host E) (x : ℝ) : LamDegSt H x ↔ Formalism.L2.Pj.abelian₂.LamDegSt H x :=
  ⟨fun h _ l c hs nΨ n' f o La ho => h l c hs nΨ n' f (LamObj.ofFrozen o) La ((lambdaBundle_objectCondition_of_fixed o f La).2 ho),
   fun h _ l c hs nΨ n' f o La ho => h l c hs nΨ n' f o.toFrozen La ((fixed_of_lambdaBundle_objectCondition o f La).2 ho)⟩

theorem lambdaBundle_index_iff : LamIndSt ↔ Formalism.L2.Pj.abelian₂.LamIndSt :=
  ⟨fun h E _ _ _ _ H l c hs nΨ n' f o La ho L hL =>
      h E H l c hs nΨ n' f (LamObj.ofFrozen o) La ((lambdaBundle_objectCondition_of_fixed o f La).2 ho) (LamLetters.ofFrozen L)
        ((LamLetters.isGood_ofFrozen L).2 hL),
   fun h E _ _ _ _ H l c hs nΨ n' f o La ho L hL =>
      h E H l c hs nΨ n' f o.toFrozen La ((fixed_of_lambdaBundle_objectCondition o f La).2 ho) L.toFrozen (L.isGood_toFrozen.2 hL)⟩

theorem lambdaBundle_length_iff : LamLenSt ↔ Formalism.L2.Pj.abelian₂.LamLenSt :=
  ⟨fun h E _ _ _ _ H l c hs nΨ n' f o La ho L hL =>
      h E H l c hs nΨ n' f (LamObj.ofFrozen o) La ((lambdaBundle_objectCondition_of_fixed o f La).2 ho) (LamLetters.ofFrozen L)
        ((LamLetters.isGood_ofFrozen L).2 hL),
   fun h E _ _ _ _ H l c hs nΨ n' f o La ho L hL =>
      h E H l c hs nΨ n' f o.toFrozen La ((fixed_of_lambdaBundle_objectCondition o f La).2 ho) L.toFrozen (L.isGood_toFrozen.2 hL)⟩

theorem lambdaBundle_conditions_iff :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (x : ℝ),
      GlobalTheory.LamF.LamDegSt H x ↔ Formalism.L2.Pj.abelian₂.LamDegSt H x) ∧
    (GlobalTheory.LamF.LamIndSt ↔ Formalism.L2.Pj.abelian₂.LamIndSt) ∧ (GlobalTheory.LamF.LamLenSt ↔ Formalism.L2.Pj.abelian₂.LamLenSt) :=
  ⟨fun _ _ _ _ H x => lambdaBundle_degree_iff H x, lambdaBundle_index_iff, lambdaBundle_length_iff⟩

end GlobalTheory.LamF
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem valuative_lift_of_isProper {V K : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {X S : Scheme.{0}} (s : X ⟶ S) [IsProper s] (y : Sp K ⟶ X) (r : Sp V ⟶ S)
    (h : y ≫ s = spMap (algebraMap V K) ≫ r) :
    ∃ x : Sp V ⟶ X, spMap (algebraMap V K) ≫ x = y ∧ x ≫ s = r := by
  have hE : ValuativeCriterion.Existence s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) s).1
  obtain ⟨⟨l⟩⟩ := hE { R := V, K := K, i₁ := y, i₂ := r, commSq := ⟨h⟩ }
  exact ⟨l.l, l.fac_left, l.fac_right⟩

theorem range_subset_abLocus_of_isProper {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G]
    (hG : IsSemiAbelian G) {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsPullback φ G'.hom G.hom f)
    [IsProper G'.hom] : Set.range f ⊆ abLocus G := by
  rintro _ ⟨x, rfl⟩
  refine (abLocus_pullback abLocusOne hG h x).2 ?_
  intro K _ _ t _
  infer_instance

theorem model_point_extends :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l)
  (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
  (b : O →+* V) (y : Sp K ⟶ Xo.XF c), y ≫ Y.j ≫ Y.s = spMap (algebraMap V K) ≫ spMap b →
  ∃ (y' : Sp V ⟶ Y.X) (t : SAB H (Sp V)) (_ : SABMap t Y.t y'), y' ≫ Y.s = spMap b ∧ spMap (algebraMap V K) ≫ y' = y ≫ Y.j ∧
    (IsAbelianScheme t.G → Set.range y' ⊆ abLocus Y.t.G) := by
  intro E _ _ _ H D l Xo c O _ β Y V K _ _ _ _ _ _ b y hy
  have := projProper O Y.X Y.s Y.proj
  obtain ⟨y', h₁, h₂⟩ := valuative_lift_of_isProper Y.s (y ≫ Y.j) (spMap b) (by rw [Category.assoc, hy])
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull y' Y.t
  refine ⟨y', _, m, h₂, h₁, fun hA => ?_⟩
  have := hA.proper
  exact range_subset_abLocus_of_isProper Y.t.semi m.cart.1

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.kernelPolarisation_trivial_of_sections_vanish_zero : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (θ : L.Sec), L.IsLB → (∀ (T : Scheme.{0}) (t : T ⟶ A.left) (i : L.ι) (h : ⊤ ≤ t ⁻¹ᵁ L.U i), (t.appLE (L.U i) ⊤ h).hom (θ.f i) = 0 ↔ t = t ≫ A.hom ≫ eSec A) → (∀ (R' : Type) [CommRing R'] (f : Sp R' ⟶ S) (Y : Scheme.{0}) (φ : Y ⟶ A.left) (q : Y ⟶ Sp R'), IsPullback φ q A.hom f → ∀ (s : (L.pull φ).Sec) (T : Scheme.{0}) (t : T ⟶ Y) (j : (L.pull φ).ι) (h : ⊤ ≤ t ⁻¹ᵁ (L.pull φ).U j), t ≫ φ = t ≫ φ ≫ A.hom ≫ eSec A → (t.appLE ((L.pull φ).U j) ⊤ h).hom (s.f j) = 0) → Out.KTriv A L := by
  first | exact @GlobalTheory.kTriv_of_sections_vanish_on_zero | exact GlobalTheory.kTriv_of_sections_vanish_on_zero | (intros; apply GlobalTheory.kTriv_of_sections_vanish_on_zero <;> assumption)
end
