module

public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamPtClauses
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle020
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_lieComb_image {R R' : Type} [CommRing R] [CommRing R'] (A B : Out.PolAV (Sp R)) (x y : KeyIn R')
    (f : Sp R' ⟶ Sp R) (φ : x.P.A.left ⟶ A.A.left) (ψ : y.P.A.left ⟶ B.A.left)
    (hx : IsFibreOf A x f φ) (hy : IsFibreOf B y f ψ) (F : A.A ⟶ B.A) (hF : IsMonHom F) (i : Fin x.P.g) :
    ∃ (u : Fin y.P.g → R') (w : epsR R' ⟶ y.P.A), w.left ≫ ψ = (x.v i).left ≫ φ ≫ F.left ∧ IsLieComb u y.v w := by
  obtain ⟨⟨F', hF', -⟩, hmon⟩ := existsUnique_hom_of_isGrpPullback _ _ f A.A B.A x.P.A y.P.A φ ψ hx.1 hy.1 F
  have hm : IsMonHom F' := hmon F' hF' hF
  have ht : IsTangent (x.v i ≫ F') :=
    ((GlobalTheory.LieCombHom.lieComb_add_pow_map R' x.P.A y.P.A x.P.g x.v x.basis.1).2.2.2 F' hm).1 i
  obtain ⟨u, hu, -⟩ := y.basis.2 _ ht
  exact ⟨u, x.v i ≫ F', by rw [Over.comp_left, Category.assoc, hF'], hu⟩

def blockEquiv {T : Type} (p : T → Prop) [DecidablePred p] (a b : ℕ) {α β : Type} (s : α ≃ {t // p t})
    (s' : β ≃ {t // ¬ p t}) : (Σ t, Fin (if p t then a else b)) ≃ (Fin a × α) ⊕ (Fin b × β) where
  toFun z := if h : p z.1 then Sum.inl (z.2.cast (if_pos h), s.symm ⟨z.1, h⟩)
    else Sum.inr (z.2.cast (if_neg h), s'.symm ⟨z.1, h⟩)
  invFun
    | Sum.inl q => ⟨(s q.2).1, q.1.cast (if_pos (s q.2).2).symm⟩
    | Sum.inr q => ⟨(s' q.2).1, q.1.cast (if_neg (s' q.2).2).symm⟩
  left_inv := by
    rintro ⟨t, i⟩
    by_cases h : p t
    · simp only [dif_pos h]
      refine Sigma.ext (by simp) ?_
      exact (Fin.heq_ext_iff (by simp)).2 rfl
    · simp only [dif_neg h]
      refine Sigma.ext (by simp) ?_
      exact (Fin.heq_ext_iff (by simp)).2 rfl
  right_inv := by
    rintro (q | q)
    · simp [dif_pos (s q.2).2]
    · simp [dif_neg (s' q.2).2]

theorem exists_lamLetters_isGood : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La → ∃ L : LamLetters o, L.IsGood ∧ ∀ b : E →+* ℂ, (b (H.rt : E) = H.rt0 → L.m b = nΨ) ∧ (b (H.rt : E) ≠ H.rt0 → L.m b = n') := by
  intro E _ _ _ _ H l c nΨ n' f o La hg
  classical
  obtain ⟨-, -, -, hB, hΨ, h', g1, g2, g3, -, -, -, -, ⟨m1, m2, -⟩, -⟩ := hg
  let p : (E →+* ℂ) → Prop := fun b => b (H.rt : E) = H.rt0
  let ε := blockEquiv p nΨ n' o.τΨ o.τ'
  have hc : Fintype.card ((Fin nΨ × Fin o.xΨ.P.g) ⊕ (Fin n' × Fin o.x'.P.g)) = o.xB.P.g := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    rw [g1, g2, g3]; ring
  let κ := Fintype.equivFinOfCardEq hc
  have hU : ∀ q : (Fin nΨ × Fin o.xΨ.P.g) ⊕ (Fin n' × Fin o.x'.P.g),
      ∃ (u : Fin o.xB.P.g → o.K₁) (w : epsR o.K₁ ⟶ o.xB.P.A),
        (match q with
          | Sum.inl q => w.left ≫ o.φB = (o.xΨ.v q.2).left ≫ o.φΨg ≫ (o.φΨ q.1).left
          | Sum.inr q => w.left ≫ o.φB = (o.x'.v q.2).left ≫ o.φ'g ≫ (o.φ' q.1).left) ∧ IsLieComb u o.xB.v w := by
    rintro (q | q)
    · exact exists_lieComb_image _ _ _ _ _ _ _ hΨ hB _ (m1 q.1) q.2
    · exact exists_lieComb_image _ _ _ _ _ _ _ h' hB _ (m2 q.1) q.2
  choose u w hw hu using hU
  refine ⟨⟨fun b => if p b then nΨ else n', ε.trans κ, κ.symm, fun k => u (κ.symm k),
    fun k => Sum.elim (fun q => o.ℓΨ q.2) (fun q => o.ℓ' q.2) (κ.symm k)⟩, ⟨κ.symm.bijective, ?_, ?_, ?_⟩, ?_⟩
  · intro b i
    have : κ.symm ((ε.trans κ) ⟨b, i⟩) = ε ⟨b, i⟩ := by simp
    simp only [this]
    by_cases h : p b
    · have e1 : ε ⟨b, i⟩ = Sum.inl (i.cast (if_pos h), o.τΨ.symm ⟨b, h⟩) := dif_pos h
      rw [e1]; simp
    · have e1 : ε ⟨b, i⟩ = Sum.inr (i.cast (if_neg h), o.τ'.symm ⟨b, h⟩) := dif_neg h
      rw [e1]; simp
  · intro k
    refine ⟨w (κ.symm k), ?_, hu _⟩
    have := hw (κ.symm k)
    unfold LamLetters.IsLetter
    dsimp only
    generalize κ.symm k = q at this ⊢
    cases q <;> exact this
  · intro k
    dsimp only
    generalize κ.symm k = q
    cases q <;> rfl
  · intro b
    exact ⟨fun h => if_pos h, fun h => if_neg h⟩

end GlobalTheory.LamF
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

theorem _root_.GlobalTheory.T.cmLieStatements_iff_library : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (x : ℝ), GlobalTheory.LamF.LamDegSt H x ↔ Formalism.L2.Pj.abelian₂.LamDegSt H x) ∧ (GlobalTheory.LamF.LamIndSt ↔ Formalism.L2.Pj.abelian₂.LamIndSt) ∧ (GlobalTheory.LamF.LamLenSt ↔ Formalism.L2.Pj.abelian₂.LamLenSt) := by
  first | exact @GlobalTheory.LamF.lambdaBundle_conditions_iff | exact GlobalTheory.LamF.lambdaBundle_conditions_iff | (intros; apply GlobalTheory.LamF.lambdaBundle_conditions_iff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_torsion_fieldExt : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (k k' : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field k'] [IsAlgClosed k'] (j : k →+* k') (t : Sp k ⟶ S), ∃ r : (Over.mk t ⟶ P.A) →* (Over.mk (spMap j ≫ t) ⟶ P.A), (∀ x, (r x).left = spMap j ≫ x.left) ∧ Function.Injective r ∧ (∀ (n : ℕ) y, 0 < n → y ^ n = 1 → ∃ x, r x = y) ∧ ∀ (n : ℕ) x y (c : kˣ), 0 < n → x ^ n = 1 → y ^ n = 1 → (Out.WeilIs P.A P.L n x y (unitOn c) ↔ Out.WeilIs P.A P.L n (r x) (r y) (unitOn (Units.map j.toMonoidHom c))) := by
  intro hL S _ P k k' _ _ _ _ _ j t
  let h : Over.mk (spMap j ≫ t) ⟶ Over.mk t := Over.homMk (spMap j) rfl
  let r : (Over.mk t ⟶ P.A) →* (Over.mk (spMap j ≫ t) ⟶ P.A) :=
    { toFun := fun x => h ≫ x, map_one' := comp_one _, map_mul' := fun x y => comp_mul _ _ _ }
  have hr : Function.Injective r := by
    letI := j.toAlgebra
    haveI : Flat (spMap j) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact (inferInstance : Module.Flat k k')
    haveI : Surjective (spMap j) := ⟨fun p => ⟨(⊥ : PrimeSpectrum k'), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
    haveI : Epi h.left := Flat.epi_of_flat_of_surjective (spMap j)
    haveI : Epi h := Over.epi_of_epi_left _
    exact fun x y e => (cancel_epi h).1 e
  have hu : ∀ c : kˣ, Units.map h.left.appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map j.toMonoidHom c) :=
    fun c => Units.ext (congrArg (fun q => q.hom (c : k))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm
  have up : ∀ (n : ℕ) x y (c : kˣ), Out.WeilIs P.A P.L n x y (unitOn c) →
      Out.WeilIs P.A P.L n (r x) (r y) (unitOn (Units.map j.toMonoidHom c)) := fun n x y c H =>
    hu c ▸ CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB h H
  refine ⟨r, fun _ => rfl, hr, fun n y hn hy => ?_, fun n x y c _ hx hy => ⟨up n x y c, fun H => ?_⟩⟩
  · have hk : (n : k) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hk' : (n : k') ≠ 0 := by rw [← map_natCast j]; exact (map_ne_zero j).2 hk
    have c₁ := (hL.mulN S P n hn).2.2.2.2 k t hk
    have c₂ := (hL.mulN S P n hn).2.2.2.2 k' (spMap j ≫ t) hk'
    let f : {x : Over.mk t ⟶ P.A // x ^ n = 1} → {x : Over.mk (spMap j ≫ t) ⟶ P.A // x ^ n = 1} :=
      fun x => ⟨r x.1, by rw [← map_pow, x.2, map_one]⟩
    have hf : Function.Injective f := fun a b e => Subtype.ext (hr (congrArg Subtype.val e))
    haveI : Finite {x : Over.mk (spMap j ≫ t) ⟶ P.A // x ^ n = 1} :=
      Nat.finite_of_card_ne_zero (by rw [c₂]; positivity)
    obtain ⟨x, hx⟩ := (hf.bijective_of_nat_card_le (by rw [c₁, c₂])).2 ⟨y, hy⟩
    exact ⟨x.1, congrArg Subtype.val hx⟩
  · obtain ⟨d, hd, -⟩ := (hL.weil S P n (Over.mk t)).1 x y hx hy
    let u : kˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom d
    have e : unitOn u = d := Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of k)) d.val)
    rw [← e] at hd
    have e₁ := ((hL.weil S P n (Over.mk (spMap j ≫ t))).1 (r x) (r y) (by rw [← map_pow, hx, map_one])
      (by rw [← map_pow, hy, map_one])).unique (up n x y u hd) H
    have e₂ : u = c := Units.ext (j.injective
      ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k')).inv).1 (congrArg Units.val e₁)))
    exact e₂ ▸ hd

end GlobalTheory
end
