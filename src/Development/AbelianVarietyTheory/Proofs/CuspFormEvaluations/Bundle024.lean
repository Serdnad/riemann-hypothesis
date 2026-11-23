module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsSecondPartialLaw
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree

namespace GlobalTheory.NetMulti

theorem component_mem_SS {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r) {P : FDSec X} (h : P ∈ holSub X la) :
    ∀ k, P k ∈ (X k).SS (la k) := by
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.1
  | add x y _ _ hx hy =>
    exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.1 _ (hx k) _ (hy k)
  | smul a x _ hx => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 a _ (hx k)

theorem one_le_absDisc (E : Type) [Field E] [NumberField E] [IsCMField E] : 1 ≤ dE E := by
  have h : (1 : ℤ) ≤ |discr E| := Int.one_le_abs (discr_ne_zero E)
  unfold dE
  exact_mod_cast h

end GlobalTheory.NetMulti
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FlatRoots

theorem exists_lift {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f]
    (S : Type) [CommRing S] (t : Sp S ⟶ Y) :
    ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : Sp B ⟶ X),
      φ.FaithfullyFlat ∧ w ≫ f = spMap φ ≫ t := by
  haveI : IsAffine (pullback t f) := isAffine_of_isAffineHom (pullback.fst t f)
  let e := (pullback t f).isoSpec
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (e.inv ≫ pullback.fst t f)
  have hff : ψ.hom.FaithfullyFlat := by
    rw [← flat_and_surjective_SpecMap_iff, hψ]
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨Γ(pullback t f, ⊤), inferInstance, ψ.hom, e.inv ≫ pullback.snd t f, hff, ?_⟩
  change _ = Spec.map ψ ≫ t
  rw [hψ, Category.assoc, Category.assoc, pullback.condition]

theorem spMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem exists_lifts {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f]
    (S : Type) [CommRing S] (J : Type) (t : J → (Sp S ⟶ Y)) (s : Finset J) :
    ∃ (B : Type) (_ : CommRing B) (φ : S →+* B), φ.FaithfullyFlat ∧
      ∀ i ∈ s, ∃ w : Sp B ⟶ X, w ≫ f = spMap φ ≫ t i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨S, inferInstance, RingHom.id S, RingHom.FaithfullyFlat.of_bijective Function.bijective_id,
      fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert j s _ ih =>
    obtain ⟨B, _, φ, hφ, h⟩ := ih
    obtain ⟨C, _, ψ, w, hψ, hw⟩ := exists_lift f B (spMap φ ≫ t j)
    refine ⟨C, inferInstance, ψ.comp φ, RingHom.FaithfullyFlat.stableUnderComposition φ ψ hφ hψ, fun i hi => ?_⟩
    rw [spMap_comp, Category.assoc]
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨w, hw⟩
    · obtain ⟨v, hv⟩ := h i hi
      exact ⟨spMap ψ ≫ v, by rw [Category.assoc, hv]⟩

end FlatRoots

theorem exists_faithfullyFlat_roots :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X) (N k : ℕ), 0 < N → 0 < k → ∀ (J : Type) [Fintype J] (t : J → (ptO Xo x0 ⟶ Xo.univ.t.G)), (∀ i, t i ^ k = 1) → ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : J → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.FaithfullyFlat ∧ ∀ i, (w i ^ N).left = spMap φ ≫ (t i).left := by
  intro hL E _ _ _ H Dw l Xo S _ x0 N k hN _ J _ t _
  haveI := UnivPol.isLocallyNoetherian Xo
  obtain ⟨h1, h2, h3, -⟩ := hL.mulN _ (UnivPol.pol Xo) N hN
  let m : Xo.univ.t.G ⟶ Xo.univ.t.G := (𝟙 Xo.univ.t.G) ^ N
  haveI : IsFinite m.left := h1
  haveI : Flat m.left := h2
  haveI : Surjective m.left := h3
  obtain ⟨B, _, φ, hφ, h⟩ := FlatRoots.exists_lifts m.left S J (fun i => (t i).left) Finset.univ
  choose w hw using fun i => h i (Finset.mem_univ i)
  have hb : ∀ i, w i ≫ Xo.univ.t.G.hom = spMap φ ≫ x0 := fun i => by
    rw [← Over.w m, ← Category.assoc, hw i, Category.assoc, Over.w (t i)]
    rfl
  refine ⟨B, inferInstance, φ, fun i => Over.homMk (w i) (hb i), hφ, fun i => ?_⟩
  have e : ∀ x : ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G, x ^ N = x ≫ m := fun x => by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [e, Over.comp_left]
  exact hw i

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TorsTuple

theorem exists_power {X : Scheme.{0}} (Q : Over X) [IsAffineHom Q.hom] [Flat Q.hom] (J : Type) [Finite J] :
    ∃ (R : Over X) (p : J → (R ⟶ Q)), IsAffineHom R.hom ∧ Flat R.hom ∧
      ∀ (T : Over X) (u : J → (T ⟶ Q)), ∃ v : T ⟶ R, ∀ i, v ≫ p i = u i := by

  have key : ∀ n : ℕ, ∃ (R : Over X) (p : Fin n → (R ⟶ Q)), IsAffineHom R.hom ∧ Flat R.hom ∧
      ∀ (T : Over X) (u : Fin n → (T ⟶ Q)), ∃ v : T ⟶ R, ∀ i, v ≫ p i = u i := by
    intro n
    induction n with
    | zero =>
      refine ⟨Over.mk (𝟙 X), fun i => i.elim0, ?_, ?_, fun T u => ⟨Over.homMk T.hom (by simp), fun i => i.elim0⟩⟩
      · show IsAffineHom (𝟙 X)
        infer_instance
      · show Flat (𝟙 X)
        infer_instance
    | succ n ih =>
      obtain ⟨R, p, hRa, hRf, hR⟩ := ih
      have ha : IsAffineHom (pullback.fst R.hom Q.hom) :=
        MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
          (IsPullback.of_hasPullback R.hom Q.hom).flip ‹_›
      let R' : Over X := Over.mk (pullback.fst R.hom Q.hom ≫ R.hom)
      let a : R' ⟶ Q := Over.homMk (pullback.snd R.hom Q.hom) pullback.condition.symm
      let b : R' ⟶ R := Over.homMk (pullback.fst R.hom Q.hom) rfl
      refine ⟨R', Fin.cons (α := fun _ => R' ⟶ Q) a (fun i => b ≫ p i), ?_, ?_, ?_⟩
      · show IsAffineHom (pullback.fst R.hom Q.hom ≫ R.hom)
        infer_instance
      · show Flat (pullback.fst R.hom Q.hom ≫ R.hom)
        infer_instance
      · intro T u
        obtain ⟨v, hv⟩ := hR T (fun i => u i.succ)
        have hc : v.left ≫ R.hom = (u 0).left ≫ Q.hom := by rw [Over.w v, Over.w (u 0)]
        refine ⟨Over.homMk (pullback.lift v.left (u 0).left hc) (by
          change _ ≫ pullback.fst R.hom Q.hom ≫ R.hom = _
          rw [pullback.lift_fst_assoc, Over.w v]), ?_⟩
        refine Fin.cases ?_ (fun i => ?_)
        · apply Over.OverMorphism.ext
          simp only [a, Fin.cons_zero, Over.comp_left, Over.homMk_left]
          exact pullback.lift_snd _ _ _
        · apply Over.OverMorphism.ext
          simp only [b, Fin.cons_succ, Over.comp_left, Over.homMk_left, ← hv i]
          rw [pullback.lift_fst_assoc]
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  obtain ⟨R, p, ha, hf, hu⟩ := key n
  refine ⟨R, fun j => p (e j), ha, hf, fun T u => ?_⟩
  obtain ⟨v, hv⟩ := hu T (fun i => u (e.symm i))
  exact ⟨v, fun j => by simpa using hv (e j)⟩

theorem exists_point {X : Scheme.{0}} (R : Over X) [IsAffineHom R.hom] [Flat R.hom] (S : Type) [CommRing S]
    (x0 : Sp S ⟶ X) :
    ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : Over.mk (spMap φ ≫ x0) ⟶ R), φ.Flat ∧
      ∀ (T : Type) [CommRing T] (ψ : S →+* T) (u : Over.mk (spMap ψ ≫ x0) ⟶ R),
        ∃ χ : B →+* T, χ.comp φ = ψ ∧ u.left = spMap χ ≫ w.left := by

  have : IsAffine (pullback x0 R.hom) := inferInstance
  let e := (pullback x0 R.hom).isoSpec
  obtain ⟨φ, hφ⟩ : ∃ φ : S →+* Γ(pullback x0 R.hom, ⊤), spMap φ = e.inv ≫ pullback.fst x0 R.hom :=
    ⟨_, Spec.map_preimage _⟩
  have hw : (e.inv ≫ pullback.snd x0 R.hom) ≫ R.hom = (Over.mk (spMap φ ≫ x0)).hom := by
    simp [hφ, pullback.condition]
  refine ⟨Γ(pullback x0 R.hom, ⊤), inferInstance, φ, Over.homMk (e.inv ≫ pullback.snd x0 R.hom) hw, ?_, ?_⟩
  · have hfl : Flat (spMap φ) := by
      rw [hφ]
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp hfl
  · intro T _ ψ u
    let g : Sp T ⟶ pullback x0 R.hom := pullback.lift (spMap ψ) u.left (Over.w u).symm
    obtain ⟨χ, hχ⟩ : ∃ χ : Γ(pullback x0 R.hom, ⊤) →+* T, spMap χ = g ≫ e.hom := ⟨_, Spec.map_preimage _⟩
    refine ⟨χ, ?_, ?_⟩
    · have h1 : spMap (χ.comp φ) = spMap ψ := by
        change Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom χ) = _
        rw [Spec.map_comp]
        change spMap χ ≫ spMap φ = _
        rw [hχ, hφ, Category.assoc, Iso.hom_inv_id_assoc]
        exact pullback.lift_fst _ _ _
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    · rw [hχ]
      change u.left = (g ≫ e.hom) ≫ e.inv ≫ pullback.snd x0 R.hom
      rw [Category.assoc, Iso.hom_inv_id_assoc]
      exact (pullback.lift_snd _ _ _).symm

theorem exists_kernel {X : Scheme.{0}} (A : Over X) [GrpObj A] (k : ℕ) [IsFinite (mulA A k).left]
    [Flat (mulA A k).left] :
    ∃ (Q : Over X) (j : Q ⟶ A), IsAffineHom Q.hom ∧ Flat Q.hom ∧ j ^ k = 1 ∧
      ∀ (T : Over X) (u : T ⟶ A), u ^ k = 1 → ∃ v : T ⟶ Q, v ≫ j = u := by

  have hm : ∀ {T : Over X} (u : T ⟶ A), u ^ k = u ≫ mulA A k := by
    intro T u
    rw [show mulA A k = 𝟙 A ^ k from rfl, MonObj.comp_pow, Category.comp_id]

  let Q : Over X := Over.mk (pullback.snd (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left : _ ⟶ X)
  have hjw : pullback.fst (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left ≫ A.hom = Q.hom := by
    rw [← Over.w (mulA A k), pullback.condition_assoc, Over.w]
    exact Category.comp_id _
  let j : Q ⟶ A := Over.homMk (pullback.fst _ _) hjw
  refine ⟨Q, j, ?_, ?_, ?_, ?_⟩
  · show IsAffineHom (pullback.snd (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left)
    infer_instance
  · show Flat (pullback.snd (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left)
    infer_instance
  · rw [hm j]
    apply Over.OverMorphism.ext
    show (j ≫ mulA A k).left = (toUnit Q ≫ MonObj.one).left
    rw [Over.comp_left, Over.comp_left]
    exact pullback.condition
  · intro T u hu
    have h0 : u ≫ mulA A k = toUnit T ≫ MonObj.one := by
      rw [← hm u, hu]
      rfl
    have h1 : u.left ≫ (mulA A k).left = T.hom ≫ (MonObj.one : 𝟙_ (Over X) ⟶ A).left := by
      have h2 := congrArg (fun f => f.left) h0
      simp only [Over.comp_left] at h2
      exact h2
    refine ⟨Over.homMk (pullback.lift u.left T.hom h1) (pullback.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    exact pullback.lift_fst _ _ _

theorem exists_tuple {X : Scheme.{0}} (A : Over X) [GrpObj A] (k : ℕ) [IsFinite (mulA A k).left]
    [Flat (mulA A k).left] (S : Type) [CommRing S] (x0 : Sp S ⟶ X) (J : Type) [Finite J] :
    ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : J → (Over.mk (spMap φ ≫ x0) ⟶ A)), φ.Flat ∧
      (∀ i, w i ^ k = 1) ∧ ∀ (T : Type) [CommRing T] (ψ : S →+* T) (u : J → (Over.mk (spMap ψ ≫ x0) ⟶ A)),
        (∀ i, u i ^ k = 1) → ∃ χ : B →+* T, χ.comp φ = ψ ∧ ∀ i, (u i).left = spMap χ ≫ (w i).left := by
  obtain ⟨Q, j, hQa, hQf, hj, hQ⟩ := exists_kernel A k
  have := hQa
  have := hQf
  obtain ⟨R, p, hRa, hRf, hR⟩ := exists_power Q J
  have := hRa
  have := hRf
  obtain ⟨B, iB, φ, w, hφ, hw⟩ := exists_point R S x0
  refine ⟨B, iB, φ, fun i => w ≫ p i ≫ j, hφ, fun i => ?_, ?_⟩
  · show (w ≫ p i ≫ j) ^ k = 1
    rw [← Category.assoc, ← MonObj.comp_pow, hj, MonObj.comp_one]
  · intro T _ ψ u hu
    choose v hv using fun i => hQ _ (u i) (hu i)
    obtain ⟨v', hv'⟩ := hR _ v
    obtain ⟨χ, hχ, hχw⟩ := hw T ψ v'
    refine ⟨χ, hχ, fun i => ?_⟩
    rw [← hv i, ← hv' i]
    simp [hχw]

end TorsTuple

theorem exists_flat_universal_torsion_tuple :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X) (k : ℕ), 0 < k → ∀ (J : Type) [Fintype J], ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : J → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.Flat ∧ (∀ i, w i ^ k = 1) ∧ ∀ (T : Type) [CommRing T] (ψ : S →+* T) (u : J → (ptO Xo (spMap ψ ≫ x0) ⟶ Xo.univ.t.G)), (∀ i, u i ^ k = 1) → ∃ χ : B →+* T, χ.comp φ = ψ ∧ ∀ i, (u i).left = spMap χ ≫ (w i).left := by
  intro hL E _ _ _ H Dw l Xo S _ x0 k hk J _

  have hN := hL.mulN
  unfold MulNSt at hN
  obtain ⟨hloc, -⟩ := moduli_univ_polAV E H Dw l Xo
  obtain ⟨hfin, hfl, -⟩ := hN Xo.X (UnivPol.pol Xo) k hk
  have hfin' : IsFinite (mulA Xo.univ.t.G k).left := hfin
  have hfl' : Flat (mulA Xo.univ.t.G k).left := hfl
  exact TorsTuple.exists_tuple Xo.univ.t.G k S x0 J

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem eq_one_iff_isUnit_of_isIdempotentElem {R : Type} [CommRing R] {u : R} (hu : IsIdempotentElem u) :
    u = 1 ↔ IsUnit u := by
  constructor
  · rintro rfl
    exact isUnit_one
  · intro h
    exact h.mul_left_cancel (by rw [hu.eq, _root_.mul_one])

private theorem isUnit_iff_forall_primeSpectrum_notMem {R : Type} [CommRing R] (x : R) :
    IsUnit x ↔ ∀ q : PrimeSpectrum R, x ∉ q.asIdeal := by
  constructor
  · intro h q hq
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hq h)
  · intro h
    by_contra hx
    obtain ⟨I, hI, hxI⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hx)
    exact h ⟨I, hI.isPrime⟩ hxI

theorem exists_isIdempotentElem_range_spMap_subset {B : Type} [CommRing B] {U : Set (Sp B)} (hU : IsClopen U) :
    ∃ e : B, IsIdempotentElem e ∧ ∀ (T : Type) [CommRing T] (χ : B →+* T), χ e = 1 ↔ Set.range (spMap χ) ⊆ U := by
  let s : TopologicalSpace.Clopens (PrimeSpectrum B) := ⟨U, hU⟩
  have he : IsIdempotentElem (PrimeSpectrum.isIdempotentElemEquivClopens.symm s).1 :=
    (PrimeSpectrum.isIdempotentElemEquivClopens.symm s).2

  have hmem : ∀ p : PrimeSpectrum B,
      p ∈ U ↔ (PrimeSpectrum.isIdempotentElemEquivClopens.symm s).1 ∉ p.asIdeal := by
    intro p
    have h := congrArg (fun o : TopologicalSpace.Opens (PrimeSpectrum B) => p ∈ o)
      (PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm s)
    simp only [eq_iff_iff] at h
    rw [PrimeSpectrum.mem_basicOpen] at h
    exact h.symm
  refine ⟨_, he, fun T _ χ => ?_⟩
  rw [eq_one_iff_isUnit_of_isIdempotentElem (he.map χ), isUnit_iff_forall_primeSpectrum_notMem]
  constructor
  · rintro h _ ⟨q, rfl⟩
    exact (hmem _).2 (h q)
  · intro h q
    exact (hmem _).1 (h ⟨q, rfl⟩)

theorem exists_isIdempotentElem_torsion_eq :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (B : Type) [CommRing B] (x0 : Sp B ⟶ Xo.X) (k : ℕ), 0 < k → ∀ (a b : ptO Xo x0 ⟶ Xo.univ.t.G), a ^ k = 1 → b ^ k = 1 → ∃ e : B, IsIdempotentElem e ∧ ∀ (T : Type) [CommRing T] (χ : B →+* T), χ e = 1 ↔ spMap χ ≫ a.left = spMap χ ≫ b.left := by
  intro _ E _ _ _ H Dw l Xo B _ x0 k hk a b ha hb
  obtain ⟨-, -, hunit, hab, -⟩ := moduli_univ_polAV E H Dw l Xo
  obtain ⟨Z, et, hZf, hZe, hadd, hpow, huniv⟩ :=
    exists_finiteEtale_latticeTorsionHom Xo.X Xo.univ.t.G k ℤ hab (hunit k hk)
  have R : LevCover.RepTors Xo.univ.t.G k ℤ Z et := ⟨hZf, hZe, hadd, hpow, huniv⟩

  have hz : ∀ c : ptO Xo x0 ⟶ Xo.univ.t.G, c ^ k = 1 → ∀ m : ℤ, (c ^ m) ^ k = 1 := by
    intro c hc m
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow]
  obtain ⟨U, hUc, hU⟩ := R.clopenCond (T := ptO Xo x0) (fun m => a ^ m) (fun m => b ^ m)
    (fun m c => zpow_add a m c) (hz a ha) (fun m c => zpow_add b m c) (hz b hb)
  let V : Set (Sp B) := (U : Set (ptO Xo x0).left)
  obtain ⟨e, he, hE⟩ := exists_isIdempotentElem_range_spMap_subset (B := B) (U := V) ⟨hUc, U.isOpen⟩
  refine ⟨e, he, fun T _ χ => ?_⟩
  rw [hE T χ]
  let h : Over.mk (spMap χ ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap χ) rfl
  have hh : Set.range (spMap χ) ⊆ V ↔ Set.range h.left ⊆ U := Iff.rfl
  rw [hh, ← hU _ h]
  simp only [GrpObj.comp_zpow]
  constructor
  · intro hm
    have h1 : h ≫ a = h ≫ b := by simpa using hm 1
    simpa [h] using congrArg CommaMorphism.left h1
  · intro hl m
    have h1 : h ≫ a = h ≫ b := Over.OverMorphism.ext (by simpa [h] using hl)
    rw [h1]

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.exists_symmetry_series_of_frames_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → FrTrunc t x0 d x e → FrAxes t x0 d x e → ∃ sy : PS S 2 d, ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧ LB.Gen.Corr t.PP.L _ _ _ _ (e m) (scaleGenG t _ _ (unitΓ u⁻¹) (peG t x0 d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)])) := by
  first | exact @GlobalTheory.exists_symmetry_series_of_frames | exact GlobalTheory.exists_symmetry_series_of_frames | (intros; apply GlobalTheory.exists_symmetry_series_of_frames <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.exists_second_partial_law_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → FrTrunc t x0 d x e → FrAxes t x0 d x e → ∃ ph2 : PS S 3 d, ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift (jptG t x0 d x m (1 : Fin 3)) (lift (jptG t x0 d x m (2 : Fin 3)) (jptG t x0 d x m (0 : Fin 3)))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)]) (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)])) (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))))) := by
  first | exact @GlobalTheory.SecondPartialLaw.exists_second_partial_law | exact GlobalTheory.SecondPartialLaw.exists_second_partial_law | (intros; apply GlobalTheory.SecondPartialLaw.exists_second_partial_law <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

namespace GlobalTheory

theorem page_relation_deg_three : ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CG AG : ℝ), 1041 ≤ CG → 3 ≤ AG → 1 ≤ Zb D large₂ → 1041 * Zb D large₂ ^ 3 ≤ WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size) := by
  intro D large₂ j ka CG AG hC hA hZ
  have h1 : Zb D large₂ ^ 3 ≤ Zb D large₂ ^ AG := by
    have := Real.rpow_le_rpow_of_exponent_le hZ hA
    rwa [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast] at this
  have h2 : 0 ≤ Real.log ka.size := Real.log_nonneg ka.one_le_size
  have h3 : WeightFamilies.PPv D large₂ CG AG = CG * Zb D large₂ ^ AG := rfl
  have h4 : 0 ≤ Zb D large₂ ^ 3 := by positivity
  rw [h3]
  have h5 : 1041 * Zb D large₂ ^ 3 ≤ CG * Zb D large₂ ^ AG :=
    mul_le_mul hC h1 h4 (by linarith)
  have h6 : 0 ≤ CG * Zb D large₂ ^ AG := le_trans (by positivity) h5
  nlinarith [mul_nonneg h6 h2]

end GlobalTheory
end
