module

import Development.EtaleCohomology.EtaleSheaves.Bundle077
public import Development.EtaleCohomology.EtaleSheaves.Bundle003
public import Development.EtaleCohomology.EtaleSheaves.Bundle068
public import Development.EtaleCohomology.EtaleSheaves.Bundle004
public import Development.EtaleCohomology.EtaleSheaves.Bundle074
public import Development.EtaleCohomology.EtaleSheaves.Bundle055
public import Development.EtaleCohomology.EtaleSheaves.CokernelKilling.AssembleOf
import Development.EtaleCohomology.EtaleSheaves.CokernelKilling.FiniteSubcover
public import Development.EtaleCohomology.EtaleSheaves.CokernelKilling.KillCokOf
public import Development.EtaleCohomology.EtaleSheaves.Bundle056
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle042
public import Development.EtaleCohomology.EtaleSheaves.Bundle066
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
public import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

theorem etaleFreeSheafOfRepresentable_isZero_of_isEmpty_scheme (R : Type) [CommRing R] (E : Scheme.{0}) [IsEmpty E] :
    IsZero ((free R).obj (yoneda.obj E)) := by
  apply LateralTheory.E.LeafVanVPf.free_empty <;> assumption

theorem leafEmptyVanish : LeafEmptyVanish := by
  intro R _ X F n
  have hE : IsEmpty (((⊥ : X.Opens) : Scheme.{0}) : Type) := by
    change IsEmpty ((⊥ : X.Opens) : Set X); simp
  have hfree := etaleFreeSheafOfRepresentable_isZero_of_isEmpty_scheme R ((⊥ : X.Opens) : Scheme.{0})
  have hN : IsZero ((chainsN R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) := by
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.hom_ext
    intro j
    refine IsZero.eq_of_src ?_ _ _
    exact hfree
  have hC : IsZero ((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) :=
    Functor.map_isZero (ComplexShape.embeddingDownNat.extendFunctor (Shv R)) hN
  have hX : ∀ p, IsZero (((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))).X p) := fun p =>
    Functor.map_isZero (HomologicalComplex.eval _ _ p) hC
  have : Subsingleton (Cochain ((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) (res R F) n) :=
    ⟨fun a b => Cochain.ext _ _ fun p q hpq => (hX p).eq_of_src _ _⟩
  have : Subsingleton (Cocycle ((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) (res R F) n) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  change Subsingleton (CohomologyClass _ _ n)
  unfold CohomologyClass
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective b
  rw [Subsingleton.elim a b]

end LateralTheory.E.E8

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafInj0VPf
open CochainComplex CochainComplex.HomComplex
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf

def LeafSecTr : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (ι : W ⟶ B) (P : Y ⟶ B) (U : B.Etale)
  (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0), ∃ s : Sec (tw q i) U.left,
  (∀ (U' : B.Etale) (a : U' ⟶ U), Sec.res a.left s = 0 → rB q i ι a 0 c = 0) ∧
  (∀ (U' : B.Etale) (a : U' ⟶ U), rY q i P ι a 0 (bY q i P ι U 0 c) = 0 → Sec.res (toBY P U' ≫ a.left) s = 0)

def LeafSecV : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale) (s : Sec (tw q i) U.left),
  Cov U (fun U' a => Sec.res (toBY (g2 ≫ g1 ≫ p) U' ≫ a.left) s = 0) →
  ∀ x : U.left, U.hom x ∉ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Sec.res a.left s = 0

theorem res_comp {q : ℕ} {i : ℤ} {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (s : Sec (tw q i) Z) :
    Sec.res (f ≫ g) s = Sec.res f (Sec.res g s) := by
  simp [Sec.res, op_comp, Functor.map_comp]

theorem relative_cohomology_forget_injective_degree_zero_of_subsingleton (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E)
    (hU : Subsingleton (H R U F (-1))) (y : Hrel R f F 0) (hy : fgt R f F 0 y = 0) : y = 0 := by
  apply LateralTheory.E.LeafInj0WPf.fgtInj0 <;> assumption

theorem secTr (hH : Hyps) (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (ι : W ⟶ B) (P : Y ⟶ B) (U : B.Etale)
    (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0) : ∃ s : Sec (tw q i) U.left,
    (∀ (U' : B.Etale) (a : U' ⟶ U), Sec.res a.left s = 0 → rB q i ι a 0 c = 0) ∧
    (∀ (U' : B.Etale) (a : U' ⟶ U), rY q i P ι a 0 (bY q i P ι U 0 c) = 0 → Sec.res (toBY P U' ≫ a.left) s = 0) := by
  have hA9 : A9 := hH.2.2.2.2.2.2.2.1
  obtain ⟨hneg, e, hnat, -⟩ := hA9 (ZMod q) (tw q i)
  refine ⟨(e U.left).symm (fgt _ _ _ 0 c), ?_, ?_⟩
  · intro U' a ha
    apply relative_cohomology_forget_injective_degree_zero_of_subsingleton _ _ _ (hneg _ (-1) (by norm_num))
    rw [relNat]
    have := hnat a.left ((e U.left).symm (fgt _ _ _ 0 c))
    rw [AddEquiv.apply_symm_apply] at this
    rw [this, ha, map_zero]
  · intro U' a ha
    have h0 := congrArg (fgt _ _ _ 0) ha
    rw [map_zero, relNat, relNat, ← pull_comp, ← Functor.map_comp] at h0
    have hsq : resY P a ≫ toBY P U = toBY P U' ≫ a.left := by simp only [resY, toBY]; exact pullback.lift_snd _ _ _
    rw [hsq] at h0
    have := hnat (toBY P U' ≫ a.left) ((e U.left).symm (fgt _ _ _ 0 c))
    rw [AddEquiv.apply_symm_apply, h0] at this
    exact (e _).injective (by rw [← this, map_zero])

def LeafSHPt : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ) {B : Scheme.{0}}
  (U : B.Etale) (_ : U.left ⟶ Sp k) (x : U.left), ∃ (A : Type) (_ : CommRing A) (t : Sp A ⟶ U.left), SH A ∧
  (∀ O : U.left.Opens, x ∈ O → Set.range t ⊆ O) ∧
  (∀ S ∈ (EtTop B) U, ∃ (U' : B.Etale) (a : U' ⟶ U), S a ∧ ∃ t' : Sp A ⟶ U'.left, t' ≫ a.left = t) ∧
  ∀ s : Sec (tw q i) U.left, Sec.res t s = 0 → ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Sec.res a.left s = 0

theorem LeafSecV_of (hP : LeafSHPt) : LeafSecV := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s0 ι _ V hV' p g1 g2 hp1 hp2 hp3 hSH U s hc x hx
  have hA9 : A9 := hH.2.2.2.2.2.2.2.1
  obtain ⟨-, e, hnat, -⟩ := hA9 (ZMod q) (tw q i)
  obtain ⟨A, _, t, hA, hO, hL, hG⟩ := hP hH q k hq i U (U.hom ≫ s0) x
  apply hG
  set P := g2 ≫ g1 ≫ p
  have hxV : x ∈ (U.hom ⁻¹ᵁ V) := by
    change U.hom x ∈ (V : Set B); rw [hV']; exact hx
  have hr : Set.range (t ≫ U.hom) ⊆ (V : Set B) := by
    rintro _ ⟨z, rfl⟩
    exact hO _ hxV ⟨z, rfl⟩
  have hinj := ((hSH A (t ≫ U.hom) hA hr).2.2.2).1
  obtain ⟨S, hS, hPS⟩ := hc
  obtain ⟨U', a, hSa, t', ht'⟩ := hL S hS
  have h0 := hPS U' a hSa
  have hm : pullback.snd P (t ≫ U.hom) ≫ t =
      pullback.map P (t ≫ U.hom) P U'.hom (𝟙 _) t' (𝟙 B) (by simp) (by
        rw [Category.comp_id, ← ht', Category.assoc]; congr 1; simpa using a.w) ≫ (toBY P U' ≫ a.left) := by
    simp only [toBY]
    rw [pullback.lift_snd_assoc, Category.assoc, ht']
  apply (e _).injective
  apply hinj
  rw [map_zero, map_zero]
  change pull _ (sch.map (pullback.snd P (t ≫ U.hom))) _ 0 (e _ (Sec.res t s)) = 0
  rw [hnat, ← res_comp, hm, res_comp, h0]
  simp

theorem LeafInj0V_of_sec (hT : LeafSecTr) (hS : LeafSecV) : LeafInj0V := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s0 ι _ V hV' p g1 g2 hp1 hp2 hp3 hSH U c hc x hx
  obtain ⟨s, h1, h2⟩ := hT hH q i ι (g2 ≫ g1 ≫ p) U c
  obtain ⟨U', a, y, hy, hs⟩ := hS hH q k hq i s0 ι V hV' p g1 g2 hp1 hp2 hp3 hSH U s
    (hc.mono fun U'' b hb => h2 U'' b hb) x hx
  refine ⟨U', a, y, hy, Cov.all fun U'' b => h1 U'' (b ≫ a) ?_⟩
  change Sec.res (b.left ≫ a.left) s = 0
  rw [res_comp, hs]
  simp
theorem LeafInj0V_of (hP : LeafSHPt) : LeafInj0V :=
  LeafInj0V_of_sec (fun hH q _ i _ _ _ ι P U c => secTr hH q i ι P U c) (LeafSecV_of hP)
end LateralTheory.E.LeafInj0VPf
end
end

section

namespace LateralTheory.E.RingCommutativity

theorem goal_of : LateralTheory.E.CupProductRingLaws.LeafRingComm := LateralTheory.Fix.CupProductTensor.ringComm'

end LateralTheory.E.RingCommutativity
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf
open LateralTheory.E.LeafGhostCut LateralTheory.E.KillCokPf.Asm

namespace LateralTheory.E.KernelLocalization

theorem bij_of_iso (R : Type) [CommRing R] (F : Shv R) {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (n : ℤ) :
    Function.Bijective (pull R (sch.map f) F n) := by
  have h1 : ∀ x, pull R (sch.map (inv f)) F n (pull R (sch.map f) F n x) = x := fun x => by
    rw [← pull_comp, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  have h2 : ∀ x, pull R (sch.map f) F n (pull R (sch.map (inv f)) F n x) = x := fun x => by
    rw [← pull_comp, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem cover_bij (hC : Coprod) (R : Type) [CommRing R] (F : Shv R) {ι : Type} {X : ι → Scheme.{0}} {S : Scheme.{0}}
    (π : ∀ j, X j ⟶ S) [IsIso (Sigma.desc π)] (n : ℤ) :
    Function.Bijective fun (x : H R (sch.obj S) F n) (j : ι) => pull R (sch.map (π j)) F n x := by
  have := (hC R F X n).comp (bij_of_iso R F (Sigma.desc π) n)
  convert this using 1
  funext x j
  simp only [Function.comp]
  rw [← pull_comp, ← Functor.map_comp, Sigma.ι_desc]

abbrev pr {ι : Type} (E : ι → CommRingCat.{0}) (j : ι) : CommRingCat.of (∀ k, E k) ⟶ E j :=
  CommRingCat.ofHom (Pi.evalRingHom (fun k => E k) j)

theorem pi_bij (hC : Coprod) (q : ℕ) (i n : ℤ) {ι : Type} [Finite ι] (E : ι → CommRingCat.{0}) :
    Function.Bijective fun x (j : ι) => PP q i n (pr E j) x := by
  have : IsIso (Sigma.desc fun j => Spec.map (pr E j)) := inferInstanceAs (IsIso (sigmaSpec E))
  exact cover_bij hC _ _ _ n

theorem push_inj (hC : Coprod) (q : ℕ) (i n : ℤ) {ι : Type} [Finite ι] (E : ι → CommRingCat.{0}) {Z : CommRingCat.{0}}
    (ψ : CommRingCat.of (∀ k, E k) ⟶ Z) (y : H (ZMod q) (sch.obj (Spec Z)) (tw q i) n)
    (hy : ∀ j, PP q i n (pushout.inl ψ (pr E j)) y = 0) : y = 0 := by
  have h0 : IsIso (Sigma.desc fun j => Spec.map (pr E j)) := inferInstanceAs (IsIso (sigmaSpec E))
  have := FinitaryPreExtensive.isIso_sigmaDesc_fst (fun j => Spec.map (pr E j)) (Spec.map ψ) h0
  apply (cover_bij hC (ZMod q) (tw q i) (fun j => pullback.fst (Spec.map ψ) (Spec.map (pr E j))) n).1
  funext j
  have hp := isPullback_SpecMap_of_isPushout _ _ _ _ (IsPushout.of_hasPushout ψ (pr E j))
  simp only [map_zero]
  rw [← hp.isoPullback_inv_fst, Functor.map_comp, pull_comp]
  change pull _ _ _ _ (PP q i n _ y) = 0
  rw [hy, map_zero]

theorem rel_pi (hC : Coprod) (q : ℕ) (i n : ℤ) {D Y : CommRingCat.{0}} (φ : D ⟶ Y) {ι : Type} [Finite ι]
    (E : ι → CommRingCat.{0}) (e : ∀ j, D ⟶ E j) (z : HR q i n φ)
    (hz : ∀ j, ∃ (Z : CommRingCat.{0}) (u : Y ⟶ Z) (ψ : E j ⟶ Z) (h : IsPushout φ (e j) u ψ), RP q i n φ (e j) u ψ h.w z = 0)
    {Z : CommRingCat.{0}} (u : Y ⟶ Z) (ψ : CommRingCat.of (∀ k, E k) ⟶ Z) (h : IsPushout φ (piMap E e) u ψ) :
    RP q i n φ (piMap E e) u ψ h.w z = 0 := by
  have hpr : ∀ j, piMap E e ≫ pr E j = e j := fun j => by ext a; rfl
  have hw : ∀ j, φ ≫ u ≫ pushout.inl ψ (pr E j) = e j ≫ pushout.inr ψ (pr E j) := fun j => by
    rw [h.w_assoc, pushout.condition, ← Category.assoc, hpr]
  have hj : ∀ j, RP q i n ψ (pr E j) (pushout.inl ψ (pr E j)) (pushout.inr ψ (pr E j)) pushout.condition
      (RP q i n φ (piMap E e) u ψ h.w z) = 0 := fun j => by
    obtain ⟨Z', u', ψ', h', h0⟩ := hz j
    rw [← RP_comp q i n φ _ u ψ h.w _ _ _ _ (e j) _ (hw j) (hpr j) rfl,
      RP_comp q i n φ (e j) u' ψ' h'.w (𝟙 _) (h'.desc _ _ (hw j)) _ (by simp) (e j) _ (hw j) (by simp) (by simp),
      h0, map_zero]
  set z' := RP q i n φ (piMap E e) u ψ h.w z
  have hm : 1 + (n - 1) = n := by omega
  have hf : fgt _ _ _ n z' = 0 := by
    apply (pi_bij hC q i n E).1
    funext j
    simp only [map_zero]
    rw [← fgt_RP q i n ψ (pr E j) _ _ pushout.condition, hj, map_zero]
  obtain ⟨y, hy⟩ := exists_bd _ _ _ (n - 1) n hm z' hf
  have hb : ∀ j, ∃ w, PP q i (n - 1) (pushout.inr ψ (pr E j)) w = PP q i (n - 1) (pushout.inl ψ (pr E j)) y := fun j => by
    refine range_of_bd _ _ _ (n - 1) n hm _ ?_
    rw [← RP_bd q i (n - 1) n hm ψ (pr E j) _ _ pushout.condition, hy, hj]
  choose w hw' using hb
  obtain ⟨a, ha⟩ := (pi_bij hC q i (n - 1) E).2 w
  have hya : y - PP q i (n - 1) ψ a = 0 := push_inj hC q i (n - 1) E ψ _ fun j => by
    rw [map_sub, ← PP_comp, pushout.condition, PP_comp, ← hw' j, ← congrFun ha j, sub_self]
  rw [← hy, sub_eq_zero.1 hya]
  exact bd_pull ..

theorem relKill (hB1 : B1) (hC : Coprod) (q : ℕ) (i n : ℤ) {A Y D Y' : CommRingCat.{0}} (φ : A ⟶ Y) (hq : IsUnit (q : A))
    (d : A ⟶ D) (hpts : LocPts q i φ d) (w : Y ⟶ Y') (φ' : D ⟶ Y') (hpo : IsPushout φ d w φ') (z : HR q i n φ')
    (hz : PP q i n φ' (fgt _ _ _ n z) = 0) :
    ∃ (E : CommRingCat.{0}) (e : D ⟶ E) (Z : CommRingCat.{0}) (u : Y' ⟶ Z) (ψ : E ⟶ Z) (h : IsPushout φ' e u ψ),
      Et e ∧ SpS e ∧ RP q i n φ' e u ψ h.w z = 0 := by
  have h' : ∀ x : PrimeSpectrum D, ∃ (E : CommRingCat.{0}) (e : D ⟶ E), Et e ∧
      x ∈ Set.range (PrimeSpectrum.comap e.hom) ∧
      ∃ (Z : CommRingCat.{0}) (u : Y' ⟶ Z) (ψ : E ⟶ Z) (h : IsPushout φ' e u ψ), RP q i n φ' e u ψ h.w z = 0 := by
    intro x
    obtain ⟨O, o, Q, hIE, hQ, hQr, hBC⟩ := hpts x.asIdeal x.isPrime
    obtain ⟨E, e, s, Z, u, ψ, h, he, hes, h0⟩ := relAt hB1 q i n φ' (unit_of d hq) o hIE
      (fun Z u ψ h => hBC Z (w ≫ u) ψ (hpo.paste_vert h)) z hz
    refine ⟨E, e, he, ⟨⟨Q.comap s.hom, inferInstance⟩, PrimeSpectrum.ext ?_⟩, Z, u, ψ, h, h0⟩
    change (Q.comap s.hom).comap e.hom = _
    rw [Ideal.comap_comap, ← CommRingCat.hom_comp, hes, hQr]
  choose E e he hx hY using h'
  obtain ⟨s, hs⟩ := LateralTheory.E.KillCokPf.Lem.finite_subcover E e he hx
  refine ⟨_, piMap (fun k : s => E k.1) (fun k => e k.1), _, _, _, IsPushout.of_hasPushout _ _,
    LateralTheory.E.KillCokPf.Glue.et_pi _ _ (fun k => he k.1), sps_pi _ _ fun x => ?_,
    rel_pi hC q i n φ' _ _ z (fun k => hY k.1) _ _ (IsPushout.of_hasPushout _ _)⟩
  obtain ⟨r, hr, hxr⟩ := hs x
  exact ⟨⟨r, hr⟩, hxr⟩

end LateralTheory.E.KernelLocalization
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.QuotientFieldNonconstantLift

def LeafCurveSmall : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  (Set.univ : Set C).Infinite ∧ ∀ Z : Set C, IsClosed Z → Z.Infinite → Z = Set.univ

def LeafLiftNonconst : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
  [IsProper p] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], (∀ R : Subalgebra k Ω, R.FG → ringKrullDim R <
    topologicalKrullDim X) → ∀ {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    ∀ (he : e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))), genericPoint X ∈ Set.range e →
    ∀ y : C0, ∃ a : C0, pullback.lift c0 e he.symm a ≠ pullback.lift c0 e he.symm y

theorem lqf_of_nonconst (hC : LeafCurveSmall) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {C Y : Scheme.{0}}
    (c : C ⟶ Sp Ω) (hc : IsCurve c) (g : C ⟶ Y) [LocallyOfFiniteType g] [UniversallyClosed g]
    (hn : ∀ y, ∃ a, g a ≠ g y) : LocallyQuasiFinite g := by
  obtain ⟨_, _, _⟩ := id hc
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace c
  refine GlobalTheory.locallyQuasiFinite_of_finite_fibres_closedPoints g fun y hy => ?_
  have hcl : IsClosed ({g y} : Set Y) := by
    have := g.isClosedMap _ hy
    simpa using this
  by_contra hinf
  have := (hC Ω c hc).2 _ (hcl.preimage g.continuous) hinf
  obtain ⟨a, ha⟩ := hn y
  have : a ∈ g ⁻¹' {g y} := this ▸ Set.mem_univ a
  exact ha this

theorem nonconst_of_surj (hC : LeafCurveSmall) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {C0 C1 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω) (hc : IsCurve c0) (g : C1 ⟶ C0) (hg : Surjective g) (y : C1) : ∃ a, g a ≠ g y := by
  obtain ⟨b, hb⟩ := ((hC Ω c0 hc).1.sdiff (Set.finite_singleton (g y))).nonempty
  obtain ⟨a, rfl⟩ := hg.surj b
  exact ⟨a, by simpa using hb.2⟩

theorem lqf_gamma (hC : LeafCurveSmall) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {C0 C1 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω) (hc : IsCurve c0) (g : C1 ⟶ C0) (hc1 : IsCurve (g ≫ c0)) (hg : Surjective g) :
    LocallyQuasiFinite g := by
  obtain ⟨_, _, _⟩ := id hc
  obtain ⟨_, _, _⟩ := id hc1
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g c0
  have : UniversallyClosed g := UniversallyClosed.of_comp_of_isSeparated g c0
  exact lqf_of_nonconst hC (g ≫ c0) hc1 g (nonconst_of_surj hC c0 hc g hg)

theorem LeafQFOmega_of (hC : LeafCurveSmall) (hL : LeafLiftNonconst) :
    LateralTheory.E.QuasiFiniteDescent.LeafQFOmega := by
  intro k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he hgen C1 C2 γ1 γ2 h1 h2 s1 s2
  refine ⟨?_, lqf_gamma hC c0 hc0 γ1 h1 s1, lqf_gamma hC (γ1 ≫ c0) h1 γ2 h2 s2⟩
  obtain ⟨_, _, _⟩ := id hc0
  set g := pullback.lift c0 e he.symm with hgdef
  have hfst : g ≫ pullback.fst _ _ = c0 := pullback.lift_fst _ _ _
  have : LocallyOfFiniteType (g ≫ pullback.fst _ _) := by rw [hfst]; infer_instance
  have : UniversallyClosed (g ≫ pullback.fst _ _) := by rw [hfst]; infer_instance
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (pullback.fst _ _)
  have : UniversallyClosed g := UniversallyClosed.of_comp_of_isSeparated g (pullback.fst _ _)
  exact lqf_of_nonconst hC c0 hc0 g (hL k p Ω hdim c0 e hc0 he hgen)

end LateralTheory.E.QuotientFieldNonconstantLift
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafPairFPPf

namespace LateralTheory.E.LeafMapFPPf

section
variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

theorem incl_comp {R S T : Subalgebra k Ω} (h1 : R ≤ S) (h2 : S ≤ T) :
    incl h2 ≫ incl h1 = incl (h1.trans h2) := by
  simp only [incl, ← Spec.map_comp]
  congr 1

theorem incl_refl (R : Subalgebra k Ω) : incl (le_refl R) = 𝟙 _ := by
  simp only [incl]
  rw [← Spec.map_id]
  congr 1

theorem sq {R S : Subalgebra k Ω} (h : R ≤ S) {C D : Scheme.{0}} {c : C ⟶ Sp Ω} {q : D ⟶ Sp R} {v : C ⟶ D}
    (hs : IsPullback v c q (toR R)) :
    IsPullback (pullback.lift v (c ≫ toR S) (by rw [Category.assoc, toR_incl, hs.w])) c
      (pullback.snd q (incl h)) (toR S) :=
  IsPullback.of_right (h₁₂ := pullback.fst q (incl h)) (h₂₂ := incl h)
    (by rw [pullback.lift_fst, toR_incl]; exact hs) (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)

def dgMap {R : Subalgebra k Ω} {D1 : Scheme.{0}} (q1 : D1 ⟶ Sp R) {S T : Subalgebra k Ω} (hS : R ≤ S)
    (hT : R ≤ T) (h : S ≤ T) : pullback q1 (incl hT) ⟶ pullback q1 (incl hS) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ incl h) (by
    rw [pullback.condition, Category.assoc, incl_comp])

@[reassoc (attr := simp)]
theorem dgMap_fst {R : Subalgebra k Ω} {D1 : Scheme.{0}} (q1 : D1 ⟶ Sp R) {S T : Subalgebra k Ω} (hS : R ≤ S)
    (hT : R ≤ T) (h : S ≤ T) : dgMap q1 hS hT h ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem dgMap_snd {R : Subalgebra k Ω} {D1 : Scheme.{0}} (q1 : D1 ⟶ Sp R) {S T : Subalgebra k Ω} (hS : R ≤ S)
    (hT : R ≤ T) (h : S ≤ T) : dgMap q1 hS hT h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ incl h :=
  pullback.lift_snd _ _ _

def dg {R : Subalgebra k Ω} {D1 : Scheme.{0}} (q1 : D1 ⟶ Sp R) : (GlobalTheory.FGAbove R)ᵒᵖ ⥤ Scheme.{0} where
  obj S := pullback q1 (incl S.unop.2.2)
  map {S T} f := dgMap q1 _ _ (show T.unop.1 ≤ S.unop.1 from leOfHom f.unop)
  map_id S := by apply pullback.hom_ext <;> simp [incl_refl]
  map_comp f g := by apply pullback.hom_ext <;> simp [incl_comp]

def dgT {R : Subalgebra k Ω} {D1 : Scheme.{0}} (q1 : D1 ⟶ Sp R) : dg q1 ⟶ (Functor.const _).obj (Sp R) where
  app S := pullback.fst _ _ ≫ q1
  naturality S T f := by simp [dg]

theorem dgπ_map {R : Subalgebra k Ω} {C1 D1 : Scheme.{0}} (c1 : C1 ⟶ Sp Ω) (q1 : D1 ⟶ Sp R) (v1 : C1 ⟶ D1)
    (hs : IsPullback v1 c1 q1 (toR R)) {S T : Subalgebra k Ω} (hS : R ≤ S) (hT : R ≤ T) (h : S ≤ T) :
    pullback.lift v1 (c1 ≫ toR T) (by rw [Category.assoc, toR_incl, hs.w]) ≫ dgMap q1 hS hT h =
      (pullback.lift v1 (c1 ≫ toR S) (by rw [Category.assoc, toR_incl, hs.w]) : C1 ⟶ pullback q1 (incl hS)) := by
  apply pullback.hom_ext
  · erw [Category.assoc, dgMap_fst, pullback.lift_fst, pullback.lift_fst]
  · erw [Category.assoc, dgMap_snd, pullback.lift_snd_assoc, pullback.lift_snd, Category.assoc, toR_incl]

def dgCone {R : Subalgebra k Ω} {C1 D1 : Scheme.{0}} (c1 : C1 ⟶ Sp Ω) (q1 : D1 ⟶ Sp R) (v1 : C1 ⟶ D1)
    (hs : IsPullback v1 c1 q1 (toR R)) : Cone (dg q1) where
  pt := C1
  π := { app S := pullback.lift v1 (c1 ≫ toR S.unop.1) (by rw [Category.assoc, toR_incl, hs.w])
         naturality S T f := by
           exact (Category.id_comp _).trans (dgπ_map c1 q1 v1 hs _ _ _).symm }

end

def LeafLimFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C1 D1 : Scheme.{0}} (c1 : C1 ⟶ Sp Ω) (q1 : D1 ⟶ Sp R) (v1 : C1 ⟶ D1) (hs : IsPullback v1 c1 q1 (toR R)),
    FP q1 → Nonempty (IsLimit (dgCone c1 q1 v1 hs))

def LeafStagesFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
    {D1 : Scheme.{0}} (q1 : D1 ⟶ Sp R), FP q1 →
    (∀ S : (GlobalTheory.FGAbove R)ᵒᵖ, CompactSpace ((dg q1).obj S) ∧ QuasiSeparatedSpace ((dg q1).obj S)) ∧
    ∀ (S T : GlobalTheory.FGAbove R) (h : S.1 ≤ T.1), IsAffineHom (dgMap q1 S.2.2 T.2.2 h)

theorem morphismDescent_of_isLimit (hL : LeafLimFP) (hI : LeafStagesFP) : LeafMapFP := by
  intro k _ Ω _ _ R hR C0 C1 c0 γ1 D0 D1 q q1 v0 v1 hq hq1 hs0 hs1
  haveI := GlobalTheory.FGAbove.isFiltered hR
  obtain ⟨hc⟩ := hL k Ω R hR (γ1 ≫ c0) q1 v1 hs1 hq1
  obtain ⟨hcs, haf⟩ := hI k Ω R q1 hq1
  haveI := hq.1
  haveI : ∀ S : (GlobalTheory.FGAbove R)ᵒᵖ, CompactSpace ((dg q1).obj S) := fun S => (hcs S).1
  haveI : ∀ S : (GlobalTheory.FGAbove R)ᵒᵖ, QuasiSeparatedSpace ((dg q1).obj S) := fun S => (hcs S).2
  haveI : ∀ {S T : (GlobalTheory.FGAbove R)ᵒᵖ} (f : S ⟶ T), IsAffineHom ((dg q1).map f) := fun f => haf _ _ _
  obtain ⟨S, g, hg1, hg2⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (D := dg q1)
    (t := dgT q1) (f := q) (c := dgCone (γ1 ≫ c0) q1 v1 hs1) hc (γ1 ≫ v0) (by
      ext S
      dsimp [dgCone, dgT, dg]
      rw [← Category.assoc, pullback.lift_fst, hs1.w]
      simp only [Category.assoc, hs0.w])
  let P := pullback q1 (incl S.unop.2.2)
  let g' : P ⟶ D0 := g
  let w1 : C1 ⟶ P := pullback.lift v1 ((γ1 ≫ c0) ≫ toR S.unop.1) (by rw [Category.assoc, toR_incl, hs1.w])
  have hg1' : w1 ≫ g' = γ1 ≫ v0 := hg1
  have hg2' : g' ≫ q = pullback.snd q1 (incl S.unop.2.2) ≫ incl S.unop.2.2 := by
    rw [show g' ≫ q = pullback.fst q1 (incl S.unop.2.2) ≫ q1 from hg2]; exact pullback.condition
  refine ⟨S.unop.1, S.unop.2.1, pullback q (incl S.unop.2.2), P, pullback.snd _ _,
    pullback.lift g' (pullback.snd _ _) hg2', pullback.lift v0 (c0 ≫ toR S.unop.1)
      (by rw [Category.assoc, toR_incl, hs0.w]), w1, fp_snd _ _ hq, ?_, sq S.unop.2.2 hs0, ?_, ?_⟩
  · rw [pullback.lift_snd]; exact fp_snd _ _ hq1
  · rw [pullback.lift_snd]; exact sq S.unop.2.2 hs1
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]; exact hg1'.symm
    · simp only [Category.assoc, pullback.lift_snd, w1]

end LateralTheory.E.LeafMapFPPf

end
end
