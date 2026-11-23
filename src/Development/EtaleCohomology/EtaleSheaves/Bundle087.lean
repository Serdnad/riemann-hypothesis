module

public import Development.EtaleCohomology.EtaleSheaves.Bundle079
public import Development.EtaleCohomology.EtaleSheaves.Bundle045
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Development.EtaleCohomology.EtaleSheaves.CokernelKilling.KillCokOf
public import Development.EtaleCohomology.EtaleSheaves.LeafSpreadSmoothPf
public import Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling.LeafKill2Of
public import Development.EtaleCohomology.EtaleSheaves.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.Tactic.TypeStar
import Development.EtaleCohomology.EtaleSheaves.Bundle046
import Development.EtaleCohomology.EtaleSheaves.PropertyDescent.BaseChange

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocGenPf
open LateralTheory.E.LeafTw0LocGenPfA LateralTheory.E.LeafTw0LocGenPfB

theorem loc_top {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => h V g⟩

theorem loc_finset {ι : Type*} [DecidableEq ι] {U : Scheme.{0}} (s : Finset ι)
    {P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : ∀ i ∈ s, Loc U (P i)) : Loc U fun V g => ∀ i ∈ s, P i V g := by
  induction s using Finset.induction_on with
  | empty => exact loc_top fun _ _ i hi => by simp at hi
  | insert j s hj ih =>
    obtain ⟨S0, h0, hP0⟩ := h j (Finset.mem_insert_self j s)
    obtain ⟨S1, h1, hP1⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨S0 ⊓ S1, Scheme.etaleTopology.intersection_covering h0 h1, fun V g hg i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hP0 V g hg.1
    · exact hP1 V g hg.2 i hi

theorem res_sec {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {W V : Scheme.{0}}
    (g : W ⟶ V) (x : M.obj Γ(V, ⊤)) :
    Sec.res g (ofRings.sec M V x) = ofRings.sec M W ((M.map g.appTop).hom x) := by
  have := congrArg (fun f => f.hom x) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op)
  exact this.symm

theorem relq {q : ℕ} {A : CommRingCat.{0}} (ζ ξ : Prim q A) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    (Submodule.Quotient.mk (Finsupp.single ξ 1) : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 A) =
      Submodule.Quotient.mk (Finsupp.single ζ 1) := by
  rw [Submodule.Quotient.eq]
  refine Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩
  simp
  rfl

theorem mk_mapDomain {q : ℕ} {A B : CommRingCat.{0}} (f : A ⟶ B) (r : Prim q A →₀ ULift.{1} (ZMod q))
    (ζ0 : Prim q A)
    (hrel : ∀ ξ ∈ r.support, (Submodule.Quotient.mk (Finsupp.single (Prim.map f.hom ξ) 1) :
      (Prim q B →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 B) = Submodule.Quotient.mk (Finsupp.single (Prim.map f.hom ζ0) 1)) :
    (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) r) : (Prim q B →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 B) =
      (r.sum fun _ c => c) • Submodule.Quotient.mk (Finsupp.single (Prim.map f.hom ζ0) 1) := by
  classical

  rw [← Submodule.mkQ_apply, Finsupp.mapDomain, Finsupp.sum, map_sum, Finsupp.sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun ξ hξ => ?_
  rw [← hrel ξ hξ, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Finsupp.smul_single_one]

theorem LeafTw0LocGen_of : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocGen := by
  classical
  intro q _ U n a
  have hA : ∀ k, Loc U fun V g => ∃ t : (twF q 0).obj Γ(V, ⊤), ofRings.sec (twF q 0) V t = Sec.res g (a k) := by
    intro k
    exact ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)) (U := op U) (a k), fun V g hg => hg⟩
  have hA' := loc_finset (U := U) Finset.univ (fun k _ => hA k)
  refine LateralTheory.E.LeafTensMonoPf.loc_trans hA' fun V g hg => ?_
  choose t ht using fun k => hg k (Finset.mem_univ k)
  let r : Fin n → (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) := fun k =>
    (Submodule.Quotient.mk_surjective _ (t k : (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 Γ(V, ⊤))).choose
  have hr : ∀ k, (Submodule.Quotient.mk (r k) : (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 Γ(V, ⊤)) = t k :=
    fun k => (Submodule.Quotient.mk_surjective _ (t k : (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 Γ(V, ⊤))).choose_spec
  rcases isEmpty_or_nonempty (Prim q Γ(V, ⊤)) with hE | ⟨⟨ζ0⟩⟩
  · refine loc_top fun W h => ⟨0, fun _ => 0, fun k => ?_, Or.inl rfl⟩
    rw [zero_smul, LateralTheory.E.LeafTensMonoPf.res_comp, ← ht k, ← hr k, Subsingleton.elim (r k) 0,
      Submodule.Quotient.mk_zero]
    unfold ofRings.sec
    have h0 := map_zero (((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).app (op V)).hom)
    first
      | exact (congrArg (Sec.res h) h0).trans (map_zero _)
      | (erw [h0]; exact map_zero _)
  · obtain ⟨S, hS, hP⟩ := loc_finset (U := V) (Finset.univ.biUnion fun k => (r k).support) (fun ξ _ => geo V ζ0 ξ)
    refine ⟨S, hS, fun W h hh => ?_⟩
    have hrel := hP W h hh
    refine ⟨twGen 0 (Prim.map h.appTop.hom ζ0), fun k => (r k).sum fun _ c => c, fun k => ?_, Or.inr ⟨_, rfl⟩⟩
    rw [LateralTheory.E.LeafTensMonoPf.res_comp, ← ht k, ← hr k]
    refine (res_sec (twF q 0) h _).trans ?_
    have e1 : ((twF q 0).map h.appTop).hom (Submodule.Quotient.mk (r k)) =
        Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map h.appTop.hom) (r k)) := rfl
    rw [e1, mk_mapDomain h.appTop (r k) ζ0 (fun ξ hξ => ?_)]
    · exact map_smul _ _ _
    · obtain ⟨b, hb⟩ := hrel ξ (Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, hξ⟩)
      exact relq _ _ b hb

end LateralTheory.E.LeafTw0LocGenPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.KillCokPf.Asm
open scoped TensorProduct

namespace LateralTheory.E.PushGluePf

abbrev pS (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) :
    H R (sch.obj (Spec A)) F n →+ H R (sch.obj (Spec B)) F n :=
  pull R (sch.map (Spec.map f)) F n

theorem pS_comp (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C)
    (x : H R (sch.obj (Spec A)) F n) : pS R F n (f ≫ g) x = pS R F n g (pS R F n f x) := by
  simp only [pS]; rw [Spec.map_comp, Functor.map_comp, pull_comp]

abbrev ev {ι : Type} (Y : ι → CommRingCat.{0}) (j : ι) : CommRingCat.of (∀ k, Y k) ⟶ Y j :=
  CommRingCat.ofHom (Pi.evalRingHom (fun k => Y k) j)

theorem pull_iso_bij (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {E E' : Spc} (g : E ⟶ E') [IsIso g] :
    Function.Bijective (pull R g F n) := by
  have h1 : ∀ x, pull R (inv g) F n (pull R g F n x) = x := fun x => by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  have h2 : ∀ x, pull R g F n (pull R (inv g) F n x) = x := fun x => by
    rw [← pull_comp, IsIso.hom_inv_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem pi_bij (hC : Coprod) (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {ι : Type} [Finite ι]
    (Y : ι → CommRingCat.{0}) :
    Function.Bijective fun (x : H R (sch.obj (Spec (CommRingCat.of (∀ k, Y k)))) F n) (j : ι) => pS R F n (ev Y j) x := by
  have h : (fun (x : H R (sch.obj (Spec (CommRingCat.of (∀ k, Y k)))) F n) (j : ι) => pS R F n (ev Y j) x) =
      (fun (x : H R (sch.obj (∐ fun k => Spec (Y k))) F n) (j : ι) =>
        pull R (sch.map (Sigma.ι (fun k => Spec (Y k)) j)) F n x) ∘ pull R (sch.map (sigmaSpec Y)) F n := by
    funext x j
    simp only [Function.comp_apply, pS, ev]
    rw [← pull_comp, ← Functor.map_comp, ι_sigmaSpec]
  rw [h]
  exact (hC R F (fun k => Spec (Y k)) n).comp (pull_iso_bij R F n _)

theorem pushout_pi {D Y' : CommRingCat.{0}} (φ' : D ⟶ Y') {ι : Type} [Fintype ι] (D₁ : ι → CommRingCat.{0})
    (e : ∀ k, D ⟶ D₁ k) (Y₁ : ι → CommRingCat.{0}) (u : ∀ k, Y' ⟶ Y₁ k) (φ₁ : ∀ k, D₁ k ⟶ Y₁ k)
    (hpo : ∀ k, IsPushout φ' (e k) (u k) (φ₁ k)) :
    IsPushout φ' (piMap D₁ e) (CommRingCat.ofHom (Pi.ringHom fun k => (u k).hom))
      (CommRingCat.ofHom (Pi.ringHom fun k => (φ₁ k).hom.comp (Pi.evalRingHom (fun k => D₁ k) k))) := by
  classical
  letI : Algebra D Y' := φ'.hom.toAlgebra
  letI : ∀ k, Algebra D (D₁ k) := fun k => (e k).hom.toAlgebra
  have hT : IsPushout φ' (piMap D₁ e) _ _ := CommRingCat.isPushout_tensorProduct D Y' (∀ k, D₁ k)
  have hTk : ∀ k, IsPushout φ' (e k) _ _ := fun k => CommRingCat.isPushout_tensorProduct D Y' (D₁ k)
  let isk : ∀ k, CommRingCat.of (Y' ⊗[D] D₁ k) ≅ Y₁ k := fun k => IsPushout.isoIsPushout _ _ (hTk k) (hpo k)
  have hl : ∀ k (y : Y'), (isk k).hom (y ⊗ₜ 1) = u k y := fun k y => by
    have := IsPushout.inl_isoIsPushout_hom _ _ (hTk k) (hpo k)
    exact congrArg (fun f => f.hom y) this
  have hr : ∀ k (d : D₁ k), (isk k).hom (1 ⊗ₜ d) = φ₁ k d := fun k d => by
    have := IsPushout.inr_isoIsPushout_hom _ _ (hTk k) (hpo k)
    exact congrArg (fun f => f.hom d) this
  let e₄ : CommRingCat.of (Y' ⊗[D] (∀ k, D₁ k)) ≅ CommRingCat.of (∀ k, Y₁ k) :=
    ((Algebra.TensorProduct.piRight D D Y' (fun k => D₁ k)).toRingEquiv.trans
      (RingEquiv.piCongrRight fun k => (isk k).commRingCatIsoToRingEquiv)).toCommRingCatIso
  refine hT.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e₄ (by simp) (by simp) ?_ ?_
  · refine CommRingCat.hom_ext (RingHom.ext fun y => funext fun k => ?_)
    have h4 : e₄.hom (y ⊗ₜ (1 : ∀ k, D₁ k)) k = (isk k).hom (y ⊗ₜ 1) := by
      simp [e₄, Algebra.TensorProduct.piRight_tmul]; rfl
    exact h4.trans (hl k y)
  · refine CommRingCat.hom_ext (RingHom.ext fun d => funext fun k => ?_)
    have h4 : e₄.hom ((1 : Y') ⊗ₜ d) k = (isk k).hom (1 ⊗ₜ d k) := by
      simp [e₄, Algebra.TensorProduct.piRight_tmul]; rfl
    exact h4.trans (hr k (d k))

theorem PushGlue_of (hC : Coprod) : LateralTheory.E.KillCokPf.Glue.PushGlue := by
  intro _ q _ i D Y' φ' m y ι _ D₁ e _ hk
  classical
  choose Y₁ u φ₁ hpo hz using hk
  choose z hz using hz
  obtain ⟨z₀, hz₀⟩ := (pi_bij hC (ZMod q) (tw q i) m D₁).2 z
  have hz₀' : ∀ j, pS _ (tw q i) m (ev D₁ j) z₀ = z j := fun j => congrFun hz₀ j
  let u'' : Y' ⟶ CommRingCat.of (∀ k, Y₁ k) := CommRingCat.ofHom (Pi.ringHom fun k => (u k).hom)
  let φ'' : CommRingCat.of (∀ k, D₁ k) ⟶ CommRingCat.of (∀ k, Y₁ k) :=
    CommRingCat.ofHom (Pi.ringHom fun k => (φ₁ k).hom.comp (Pi.evalRingHom (fun k => D₁ k) k))
  refine ⟨CommRingCat.of (∀ k, Y₁ k), u'', φ'', ?_, z₀, ?_⟩
  · exact pushout_pi φ' D₁ e Y₁ u φ₁ hpo
  · apply (pi_bij hC (ZMod q) (tw q i) m Y₁).1
    funext j
    have e1 : φ'' ≫ ev Y₁ j = ev D₁ j ≫ φ₁ j := rfl
    have e2 : u'' ≫ ev Y₁ j = u j := rfl
    show pS _ (tw q i) m (ev Y₁ j) (pS _ (tw q i) m φ'' z₀) = pS _ (tw q i) m (ev Y₁ j) (pS _ (tw q i) m u'' y)
    rw [← pS_comp, ← pS_comp, e1, e2, pS_comp, hz₀']
    exact hz j

end LateralTheory.E.PushGluePf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafPropsDescendPf LateralTheory.E.LeafPropsDescendPf.Split LateralTheory.E.LeafSpreadSmoothPf Topology

namespace LateralTheory.E.LeafSpreadSmoothAffSmPf

def LeafGenericSmooth : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D), IsAffine D →
    ∀ [LocallyOfFinitePresentation q], SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) →
    ∀ x : D, q.base x ∈ Set.range (toR R).base → x ∈ q.smoothLocus

def LeafSpreadOpen : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {D : Scheme.{0}} (q : D ⟶ Sp R), IsAffine D → LocallyOfFinitePresentation q →
    ∀ U : D.Opens, (∀ x : D, q.base x ∈ Set.range (toR R).base → x ∈ U) →
    ∃ (S : Subalgebra k Ω) (h : R ≤ S), S.FG ∧
      ∀ y : (pullback q (incl h) : Scheme.{0}), (pullback.fst q (incl h)).base y ∈ U

def LeafSmoothOfLocus : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {R S : Subalgebra k Ω}
    (h : R ≤ S) {D : Scheme.{0}} (q : D ⟶ Sp R) [LocallyOfFinitePresentation q],
    (∀ y : (pullback q (incl h) : Scheme.{0}), (pullback.fst q (incl h)).base y ∈ q.smoothLocus) →
    Smooth (pullback.snd q (incl h))

theorem leafSmoothOfLocus : LeafSmoothOfLocus := by
  intro k _ Ω _ _ R S h D q _ hy
  have hU : Smooth (q.smoothLocus.ι ≫ q) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact Scheme.Opens.ι_preimage_self _
  have sq := (isPullback_morphismRestrict (pullback.fst q (incl h)) q.smoothLocus).paste_vert
    (IsPullback.of_hasPullback q (incl h))
  have hs : Smooth (((pullback.fst q (incl h)) ⁻¹ᵁ q.smoothLocus).ι ≫ pullback.snd q (incl h)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq hU
  have hL : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth)
    (fun _ : Unit => (pullback.fst q (incl h)) ⁻¹ᵁ q.smoothLocus) ?_ (fun _ => hs)
  exact top_le_iff.mp fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨(), hy y⟩

def LeafClosedConstructible : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {D : Scheme.{0}} (q : D ⟶ Sp R), IsAffine D → LocallyOfFinitePresentation q →
    ∀ Z : Set D, IsClosed Z → IsConstructible Z

def LeafAvoidConstructible : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ T : Set (Sp R), IsConstructible T → (∀ z ∈ T, z ∉ Set.range (toR R).base) →
    ∃ (S : Subalgebra k Ω) (h : R ≤ S), S.FG ∧ ∀ w : (Sp S : Scheme.{0}), (incl h).base w ∉ T

theorem leafClosedConstructible : LeafClosedConstructible := by
  intro k _ Ω _ _ R hR D q hD hlfp Z hZ
  have : IsNoetherianRing R := isNoetherianRing_of_fg hR
  have : IsNoetherianRing (CommRingCat.of R) := this
  have : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsNoetherian D := ⟨⟩
  have hc : IsConstructible (Zᶜ) := (TopologicalSpace.NoetherianSpace.isCompact _).isConstructible hZ.isOpen_compl
  simpa using hc

def LeafGenericNbhd : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ T : Set (Sp R), IsConstructible T → (∀ z ∈ T, z ∉ Set.range (toR R).base) →
    ∃ f : R, f ≠ 0 ∧ ∀ z ∈ T, f ∈ (show PrimeSpectrum R from z).asIdeal

theorem leafInvert (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (hR : R.FG)
    (f : R) (hf : f ≠ 0) : ∃ (S : Subalgebra k Ω) (h : R ≤ S), S.FG ∧
      ∀ w : (Sp S : Scheme.{0}), f ∉ (show PrimeSpectrum R from (incl h).base w).asIdeal := by
  have hf0 : (f : Ω) ≠ 0 := fun e => hf (Subtype.ext e)
  refine ⟨R ⊔ Algebra.adjoin k {(f : Ω)⁻¹}, le_sup_left, hR.sup ⟨{(f : Ω)⁻¹}, by simp⟩, fun w hw => ?_⟩
  have hi : (f : Ω)⁻¹ ∈ R ⊔ Algebra.adjoin k {(f : Ω)⁻¹} :=
    (le_sup_right : Algebra.adjoin k {(f : Ω)⁻¹} ≤ _) (Algebra.subset_adjoin rfl)
  have hu : IsUnit (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ Algebra.adjoin k {(f : Ω)⁻¹}) f) := by
    refine IsUnit.of_mul_eq_one (⟨_, hi⟩ : ↥(R ⊔ Algebra.adjoin k {(f : Ω)⁻¹})) ?_
    apply Subtype.ext
    simp [hf0]
  have hw' : Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ Algebra.adjoin k {(f : Ω)⁻¹}) f ∈ w.asIdeal := hw
  exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hw' hu)

theorem leafGenericNbhd : LeafGenericNbhd := by
  classical
  intro k _ Ω _ _ R hR T hT hgen
  let η : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : (show Sp R from η) ∈ Set.range (toR R).base := by
    refine ⟨(show Sp Ω from (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω)), ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R Ω) ⊥ = ⊥
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp Subtype.val_injective
  obtain ⟨C, hC⟩ := (PrimeSpectrum.exists_constructibleSetData_iff (R := R) (s := T)).mpr hT
  have hne : ∀ c ∈ C, ∃ a : R, a ≠ 0 ∧ ∀ z ∈ c.toSet, a ∈ z.asIdeal := by
    intro c hc
    by_cases h0 : c.f = 0
    · refine ⟨1, one_ne_zero, fun z hz => absurd ?_ hz.2⟩
      simp [h0, PrimeSpectrum.mem_zeroLocus]
    · by_cases hg : ∃ i, c.g i ≠ 0
      · obtain ⟨i, hi⟩ := hg
        exact ⟨c.g i, hi, fun z hz => hz.1 ⟨i, rfl⟩⟩
      · simp only [not_exists, not_not] at hg
        exfalso
        have hηc : η ∈ c.toSet := by
          refine ⟨?_, ?_⟩
          · rintro _ ⟨i, rfl⟩
            simp [η, hg i]
          · intro h
            exact h0 (by simpa [η, PrimeSpectrum.mem_zeroLocus] using h)
        have hηT : η ∈ T := by
          rw [← hC]
          simp only [PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion]
          exact Set.mem_iUnion₂.mpr ⟨c, hc, hηc⟩
        exact hgen _ hηT hη
  choose! a ha using hne
  refine ⟨∏ c ∈ C, a c, Finset.prod_ne_zero_iff.mpr (fun c hc => (ha c hc).1), fun z hz => ?_⟩
  rw [← hC] at hz
  simp only [PrimeSpectrum.ConstructibleSetData.toSet] at hz
  obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.mp hz
  rw [← Finset.mul_prod_erase C a hc]
  exact Ideal.mul_mem_right _ _ ((ha c hc).2 z hzc)

theorem leafAvoidConstructible_of (hN : LeafGenericNbhd) : LeafAvoidConstructible := by
  intro k _ Ω _ _ R hR T hT hgen
  obtain ⟨f, hf, hfT⟩ := hN k Ω R hR T hT hgen
  obtain ⟨S, h, hS, hw⟩ := leafInvert k Ω R hR f hf
  exact ⟨S, h, hS, fun w hwT => hw w (hfT _ hwT)⟩

theorem leafSpreadOpen_of (hC : LeafClosedConstructible) (hA : LeafAvoidConstructible) : LeafSpreadOpen := by
  intro k _ Ω _ _ R hR D q hD hlfp U hU
  have : QuasiCompact q := inferInstance
  have hT := q.isConstructible_image (hC k Ω R hR q hD hlfp ((U : Set D)ᶜ) U.isOpen.isClosed_compl)
  obtain ⟨S, h, hS, hw⟩ := hA k Ω R hR _ hT (by
    rintro z ⟨x, hx, rfl⟩ hz
    exact hx (hU x hz))
  refine ⟨S, h, hS, fun y => ?_⟩
  by_contra hy
  apply hw ((pullback.snd q (incl h)).base y)
  refine ⟨(pullback.fst q (incl h)).base y, hy, ?_⟩
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]

theorem LeafSpreadSmoothAffSm_of_cut (hG : LeafGenericSmooth) (hO : LeafSpreadOpen) (hL : LeafSmoothOfLocus) :
    LeafSpreadSmoothAffSm := by
  intro k _ Ω _ _ R hR C D c q v hD hlfp hs hv
  obtain ⟨S, h, hS, hy⟩ := hO k Ω R hR q hD hlfp q.smoothLocus (hG k Ω R hR c q v hD hs hv)
  exact ⟨S, h, hS, hL k Ω h q hy⟩

def LeafStalkDescend : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D), IsAffine D →
    ∀ [LocallyOfFinitePresentation q], SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) → ∀ y : C, v.base y ∈ q.smoothLocus

theorem leafGenericSmooth_of (hS : LeafStalkDescend) : LeafGenericSmooth := by
  intro k _ Ω _ _ R hR C D c q v hD _ hs hv x ⟨w, hw⟩
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback x w hw.symm
  have := hS k Ω R hR c q v hD hs hv (hv.isoPullback.inv.base z)
  rwa [← Scheme.Hom.comp_apply, hv.isoPullback_inv_fst, hz1] at this

theorem LeafSpreadSmoothAffSm_of (hD : LeafStalkDescend) :
    LeafSpreadSmoothAffSm :=
  LeafSpreadSmoothAffSm_of_cut (leafGenericSmooth_of hD) (leafSpreadOpen_of leafClosedConstructible (leafAvoidConstructible_of leafGenericNbhd))
    leafSmoothOfLocus

end LateralTheory.E.LeafSpreadSmoothAffSmPf

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafKill1V2Cut
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

theorem goal_of' (hN : LateralTheory.E.SecondDegreeKilling.Nbhd.LeafKillNbhd) (hW : LateralTheory.E.SecondDegreeKilling.LeafPtW)
    (hV : LateralTheory.E.SecondDegreeKilling.LeafPtV) : LateralTheory.E.LeafDegCut.LeafKill1 := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s ι _ V hV' p g1 g2 hp hp1 hp2 hSHV U y
  refine LateralTheory.E.SecondDegreeKilling.Nbhd.killPt_of hN hH q k hq i s ι (g2 ≫ g1 ≫ p) hp2 U 1 (gY q i (g1 ≫ p) g2 ι U 1 y) ?_
  intro A _ t hA
  by_cases h : Set.range (t ≫ U.hom : Sp A ⟶ B) ⊆ (V : Set B)
  · exact hV hH q k hq i s ι V hV' (g1 ≫ p) g2 hp1 hp2 U A t hA h 1 (hSHV A (t ≫ U.hom) hA h).2.2.1 y
  · have := hW hH q k hq i s ι V hV' (g2 ≫ g1 ≫ p) hp2 A (t ≫ U.hom) hA h 1
    exact Subsingleton.elim _ _

end LateralTheory.E.LeafKill1V2Cut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.NeighbourhoodKilling
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.SecondDegreeKilling.Nbhd

structure Tri (J : Type) [SmallCategory J] where
  Rm : J ⥤ AddCommGrpCat.{1}
  Ym : J ⥤ AddCommGrpCat.{1}
  Yp : J ⥤ AddCommGrpCat.{1}
  Wp : J ⥤ AddCommGrpCat.{1}
  cR : Cocone Rm
  cYm : Cocone Ym
  cYp : Cocone Yp
  cWp : Cocone Wp
  fg : Rm ⟶ Ym
  fgL : cR.pt ⟶ cYm.pt
  fg_w : ∀ j, cR.ι.app j ≫ fgL = fg.app j ≫ cYm.ι.app j
  dl : Wp ⟶ Rm
  dlL : cWp.pt ⟶ cR.pt
  dl_w : ∀ j, cWp.ι.app j ≫ dlL = dl.app j ≫ cR.ι.app j
  rs : Yp ⟶ Wp
  rsL : cYp.pt ⟶ cWp.pt
  rs_w : ∀ j, cYp.ι.app j ≫ rsL = rs.app j ≫ cWp.ι.app j

  exR : ∀ j (x : Rm.obj j), (fg.app j).hom x = 0 → ∃ w, (dl.app j).hom w = x

  exWL : ∀ w : cWp.pt, dlL.hom w = 0 → ∃ y, rsL.hom y = w

  cx : ∀ j (y : Yp.obj j), (dl.app j).hom ((rs.app j).hom y) = 0

  injYm : ∀ j (y : Ym.obj j), (cYm.ι.app j).hom y = 0 → ∃ (k : J) (f : j ⟶ k), (Ym.map f).hom y = 0

  surYp : ∀ y : cYp.pt, ∃ (j : J) (y' : Yp.obj j), (cYp.ι.app j).hom y' = y

  injWp : ∀ j (w : Wp.obj j), (cWp.ι.app j).hom w = 0 → ∃ (k : J) (f : j ⟶ k), (Wp.map f).hom w = 0

def PairFive : Prop := ∀ (J : Type) [SmallCategory J] [IsFiltered J] (T : Tri J) (j : J) (x : T.Rm.obj j),
  (T.cR.ι.app j).hom x = 0 → ∃ (k : J) (f : j ⟶ k), (T.Rm.map f).hom x = 0

def ObsExact : Prop := ∀ (q : ℕ) [NeZero q] {U E : Spc} (u : U ⟶ E) (i m : ℤ) (y : Hrel (ZMod q) u (tw q i) (m + 1)),
  fgt (ZMod q) u (tw q i) (m + 1) y = 0 → ∃ w, LateralTheory.E.GlueRelPf.obs q u i m w = y

def ObsNat : Prop := ∀ (q : ℕ) [NeZero q] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
  (comm : f' ≫ e = u ≫ f) (i m : ℤ) (w : Ht q U m i),
  rpull (ZMod q) f f' u e comm (tw q i) (m + 1) (LateralTheory.E.GlueRelPf.obs q f i m w) =
    LateralTheory.E.GlueRelPf.obs q f' i m (pull (ZMod q) u (tw q i) m w)

def Bridge : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (m : ℤ) (z : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m) (u : U.left),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (T : Tri J) (j0 : J) (x0 : T.Rm.obj j0) (A : Type) (_ : CommRing A)
    (t : Sp A ⟶ U.left), SH A ∧
    (LateralTheory.E.SecondDegreeKilling.rT q i p ι U t m z = 0 → (T.cR.ι.app j0).hom x0 = 0) ∧
    ∀ (j : J) (f : j0 ⟶ j), (T.Rm.map f).hom x0 = 0 →
      ∃ (U' : B.Etale) (a : U' ⟶ U), u ∈ Set.range a.left ∧ rY q i p ι a m z = 0

theorem goal_of (hF : PairFive) (_hO : ObsExact) (_hN : ObsNat) (hB : Bridge) : LeafKillNbhd := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp U m z hz u
  obtain ⟨J, _, _, T, j0, x0, A, _, t, hSH, hlim, hst⟩ := hB hH q k hq i toK ι p hp U m z u
  obtain ⟨j, f, hf⟩ := hF J T j0 x0 (hlim (hz A t hSH))
  exact hst j f hf

end LateralTheory.E.NeighbourhoodKilling
end
end
