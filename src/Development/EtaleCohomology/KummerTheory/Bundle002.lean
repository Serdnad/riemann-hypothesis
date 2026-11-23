module

public import Development.EtaleCohomology.KummerTheory.InjSlice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Comma.LocallySmall
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.KummerTheory.InsepPf

theorem res_comp {R : Type} [CommRing R] (F : Shv R) {W V U : Scheme.{0}} (g : W ⟶ V) (h : V ⟶ U) (x : Sec F U) :
    Sec.res (g ≫ h) x = Sec.res g (Sec.res h x) := by
  simp [Sec.res]

theorem res_id {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (x : Sec F U) : Sec.res (𝟙 U) x = x := by
  simp [Sec.res]

theorem res_bij_iso {R : Type} [CommRing R] (F : Shv R) {V U : Scheme.{0}} (e : V ≅ U) :
    Function.Bijective (Sec.res (F := F) e.hom) := by
  refine Function.bijective_iff_has_inverse.2 ⟨Sec.res e.inv, fun x => ?_, fun x => ?_⟩
  · rw [← res_comp, e.inv_hom_id, res_id]
  · rw [← res_comp, e.hom_inv_id, res_id]

theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (Prim.map (Scheme.Γ.map g.op).hom ζ) := by
  have h := congrArg (fun f => f.hom (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q))) : (twF q i).obj Γ(U, ⊤)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
  simp only [ModuleCat.hom_comp] at h
  unfold twGen ofRings.sec
  refine h.symm.trans ?_
  show ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom
    (((Scheme.Γ ⋙ twF q i).map g.op).hom (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q))))) = _
  refine congrArg ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom ?_
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (Scheme.Γ.map g.op).hom) (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))) = _
  exact congrArg _ (Finsupp.mapDomain_single (f := Prim.map (Scheme.Γ.map g.op).hom) (a := ζ) (b := (1 : ULift.{1} (ZMod q))))

theorem res_smul {R : Type} [CommRing R] (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) (c : ULift.{1} R) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x := map_smul (F.obj.map g.op).hom c x

theorem res_spec_bij (hTw : TwSec) (q : ℕ) [NeZero q] {A B : Type} [CommRing A] [CommRing B] (hA : SH A) (hB : SH B)
    (hq : IsUnit (q : A)) (φ : A →+* B) (i : ℤ) :
    Function.Bijective (Sec.res (F := tw q i) (Spec.map (CommRingCat.ofHom φ))) := by
  have hqB : IsUnit (q : B) := by simpa using hq.map φ
  obtain ⟨⟨ζ⟩, hζ⟩ := hTw q A hA hq
  have h1 := hζ i ζ
  have h2 := (hTw q B hB hqB).2 i (Prim.map (Scheme.Γ.map (Spec.map (CommRingCat.ofHom φ)).op).hom ζ)
  have e : (Sec.res (F := tw q i) (Spec.map (CommRingCat.ofHom φ))) ∘
      (fun t : ZMod q => (ULift.up t : ULift.{1} (ZMod q)) • twGen i ζ) =
      fun t : ZMod q => (ULift.up t : ULift.{1} (ZMod q)) •
        twGen i (Prim.map (Scheme.Γ.map (Spec.map (CommRingCat.ofHom φ)).op).hom ζ) := by
    funext t
    simp only [Function.comp]
    rw [res_smul, twGen_res]
    rfl
  exact (Function.Bijective.of_comp_iff _ h1).1 (by rw [e]; exact h2)

theorem res_bij (hTw : TwSec) (q : ℕ) [NeZero q] (i : ℤ) {P Q : Scheme.{0}} (m : P ⟶ Q) {A B : Type} [CommRing A]
    [CommRing B] (hA : SH A) (hB : SH B) (hq : IsUnit (q : A)) (iP : P ≅ Spec (CommRingCat.of B))
    (iQ : Q ≅ Spec (CommRingCat.of A)) : Function.Bijective (Sec.res (F := tw q i) m) := by
  set g' := iP.inv ≫ m ≫ iQ.hom
  have hm : m = iP.hom ≫ Spec.map (CommRingCat.ofHom (Spec.preimage g').hom) ≫ iQ.inv := by
    simp [g']
  have hg := res_spec_bij hTw q hA hB hq (Spec.preimage g').hom i
  have : (Sec.res (F := tw q i) m) = Sec.res iP.hom ∘ Sec.res (Spec.map (CommRingCat.ofHom (Spec.preimage g').hom)) ∘
      Sec.res (F := tw q i) iQ.inv := by
    funext x
    simp only [Function.comp]
    rw [hm, res_comp, res_comp]
  rw [this]
  exact (res_bij_iso _ iP).comp (hg.comp (res_bij_iso _ iQ.symm))

theorem sub_of_iso {R : Type} [CommRing R] (F : Shv R) (n : ℤ) {P : Scheme.{0}} {B : Type} [CommRing B]
    (e : P ≅ Spec (CommRingCat.of B)) (h : Subsingleton (H R (sp B) F n)) : Subsingleton (H R (sch.obj P) F n) := by
  refine ⟨fun x y => ?_⟩
  have hx : ∀ z : H R (sch.obj P) F n, z = pull R (sch.map e.hom) F n (pull R (sch.map e.inv) F n z) := fun z => by
    rw [← pull_comp, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [hx x, hx y, Subsingleton.elim (pull R (sch.map e.inv) F n x) (pull R (sch.map e.inv) F n y)]

theorem bij_of_sub {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G →+ G') (h : Subsingleton G)
    (h' : Subsingleton G') : Function.Bijective f :=
  ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

theorem eqv_of (hA9 : A9) (hB2 : B2) (hTw : TwSec) (q : ℕ) [NeZero q] (i : ℤ) {P Q : Scheme.{0}} (m : P ⟶ Q)
    {A B : Type} [CommRing A] [CommRing B] (hA : SH A) (hB : SH B) (hq : IsUnit (q : A))
    (iP : P ≅ Spec (CommRingCat.of B)) (iQ : Q ≅ Spec (CommRingCat.of A)) : Eqv _ (sch.map m) (tw q i) := by
  intro n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · exact bij_of_sub _ ((hA9 _ (tw q i)).1 _ n hn) ((hA9 _ (tw q i)).1 _ n hn)
  · obtain ⟨e, he, -⟩ := (hA9 _ (tw q i)).2
    have h0 := res_bij hTw q i m hA hB hq iP iQ
    have : (pull _ (sch.map m) (tw q i) 0 : _ → _) = e P ∘ Sec.res m ∘ (e Q).symm := by
      funext x
      simp only [Function.comp]
      rw [← he, AddEquiv.apply_symm_apply]
    rw [this]
    exact (e P).bijective.comp (h0.comp (e Q).symm.bijective)
  · exact bij_of_sub _ (sub_of_iso _ n iQ (hB2 _ A hA _ n hn)) (sub_of_iso _ n iP (hB2 _ B hB _ n hn))

theorem Insep_of (hSH : SHInsep) (hTw : TwSec) : Insep := by
  intro hA9 hB2 hB3 q _ κ K _ _ _ _ hq X p i
  have hqX : IsUnit (q : Γ(X, ⊤)) := by
    have h1 : IsUnit (q : Γ(Spec (CommRingCat.of κ), ⊤)) := by
      simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom
    simpa using h1.map (p.appTop).hom
  refine hB3 q (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap κ K)))) (𝟙 X) hqX i ?_
  intro A _ s hA
  let _ : Algebra κ A := (Spec.preimage (s ≫ p)).hom.toAlgebra
  have hsp : s ≫ p = Spec.map (CommRingCat.ofHom (algebraMap κ A)) := (Spec.map_preimage _).symm
  have hqA : IsUnit (q : A) := by simpa using hq.map (algebraMap κ A)
  refine eqv_of hA9 hB2 hTw q i _ hA (hSH κ K A hA) hqA ?_ (asIso (pullback.snd (𝟙 X) s))
  exact pullback.congrHom (Category.comp_id _) rfl ≪≫ pullbackSymmetry _ _ ≪≫
    pullbackRightPullbackFstIso p _ s ≪≫ pullback.congrHom hsp rfl ≪≫ pullbackSpecIso κ A K

end LateralTheory.KummerTheory.InsepPf
end
end

section

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.KummerTheory.SHenCut

def Sat {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) (e : Cocone D) : Prop :=
  ∀ (j : J) (B : CommRingCat.{0}) (φ : D.obj j ⟶ B) (β : B ⟶ e.pt), φ.hom.Etale → φ ≫ β = e.ι.app j →
    ∃ (k : J) (f : j ⟶ k) (γ : B ⟶ D.obj k), φ ≫ γ = D.map f ∧ γ ≫ e.ι.app k = β

def UnitLift {C Ω : Type} [CommRing C] [CommRing Ω] (ε : C →+* Ω) : Prop := ∀ x, ε x ≠ 0 → IsUnit x

def RootLift {C Ω : Type} [CommRing C] [CommRing Ω] (ε : C →+* Ω) : Prop :=
  ∀ f : Polynomial C, f.Monic → ∀ ω : Ω, f.eval₂ ε ω = 0 → f.derivative.eval₂ ε ω ≠ 0 → ∃ a : C, f.IsRoot a ∧ ε a = ω

def SatUnit : Prop := ∀ {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (hc : IsColimit c)
  (e : Cocone D), IsField e.pt → Sat D e → UnitLift (hc.desc e).hom

def SatRoot : Prop := ∀ {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (hc : IsColimit c)
  (e : Cocone D), IsField e.pt → Sat D e → RootLift (hc.desc e).hom

def SHOfLift : Prop := ∀ (C Ω : Type) [CommRing C] [Field Ω] [IsAlgClosed Ω] (ε : C →+* Ω), UnitLift ε → RootLift ε → SH C

abbrev Et : MorphismProperty CommRingCat.{0} := RingHom.toMorphismProperty RingHom.Etale

instance : Et.IsStableUnderCobaseChange :=
  RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
instance : Et.IsStableUnderComposition where
  comp_mem f g hf hg := RingHom.Etale.stableUnderComposition f.hom g.hom hf hg
instance : Et.ContainsIdentities where
  id_mem _ := RingHom.Etale.of_bijective Function.bijective_id
instance : Et.HasOfPrecompProperty Et where
  of_precomp {A B C} f g hf hfg := by
    have hf' : f.hom.Etale := hf
    have hfg' : (g.hom.comp f.hom).Etale := hfg
    algebraize [f.hom, g.hom, g.hom.comp f.hom]
    exact Algebra.Etale.of_restrictScalars A B C

abbrev Nb {R Ω : CommRingCat.{0}} (s : R ⟶ Ω) := CostructuredArrow (MorphismProperty.Under.forget Et ⊤ R) (Under.mk s)

instance {R Ω : CommRingCat.{0}} (s : R ⟶ Ω) : EssentiallySmall.{0} (Nb s) := by
  have : EssentiallySmall.{0} (MorphismProperty.Under Et ⊤ R) := essentiallySmall_of_le (fun _ _ f hf => by
    have hf' : f.hom.Etale := hf
    exact RingHom.FiniteType.of_finitePresentation (RingHom.Etale.iff_flat_and_formallyUnramified.1 hf').2.2) R
  infer_instance

instance {R Ω : CommRingCat.{0}} (s : R ⟶ Ω) : IsFiltered (Nb s) := by
  have : RepresentablyCoflat (MorphismProperty.Under.forget Et ⊤ R) := coflat_of_preservesFiniteColimits _
  infer_instance

def Nb.ring {R Ω : CommRingCat.{0}} (s : R ⟶ Ω) : Nb s ⥤ CommRingCat.{0} :=
  CostructuredArrow.proj _ _ ⋙ MorphismProperty.Under.forget Et ⊤ R ⋙ Under.forget R

theorem exists_sat {R Ω : CommRingCat.{0}} (s : R ⟶ Ω) : ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J)
    (D : J ⥤ CommRingCat.{0}) (u : (Functor.const J).obj R ⟶ D) (e : D ⟶ (Functor.const J).obj Ω),
    Sat D (Cocone.mk Ω e) ∧ ∀ j, (u.app j).hom.Etale ∧ u.app j ≫ e.app j = s := by
  let E := equivSmallModel.{0} (Nb s)
  refine ⟨SmallModel.{0} (Nb s), inferInstance, IsFiltered.of_equivalence E, E.inverse ⋙ Nb.ring s,
    { app := fun j => (E.inverse.obj j).left.hom, naturality := fun j k f => ?_ },
    { app := fun j => (E.inverse.obj j).hom.right, naturality := fun j k f => ?_ }, ?_, fun j => ⟨?_, ?_⟩⟩
  · exact (Category.id_comp _).trans (Under.w ((MorphismProperty.Under.forget Et ⊤ R).map (E.inverse.map f).left)).symm
  · exact (congrArg (fun t => t.right) (CostructuredArrow.w (E.inverse.map f))).trans (Category.comp_id _).symm
  · intro j B φ β hφ hβ
    have hw : (E.inverse.obj j).left.hom ≫ (E.inverse.obj j).hom.right = s := Under.w (E.inverse.obj j).hom
    let A : MorphismProperty.Under Et ⊤ R := MorphismProperty.Under.mk ⊤ ((E.inverse.obj j).left.hom ≫ φ)
      (Et.comp_mem _ _ (E.inverse.obj j).left.prop hφ)
    let N : Nb s := CostructuredArrow.mk (Y := A) (Under.homMk β
      ((Category.assoc _ _ _).trans ((congrArg (fun t => (E.inverse.obj j).left.hom ≫ t) hβ).trans hw)))
    let m : E.inverse.obj j ⟶ N := CostructuredArrow.homMk (MorphismProperty.Under.homMk φ rfl trivial)
      (Under.UnderMorphism.ext hβ)
    refine ⟨E.functor.obj N, E.inverse.preimage (m ≫ E.unit.app N), (Nb.ring s).map (E.unit.app N), ?_, ?_⟩
    · change (Nb.ring s).map m ≫ _ = (Nb.ring s).map (E.inverse.map _)
      rw [Functor.map_preimage, Functor.map_comp]
    · exact congrArg (fun t => t.right) (CostructuredArrow.w (E.unit.app N))
  · exact (E.inverse.obj j).left.prop
  · exact Under.w (E.inverse.obj j).hom

theorem goal_of (h1 : SatUnit) (h2 : SatRoot) (h3 : SHOfLift) : LateralTheory.KummerTheory.StrictHenselization := by
  intro R 𝔭
  let Ω := AlgebraicClosure 𝔭.asIdeal.ResidueField
  let s : R →+* Ω := (algebraMap 𝔭.asIdeal.ResidueField Ω).comp (algebraMap R 𝔭.asIdeal.ResidueField)
  have hs : RingHom.ker s = 𝔭.asIdeal := by
    rw [RingHom.ker_comp_of_injective _ (algebraMap 𝔭.asIdeal.ResidueField Ω).injective,
      Ideal.ker_algebraMap_residueField]
  obtain ⟨J, _, _, D, u, e, hsat, hu⟩ := exists_sat (Ω := CommRingCat.of Ω) (CommRingCat.ofHom s)
  have hF : IsField (Cocone.mk (F := D) (CommRingCat.of Ω) e).pt := Field.toIsField Ω
  refine ⟨J, inferInstance, inferInstance, D, colimit.cocone D, colimit.isColimit D, u,
    h3 _ Ω _ (h1 D _ (colimit.isColimit D) _ hF hsat) (h2 D _ (colimit.isColimit D) _ hF hsat), fun j => ⟨(hu j).1, ?_⟩⟩
  let ej : D.obj j →+* Ω := (e.app j).hom
  refine ⟨⟨RingHom.ker ej, RingHom.ker_isPrime ej⟩, ?_⟩
  have : ej.comp (u.app j).hom = s := congrArg CommRingCat.Hom.hom (hu j).2
  exact (congrArg RingHom.ker this).trans hs

end LateralTheory.KummerTheory.SHenCut

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

theorem shinv_eqv_of_iso {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') [IsIso f] (F : Shv R) : Eqv R f F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem shinv_pull_comp_fun {R : Type} [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R) (n : ℤ) :
    (pull R (f ≫ g) F n : H R E'' F n → H R E F n) = pull R f F n ∘ pull R g F n := by
  funext x; exact pull_comp R f g F n x

theorem shinv_eqv_comp {R : Type} [CommRing R] {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv R}
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n; rw [shinv_pull_comp_fun]; exact (hf n).comp (hg n)

theorem shinv_eqv_right {R : Type} [CommRing R] {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv R}
    (hf : Eqv R f F) (hfg : Eqv R (f ≫ g) F) : Eqv R g F := by
  intro n; have := hfg n; rw [shinv_pull_comp_fun] at this
  exact (Function.Bijective.of_comp_iff' (hf n) _).1 this

theorem SHInv_of (hAlgExt : AlgExt) (hInsep : Insep) : SHInv := by
  intro hA9 hB2 hB3 hE2 hE3 q _ k _ _ hq X p _ _ A s hSH i
  obtain ⟨hHL, hsc⟩ := hSH
  have hqA : IsUnit (q : A) := by simpa using hq.map s.hom
  have hqκ : IsUnit (q : IsLocalRing.ResidueField A) := by simpa using hqA.map (IsLocalRing.residue A)
  haveI : IsPurelyInseparable (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A)) :=
    (isSepClosed_iff_isPurelyInseparable_algebraicClosure _ _).mp hsc
  let res := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  let alg := Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField A)
    (AlgebraicClosure (IsLocalRing.ResidueField A))))
  let pA := pullback.snd p (Spec.map s)
  have h1 : Eqv _ (sch.map (pullback.fst pA res)) (tw q i) := hE2 q A ⟨hHL, hsc⟩ hqA pA i
  have h2 : Eqv _ (sch.map (pullback.fst (pullback.snd pA res) alg)) (tw q i) :=
    hInsep hA9 hB2 hB3 q _ _ hqκ (pullback.snd pA res) i
  let f : k →+* AlgebraicClosure (IsLocalRing.ResidueField A) :=
    (algebraMap (IsLocalRing.ResidueField A) _).comp ((IsLocalRing.residue A).comp s.hom)
  have h3 := hAlgExt hE2 hE3 q k _ f hq p i
  have hf : Spec.map (CommRingCat.ofHom f) = (alg ≫ res) ≫ Spec.map s := by
    simp only [alg, res, ← Spec.map_comp]; rfl
  have h3' : Eqv _ (sch.map (pullback.fst p ((alg ≫ res) ≫ Spec.map s))) (tw q i) := by
    have key : ∀ g, g = (alg ≫ res) ≫ Spec.map s → Eqv _ (sch.map (pullback.fst p g)) (tw q i) →
        Eqv _ (sch.map (pullback.fst p ((alg ≫ res) ≫ Spec.map s))) (tw q i) := by
      intro g hg h; subst hg; exact h
    exact key _ hf h3
  have hcomp : pullback.fst (pullback.snd pA res) alg ≫ pullback.fst pA res ≫ pullback.fst p (Spec.map s) =
      ((pullbackLeftPullbackSndIso pA res alg).hom ≫ (pullbackLeftPullbackSndIso p (Spec.map s) (alg ≫ res)).hom) ≫
        pullback.fst p ((alg ≫ res) ≫ Spec.map s) := by
    rw [Category.assoc, pullbackLeftPullbackSndIso_hom_fst p (Spec.map s) (alg ≫ res)]
    erw [← Category.assoc (pullbackLeftPullbackSndIso pA res alg).hom, pullbackLeftPullbackSndIso_hom_fst pA res alg]
    rw [Category.assoc]
  have hall : Eqv _ (sch.map (pullback.fst (pullback.snd pA res) alg) ≫ sch.map (pullback.fst pA res) ≫
      sch.map (pullback.fst p (Spec.map s))) (tw q i) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hcomp, Functor.map_comp]
    exact shinv_eqv_comp (shinv_eqv_of_iso _ _) h3'
  exact shinv_eqv_right h1 (shinv_eqv_right h2 hall)

end LateralTheory.KummerTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.KummerTheory

def AdicLim : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (i : ℤ), (∀ b, BockData l b E i) →
  (∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) → ∀ n : ℤ, Module.Finite ℤ_[l] (Hl l E n i) ∧
    (∀ (k : ℕ) (x : Hl l E n i), lev l x k = 0 → ∃ y : Hl l E n i, x = ((l : ℤ_[l]) ^ k) • y) ∧
    ∃ M : ℕ, 0 < M ∧ ∀ (k : ℕ) (z : Ht (l ^ k) E n i), ∃ x : Hl l E n i, lev l x k = M • z

def AdicAlg : Prop := ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ), Module.Finite ℤ_[l] (Hl l E n i) →
  (∀ (k : ℕ) (x : Hl l E n i), lev l x k = 0 → ∃ y : Hl l E n i, x = ((l : ℤ_[l]) ^ k) • y) →
  ∀ M : ℕ, 0 < M → (∀ (k : ℕ) (z : Ht (l ^ k) E n i), ∃ x : Hl l E n i, lev l x k = M • z) →
  ∃ (r : ℕ) (c : Fin r → Hl l E n i) (N : ℕ), 0 < N ∧ QBasis l c ∧
    ∀ k, IsoUpTo N (comb (l ^ k) fun s => lev l (c s) k)

theorem AdicDeg_of (h1 : AdicLim) (h2 : AdicAlg) : AdicDeg := by
  intro hA l _ E i hB hF n
  obtain ⟨hfin, hker, M, hM, hcok⟩ := h1 hA l E i hB hF n
  exact h2 l E n i hfin hker M hM hcok

end LateralTheory.KummerTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.KummerTheory.AlgExtPf

variable {R : Type} [CommRing R] (F : Shv R)

theorem eqv_comp {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (hf : Eqv R f F) (hg : Eqv R g F) :
    Eqv R (f ≫ g) F := fun n => by
  have : (pull R (f ≫ g) F n : _ → _) = (pull R f F n) ∘ (pull R g F n) := funext (pull_comp R f g F n)
  rw [this]; exact (hf n).comp (hg n)

theorem eqv_cancel {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (h : Eqv R (f ≫ g) F) (hf : Eqv R f F) :
    Eqv R g F := fun n => by
  have hc : ∀ x, pull R (f ≫ g) F n x = pull R f F n (pull R g F n x) := pull_comp R f g F n
  refine ⟨fun a b hab => (h n).1 (by rw [hc, hc, hab]), fun y => ?_⟩
  obtain ⟨z, hz⟩ := (h n).2 (pull R f F n y)
  exact ⟨z, (hf n).1 (by rw [← hc, hz])⟩

theorem eqv_iso {E E' : Spc} (f : E ⟶ E') [IsIso f] : Eqv R f F := fun n => by
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem eqv_sch_iso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] : Eqv R (sch.map f) F := eqv_iso F _

theorem eqv_fst_comp {W X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y)
    (h1 : Eqv R (sch.map (pullback.fst (pullback.snd f g) g')) F) (h2 : Eqv R (sch.map (pullback.fst f g)) F) :
    Eqv R (sch.map (pullback.fst f (g' ≫ g))) F := by
  rw [← pullbackLeftPullbackSndIso_inv_fst, Functor.map_comp, Functor.map_comp]
  exact eqv_comp F (eqv_sch_iso F _) (eqv_comp F h1 h2)

theorem eqv_fst_congr {X Z W : Scheme.{0}} (f : X ⟶ Z) {h h' : W ⟶ Z} (e : h = h') :
    Eqv R (sch.map (pullback.fst f h)) F → Eqv R (sch.map (pullback.fst f h')) F := by
  subst e; exact id

end LateralTheory.KummerTheory.AlgExtPf

namespace LateralTheory.KummerTheory
open LateralTheory.KummerTheory.AlgExtPf

theorem AlgExt_of (hP : Place) : AlgExt := by
  intro hE2 hE3 q _ k K _ _ _ _ f hq X p _ _ i
  let _ := f.toAlgebra
  obtain ⟨T, σ, hσ, hres, hAIC, hSH⟩ := hP k K
  have hqT : IsUnit ((q : ℕ) : T) := by simpa using hq.map σ
  set gσ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom σ) with hgσ
  set gr : Spec (CommRingCat.of (IsLocalRing.ResidueField T)) ⟶ Spec (CommRingCat.of T) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue T)) with hgr
  have e2 := hE2 q T hSH hqT (pullback.snd p gσ) i

  have hiso : IsIso (CommRingCat.ofHom ((IsLocalRing.residue T).comp σ)) :=
    (RingEquiv.ofBijective _ hres).toCommRingCatIso.isIso_hom
  have hcomp : gr ≫ gσ = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue T).comp σ)) := by
    rw [hgr, hgσ, ← Spec.map_comp]; rfl
  have hs : Eqv (ZMod q) (sch.map (pullback.fst p (gr ≫ gσ))) (tw q i) := by
    rw [hcomp]; exact eqv_sch_iso _ _
  rw [← pullbackLeftPullbackSndIso_inv_fst, Functor.map_comp, Functor.map_comp] at hs
  have hT : Eqv (ZMod q) (sch.map (pullback.fst p gσ)) (tw q i) :=
    eqv_cancel _ (eqv_cancel _ hs (eqv_sch_iso _ _)) e2

  have e3 := hE3 q T hAIC hqT (pullback.snd p gσ) i
  let eK : FractionRing T ≃+* K := (IsLocalization.algEquiv (nonZeroDivisors T) (FractionRing T) K).toRingEquiv
  set gj : Spec (CommRingCat.of (FractionRing T)) ⟶ Spec (CommRingCat.of T) :=
    Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T))) with hgj
  set ge : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (FractionRing T)) :=
    Spec.map (CommRingCat.ofHom eK.toRingHom) with hge
  have hge_iso : IsIso ge := by
    have : IsIso (CommRingCat.ofHom eK.toRingHom) := eK.toCommRingCatIso.isIso_hom
    rw [hge]; infer_instance
  have hfac : (ge ≫ gj) ≫ gσ = Spec.map (CommRingCat.ofHom f) := by
    rw [hge, hgj, hgσ, ← Spec.map_comp, ← Spec.map_comp]
    congr 1; ext x
    have h1 := hσ x
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    change eK (algebraMap T (FractionRing T) (σ x)) = f x
    rw [show f x = algebraMap k K x from rfl, ← h1]
    exact (IsLocalization.algEquiv (nonZeroDivisors T) (FractionRing T) K).commutes (σ x)
  refine eqv_fst_congr _ p hfac (eqv_fst_comp _ p gσ (ge ≫ gj) ?_ hT)
  refine eqv_fst_comp _ _ gj ge ?_ e3
  exact eqv_sch_iso _ _

end LateralTheory.KummerTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

theorem cupSch_ev_pos {R : Type} [CommRing R] {X : Scheme.{0}} {I : Cx R} {n : ℤ}
    (α : Cochain ((chains R).obj (sch.obj X)) I n)
    (hα : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : Sx (sch.obj X) (p + 1) U),
      ev α (p + 1) s h U y = 0) :
    ∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (y : Sx (sch.obj X) p U), ev α p s h U y = 0 := by
  intro p hp s h U y
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  exact hα q s h U y

theorem cupSch_mul_cast {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) {n m k : ℤ}
    (f : ∀ s : ℤ, s = n → Sec (I.X s) U) (g : ∀ t : ℤ, t = m → Sec (J.X t) U)
    (s t : ℤ) (hs : s = n) (ht : t = m) (h : s + t = k) (hk : n + m = k) :
    μ.mul U s t k h (f s hs) (g t ht) = μ.mul U n m k hk (f n rfl) (g m rfl) := by
  subst hs; subst ht; rfl

theorem CupSch_of (hAW : CupAW) : CupSch := by
  intro R _ I J K μ X n m k hk x y a b hx hy
  obtain ⟨α, rfl, ha, hα⟩ := hx
  obtain ⟨β, rfl, hb, hβ⟩ := hy
  obtain ⟨γ, hγ, hc⟩ := hAW R μ (sch.obj X) hk α β
  refine ⟨γ, hc.symm, ?_, ?_⟩
  · have h0 := hγ 0 k (by simp) X (𝟙 X)
    rw [h0, Fin.sum_univ_one]
    simp only [Fin.val_zero, Nat.cast_zero, mul_zero, Int.negOnePow_zero, one_smul]
    rw [← ha, ← hb]
    exact cupSch_mul_cast μ X (fun s hs => ev α.1 0 s (by omega) X (𝟙 X)) (fun t ht => ev β.1 0 t (by omega) X (𝟙 X))
      _ _ (by simp) (by simp) _ hk
  · intro p s h U z
    rw [hγ (p + 1) s h U z]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : (i : ℕ) = 0
    · rw [cupSch_ev_pos β.1 hβ ((p + 1) - (i : ℕ)) (by omega), map_zero, smul_zero]
    · rw [cupSch_ev_pos α.1 hα (i : ℕ) (by omega), map_zero, LinearMap.zero_apply, smul_zero]

end LateralTheory.KummerTheory
end
end
