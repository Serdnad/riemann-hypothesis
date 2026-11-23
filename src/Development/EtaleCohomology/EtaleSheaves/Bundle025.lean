module

public import Development.EtaleCohomology.EtaleSheaves.Bundle012
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.RingTheory.Etale.StandardEtale
public import Development.EtaleCohomology.EtaleSheaves.Bundle013
public import Development.EtaleCohomology.EtaleSheaves.LineHigh
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafCover2Pf

variable (R : Type) [CommRing R]

theorem pre_eq {P Q : PSh} (G : Shv R) (φ : Q ⟶ P) (u v : (free R).obj P ⟶ G)
    (h : (free R).map φ ≫ u = (free R).map φ ≫ v) :
    (freeP R).map φ ≫ (toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ u.hom) =
      (freeP R).map φ ≫ (toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ v.hom) := by
  have k := congrArg (fun w => toSheafify Scheme.etaleTopology ((freeP R).obj Q) ≫ w.hom) h
  exact (toSheafify_naturality_assoc Scheme.etaleTopology ((freeP R).map φ) u.hom).trans
    (k.trans (toSheafify_naturality_assoc Scheme.etaleTopology ((freeP R).map φ) v.hom).symm)

theorem gen_eq {P Q : PSh} (G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : Q ⟶ P) (a b : (freeP R).obj P ⟶ G)
    (h : (freeP R).map φ ≫ a = (freeP R).map φ ≫ b) (Y : Scheme.{0}) (y : Q.obj (op Y)) :
    a.app (op Y) (ModuleCat.freeMk (ULift.up (φ.app _ y))) = b.app (op Y) (ModuleCat.freeMk (ULift.up (φ.app _ y))) := by
  have e : ((freeP R).map φ).app (op Y) (ModuleCat.freeMk (ULift.up y)) =
      ModuleCat.freeMk (ULift.up (φ.app _ y)) := by
    first | rfl | exact ModuleCat.free_map_apply (R := ULift R) _ _
  have h3 := congrArg (fun w => w (ModuleCat.freeMk (ULift.up y)))
    (congrArg (fun t => ConcreteCategory.hom t) (NatTrans.congr_app h (op Y)))
  simp only [NatTrans.comp_app] at h3
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, e] at h3
  exact h3

theorem loc_eq {P : PSh} (G : Shv R) (a b : (freeP R).obj P ⟶ G.obj) (X : Scheme.{0}) (x : P.obj (op X))
    (S : Sieve X) (hS : S ∈ Scheme.etaleTopology X)
    (h : ∀ (Y : Scheme.{0}) (k : Y ⟶ X), S.arrows k →
      a.app (op Y) (ModuleCat.freeMk (ULift.up (P.map k.op x))) = b.app (op Y) (ModuleCat.freeMk (ULift.up (P.map k.op x)))) :
    a.app (op X) (ModuleCat.freeMk (ULift.up x)) = b.app (op X) (ModuleCat.freeMk (ULift.up x)) := by
  have key : ∀ (c : (freeP R).obj P ⟶ G.obj) (Y : Scheme.{0}) (k : Y ⟶ X),
      G.obj.map k.op (c.app (op X) (ModuleCat.freeMk (ULift.up x))) = c.app (op Y) (ModuleCat.freeMk (ULift.up (P.map k.op x))) := by
    intro c Y k
    have n1 := ConcreteCategory.congr_hom (c.naturality k.op) (ModuleCat.freeMk (ULift.up x))
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at n1
    rw [← n1]
    congr 1
    first | rfl | exact ModuleCat.free_map_apply (R := ULift R) _ _
  have hE := Presheaf.IsSheaf.hom_ext G.2 ⟨S, hS⟩
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift R) _ (a.app (op X) (ModuleCat.freeMk (ULift.up x)))))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift R) _ (b.app (op X) (ModuleCat.freeMk (ULift.up x))))) (by
      intro I
      ext1
      apply LinearMap.ext_ring
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.toSpanSingleton_apply, one_smul]
      erw [key a, key b]
      exact h _ _ I.hf)
  have := ConcreteCategory.congr_hom hE (1 : ULift R)
  simpa using this

theorem LeafCover2_of : LateralTheory.E.D2.LeafCover2 := by
  intro R _ U V E f g hf hg hc
  refine ⟨hf, hg, fun n => ⟨fun {G} u v huv => ?_⟩⟩
  induction n using Opposite.rec with | op n => ?_
  obtain ⟨m, rfl⟩ : ∃ m, n = SimplexCategory.mk m := ⟨n.len, rfl⟩
  have h1 : (free R).map (f.app _) ≫ u = (free R).map (f.app _) ≫ v := by
    simpa using congrArg (biprod.inl ≫ ·) huv
  have h2 : (free R).map (g.app _) ≫ u = (free R).map (g.app _) ≫ v := by
    simpa using congrArg (biprod.inr ≫ ·) huv
  have p1 := pre_eq R G _ u v h1
  have p2 := pre_eq R G _ u v h2
  apply Sheaf.hom_ext
  refine sheafify_hom_ext (P := (freeP R).obj (E.obj (op (SimplexCategory.mk m)))) _ _ _ G.2 ?_
  apply NatTrans.ext
  funext Y
  induction Y using Opposite.rec with | op X => ?_
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  obtain ⟨S, hS, hk⟩ := hc m X x
  refine loc_eq R G _ _ X x S hS ?_
  intro Y k hk'
  rcases hk Y k hk' with ⟨y, hy⟩ | ⟨y, hy⟩
  · rw [← hy]; exact gen_eq R _ _ _ _ p1 Y y
  · rw [← hy]; exact gen_eq R _ _ _ _ p2 Y y

end LateralTheory.E.LeafCover2Pf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.ZariskiLocalCech

def CechSigma : Prop := t_E3Cut.Hyp → ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens)
  {ι : Type} (V : ι → X.Opens), (∀ j, V j ≤ O) → O ≤ ⨆ j, V j →
  (∀ n : ℕ, Eqv R (sch.map (Limits.Sigma.map fun j : Fin (n + 1) → ι => g ∣_ (⨅ k, V (j k)))) F) →
  Eqv R (sch.map (g ∣_ O)) F

section
variable {R : Type} [CommRing R] {F : Shv R}

theorem eqv_comp {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (hf : Eqv R f F) (hg : Eqv R g F) :
    Eqv R (f ≫ g) F := fun n => by
  have h : ⇑(pull R (f ≫ g) F n) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  rw [h]; exact (hf n).comp (hg n)

theorem eqv_iso {E E' : Spc} (f : E ⟶ E') [IsIso f] : Eqv R f F := fun n => by
  have h1 : ∀ x, pull R (inv f) F n (pull R f F n x) = x := fun x => by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  have h2 : ∀ x, pull R f F n (pull R (inv f) F n x) = x := fun x => by
    rw [← pull_comp, IsIso.hom_inv_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem sigmaEqv (hC : t_E3Cut.Coprod) {ι : Type} {Y X : ι → Scheme.{0}} (f : ∀ j, Y j ⟶ X j)
    (hf : ∀ j, Eqv R (sch.map (f j)) F) : Eqv R (sch.map (Limits.Sigma.map f)) F := fun n => by
  have key : (fun (x : H R (sch.obj (∐ X)) F n) (j : ι) => pull R (sch.map (Sigma.ι Y j)) F n
      (pull R (sch.map (Limits.Sigma.map f)) F n x)) =
      Pi.map (fun j => pull R (sch.map (f j)) F n) ∘
        (fun (x : H R (sch.obj (∐ X)) F n) (j : ι) => pull R (sch.map (Sigma.ι X j)) F n x) := by
    funext x j
    simp only [Function.comp_apply, Pi.map_apply]
    rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, Sigma.ι_map]
  have hb := (Function.Bijective.piMap (fun j => hf j n)).comp (hC R F X n)
  rw [← key] at hb
  exact (Function.Bijective.of_comp_iff' (hC R F Y n) _).1 hb

theorem eqv_of_top {Y X : Scheme.{0}} (g : Y ⟶ X) (h : Eqv R (sch.map (g ∣_ ⊤)) F) : Eqv R (sch.map g) F := by
  have : IsIso (⊤ : X.Opens).ι := isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  have : IsIso (g ⁻¹ᵁ ⊤).ι := isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  have e : g = inv (g ⁻¹ᵁ ⊤).ι ≫ (g ∣_ ⊤) ≫ (⊤ : X.Opens).ι := by
    rw [morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  rw [e, Functor.map_comp, Functor.map_comp]
  exact eqv_comp (eqv_iso _) (eqv_comp h (eqv_iso _))

end

theorem inf_basicOpen {X : Scheme.{0}} {A : X.Opens} {κ : Type} [DecidableEq κ] (f : κ → Γ(X, A)) (s : Finset κ) :
    (s.inf fun k => X.basicOpen (f k)) ⊓ A = X.basicOpen (∏ k ∈ s, f k) := by
  induction s using Finset.induction_on with
  | empty => simp [X.basicOpen_of_isUnit isUnit_one]
  | insert a s ha ih =>
    rw [Finset.inf_insert, Finset.prod_insert ha, Scheme.basicOpen_mul, ← ih, inf_assoc]

theorem iInf_basicOpen {X : Scheme.{0}} {A : X.Opens} {n : ℕ} (f : Fin (n + 1) → Γ(X, A)) :
    (⨅ k, X.basicOpen (f k)) = X.basicOpen (∏ k, f k) := by
  rw [← inf_basicOpen f Finset.univ, Finset.inf_univ_eq_iInf]
  exact (inf_eq_left.2 ((iInf_le (fun k => X.basicOpen (f k)) 0).trans (X.basicOpen_le (f 0)))).symm

theorem ZarLocal_of (hCop : t_E3Cut.Coprod) (hCS : CechSigma) : t_E3Cut.ZarLocal := by
  intro hH R _ F Y X g hU
  choose U hxU hUe using hU
  have hA : ∀ x : X, ∃ A : X.Opens, IsAffineOpen A ∧ x ∈ A ∧ A ≤ U x := fun x => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (hxU x) (U x).2
    exact ⟨V, hV, hxV, hVU⟩
  choose A hAaff hxA hAU using hA
  have st1 : ∀ (x : X) (O : X.Opens), O ≤ A x → Eqv R (sch.map (g ∣_ O)) F := by
    intro x O hO
    refine hCS hH R F g O (ι := {f : Γ(X, A x) // X.basicOpen f ≤ O}) (fun f => X.basicOpen f.1) (fun f => f.2) ?_ ?_
    · intro y hy
      obtain ⟨f, hfO, hyf⟩ := (hAaff x).exists_basicOpen_le ⟨y, hy⟩ (hO hy)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hfO⟩, hyf⟩
    · intro n
      apply sigmaEqv hCop
      intro j
      have e := iInf_basicOpen (X := X) (A := A x) (fun k => (j k).1)
      apply hUe x
      · rw [e]; exact (hAaff x).basicOpen _
      · exact (iInf_le _ 0).trans ((X.basicOpen_le _).trans (hAU x))
  refine eqv_of_top g (hCS hH R F g ⊤ A (fun _ => le_top) ?_ ?_)
  · intro y _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, hxA y⟩
  · exact fun n => sigmaEqv hCop _ fun j => st1 (j 0) _ (iInf_le _ 0)

end LateralTheory.E.ZariskiLocalCech
end
end

section

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.IECompPf
open LateralTheory.E.t_E3Cut

def UnderFA : Prop := ∀ X : CommRingCat.{0}, IsFinitelyAccessibleCategory.{0} (Under X)

def EtSpreads : Prop := MorphismProperty.PreIndSpreads.{0} Et

theorem et_comp : Et.IsStableUnderComposition where
  comp_mem f g hf hg := by
    show (f ≫ g).hom.Etale
    rw [CommRingCat.hom_comp]
    exact RingHom.Etale.stableUnderComposition _ _ hf hg

theorem et_cobase : Et.IsStableUnderCobaseChange :=
  (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).2 RingHom.Etale.isStableUnderBaseChange

theorem et_fp : Et ≤ MorphismProperty.isFinitelyPresentable.{0} CommRingCat.{0} := fun _ _ f hf =>
  CommRingCat.isFinitelyPresentable_hom f (RingHom.Etale.iff_flat_and_formallyUnramified.1 hf).2.2

theorem IEComp_of (h1 : UnderFA) (h2 : EtSpreads) : IEComp := by
  intro A B C f g hf hg
  have : ∀ X : CommRingCat.{0}, IsFinitelyAccessibleCategory.{0} (Under X) := h1
  have : MorphismProperty.PreIndSpreads.{0} Et := h2
  have := et_comp
  have := et_cobase
  have := MorphismProperty.IsStableUnderComposition.ind_of_preIndSpreads (P := Et) et_fp
  exact this.comp_mem f g hf hg

end LateralTheory.E.IECompPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial GlobalTheory.EtC

namespace LateralTheory.E.PrimitiveRootLocalization

theorem cyc_cond {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    ∃ (p₁ p₂ : A[X]) (n : ℕ), derivative (cyclotomic q A) * p₁ + cyclotomic q A * p₂ = (1 : A[X]) ^ n := by
  obtain ⟨h, e1⟩ := cyclotomic.dvd_X_pow_sub_one q A
  obtain ⟨v, hv⟩ := hq.exists_left_inv
  have e2 := congrArg derivative e1
  rw [derivative_sub, derivative_X_pow, derivative_one, sub_zero, derivative_mul] at e2
  have e3 : C v * C (q : A) = 1 := by rw [← C_mul, hv, C_1]
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have e4 : X * X ^ (q - 1) = (X : A[X]) ^ q := by rw [← pow_succ']; congr 1; omega
  refine ⟨C v * X * h, C v * X * derivative h - h, 0, ?_⟩
  linear_combination (-(C v * X)) * e2 + (C v * C (q : A)) * e4 + X ^ q * e3 + e1

def cycPair {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) : StandardEtalePair A where
  f := cyclotomic q A
  monic_f := cyclotomic.monic q A
  g := 1
  cond := cyc_cond q hq

section
variable {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A))

theorem cycPair_hasMap_root : (cycPair q hq).HasMap (AdjoinRoot.root (cyclotomic q A)) := by
  refine ⟨?_, ?_⟩
  · simp [cycPair]
  · simp [cycPair]

theorem adjoinRoot_nontrivial [Nontrivial A] : Nontrivial (AdjoinRoot (cyclotomic q A)) := by
  refine Ideal.Quotient.nontrivial_iff.mpr ?_
  rw [Ne, Ideal.span_singleton_eq_top]
  intro hu
  have h1 := (cyclotomic.monic q A).isUnit_iff.mp hu
  have h2 := natDegree_cyclotomic q A
  rw [h1, natDegree_one] at h2
  exact (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne' h2.symm

theorem comap_surj : Function.Surjective (PrimeSpectrum.comap (algebraMap A (cycPair q hq).Ring)) := by
  by_cases hA : Nontrivial A
  · let ψ : (cycPair q hq).Ring →ₐ[A] AdjoinRoot (cyclotomic q A) := (cycPair q hq).lift _ (cycPair_hasMap_root q hq)
    have := (cyclotomic.monic q A).free_adjoinRoot
    have := adjoinRoot_nontrivial (A := A) q
    have hs := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := AdjoinRoot (cyclotomic q A))
    have e : algebraMap A (AdjoinRoot (cyclotomic q A)) = (ψ : (cycPair q hq).Ring →+* _).comp (algebraMap A (cycPair q hq).Ring) := by
      ext a; simp
    intro x
    obtain ⟨y, hy⟩ := hs x
    refine ⟨PrimeSpectrum.comap (ψ : (cycPair q hq).Ring →+* _) y, ?_⟩
    rw [← hy, e]
    rfl
  · intro x
    rw [not_nontrivial_iff_subsingleton] at hA
    exact absurd (Subsingleton.elim _ _) x.isPrime.ne_top

def primRing : Prim q (cycPair q hq).Ring :=
  ⟨(cycPair q hq).X, by simpa using hq.map (algebraMap A (cycPair q hq).Ring), by
    have h := (cycPair q hq).hasMap_X.1
    change aeval (cycPair q hq).X (cyclotomic q A) = 0 at h
    rw [← map_cyclotomic q (algebraMap ℤ A), aeval_map_algebraMap] at h
    exact h⟩

end

theorem LeafPrimLoc_of : LateralTheory.E.LeafOneLocPf.LeafPrimLoc := by
  intro q _ U hq
  let P := cycPair (A := Γ(U, ⊤)) q hq
  let f : Spec (CommRingCat.of P.Ring) ⟶ Spec Γ(U, ⊤) := Spec.map (CommRingCat.ofHom (algebraMap Γ(U, ⊤) P.Ring))
  have hfe : Etale f := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  have hfs : Surjective f := ⟨comap_surj q hq⟩
  have hge : Etale (pullback.fst U.toSpecΓ f) := inferInstance
  have hgs : Surjective (pullback.fst U.toSpecΓ f) := inferInstance
  let S : Sieve U :=
    { arrows := fun V _ => Nonempty (Prim q Γ(V, ⊤))
      downward_closed := fun {V W} g hg h => hg.elim fun ζ => ⟨Prim.map h.appTop.hom ζ⟩ }
  refine ⟨S, ?_, fun V g hg => hg⟩
  refine GrothendieckTopology.superset_covering _ ?_ (Precoverage.generate_mem_toGrothendieck
    ((Scheme.singleton_mem_precoverage_iff _ _).mpr ⟨hgs.surj, hge⟩))
  rintro V _ ⟨W, h, k, ⟨⟩, rfl⟩
  exact ⟨Prim.map ((Scheme.ΓSpecIso (CommRingCat.of P.Ring)).inv ≫ (h ≫ pullback.snd _ _).appTop).hom (primRing q hq)⟩

end LateralTheory.E.PrimitiveRootLocalization
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitSecPf

def LeafTwGenIndep : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)), twGen 0 ζ = twGen 0 ξ

theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map (Scheme.Γ.map g.op).hom) := by
  unfold twGen ofRings.sec
  have h := congrArg (fun t => t.hom (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
  simp only [ModuleCat.hom_comp] at h
  refine h.symm.trans (congrArg (fun y => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom y) ?_)
  exact congrArg (Submodule.Quotient.mk (p := twRel q i Γ(V, ⊤))) (Finsupp.mapDomain_single (f := Prim.map (Scheme.Γ.map g.op).hom))

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (k : V ⟶ U) (x : Sec F U) :
    Sec.res h (Sec.res k x) = Sec.res (h ≫ k) x := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.res (𝟙 U) x = x := by
  show (F.obj.map (𝟙 U).op).hom x = x
  rw [op_id, F.obj.map_id]
  rfl

theorem tw_isSheafFor (q : ℕ) (U : Scheme.{0}) (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U) :
    Presieve.IsSheafFor ((tw q 0).obj ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) S.arrows := by
  have hF := (Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology (tw q 0).obj
    (forget (ModuleCat.{1} (ULift.{1} (ZMod q))))).1 (tw q 0).property
  rw [isSheaf_iff_isSheaf_of_type] at hF
  exact hF S hS

section Glue

def cov (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : Sieve U := Classical.choose (hP q U hU)

theorem cov_mem (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : cov hP q U hU ∈ Scheme.etaleTopology U :=
  (Classical.choose_spec (hP q U hU)).1

theorem cov_prim (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) (V : Scheme.{0}) (g : V ⟶ U) (hg : (cov hP q U hU).arrows g) :
    Nonempty (Prim q Γ(V, ⊤)) :=
  (Classical.choose_spec (hP q U hU)).2 V g hg

def fam (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) :
    Presieve.FamilyOfElements ((tw q 0).obj ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) (cov hP q U hU).arrows :=
  fun V g hg => twGen 0 (Classical.choice (cov_prim hP q U hU V g hg))

theorem fam_compat (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : (fam hP q U hU).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro Y Z f g hf
  change _ = Sec.res g (twGen 0 _)
  rw [twGen_res]
  exact hI q Z _ _

def one (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : Sec (tw q 0) U :=
  (tw_isSheafFor q U _ (cov_mem hP q U hU)).amalgamate (fam hP q U hU) (fam_compat hP hI q U hU)

theorem one_char (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) (W : Scheme.{0}) (k : W ⟶ U) (ζ : Prim q Γ(W, ⊤)) :
    Sec.res k (one hP hI q U hU) = twGen 0 ζ := by
  refine LateralTheory.E.LeafOneSpecPf.sec_sep (ZMod q) (tw q 0) W ((cov hP q U hU).pullback k)
    (Scheme.etaleTopology.pullback_stable k (cov_mem hP q U hU)) _ _ fun V h hh => ?_
  rw [res_comp, twGen_res]
  have hv := (tw_isSheafFor q U _ (cov_mem hP q U hU)).valid_glue (fam_compat hP hI q U hU) (h ≫ k) hh
  refine hv.trans ?_
  exact hI q V _ _

end Glue

theorem LeafUnitSec_of (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) :
    LateralTheory.E.LeafOneExistsPf.LeafUnitSec := by
  intro q _
  refine ⟨one hP hI q, fun V U g hU hV => ?_, fun U hU ζ => ?_⟩
  · refine LateralTheory.E.LeafOneSpecPf.sec_sep (ZMod q) (tw q 0) V (cov hP q V hV) (cov_mem hP q V hV) _ _ fun W h hh => ?_
    obtain ⟨ζ⟩ := cov_prim hP q V hV W h hh
    rw [res_comp, one_char hP hI q U hU W _ ζ, one_char hP hI q V hV W h ζ]
  · rw [← one_char hP hI q U hU U (𝟙 U) ζ, res_id]

end LateralTheory.E.LeafUnitSecPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.AICAcycPf

theorem acyc_of_iso (q : ℕ) {X Y : Scheme.{0}} (e : X ≅ Y) (h : Acyc q (sch.obj Y)) : Acyc q (sch.obj X) := by
  intro n i hn
  have := h n i hn
  constructor
  intro a b
  have key : ∀ a : Ht q (sch.obj X) n i,
      a = pull _ (sch.map e.hom) _ n (pull _ (sch.map e.inv) _ n a) := by
    intro a
    rw [← pull_comp, ← CategoryTheory.Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [key a, key b, Subsingleton.elim (pull _ (sch.map e.inv) _ n a) (pull _ (sch.map e.inv) _ n b)]

theorem aff (hB5 : B5) (q : ℕ) (Z : Scheme.{0}) [IsAffine Z] (hZ : AICSch Z) (hq : IsUnit (q : Γ(Z, ⊤))) :
    Acyc q (sch.obj Z) := by
  have : IsIntegral Z := hZ.1
  have hA : AIC Γ(Z, ⊤) := hZ.2 ⊤ (isAffineOpen_top Z) ⟨Nonempty.some inferInstance, by simp⟩
  have h5 := hB5 q Γ(Z, ⊤) hA hq
  exact acyc_of_iso q Z.isoSpec h5

def Step : Prop := Hyp → MV → HZero → ∀ (q : ℕ) {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f]
  [IsOpenImmersion g], Set.range f ∪ Set.range g = Set.univ → AICSch X → AICSch U → AICSch V → IsUnit (q : Γ(X, ⊤)) →
  Acyc q (sch.obj U) → Acyc q (sch.obj V) → (Nonempty ↥(pullback f g : Scheme.{0}) → Acyc q (sch.obj (pullback f g))) → Acyc q (sch.obj X)

def Cov : Prop := ∀ (q : ℕ) (P : Scheme.{0} → Prop), (∀ {X Y : Scheme.{0}}, (X ≅ Y) → P Y → P X) →
  (∀ Z : Scheme.{0}, IsAffine Z → AICSch Z → IsUnit (q : Γ(Z, ⊤)) → P Z) →
  (∀ {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g],
    Set.range f ∪ Set.range g = Set.univ → AICSch X → AICSch U → AICSch V → IsUnit (q : Γ(X, ⊤)) →
    P U → P V → (Nonempty ↥(pullback f g : Scheme.{0}) → P (pullback f g)) → P X) →
  ∀ (Z : Scheme.{0}) [CompactSpace Z] [QuasiSeparatedSpace Z], AICSch Z → IsUnit (q : Γ(Z, ⊤)) → P Z

theorem AICAcyc_of (hZ : HZero) (hMV : MV) (hStep : Step) (hCov : Cov) : AICAcyc := by
  intro hyp q Z _ _ hZs hq
  refine hCov q (fun W => Acyc q (sch.obj W)) ?_ ?_ ?_ Z hZs hq
  · intro X Y e h
    exact acyc_of_iso q e h
  · intro W hA hW hWq
    exact aff hyp.b5 q W hW hWq
  · intro U V X f g _ _ hc hX hU hV hq' hPU hPV hPW
    exact hStep hyp hMV hZ q f g hc hX hU hV hq' hPU hPV hPW

end LateralTheory.E.AICAcycPf
end
end
