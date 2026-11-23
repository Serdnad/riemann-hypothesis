module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle408
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.FlatLoc

theorem zmod_dvd_of_mul_eq_zero (Q q e : ℕ) [NeZero Q] (hQ : q * e = Q) (r : ZMod Q)
    (hr : (e : ZMod Q) * r = 0) : ∃ s : ZMod Q, r = (q : ZMod Q) * s := by
  have he : e ≠ 0 := by
    rintro rfl; exact NeZero.ne Q (by rw [← hQ, mul_zero])
  have h1 : ((e * r.val : ℕ) : ZMod Q) = 0 := by push_cast; rw [ZMod.natCast_zmod_val]; exact hr
  rw [ZMod.natCast_eq_zero_iff] at h1
  have h2 : e * q ∣ e * r.val := by rw [mul_comm e q, hQ]; exact h1
  obtain ⟨t, ht⟩ := Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero he) h2
  refine ⟨t, ?_⟩
  rw [← ZMod.natCast_zmod_val r, ht]; push_cast; ring

theorem flat_dvd (Q q e : ℕ) [NeZero Q] (hQ : q * e = Q) (N : Type*) [AddCommGroup N]
    [Module (ULift.{1} (ZMod Q)) N] [Module.Flat (ULift.{1} (ZMod Q)) N] (n : N) (hn : e • n = 0) :
    ∃ n' : N, n = q • n' := by
  have hs : ∑ _i : Unit, (e : ULift.{1} (ZMod Q)) • n = 0 := by
    simpa [Nat.cast_smul_eq_nsmul] using hn
  obtain ⟨k, a, y, hx, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
    (f := fun _ : Unit => (e : ULift.{1} (ZMod Q))) (x := fun _ : Unit => n) hs
  have hb : ∀ j, ∃ s : ZMod Q, (a () j).down = (q : ZMod Q) * s := fun j => by
    refine zmod_dvd_of_mul_eq_zero Q q e hQ _ ?_
    have := congrArg ULift.down (ha j)
    simpa using this
  choose s hs using hb
  refine ⟨∑ j, (ULift.up (s j) : ULift.{1} (ZMod Q)) • y j, ?_⟩
  rw [show n = ∑ j, a () j • y j from hx (), Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod Q)), smul_smul]
  congr 1
  apply ULift.ext
  simp [hs j]

theorem flat_loc : ∀ (Q q e : ℕ) [NeZero Q], q * e = Q → ∀ (M : Shv (ZMod Q)), FlatS M → ∀ (U : Scheme.{0}) (x : Sec M U),
    e • x = 0 → Loc U fun V g => ∃ y : Sec M V, Sec.res g x = q • y := by
  intro Q q e _ hQ M hM U x hx
  obtain ⟨P, φ, hsurj, hinj, hflat⟩ := hM
  have hnat : ∀ {W V : Scheme.{0}} (k : W ⟶ V) (p : P.obj (op V)),
      (φ.app (op W)).hom ((P.map k.op).hom p) = Sec.res k ((φ.app (op V)).hom p) := fun k p => by
    have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.naturality k.op)) p
    simpa using this
  have hres : ∀ {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (s : Sec M U),
      Sec.res k (Sec.res g s) = Sec.res (k ≫ g) s := by
    intro W V U k g s
    simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  refine loc_trans U _ (loc_mono U _ _ (hsurj U x) fun V g hpg => ?_)
  obtain ⟨p, hp⟩ := hpg
  have hep : (φ.app (op V)).hom (e • p) = 0 := by
    rw [map_nsmul, hp]
    show e • (M.obj.map g.op).hom x = 0
    rw [← map_nsmul, hx, map_zero]
  refine loc_mono V _ _ (hinj V (e • p) hep) fun W k hk => ?_
  by_cases hW : Nonempty W
  · haveI := hflat W hW
    obtain ⟨p', hp'⟩ := flat_dvd Q q e hQ _ ((P.map k.op).hom p) (by rw [← map_nsmul]; exact hk)
    refine ⟨(φ.app (op W)).hom p', ?_⟩
    rw [← hres, ← hp, ← hnat, hp', map_nsmul]
  · haveI : IsEmpty W := not_nonempty_iff.mp hW
    refine ⟨0, ?_⟩
    rw [smul_zero]
    exact (sec_ext_glue (ZMod Q) M W).1 _ _ (loc_of_isEmpty W _)

end GlobalTheory.EtC.FlatLoc
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

namespace DescLoc

variable {S : Type} [CommRing S] {P Q : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}} (φ : P ⟶ Q)

theorem res_res {M : Shv S} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec M U) :
    Sec.res k (Sec.res g a) = Sec.res (k ≫ g) a := by
  simp [Sec.res]

theorem res_add {M : Shv S} {V U : Scheme.{0}} (g : V ⟶ U) (a a' : Sec M U) :
    Sec.res g (a + a') = Sec.res g a + Sec.res g a' := map_add _ _ _

theorem pmap_comp (P : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}) {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (x : P.obj (op U)) : (P.map k.op).hom ((P.map g.op).hom x) = (P.map (k ≫ g).op).hom x := by
  simp

theorem nat_apply {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (φ.app (op V)).hom ((P.map g.op).hom x) = (Q.map g.op).hom ((φ.app (op U)).hom x) := by
  have := congrArg (fun f => f.hom x) (φ.naturality g.op)
  simpa using this

section Main
variable {S : Type} [CommRing S] {P Q : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}} (φ : P ⟶ Q) (M : Shv S)
  (b : ∀ U : Scheme.{0}, P.obj (op U) →+ Sec M U)
  (hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V ((P.map g.op).hom x))

theorem ext_loc {U : Scheme.{0}} (a a' : Sec M U) (h : Loc U fun _ g => Sec.res g a = Sec.res g a') : a = a' :=
  (sec_ext_glue S M U).1 a a' h


include hb in
theorem key (h2 : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)
    {V : Scheme.{0}} (x x' : P.obj (op V)) (hx : (φ.app (op V)).hom x = (φ.app (op V)).hom x') : b V x = b V x' := by
  obtain ⟨T, hT, hz⟩ := h2 V (x - x') (by rw [map_sub, hx, sub_self])
  refine ext_loc M _ _ ⟨T, hT, fun W k hk => ?_⟩
  dsimp only
  rw [hb, hb]
  have := hz W k hk
  dsimp only at this
  rw [map_sub, sub_eq_zero] at this
  rw [this]

def Ch (U : Scheme.{0}) (y : Q.obj (op U)) (a : Sec M U) : Prop :=
  ∀ (V : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op V)), (φ.app (op V)).hom x = (Q.map g.op).hom y → Sec.res g a = b V x

theorem ch_unique (h1 : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
    {U : Scheme.{0}} (y : Q.obj (op U)) (a a' : Sec M U) (ha : Ch φ M b U y a) (ha' : Ch φ M b U y a') : a = a' := by
  obtain ⟨T, hT, hl⟩ := h1 U y
  refine ext_loc M _ _ ⟨T, hT, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hl V g hg
  rw [ha V g x hx, ha' V g x hx]

include hb in
theorem ch_exists (h1 : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
    (h2 : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)
    (U : Scheme.{0}) (y : Q.obj (op U)) : ∃ a, Ch φ M b U y a := by
  obtain ⟨T, hT, hl⟩ := h1 U y
  let s : ∀ (V : Scheme.{0}) (g : V ⟶ U), T.arrows g → Sec M V := fun V g hg => b V (hl V g hg).choose
  have hs : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : T.arrows g),
      Sec.res k (s V g hg) = s W (k ≫ g) (T.downward_closed hg k) := by
    intro V W g k hg
    simp only [s]
    rw [hb]
    apply key φ M b hb h2
    rw [nat_apply, (hl V g hg).choose_spec, (hl W (k ≫ g) (T.downward_closed hg k)).choose_spec, pmap_comp]
  obtain ⟨a, ha⟩ := (sec_ext_glue S M U).2 T hT s hs
  refine ⟨a, fun V g x hx => ?_⟩
  refine ext_loc M _ _ ⟨T.pullback g, Scheme.etaleTopology.pullback_stable g hT, fun W k hk => ?_⟩
  dsimp only
  rw [res_res, ha W (k ≫ g) hk, hb]
  simp only [s]
  apply key φ M b hb h2
  rw [nat_apply, hx, (hl W (k ≫ g) hk).choose_spec, pmap_comp]

end Main

section Main2
variable {S : Type} [CommRing S] {P Q : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}} (φ : P ⟶ Q) (M : Shv S)
  (b : ∀ U : Scheme.{0}, P.obj (op U) →+ Sec M U)
  (hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V ((P.map g.op).hom x))
  (h1 : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
  (h2 : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)

include hb h1 h2 in
theorem ch_add {U : Scheme.{0}} (y y' : Q.obj (op U)) (a a' : Sec M U) (ha : Ch φ M b U y a) (ha' : Ch φ M b U y' a') :
    Ch φ M b U (y + y') (a + a') := by
  intro V g x hx
  obtain ⟨T1, hT1, hl1⟩ := h1 V ((Q.map g.op).hom y)
  obtain ⟨T2, hT2, hl2⟩ := h1 V ((Q.map g.op).hom y')
  refine ext_loc M _ _ ⟨T1 ⊓ T2, Scheme.etaleTopology.intersection_covering hT1 hT2, fun W k hk => ?_⟩
  obtain ⟨x1, e1⟩ := hl1 W k hk.1
  obtain ⟨x2, e2⟩ := hl2 W k hk.2
  rw [pmap_comp] at e1 e2
  rw [res_res, res_add, ha W (k ≫ g) x1 e1, ha' W (k ≫ g) x2 e2, hb, ← map_add (f := _)]
  apply key φ M b hb h2
  rw [nat_apply, hx, pmap_comp]
  simp only [map_add (f := _), e1, e2]

theorem ch_res {U V : Scheme.{0}} (h : V ⟶ U) (y : Q.obj (op U)) (a : Sec M U) (ha : Ch φ M b U y a) :
    Ch φ M b V ((Q.map h.op).hom y) (Sec.res h a) := by
  intro W k x hx
  rw [res_res]
  exact ha W (k ≫ h) x (by rw [hx, pmap_comp])

include hb h2 in
theorem ch_base {U : Scheme.{0}} (x : P.obj (op U)) : Ch φ M b U ((φ.app (op U)).hom x) (b U x) := by
  intro V g x' hx
  rw [hb]
  apply key φ M b hb h2
  rw [nat_apply, hx]

end Main2
end DescLoc

open DescLoc in
theorem desc_loc : ∀ (S : Type) [CommRing S] (P Q : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ (M : Shv S) (b : ∀ U : Scheme.{0}, P.obj (op U) →+ Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V ((P.map g.op).hom x)) → ∃ c : ∀ U : Scheme.{0}, Q.obj (op U) →+ Sec M U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (c U y) = c V ((Q.map g.op).hom y)) ∧ ∀ U x, c U ((φ.app (op U)).hom x) = b U x := by
  intro S _ P Q φ h1 h2 M b hb
  have hex := ch_exists φ M b hb h1 h2
  let c0 : ∀ U : Scheme.{0}, Q.obj (op U) → Sec M U := fun U y => (hex U y).choose
  have hc0 : ∀ U y, Ch φ M b U y (c0 U y) := fun U y => (hex U y).choose_spec
  let c : ∀ U : Scheme.{0}, Q.obj (op U) →+ Sec M U := fun U =>
    AddMonoidHom.mk' (c0 U) (fun y y' => ch_unique φ M b h1 (y + y') _ _ (hc0 U (y + y'))
      (ch_add φ M b hb h1 h2 y y' _ _ (hc0 U y) (hc0 U y')))
  refine ⟨c, fun V U g y => ?_, fun U x => ?_⟩
  · exact ch_unique φ M b h1 _ _ _ (ch_res φ M b g y _ (hc0 U y)) (hc0 V _)
  · exact ch_unique φ M b h1 _ _ _ (hc0 U _) (ch_base φ M b hb h2 x)
end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleSheafSections_ext_and_glue : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg := by
  first | exact @GlobalTheory.EtC.sec_ext_glue | exact GlobalTheory.EtC.sec_ext_glue | (intros; apply GlobalTheory.EtC.sec_ext_glue <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleSheafSections_glue_of_locally_unique : ∀ {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0}) (A : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U → Prop),
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : U ⟶ X) (s : Sec F U), A U x s → A V (g ≫ x) (Sec.res g s)) →
    (∀ (U : Scheme.{0}) (x : U ⟶ X) (s t : Sec F U), A U x s → A U x t → s = t) →
    (∀ (U : Scheme.{0}) (x : U ⟶ X), Loc U fun V g => ∃ s, A V (g ≫ x) s) →
    ∃ e : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : U ⟶ X), Sec.res g (e U x) = e V (g ≫ x)) ∧
      ∀ (U : Scheme.{0}) (x : U ⟶ X) (s : Sec F U), A U x s → e U x = s := by
  first | exact @GlobalTheory.EtC.secGlue_of_loc | exact GlobalTheory.EtC.secGlue_of_loc | (intros; apply GlobalTheory.EtC.secGlue_of_loc <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.standardSimplexFacePairs_acyclic_positive_degree : ∀ N k (c : Pr N →₀ ℤ), Pr.Deg (k + 1) c → Pr.d N c = 0 → ∃ e, Pr.Deg (k + 2) e ∧ Pr.d N e = c := by
  first | (exact @GlobalTheory.PrAcyc.pr_acyclic) | (exact GlobalTheory.PrAcyc.pr_acyclic) | (intros; apply GlobalTheory.PrAcyc.pr_acyclic  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem smooth_surjective_loc_sections : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [Smooth f] [Surjective f] (U : Scheme.{0}) (y : U ⟶ X), Loc U fun V g => ∃ x : V ⟶ Y, x ≫ f = g ≫ y := by
  intro Y X f _ _ U y
  refine (loc_iff_etale_affine_points U (fun V g => ∃ x : V ⟶ Y, x ≫ f = g ≫ y) ?_).2 ?_
  · rintro V W g k ⟨x, hx⟩
    exact ⟨k ≫ x, by simp [Category.assoc, hx]⟩
  · intro u
    obtain ⟨V, s, hE, hu⟩ := GlobalTheory.T.exists_etale_quasiSection_of_smooth_scheme_hom f (y u) (f.surjective (y u))
    obtain ⟨v, hv⟩ := hu
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback v u hv
    let W := pullback (s ≫ f) y
    obtain ⟨z, hz⟩ := W.affineCover.covers w
    haveI := hE
    have hEt : Etale (pullback.snd (s ≫ f) y) := inferInstance
    refine ⟨_, W.affineCover.f (W.affineCover.idx w) ≫ pullback.snd (s ≫ f) y, inferInstance, inferInstance, ⟨z, ?_⟩, ?_⟩
    · simp [hz, hw2]
    · refine ⟨W.affineCover.f (W.affineCover.idx w) ≫ pullback.fst (s ≫ f) y ≫ s, ?_⟩
      simp only [Category.assoc]
      rw [show pullback.fst (s ≫ f) y ≫ s ≫ f = pullback.snd (s ≫ f) y ≫ y from pullback.condition]

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cocycle_eq_chainMap_shift_compat_classes : ∀ (R : Type) [CommRing R] (L C : Cx R) (d : ℤ) (ψ : Cocycle L C d), ∃ (L' : Cx R) (g : L' ⟶ C), (∀ m, L.IsStrictlyGE m → L'.IsStrictlyGE (m + d)) ∧ ((∀ n, CategoryTheory.Injective (L.X n)) → ∀ n, CategoryTheory.Injective (L'.X n)) ∧ ∀ (K : Cx R) (n : ℤ), ∃ e : CohomologyClass K L (n - d) ≃ CohomologyClass K L' n, ∀ a, cpush K g n (e a) = cpost K ψ (n - d) n (by omega) a := by
  first | (exact @GlobalTheory.EtC.cocycle_as_chainMap_of_shift) | (exact GlobalTheory.EtC.cocycle_as_chainMap_of_shift) | (intros; apply GlobalTheory.EtC.cocycle_as_chainMap_of_shift  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite : ∀ {E : Spc} {U : Scheme.{0}} {N : ℕ} (x : Sx E N U), (∀ (j l j' l' : ℕ) (h : j + l ≤ N) (h' : j' + l' ≤ l), (x.sub j l h).sub j' l' h' = x.sub (j + j') l' (by omega)) ∧ x.sub 0 N (by omega) = x ∧ (∀ (j l : ℕ) (h : j + l ≤ N), (∀ {V : Scheme.{0}} (g : V ⟶ U), (x.res g).sub j l h = (x.sub j l h).res g) ∧ (∀ {E' : Spc} (f : E ⟶ E'), (x.map f).sub j l h = (x.sub j l h).map f) ∧ x.sub j l h = x.along (SimplexCategory.subinterval j l h)) ∧ ∀ {p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p), (x.along a).along b = x.along (b ≫ a) := by
  first | (exact @GlobalTheory.EtC.SubSub.main) | (exact GlobalTheory.EtC.SubSub.main) | (intros; apply GlobalTheory.EtC.SubSub.main  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact : ∀ (R : Type) [CommRing R] (K : Cx R) {I J : Cx R} (f : I ⟶ J) (n : ℤ), Function.Exact (cpush K f n) (cpush K (mappingCone.inr f) n) ∧ Function.Exact (cpush K (mappingCone.inr f) n) (cpost K (mappingCone.fst f) n (n + 1) rfl) ∧ Function.Exact (cpost K (mappingCone.fst f) n (n + 1) rfl) (cpush K f (n + 1)) := by
  first | (exact @GlobalTheory.EtC.coneSeqTgt_exact) | (exact GlobalTheory.EtC.coneSeqTgt_exact) | (intros; apply GlobalTheory.EtC.coneSeqTgt_exact  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isTensor_of_compat_isIso_target : ∀ (R : Type) [CommRing R] {I J K K' : Cx R} (τ : Pair I J K) (ν : Pair I J K') (u : K ⟶ K'), IsIso u → τ.Compat ν (𝟙 I) (𝟙 J) u → τ.IsTensor → ν.IsTensor := by
  first | (exact @GlobalTheory.EtC.Pair.isTensor_of_compat_isIso) | (exact GlobalTheory.EtC.Pair.isTensor_of_compat_isIso) | (intros; apply GlobalTheory.EtC.Pair.isTensor_of_compat_isIso  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_cocycle_of_map_to_degreeOne_term : ∀ (C : Shv ℤ) (I : Cx ℤ) (ψ : C ⟶ I.X 1), ψ ≫ I.d 1 2 = 0 → ∃ w : Cocycle (sgl C) I 1, sglι C ≫ w.1.v 0 1 (zero_add 1) = ψ := by
  first | (exact @GlobalTheory.EtC.exists_cocycle_of_map_to_X_one) | (exact GlobalTheory.EtC.exists_cocycle_of_map_to_X_one) | (intros; apply GlobalTheory.EtC.exists_cocycle_of_map_to_X_one  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_isFlip_sheafComplexPairing : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), ∃ ν : Pair J I K, μ.IsFlip ν ∧ ν.IsFlip μ ∧ (μ.IsTensor → ν.IsTensor) := by
  first | exact @GlobalTheory.EtC.Pair.exists_isFlip | exact GlobalTheory.EtC.Pair.exists_isFlip | (intros; apply GlobalTheory.EtC.Pair.exists_isFlip <;> assumption)
end
