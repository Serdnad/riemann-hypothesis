module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle598
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Ext
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.LesChar

variable {R' : Type} [CommRing R']

theorem resAug_comm (R : Type) [CommRing R] {F G : Shv R} (φ : F ⟶ G) :
    (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G = resAug F ≫ resMap R φ :=
  (InjectiveResolution.Hom.ι'_comp_hom'
    (⟨InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F),
      InjectiveResolution.desc_commutes_zero φ _ _⟩ : InjectiveResolution.Hom _ _ φ)).symm

theorem mk_ofHom_eq {K L : Cx R'} {f g : K ⟶ L} (ho : Homotopy f g) :
    CohomologyClass.mk (Cocycle.ofHom f) = CohomologyClass.mk (Cocycle.ofHom g) := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  exact ⟨-1, by omega, Cochain.ofHomotopy ho, by ext; simp [δ_ofHomotopy]⟩

theorem exact_part : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R))
    (e : HomotopyEquiv (mappingCone (resMap R S.f)) (res R S.X₃)),
    Homotopy (mappingCone.inr (resMap R S.f) ≫ e.hom) (resMap R S.g) → ∀ (K : Cx R) (n : ℤ),
    Function.Exact (HK.post R K S.f n) (HK.post R K S.g n) ∧
    Function.Exact (HK.post R K S.g n)
      (HK.ext R K (zcomp (Cocycle.ofHom e.inv) (mappingCone.fst (resMap R S.f)) (zero_add 1)) n (n + 1) rfl) ∧
    Function.Exact (HK.ext R K (zcomp (Cocycle.ofHom e.inv) (mappingCone.fst (resMap R S.f)) (zero_add 1)) n (n + 1) rfl)
      (HK.post R K S.f (n + 1)) := by
  intro R _ S e h K n
  obtain ⟨hid, -, hcomp, -, hhtp⟩ := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R
  obtain ⟨-, -, hass⟩ := GlobalTheory.T.cocycleCompHomComplex_assoc_on_cohomology_classes R (add_zero n) (zero_add 1) (rfl : n + 1 = n + 1) (rfl : n + 1 = n + 1)
  obtain ⟨x1, x2, x3⟩ := GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact R K (resMap R S.f) n
  have hg : ∀ x, HK.post R K S.g n x = cpush K e.hom n (cpush K (mappingCone.inr (resMap R S.f)) n x) := by
    intro x
    rw [← hcomp]
    exact (congrFun (congrArg DFunLike.coe ((hhtp _ _ ⟨h⟩ K n).2)) x).symm
  have hz : ∀ x, HK.ext R K (zcomp (Cocycle.ofHom e.inv) (mappingCone.fst (resMap R S.f)) (zero_add 1)) n (n + 1) rfl x =
      cpost K (mappingCone.fst (resMap R S.f)) n (n + 1) rfl (cpush K e.inv n x) := fun x => hass _ _ _
  have hie : ∀ x, cpush K e.inv n (cpush K e.hom n x) = x := by
    intro x
    rw [← hcomp, (hhtp _ _ ⟨e.homotopyHomInvId⟩ K n).2]
    exact (hid K _ n x).2
  have hei : ∀ x, cpush K e.hom n (cpush K e.inv n x) = x := by
    intro x
    rw [← hcomp, (hhtp _ _ ⟨e.homotopyInvHomId⟩ K n).2]
    exact (hid K _ n x).2
  refine ⟨fun y => ?_, fun y => ?_, fun y => ?_⟩
  · rw [hg, ← map_zero (cpush K e.hom n)]
    constructor
    · intro hy
      exact (x1 _).1 (by rw [← hie (cpush K (mappingCone.inr (resMap R S.f)) n y), hy, hie])
    · intro hy
      rw [(x1 _).2 hy]
  · rw [hz]
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := (x2 _).1 hy
      exact ⟨x, by rw [hg, hx, hei]⟩
    · rintro ⟨x, rfl⟩
      rw [hg, hie]
      exact (x2 _).2 ⟨x, rfl⟩
  · constructor
    · intro hy
      obtain ⟨x, hx⟩ := (x3 _).1 hy
      exact ⟨cpush K e.hom n x, by rw [hz, hie, hx]⟩
    · rintro ⟨x, rfl⟩
      rw [hz]
      exact (x3 _).2 ⟨_, rfl⟩

theorem zcomp_ofHom_ofHom {K L M N : Cx R'} {n : ℤ} (f : K ⟶ L) (g : L ⟶ M) (b : Cocycle M N n) :
    zcomp (Cocycle.ofHom f) (zcomp (Cocycle.ofHom g) b (zero_add n)) (zero_add n) =
      zcomp (Cocycle.ofHom (f ≫ g)) b (zero_add n) := by
  ext1
  change (Cochain.ofHom f).comp ((Cochain.ofHom g).comp b.1 (zero_add n)) (zero_add n) =
    (Cochain.ofHom (f ≫ g)).comp b.1 (zero_add n)
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem assemble {D C I₃ I₁ X : Cx R'} (q : D ⟶ X) (a : X ⟶ I₃) (m : D ⟶ C) (eh : C ⟶ I₃) (ei : I₃ ⟶ C)
    (fst : Cocycle C I₁ 1) (w : Cocycle X I₁ 1) (hh : Homotopy (eh ≫ ei) (𝟙 C))
    (cmp : CohomologyClass.mk (Cocycle.ofHom (q ≫ a)) = CohomologyClass.mk (Cocycle.ofHom (m ≫ eh)))
    (key : CohomologyClass.mk (zcomp (Cocycle.ofHom m) fst (zero_add 1)) =
      CohomologyClass.mk (zcomp (Cocycle.ofHom q) w (zero_add 1))) :
    cpull q I₁ 1 (CohomologyClass.mk (zcomp (Cocycle.ofHom a) (zcomp (Cocycle.ofHom ei) fst (zero_add 1)) (zero_add 1))) =
      cpull q I₁ 1 (CohomologyClass.mk w) := by
  have h1 : CohomologyClass.mk (Cocycle.ofHom ((m ≫ eh) ≫ ei)) = CohomologyClass.mk (Cocycle.ofHom m) :=
    mk_ofHom_eq (((Homotopy.ofEq (Category.assoc _ _ _)).trans (hh.compLeft m)).trans
      (Homotopy.ofEq (Category.comp_id m)))
  change CohomologyClass.mk (zcomp (Cocycle.ofHom q) _ (zero_add 1)) = CohomologyClass.mk (zcomp (Cocycle.ofHom q) w (zero_add 1))
  rw [zcomp_ofHom_ofHom, ← key, ← cpost_mk, cmp, cpost_mk, zcomp_ofHom_ofHom, ← cpost_mk, h1, cpost_mk]

theorem exists_connecting_cocycle : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
  ∃ z : Cocycle (res R S.X₃) (res R S.X₁) 1,
    (∀ (K : Cx R) (n : ℤ),
      Function.Exact (HK.post R K S.f n) (HK.post R K S.g n) ∧
      Function.Exact (HK.post R K S.g n) (HK.ext R K z n (n + 1) rfl) ∧
      Function.Exact (HK.ext R K z n (n + 1) rfl) (HK.post R K S.f (n + 1))) ∧
    ∃ s : ℤˣ, ∀ (φ : S.X₂ ⟶ (res R S.X₁).X 0) (ψ : S.X₃ ⟶ (res R S.X₁).X 1),
      S.f ≫ φ = resι R S.X₁ → S.g ≫ ψ = φ ≫ (res R S.X₁).d 0 1 →
      ∀ w : Cocycle (sgl S.X₃) (res R S.X₁) 1, sglι S.X₃ ≫ w.1.v 0 1 (zero_add 1) = ψ →
        CohomologyClass.mk (zcomp (Cocycle.ofHom (resAug S.X₃)) z (zero_add 1)) = s • CohomologyClass.mk w := by
  intro R _ S hS
  obtain ⟨e, ⟨h⟩⟩ := GlobalTheory.T.shortExact_mappingCone_resolution_homotopyEquiv R S hS
  refine ⟨_, exact_part R S e h, 1, ?_⟩
  intro φ ψ hφ hψ w hw
  rw [one_smul]
  have hc := resAug_comm R S.f
  have hS' : (S.map (CochainComplex.singleFunctor (Shv R) 0)).ShortExact := hS.map_of_exact (HomologicalComplex.single _ _ _)
  haveI := mappingCone.quasiIso_descShortComplex hS'
  haveI : (res R S.X₁).IsKInjective := by unfold res; infer_instance
  apply (GlobalTheory.T.hypercohomologyPullback_bijective_of_quasiIso R (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0)))
    (res R S.X₁) 1).1
  exact assemble _ _ _ _ _ _ _ e.homotopyHomInvId (GlobalTheory.T.mappingCone_shortExact_augmentation_class_eq R S hS hc e h) (GlobalTheory.T.mappingCone_connecting_cocycle_shortComplex_degree_zero R S hc φ ψ hφ hψ w hw)

end GlobalTheory.EtC.LesChar
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

noncomputable section

namespace GlobalTheory.EtC.SemiTens

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (z : Sec F U) :
    Sec.res g (Sec.map f z) = Sec.map f (Sec.res g z) := by
  have := congrArg (fun k => k.hom z) (f.hom.naturality g.op)
  simpa using this.symm

theorem map_zero' {R : Type} [CommRing R] {F G : Shv R} {U : Scheme.{0}} (z : Sec F U) :
    Sec.map (0 : F ⟶ G) z = 0 := by
  first
  | rfl
  | (show ((0 : F ⟶ G).hom.app (op U)).hom z = 0
     rw [Sheaf.Hom.zero_hom]; rfl)
  | (simp [Sec.map, Sheaf.zero_val])

variable {Q : ℕ} {R : Type} [CommRing R] {I J T : Cx (ZMod Q)} {I' J' K' : Cx R}

def pairHom (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) :
    Sec (I.X s) U →+ Sec (J.X t) U →+ Sec (K'.X w) U :=
  AddMonoidHom.mk' (fun a => ((ν.mul U s t w h (ρ₁.app U s a)).toAddMonoidHom).comp (ρ₂.app U t))
    (fun a₁ a₂ => by ext b; simp)

theorem pairHom_smul (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (U : Scheme.{0}) (s t w : ℤ)
    (h : s + t = w) (r : ULift.{1} (ZMod Q)) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    pairHom ν ρ₁ ρ₂ U s t w h (r • a) b = pairHom ν ρ₁ ρ₂ U s t w h a (r • b) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, (n : ULift.{1} (ZMod Q)) = r :=
    ⟨(r.down.cast : ℤ), ULift.ext (by change ((r.down.cast : ℤ) : ZMod Q) = r.down; exact ZMod.intCast_zmod_cast _)⟩
  simp [pairHom, Int.cast_smul_eq_zsmul, map_zsmul, LinearMap.smul_apply]

def bmap (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (U : Scheme.{0}) (w : ℤ) :
    Tens I J U w →+ Sec (K'.X w) U := by
  classical
  exact DirectSum.toAddMonoid fun p =>
    TensorProduct.liftAddHom (pairHom ν ρ₁ ρ₂ U p.1.1 p.1.2 w p.2) (pairHom_smul ν ρ₁ ρ₂ U p.1.1 p.1.2 w p.2)

theorem bmap_of (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (U : Scheme.{0}) (w : ℤ)
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    bmap ν ρ₁ ρ₂ U w (DirectSum.of _ p (a ⊗ₜ b)) = ν.mul U p.1.1 p.1.2 w p.2 (ρ₁.app U _ a) (ρ₂.app U _ b) := by
  unfold bmap
  rw [DirectSum.toAddMonoid_of]
  simp [pairHom]

theorem lift_of (τ : Pair I J T) (U : Scheme.{0}) (w : ℤ)
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    τ.lift U w (DirectSum.of _ p (a ⊗ₜ b)) = τ.mul U p.1.1 p.1.2 w p.2 a b := by
  unfold Pair.lift
  rw [← DirectSum.lof_eq_of (ULift.{1} (ZMod Q)), DirectSum.toModule_lof]
  simp

theorem tensRes_of {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ)
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res g w (DirectSum.of _ p (a ⊗ₜ b)) = DirectSum.of _ p (Sec.res g a ⊗ₜ Sec.res g b) := by
  unfold Tens.res
  rw [← DirectSum.lof_eq_of (ULift.{1} (ZMod Q)), DirectSum.lmap_lof]
  simp [DirectSum.lof_eq_of]

theorem bmap_nat (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ)
    (x : Tens I J U w) : Sec.res g (bmap ν ρ₁ ρ₂ U w x) = bmap ν ρ₁ ρ₂ V w (Tens.res g w x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [bmap_of, tensRes_of, bmap_of, ν.nat, ρ₁.nat, ρ₂.nat]
    | add y₁ y₂ h₁ h₂ => have e := congrArg₂ (· + ·) h₁ h₂; simpa only [map_add (f := _)] using e
  | add x y hx hy => have e := congrArg₂ (· + ·) hx hy; simpa only [map_add (f := _)] using e

end GlobalTheory.EtC.SemiTens

namespace GlobalTheory.EtC


open SemiTens in
theorem semiMap_of_tensorPair : ∀ (Q : ℕ) (R : Type) [CommRing R] {I J T : Cx (ZMod Q)} {I' J' K' : Cx R} (τ : Pair I J T),
    τ.IsTensor → ∀ (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J'), ∃ σ : SemiMap T K',
    ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      σ.app U w (τ.mul U s t w h a b) = ν.mul U s t w h (ρ₁.app U s a) (ρ₂.app U t b) := by
  intro Q R _ I J T I' J' K' τ hτ ν ρ₁ ρ₂
  have H := fun w => GlobalTheory.T.sheafComplexPairing_tensor_universal_property (ZMod Q) R τ hτ w (K'.X w) (fun U => bmap ν ρ₁ ρ₂ U w)
    (fun V U g x => bmap_nat ν ρ₁ ρ₂ g w x)
  choose φ hnat hlift using H
  have hmul : ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      φ w U (τ.mul U s t w h a b) = ν.mul U s t w h (ρ₁.app U s a) (ρ₂.app U t b) := by
    intro U s t w h a b
    have := hlift w U (DirectSum.of _ ⟨(s, t), h⟩ (a ⊗ₜ b))
    rw [lift_of, bmap_of] at this
    exact this
  have key : ∀ (V : Scheme.{0}) (s : ℤ) (x : Tens I J V s),
      Sec.map (K'.d s (s + 1)) (bmap ν ρ₁ ρ₂ V s x) = φ (s + 1) V (Sec.map (T.d s (s + 1)) (τ.lift V s x)) := by
    intro V s x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of p y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        obtain ⟨⟨s₁, t₁⟩, hp⟩ := p
        rw [bmap_of, lift_of, ν.leibniz, τ.leibniz, map_add (f := _), Units.smul_def, Units.smul_def, map_zsmul, hmul, hmul,
          ρ₁.comm, ρ₂.comm]
      | add y₁ y₂ h₁ h₂ => have e := congrArg₂ (· + ·) h₁ h₂; simpa only [map_add (f := _)] using e
    | add x y hx hy => have e := congrArg₂ (· + ·) hx hy; simpa only [map_add (f := _)] using e
  refine ⟨⟨fun U w => φ w U, fun g w a => hnat w _ _ g a, ?_⟩, hmul⟩
  intro U s t y
  by_cases hst : (ComplexShape.up ℤ).Rel s t
  · have ht : t = s + 1 := hst.symm
    subst ht
    apply (GlobalTheory.T.etaleSheafSections_ext_and_glue R (K'.X (s + 1)) U).1
    obtain ⟨S, hS, hP⟩ := hτ.1 U s y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hP V g hg
    rw [res_map, hnat, ← hx, hlift, key, hnat, res_map, ← hx]
  · rw [T.shape s t hst, K'.shape s t hst, map_zero', map_zero', map_zero]

end GlobalTheory.EtC
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.AcycResLevel

theorem res_lift {R : Type} [CommRing R] (F : Shv R) {W : Shv R} (φ : W ⟶ (res R F).X 0)
    (hφ : φ ≫ (res R F).d 0 1 = 0) : ∃ g : W ⟶ F, g ≫ resι R F = φ := by
  let I := injectiveResolution F
  let e0 : (res R F).X 0 ≅ I.cocomplex.X 0 := I.cochainComplexXIso 0 0 rfl
  let e1 : (res R F).X 1 ≅ I.cocomplex.X 1 := I.cochainComplexXIso 1 1 rfl
  have hd : (res R F).d 0 1 = e0.hom ≫ I.cocomplex.d 0 1 ≫ e1.inv := I.cochainComplex_d 0 1 0 1 rfl rfl
  have hψ : (φ ≫ e0.hom) ≫ I.cocomplex.d 0 1 = 0 := by
    rw [← cancel_mono e1.inv, zero_comp]
    rw [hd] at hφ
    simpa only [Category.assoc] using hφ
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' I.isLimitKernelFork (φ ≫ e0.hom) hψ
  let l' : W ⟶ F := l
  refine ⟨l', ?_⟩
  let ι0 : F ⟶ I.cocomplex.X 0 := I.ι.f 0
  have h1 : resι R F = ι0 ≫ e0.inv := by
    change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ I.ι'.f 0 = _
    rw [InjectiveResolution.ι'_f_zero]
    simp [e0, ι0]
    rfl
  rw [h1]
  have h2 : l' ≫ ι0 = φ ≫ e0.hom := hl
  rw [← Category.assoc, h2, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem cocycle0_v_eq_zero {R : Type} [CommRing R] (G F : Shv R) (a : Cochain (sgl G) (res R F) 0)
    (h : ∃ m, ∃ _ : m + 1 = 0, ∃ b : Cochain (sgl G) (res R F) m, δ m 0 b = a) : a.v 0 0 (add_zero 0) = 0 := by
  obtain ⟨m, hm, b, rfl⟩ := h
  have hz : IsZero ((res R F).X m) :=
    CochainComplex.isZero_of_isStrictlyGE ((injectiveResolution F).cochainComplex) 0 m (by omega)
  have hsd : (sgl G).d 0 1 = 0 :=
    (HomologicalComplex.isZero_single_obj_X _ 0 G 1 (by simp)).eq_of_tgt _ _
  rw [δ_v m 0 (by omega) b 0 0 (add_zero 0) m 1 (by omega) rfl, hsd, zero_comp, smul_zero, add_zero]
  rw [hz.eq_of_tgt (b.v 0 m (by omega)) 0, zero_comp]

theorem ext_subsingleton_of_isZero : ∀ (R : Type) [CommRing R] (G Z : Shv R), IsZero Z → ∀ i : ℤ, Subsingleton (CohomologyClass (sgl G) (res R Z) i) := by
  intro R _ G Z hZ i
  haveI : (res R Z).IsKInjective := inferInstanceAs ((injectiveResolution Z).cochainComplex.IsKInjective)
  haveI : QuasiIso (resAug Z) := inferInstanceAs (QuasiIso (injectiveResolution Z).ι')
  have h0 : (sgl Z).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ ((CochainComplex.singleFunctor (Shv R) 0).map_isZero hZ)
  have h1 : (res R Z).Acyclic := by
    rw [HomologicalComplex.acyclic_iff]
    intro j
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have h2 := (h0 j)
    rw [HomologicalComplex.exactAt_iff_isZero_homology] at h2
    exact h2.of_iso (asIso (HomologicalComplex.homologyMap (resAug Z) j)).symm
  obtain ⟨H⟩ := IsKInjective.nonempty_homotopy_zero (𝟙 (res R Z)) h1
  have gen : ∀ a : Cochain (sgl G) (res R Z) i, δ i (i + 1) a = 0 →
      δ (i - 1) i (a.comp (Cochain.ofHomotopy H) (by omega)) = a := by
    intro a ha
    rw [δ_comp a (Cochain.ofHomotopy H) (by omega) (i + 1) 0 i (by omega) rfl (by omega), δ_ofHomotopy, ha,
      Cochain.zero_comp, smul_zero, add_zero, Cochain.ofHom_zero, sub_zero, Cochain.comp_id]
  have key : ∀ x : CohomologyClass (sgl G) (res R Z) i, x = 0 := by
    intro x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨i - 1, by omega, _, gen α.1 (Cocycle.δ_eq_zero α (i + 1))⟩
  exact ⟨fun x y => (key x).trans (key y).symm⟩

theorem cycles_shortExact : ∀ (R : Type) [CommRing R] (M : Cx R) (k j : ℤ), k + 1 = j → M.ExactAt j → ∃ h : M.iCycles k ≫ M.toCycles k j = 0, (ShortComplex.mk _ _ h).ShortExact := by
  intro R _ M k j hkj hj
  have hw : M.iCycles k ≫ M.toCycles k j = 0 := by
    rw [← cancel_mono (M.iCycles j)]; simp
  refine ⟨hw, ?_⟩
  have hp : (ComplexShape.up ℤ).prev j = k := by simp; omega
  have he : Epi (M.toCycles k j) := by
    subst hp
    exact hj.epi_toCycles
  have hlim : IsLimit (KernelFork.ofι (M.iCycles k) hw) :=
    KernelFork.IsLimit.ofι _ _ (fun φ hφ => M.liftCycles φ j (by simp; omega) (by
        have := congrArg (· ≫ M.iCycles j) hφ
        simpa using this))
      (fun φ hφ => by simp) (fun φ hφ m hm => by rw [← cancel_mono (M.iCycles k)]; simpa using hm)
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ hlim) (by dsimp; infer_instance) he


set_option backward.isDefEq.respectTransparency false in
theorem lift_of_ext_one_subsingleton : ∀ (R : Type) [CommRing R] (G : Shv R) (S : ShortComplex (Shv R)), S.ShortExact → Subsingleton (CohomologyClass (sgl G) (res R S.X₁) 1) → ∀ f : G ⟶ S.X₃, ∃ g : G ⟶ S.X₂, g ≫ S.g = f := by
  intro R _ G S hS h1 f
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence R S hS
  have hI3 := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R S.X₃
  have hI2 := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R S.X₂
  have hmono : Mono (resι R S.X₃) := hI3.2.2.2.2.2.1
  have hd3 : resι R S.X₃ ≫ (res R S.X₃).d 0 1 = 0 := hI3.2.2.2.2.2.2.1
  have hnat : resι R S.X₂ ≫ (resMap R S.g).f 0 = S.g ≫ resι R S.X₃ := (hI2.2.2.2.2.2.2.2 S.X₃ S.g).2
  let e : (sgl G).X 0 ≅ G := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G
  have hz0 : ∀ p : ℤ, p ≠ 0 → IsZero ((sgl G).X p) := fun p hp =>
    HomologicalComplex.isZero_single_obj_X _ 0 G p hp
  have hsd : (sgl G).d 0 1 = 0 := (hz0 1 (by simp)).eq_of_tgt _ _
  let a3 : Cochain (sgl G) (res R S.X₃) 0 := Cochain.single (p := 0) (q := 0) (e.hom ≫ f ≫ resι R S.X₃) 0
  have ha3 : δ 0 1 a3 = 0 := by
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    by_cases hp : p = 0
    · subst hp
      obtain rfl : q = 1 := by omega
      rw [δ_v 0 1 rfl a3 0 1 hpq 0 1 (by omega) rfl, Cochain.single_v, hsd, zero_comp, smul_zero, add_zero,
        Cochain.zero_v, Category.assoc, Category.assoc, hd3, comp_zero, comp_zero]
    · exact (hz0 p hp).eq_of_src _ _
  let c3 : CohomologyClass (sgl G) (res R S.X₃) 0 := CohomologyClass.mk (Cocycle.mk a3 1 rfl ha3)
  have hc3 : HK.ext R (sgl G) z 0 (0 + 1) rfl c3 = 0 := h1.elim _ _
  obtain ⟨w, hw⟩ := ((hz (sgl G) 0).2.1 c3).1 hc3
  obtain ⟨β, rfl⟩ := w.mk_surjective
  have hw' : CohomologyClass.mk (zcomp β (Cocycle.ofHom (resMap R S.g)) (add_zero 0)) = c3 := hw
  have hdiff : CohomologyClass.mk (zcomp β (Cocycle.ofHom (resMap R S.g)) (add_zero 0) - Cocycle.mk a3 1 rfl ha3) = 0 := by
    rw [CohomologyClass.mk_sub, hw', sub_self]
  rw [CohomologyClass.mk_eq_zero_iff] at hdiff
  have hv := GlobalTheory.AcycResLevel.cocycle0_v_eq_zero G S.X₃ _ hdiff
  have hv' : β.1.v 0 0 (add_zero 0) ≫ (resMap R S.g).f 0 = e.hom ≫ f ≫ resι R S.X₃ := by
    have h := hv
    simp [zcomp, a3, Cochain.comp_zero_cochain_v, sub_eq_zero] at h
    exact h
  have hb : β.1.v 0 0 (add_zero 0) ≫ (res R S.X₂).d 0 1 = 0 := by
    have h := congrArg (fun c => c.v 0 1 (by simp)) (Cocycle.δ_eq_zero β 1)
    rw [δ_v 0 1 rfl _ 0 1 (by simp) 0 1 (by simp) (by simp)] at h
    rw [hsd, zero_comp, smul_zero, add_zero, Cochain.zero_v] at h
    exact h
  obtain ⟨g', hg'⟩ := GlobalTheory.AcycResLevel.res_lift S.X₂ (e.inv ≫ β.1.v 0 0 (add_zero 0))
    (by rw [Category.assoc, hb, comp_zero])
  refine ⟨g', ?_⟩
  rw [← cancel_mono (resι R S.X₃), ← cancel_epi e.hom, Category.assoc, ← hnat, ← Category.assoc g', hg', ← hv']
  simp

theorem ext_pos_subsingleton_of_shortExact : ∀ (R : Type) [CommRing R] (G : Shv R) (S : ShortComplex (Shv R)), S.ShortExact → (∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R S.X₂) i)) → (∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R S.X₁) i)) → ∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R S.X₃) i) := by
  intro R _ G S hS h2 h1 i hi
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence R S hS
  have key : ∀ x : CohomologyClass (sgl G) (res R S.X₃) i, x = 0 := by
    intro x
    have e := (hz (sgl G) i).2.1
    have h0 : HK.ext R (sgl G) z i (i + 1) rfl x = 0 := (h1 (i + 1) (by omega)).elim _ _
    obtain ⟨w, hw⟩ := (e x).1 h0
    rw [← hw, (h2 i hi).elim w 0, map_zero]
  exact ⟨fun x y => (key x).trans (key y).symm⟩

theorem subsingleton_of_lifts : ∀ (R : Type) [CommRing R] (G : Shv R) (M : Cx R) (n : ℤ), (∀ f : G ⟶ M.X n, f ≫ M.d n (n + 1) = 0 → ∃ g : G ⟶ M.X (n - 1), g ≫ M.d (n - 1) n = f) → Subsingleton (CohomologyClass (sgl G) M n) := by
  intro R _ G M n hlift
  have hz : ∀ p : ℤ, p ≠ 0 → IsZero ((sgl G).X p) := fun p hp =>
    HomologicalComplex.isZero_single_obj_X _ 0 G p hp
  have hd : (sgl G).d 0 1 = 0 := (hz 1 (by simp)).eq_of_tgt _ _
  let e : (sgl G).X 0 ≅ G := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G
  have gen : ∀ a : Cochain (sgl G) M n, δ n (n + 1) a = 0 → ∃ b : Cochain (sgl G) M (n - 1), δ (n - 1) n b = a := by
    intro a ha
    have h := congrArg (fun c => c.v 0 (n + 1) (by simp)) ha
    rw [δ_v n (n + 1) rfl _ 0 (n + 1) (by simp) n 1 (by simp) (by simp)] at h
    rw [hd, zero_comp, smul_zero, add_zero, Cochain.zero_v] at h
    have hf : (e.inv ≫ a.v 0 n (by simp)) ≫ M.d n (n + 1) = 0 := by
      rw [Category.assoc, h, comp_zero]
    obtain ⟨g, hg⟩ := hlift _ hf
    refine ⟨Cochain.single (p := 0) (q := n - 1) (e.hom ≫ g) (n - 1), ?_⟩
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    by_cases hp : p = 0
    · subst hp
      obtain rfl : n = q := by omega
      rw [δ_v (n - 1) n (by omega) _ 0 n hpq (n - 1) 1 (by omega) rfl, Cochain.single_v, hd, zero_comp,
        smul_zero, add_zero, Category.assoc, hg, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    · exact (hz p hp).eq_of_src _ _
  have key : ∀ x : CohomologyClass (sgl G) M n, x = 0 := by
    intro x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    obtain ⟨b, hb⟩ := gen α.1 (Cocycle.δ_eq_zero α (n + 1))
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨n - 1, by omega, b, hb⟩
  exact ⟨fun x y => (key x).trans (key y).symm⟩

end GlobalTheory.AcycResLevel

theorem GlobalTheory.EtC.subsingleton_cohomologyClass_sgl_of_acyclic : ∀ (R : Type) [CommRing R] (G : Shv R) (M : Cx R) (a : ℤ) [M.IsStrictlyGE a], M.Acyclic → (∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (M.X t)) i)) → ∀ n : ℤ, Subsingleton (CohomologyClass (sgl G) M n) := by
  intro R _ G M a _ hM hExt n
  have hZ0 : ∀ k, k ≤ a → IsZero (M.cycles k) := by
    intro k hk
    obtain ⟨h, hS⟩ := GlobalTheory.AcycResLevel.cycles_shortExact R M (k - 1) k (by omega) (hM k)
    have : Epi (M.toCycles (k - 1) k) := hS.epi_g
    exact IsZero.of_epi (M.toCycles (k - 1) k) (M.isZero_of_isStrictlyGE a (k - 1))
  have hge : ∀ k, a ≤ k → ∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (M.cycles k)) i) := by
    intro k hk
    induction k, hk using Int.leInduction with
    | base => intro i _; exact GlobalTheory.AcycResLevel.ext_subsingleton_of_isZero R G _ (hZ0 a le_rfl) i
    | succ k hak ih =>
      obtain ⟨h, hS⟩ := GlobalTheory.AcycResLevel.cycles_shortExact R M k (k + 1) rfl (hM (k + 1))
      exact GlobalTheory.AcycResLevel.ext_pos_subsingleton_of_shortExact R G _ hS (hExt k) ih
  have hZ : ∀ k, ∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (M.cycles k)) i) := by
    intro k
    rcases le_or_gt k a with hk | hk
    · intro i _
      exact GlobalTheory.AcycResLevel.ext_subsingleton_of_isZero R G _ (hZ0 k hk) i
    · exact hge k hk.le
  refine GlobalTheory.AcycResLevel.subsingleton_of_lifts R G M n fun f hf => ?_
  obtain ⟨h, hS⟩ := GlobalTheory.AcycResLevel.cycles_shortExact R M (n - 1) n (by omega) (hM n)
  obtain ⟨g, hg⟩ := GlobalTheory.AcycResLevel.lift_of_ext_one_subsingleton R G _ hS ((hZ (n - 1) 1 one_pos)) (M.liftCycles f (n + 1) (by simp) hf)
  refine ⟨g, ?_⟩
  have := congrArg (· ≫ M.iCycles n) hg
  simpa using this
end
