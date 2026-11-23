module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTensorUniversalProperty
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle652
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle655
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.TwMulInj

theorem loc_bind {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  choose R hR hRQ using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => h V g (hSP V g hg)
  refine ⟨Sieve.bind S.arrows (fun V g hg => R V g hg), ?_, ?_⟩
  · exact (Scheme.etaleTopology).bind_covering hS (fun V g hg => hR V g hg)
  · rintro W _ ⟨V, k, g, hg, hk, rfl⟩
    exact hRQ V g hg W k hk

theorem loc_top {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => h V g⟩

theorem loc_empty {U : Scheme.{0}} [IsEmpty U] {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} : Loc U P :=
  ⟨⊥, Scheme.bot_mem_grothendieckTopology (P := @Etale) U, fun _ _ hg => hg.elim⟩

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res, op_comp, Functor.map_comp]

theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) :=
  congrArg (fun f => f.hom x) (φ.hom.naturality g.op)

theorem sglι_left {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom (Sec.map (sglι F) x) = x := by
  have h := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv_hom_id
  exact (congrArg (fun f : F ⟶ F => (f.hom.app (op U)).hom x) h).trans rfl

theorem nsmul_eq_zero_of_dvd {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] {c : ℕ} (h : q ∣ c)
    (x : M) : c • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((c : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    simp only [ULift.down_natCast, ULift.zero_down]
    exact (CharP.cast_eq_zero_iff (ZMod q) q c).2 h
  rw [this, zero_smul]

theorem res_zero {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res (F := F) g 0 = 0 :=
  map_zero _

theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x :=
  map_nsmul _ _ _

theorem map_nsmul' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℕ) (x : Sec F U) :
    Sec.map φ (c • x) = c • Sec.map φ x :=
  map_nsmul _ _ _

end GlobalTheory.EtC.TwMulInj

namespace GlobalTheory.EtC.TwMulInj
variable {R : Type} [CommRing R]

theorem tmap_nsmul {M N M' N' : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
    [Module (ULift.{1} R) M] [Module (ULift.{1} R) N] [Module (ULift.{1} R) M'] [Module (ULift.{1} R) N']
    (f : M →ₗ[ULift.{1} R] M') (g : N →ₗ[ULift.{1} R] N') (c : ℕ) (s : M) (t : N) :
    TensorProduct.map f g (c • (s ⊗ₜ[ULift.{1} R] t)) = c • (f s ⊗ₜ g t) := by
  rw [map_nsmul, TensorProduct.map_tmul]

theorem tens_res_lof {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (s : Sec (I.X p.1.1) U) (t : Sec (J.X p.1.2) U) (c : ℕ) :
    Tens.res g w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p (c • (s ⊗ₜ t))) =
    DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) V ⊗[ULift.{1} R] Sec (J.X p.1.2) V) p (c • (Sec.res g s ⊗ₜ Sec.res g t)) := by
  classical
  unfold Tens.res
  rw [DirectSum.lmap_lof, tmap_nsmul]

theorem lift_lof {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (s : Sec (I.X p.1.1) U) (t : Sec (J.X p.1.2) U) (c : ℕ) :
    μ.lift U w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p (c • (s ⊗ₜ t))) = c • μ.mul U p.1.1 p.1.2 w p.2 s t := by
  classical
  unfold Pair.lift
  rw [DirectSum.toModule_lof, map_nsmul, TensorProduct.lift.tmul]

theorem lof_eq_zero {ι : Type*} [DecidableEq ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module (ULift.{1} R) (M i)]
    (i : ι) (x : M i) (h : DirectSum.lof (ULift.{1} R) ι M i x = 0) : x = 0 :=
  DirectSum.of_injective (β := M) i (h.trans (map_zero _).symm)

end GlobalTheory.EtC.TwMulInj

namespace GlobalTheory.EtC.TwMulInj

theorem tw_mul_loc_injective : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → (∀ (W : Scheme.{0}) (ζ : Prim q Γ(W, ⊤)) (c : ℕ), c • (twGen i ζ ⊗ₜ[ULift.{1} (ZMod q)] twGen j ζ) = 0 → Loc W fun V _ => Nonempty V → q ∣ c) → ∀ {K : Cx (ZMod q)} (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), τ.IsTensor → ∀ φ : tw q k ⟶ K.X 0, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen k ζ) = τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) → ∀ (U : Scheme.{0}) (a : Sec (tw q k) U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0 := by
  intro q _ i j k hk hyp K τ hτ φ hφ U a ha
  have Tk := GlobalTheory.T.tateTwist_sections_locally_generated q k
  have Ti := GlobalTheory.T.tateTwist_sections_locally_generated q i
  have Tj := GlobalTheory.T.tateTwist_sections_locally_generated q j
  refine loc_bind (Tk.1 U a) ?_
  rintro V g (h0 | ⟨ζ, c, hc⟩)
  · exact loc_top fun W k' => by rw [res_comp, h0, res_zero]
  ·
    have hres : ∀ (W : Scheme.{0}) (h : W ⟶ V), Sec.res (h ≫ g) a = c • Sec.res h (twGen k ζ) := by
      intro W h
      rw [res_comp, hc, res_nsmul]
    set A := Sec.map (sglι (tw q i)) (twGen i ζ) with hA
    set B := Sec.map (sglι (tw q j)) (twGen j ζ) with hB
    have h1 : c • τ.mul V 0 0 0 (add_zero 0) A B = 0 := by
      rw [← hφ V ζ, ← map_nsmul', ← hc, map_res, ha, res_zero]
    classical
    let x : Tens (sgl (tw q i)) (sgl (tw q j)) V 0 :=
      DirectSum.lof (ULift.{1} (ZMod q)) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = 0} =>
        Sec ((sgl (tw q i)).X p.1.1) V ⊗[ULift.{1} (ZMod q)] Sec ((sgl (tw q j)).X p.1.2) V) ⟨(0, 0), by simp⟩ (c • (A ⊗ₜ B))
    have hx : τ.lift V 0 x = 0 := (lift_lof τ V 0 ⟨(0, 0), by simp⟩ A B c).trans h1
    refine loc_bind (hτ.2 V 0 x hx) ?_
    intro V' g' hx'

    set ζ' := ζ.map g'.appTop.hom with hζ'
    have h2 : c • (twGen i ζ' ⊗ₜ[ULift.{1} (ZMod q)] twGen j ζ') = 0 := by
      have e2 := lof_eq_zero _ _ _ ((tens_res_lof g' 0 ⟨(0, 0), by simp⟩ A B c).symm.trans hx')
      have e3 : c • (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)).hom.hom.app (op V')).hom
          (Sec.res g' A) ⊗ₜ[ULift.{1} (ZMod q)]
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q j)).hom.hom.app (op V')).hom (Sec.res g' B)) = 0 :=
        (tmap_nsmul _ _ c _ _).symm.trans ((congrArg (TensorProduct.map
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)).hom.hom.app (op V')).hom
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q j)).hom.hom.app (op V')).hom) e2).trans (map_zero _))
      have ei : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)).hom.hom.app (op V')).hom
          (Sec.res g' A) = twGen i ζ' := by
        have h := (map_res (sglι (tw q i)) g' (twGen i ζ)).symm
        rw [Ti.2.2.2.1 V' V g' ζ] at h
        exact (congrArg ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)).hom.hom.app (op V')).hom h).trans
          (sglι_left _ _)
      have ej : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q j)).hom.hom.app (op V')).hom
          (Sec.res g' B) = twGen j ζ' := by
        have h := (map_res (sglι (tw q j)) g' (twGen j ζ)).symm
        rw [Tj.2.2.2.1 V' V g' ζ] at h
        exact (congrArg ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q j)).hom.hom.app (op V')).hom h).trans
          (sglι_left _ _)
      rw [ei, ej] at e3
      exact e3
    refine loc_bind (hyp V' ζ' c h2) ?_
    intro V'' g'' hq
    rcases isEmpty_or_nonempty V'' with hV | hV
    · exact loc_empty
    · have hqc := hq hV
      exact loc_top fun W h => by
        rw [hres, nsmul_eq_zero_of_dvd hqc]

end GlobalTheory.EtC.TwMulInj
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.TwMulSurj

variable {R : Type} [CommRing R]

theorem loc_top (U : Scheme.{0}) {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem loc_mono {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (h' : ∀ V g, P V g → P' V g) :
    Loc U P' := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => h' V g (hP V g hg)⟩

theorem loc_and {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (h' : Loc U P') :
    Loc U fun V g => P V g ∧ P' V g := by
  obtain ⟨S, hS, hP⟩ := h
  obtain ⟨S', hS', hP'⟩ := h'
  exact ⟨S ⊓ S', GrothendieckTopology.intersection_covering _ hS hS', fun V g hg => ⟨hP V g hg.1, hP' V g hg.2⟩⟩

theorem loc_bind {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} {P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U P) (h' : ∀ V g, P V g → Loc V fun W k => P' W (k ≫ g)) : Loc U P' := by
  classical
  obtain ⟨S, hS, hP⟩ := h
  let Rs : ∀ ⦃V : Scheme.{0}⦄ ⦃g : V ⟶ U⦄, S.arrows g → Sieve V := fun V g hg => (h' V g (hP V g hg)).choose
  refine ⟨Sieve.bind S.arrows Rs, Scheme.etaleTopology.bind_covering hS fun V g hg => (h' V g (hP V g hg)).choose_spec.1, ?_⟩
  rintro W _ ⟨V, k, g, hg, hk, rfl⟩
  exact (h' V g (hP V g hg)).choose_spec.2 W k hk

theorem map_comp_apply {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem map_id_apply {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl

theorem res_map {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map f x) = Sec.map f (Sec.res g x) := by
  have := congrArg (fun m => m.hom x) (f.hom.naturality g.op)
  simpa using this.symm

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res]

theorem smap_add {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map f (x + y) = Sec.map f x + Sec.map f y := map_add _ x y

theorem sres_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := map_add _ x y

theorem smap_nsmul {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} (n : ℕ) (x : Sec F U) :
    Sec.map f (n • x) = n • Sec.map f x := map_nsmul _ n x

theorem sres_nsmul {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (x : Sec F U) :
    Sec.res g (n • x) = n • Sec.res g x := map_nsmul _ n x

theorem smap_zero {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} : Sec.map f (0 : Sec F U) = 0 := map_zero _

theorem map_zero_hom {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := by
  rfl

theorem eq_zero_of_isZero {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (x : Sec F U) : x = 0 := by
  rw [← map_id_apply x, hF.eq_of_src (𝟙 F) 0, map_zero_hom]

def Good {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) (x : Sec G U) : Prop :=
  Loc U fun V g => ∃ z : Sec F V, Sec.map φ z = Sec.res g x

theorem good_of {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {x : Sec G U} (h : ∃ z, Sec.map φ z = x) : Good φ U x := by
  obtain ⟨z, rfl⟩ := h
  exact loc_top U fun V g => ⟨Sec.res g z, (res_map φ g z).symm⟩

theorem good_bind {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec G U) {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (hP : Loc U P) (h : ∀ V g, P V g → Good φ V (Sec.res g x)) : Good φ U x := by
  refine loc_bind hP fun V g hg => ?_
  obtain ⟨S, hS, hS'⟩ := h V g hg
  exact ⟨S, hS, fun W k hk => by obtain ⟨z, hz⟩ := hS' W k hk; exact ⟨z, by rw [hz, res_comp]⟩⟩

theorem good_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {x x' : Sec G U} (h : Good φ U x) (h' : Good φ U x') :
    Good φ U (x + x') :=
  loc_mono (loc_and h h') fun _ g ⟨⟨z, hz⟩, ⟨z', hz'⟩⟩ => ⟨z + z', by rw [smap_add, sres_add, hz, hz']⟩

theorem good_zero {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) : Good φ U 0 := good_of φ ⟨0, smap_zero _⟩

end GlobalTheory.EtC.TwMulSurj

namespace GlobalTheory.EtC


open TwMulSurj in
theorem tw_mul_locSurj : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {K : Cx (ZMod q)}
    (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), τ.IsTensor → ∀ φ : tw q k ⟶ K.X 0,
    (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen k ζ) =
      τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) →
    ∀ (U : Scheme.{0}) (y : Sec (K.X 0) U), Loc U fun V g => ∃ z : Sec (tw q k) V, Sec.map φ z = Sec.res g y := by
  intro q _ i j k hk K τ hτ φ hφ
  have hT := GlobalTheory.T.tateTwist_sections_locally_generated
  have key_gen : ∀ V (a : Sec (tw q i) V) (b : Sec (tw q j) V),
      Good φ V (τ.mul V 0 0 0 (add_zero 0) (Sec.map (sglι _) a) (Sec.map (sglι _) b)) := by
    intro V a b
    refine good_bind φ _ ((hT q i).1 V a) ?_
    rintro W g (ha | ⟨ζ, c, ha⟩)
    · apply good_of
      refine ⟨0, ?_⟩
      rw [smap_zero, τ.nat, res_map, res_map, ha, smap_zero]
      simp
    · refine good_bind φ _ ((hT q j).2.1 W ζ (Sec.res g b)) ?_
      rintro W' g' ⟨c', hb⟩
      apply good_of
      refine ⟨(c * c') • twGen k (ζ.map g'.appTop.hom), ?_⟩
      rw [smap_nsmul, hφ, τ.nat, τ.nat, res_map, res_map, res_map, res_map, ha, hb, sres_nsmul, (hT q i).2.2.2.1, smap_nsmul, smap_nsmul]
      simp [mul_comm, mul_smul]
  have key : ∀ V (x : Tens (sgl (tw q i)) (sgl (tw q j)) V 0), Good φ V (τ.lift V 0 x) := by
    intro V x
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero]; exact good_zero φ V
    | of p t =>
      obtain ⟨⟨s, t'⟩, hst⟩ := p
      induction t using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]; exact good_zero φ V
      | add u u' hu hu' => rw [map_add (f := _), map_add (f := _)]; exact good_add φ hu hu'
      | tmul a b =>
        have hlift : τ.lift V 0 (DirectSum.of _ ⟨(s, t'), hst⟩ (a ⊗ₜ b)) = τ.mul V s t' 0 hst a b := by
          unfold Pair.lift
          erw [DirectSum.toModule_lof]
          rfl
        rw [hlift]
        by_cases hs : s = 0
        · subst hs
          obtain rfl : t' = 0 := by omega
          have ea : Sec.map (sglι _) (Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)).hom a) = a := by
            refine (map_comp_apply _ (sglι _) a).symm.trans ?_
            simp [sglι]; rfl
          have eb : Sec.map (sglι _) (Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q j)).hom b) = b := by
            refine (map_comp_apply _ (sglι _) b).symm.trans ?_
            simp [sglι]; rfl
          rw [← ea, ← eb]
          exact key_gen V _ _
        · have h0 : τ.mul V s t' 0 hst a b = 0 := by
            rw [eq_zero_of_isZero (F := (sgl (tw q i)).X s) (HomologicalComplex.isZero_single_obj_X _ _ _ _ hs) a]
            simp
          rw [h0]
          exact good_zero φ V
    | add x x' hx hx' => rw [map_add (f := _)]; exact good_add φ hx hx'
  intro U y
  exact good_bind φ y (hτ.1 U 0 y) fun V g ⟨x, hx⟩ => hx ▸ key V x

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.isTensor_universal_property : ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → (∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J'), ∃! u : K ⟶ K', τ.Compat ν f g u) ∧ (I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0) ∧ ∀ {K' : Cx R} (u : K ⟶ K'), ∃ ν : Pair I J K', τ.Compat ν (𝟙 I) (𝟙 J) u := by
  first | (exact @GlobalTheory.EtC.Pair.isTensor_universal) | (exact GlobalTheory.EtC.Pair.isTensor_universal) | (intros; apply GlobalTheory.EtC.Pair.isTensor_universal  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

abbrev secEvalFun (R : Type) [CommRing R] (U : Scheme.{0}) : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
  sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙ (evaluation _ _).obj (op U)

theorem injectiveResolution_sections_degree_zero_kernel (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) :
    (∀ w : Sec ((injectiveResolution F).cocomplex.X 0) U,
      Sec.map ((injectiveResolution F).cocomplex.d 0 1) w = 0 →
        ∃ a : Sec F U, Sec.map ((injectiveResolution F).ι.f 0) a = w) ∧
    Function.Injective (Sec.map ((injectiveResolution F).ι.f 0) (U := U)) := by
  set I := injectiveResolution F
  have hlim := KernelFork.mapIsLimit _ I.isLimitKernelFork (secEvalFun R U)
  let S : ShortComplex (ModuleCat.{1} (ULift.{1} R)) :=
    ShortComplex.mk ((secEvalFun R U).map (I.ι.f 0)) ((secEvalFun R U).map (I.cocomplex.d 0 1))
      (by rw [← Functor.map_comp, I.ι_f_zero_comp_complex_d, Functor.map_zero])
  have hS : S.Exact := S.exact_of_f_is_kernel hlim
  refine ⟨fun w hw => (ShortComplex.moduleCat_exact_iff S).1 hS w hw, ?_⟩
  have : Mono ((secEvalFun R U).map (I.ι.f 0)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

theorem chosenInjectiveResolutionAugmentation_eq_iota_comp (R : Type) [CommRing R] (F : Shv R) :
    resι R F = (injectiveResolution F).ι.f 0 ≫ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).inv := by
  simp [resι, InjectiveResolution.ι'_f_zero]
  rfl

theorem chosenInjectiveResolutionEtaleSheaf_d_zero_one_eq (R : Type) [CommRing R] (F : Shv R) :
    (res R F).d 0 1 = ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom ≫
      (injectiveResolution F).cocomplex.d 0 1 ≫ ((injectiveResolution F).cochainComplexXIso 1 1 rfl).inv :=
  InjectiveResolution.cochainComplex_d _ 0 1 0 1 rfl rfl

theorem chosenInjectiveResolutionEtaleSheaf_exactAt_ne_zero (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (hn : n ≠ 0) : (res R F).ExactAt n := by
  have h : ((CochainComplex.singleFunctor (Shv R) 0).obj F).ExactAt n :=
    HomologicalComplex.exactAt_single_obj (ComplexShape.up ℤ) 0 F n hn
  exact (quasiIsoAt_iff_exactAt (injectiveResolution F).ι' n h).1 inferInstance

theorem resSec (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) :
    (∀ z : Sec ((res R F).X 0) U, Sec.map ((res R F).d 0 1) z = 0 ↔ ∃ a : Sec F U, Sec.map (resι R F) a = z) ∧
    Function.Injective (Sec.map (resι R F) (U := U)) ∧
    (∀ (m n k : ℤ), 0 < n → m + 1 = n → ∀ z : Sec ((res R F).X n) U, n + 1 = k →
      Sec.map ((res R F).d n k) z = 0 →
        Loc U fun V g => ∃ y : Sec ((res R F).X m) V, Sec.map ((res R F).d m n) y = Sec.res g z) ∧
    ∀ n : ℤ, n < 0 → Subsingleton (Sec ((res R F).X n) U) := by
  obtain ⟨hker, hinj⟩ := injectiveResolution_sections_degree_zero_kernel R F U
  set I := injectiveResolution F
  set e0 := I.cochainComplexXIso 0 0 rfl
  set e1 := I.cochainComplexXIso 1 1 rfl
  have hι : ∀ a : Sec F U, Sec.map (resι R F) a = Sec.map e0.inv (Sec.map (I.ι.f 0) a) := by
    intro a; rw [chosenInjectiveResolutionAugmentation_eq_iota_comp]; rfl
  have hd : ∀ z : Sec ((res R F).X 0) U,
      Sec.map ((res R F).d 0 1) z = Sec.map e1.inv (Sec.map (I.cocomplex.d 0 1) (Sec.map e0.hom z)) := by
    intro z; rw [chosenInjectiveResolutionEtaleSheaf_d_zero_one_eq]; rfl
  have he0 : ∀ z : Sec ((res R F).X 0) U, Sec.map e0.inv (Sec.map e0.hom z) = z := by
    intro z; change Sec.map (e0.hom ≫ e0.inv) z = z; rw [e0.hom_inv_id]; rfl
  have he0' : ∀ w : Sec (I.cocomplex.X 0) U, Sec.map e0.hom (Sec.map e0.inv w) = w := by
    intro w; change Sec.map (e0.inv ≫ e0.hom) w = w; rw [e0.inv_hom_id]; rfl
  have he1 : ∀ w : Sec (I.cocomplex.X 1) U, Sec.map e1.hom (Sec.map e1.inv w) = w := by
    intro w; change Sec.map (e1.inv ≫ e1.hom) w = w; rw [e1.inv_hom_id]; rfl
  refine ⟨fun z => ⟨fun hz => ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hd] at hz
    have hz' : Sec.map (I.cocomplex.d 0 1) (Sec.map e0.hom z) = 0 := by
      have := congrArg (Sec.map e1.hom) hz
      rw [he1] at this
      exact this.trans (map_zero (e1.hom.hom.app (op U)).hom)
    obtain ⟨a, ha⟩ := hker _ hz'
    exact ⟨a, by rw [hι, ha, he0]⟩
  · rintro ⟨a, rfl⟩
    rw [hd, hι, he0']
    change Sec.map e1.inv (Sec.map (I.ι.f 0 ≫ I.cocomplex.d 0 1) a) = 0
    rw [I.ι_f_zero_comp_complex_d]
    exact map_zero _
  · intro a b hab
    rw [hι, hι] at hab
    have := congrArg (Sec.map e0.hom) hab
    rw [he0', he0'] at this
    exact hinj this
  · intro m n k hn hmn z hnk hz
    have hex : ((res R F).sc' m n k).Exact :=
      (HomologicalComplex.exactAt_iff' _ m n k (by simp; omega) (by simp; omega)).1
        (chosenInjectiveResolutionEtaleSheaf_exactAt_ne_zero R F n (by omega))
    exact (GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally R ((res R F).sc' m n k)).1 hex U z hz
  · intro n hn
    haveI : (res R F).IsStrictlyGE 0 := (inferInstance : I.cochainComplex.IsStrictlyGE 0)
    have h0 : IsZero ((res R F).X n) := CochainComplex.isZero_of_isStrictlyGE _ 0 n hn
    exact ModuleCat.isZero_iff_subsingleton.1 ((secEvalFun R U).map_isZero h0)

end GlobalTheory.EtC
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

theorem _root_.GlobalTheory.T.exists_siegel_period_of_symplectic_basis : ∀ (h : ℕ) (Hm : Matrix (Fin h) (Fin h) ℂ) (v : Fin h ⊕ Fin h → (Fin h → ℂ)), Hm.IsHermitian → (∀ z : Fin h → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ i j, (hermForm Hm (v i) (v j)).im = (omegaStd (Pi.single i 1 : Fin h ⊕ Fin h → ℤ) (Pi.single j 1) : ℝ)) → ∃ (τ : Matrix (Fin h) (Fin h) ℂ) (T : (Fin h → ℂ) ≃ₗ[ℂ] (Fin h → ℂ)), τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ ∀ a, T (per τ a) = ∑ i, a i • v i := by
  first | exact @GlobalTheory.RiemannRel.exists_siegel_of_symplectic | exact GlobalTheory.RiemannRel.exists_siegel_of_symplectic | (intros; apply GlobalTheory.RiemannRel.exists_siegel_of_symplectic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.isGrpPullback_descent_along_galoisCover : ∀ (S S₁ Y : Scheme.{0}) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga] (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y) (A' : Over S₁) (A : Over S) (B : Over Y) [GrpObj A'] [GrpObj A] [GrpObj B] (φ₁ : A'.left ⟶ A.left) (ψ : A'.left ⟶ B.left) (φ : A.left ⟶ B.left), GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → IsGrpPullback A' A π₁ φ₁ → IsGrpPullback A' B (π₁ ≫ f) ψ → φ₁ ≫ φ = ψ → IsGrpPullback A B f φ := by
  first | exact @GlobalTheory.GaloisCartDesc.isGrpPullback_of_galoisCover | exact GlobalTheory.GaloisCartDesc.isGrpPullback_of_galoisCover | (intros; apply GlobalTheory.GaloisCartDesc.isGrpPullback_of_galoisCover <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.invAlg_identity_of_principal_congruence : UnitLemmaLie → ∀ (K : UQ) (a : K.O), K.Small a → ∀ B₁ B₂ : InvAlg K, (1 + algebraMap K.O B₁.A a * B₁.g) * B₁.σ (1 + algebraMap K.O B₁.A a * B₁.g) = 1 → (1 + algebraMap K.O B₂.A a * B₂.g) * B₂.σ (1 + algebraMap K.O B₂.A a * B₂.g) = 1 → (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.CongruenceCayley.identity_of_principal_congruence | exact GlobalTheory.UnitLemma.CongruenceCayley.identity_of_principal_congruence | (intros; apply GlobalTheory.UnitLemma.CongruenceCayley.identity_of_principal_congruence <;> assumption)
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

theorem _root_.GlobalTheory.T.unitary_block_triangular_levi_part_unitary : GlobalTheory.SatakeWeyl.LeviPart := by
  first | exact @GlobalTheory.SatakeWeyl.leviPart | exact GlobalTheory.SatakeWeyl.leviPart | (intros; apply GlobalTheory.SatakeWeyl.leviPart <;> assumption)
end
