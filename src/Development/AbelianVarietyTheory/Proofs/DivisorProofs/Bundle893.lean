module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle863
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle654
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle548
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle263

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.liftBaseChange_bijective_linearEquiv_square_univ : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type 1) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (M' : Type 1) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (e : M →ₗ[R] N) (e' : M' →ₗ[R'] N') (f : M →ₛₗ[algebraMap R R'] M') (g : N →ₛₗ[algebraMap R R'] N'), Function.Bijective e → Function.Bijective e' → (∀ x, e' (f x) = g (e x)) → (Function.Bijective (liftSemi f) ↔ Function.Bijective (liftSemi g)) := by
  first | exact @GlobalTheory.BaseChangeIso.main | exact GlobalTheory.BaseChangeIso.main | (intros; apply GlobalTheory.BaseChangeIso.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.liftBaseChange_prod_bijective_semilinear : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (M' : Type) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (f : M →ₛₗ[algebraMap R R'] M') (f' : N →ₛₗ[algebraMap R R'] N') (g : (M × N) →ₛₗ[algebraMap R R'] (M' × N')), (∀ x, g x = (f x.1, f' x.2)) → Function.Bijective (liftSemi f) → Function.Bijective (liftSemi f') → Function.Bijective (liftSemi g) := by
  first | exact @GlobalTheory.liftSemi_prod_bijective | exact GlobalTheory.liftSemi_prod_bijective | (intros; apply GlobalTheory.liftSemi_prod_bijective <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.GeomZero

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  simp [Sec.res]

theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (t : Sec F U) :
    Sec.res g (n • t) = n • Sec.res g t := map_nsmul ((F.obj.map g.op).hom) n t

theorem res_zero {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero ((F.obj.map g.op).hom)

theorem q_dvd_nsmul {q : ℕ} {i : ℤ} {U : Scheme.{0}} (t : Sec (tw q i) U) (k : ℕ) : (q * k) • t = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q * k : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    simp
  rw [this]
  exact zero_smul _ t

theorem eq_zero_of_geom : ∀ (q : ℕ) [NeZero q] (R : Type) [CommRing R], IsUnit (q : R) → ∀ (j : ℤ)
    (a : Ht q (sp R) 0 j), (∀ (K : Type) [Field K] [IsAlgClosed K] (f : R →+* K), pull _ (spMap f) _ 0 a = 0) → a = 0 := by
  intro q _ R _ _ j a ha
  obtain ⟨-, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q j)
  obtain ⟨s, rfl⟩ := (e (Spec (CommRingCat.of R))).surjective a
  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (φ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)),
      Sec.res φ s = 0 := by
    intro K _ _ φ
    have h := ha K (Spec.preimage φ).hom
    have hφ : Spec.map (CommRingCat.ofHom (Spec.preimage φ).hom) = φ := by
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    rw [spMap, hφ, he] at h
    exact (map_eq_zero_iff _ (e _).injective).1 h
  have hs : s = 0 := by
    refine (sec_ext_glue (ZMod q) (tw q j) (Spec (CommRingCat.of R))).1 s 0 ?_
    refine (loc_iff_etale_affine_points (Spec (CommRingCat.of R)) (fun _ g => Sec.res g s = Sec.res g 0)
      (fun V W g k h => by rw [res_comp, res_comp, h])).2 ?_
    intro x
    have stab : ∀ (V W : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of R)) (k : W ⟶ V),
        (Sec.res g s = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g s = c • twGen j ζ) →
        (Sec.res (k ≫ g) s = 0 ∨ ∃ (ζ : Prim q Γ(W, ⊤)) (c : ℕ), Sec.res (k ≫ g) s = c • twGen j ζ) := by
      rintro V W g k (h | ⟨ζ, c, h⟩)
      · left; rw [res_comp, h, res_zero]
      · right; exact ⟨ζ.map k.appTop.hom, c, by rw [res_comp, h, res_nsmul, (GlobalTheory.T.tateTwist_sections_locally_generated q j).2.2.2.1]⟩
    obtain ⟨V, g, hV, hg, hx, hP⟩ := (loc_iff_etale_affine_points (Spec (CommRingCat.of R))
      (fun V g => Sec.res g s = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g s = c • twGen j ζ) stab).1
      ((GlobalTheory.T.tateTwist_sections_locally_generated q j).1 _ s) x
    refine ⟨V, g, hV, hg, hx, ?_⟩
    show Sec.res g s = Sec.res g 0
    rw [res_zero]
    rcases hP with h | ⟨ζ, c, h⟩
    · exact h
    · obtain ⟨v, -⟩ := hx
      let ψ : Spec (CommRingCat.of (AlgebraicClosure (V.residueField v))) ⟶ V :=
        Spec.map (CommRingCat.ofHom (algebraMap (V.residueField v) (AlgebraicClosure (V.residueField v)))) ≫
          V.fromSpecResidueField v
      have h0 := hgeo (AlgebraicClosure (V.residueField v)) (ψ ≫ g)
      rw [res_comp, h, res_nsmul, (GlobalTheory.T.tateTwist_sections_locally_generated q j).2.2.2.1] at h0
      haveI : Nonempty (Spec (CommRingCat.of (AlgebraicClosure (V.residueField v)))) := inferInstance
      obtain ⟨k, rfl⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q j).2.2.1 _ _ _ h0
      rw [h]
      exact q_dvd_nsmul _ k
  rw [hs, map_zero]

end GlobalTheory.EtC.GeomZero
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ConnectedGlobalSections

variable {q : ℕ} [NeZero q] {i : ℤ}

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  simp [Sec.res]

theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (t : Sec F U) :
    Sec.res g (n • t) = n • Sec.res g t := map_nsmul ((F.obj.map g.op).hom) n t

theorem res_twGen {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 V U g ζ

theorem prim_map_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    (ζ.map g.appTop.hom).map k.appTop.hom = ζ.map (k ≫ g).appTop.hom := by
  apply Subtype.ext
  simp [Prim.map]
  rfl

theorem nsmul_eq_up {U : Scheme.{0}} (n : ℕ) (t : Sec (tw q i) U) : n • t = (ULift.up (n : ZMod q)) • t := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  rfl

theorem scalar_eq {U : Scheme.{0}} [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c d : ZMod q)
    (h : c.val • twGen i ζ = d.val • twGen i ζ) : c = d := by
  have h0 : (c - d).val • twGen i ζ = 0 := by
    rw [nsmul_eq_up, ZMod.natCast_zmod_val]
    rw [nsmul_eq_up, nsmul_eq_up, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h
    have : (ULift.up (c - d) : ULift.{1} (ZMod q)) = ULift.up c - ULift.up d := rfl
    rw [this, sub_smul, h, sub_self]
  have hd := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 U ζ _ h0
  have hv : (c - d).val = 0 := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt _)
  exact sub_eq_zero.1 ((ZMod.val_eq_zero _).1 hv)

theorem q_nsmul {U : Scheme.{0}} (t : Sec (tw q i) U) (k : ℕ) : (q * k) • t = 0 := by
  rw [nsmul_eq_up]
  have : ((q * k : ℕ) : ZMod q) = 0 := by simp
  rw [this]
  exact zero_smul _ t

theorem sec_eq_nsmul (X : Scheme.{0}) [Nonempty X] (hX : ∀ s : Set X, IsClopen s → s = ∅ ∨ s = Set.univ)
    (ζ : Prim q Γ(X, ⊤)) (y : Sec (tw q i) X) : ∃ c : ℕ, y = c • twGen i ζ := by
  classical
  let P : ∀ V : Scheme.{0}, (V ⟶ X) → ℕ → Prop := fun V g c => Sec.res g y = c • twGen i (ζ.map g.appTop.hom)
  have hstab : ∀ c (V W : Scheme.{0}) (g : V ⟶ X) (k : W ⟶ V), P V g c → P W (k ≫ g) c := by
    intro c V W g k h
    simp only [P] at h ⊢
    rw [res_comp, h, res_nsmul, res_twGen, prim_map_comp]
  have hloc := (loc_iff_etale_affine_points X (fun V g => ∃ c, P V g c)
    (fun V W g k ⟨c, h⟩ => ⟨c, hstab c V W g k h⟩)).1 ((GlobalTheory.T.tateTwist_sections_locally_generated q i).2.1 X ζ y)
  let S : ZMod q → Set X := fun c =>
    {x | ∃ (V : Scheme.{0}) (g : V ⟶ X), IsAffine V ∧ Etale g ∧ x ∈ Set.range g ∧ P V g c.val}
  have hopen : ∀ c, IsOpen (S c) := by
    intro c
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨V, g, hV, hg, hx, hP⟩
    haveI := hg
    refine ⟨Set.range g, ?_, g.isOpenMap.isOpen_range, hx⟩
    rintro _ ⟨v, rfl⟩
    exact ⟨V, g, hV, hg, ⟨v, rfl⟩, hP⟩
  have hcov : ∀ x, ∃ c, x ∈ S c := by
    intro x
    obtain ⟨V, g, hV, hg, hx, n, hn⟩ := hloc x
    refine ⟨(n : ZMod q), V, g, hV, hg, hx, ?_⟩
    simp only [P] at hn ⊢
    rw [hn, nsmul_eq_up, nsmul_eq_up, ZMod.natCast_zmod_val]
  have hdisj : ∀ c d x, x ∈ S c → x ∈ S d → c = d := by
    rintro c d x ⟨V, g, -, -, ⟨v, rfl⟩, hP⟩ ⟨V', g', -, -, ⟨v', hv'⟩, hP'⟩
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := g') v v' hv'.symm
    haveI : Nonempty ↥(Limits.pullback g g') := ⟨z⟩
    have h1 := hstab _ _ _ g (pullback.fst g g') hP
    have h2 := hstab _ _ _ g' (pullback.snd g g') hP'
    simp only [P] at h1 h2
    rw [pullback.condition] at h1
    exact scalar_eq _ c d (h1.symm.trans h2)
  obtain ⟨x0⟩ := ‹Nonempty X›
  obtain ⟨c0, hx0⟩ := hcov x0
  have hcompl : (S c0)ᶜ = ⋃ d ∈ ({c0}ᶜ : Set (ZMod q)), S d := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
    constructor
    · intro hx
      obtain ⟨d, hd⟩ := hcov x
      exact ⟨d, fun h => hx (h ▸ hd), hd⟩
    · rintro ⟨d, hd, hxd⟩ hx
      exact hd (hdisj d c0 x hxd hx)
  have hclopen : IsClopen (S c0) := by
    refine ⟨?_, hopen c0⟩
    rw [← isOpen_compl_iff, hcompl]
    exact isOpen_biUnion fun d _ => hopen d
  have huniv : S c0 = Set.univ := by
    rcases hX _ hclopen with h | h
    · rw [h] at hx0; exact absurd hx0 (Set.notMem_empty _)
    · exact h
  refine ⟨c0.val, (sec_ext_glue (ZMod q) (tw q i) X).1 _ _ ?_⟩
  refine (loc_iff_etale_affine_points X (fun _ g => Sec.res g y = Sec.res g (c0.val • twGen i ζ))
    (fun V W g k h => by rw [res_comp, res_comp, h])).2 ?_
  intro x
  obtain ⟨V, g, hV, hg, hx, hP⟩ : x ∈ S c0 := huniv ▸ Set.mem_univ x
  refine ⟨V, g, hV, hg, hx, ?_⟩
  rw [hP, res_nsmul, res_twGen]

end GlobalTheory.EtC.ConnectedGlobalSections

namespace GlobalTheory.EtC.ConnectedGlobalSections

theorem clopen_of_idem (B : Type) [CommRing B] (hB : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (s : Set (Spec (CommRingCat.of B))) (hs : IsClopen s) : s = ∅ ∨ s = Set.univ := by
  obtain ⟨e, he, h⟩ := PrimeSpectrum.isClopen_iff.1 (show IsClopen (X := PrimeSpectrum B) s from hs)
  rcases hB e he with rfl | rfl
  · left
    change (s : Set (PrimeSpectrum B)) = ∅
    rw [h]; simp <;> rfl
  · right
    change (s : Set (PrimeSpectrum B)) = Set.univ
    rw [h]; simp <;> rfl

end GlobalTheory.EtC.ConnectedGlobalSections


open GlobalTheory.EtC.ConnectedGlobalSections in
theorem GlobalTheory.EtC.h_zero_pull_bijective : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] (f : A →+* A'),
    IsUnit (q : A) → (∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) → Nontrivial A' →
    (∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) → (∀ e : A', IsIdempotentElem e → e = 0 ∨ e = 1) →
    ∀ i : ℤ, Function.Bijective (pull _ (spMap f) (tw q i) 0) := by
  intro q _ A A' _ _ f hq ⟨ζ0, hζ0⟩ hA' hidA hidA' i
  haveI : Nontrivial A := f.domain_nontrivial
  obtain ⟨-, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)
  let g : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom f)
  haveI : Nonempty (Spec (CommRingCat.of A)) := inferInstance
  haveI : Nonempty (Spec (CommRingCat.of A')) := inferInstance
  let ζ : Prim q Γ(Spec (CommRingCat.of A), ⊤) :=
    Prim.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ⟨ζ0, hq, hζ0⟩
  have hres : Function.Bijective (Sec.res (F := tw q i) g) := by
    constructor
    · change Function.Injective ((tw q i).obj.map g.op).hom
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨c, rfl⟩ := sec_eq_nsmul _ (clopen_of_idem A hidA) ζ y
      have h0 : c • twGen i (ζ.map g.appTop.hom) = 0 := by
        rw [← res_twGen, ← res_nsmul]; exact hy
      obtain ⟨k, rfl⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 _ _ _ h0
      exact q_nsmul _ k
    · intro y
      obtain ⟨c, rfl⟩ := sec_eq_nsmul _ (clopen_of_idem A' hidA') (ζ.map g.appTop.hom) y
      exact ⟨c • twGen i ζ, by rw [res_nsmul, res_twGen]⟩
  have key : ∀ s, pull _ (spMap f) (tw q i) 0 (e _ s) = e _ (Sec.res g s) := fun s => he g s
  have hfun : ⇑(pull _ (spMap f) (tw q i) 0) = e _ ∘ Sec.res g ∘ (e _).symm := by
    funext x
    obtain ⟨s, rfl⟩ := (e _).surjective x
    simp [key]
  rw [hfun]
  exact (e _).bijective.comp (hres.comp (e _).symm.bijective)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.NatRef

variable {R : Type} [CommRing R]

theorem cpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = CohomologyClass.mk _
  congr 1; ext1; simp [zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem cpull_inr_map {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) (I : Cx R) (n : ℤ) (x : CohomologyClass (mappingCone φ₂) I n) :
    cpull (mappingCone.inr φ₁) I n (cpull (mappingCone.map φ₁ φ₂ a b comm) I n x) =
      cpull b I n (cpull (mappingCone.inr φ₂) I n x) := by
  rw [← cpull_comp, ← cpull_comp]
  congr 2
  simp [mappingCone.map]

theorem cpull_map_fst {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) (I : Cx R) (n : ℤ) (x : CohomologyClass K₂ I n) :
    cpull (mappingCone.map φ₁ φ₂ a b comm) I (n + 1) (cpre (mappingCone.fst φ₂) I n (n + 1) (by omega) x) =
      cpre (mappingCone.fst φ₁) I n (n + 1) (by omega) (cpull a I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = CohomologyClass.mk _
  congr 1; ext1
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe]
  have key : (Cochain.ofHom (mappingCone.map φ₁ φ₂ a b comm)).comp (mappingCone.fst φ₂).1 (zero_add 1) =
      (mappingCone.fst φ₁).1.comp (Cochain.ofHom a) (add_zero 1) := by
    refine (mappingCone.ext_cochain_from_iff φ₁ 0 1 rfl).2 ⟨?_, ?_⟩
    · rw [← Cochain.comp_assoc _ _ _ (show -1 + 0 = -1 by omega) (zero_add 1) (by omega), ← Cochain.comp_assoc _ _ _ (show -1 + 1 = 0 by omega) (add_zero 1) (by omega)]
      simp [mappingCone.map, Cochain.comp_assoc_of_second_is_zero_cochain]
    · rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.comp_assoc_of_first_is_zero_cochain]
      simp [mappingCone.map, Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, key, Cochain.comp_assoc_of_second_is_zero_cochain]

end GlobalTheory.EtC.NatRef

namespace GlobalTheory.EtC.NatRef
variable {R : Type} [CommRing R]

theorem abstract_nat {K L K' L' : Cx R} (φ : K ⟶ L) (φ' : K' ⟶ L') (a : K' ⟶ K) (b : L' ⟶ L)
    (comm : φ' ≫ b = a ≫ φ) (I : Cx R) (n : ℤ)
    (hbij : Function.Bijective (cpull (mappingCone.map φ' φ a b comm) I (n + 1))) :
    ∃ δ : CohomologyClass K' I n →+ CohomologyClass L I (n + 1),
      Function.Exact δ (fun x : CohomologyClass L I (n + 1) => (cpull φ I (n + 1) x, cpull b I (n + 1) x)) ∧
      ∀ {K₂ L₂ : Cx R} (φ₂ : K₂ ⟶ L₂) (a₂ : K₂ ⟶ K') (b₂ : L₂ ⟶ L') (comm₂ : φ₂ ≫ b₂ = a₂ ≫ φ')
        (a₃ : K₂ ⟶ K) (b₃ : L₂ ⟶ L) (comm₃ : φ₂ ≫ b₃ = a₃ ≫ φ), a₂ ≫ a = a₃ → b₂ ≫ b = b₃ →
        Function.Injective (cpull (mappingCone.map φ₂ φ a₃ b₃ comm₃) I (n + 1)) →
        ∀ (w : CohomologyClass K' I n) (c : CohomologyClass K I n), cpull a₂ I n w = cpull a₃ I n c → δ w = 0 := by
  set m := mappingCone.map φ' φ a b comm
  let e := AddEquiv.ofBijective _ hbij
  have he : ∀ y, cpull m I (n + 1) (e.symm y) = y := e.apply_symm_apply
  have he' : ∀ r, e.symm (cpull m I (n + 1) r) = r := e.symm_apply_apply
  have P1 := (coneSeq_exact R φ I (n + 1)).1
  have P3 := (coneSeq_exact R φ' I n).2.2
  have P3φ := (coneSeq_exact R φ I n).2.2
  refine ⟨(cpull (mappingCone.inr φ) I (n + 1)).comp
    (e.symm.toAddMonoidHom.comp (cpre (mappingCone.fst φ') I n (n + 1) (by omega))), ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have hx1 : cpull φ I (n + 1) x = 0 := congrArg Prod.fst hx
      have hx2 : cpull b I (n + 1) x = 0 := congrArg Prod.snd hx
      obtain ⟨r, rfl⟩ := (P1 x).1 hx1
      have h0 : cpull (mappingCone.inr φ') I (n + 1) (cpull m I (n + 1) r) = 0 := by
        rw [cpull_inr_map]; exact hx2
      obtain ⟨w, hw⟩ := (P3 _).1 h0
      refine ⟨w, ?_⟩
      change cpull (mappingCone.inr φ) I (n + 1) (e.symm (cpre (mappingCone.fst φ') I n (n + 1) _ w)) = _
      rw [hw, he']
    · rintro ⟨w, rfl⟩
      refine Prod.ext ((P1 _).2 ⟨_, rfl⟩) ?_
      change cpull b I (n + 1) (cpull (mappingCone.inr φ) I (n + 1) (e.symm (cpre (mappingCone.fst φ') I n (n + 1) _ w))) = 0
      rw [← cpull_inr_map φ' φ a b comm, he]
      exact (P3 _).2 ⟨w, rfl⟩
  · intro K₂ L₂ φ₂ a₂ b₂ comm₂ a₃ b₃ comm₃ ha hb hinj w c hwc
    subst ha hb
    have hM : mappingCone.map φ₂ φ (a₂ ≫ a) (b₂ ≫ b) comm₃ =
        mappingCone.map φ₂ φ' a₂ b₂ comm₂ ≫ m := mappingCone.map_comp φ₂ φ' φ a₂ b₂ comm₂ a b comm
    have hr : e.symm (cpre (mappingCone.fst φ') I n (n + 1) (by omega) w) =
        cpre (mappingCone.fst φ) I n (n + 1) (by omega) c := by
      apply hinj
      rw [cpull_map_fst, ← hwc, hM, cpull_comp, he, cpull_map_fst]
    change cpull (mappingCone.inr φ) I (n + 1) (e.symm (cpre (mappingCone.fst φ') I n (n + 1) _ w)) = 0
    rw [hr]
    exact (P3φ _).2 ⟨c, rfl⟩

end GlobalTheory.EtC.NatRef

namespace GlobalTheory.EtC


open NatRef in
theorem excision_boundary_natural_refine : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ), ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A₂ : Type) [CommRing A₂] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂], IsExcisionNbhd A A₂ f → ∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ∀ (w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i) (b : Ht q (sp (Localization.Away f)) n i), pull _ (spMap φ) _ _ w = pull _ (spMap (Localization.awayMap (algebraMap A A₂) f)) _ _ b → δ w = 0 := by
  intro q A A' _ _ _ f hN n i
  have hbij : ∀ (B : Type) [CommRing B] [Algebra A B], IsExcisionNbhd A B f →
      Function.Bijective (cpull (excisionConeMap (ZMod q) A B f) (res (ZMod q) (tw q i)) (n + 1)) := by
    intro B _ _ hB
    haveI := GlobalTheory.T.excisionConeMap_quasiIso' (ZMod q) A B f hB
    exact quasiIso_hypercohomology_bijective' (ZMod q) (excisionConeMap (ZMod q) A B f) (tw q i) (n + 1)
  obtain ⟨δ, hex, hnat⟩ := abstract_nat _ _ _ _ (excision_square_comm (ZMod q) A A' f) (res (ZMod q) (tw q i)) n
    (hbij A' hN)
  refine ⟨δ, hex, ?_⟩
  intro A₂ _ _ _ _ h₂ φ hφ w b hwb
  refine hnat ((chains (ZMod q)).map (spMap (algebraMap A₂ (Localization.Away (algebraMap A A₂ f)))))
    ((chains (ZMod q)).map (spMap φ)) ((chains (ZMod q)).map (spMap (algebraMap A' A₂))) ?_ _ _
    (excision_square_comm (ZMod q) A A₂ f) ?_ ?_ (hbij A₂ h₂).1 w b hwb
  · rw [chains_spMap_comp, chains_spMap_comp, hφ]
  · rw [chains_spMap_comp]
    congr 2
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    rw [RingHom.comp_assoc, awayMap_comp_algebraMap, awayMap_comp_algebraMap, ← RingHom.comp_assoc, hφ,
      RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  · rw [chains_spMap_comp, ← IsScalarTower.algebraMap_eq]

end GlobalTheory.EtC
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsGrpPullback isGrpPullback_pullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme)
open GlobalTheory.Cris (dp0)
open GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DeRhamCpl

open GlobalTheory.PDiv (ModPow)

section Rings

variable (p : ℕ) (O : Type) [CommRing O]

end Rings

section BaseChange

variable {O O' B B' : Type} [CommRing O] [CommRing O'] [CommRing B] [CommRing B']

abbrev bcObj (a : O →+* B) (A : Over (Sp O)) : Over (Sp B) := (Over.pullback (spMap a)).obj A

instance bcObj.instGrpObj (a : O →+* B) (A : Over (Sp O)) [GrpObj A] : GrpObj (bcObj a A) :=
  letI : (Over.pullback (spMap a)).Monoidal :=
    (Over.instBraidedPullback (f := spMap a)).toMonoidal
  Functor.grpObjObj (F := Over.pullback (spMap a))

end BaseChange

section Levels

variable (p : ℕ) {O : Type} [CommRing O]

variable {p} {A : Over (Sp O)} [GrpObj A]


end Levels

abbrev Family (p : ℕ) : Type 1 :=
  ∀ ⦃R : Type⦄ [CommRing R], IsAdicComplete (Ideal.span {(p : R)}) R →
    ∀ ⦃A : Over (Sp R)⦄ [GrpObj A],
      IsAbelianScheme A → (∃ g : ℕ, SmoothOfRelativeDimension g A.hom) →
      ∀ ⦃G : PDivGroup p R⦄, G.TorsionTower A → (primDR A ≃ₗ[R] G.RigExt)

variable {p : ℕ} (E : Family p)

end GlobalTheory.DeRhamCpl
end
end
