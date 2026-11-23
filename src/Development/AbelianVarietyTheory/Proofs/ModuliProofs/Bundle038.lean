module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KS.PtDual

variable {X : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S]

def ev (v : Sp R ⟶ X) (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) : Γ(X, W) →+* R :=
  (v.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom

theorem ev_fromSpec (v : Sp R ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ v ⁻¹ᵁ U) :
    Spec.map (CommRingCat.ofHom (ev v U h)) ≫ hU.fromSpec = v := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec v hU (isAffineOpen_top _) h
  rw [ev, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, this, IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem ev_ext {v v' : Sp R ⟶ X} {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U)
    (e : ev v U h = ev v' U h') : v = v' := by
  rw [← ev_fromSpec v hU h, ← ev_fromSpec v' hU h', e]

theorem exists_ev {U : X.Opens} (hU : IsAffineOpen U) (φ : Γ(X, U) →+* R) :
    ∃ (v : Sp R ⟶ X) (h : ⊤ ≤ v ⁻¹ᵁ U), ev v U h = φ := by
  have h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
    exact le_top
  refine ⟨_, h, ?_⟩
  have := ev_fromSpec _ hU h
  rw [cancel_mono] at this
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)

theorem ev_res (v : Sp R ⟶ X) {W W' : X.Opens} (e : W' ≤ W) (h : ⊤ ≤ v ⁻¹ᵁ W) (h' : ⊤ ≤ v ⁻¹ᵁ W') (f : Γ(X, W)) :
    ev v W' h' (resG X e f) = ev v W h f := by
  have : X.presheaf.map (homOfLE e).op ≫ v.appLE W' ⊤ h' = v.appLE W ⊤ h := Scheme.Hom.map_appLE ..
  unfold ev
  rw [← this]
  rfl

theorem ev_comp (φ : R →+* S) (v : Sp R ⟶ X) (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (h' : ⊤ ≤ (spMap φ ≫ v) ⁻¹ᵁ W)
    (f : Γ(X, W)) : ev (spMap φ ≫ v) W h' f = φ (ev v W h f) := by
  have h1 : v.appLE W ⊤ h ≫ (spMap φ).appLE ⊤ ⊤ le_top = (spMap φ ≫ v).appLE W ⊤ h' :=
    Scheme.Hom.appLE_comp_appLE ..
  have h2 : (spMap φ).appLE ⊤ ⊤ le_top = (spMap φ).appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact (congrArg _ ((Sp S).presheaf.map_id _)).trans (Category.comp_id _)
  have h3 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  unfold ev
  rw [← h1, h2, Category.assoc]
  erw [h3]
  rfl

abbrev pt0 : Sp ℂ ⟶ Sp (DualNumber ℂ) := spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom

theorem le_preimage_iff (v : Sp (DualNumber ℂ) ⟶ X) (W : X.Opens) :
    ⊤ ≤ v ⁻¹ᵁ W ↔ ⊤ ≤ (pt0 ≫ v) ⁻¹ᵁ W := by
  rw [Scheme.Hom.comp_preimage]
  refine ⟨fun h p _ => h (Set.mem_univ _), fun h p _ => ?_⟩
  have hs : Function.Surjective (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hp : (p : PrimeSpectrum (DualNumber ℂ)) ∈
      Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    rw [range_comap_of_surjective _ _ hs]
    intro x hx
    have hx' : x.fst = 0 := hx
    refine (p : PrimeSpectrum (DualNumber ℂ)).isPrime.mem_of_pow_mem 2 ?_
    have : x ^ 2 = 0 := by
      ext <;> simp [pow_two, hx']
    rw [this]
    exact zero_mem _
  obtain ⟨q, rfl⟩ := hp
  exact h (Set.mem_univ q)

theorem fst_ev {y : Sp ℂ ⟶ X} {v : Sp (DualNumber ℂ) ⟶ X} (hv : pt0 ≫ v = y) (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W)
    (f : Γ(X, W)) : (ev v W h f).fst = valAt' y W f := by
  subst hv
  have h' := (le_preimage_iff v W).1 h
  rw [valAt'_eq_valAtHom _ h']
  exact (ev_comp _ v W h h' f).symm

def derHom {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) (W : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ W) :
    Γ(X, W) →+* DualNumber ℂ where
  toFun f := TrivSqZeroExt.inl (valAt' y W f) + TrivSqZeroExt.inr (δ W f)
  map_one' := by
    have := hδ.mul W h 1 1
    rw [_root_.mul_one, valAt'_one y h, _root_.one_mul, left_eq_add] at this
    ext <;> simp [valAt'_one y h, this]
  map_mul' a b := by
    ext
    · simp [valAt'_mul]
    · simp [hδ.mul W h, mul_comm]
  map_zero' := by
    have := hδ.add W h 0 0
    rw [add_zero, left_eq_add] at this
    ext <;> simp [valAt'_zero, this]
  map_add' a b := by
    ext
    · simp [valAt'_add]
    · simp [hδ.add W h]

theorem fst_derHom {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) (W : X.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (f : Γ(X, W)) : (derHom hδ W h f).fst = valAt' y W f := by
  simp [derHom]

theorem snd_derHom {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) (W : X.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (f : Γ(X, W)) : (derHom hδ W h f).snd = δ W f := by
  simp [derHom]

theorem derHom_res {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) {W W' : X.Opens} (e : W' ≤ W)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (h' : ⊤ ≤ y ⁻¹ᵁ W') (f : Γ(X, W)) : derHom hδ W' h' (resG X e f) = derHom hδ W h f := by
  ext
  · rw [fst_derHom, fst_derHom, valAt'_res y e f h']
  · rw [snd_derHom, snd_derHom, hδ.res W W' e h']

theorem exists_affine (y : Sp ℂ ⟶ X) : ∃ U : X.Opens, IsAffineOpen U ∧ ⊤ ≤ y ⁻¹ᵁ U := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (x := y (default : PrimeSpectrum ℂ)) (U := ⊤) trivial
  exact ⟨U, hU, (top_le_preimage_iff_mem y U).2 hy⟩

theorem ev_eq_derHom {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) {v : Sp (DualNumber ℂ) ⟶ X}
    (hv : pt0 ≫ v = y) {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U)
    (e : ev v U h = derHom hδ U h') (W : X.Opens) (k : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)) : (ev v W k f).snd = δ W f := by
  have k' : ⊤ ≤ y ⁻¹ᵁ W := hv ▸ (le_preimage_iff v W).1 k
  obtain ⟨g, hg, hy⟩ := hU.exists_basicOpen_le (V := W) ⟨_, (top_le_preimage_iff_mem y W).1 k'⟩
    ((top_le_preimage_iff_mem y U).1 h')
  have l' : ⊤ ≤ y ⁻¹ᵁ X.basicOpen g := (top_le_preimage_iff_mem y _).2 hy
  have l : ⊤ ≤ v ⁻¹ᵁ X.basicOpen g := (le_preimage_iff v _).2 (hv ▸ l')
  have := hU.isLocalization_basicOpen g
  have e' : ev v _ l = derHom hδ _ l' := by
    refine IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext fun a => ?_)
    refine (ev_res v (X.basicOpen_le g) h l a).trans ?_
    rw [e]
    exact (derHom_res hδ (X.basicOpen_le g) h' l' a).symm
  rw [← ev_res v hg k l, e', derHom_res hδ hg k' l', snd_derHom]

open Classical in
theorem exists_ptDer {y : Sp ℂ ⟶ X} {v : Sp (DualNumber ℂ) ⟶ X} (hv : pt0 ≫ v = y) :
    ∃ δ, PtDer y δ ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), (ev v W h f).snd = δ W f := by
  have H : ∀ W, ⊤ ≤ y ⁻¹ᵁ W → ⊤ ≤ v ⁻¹ᵁ W := fun W h => (le_preimage_iff v _).2 (hv ▸ h)
  refine ⟨fun W f => if h : ⊤ ≤ v ⁻¹ᵁ W then (ev v W h f).snd else 0, ⟨?_, ?_, ?_⟩, fun W h f => ?_⟩
  · intro W h f f'
    simp only [dif_pos (H W h), map_add (f := _), TrivSqZeroExt.snd_add]
  · intro W h f f'
    simp only [dif_pos (H W h), map_mul, DualNumber.snd_mul, fst_ev hv]
    ring
  · intro W W' e h f
    have k := H W (top_le_preimage_mono y e h)
    simp only [dif_pos (H W' h), dif_pos k, ev_res v e k]
  · simp only [dif_pos h]

theorem existsUnique_point {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) :
    ∃! v : Sp (DualNumber ℂ) ⟶ X, pt0 ≫ v = y ∧
      ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), (ev v W h f).snd = δ W f := by
  obtain ⟨U, hU, h'⟩ := exists_affine y
  obtain ⟨v, h, e⟩ := exists_ev hU (derHom hδ U h')
  have hv : pt0 ≫ v = y := by
    refine ev_ext hU ((le_preimage_iff v U).1 h) h' (RingHom.ext fun f => ?_)
    rw [ev_comp _ v U h, e]
    exact (fst_derHom hδ U h' f).trans (valAt'_eq_valAtHom y h' f)
  refine ⟨v, ⟨hv, ev_eq_derHom hδ hv hU h h' e⟩, ?_⟩
  rintro w ⟨hw, hw'⟩
  have k : ⊤ ≤ w ⁻¹ᵁ U := (le_preimage_iff w _).2 (hw ▸ h')
  refine ev_ext hU k h (RingHom.ext fun f => ?_)
  rw [e]
  ext
  · rw [fst_ev hw, fst_derHom]
  · rw [hw', snd_derHom]

end GlobalTheory.KS.PtDual

namespace GlobalTheory.KS

theorem ptDer_iff_dualPoint : ∀ (X : Scheme.{0}) (y : Sp ℂ ⟶ X), (∀ δ, PtDer y δ → ∃! v : Sp (DualNumber ℂ) ⟶ X, (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v = y ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE W ⊤ h).hom f)) = δ W f) ∧ ∀ v : Sp (DualNumber ℂ) ⟶ X, (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v = y → ∃ δ, PtDer y δ ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE W ⊤ h).hom f)) = δ W f :=
  fun _ _ => ⟨fun _ hδ => PtDual.existsUnique_point hδ, fun _ hv => PtDual.exists_ptDer hv⟩

end GlobalTheory.KS
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM

theorem stalkMap_germ_appLE {Y Z : Scheme.{0}} (f : Z ⟶ Y) (W : Y.Opens) (W' : Z.Opens) (h : W' ≤ f ⁻¹ᵁ W)
    (z : Z) (hz : z ∈ W') (s : Γ(Y, W)) :
    (f.stalkMap z).hom ((Y.presheaf.germ W (f z) (h hz)).hom s) =
      (Z.presheaf.germ W' z hz).hom ((f.appLE W W' h).hom s) := by
  have e : Y.presheaf.germ W (f z) (h hz) ≫ f.stalkMap z = f.appLE W W' h ≫ Z.presheaf.germ W' z hz := by
    erw [Scheme.Hom.germ_stalkMap]
    rw [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  exact congrArg (fun g => g.hom s) e

theorem sec_eq_of_openImm {Y : Scheme.{0}} (W : Y.Opens) (s t : Γ(Y, W))
    (H : ∀ p ∈ W, ∃ (Z : Scheme.{0}) (f : Z ⟶ Y) (_ : IsOpenImmersion f) (z : Z) (W' : Z.Opens)
      (h : W' ≤ f ⁻¹ᵁ W), z ∈ W' ∧ f z = p ∧ (f.appLE W W' h).hom s = (f.appLE W W' h).hom t) : s = t := by
  apply TopCat.Presheaf.section_ext Y.sheaf W s t
  intro p hp
  obtain ⟨Z, f, _, z, W', h, hz, rfl, e⟩ := H p hp
  apply (ConcreteCategory.injective_of_mono_of_preservesPullback (f.stalkMap z))
  have e1 := stalkMap_germ_appLE f W W' h z hz s
  have e2 := stalkMap_germ_appLE f W W' h z hz t
  rw [e] at e1
  exact e1.trans e2.symm

theorem sec_isUnit_of_pull {Y : Scheme.{0}} (W : Y.Opens) (s : Γ(Y, W))
    (H : ∀ p ∈ W, ∃ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (W' : Z.Opens)
      (h : W' ≤ f ⁻¹ᵁ W), z ∈ W' ∧ f z = p ∧ IsUnit ((f.appLE W W' h).hom s)) : IsUnit s := by
  apply Y.toRingedSpace.isUnit_of_isUnit_germ W s
  intro p hp
  obtain ⟨Z, f, z, W', h, hz, rfl, u⟩ := H p hp
  apply isUnit_of_map_unit (f.stalkMap z).hom
  rw [stalkMap_germ_appLE f W W' h z hz]
  exact u.map _

def spConst (R : Type) [CommRing R] (W : (Sp R).Opens) : R →+* Γ(Sp R, W) :=
  (resG (Sp R) (le_top : W ≤ ⊤)).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem appLE_spConst {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (W : (Sp R).Opens)
    (W' : (Sp R').Opens) (h : W' ≤ spMap φ ⁻¹ᵁ W) (r : R) :
    ((spMap φ).appLE W W' h).hom (spConst R W r) = spConst R' W' (φ r) := by
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
      (spMap φ).appLE W W' h =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫
        (Sp R').presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op := by
    rw [Scheme.Hom.map_appLE, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    rfl
  exact congrArg (fun g => g.hom r) key

private theorem mem_pull_U_iff' {X T : Scheme.{0}} (M : LB X) (y : T ⟶ X) (j : PUnit → M.ι) (p : T) :
    p ∈ (M.pull y).U j ↔ y p ∈ M.U (j PUnit.unit) := by
  unfold LB.pull LB.LinComb LB.wchart
  simp only [TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage]
  exact ⟨fun h => h _, fun h _ => h⟩

private theorem appLE_appLE_lemma_2 {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (V' : Z.Opens) (hV : V ≤ g ⁻¹ᵁ U) (hV' : V' ≤ f ⁻¹ᵁ V) (h3 : V' ≤ (f ≫ g) ⁻¹ᵁ U) (s : Γ(X, U)) :
    (f.appLE V V' hV').hom ((g.appLE U V hV).hom s) = ((f ≫ g).appLE U V' h3).hom s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]

private theorem appLE_resG_eq_resG_appLE {Y Z : Scheme.{0}} (f : Z ⟶ Y) {V1 V2 : Y.Opens} {W1 W2 : Z.Opens}
    (hV : V1 ≤ V2) (hW : W1 ≤ W2) (h1 : W1 ≤ f ⁻¹ᵁ V1) (h2 : W2 ≤ f ⁻¹ᵁ V2) (s : Γ(Y, V2)) :
    (f.appLE V1 W1 h1).hom (resG Y hV s) = resG Z hW ((f.appLE V2 W2 h2).hom s) := by
  simp only [resG]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]

private theorem pull_g_coe_eq_appLE_g {X T : Scheme.{0}} (M : LB X) (y : T ⟶ X) (j j' : PUnit → M.ι)
    (h : (M.pull y).U j ⊓ (M.pull y).U j' ≤ y ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) :
    (((M.pull y).g j j' : (Γ(T, (M.pull y).U j ⊓ (M.pull y).U j'))ˣ) : Γ(T, (M.pull y).U j ⊓ (M.pull y).U j')) =
      (y.appLE _ _ h).hom (M.g (j PUnit.unit) (j' PUnit.unit) : Γ(X, M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) := by
  unfold LB.pull LB.LinComb
  simp [pullU, res, Scheme.Hom.appLE]
  rfl

theorem secCoord_of_locally (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec) (R : Type) [CommRing R]
    (x : Sp R ⟶ X) (v : I → R) (_hM : M.IsLB) (hv : Ideal.span (Set.range v) = ⊤)
    (H : ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R'), IsOpenImmersion (spMap φ) ∧
      p ∈ Set.range (spMap φ) ∧ SecCoord M th (spMap φ ≫ x) (fun i => φ (v i))) :
    SecCoord M th x v := by
  have h1 : (1 : R) ∈ Ideal.span (Set.range v) := by rw [hv]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.1 h1
  have W1 : ∀ j : PUnit → M.ι, (M.pull x).U j ≤ x ⁻¹ᵁ M.U (j PUnit.unit) :=
    fun j p hp => (mem_pull_U_iff' M x j p).1 hp
  have W2 : ∀ {R' : Type} [CommRing R'] (φ : R →+* R') (j : PUnit → M.ι),
      (M.pull (spMap φ ≫ x)).U j ≤ spMap φ ⁻¹ᵁ (M.pull x).U j :=
    fun φ j z hz => (mem_pull_U_iff' M x j _).2 ((mem_pull_U_iff' M _ j z).1 hz)
  let t : ∀ j : PUnit → M.ι, Γ(Sp R, (M.pull x).U j) := fun j =>
    c.sum (fun i a => spConst R _ a * (x.appLE _ _ (W1 j)).hom ((th i).f (j PUnit.unit)))
  have pt : ∀ {R' : Type} [CommRing R'] (φ : R →+* R') (τ' : (M.pull (spMap φ ≫ x)).Gen),
      (∀ i j h, ((spMap φ ≫ x).appLE (M.U (j PUnit.unit)) ((M.pull (spMap φ ≫ x)).U j) h).hom
          ((th i).f (j PUnit.unit)) = spConst R' _ (φ (v i)) * (τ'.s j).val) →
      ∀ j, ((spMap φ).appLE _ _ (W2 φ j)).hom (t j) = (τ'.s j).val := by
    intro R' _ φ τ' hco j
    have e1 : ∀ i, ((spMap φ).appLE _ _ (W2 φ j)).hom
        (spConst R _ (c i) * (x.appLE _ _ (W1 j)).hom ((th i).f (j PUnit.unit))) =
        spConst R' _ (φ (c i) * φ (v i)) * (τ'.s j).val := by
      intro i
      rw [map_mul, appLE_spConst, appLE_appLE_lemma_2 (spMap φ) x _ _ _ (W1 j) (W2 φ j)
        (fun p hp => (mem_pull_U_iff' M _ j p).1 hp), map_mul, _root_.mul_assoc]
      exact congrArg (spConst R' _ (φ (c i)) * ·) (hco i j (fun p hp => (mem_pull_U_iff' M _ j p).1 hp))
    have e2 : ∑ i ∈ c.support, φ (c i) * φ (v i) = 1 := by
      have := congrArg φ hc

      rw [map_one, Finsupp.sum, map_sum] at this
      simpa [map_mul] using this
    show ((spMap φ).appLE _ _ (W2 φ j)).hom (∑ i ∈ c.support, _) = _

    rw [map_sum, Finset.sum_congr rfl (fun i _ => e1 i), ← Finset.sum_mul, ← map_sum, e2, map_one, _root_.one_mul]
  have hu : ∀ j, IsUnit (t j) := by
    intro j
    apply sec_isUnit_of_pull
    intro p hp
    obtain ⟨R', _, φ, _, ⟨z, rfl⟩, τ', _, hco⟩ := H p
    refine ⟨Sp R', spMap φ, z, (M.pull (spMap φ ≫ x)).U j, W2 φ j, ?_, rfl, ?_⟩
    · exact (mem_pull_U_iff' M _ j z).2 ((mem_pull_U_iff' M x j _).1 hp)
    · rw [pt φ τ' hco j]; exact (τ'.s j).isUnit
  unfold SecCoord
  refine ⟨⟨fun j => (hu j).unit⟩, ?_, ?_⟩
  · intro i j
    apply Units.ext
    show resG _ inf_le_left (t i) = ((M.pull x).g i j).val * resG _ inf_le_right (t j)
    apply sec_eq_of_openImm
    intro p hp
    obtain ⟨R', _, φ, hoi, ⟨z, rfl⟩, τ', hg, hco⟩ := H p
    have Wi : (M.pull (spMap φ ≫ x)).U i ⊓ (M.pull (spMap φ ≫ x)).U j ≤
        spMap φ ⁻¹ᵁ ((M.pull x).U i ⊓ (M.pull x).U j) := fun z hz => ⟨W2 φ i hz.1, W2 φ j hz.2⟩
    refine ⟨Sp R', spMap φ, hoi, z, _, Wi, ?_, rfl, ?_⟩
    · exact ⟨(mem_pull_U_iff' M _ i z).2 ((mem_pull_U_iff' M x i _).1 hp.1),
        (mem_pull_U_iff' M _ j z).2 ((mem_pull_U_iff' M x j _).1 hp.2)⟩
    · rw [map_mul, appLE_resG_eq_resG_appLE (spMap φ) inf_le_left inf_le_left Wi (W2 φ i),
        appLE_resG_eq_resG_appLE (spMap φ) inf_le_right inf_le_right Wi (W2 φ j), pt φ τ' hco i, pt φ τ' hco j]
      have h3 : (M.pull (spMap φ ≫ x)).U i ⊓ (M.pull (spMap φ ≫ x)).U j ≤
          (spMap φ ≫ x) ⁻¹ᵁ (M.U (i PUnit.unit) ⊓ M.U (j PUnit.unit)) :=
        fun q hq => ⟨(mem_pull_U_iff' M _ i q).1 hq.1, (mem_pull_U_iff' M _ j q).1 hq.2⟩
      rw [pull_g_coe_eq_appLE_g M x i j (fun q hq => ⟨W1 i hq.1, W1 j hq.2⟩)]
      erw [appLE_appLE_lemma_2 (spMap φ) x _ _ _ _ Wi h3, ← pull_g_coe_eq_appLE_g M (spMap φ ≫ x) i j h3]
      exact congrArg Units.val (hg i j)
  · intro i j h
    show _ = spConst R _ (v i) * t j
    apply sec_eq_of_openImm
    intro p hp
    obtain ⟨R', _, φ, hoi, ⟨z, rfl⟩, τ', _, hco⟩ := H p
    refine ⟨Sp R', spMap φ, hoi, z, _, W2 φ j, ?_, rfl, ?_⟩
    · exact (mem_pull_U_iff' M _ j z).2 ((mem_pull_U_iff' M x j _).1 hp)
    · rw [map_mul, appLE_spConst, pt φ τ' hco j, appLE_appLE_lemma_2 (spMap φ) x _ _ _ h (W2 φ j)
        (fun p hp => (mem_pull_U_iff' M _ j p).1 hp)]
      exact hco i j (fun p hp => (mem_pull_U_iff' M _ j p).1 hp)

end GlobalTheory.ZM
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory


open MvPolynomial in
theorem homogeneousComponent_mul_mem_span_degree {K σ : Type} [Field K] (I : Ideal (MvPolynomial σ K)) {d₀ d e : ℕ}
    (h₀ : d₀ ≤ d) (he : d ≤ e) {F : MvPolynomial σ K} (hF : F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d₀})
    (a : MvPolynomial σ K) :
    homogeneousComponent e (a * F) ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d} := by
  induction hF using Submodule.span_induction generalizing a with
  | mem G hG =>
    obtain ⟨hGI, hG⟩ := hG
    induction a using MvPolynomial.induction_on' with
    | monomial m c =>
      have hm : (monomial m c * G).IsHomogeneous (m.degree + d₀) :=
        (isHomogeneous_monomial c rfl).mul hG
      rw [homogeneousComponent_of_mem hm]
      split_ifs with h
      · obtain ⟨m₂, hle, hdeg⟩ := Finsupp.exists_le_degree_eq m (d - d₀) (by omega)
        obtain ⟨m₁, rfl⟩ := exists_add_of_le hle
        have : (monomial (m₂ + m₁) c : MvPolynomial σ K) * G = monomial m₁ c * (monomial m₂ 1 * G) := by
          rw [← _root_.mul_assoc, monomial_mul, _root_.mul_one, add_comm]
        rw [this]
        refine Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨I.mul_mem_left _ hGI, ?_⟩)
        have h2 := (isHomogeneous_monomial (1 : K) hdeg).mul hG
        rwa [Nat.sub_add_cancel h₀] at h2
      · exact Ideal.zero_mem _
    | add a b ha hb => rw [add_mul, map_add (f := _)]; exact Ideal.add_mem _ ha hb
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, map_add (f := _)]; exact Ideal.add_mem _ (hx a) (hy a)
  | smul r x _ hx => rw [smul_eq_mul, ← _root_.mul_assoc]; exact hx _

theorem cutBy_of_regular_of_zeroEstimate : ∀ (K σ Hh : Type) [Field K] (I : Ideal (MvPolynomial σ K)) (Q : Polynomial ℚ) (d₀ d : ℕ) (p : Hh → σ → K), d₀ ≤ d → (∀ e ≥ d₀, (dimDeg I e : ℚ) = Q.eval (e : ℚ) ∧ ∀ F ∈ I, F.IsHomogeneous e → F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d₀}) → (∀ F ∈ I, ∀ h, MvPolynomial.eval (p h) F = 0) → (∀ F : MvPolynomial σ K, F.IsHomogeneous d → (∀ h, MvPolynomial.eval (p h) F = 0) → F ∈ I) → CutBy I Q d p := by
  intro K σ Hh _ I Q d₀ d p h₀ hreg hvan hzero e he
  have hV : vanIdeal d p = Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d} := by
    unfold vanIdeal
    congr 1
    ext F
    exact ⟨fun h => ⟨hzero F h.1 h.2, h.1⟩, fun h => ⟨h.2, hvan F h.1⟩⟩
  refine ⟨(hreg e (h₀.trans he)).1, fun F hF => ⟨fun hI => ?_, fun h => ?_⟩⟩
  · have h := homogeneousComponent_mul_mem_span_degree I h₀ he ((hreg e (h₀.trans he)).2 F hI hF) 1
    rw [_root_.one_mul, MvPolynomial.homogeneousComponent_of_mem hF, if_pos rfl] at h
    rwa [hV]
  · rw [hV] at h
    exact (Ideal.span_le.2 fun G (hG : G ∈ {G : MvPolynomial σ K | G ∈ I ∧ G.IsHomogeneous d}) => hG.1) h

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.EmbedLocal

theorem isPullback_whisker {S : Scheme.{0}} (A : Over S) {T T' : Over S} (h : T' ⟶ T) :
    IsPullback (h ▷ A).left (fst T' A).left (fst T A).left h.left := by
  have h1 : IsPullback (snd T A).left (fst T A).left A.hom T.hom := (IsPullback.of_hasPullback T.hom A.hom).flip
  have h2 : IsPullback (snd T' A).left (fst T' A).left A.hom T'.hom := (IsPullback.of_hasPullback T'.hom A.hom).flip
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerRight_snd, Over.w h]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerRight_fst]

theorem of_parts
    (hex : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S), Odd N' → m ∣ N' → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (σ : _), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ t.Emb m (Over.mk (spMap φ ≫ x)) σ)
    (hpb : Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (T T' : Over S) (h : T' ⟶ T) σ, IsAffine T.left → IsAffine T'.left → t.Emb m T σ → ∃ σ', t.Emb m T' σ' ∧ ∀ (R : Type) [CommRing R] (y : Sp R ⟶ (T' ⊗ t.A).left) (w : Ix g (N' ^ 2) → R), SecCoord _ σ' y w ↔ SecCoord _ σ (y ≫ (h ▷ t.A).left) w)
    (hspan : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) σ, Odd N' → m ∣ N' → 2 ≤ m → t.Emb m (Over.mk x) σ → Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun a => (Out.SecM.ofSec t.A (σ a) : Out.SecM t.A t.L ((m : ℤ) ^ 2) (Over.mk x))) = ⊤)
    (hva : Out.Laws → Out.Laws2 → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (k : ℤ) (I : Type) [Finite I] (σ : I → LB.Sec (Out.LPow P.A P.L k (Over.mk x))), 4 ≤ k → Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun a => (Out.SecM.ofSec P.A (σ a) : Out.SecM P.A P.L k (Over.mk x))) = ⊤ → ProjRep (idealOf (fst (Over.mk x) P.A).left _ σ (𝟙 _)) (fst (Over.mk x) P.A).left _ σ)
    (hfib : ∀ (R σ : Type) [CommRing R] [Finite σ] (X : Scheme.{0}) (s : X ⟶ Sp R) (M : LB X) (th : σ → M.Sec), M.IsLB → IsProper s → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K), ∃ (X' : Scheme.{0}) (π : X' ⟶ X) (s' : X' ⟶ Sp K) (M' : LB X') (th' : σ → M'.Sec) (I : Ideal (MvPolynomial σ K)), IsPullback π s' s (spMap x) ∧ ProjRep I s' M' th' ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X') (w : σ → T), SecCoord M' th' y w ↔ SecCoord M th (y ≫ π) w) → ProjRep (idealOf s M th (𝟙 X)) s M th) :
    Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), m ^ 2 ∣ N' → 2 ≤ m → t.HasTh x v → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (σ : _), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ t.Emb m (Over.mk (spMap φ ≫ x)) σ ∧ ProjRep (idealOf (fst (Over.mk (spMap φ ≫ x)) t.A).left _ σ (𝟙 _)) (fst (Over.mk (spMap φ ≫ x)) t.A).left _ σ := by
  intro l1 l2 o _ g N' J b S s t m R _ x v hm h2 hth p
  have hodd : Odd N' := hth.1
  have hdvd : m ∣ N' := (dvd_pow_self m two_ne_zero).trans hm
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero 2 hodd.pos.ne'⟩
  obtain ⟨R', _, φ, σ, hφ, hp, hE⟩ := hex l1 l2 o g N' J b S s t m R x hodd hdvd p
  refine ⟨R', inferInstance, φ, σ, hφ, hp, hE, ?_⟩
  refine hfib R' (Ix g (N' ^ 2)) _ _ _ σ (LB.isLB_linComb t.isLB _ _) ?_ ?_
  · haveI := t.ab.proper
    exact inferInstanceAs (IsProper (pullback.fst (spMap φ ≫ x) t.A.hom))
  · intro K _ _ y
    let h : Over.mk (spMap y ≫ spMap φ ≫ x) ⟶ Over.mk (spMap φ ≫ x) := Over.homMk (spMap y) rfl
    obtain ⟨σ', hE', hc⟩ := hpb l2 o g N' J b S s t m _ _ h σ
      (inferInstanceAs (IsAffine (Spec _))) (inferInstanceAs (IsAffine (Spec _))) hE
    have hs := hspan l1 l2 o g N' J b S s t m K _ σ' hodd hdvd h2 hE'
    have h4 : (4 : ℤ) ≤ (m : ℤ) ^ 2 := by
      have : (2 : ℤ) ≤ m := by exact_mod_cast h2
      nlinarith
    exact ⟨_, (h ▷ t.A).left, _, _, σ', _, isPullback_whisker t.A h,
      hva l1 l2 S t.pol K _ _ _ σ' h4 hs, hc⟩

end GlobalTheory.ZM.EmbedLocal
end
