module

public import Development.EtaleCohomology.TateTwists.Bundle011
public import Development.EtaleCohomology.TateTwists.Bundle020
public import Development.EtaleCohomology.TateTwists.Bundle021
public import Development.EtaleCohomology.TateTwists.Bundle019
import Development.EtaleCohomology.TateTwists.Bundle013
public import Development.EtaleCohomology.TateTwists.Bundle022
public import Development.EtaleCohomology.TateTwists.Bundle025
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
public import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

namespace LateralTheory.Fin.EtaleTwistResolutionUniversalExtension
theorem etale_twisted_resolution_sections_injective : LateralTheory.EtaleFoundations.EtaleInjectiveSheafSectionsInjective := by
  apply LateralTheory.EtaleFoundations.etale_injective_sheaf_sections_injective_holds
theorem etale_twisted_resolution_quasiIso_flat : LateralTheory.EtaleFoundations.ZModInjectiveModuleFlat := by
  apply LateralTheory.EtaleFoundations.zmod_injective_module_flat_holds
theorem etale_twisted_resolution_exists_of_flat_sections : LateralTheory.EtaleFoundations.EtaleTwistResolutionUniversalExtension := by
  apply LateralTheory.EtaleFoundations.etale_tate_twist_resolution_universal_of_injective_sections_and_zmod_f <;> first | exact etale_twisted_resolution_sections_injective | exact etale_twisted_resolution_quasiIso_flat
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleTwistResolutionUniversalExtension := etale_twisted_resolution_exists_of_flat_sections
end LateralTheory.Fin.EtaleTwistResolutionUniversalExtension
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.EtaleFoundations.PrimLocKumPf

noncomputable abbrev kpol {A : Type} [CommRing A] (q : ℕ) (u : A) : A[X] := X ^ q - C u

theorem kpol_monic {A : Type} [CommRing A] (q : ℕ) [NeZero q] (u : A) : (kpol q u).Monic :=
  monic_X_pow_sub_C u (NeZero.ne q)

theorem kpol_natDegree {A : Type} [CommRing A] [Nontrivial A] (q : ℕ) [NeZero q] (u : A) :
    (kpol q u).natDegree = q :=
  natDegree_X_pow_sub_C _

theorem root_pow {A : Type} [CommRing A] (q : ℕ) (u : A) :
    AdjoinRoot.root (kpol q u) ^ q = algebraMap A (AdjoinRoot (kpol q u)) u := by
  have h := AdjoinRoot.eval₂_root (kpol q u)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [← AdjoinRoot.algebraMap_eq] at h
  exact sub_eq_zero.mp h

theorem root_isUnit {A : Type} [CommRing A] (q : ℕ) [NeZero q] (u : Aˣ) :
    IsUnit (AdjoinRoot.root (kpol q (u : A))) := by
  have h : IsUnit (AdjoinRoot.root (kpol q (u : A)) ^ q) := by
    rw [root_pow]; exact u.isUnit.map _
  exact (isUnit_pow_iff (NeZero.ne q)).mp h

theorem deriv_isUnit {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) (u : Aˣ) :
    IsUnit (AdjoinRoot.mk (kpol q (u : A)) (derivative (kpol q (u : A)))) := by
  have hd : derivative (kpol q (u : A)) = C (q : A) * X ^ (q - 1) := by
    simp [kpol, derivative_X_pow]
  rw [hd, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
  refine IsUnit.mul (hq.map _) ?_
  exact (root_isUnit q u).pow _

theorem etale_kum {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) (u : Aˣ) :
    Algebra.Etale A (AdjoinRoot (kpol q (u : A))) :=
  let P : StandardEtalePair A := ⟨kpol q (u : A), kpol_monic q _, derivative (kpol q (u : A)), 1, 0, 1, by simp⟩
  .of_equiv (P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit _ (Localization.Away (AdjoinRoot.mk P.f (derivative (kpol q (u : A))))) _
      (deriv_isUnit q hq u)).symm.restrictScalars A))

theorem ff_kum {A : Type} [CommRing A] [Nontrivial A] (q : ℕ) [NeZero q] (u : A) :
    Module.FaithfullyFlat A (AdjoinRoot (kpol q u)) := by
  have hf := kpol_monic q u
  have : Module.Free A (AdjoinRoot (kpol q u)) := hf.free_adjoinRoot
  have : Module.Finite A (AdjoinRoot (kpol q u)) := hf.finite_adjoinRoot
  have hr : Module.finrank A (AdjoinRoot (kpol q u)) = q := by
    rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasis' hf).basis, Fintype.card_fin]
    exact kpol_natDegree q u
  have : Nontrivial (AdjoinRoot (kpol q u)) :=
    Module.nontrivial_of_finrank_pos (R := A) (by rw [hr]; exact Nat.pos_of_neZero q)
  infer_instance

theorem mono_kum (q : ℕ) {U : Scheme.{0}} (u : (Γ(U, ⊤))ˣ) :
    ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
    (∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u) →
    ∃ v : (Γ(W, ⊤))ˣ, v ^ q = Units.map (k ≫ g).appTop.hom.toMonoidHom u := by
  rintro V W g k ⟨v, hv⟩
  refine ⟨Units.map k.appTop.hom.toMonoidHom v, ?_⟩
  rw [← map_pow, hv]
  ext
  simp <;> rfl

theorem pt (q : ℕ) [NeZero q] (U : Scheme.{0}) (hq : IsUnit (q : Γ(U, ⊤))) (u : (Γ(U, ⊤))ˣ)
    (y : U) : ∃ (V : Scheme.{0}) (g : V ⟶ U), IsAffine V ∧ Etale g ∧ y ∈ Set.range g ∧
      ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u := by
  obtain ⟨W, hW, hyW, -⟩ : ∃ W : U.Opens, IsAffineOpen W ∧ y ∈ W ∧ W ≤ ⊤ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens) (Set.mem_univ y)
  obtain ⟨z, hz⟩ : y ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hyW
  let A : CommRingCat.{0} := Γ(U, W)
  have : Nontrivial A := by
    have := z.asIdeal.ne_top_iff_one.mp z.isPrime.ne_top
    exact ⟨⟨1, 0, fun h => this (h ▸ z.asIdeal.zero_mem)⟩⟩
  let ρ : Γ(U, ⊤) →+* A := (Scheme.ΓSpecIso A).hom.hom.comp hW.fromSpec.appTop.hom
  let u₁ : Aˣ := Units.map ρ.toMonoidHom u
  have hqA : IsUnit (q : A) := by simpa using hq.map ρ
  let B : CommRingCat.{0} := CommRingCat.of (AdjoinRoot (kpol q (u₁ : A)))
  let φ : A ⟶ B := CommRingCat.ofHom (algebraMap A (AdjoinRoot (kpol q (u₁ : A))))
  have he : Algebra.Etale A (AdjoinRoot (kpol q (u₁ : A))) := etale_kum q hqA u₁
  have hff : Module.FaithfullyFlat A (AdjoinRoot (kpol q (u₁ : A))) := ff_kum q _
  have hE : Etale (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr he
  have hS : Surjective (Spec.map φ) :=
    ((flat_and_surjective_SpecMap_iff φ).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hff)).2
  refine ⟨Spec B, Spec.map φ ≫ hW.fromSpec, inferInstance, inferInstance, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hS.surj z
    exact ⟨w, by simp [hw, hz]⟩
  · obtain ⟨r, hr⟩ := root_isUnit q u₁
    refine ⟨Units.map (Scheme.ΓSpecIso B).inv.hom.toMonoidHom r, ?_⟩
    ext
    set w : Γ(Spec A, ⊤) := hW.fromSpec.appTop.hom (u : Γ(U, ⊤)) with hw
    have hnat : (Scheme.ΓSpecIso B).hom.hom ((Spec.map φ).appTop.hom w) =
        φ.hom ((Scheme.ΓSpecIso A).hom.hom w) := by
      rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
    simp only [Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe]
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    show ((Scheme.ΓSpecIso B).inv.hom (r : AdjoinRoot (kpol q (u₁ : A)))) ^ q =
      (Spec.map φ).appTop.hom w
    rw [← map_pow, hr, root_pow]
    change (Scheme.ΓSpecIso B).inv.hom (φ.hom ((Scheme.ΓSpecIso A).hom.hom w)) = _
    rw [← hnat, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

end LateralTheory.EtaleFoundations.PrimLocKumPf

theorem LateralTheory.EtaleFoundations.etale_locally_kummer_roots_of_units_of_invertible_order : LateralTheory.EtaleFoundations.EtaleLocallyKummerRootsOfUnits := by
  intro q _ U hq u
  rw [LateralTheory.EtaleFoundations.etale_sheaf_section_locally_iff_of_presheaf_facts U _ (LateralTheory.EtaleFoundations.PrimLocKumPf.mono_kum q u)]
  exact LateralTheory.EtaleFoundations.PrimLocKumPf.pt q U hq u
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

def LateralTheory.EtaleFoundations.EtaleTensorPairingSectionsLocallyFiniteSums : Prop :=
  ∀ (R : Type) [CommRing R] (F G T : Shv R) (μ : Pair (sgl F) (sgl G) (sgl T)), μ.IsTensor →
    ∀ (U : Scheme.{0}) (y : Sec ((sgl T).X 0) U), Loc U fun V g => ∃ (n : ℕ) (a : Fin n → Sec F V) (b : Fin n → Sec G V),
      Sec.res g y = ∑ m, μ.mul V 0 0 0 (add_zero 0) (Sec.map (sglι F) (a m)) (Sec.map (sglι G) (b m))

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapHitsProductsLocally : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    i + j = k → ∀ φ : tw q k ⟶ T, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) →
    ∀ (U : Scheme.{0}) (a : Sec (tw q i) U) (b : Sec (tw q j) U), Loc U fun V g => ∃ c : Sec (tw q k) V,
      Sec.map (sglι T) (Sec.map φ c) =
        μ.mul V 0 0 0 (add_zero 0) (Sec.map (sglι _) (Sec.res g a)) (Sec.map (sglι _) (Sec.res g b))

namespace LateralTheory.EtaleFoundations.GenIsoSurjPf

variable {R : Type} [CommRing R]

theorem loc_mono' {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, h'⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (h' V g hg)⟩

theorem loc_top' {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem loc_and' {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, h⟩ := hP
  obtain ⟨T, hT, h'⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨h V g hg.1, h' V g hg.2⟩⟩

theorem loc_bind' {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U fun V g => Loc V fun W k => P W (k ≫ g)) : Loc U P := by
  obtain ⟨S, hS, h'⟩ := h
  choose T hT hP using h'
  refine ⟨Sieve.bind S.arrows fun V g hg => T V g hg, Scheme.etaleTopology.bind_covering hS hT, ?_⟩
  rintro W f ⟨V, k, g, hg, hk, rfl⟩
  exact hP V g hg W k hk

theorem loc_fin {U : Scheme.{0}} : ∀ (n : ℕ) (P : Fin n → ∀ V : Scheme.{0}, (V ⟶ U) → Prop),
    (∀ m, Loc U (P m)) → Loc U fun V g => ∀ m, P m V g
  | 0, _, _ => loc_top' fun _ _ m => m.elim0
  | n + 1, P, h => loc_mono' (loc_and' (h 0) (loc_fin n (fun m => P m.succ) fun m => h m.succ))
      fun _ _ hv m => Fin.cases hv.1 hv.2 m

theorem res_res {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res k (Sec.res g x) = Sec.res (k ≫ g) x := by
  simp [Sec.res]

theorem res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.hom.naturality g.op)) x
  simpa using this.symm

theorem map_id' {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := by
  simp [Sec.map]

theorem sglι_inj (F : Shv R) {U : Scheme.{0}} {x y : Sec F U}
    (h : Sec.map (sglι F) x = Sec.map (sglι F) y) : x = y := by
  have e : ∀ z : Sec F U, Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom
      (Sec.map (sglι F) z) = z := by
    intro z
    change Sec.map (sglι F ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom) z = z
    rw [sglι]
    erw [Iso.inv_hom_id]
    exact map_id' z
  rw [← e x, ← e y, h]

end LateralTheory.EtaleFoundations.GenIsoSurjPf

namespace LateralTheory.EtaleFoundations.GenIsoSurjPf

variable {R : Type} [CommRing R]

theorem sec_zero_of_isZero {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (x : Sec F U) : x = 0 := by
  have h1 : Sec.map (𝟙 F) x = Sec.map (0 : F ⟶ F) x := by rw [hF.eq_of_src (𝟙 F) 0]
  rw [map_id'] at h1
  rw [h1]
  simp [Sec.map]

theorem sglι_surj (F : Shv R) {U : Scheme.{0}} (y : Sec ((sgl F).X 0) U) : ∃ a : Sec F U, Sec.map (sglι F) a = y := by
  refine ⟨Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom y, ?_⟩
  change Sec.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫ sglι F) y = y
  rw [sglι]
  erw [Iso.hom_inv_id]
  exact map_id' y

def IsSum {F G T : Shv R} (μ : Pair (sgl F) (sgl G) (sgl T)) (V : Scheme.{0}) (z : Sec ((sgl T).X 0) V) : Prop :=
  ∃ (n : ℕ) (a : Fin n → Sec F V) (b : Fin n → Sec G V),
    z = ∑ m, μ.mul V 0 0 0 (add_zero 0) (Sec.map (sglι F) (a m)) (Sec.map (sglι G) (b m))

theorem isSum_zero {F G T : Shv R} (μ : Pair (sgl F) (sgl G) (sgl T)) (V : Scheme.{0}) : IsSum μ V 0 :=
  ⟨0, Fin.elim0, Fin.elim0, by simp⟩

theorem isSum_add {F G T : Shv R} (μ : Pair (sgl F) (sgl G) (sgl T)) (V : Scheme.{0}) {z w : Sec ((sgl T).X 0) V}
    (hz : IsSum μ V z) (hw : IsSum μ V w) : IsSum μ V (z + w) := by
  obtain ⟨n, a, b, rfl⟩ := hz
  obtain ⟨n', a', b', rfl⟩ := hw
  refine ⟨n + n', Fin.append a a', Fin.append b b', ?_⟩
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem isSum_lift {F G T : Shv R} (μ : Pair (sgl F) (sgl G) (sgl T)) (V : Scheme.{0})
    (x : Tens (sgl F) (sgl G) V 0) : IsSum μ V (μ.lift V 0 x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simpa using isSum_zero μ V
  | add x y hx hy => simpa using isSum_add μ V hx hy
  | of p t =>
    obtain ⟨⟨s, u⟩, hsu⟩ := p
    have hl : μ.lift V 0 (DirectSum.of _ ⟨⟨s, u⟩, hsu⟩ t) = TensorProduct.lift (μ.mul V s u 0 hsu) t := by
      simp [Pair.lift, ← DirectSum.lof_eq_of (ULift.{1} R)]
    rw [hl]
    clear hl
    induction t using TensorProduct.induction_on with
    | zero => simpa using isSum_zero μ V
    | add x y hx hy => simpa using isSum_add μ V hx hy
    | tmul a b =>
      simp only [TensorProduct.lift.tmul]
      by_cases hs : s = 0
      · subst hs
        have hu : u = 0 := by simpa using hsu
        subst hu
        obtain ⟨a', rfl⟩ := sglι_surj F a
        obtain ⟨b', rfl⟩ := sglι_surj G b
        exact ⟨1, fun _ => a', fun _ => b', by simp⟩
      · have ha : a = 0 := sec_zero_of_isZero
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F s hs) a
        rw [ha]
        simpa using isSum_zero μ V

theorem etale_tensor_pairing_sections_locally_finite_sums : LateralTheory.EtaleFoundations.EtaleTensorPairingSectionsLocallyFiniteSums := by
  intro R _ F G T μ hμ U y
  refine loc_mono' (hμ.1 U 0 y) fun V g ⟨x, hx⟩ => ?_
  obtain ⟨n, a, b, h⟩ := isSum_lift μ V x
  exact ⟨n, a, b, hx ▸ h⟩

end LateralTheory.EtaleFoundations.GenIsoSurjPf

open LateralTheory.EtaleFoundations.GenIsoSurjPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_locally_surjective_of_pairs (hp : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapHitsProductsLocally) : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapLocallySurjective := by
  intro q _ i j k T μ hμ hk φ hφ U b
  refine loc_bind' (loc_mono' (etale_tensor_pairing_sections_locally_finite_sums (ZMod q) _ _ _ μ hμ U (Sec.map (sglι T) b)) fun V g ⟨n, a, c, hy⟩ => ?_)
  refine loc_mono' (loc_fin n _ fun m => hp q i j k T μ hk φ hφ V (a m) (c m)) fun W h hW => ?_
  choose e he using hW
  refine ⟨∑ m, e m, sglι_inj T ?_⟩
  rw [← res_map, ← res_res, hy]

  simp only [map_sum, he, μ.nat, res_map]
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem awleib_ev_smul {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (u : ℤˣ)
    (α : Cochain ((chains R).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (u • α) p s h U x = u • ev α p s h U x := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · rw [one_smul, one_smul]
  · rw [Units.neg_smul, Units.neg_smul, one_smul, one_smul]
    unfold ev
    rw [Cochain.neg_v, Preadditive.comp_neg]
    rfl

def EtaleSimplicialCochainEqOfEvaluationsAgree : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {K : Cx R} {k : ℤ} (γ γ' : Cochain ((chains R).obj E) K k),
    (∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (U : Scheme.{0}) (x : Sx E N U), ev γ N w h U x = ev γ' N w h U x) →
    γ = γ'

def EtaleAlexanderWhitneyLeibnizZeroSimplexDegree : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k n₁ m₁ k₁ : ℤ} (hk : n + m = k)
    (hn : n + 1 = n₁) (hm : m + 1 = m₁) (hk₁ : n₁ + m = k₁) (hk₂ : n + m₁ = k₁)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k) (γ₁ γ₂ : Cochain ((chains R).obj E) K k₁),
    μ.IsAW hk α β γ → μ.IsAW hk₁ (δ n n₁ α) β γ₁ → μ.IsAW hk₂ α (δ m m₁ β) γ₂ →
    ∀ (w : ℤ) (h : -((0 : ℕ) : ℤ) + k₁ = w) (U : Scheme.{0}) (x : Sx E 0 U),
      ev (δ k k₁ γ) 0 w h U x = ev γ₁ 0 w h U x + n.negOnePow • ev γ₂ 0 w h U x

def EtaleAlexanderWhitneyLeibnizPositiveSimplexDegree : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k n₁ m₁ k₁ : ℤ} (hk : n + m = k)
    (hn : n + 1 = n₁) (hm : m + 1 = m₁) (hk₁ : n₁ + m = k₁) (hk₂ : n + m₁ = k₁)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k) (γ₁ γ₂ : Cochain ((chains R).obj E) K k₁),
    μ.IsAW hk α β γ → μ.IsAW hk₁ (δ n n₁ α) β γ₁ → μ.IsAW hk₂ α (δ m m₁ β) γ₂ →
    ∀ (P : ℕ) (w : ℤ) (h : -((P + 1 : ℕ) : ℤ) + k₁ = w) (U : Scheme.{0}) (x : Sx E (P + 1) U),
      ev (δ k k₁ γ) (P + 1) w h U x = ev γ₁ (P + 1) w h U x + n.negOnePow • ev γ₂ (P + 1) w h U x

theorem etale_zero_simplex_subface_zero_zero_eq_self {E : Spc} {U : Scheme.{0}} (x : Sx E 0 U) (h : 0 + 0 ≤ 0) : x.sub 0 0 h = x := by
  unfold Sx.sub
  have e : SimplexCategory.subinterval 0 0 h = 𝟙 _ := by
    ext i
    exact congrArg Fin.val (Subsingleton.elim (α := Fin 1) _ _)
  rw [e, op_id, E.map_id]
  rfl

theorem etale_alexander_whitney_cup_evaluation_degree_zero {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    {α : Cochain ((chains R).obj E) I n} {β : Cochain ((chains R).obj E) J m} {γ : Cochain ((chains R).obj E) K k}
    (ha : μ.IsAW hk α β γ) (s t w : ℤ) (hs : -((0 : ℕ) : ℤ) + n = s) (ht : -((0 : ℕ) : ℤ) + m = t)
    (hw : -((0 : ℕ) : ℤ) + k = w) (h : s + t = w) (U : Scheme.{0}) (x : Sx E 0 U) :
    ev γ 0 w hw U x = μ.mul U s t w h (ev α 0 s hs U x) (ev β 0 t ht U x) := by
  subst hs ht hw
  rw [ha 0 _ _ U x, Fin.sum_univ_one]
  simp only [Fin.val_zero, Nat.cast_zero, mul_zero, Int.negOnePow_zero, one_smul]
  rw [etale_zero_simplex_subface_zero_zero_eq_self]

theorem awleib_leib' {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0})
    (s t w s' t' w' : ℤ) (h : s + t = w) (hs : s + 1 = s') (ht : t + 1 = t') (hw : w + 1 = w')
    (h1 : s' + t = w') (h2 : s + t' = w') (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Sec.map (K.d w w') (μ.mul U s t w h a b) = μ.mul U s' t w' h1 (Sec.map (I.d s s') a) b +
      s.negOnePow • μ.mul U s t' w' h2 a (Sec.map (J.d t t') b) := by
  subst hs ht hw
  exact μ.leibniz U s t w h a b

def EtaleCochainDifferentialEvaluationDegreeZero : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n)
    (U : Scheme.{0}) (x : Sx E 0 U) (w w' : ℤ) (h : -((0 : ℕ) : ℤ) + n = w) (h' : -((0 : ℕ) : ℤ) + m = w'),
    ev (δ n m α) 0 w' h' U x = Sec.map (I.d w w') (ev α 0 w h U x)

theorem awleib_zero_of (hd : EtaleCochainDifferentialEvaluationDegreeZero) : EtaleAlexanderWhitneyLeibnizZeroSimplexDegree := by
  intro R _ I J K μ E n m k n₁ m₁ k₁ hk hn hm hk₁ hk₂ α β γ γ₁ γ₂ ha h1 h2 w h U x
  rw [hd R (by omega) γ U x (-((0 : ℕ) : ℤ) + k) w rfl h,
    etale_alexander_whitney_cup_evaluation_degree_zero μ hk ha (-((0 : ℕ) : ℤ) + n) (-((0 : ℕ) : ℤ) + m) _ rfl rfl rfl (by omega),
    awleib_leib' μ U _ _ _ (-((0 : ℕ) : ℤ) + n₁) (-((0 : ℕ) : ℤ) + m₁) w _ (by omega) (by omega) (by omega)
      (by omega) (by omega),
    etale_alexander_whitney_cup_evaluation_degree_zero μ hk₁ h1 (-((0 : ℕ) : ℤ) + n₁) (-((0 : ℕ) : ℤ) + m) w rfl rfl h (by omega),
    etale_alexander_whitney_cup_evaluation_degree_zero μ hk₂ h2 (-((0 : ℕ) : ℤ) + n) (-((0 : ℕ) : ℤ) + m₁) w rfl rfl h (by omega),
    hd R hn α U x _ _ rfl rfl, hd R hm β U x _ _ rfl rfl]
  simp

theorem etale_alexander_whitney_leibniz_of_ext_degree_zero_succ (h0 : EtaleSimplicialCochainEqOfEvaluationsAgree) (hd : EtaleCochainDifferentialEvaluationDegreeZero)
    (hs : EtaleAlexanderWhitneyLeibnizPositiveSimplexDegree) : EtaleAlexanderWhitneyCupLeibnizRule := by
  intro R _ I J K μ E n m k n₁ m₁ k₁ hk hn hm hk₁ hk₂ α β γ γ₁ γ₂ ha h1 h2
  apply h0 R
  intro N w h U x
  rw [ev_add', awleib_ev_smul]
  cases N with
  | zero => exact awleib_zero_of hd R μ hk hn hm hk₁ hk₂ α β γ γ₁ γ₂ ha h1 h2 w h U x
  | succ P => exact hs R μ hk hn hm hk₁ hk₂ α β γ γ₁ γ₂ ha h1 h2 P w h U x

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

def MuRootListProductOneSumEtaleLocallyZero : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (l : List (Prim q Γ(U, ⊤))), (l.map fun ζ => ζ.1).prod = 1 →
    Loc U fun _ g => ((twF q 1).map g.appTop).hom (l.map fun ζ => twGenR Γ(U, ⊤) ζ).sum = 0

theorem mu_root_relation_submodule_etale_locally_zero_of_root_lists (h : MuRootListProductOneSumEtaleLocallyZero) : MuRootRelationSubmoduleEtaleLocallyZero := by
  intro q _ U x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact h q U l hl
  | zero => exact ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨S, hS, hSa⟩ := ha
    obtain ⟨T, hT, hTb⟩ := hb
    refine ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ?_⟩
    have h1 : ((twF q 1).map g.appTop).hom a = 0 := hSa V g hg.1
    have h2 : ((twF q 1).map g.appTop).hom b = 0 := hTb V g hg.2
    show ((twF q 1).map g.appTop).hom (a + b) = 0
    rw [map_add (f := _), h1, h2, add_zero]
  | smul c a _ ha =>
    obtain ⟨S, hS, hSa⟩ := ha
    exact ⟨S, hS, fun V g hg => by
      have h1 : ((twF q 1).map g.appTop).hom a = 0 := hSa V g hg
      show ((twF q 1).map g.appTop).hom (c • a) = 0
      rw [map_smul, h1, smul_zero]⟩

theorem exists_etale_mono_mu_twist_quotient_of_root_lists_locally_zero (h : MuRootListProductOneSumEtaleLocallyZero) : ExistsEtaleMonoMuTwistKillingRootRelations :=
  exists_etale_mono_muTwist_quotient_of_locally_zero etale_sheafify_mono_of_kernel_locally_zero (mu_root_relation_submodule_etale_locally_zero_of_root_lists h)

end LateralTheory.EtaleFoundations
end
