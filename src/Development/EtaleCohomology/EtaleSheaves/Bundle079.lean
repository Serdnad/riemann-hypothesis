module

public import Development.EtaleCohomology.EtaleSheaves.Bundle069
import Development.EtaleCohomology.EtaleSheaves.Bundle008
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Bundle001
public import Development.EtaleCohomology.EtaleSheaves.Bundle070
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Sites.EpiMono
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.E.LeafPreTensLocInjPf
open LateralTheory.E.LeafTensMonoPf LateralTheory.E.LeafTwPairExistsPf LateralTheory.E.LeafPairExtPf2

section
variable {R : Type} [CommRing R]

theorem sec_sgl_zero (F : Shv R) {s : ℤ} (hs : s ≠ 0) {U : Scheme.{0}} (a : Sec ((sgl F).X s) U) : a = 0 := by
  have hZ : IsZero ((sgl F).X s) := HomologicalComplex.isZero_single_obj_X _ _ _ _ hs
  have h1 : (𝟙 ((sgl F).X s)) = 0 := hZ.eq_of_src _ _
  have h2 : Sec.map (𝟙 ((sgl F).X s)) a = a := rfl
  rw [← h2, h1]
  rfl

theorem tens_zero_left (F : Shv R) {J : Cx R} {s t : ℤ} (hs : s ≠ 0) {U : Scheme.{0}}
    (z : Sec ((sgl F).X s) U ⊗[ULift.{1} R] Sec (J.X t) U) : z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul a b => rw [sec_sgl_zero F hs a, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

abbrev p0 (w : ℤ) : {p : ℤ × ℤ // p.1 + p.2 = w} := ⟨(0, w), by simp⟩

theorem tens_single (F : Shv R) {J : Cx R} {U : Scheme.{0}} {w : ℤ} (x : Tens (sgl F) J U w) :
    x = DirectSum.of _ (p0 w) (x (p0 w)) := by
  classical
  ext p
  by_cases hp : p = p0 w
  · subst hp; simp
  · rw [DirectSum.of_eq_of_ne _ _ _ hp]
    have : p.1.1 ≠ 0 := by
      intro h; apply hp; apply Subtype.ext; ext
      · exact h
      · simp; have := p.2; omega
    exact tens_zero_left F this _

theorem tens_res_of {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (t : Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) :
    Tens.res g w (DirectSum.of _ p t) =
      DirectSum.of _ p (TensorProduct.map ((I.X p.1.1).obj.map g.op).hom ((J.X p.1.2).obj.map g.op).hom t) := by
  classical
  rw [← DirectSum.lof_eq_of (ULift.{1} R)]
  unfold Tens.res
  rw [DirectSum.lmap_lof]
  rfl

theorem lift_of {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (t : Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) :
    μ.lift U w (DirectSum.of _ p t) = TensorProduct.lift (μ.mul U p.1.1 p.1.2 w p.2) t := by
  classical
  unfold Pair.lift
  exact DirectSum.toModule_lof (ULift.{1} R)
    (M := fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p t

end

section
variable {R : Type} [CommRing R]
theorem tens_res_comp {I J : Cx R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (w : ℤ) (z : Tens I J U w) :
    Tens.res (k ≫ g) w z = Tens.res k w (Tens.res g w z) := by
  classical
  have : (Tens.res (I := I) (J := J) (k ≫ g) w) = (Tens.res k w).comp (Tens.res g w) := by
    apply DirectSum.linearMap_ext; intro p
    apply TensorProduct.ext'; intro a b
    simp [Tens.res]
  exact LinearMap.congr_fun this z
end

theorem LeafPreTensLocInj_of (hS : LeafTw0LocSplit) : LeafPreTensLocInj := by
  intro q _ i T τ hτ U w x hx
  classical
  obtain ⟨S, hS0⟩ := TensorProduct.exists_finset (x (p0 w))
  set a : Fin S.card → Sec ((sgl (tw q 0)).X 0) U := fun k => (S.equivFin.symm k).1.1 with ha
  set b : Fin S.card → Sec ((res _ (tw q i)).X w) U := fun k => (S.equivFin.symm k).1.2 with hb
  have hxp : x (p0 w) = ∑ k, a k ⊗ₜ[ULift.{1} (ZMod q)] b k := by
    rw [hS0, ← Finset.sum_coe_sort S]
    exact (Equiv.sum_comp S.equivFin.symm (fun i : S => i.1.1 ⊗ₜ[ULift.{1} (ZMod q)] i.1.2)).symm
  have hx' : x = DirectSum.of _ (p0 w) (∑ k, a k ⊗ₜ[ULift.{1} (ZMod q)] b k) := by
    rw [← hxp]; exact tens_single _ x
  set y : Tens (res _ (tw q 0)) (res _ (tw q i)) U w :=
    DirectSum.of _ (p0 w) (∑ k, Sec.map ((resAug (tw q 0)).f 0) (a k) ⊗ₜ[ULift.{1} (ZMod q)] b k) with hydef
  have hy : τ.lift U w y = 0 := by
    rw [← hx, hx', hydef, lift_of, lift_of]
    simp [pre]
  refine loc_trans (hτ.2 U w y hy) ?_
  intro V g hg
  refine loc_trans (hS q V S.card (fun k => Sec.res g (a k))) ?_
  rintro W k ⟨e, c, hac, he⟩
  suffices h : Tens.res (k ≫ g) w x = 0 from
    ⟨⊤, GrothendieckTopology.top_mem _ W, fun W' k' _ => by dsimp only; rw [Category.assoc, tens_res_comp, h, map_zero]⟩
  set bb : Sec ((res _ (tw q i)).X w) W := ∑ j, c j • Sec.res (k ≫ g) (b j) with hbb
  have hres : Tens.res (k ≫ g) w x = DirectSum.of _ (p0 w) (e ⊗ₜ[ULift.{1} (ZMod q)] bb) := by

    rw [hx', tens_res_of, map_sum]
    congr 1
    rw [hbb, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.map_tmul, ← TensorProduct.smul_tmul]
    congr 1
    show Sec.res (k ≫ g) (a j) = c j • e
    rw [res_comp]; exact hac j
  have hy0 : Tens.res (k ≫ g) w y =
      DirectSum.of _ (p0 w) (Sec.map ((resAug (tw q 0)).f 0) e ⊗ₜ[ULift.{1} (ZMod q)] bb) := by

    rw [hydef, tens_res_of, map_sum]
    congr 1
    rw [hbb, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.map_tmul, ← TensorProduct.smul_tmul]
    congr 1
    show Sec.res (k ≫ g) (Sec.map ((resAug (tw q 0)).f 0) (a j)) = c j • Sec.map ((resAug (tw q 0)).f 0) e
    rw [res_map, res_comp, hac j]
    exact map_smul (((resAug (tw q 0)).f 0).hom.app (op W)).hom (c j) e
  have hg0 : Tens.res (k ≫ g) w y = 0 := by rw [tens_res_comp, hg, map_zero]
  have ht : Sec.map ((resAug (tw q 0)).f 0) e ⊗ₜ[ULift.{1} (ZMod q)] bb = 0 :=
    DirectSum.of_injective (p0 w) (hy0.symm.trans (hg0.trans (map_zero _).symm))
  rw [hres]
  rcases he with he | ⟨r, hr⟩
  · rw [he, TensorProduct.zero_tmul, map_zero]
  · have hbb0 : bb = 0 := by
      have := congrArg (fun z => TensorProduct.lid (ULift.{1} (ZMod q)) _ (TensorProduct.map r LinearMap.id z)) ht
      simpa [hr] using this
    rw [hbb0, TensorProduct.tmul_zero, map_zero]

end LateralTheory.E.LeafPreTensLocInjPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.H0Lifting
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShIsoPf

theorem exists_epi {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A] (M : DerivedCategory A) :
    ∃ (Z : A) (φ : (DerivedCategory.singleFunctor A 0).obj Z ⟶ M),
      Epi ((DerivedCategory.homologyFunctor A 0).map φ) := by
  let K := DerivedCategory.Q.objPreimage M
  let e := DerivedCategory.Q.objObjPreimageIso M
  let φ0 : (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj (K.cycles 0) ⟶ K :=
    HomologicalComplex.mkHomFromSingle (K.iCycles 0) (fun k _ => K.iCycles_d 0 k)
  have h1 : (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 (K.cycles 0)).inv ≫
      HomologicalComplex.cyclesMap φ0 0 = 𝟙 _ := by
    rw [← cancel_mono (K.iCycles 0)]
    simp [φ0]
  have h2 : Epi (HomologicalComplex.cyclesMap φ0 0) := epi_of_epi_fac h1
  have h3 : Epi (HomologicalComplex.homologyMap φ0 0) :=
    epi_of_epi_fac (HomologicalComplex.homologyπ_naturality φ0 0)
  have h4 : Epi ((DerivedCategory.homologyFunctor A 0).map (DerivedCategory.Q.map φ0)) := by
    have h := (DerivedCategory.homologyFunctorFactors A 0).inv.naturality φ0
    have h5 : Epi ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) 0).map φ0) := h3
    exact epi_of_epi_fac h.symm
  refine ⟨K.cycles 0, ((DerivedCategory.singleFunctorIsoCompQ A 0).app _).hom ≫ DerivedCategory.Q.map φ0 ≫ e.hom, ?_⟩
  rw [Functor.map_comp, Functor.map_comp]
  exact @epi_comp _ _ _ _ _ _ inferInstance _ (@epi_comp _ _ _ _ _ _ h4 _ inferInstance)

theorem transport {A D : Type*} [Category A] [Category D] (S : A ⥤ D) (H : D ⥤ A) (η : S ⋙ H ≅ 𝟭 A)
    {X Y Z : A} {M : D} (a : X ⟶ Y) (s : X ⟶ Z) (t : H.obj (S.obj Y) ⟶ H.obj M) (φ : S.obj Z ⟶ M)
    (h : a ≫ η.inv.app Y ≫ t = s ≫ η.inv.app Z ≫ H.map φ) : H.map (S.map a) ≫ t = H.map (S.map s ≫ φ) := by
  have h1 : a ≫ η.inv.app Y = η.inv.app X ≫ H.map (S.map a) := η.inv.naturality a
  have h2 : s ≫ η.inv.app Z = η.inv.app X ≫ H.map (S.map s) := η.inv.naturality s
  have h3 : η.inv.app X ≫ H.map (S.map a) ≫ t = η.inv.app X ≫ H.map (S.map s) ≫ H.map φ :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ t) h1).symm.trans ((Category.assoc _ _ _).trans
      (h.trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ H.map φ) h2).trans (Category.assoc _ _ _))))))
  rw [Functor.map_comp]
  exact (cancel_epi _).1 h3

abbrev PF (B : Scheme.{0}) (q : ℕ) : B.Etale ⥤ (B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) :=
  yoneda ⋙ (Functor.whiskeringRight B.Etaleᵒᵖ (Type 0) (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj
    (uliftFunctor.{1, 0} ⋙ ModuleCat.free (ULift.{1} (ZMod q)))

def gen {B : Scheme.{0}} (q : ℕ) {U V : B.Etale} (a : V ⟶ U) : ((PF B q).obj U).obj (op V) :=
  ModuleCat.freeMk (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V ⟶ U)) (ULift.up a)

theorem gen_res {B : Scheme.{0}} (q : ℕ) {U V W : B.Etale} (a : V ⟶ U) (b : W ⟶ V) :
    ((PF B q).obj U).map b.op (gen q a) = gen q (b ≫ a) :=
  ModuleCat.free_map_apply (R := ULift.{1} (ZMod q)) _ _

theorem gen_map {B : Scheme.{0}} (q : ℕ) {U V W : B.Etale} (a : V ⟶ U) (b : W ⟶ V) :
    ((PF B q).map a).app (op W) (gen q b) = gen q (b ≫ a) :=
  ModuleCat.free_map_apply (R := ULift.{1} (ZMod q)) _ _

theorem pf_ext {B : Scheme.{0}} {q : ℕ} {U : B.Etale} {F : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))}
    (f g : (PF B q).obj U ⟶ F) (h : f.app (op U) (gen q (𝟙 U)) = g.app (op U) (gen q (𝟙 U))) : f = g := by
  ext ⟨V⟩ : 2
  refine ModuleCat.free_hom_ext (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V ⟶ U)) ?_
  rintro ⟨a⟩
  change f.app (op V) (gen q a) = g.app (op V) (gen q a)
  have e : gen q a = ((PF B q).obj U).map a.op (gen q (𝟙 U)) := by rw [gen_res, Category.comp_id]
  rw [e, NatTrans.naturality_apply, NatTrans.naturality_apply, h]

theorem pf_exists {B : Scheme.{0}} {q : ℕ} {U : B.Etale} {F : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))}
    (s : F.obj (op U)) : ∃ f : (PF B q).obj U ⟶ F, f.app (op U) (gen q (𝟙 U)) = s := by
  let c : ∀ V : B.Etaleᵒᵖ, ((PF B q).obj U).obj V ⟶ F.obj V := fun V =>
    ModuleCat.freeDesc (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V.unop ⟶ U))
      (TypeCat.ofHom (fun a => F.map a.down.op s))
  have hc : ∀ (V : B.Etale) (a : V ⟶ U), c (op V) (gen q a) = F.map a.op s := fun V a =>
    ModuleCat.freeDesc_apply (R := ULift.{1} (ZMod q)) _ _
  refine ⟨⟨c, ?_⟩, ?_⟩
  · rintro ⟨V⟩ ⟨W⟩ ⟨b⟩
    refine ModuleCat.free_hom_ext (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V ⟶ U)) ?_
    rintro ⟨a⟩
    change c (op W) (((PF B q).obj U).map (Quiver.Hom.op b) (gen q a)) = F.map (Quiver.Hom.op b) (c (op V) (gen q a))
    rw [gen_res, hc, hc, op_comp, Functor.map_comp]
    rfl
  · change c (op U) _ = _
    rw [hc]
    simp

theorem loc_lift {B : Scheme.{0}} {q : ℕ} {F G : SShv B q} (π : F ⟶ G) [Epi π] (U : B.Etale)
    (t : (presheafToSheaf (EtTop B) _).obj ((PF B q).obj U) ⟶ G) :
    Cov U (fun U' a => ∃ s : (presheafToSheaf (EtTop B) _).obj ((PF B q).obj U') ⟶ F,
      (presheafToSheaf (EtTop B) _).map ((PF B q).map a) ≫ t = s ≫ π) := by
  have : EssentiallySmall.{1} B.Etale := inferInstance
  have hSC : (EtTop B).HasSheafCompose (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) :=
    hasSheafComposeEssentiallySmallSite (J := EtTop B) (A := ModuleCat.{1} (ULift.{1} (ZMod q))) (F := forget _)
  have hπ : Sheaf.IsLocallySurjective π := (Sheaf.isLocallySurjective_iff_epi' _ π).2 inferInstance
  let adj := sheafificationAdjunction (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))
  let t' : (PF B q).obj U ⟶ G.obj := adj.homEquiv _ _ t
  refine ⟨_, Presheaf.imageSieve_mem (EtTop B) π.hom (t'.app (op U) (gen q (𝟙 U))), ?_⟩
  rintro U' a ⟨z, hz⟩
  obtain ⟨f, hf⟩ := pf_exists (F := F.obj) z
  refine ⟨(adj.homEquiv _ F).symm f, ?_⟩
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  apply pf_ext
  change t'.app (op U') (((PF B q).map a).app (op U') (gen q (𝟙 U'))) = π.hom.app (op U') (f.app (op U') (gen q (𝟙 U')))
  rw [hf, hz, gen_map, ← NatTrans.naturality_apply, gen_res, Category.id_comp, Category.comp_id]

theorem etale_sheaf_epi_lifts_degree_zero_derived_maps_locally : EtaleDerivedDegreeZeroHomologyLocallyLifts := by
  intro B q M U t
  obtain ⟨Z, φ, hφ⟩ := exists_epi M
  let η := DerivedCategory.singleFunctorCompHomologyFunctorIso (SShv B q) 0
  let X : B.Etale ⥤ SShv B q := PF B q ⋙ presheafToSheaf (EtTop B) _
  let π : Z ⟶ (H0 B q).obj M := η.inv.app Z ≫ (H0 B q).map φ
  have hπ : Epi π := epi_comp _ _
  let t0 : X.obj U ⟶ (H0 B q).obj M := η.inv.app (X.obj U) ≫ t
  refine (loc_lift π U t0).mono ?_
  rintro U' a ⟨s, hs⟩
  refine ⟨(DerivedCategory.singleFunctor _ 0).map s ≫ φ, ?_⟩
  exact transport _ _ η (X.map a) s t φ hs

end LateralTheory.E.H0Lifting
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocSplitPf

def LeafTw0LocGen : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (n : ℕ) (a : Fin n → Sec (tw q 0) U),
  Loc U fun V g => ∃ (e : Sec (tw q 0) V) (c : Fin n → ULift.{1} (ZMod q)),
    (∀ k, Sec.res g (a k) = c k • e) ∧ (e = 0 ∨ ∃ ζ : Prim q Γ(V, ⊤), e = twGen 0 ζ)

theorem baerU (q : ℕ) [NeZero q] : Module.Baer (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q)) := by
  intro I g
  let J : Ideal (ZMod q) :=
    { carrier := {y | (ULift.up y : ULift.{1} (ZMod q)) ∈ I}
      add_mem' := fun {a b} ha hb => I.add_mem ha hb
      zero_mem' := I.zero_mem
      smul_mem' := fun c {y} hy => by
        have := I.smul_mem (ULift.up c) hy
        exact this }
  let g' : J →ₗ[ZMod q] ZMod q :=
    { toFun := fun y => (g ⟨ULift.up y.1, y.2⟩).down
      map_add' := fun a b => by
        have := g.map_add ⟨ULift.up a.1, a.2⟩ ⟨ULift.up b.1, b.2⟩
        exact congrArg ULift.down this
      map_smul' := fun c a => by
        have := g.map_smul (ULift.up c) ⟨ULift.up a.1, a.2⟩
        exact congrArg ULift.down this }
  obtain ⟨h, hh⟩ := KStar.Selmer.zmod_baer J g'
  refine ⟨{ toFun := fun x => ULift.up (h x.down)
            map_add' := fun a b => congrArg ULift.up (h.map_add a.down b.down)
            map_smul' := fun c a => congrArg ULift.up (h.map_smul c.down a.down) }, ?_⟩
  intro x hx
  exact congrArg ULift.up (hh x.down hx)

theorem retract (q : ℕ) [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (x : M)
    (hx : ∀ c : ULift.{1} (ZMod q), c • x = 0 → c = 0) :
    ∃ r : M →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q), r x = 1 := by
  let f : ULift.{1} (ZMod q) →ₗ[ULift.{1} (ZMod q)] M := LinearMap.toSpanSingleton _ _ x
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc; exact hx c hc
  obtain ⟨r, hr⟩ := (baerU q).extension_property f hf LinearMap.id
  refine ⟨r, ?_⟩
  have := LinearMap.congr_fun hr 1
  simpa [f] using this

def LeafTw0GenFree : Prop := ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)),
  twGen 0 ζ = 0 ∨ ∀ c : ULift.{1} (ZMod q), c • resGen 0 ζ = 0 → c = 0

theorem genSplit_of (hF : LeafTw0GenFree) (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)) :
    twGen 0 ζ = 0 ∨ ∃ r : Sec ((res _ (tw q 0)).X 0) V →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q), r (resGen 0 ζ) = 1 := by
  rcases hF q V ζ with h | h
  · exact Or.inl h
  · exact Or.inr (retract q _ h)

section
variable {R : Type} [CommRing R]

theorem map_comp' {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := by
  simp [Sec.map]

theorem map_res' {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  exact congrArg (fun f => ModuleCat.Hom.hom f x) (φ.hom.naturality g.op)
end

theorem LeafTw0LocSplit_of (h1 : LeafTw0LocGen) (h2 : LeafTw0GenFree) : LateralTheory.E.LeafTensMonoPf.LeafTw0LocSplit := by
  intro q _ U n a
  let I : (sgl (tw q 0)).X 0 ≅ tw q 0 := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q 0)
  obtain ⟨S, hS, hP⟩ := h1 q U n (fun k => Sec.map I.hom (a k))
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨e', c, hc, he'⟩ := hP V g hg
  have back : ∀ y : Sec ((sgl (tw q 0)).X 0) V, Sec.map I.inv (Sec.map I.hom y) = y := by
    intro y; refine (map_comp' I.hom I.inv y).symm.trans ?_; simp [Sec.map]
  refine ⟨Sec.map I.inv e', c, fun k => ?_, ?_⟩
  · rw [← back (Sec.res g (a k)), map_res' I.hom g (a k), hc k]
    exact map_smul (I.inv.hom.app (op V)).hom (c k) e'
  · rcases he' with rfl | ⟨ζ, rfl⟩
    · left; simp [Sec.map]
    · rcases genSplit_of h2 q V ζ with h0 | ⟨r, hr⟩
      · left; simp [h0, Sec.map]
      · right; refine ⟨r, ?_⟩
        convert hr using 2
        exact (map_comp' I.inv ((resAug (tw q 0)).f 0) (twGen 0 ζ)).symm

end LateralTheory.E.LeafTw0LocSplitPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing LateralTheory.E.ChartsGeom_vpaPf

namespace LateralTheory.E.GeometricData

theorem rA_top {A : Type} [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) :
    rA p ⊤ = p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom := by
  have h : p.appLE ⊤ ⊤ le_top = p.appTop := p.appLE_eq_app (U := ⊤)
  rw [rA, h]

theorem topInt : TopInt := by
  intro A _ _ Z p hIL
  obtain ⟨L, u, l, hu, hl, rfl⟩ := hIL
  have : UniversallyClosed u := (IsIntegralHom.iff_universallyClosed_and_isAffineHom.mp hu).1
  have : UniversallyClosed l := hl.1.toUniversallyClosed
  have h1 := isIntegral_appTop_of_universallyClosed (u ≫ l)
  rw [rA_top]
  refine RingHom.IsIntegral.trans _ _ ?_ h1
  exact RingHom.isIntegral_of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.surjective

theorem germ_res_eq {Z : Scheme.{0}} [IsIntegral Z] (U W : Z.Opens) (h : W ≤ U) [Nonempty U] [Nonempty W]
    (s : Γ(Z, U)) : Z.germToFunctionField W (Z.presheaf.map (homOfLE h).op s) = Z.germToFunctionField U s := by
  simp only [Scheme.germToFunctionField]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

theorem embedAffine : EmbedAffine := by
  intro A _ _ Z p hI hTop hAff
  obtain ⟨z⟩ : Nonempty Z := inferInstance
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨z, trivial⟩⟩
  have : Nonempty (⊤ ⊓ ⊤ : Z.Opens) := ⟨⟨z, trivial, trivial⟩⟩
  let φ : Γ(Z, ⊤) →+* Z.functionField := (Z.germToFunctionField ⊤).hom
  let _ : Algebra A Z.functionField := (φ.comp (rA p ⊤)).toAlgebra
  let B : Subalgebra A Z.functionField :=
    { toSubsemiring := φ.rangeS, algebraMap_mem' := fun a => ⟨rA p ⊤ a, rfl⟩ }
  have hBint : ∀ x ∈ B, IsIntegral A x := by
    rintro x ⟨g, rfl⟩
    obtain ⟨P, hP, hP0⟩ := hTop g
    refine ⟨P, hP, ?_⟩
    have : Polynomial.eval₂ (algebraMap A Z.functionField) (φ g) P = φ (Polynomial.eval₂ (rA p ⊤) g P) := by
      rw [Polynomial.hom_eval₂]; rfl
    rw [this, hP0, map_zero]
  have hDov : AdjoinInv B 1 = B := by
    apply le_antisymm
    · rw [AdjoinInv, Algebra.adjoin_le_iff]
      rintro x (hx | hx)
      · exact hx
      · rw [Set.mem_singleton_iff.mp hx, inv_one]; exact B.one_mem
    · intro x hx
      exact Algebra.subset_adjoin (Or.inl hx)
  refine ⟨Z.functionField, inferInstance, inferInstance, B, B, 1, ?_, fun x hx _ => hBint x hx, ?_⟩
  · refine ⟨one_ne_zero, B.one_mem, by rw [inv_one]; exact B.one_mem, ?_, ?_, ?_⟩
    · intro b hb; exact (hBint b hb).tower_top
    · intro b hb; exact (hBint b hb).tower_top
    · rw [hDov]
      apply le_antisymm
      · intro x hx; exact Algebra.subset_adjoin (Or.inl hx)
      · rw [Algebra.adjoin_le_iff]
        rintro x (hx | hx)
        · exact hx
        · rw [Set.mem_singleton_iff.mp hx]; exact B.one_mem
  · refine ⟨⊤, ⊤, φ, φ, (Z.germToFunctionField (⊤ ⊓ ⊤)).hom, hAff, hAff, by simpa using hAff, sup_idem _,
      Z.germToFunctionField_injective _, Z.germToFunctionField_injective _, Z.germToFunctionField_injective _,
      rfl, rfl, ?_, ?_, ?_, fun a => rfl, fun a => rfl⟩
    · rw [hDov]
      ext x
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨_, germ_res_eq (⊤ ⊓ ⊤) ⊤ (le_inf le_rfl le_rfl) s⟩
      · rintro ⟨s, rfl⟩
        exact ⟨Z.presheaf.map (homOfLE inf_le_left).op s, germ_res_eq _ _ _ s⟩
    · intro s; exact germ_res_eq _ _ _ s
    · intro s; exact germ_res_eq _ _ _ s

end LateralTheory.E.GeometricData
end
end
