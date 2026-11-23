module

public import Development.EtaleCohomology.EtaleSheaves.Bundle049
public import Development.EtaleCohomology.EtaleSheaves.Bundle013
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Development.EtaleCohomology.EtaleSheaves.Bundle050
public import Development.EtaleCohomology.EtaleSheaves.Bundle051
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.TypeStar
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CompCut

namespace LateralTheory.E.NormACPf

theorem aic_integralClosure (A K : Type) [CommRing A] [CommRing K] [Algebra A K] (hK : AIC K) :
    AIC (integralClosure A K) := by
  intro p hp hd
  obtain ⟨a, ha⟩ := hK (p.map (integralClosure A K).val.toRingHom) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective Subtype.val_injective])
  have hint : IsIntegral (integralClosure A K) a := ⟨p, hp, by
    rw [Polynomial.eval_map] at ha; exact ha⟩
  have haA : a ∈ integralClosure A K := isIntegral_trans (R := A) a hint
  refine ⟨⟨a, haA⟩, Subtype.val_injective ?_⟩
  have h4 : (integralClosure A K).val.toRingHom (Polynomial.eval (⟨a, haA⟩ : integralClosure A K) p) = 0 := by
    rw [← Polynomial.eval₂_at_apply]; rw [Polynomial.eval_map] at ha; exact ha
  simpa using h4

theorem aic_of_subsingleton (R : Type) [CommRing R] [Subsingleton R] : AIC R :=
  fun _ _ _ => ⟨0, Subsingleton.elim _ _⟩

theorem aic_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : AIC R) : AIC S := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map e.symm.toRingHom) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have h4 : e.symm.toRingHom (Polynomial.eval (e a) p) = 0 := by
    rw [← Polynomial.eval₂_at_apply]; rw [Polynomial.eval_map] at ha; simpa using ha
  simpa using h4

theorem aic_spec_field (K : Type) [Field K] (hA : AIC K) (W : (Spec (CommRingCat.of K)).Opens) :
    AIC Γ(Spec (CommRingCat.of K), W) := by
  by_cases h : (default : Spec (CommRingCat.of K)) ∈ W
  · have : W = ⊤ := by
      ext x; simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      rwa [Subsingleton.elim x default]
    subst this
    exact aic_of_ringEquiv (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm hA
  · have : W = ⊥ := by
      ext x; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      rwa [Subsingleton.elim x default]
    subst this
    exact aic_of_subsingleton _

def Loc : Prop := ∀ (Z : Scheme.{0}), IsIntegral Z → (∀ z : Z, ∃ U : Z.Opens, IsAffineOpen U ∧ z ∈ U ∧ AIC Γ(Z, U)) →
  ∀ U : Z.Opens, IsAffineOpen U → (U : Set Z).Nonempty → AIC Γ(Z, U)

theorem NormAC_of (hL : Loc) : NormAC := by
  intro P _ _ K _ hF hA v
  let := hF.toField
  have hI : IsIntegral v.normalization := inferInstance
  refine ⟨hI, hL _ hI ?_⟩
  intro z
  obtain ⟨V, hV, hz, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp P.isBasis_affineOpens
    (show v.fromNormalization z ∈ (⊤ : P.Opens) from trivial)
  refine ⟨v.fromNormalization ⁻¹ᵁ V, hV.preimage _, hz, ?_⟩
  letI := (v.app V).hom.toAlgebra
  exact aic_of_ringEquiv (v.normalizationObjIso hV).commRingCatIsoToRingEquiv.symm
    (aic_integralClosure _ _ (aic_spec_field K hA _))

end LateralTheory.E.NormACPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.E.LeafTensUPPf
open LateralTheory.E.LeafTwTensExPf
open Classical

variable {R : Type} [CommRing R] {I J K : Cx R}

theorem lift_lo (μ : Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    μ.lift U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b)) = μ.mul U s t w h a b := by
  simp [Pair.lift, lo]

theorem lift_nat (μ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    ((K.X w).obj.map g.op).hom ∘ₗ μ.lift U w = μ.lift V w ∘ₗ Tens.res g w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply]
  have e := tres_tmul I J g w ⟨(s, t), h⟩ a b
  change Sec.res g (μ.lift U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b))) = μ.lift V w (Tens.res g w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b)))
  rw [e]
  change Sec.res g (μ.lift U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b))) = μ.lift V w (lo I J ⟨(s, t), h⟩ (Sec.res g a ⊗ₜ Sec.res g b))
  rw [lift_lo, lift_lo, μ.nat]

theorem lift_d (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) :
    ((K.d w (w + 1)).hom.app (op U)).hom ∘ₗ μ.lift U w = μ.lift U (w + 1) ∘ₗ dT I J U w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply]
  change Sec.map (K.d w (w + 1)) (μ.lift U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b))) =
    μ.lift U (w + 1) (dT I J U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b)))
  rw [dT_tmul, map_add (f := _), map_zsmul, lift_lo, lift_lo, lift_lo, μ.leibniz, Units.smul_def]

def liftP (μ : Pair I J K) (w : ℤ) : TP I J w ⟶ (K.X w).obj where
  app U := ModuleCat.ofHom (μ.lift U.unop w)
  naturality _ _ g := ModuleCat.hom_ext (lift_nat μ g.unop w).symm

theorem tensorPresheafLift_comm (μ : Pair I J K) (w : ℤ) :
    liftP μ w ≫ (K.d w (w + 1)).hom = dTP I J w ≫ liftP μ (w + 1) := by
  ext U : 2
  exact ModuleCat.hom_ext (lift_d μ U.unop w)

theorem etale_tensor_presheaf_lift_is_local_iso {T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) :
    Scheme.etaleTopology.{0}.W (liftP τ w) := by
  have : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (liftP τ w) := ⟨fun {U} y => by
    obtain ⟨S, hS, hP⟩ := hτ.1 U w y
    refine Scheme.etaleTopology.{0}.superset_covering ?_ hS
    intro V g hg
    obtain ⟨x, hx⟩ := hP V g hg
    exact ⟨x, hx⟩⟩
  have : Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (liftP τ w) := ⟨fun {X} x y hxy => by
    let x' : Tens I J X.unop w := x
    let y' : Tens I J X.unop w := y
    have hxy' : τ.lift X.unop w x' = τ.lift X.unop w y' := hxy
    have h0 : τ.lift X.unop w (x' - y') = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr hxy'
    obtain ⟨S, hS, hP⟩ := hτ.2 X.unop w (x' - y') h0
    refine Scheme.etaleTopology.{0}.superset_covering ?_ hS
    intro V g hg
    have h1 : Tens.res g w (x' - y') = 0 := hP V g hg
    rw [map_sub, sub_eq_zero] at h1
    exact h1⟩
  exact GrothendieckTopology.W_of_isLocallyBijective _ _

theorem etale_tensor_pairing_universal_property_holds : LateralTheory.E.LeafPairExtPf2.LeafTensUP := by
  intro R _ I J T K τ hτ μ
  have hb : ∀ w, Function.Bijective (fun g : (T.X w).obj ⟶ (K.X w).obj => liftP τ w ≫ g) :=
    fun w => etale_tensor_presheaf_lift_is_local_iso τ hτ w _ (K.X w).property
  choose u0 hu0' using fun w => (hb w).2 (liftP μ w)
  have hu0 : ∀ w, liftP τ w ≫ u0 w = liftP μ w := hu0'
  let u : T ⟶ K :=
    { f := fun w => ⟨u0 w⟩
      comm' := by
        rintro i j rfl
        apply Sheaf.hom_ext
        change u0 i ≫ (K.d i (i + 1)).hom = (T.d i (i + 1)).hom ≫ u0 (i + 1)
        have key : liftP τ i ≫ (u0 i ≫ (K.d i (i + 1)).hom) = liftP τ i ≫ ((T.d i (i + 1)).hom ≫ u0 (i + 1)) := by
          rw [← Category.assoc, ← Category.assoc, hu0, tensorPresheafLift_comm, tensorPresheafLift_comm, Category.assoc, hu0]
        exact (etale_tensor_presheaf_lift_is_local_iso τ hτ i _ (K.X (i + 1)).property).1 key }
  refine ⟨u, fun U s t w h a b => ?_⟩
  have e := congrArg (fun f => (f.app (op U)).hom (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b))) (hu0 w)
  simp only at e
  rw [← lift_lo τ, ← lift_lo μ]
  exact e

end LateralTheory.E.LeafTensUPPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafExtTensPf

theorem res_isKInjective (R : Type) [CommRing R] (F : Shv R) : (res R F).IsKInjective := by
  unfold res; infer_instance

theorem res_injective (R : Type) [CommRing R] (F : Shv R) (n : ℤ) : Injective ((res R F).X n) := by
  unfold res
  rw [InjectiveResolution.cochainComplex]
  by_cases h : ∃ k : ℕ, ComplexShape.embeddingUpNat.f k = n
  · obtain ⟨k, hk⟩ := h
    exact Injective.of_iso (HomologicalComplex.extendXIso _ _ hk).symm inferInstance
  · push_neg at h
    exact (HomologicalComplex.isZero_extend_X _ _ n h).injective

section
variable {C : Type*} [Category C] [Abelian C]

theorem exact_lift {S T L : CochainComplex C ℤ} (ι : S ⟶ T) [∀ n, Mono (ι.f n)] [∀ n, Injective (L.X n)]
    (u : S ⟶ L) (g0 : T ⟶ L) (H : Homotopy u (ι ≫ g0)) : ∃ g : T ⟶ L, ι ≫ g = u := by
  let h' : ∀ i j, T.X i ⟶ L.X j := fun i j => Injective.factorThru (H.hom i j) (ι.f i)
  have hh : (fun i j => ι.f i ≫ h' i j) = H.hom := by
    funext i j; exact Injective.comp_factorThru _ _
  refine ⟨g0 + Homotopy.nullHomotopicMap h', ?_⟩
  rw [Preadditive.comp_add, Homotopy.comp_nullHomotopicMap, hh]
  ext n
  rw [H.comm n]
  simp only [HomologicalComplex.add_f_apply]
  change _ + (dNext n H.hom + prevD n H.hom) = _
  abel

theorem homotopy_lift {S T L : CochainComplex C ℤ} (ι : S ⟶ T) [QuasiIso ι] [L.IsKInjective]
    (u : S ⟶ L) : ∃ g0 : T ⟶ L, Nonempty (Homotopy u (ι ≫ g0)) := by
  let _ := HasDerivedCategory.standard C
  let qt := (HomotopyCategory.quotient C (ComplexShape.up ℤ))
  have hi : IsIso (DerivedCategory.Qh.map (qt.map ι)) := by
    have e := (DerivedCategory.quotientCompQhIso C).hom.naturality ι
    have : IsIso (DerivedCategory.Q.map ι) := by
      rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
    have e2 : DerivedCategory.Qh.map (qt.map ι) = (DerivedCategory.quotientCompQhIso C).hom.app S ≫
        DerivedCategory.Q.map ι ≫ (DerivedCategory.quotientCompQhIso C).inv.app T := by
      simp only [Functor.comp_map] at e
      rw [← reassoc_of% e]; simp [qt]
    rw [e2]; infer_instance
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj T) L).surjective
    (inv (DerivedCategory.Qh.map (qt.map ι)) ≫ DerivedCategory.Qh.map (qt.map u))
  obtain ⟨g0, rfl⟩ := qt.map_surjective g
  refine ⟨g0, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj S) L).injective
  rw [Functor.map_comp, Functor.map_comp, hg, IsIso.hom_inv_id_assoc]

theorem extAlongQIso {S T L : CochainComplex C ℤ} (ι : S ⟶ T) (hm : ∀ n, Mono (ι.f n)) (hq : QuasiIso ι)
    (hk : L.IsKInjective) (hinj : ∀ n, Injective (L.X n)) (u : S ⟶ L) : ∃ g : T ⟶ L, ι ≫ g = u := by
  obtain ⟨g0, ⟨H⟩⟩ := homotopy_lift ι u
  exact exact_lift ι u g0 H
end

def LeafTensMono : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {S T : Cx (ZMod q)} (σ : Pair (sgl (tw q 0)) (res _ (tw q i)) S)
  (τ : Pair (res _ (tw q 0)) (res _ (tw q i)) T), σ.IsTensor → τ.IsTensor → ∀ ι : S ⟶ T,
  (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec ((sgl (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
    Sec.map (ι.f w) (σ.mul U s t w h a b) = τ.mul U s t w h (Sec.map ((resAug (tw q 0)).f s) a) b) →
  ∀ n, Mono (ι.f n)

def LeafTensQIso : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {S T : Cx (ZMod q)} (σ : Pair (sgl (tw q 0)) (res _ (tw q i)) S)
  (τ : Pair (res _ (tw q 0)) (res _ (tw q i)) T), σ.IsTensor → τ.IsTensor → ∀ ι : S ⟶ T,
  (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec ((sgl (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
    Sec.map (ι.f w) (σ.mul U s t w h a b) = τ.mul U s t w h (Sec.map ((resAug (tw q 0)).f s) a) b) →
  QuasiIso ι

theorem LeafExtTens_of (hmono : LeafTensMono) (hqiso : LeafTensQIso) : LateralTheory.E.LeafPairExtPf2.LeafExtTens := by
  intro q _ i S T σ τ hσ hτ ι hι u
  exact extAlongQIso ι (hmono q i σ τ hσ hτ ι hι) (hqiso q i σ τ hσ hτ ι hι) (res_isKInjective _ _)
    (res_injective _ _) u

end LateralTheory.E.LeafExtTensPf
end
end

section

noncomputable section
open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.AbsorbPf

def Sys : Prop := ∀ (A : CommRingCat.{0}) (Ω : Type) [Field Ω] (ι : A →+* Ω),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0})
    (t : (Functor.const J).obj A ⟶ D) (φ : ∀ j, D.obj j →+* Ω),
    (∀ j, Et (t.app j)) ∧ (∀ j, (φ j).comp (t.app j).hom = ι) ∧
    (∀ (j k : J) (a : j ⟶ k), (φ k).comp (D.map a).hom = φ j) ∧
    (∀ (B : CommRingCat.{0}) (g : A ⟶ B), Et g → ∀ φB : B →+* Ω, φB.comp g.hom = ι →
      ∃ (j : J) (h : B ⟶ D.obj j), g ≫ h = t.app j ∧ (φ j).comp h.hom = φB) ∧
    (∀ (j : J) (x : D.obj j), φ j x ≠ 0 → ∃ (k : J) (a : j ⟶ k), IsUnit ((D.map a).hom x))

theorem t_nat {J : Type} [SmallCategory J] {A : CommRingCat.{0}} {D : J ⥤ CommRingCat.{0}}
    (t : (Functor.const J).obj A ⟶ D) {j k : J} (a : j ⟶ k) : t.app j ≫ D.map a = t.app k := by
  have := t.naturality a
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
  exact this.symm

theorem Absorb_of (hS : Sys) : LateralTheory.E.ColimPf.Absorb := by
  intro A Ω _ ι
  obtain ⟨J, _, _, D, t, φ, hEt, hpt, hcomp, habs, hloc⟩ := hS A Ω ι
  let O : CommRingCat.{0} := colimit D
  let s : D ⟶ (Functor.const J).obj O := (colimit.cocone D).ι
  let j0 : J := IsFiltered.nonempty.some
  let f : A ⟶ O := t.app j0 ≫ colimit.ι D j0
  have hf : ∀ j, t.app j ≫ colimit.ι D j = f := by
    intro j
    let k := IsFiltered.max j j0
    show t.app j ≫ colimit.ι D j = t.app j0 ≫ colimit.ι D j0
    rw [← colimit.w D (IsFiltered.leftToMax j j0), ← colimit.w D (IsFiltered.rightToMax j j0),
      ← Category.assoc, ← Category.assoc, t_nat, t_nat]
  let cΩ : Cocone D :=
    { pt := CommRingCat.of Ω
      ι := { app := fun j => CommRingCat.ofHom (φ j)
             naturality := by
               intro j k a
               ext x
               have := DFunLike.congr_fun (hcomp j k a) x
               simpa using this } }
  let ψ : O →+* Ω := (colimit.desc D cΩ).hom
  have hψ : ∀ j (y : D.obj j), ψ (colimit.ι D j y) = φ j y := by
    intro j y
    have := colimit.ι_desc cΩ j
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom this) y
  refine ⟨O, f, ψ, ?_, ?_, ?_, ?_⟩
  · refine ⟨J, inferInstance, inferInstance, D, t, s, colimit.isColimit D, fun j => ⟨hEt j, hf j⟩⟩
  · ext a
    have := DFunLike.congr_fun (hpt j0) a
    simp only [RingHom.comp_apply] at this ⊢
    rw [← this, ← hψ]; rfl
  · intro x hx
    obtain ⟨j, y, rfl⟩ := Concrete.colimit_exists_rep D x
    rw [hψ] at hx
    obtain ⟨k, a, hu⟩ := hloc j y hx
    have : colimit.ι D j y = colimit.ι D k ((D.map a).hom y) := by
      rw [← colimit.w D a]; rfl
    rw [this]
    exact hu.map (colimit.ι D k).hom
  · intro B g hg φB hφB
    obtain ⟨j, h, hh1, hh2⟩ := habs B g hg φB hφB
    refine ⟨h ≫ colimit.ι D j, ?_, ?_⟩
    · rw [← Category.assoc, hh1, hf]
    · ext b
      simp only [RingHom.comp_apply, CommRingCat.hom_comp]
      rw [hψ]
      exact DFunLike.congr_fun hh2 b

def Sys2 : Prop := ∀ (A : CommRingCat.{0}) (Ω : Type) [Field Ω] (ι : A →+* Ω),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0})
    (t : (Functor.const J).obj A ⟶ D) (φ : ∀ j, D.obj j →+* Ω),
    (∀ j, Et (t.app j)) ∧ (∀ j, (φ j).comp (t.app j).hom = ι) ∧
    (∀ (j k : J) (a : j ⟶ k), (φ k).comp (D.map a).hom = φ j) ∧
    (∀ (B : CommRingCat.{0}) (g : A ⟶ B), Et g → ∀ φB : B →+* Ω, φB.comp g.hom = ι →
      ∃ (j : J) (h : B ⟶ D.obj j), g ≫ h = t.app j ∧ (φ j).comp h.hom = φB) ∧
    (∀ (j : J) (B : CommRingCat.{0}) (g : D.obj j ⟶ B), Et g → ∀ φB : B →+* Ω, φB.comp g.hom = φ j →
      ∃ (k : J) (a : j ⟶ k) (h : B ⟶ D.obj k), g ≫ h = D.map a)

theorem Sys_of (h2 : Sys2) : Sys := by
  intro A Ω _ ι
  obtain ⟨J, i1, i2, D, t, φ, hEt, hpt, hcomp, habs, hst⟩ := h2 A Ω ι
  refine ⟨J, i1, i2, D, t, φ, hEt, hpt, hcomp, habs, ?_⟩
  intro j x hx
  let B : CommRingCat.{0} := CommRingCat.of (Localization.Away x)
  let g : D.obj j ⟶ B := CommRingCat.ofHom (algebraMap (D.obj j) (Localization.Away x))
  have hg : Et g := by
    change (algebraMap (D.obj j) (Localization.Away x)).Etale
    rw [RingHom.etale_algebraMap]
    infer_instance
  have hu : IsUnit (φ j x) := isUnit_iff_ne_zero.mpr hx
  let φB : B →+* Ω := IsLocalization.Away.lift x hu
  obtain ⟨k, a, h, hh⟩ := hst j B g hg φB (IsLocalization.Away.lift_comp x hu)
  refine ⟨k, a, ?_⟩
  have e : (D.map a).hom x = h.hom (algebraMap (D.obj j) (Localization.Away x) x) := by
    rw [← hh]; rfl
  rw [e]
  exact (IsLocalization.Away.algebraMap_isUnit x).map h.hom

theorem etaleAbsorbing_of_strongFilteredEtaleSystemExists (h2 : Sys2) : LateralTheory.E.ColimPf.Absorb := Absorb_of (Sys_of h2)

end LateralTheory.E.AbsorbPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechSigma_xy1Pf_Yo
open LateralTheory.E.CechSigmaProof LateralTheory.E.CechSigma_xy1Pf_Lev

def eW {A B : Scheme.{0}} (p : A ⟶ B) (n : ℕ) :
    yoneda.obj (widePullback B (fun _ : Fin (n + 1) => A) (fun _ => p)) ≅
      widePullback (yoneda.obj B) (fun _ : Fin (n + 1) => yoneda.obj A) (fun _ => yoneda.map p) :=
  preservesLimitIso yoneda (WidePullbackShape.wideCospan B (fun _ : Fin (n + 1) => A) (fun _ => p)) ≪≫
    HasLimit.isoOfNatIso (WidePullbackShape.diagramIsoWideCospan _)

theorem eW_π {A B : Scheme.{0}} (p : A ⟶ B) (n : ℕ) (i : Fin (n + 1)) :
    (eW p n).hom ≫ WidePullback.π _ i = yoneda.map (WidePullback.π _ i) := by
  simp only [eW, Iso.trans_hom, WidePullback.π]
  erw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc, preservesLimitIso_hom_π]
  simp only [WidePullbackShape.diagramIsoWideCospan, NatIso.ofComponents_hom_app]
  exact Category.comp_id _

theorem eW_base {A B : Scheme.{0}} (p : A ⟶ B) (n : ℕ) :
    (eW p n).hom ≫ WidePullback.base _ = yoneda.map (WidePullback.base _) := by
  simp only [eW, Iso.trans_hom, WidePullback.base]
  erw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc, preservesLimitIso_hom_π]
  simp only [WidePullbackShape.diagramIsoWideCospan, NatIso.ofComponents_hom_app]
  exact Category.comp_id _

theorem cechYoneda : CechYoneda := by
  intro A B C D p q s n
  refine ⟨(Arrow.isoMk (eW p n) (eW q n) ?_).symm⟩
  apply WidePullback.hom_ext
  · intro i
    simp only [Arrow.mk_hom, Category.assoc]
    erw [Arrow.mapCechNerve_app, WidePullback.lift_π]
    erw [← Category.assoc, eW_π, Category.assoc, eW_π]
    change yoneda.map _ ≫ yoneda.map s.left = yoneda.map _ ≫ yoneda.map _
    simp only [wpMap]
    erw [← Functor.map_comp, ← Functor.map_comp, WidePullback.lift_π]
  · simp only [Arrow.mk_hom, Category.assoc]
    erw [Arrow.mapCechNerve_app, WidePullback.lift_base]
    erw [← Category.assoc, eW_base, Category.assoc, eW_base]
    change yoneda.map _ ≫ yoneda.map s.right = yoneda.map _ ≫ yoneda.map _
    simp only [wpMap]
    erw [← Functor.map_comp, ← Functor.map_comp, WidePullback.lift_base]

end LateralTheory.E.CechSigma_xy1Pf_Yo
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf

namespace LateralTheory.E.EmptyH₂

theorem sec_subsingleton {R : Type} [CommRing R] (F : Shv R) (Y : Scheme.{0}) [IsEmpty Y] :
    Subsingleton (Sec F Y) := by
  have hT := Sheaf.isTerminalOfBotCover F Y (Scheme.bot_mem_grothendieckTopology (P := @Etale) Y)
  exact (ModuleCat.isZero_iff_subsingleton).1 hT.isZero

theorem h_empty (hH : Hyp) {R : Type} [CommRing R] (F : Shv R) (Y : Scheme.{0}) [IsEmpty Y] (n : ℤ)
    (x : H R (sch.obj Y) F n) : x = 0 := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have := (hH.a9 R F).1 (sch.obj Y) n hn
    exact Subsingleton.elim _ _
  · obtain ⟨e, -, -⟩ := (hH.a9 R F).2
    have := sec_subsingleton F Y
    rw [← (e Y).apply_symm_apply x, Subsingleton.elim ((e Y).symm x) 0, map_zero]
  · obtain ⟨Z, f, -, -, hf⟩ := hH.a5 R Y F n hn x
    have : IsIso (sch.map f) := inferInstance
    have h1 : pull R (inv (sch.map f) ≫ sch.map f) F n x = 0 := by rw [pull_comp, hf, map_zero]
    simpa [pull_id] using h1

theorem EmptyH_of : LateralTheory.E.InjStepPf.EmptyH := by
  intro hH q X S p U hU i n x
  have : IsEmpty U := ⟨fun u => by
    have h : (u.1 : S) ∈ (U : Set S) := u.2
    rw [hU] at h; exact h⟩
  have : IsEmpty (overO p U) := ⟨fun z => isEmptyElim ((pullback.snd p U.ι).base z)⟩
  exact h_empty hH _ _ n x

end LateralTheory.E.EmptyH₂
end
end
