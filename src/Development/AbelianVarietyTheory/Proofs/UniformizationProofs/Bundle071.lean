module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteOfNotLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankTotalDegreeImageGrowth
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle028
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueTorusExtensionPointOfGroupPoint
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.VeryAmpleGrowth

variable {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))

theorem top_add {M : LB X} (a b : SecOnR f M ⊤) (k : M.ι) :
    (SecOnR.topEquiv f M (a + b)).f k = (SecOnR.topEquiv f M a).f k + (SecOnR.topEquiv f M b).f k := by
  rw [SecOnR.topEquiv_f, SecOnR.topEquiv_f, SecOnR.topEquiv_f, SecOnR.coord_add, map_add (f := _)]

theorem top_smul {M : LB X} (c : K) (a : SecOnR f M ⊤) (k : M.ι) :
    (SecOnR.topEquiv f M (c • a)).f k = cst f (M.U k) c * (SecOnR.topEquiv f M a).f k := by
  rw [SecOnR.topEquiv_f, SecOnR.topEquiv_f, SecOnR.coord_base_smul, map_mul, rs_cst]

theorem top_ext {M : LB X} {a b : SecOnR f M ⊤}
    (h : ∀ k, (SecOnR.topEquiv f M a).f k = (SecOnR.topEquiv f M b).f k) : a = b :=
  (SecOnR.topEquiv f M).injective (by
    generalize SecOnR.topEquiv f M a = x at h ⊢
    generalize SecOnR.topEquiv f M b = y at h ⊢
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    obtain rfl : x = y := funext h
    rfl)

theorem top_zero {M : LB X} (k : M.ι) : (SecOnR.topEquiv f M 0).f k = 0 := by
  rw [SecOnR.topEquiv_f, SecOnR.coord_zero, map_zero]

def linTop {M : LB X} {V : Type} [AddCommGroup V] [Module K V] (φ : V → LB.Sec M)
    (hadd : ∀ a b k, (φ (a + b)).f k = (φ a).f k + (φ b).f k)
    (hsmul : ∀ (c : K) a k, (φ (c • a)).f k = cst f (M.U k) c * (φ a).f k) :
    V →ₗ[K] SecOnR f M ⊤ where
  toFun a := (SecOnR.topEquiv f M).symm (φ a)
  map_add' a b := top_ext f fun k => by
    simp only [top_add, LinearEquiv.apply_symm_apply, hadd]
  map_smul' c a := top_ext f fun k => by
    simp only [top_smul, LinearEquiv.apply_symm_apply, hsmul, RingHom.id_apply]

theorem top_linTop {M : LB X} {V : Type} [AddCommGroup V] [Module K V] (φ : V → LB.Sec M) (hadd hsmul)
    (a : V) : SecOnR.topEquiv f M (linTop f φ hadd hsmul a) = φ a :=
  (SecOnR.topEquiv f M).apply_symm_apply _

def mulPw {H : LB X} (s : LB.Sec H) (t : ℕ) (σ : LB.Sec (pw H t)) : LB.Sec (pw H (t + 1 : ℕ)) where
  f := fun k => s.f k * (show Γ(X, H.U k) from σ.f k)
  compat := fun k l => by
    have h₁ : rs X (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) (s.f k) =
      (H.g k l).val * rs X (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) (s.f l) := s.compat k l
    have h₂ : rs X (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) (σ.f k) =
      (H.g k l ^ (t : ℤ)).val * rs X (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) (σ.f l) := σ.compat k l
    change rs X (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) (s.f k * (show Γ(X, H.U k) from σ.f k)) =
      (H.g k l ^ ((t + 1 : ℕ) : ℤ)).val *
        rs X (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) (s.f l * (show Γ(X, H.U l) from σ.f l))
    rw [map_mul, map_mul, h₁, h₂, zpow_natCast, zpow_natCast, pow_succ, Units.val_mul]
    ring

def mulLin {H : LB X} (s : LB.Sec H) (t : ℕ) :
    SecOnR f (pw H t) ⊤ →ₗ[K] SecOnR f (pw H (t + 1 : ℕ)) ⊤ :=
  linTop f (fun a => mulPw s t (SecOnR.topEquiv f _ a))
    (fun a b k => (congrArg (fun y : Γ(X, H.U k) => s.f k * y) (top_add f a b k)).trans
      (mul_add (s.f k) (show Γ(X, H.U k) from (SecOnR.topEquiv f (pw H t) a).f k)
        (show Γ(X, H.U k) from (SecOnR.topEquiv f (pw H t) b).f k)))
    (fun c a k => (congrArg (fun y : Γ(X, H.U k) => s.f k * y) (top_smul f c a k)).trans
      (mul_left_comm _ _ _))

theorem top_mulLin {H : LB X} (s : LB.Sec H) (t : ℕ) (a : SecOnR f (pw H t) ⊤) :
    SecOnR.topEquiv f (pw H (t + 1 : ℕ)) (mulLin f s t a) = mulPw s t (SecOnR.topEquiv f (pw H t) a) :=
  top_linTop f _ _ _ a

theorem mulLin_injective [IsIntegral X] {H : LB X} (s : LB.Sec H) {x : X} (hx : x ∈ nonzeroLocus s) (t : ℕ) :
    Function.Injective (mulLin f s t) := by
  obtain ⟨k₀, hk₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  let W : X.Opens := X.basicOpen (s.f k₀)
  have hWU : W ≤ H.U k₀ := X.basicOpen_le _
  haveI : Nonempty W := ⟨⟨x, hk₀⟩⟩
  have hu : IsUnit (rs X hWU (s.f k₀)) := X.toRingedSpace.isUnit_res_basicOpen _
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have h : s.f k₀ * (show Γ(X, H.U k₀) from (SecOnR.topEquiv f (pw H t) a).f k₀) = 0 := by
    have e := top_mulLin f s t a
    rw [ha] at e
    exact (congrArg (fun σ : LB.Sec (pw H (t + 1 : ℕ)) => σ.f k₀) e).symm.trans
      (top_zero f (M := pw H (t + 1 : ℕ)) k₀)
  have h' := congrArg (rs X hWU) h
  rw [map_mul, map_zero, hu.mul_right_eq_zero] at h'
  exact top_ext f fun k =>
    (SecGrowth.sec_eq_zero (M := pw H t) (SecOnR.topEquiv f _ a) (k₀ := k₀) hWU h' k).trans
      (top_zero f k).symm

theorem finite_of_polynomial {H : LB X} {m : ℕ} (s : Fin (m + 1) → LB.Sec H) (t : ℕ)
    (h : ∀ σ : LB.Sec (pw H t), ∃ F : MvPolynomial (Fin (m + 1)) K, F.IsHomogeneous t ∧
      ∀ k : H.ι, σ.f k = MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) F) :
    Module.Finite K (SecOnR f (pw H t) ⊤) := by
  haveI : Module.Finite K (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K t) :=
    Submodule.finiteDimensional_of_le (S₂ := MvPolynomial.restrictTotalDegree (Fin (m + 1)) K t)
      fun F hF => (MvPolynomial.mem_restrictTotalDegree _ _ _).2
        (MvPolynomial.IsHomogeneous.totalDegree_le hF)
  refine Module.Finite.of_surjective
    (linTop f (V := MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K t)
      (fun F => SecGrowth.polySec f s F.2)
      (fun a b k => map_add (MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k)) a.1 b.1)
      (fun c a k => ?_)) fun a => ?_
  · change MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) (c • a.1) =
      cst f (H.U k) c * MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) a.1
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C]
  · obtain ⟨F, hF, hFa⟩ := h (SecOnR.topEquiv f _ a)
    refine ⟨⟨F, hF⟩, top_ext f fun k => ?_⟩
    exact (congrArg (fun σ : LB.Sec (pw H t) => σ.f k) (top_linTop f _ _ _ _)).trans (hFa k).symm

theorem finite_monotone_growth : ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) ∧ (∀ t t' : ℕ, t ≤ t' → Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (f) (pw H t') ⊤)) ∧ ∃ c C : ℕ, 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t → t ^ g ≤ c * Module.finrank K (SecOnR (f) (pw H t) ⊤) ∧ Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ C * t ^ g := by
  intro K _ X _ f g hf H n s hH hs
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.exists_homogeneousForm_eq_highPowerSection K X f H n s hH hs
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have hx : x ∈ ⨆ i, nonzeroLocus (s i) := by rw [hs.1]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have hinj := mulLin_injective f (s i) hi
  have hfin : ∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤) := fun t => by
    have h : ∀ d t : ℕ, t₀ ≤ t + d → Module.Finite K (SecOnR f (pw H t) ⊤) := by
      intro d
      induction d with
      | zero => exact fun t ht => finite_of_polynomial f s t (ht₀ t ht)
      | succ d ih =>
        intro t ht
        haveI := ih (t + 1) (by omega)
        exact Module.Finite.of_injective _ (hinj t)
    exact h t₀ t (Nat.le_add_left _ _)
  refine ⟨hfin, fun t t' h => ?_, ?_⟩
  · exact monotone_nat_of_le_succ (f := fun t : ℕ => Module.finrank K (SecOnR f (pw H t) ⊤))
      (fun t => LinearMap.finrank_le_finrank_of_injective (hinj t)) h
  · exact SecGrowth.growth_of_veryAmpleBy f s hs g t₀ ht₀
      (fun B _ _ _ r => finrank_totalDegree_image_growth K B _ _ r)
      (trdeg_eq_of_smoothOfRelativeDimension K X f g hf)
      (fun t => SecOnR f (pw H t) ⊤) (fun t => SecOnR.topEquiv f _)
      (fun t a b k => top_add f a b k) (fun t c a k => top_smul f c a k)
      (fun t a ha => top_ext f fun k => (ha k).trans (top_zero f k).symm)
      (fun t σ => ⟨(SecOnR.topEquiv f _).symm σ, fun k => by rw [LinearEquiv.apply_symm_apply]⟩)

end GlobalTheory.VeryAmpleGrowth
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

noncomputable local instance (priority := high) grpObjThickForTorusPoint {R : Type} [CommRing R]
    (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] :
    GrpObj (thickObj R I e G) :=
  letI : (Over.pullback (thick R I e)).Monoidal :=
    (Over.instBraidedPullback (f := thick R I e)).toMonoidal
  Functor.grpObjObj (F := Over.pullback (thick R I e))

section Kernel

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G B T : Over S} {G' : Over S'} [GrpObj B] [GrpObj G']
  {X : Type} [AddCommGroup X]

theorem TQ.mono_i_left (Q : TQ G' X) : Mono Q.i.left := by
  have : Mono Q.i := ⟨fun _ _ h => Q.isKernel.hom_ext h (toUnit_unique _ _)⟩
  infer_instance

theorem TQ.image_eq_one_iff (Q : TQ G' X) {β : Q.B.left ⟶ B.left} (hB : IsGrpPullback Q.B B f β)
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (xe : Z ⟶ G'.left) (hc : r ≫ T.hom = (xe ≫ G'.hom) ≫ f) :
    xe ≫ Q.q.left ≫ β = r ≫ (1 : T ⟶ B).left ↔ ∃ τ : Z ⟶ (splitTorus S' X).left, τ ≫ Q.i.left = xe := by
  obtain ⟨eB, heB⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hB _ _ hc
  let R : Over.mk (r ≫ T.hom) ⟶ T := Over.homMk r rfl
  let xe' : Over.mk (xe ≫ G'.hom) ⟶ G' := Over.homMk xe rfl
  have e₁ : (eB (xe' ≫ Q.q)).left = xe ≫ Q.q.left ≫ β := (heB _).trans (Category.assoc _ _ _)
  have e₂ : (eB 1).left = r ≫ (1 : T ⟶ B).left := by
    rw [map_one, ← MonObj.comp_one R]; rfl
  rw [← e₁, ← e₂]
  constructor
  · intro h
    have h₁ : xe' ≫ Q.q = toUnit _ ≫ η[Q.B] := eB.injective (Over.OverMorphism.ext h)
    exact ⟨(Q.isKernel.lift _ _ h₁).left, congrArg (fun z => z.left) (Q.isKernel.lift_fst _ _ h₁)⟩
  · rintro ⟨τ, hτ⟩
    let τ' : Over.mk (xe ≫ G'.hom) ⟶ splitTorus S' X := Over.homMk τ (by
      rw [← hτ, ← Over.w Q.i]; exact (Category.assoc _ _ _).symm)
    have h₁ : τ' ≫ Q.i = xe' := Over.OverMorphism.ext hτ
    have h₂ : xe' ≫ Q.q = 1 := by
      rw [← h₁, Category.assoc, Q.isKernel.w, ← Category.assoc, Hom.one_def, toUnit_unique (τ' ≫ toUnit _)]
    rw [h₂]

end Kernel

section Scal

variable {A C : Type} [CommRing A] [CommRing C] {Y Y' : Scheme.{0}}

noncomputable def scalRingHom (p : Y ⟶ Spec (CommRingCat.of A)) : A →+* Γ(Y, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop).hom

theorem scalRingHom_specMap (p : Y ⟶ Spec (CommRingCat.of C)) (φ : A →+* C) :
    scalRingHom (p ≫ Spec.map (CommRingCat.ofHom φ)) = (scalRingHom p).comp φ :=
  congrArg CommRingCat.Hom.hom (SplitTorusPoints.ΓSpecIso_inv_comp_specMap p (CommRingCat.ofHom φ))

theorem exists_factor_quotient (r : Y ⟶ Spec (CommRingCat.of C)) (J : Ideal C)
    (h : J ≤ RingHom.ker (scalRingHom r)) :
    ∃ r' : Y ⟶ Spec (CommRingCat.of (C ⧸ J)), r' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) = r := by
  refine ⟨Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift J (scalRingHom r) fun _ ha => RingHom.mem_ker.1 (h ha))), ?_⟩
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk]
  apply ext_to_Spec
  refine (SplitTorusPoints.ΓSpecIso_inv_comp_specMap _ _).trans ?_
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem exists_factor_thick (φ : A →+* C) (I : Ideal A) (e : ℕ) (r : Y ⟶ Spec (CommRingCat.of C))
    (p : Y ⟶ Spec (CommRingCat.of (A ⧸ I ^ (e + 1))))
    (h : p ≫ thick A I e = r ≫ Spec.map (CommRingCat.ofHom φ)) :
    ∃ r' : Y ⟶ Spec (CommRingCat.of (C ⧸ I.map φ ^ (e + 1))), r' ≫ thick C (I.map φ) e = r := by
  refine exists_factor_quotient r _ ?_
  rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
  intro a ha
  have := congrArg (fun q => scalRingHom q a) h
  simp only [scalRingHom_specMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero] at this
  exact this.symm

theorem exists_torus_point {S : Scheme.{0}} {X : Type} [AddCommGroup X] (c : Multiplicative X →* Cˣ)
    (r : Y ⟶ Spec (CommRingCat.of C)) (p : Y ⟶ S) : ∃ τ : Y ⟶ (splitTorus S X).left, τ ≫ (splitTorus S X).hom = p ∧
      ∀ χ, τ.appTop.hom (charUnit S X χ).val = scal r (c (Multiplicative.ofAdd χ)).val := by
  obtain ⟨τ, hτ⟩ := (splitTorusPointsEquiv S X (Over.mk p)).surjective
    ((Units.map (scalRingHom r).toMonoidHom).comp c)
  refine ⟨τ.left, Over.w τ, fun χ => ?_⟩
  refine (splitTorusPointsEquiv_val S X _ τ χ).symm.trans ?_
  rw [hτ]; rfl

theorem exists_hom_of_thick {X : Type} [AddCommGroup X] (J : Ideal C) [IsAdicComplete J C] {S : ℕ → Scheme.{0}}
    (τ : ∀ e, Spec (CommRingCat.of (C ⧸ J ^ (e + 1))) ⟶ (splitTorus (S e) X).left)
    (h : ∀ e χ, (thickTrans C J e ≫ τ (e + 1)).appTop.hom (charUnit _ X χ).val =
      (τ e).appTop.hom (charUnit _ X χ).val) :
    ∃ c : Multiplicative X →* Cˣ, ∀ e χ,
      (τ e).appTop.hom (charUnit _ X χ).val = scal (thick C J e) (c (Multiplicative.ofAdd χ)).val := by
  let u := fun e => splitTorusPointsEquiv (S e) X (Over.mk (τ e ≫ (splitTorus (S e) X).hom)) (Over.homMk (τ e) rfl)
  have hu : ∀ e χ, (u e (Multiplicative.ofAdd χ)).val = (τ e).appTop.hom (charUnit _ X χ).val := fun e χ =>
    splitTorusPointsEquiv_val _ _ _ _ χ
  choose b hb using fun χ : X => CompletePoint.exists_fn_of_thick J (fun e => (τ e).appTop.hom (charUnit _ X χ).val)
    fun e => by rw [← h e χ, Scheme.Hom.comp_appTop]; rfl
  let b' : Multiplicative X →* Γ(Spec (CommRingCat.of C), ⊤) :=
    { toFun := fun χ => b χ.toAdd
      map_one' := CompletePoint.fn_eq_of_thick J fun e => by
        rw [hb, ← hu]; exact (congrArg Units.val (map_one (u e))).trans (map_one _).symm
      map_mul' := fun χ χ' => CompletePoint.fn_eq_of_thick J fun e => by
        rw [(thick C J e).appTop.hom.map_mul, hb, hb, hb, ← hu, ← hu, ← hu]
        exact congrArg Units.val (map_mul (u e) χ χ') }
  refine ⟨((Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom.toMonoidHom.comp b').toHomUnits, fun e χ => ?_⟩
  rw [← hb]
  exact congrArg (thick C J e).appTop.hom (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of C)) (b χ)).symm

end Scal

theorem image_eq_one_iff_torus_point : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B)).left) ↔ ∃ c : Multiplicative s.X →* Wˣ, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ s.X).left), τ ≫ (splitTorus (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))) s.X).hom ≫ thick V _ e = r ≫ (Spec.map (CommRingCat.ofHom (algebraMap V W))) → (∀ χ, τ.appTop.hom (charUnit _ s.X χ).val = scal r (c (Multiplicative.ofAdd χ)).val) → τ ≫ (t.l e).Q.i.left ≫ (fstG _ e G).left = r ≫ (x).left) := by
  intro V _ _ _ A G _ _ s t a W _ _ _ hW _ x
  let I := IsLocalRing.maximalIdeal V
  let φ := algebraMap V W
  have hx : x.left ≫ G.hom = Spec.map (CommRingCat.ofHom φ) := Over.w x
  have hF : ∀ e, (fstG I e G).left ≫ G.hom = (thickObj V I e G).hom ≫ thick V I e := fun e => pullback.condition
  have mF : ∀ e, Mono (fstG I e G).left := fun e => pullback.fst_of_mono (f := G.hom) (g := thick V I e)
  have base : ∀ (e : ℕ) {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x.left →
      r ≫ Spec.map (CommRingCat.ofHom φ) = (xe ≫ (thickObj V I e G).hom) ≫ thick V I e := fun e Z r xe h => by
    rw [Category.assoc, ← hF, ← hx, ← Category.assoc, ← h]
    exact Category.assoc _ _ _
  have ker := fun (e : ℕ) {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V I e G).left)
    (h : xe ≫ (fstG I e G).left = r ≫ x.left) =>
    (t.l e).Q.image_eq_one_iff (T := Over.mk (Spec.map (CommRingCat.ofHom φ))) (a.b_pb e).1 r xe (base e r xe h)
  constructor
  · intro H
    let J := I.map φ
    have hle : ∀ e : ℕ, I ^ (e + 1) ≤ (J ^ (e + 1)).comap φ := fun e => by
      rw [← Ideal.map_pow]; exact Ideal.le_comap_map
    have hp : ∀ e, (thick W J e ≫ x.left) ≫ G.hom =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ φ (hle e))) ≫ thick V I e := fun e => by
      rw [Category.assoc, hx, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]
    obtain ⟨y, hy⟩ : ∃ y : ∀ e, Spec (CommRingCat.of (W ⧸ J ^ (e + 1))) ⟶ (thickObj V I e G).left,
        ∀ e, y e ≫ (fstG I e G).left = thick W J e ≫ x.left :=
      ⟨fun e => pullback.lift _ _ (hp e), fun e => pullback.lift_fst _ _ _⟩
    choose τ hτ using fun e => (ker e _ _ (hy e)).1 (H e _ _ _ (hy e))
    obtain ⟨c, hc⟩ := exists_hom_of_thick J τ fun e χ => by
      obtain ⟨σ, -, h₁, h₂⟩ := t.tor e
      have := (t.l (e + 1)).Q.mono_i_left
      have := mF (e + 1)
      have h₃ : thickMap V I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
        (pullback.lift_fst _ _ _).trans (Category.comp_id _)
      have h₄ : thickTrans W J e ≫ y (e + 1) = y e ≫ thickMap V I e G := by
        refine (cancel_mono (fstG I (e + 1) G).left).1 ?_
        refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hy (e + 1))).trans ?_)
        refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h₃)).symm
        rw [← Category.assoc, thickTrans_comp]
        exact (hy e).symm
      have h₅ : thickTrans W J e ≫ τ (e + 1) = τ e ≫ σ := by
        rw [← cancel_mono (t.l (e + 1)).Q.i.left, Category.assoc, hτ, h₄, Category.assoc, h₂, ← Category.assoc, hτ]
      rw [h₅, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, h₁]
    refine ⟨c, fun e Z r τ' h₁ h₂ => ?_⟩
    obtain ⟨r', rfl⟩ := exists_factor_thick φ I e r _ ((Category.assoc _ _ _).trans h₁)
    have h₃ : τ' = r' ≫ τ e := by
      refine splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
      · rw [← cancel_mono (thick V I e), Category.assoc]
        refine h₁.trans ?_
        rw [Category.assoc, base e _ _ (hy e), ← hτ e, Category.assoc (τ e), Over.w]
        simp only [Category.assoc]
      · rw [h₂, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hc, scal, scal,
          Scheme.Hom.comp_appTop]
        rfl
    have h₄ : τ e ≫ (t.l e).Q.i.left ≫ (fstG I e G).left = thick W J e ≫ x.left :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I e G).left) (hτ e)).trans (hy e))
    rw [h₃]
    exact (Category.assoc _ _ _).trans ((congrArg (r' ≫ ·) h₄).trans (Category.assoc _ _ _).symm)
  · rintro ⟨c, hc⟩ e Z r xe h
    obtain ⟨τ, h₁, h₂⟩ := exists_torus_point c r (xe ≫ (thickObj V I e G).hom)
    have := mF e
    refine (ker e r xe h).2 ⟨τ, (cancel_mono (fstG I e G).left).1 ?_⟩
    refine (Category.assoc _ _ _).trans ((hc e Z r τ ?_ h₂).trans h.symm)
    rw [← Category.assoc, h₁]
    exact (base e r xe h).symm

end GlobalTheory.UU
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.IntExp

theorem gs_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (h : f (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ f) z U a = (r.stalkMap z).hom (gs f (r z) U a) := by
  rw [gs_eq f (r z) U h, gs_eq (r ≫ f) z U h]
  exact (Scheme.Hom.germ_stalkMap_apply r (f ⁻¹ᵁ U) z h _).symm

theorem sval_comp {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) (J) (hJ : Good L z J) :
    sval s (r ≫ h) z J = (r.stalkMap z).hom (sval s h (r z) (fun ψ => J (r ≫ ψ))) := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp r h z _ (Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)) _

theorem gs_scal_one {F : Type} [CommRing F] {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (p : Y ⟶ Spec (CommRingCat.of F)) :
    gs r z ⊤ (scal p (1 : F)) = 1 := by
  rw [gs_eq r z ⊤ trivial]
  simp only [scal, map_one]

theorem expF_of_expT : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α) (t) (s : Raw D F k), U.ExpT (𝟙_ _) k σ f → U.PullG F (toUnit _) k σ t → PullB D F (toUnit _) k f s → U.ExpF F k t s := by
  intro R _ _ I D A G _ _ U F _ _ k σ f t s hE hG hB
  refine ⟨1, fun _ => 1, fun _ => σ, fun _ => f, fun _ => hE, ?_, ?_⟩
  · intro Z rA y rG h₁ h₂ z JA JG hJA hJG
    rw [Fin.sum_univ_one]
    refine (hG Z rA y rG h₁ h₂ ?_ z JA JG hJA hJG).trans ?_
    · have e₁ : (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) G).left = (snd (𝟙_ _) G).left ≫ G.hom := by
        have a := Over.w (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) G)
        have b := Over.w (snd (𝟙_ (Over (Spec (CommRingCat.of R)))) G)
        exact ((Category.comp_id _).symm.trans a).trans b.symm
      have e₂ : (toUnit (TF (R := R) F)).left = jFK (R := R) F ≫ jK R := by
        have a := Over.w (toUnit (TF (R := R) F))
        exact (Category.comp_id _).symm.trans a
      have e₃ : (fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F = (snd (TFK (R := R) F) A.A).left ≫ A.A.hom :=
        (Over.w (fst (TFK (R := R) F) A.A)).trans (Over.w (snd (TFK (R := R) F) A.A)).symm
      have e₄ : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
      calc rG ≫ (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) G).left
          = (rG ≫ (snd (𝟙_ _) G).left) ≫ G.hom := by rw [e₁]; exact (Category.assoc _ _ _).symm
        _ = y ≫ pullback.fst G.hom (jK R) ≫ G.hom := by rw [h₂]; exact Category.assoc _ _ _
        _ = y ≫ (U.gen.hom.left ≫ A.A.hom) ≫ jK R := by rw [e₄]; exact congrArg (y ≫ ·) pullback.condition
        _ = (rA ≫ (snd (TFK (R := R) F) A.A).left) ≫ A.A.hom ≫ jK R := by rw [h₁]; simp only [Category.assoc]
        _ = rA ≫ ((fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F) ≫ jK R := by rw [e₃]; simp only [Category.assoc]
        _ = _ := by rw [e₂]; exact congrArg (rA ≫ ·) (Category.assoc _ _ _)
    · exact ((congrArg (· * _) (gs_scal_one rA z _)).trans (one_mul _)).symm
  · intro α Z rF rB h z J hJ
    rw [Fin.sum_univ_one]
    refine Eq.trans ?_ ((congrArg (· * _) (gs_scal_one rF z _)).trans (one_mul _)).symm
    have e : rB = rF ≫ (toUnit (TF (R := R) F) ▷ D.P.A).left := by
      have w : (toUnit (TF (R := R) F) ▷ D.P.A).left ≫ (snd (𝟙_ _) D.P.A).left = (snd _ D.P.A).left :=
        congrArg CommaMorphism.left (whiskerRight_snd (toUnit (TF (R := R) F)) D.P.A)
      have i : IsIso (snd (𝟙_ (Over (Spec (CommRingCat.of R)))) D.P.A).left := by
        rw [← leftUnitor_hom]; exact inferInstanceAs (IsIso ((Over.forget _).map (λ_ D.P.A).hom))
      rw [← cancel_mono (snd (𝟙_ (Over (Spec (CommRingCat.of R)))) D.P.A).left, Category.assoc, w, h]
    rw [e, sval_comp (f α) _ rF z J hJ, ← hB α (rF z) _ (fun ψ => hJ (rF ≫ ψ)), ← sval_comp (s α) _ rF z J hJ,
      Category.comp_id]

end GlobalTheory.UU.IntExp
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU
section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def gtCoordSetPsi {e : ℕ} (g : GtCoord I D e G) (ψ) (h) : GtCoord I (setPsi D ψ h) e G where
  q := g.q
  q_hom := g.q_hom
  q_flat := g.q_flat
  q_surj := g.q_surj
  q_affine := g.q_affine
  i := g.i
  i_hom := g.i_hom
  isKernel := g.isKernel
  t := g.t
  t_gen := g.t_gen
  t_mul := g.t_mul
  t_unit := g.t_unit
  t_weight := g.t_weight

def PreU.setPsi (U : PreU I D A G) (ψ) (h) : PreU I (setPsi D ψ h) A G where
  semi := U.semi
  gen := U.gen
  gen_hom := U.gen_hom
  P := U.P
  wA := U.wA
  wA_gen := U.wA_gen
  gt := fun e => gtCoordSetPsi (U.gt e) ψ h
  gt_q := U.gt_q
  gt_t := U.gt_t
  w := U.w
  w_gen := U.w_gen
  w_vals := U.w_vals
  w_compat := U.w_compat
end

theorem exists_preU_setPsi : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (I : Ideal R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) ψ h, ∃ (U' : PreU I (setPsi D ψ h) A G) (hP : U'.P = U.P), U'.gen = U.gen ∧ HEq U'.wA U.wA ∧ ∀ θ f, U.Theta θ f → ∃ θ', U'.Theta θ' f :=
  fun _ _ _ _ _ _ _ _ _ U ψ h => ⟨U.setPsi ψ h, rfl, rfl, HEq.rfl, fun θ _ hθ => ⟨θ, hθ⟩⟩
end GlobalTheory.UU
end
end
