module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle046
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle011
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle162
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGeneric
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle166
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle151
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle185
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle068
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle068

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.TorusModel GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.KernelNoTorsion IsLocalRing
open scoped CategoryTheory.Obj

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {Gt : Over (Sp R)} [GrpObj Gt]
  {Φ : ∀ T, (T ⟶ Gt) ≃ GtPt D T}

theorem isZero_unique {T : Over (Sp R)} {g g' : GtPt D T} (h : g.IsZero) (h' : g'.IsZero) : g = g' :=
  pt_ext (h.1.trans h'.1.symm) fun χ _ _ hJ =>
    (val_corr hJ (h.2 χ) (𝟙 _)).trans (val_corr hJ (h'.2 χ) (𝟙 _)).symm

theorem isZero_of_isAdd {T : Over (Sp R)} {g : GtPt D T} (h : g.IsAdd g g) : g.IsZero := by
  obtain ⟨hb, hv⟩ := (TorusModel.isAdd_iff _ _ _).1 h
  have hb1 : g.b = 1 := mul_eq_left.1 hb.symm
  refine ⟨hb1, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
  have e' : th D y J (cP D T χ) g.b g.b = 1 := by
    rw [hb1, C.face₃]
  have e := hv χ y J hJ
  rw [e', _root_.mul_one] at e
  have e₂ : cv g χ y J = 1 := mul_eq_left.1 e.symm
  exact e₂.trans (val_one _).symm

theorem isZero_one (hΦ : Represents Φ) (T : Over (Sp R)) : (Φ T 1).IsZero := by
  have h := hΦ.2 T 1 1
  rw [_root_.mul_one] at h
  exact isZero_of_isAdd h

theorem tors_iff (hΦ : Represents Φ) (k : ℕ) {T : Over (Sp R)} (x : T ⟶ Gt) :
    FlatIsoUnitGenerator.GtTors k (Φ T x) ↔ x ^ k = 1 := by
  constructor
  · rintro ⟨_, ⟨u, u0, us, rfl⟩, hz⟩
    have : ∀ i : Fin (k + 1), u i = Φ T (x ^ (i : ℕ)) := fun i => by
      induction i using Fin.induction with
      | zero => exact isZero_unique u0 (by simpa using isZero_one hΦ T)
      | succ i ih =>
        have h := us i
        rw [ih] at h
        rw [Fin.val_succ, pow_succ]
        exact isAdd_unique h (hΦ.2 T _ _)
    exact (Φ T).injective ((this (Fin.last k)).symm.trans (isZero_unique hz (isZero_one hΦ T)))
  · intro hx
    refine ⟨Φ T (x ^ k), ⟨fun i => Φ T (x ^ (i : ℕ)), by simpa using isZero_one hΦ T, fun i => ?_, rfl⟩,
      hx ▸ isZero_one hΦ T⟩
    simp only [Fin.val_succ, Fin.val_castSucc, pow_succ]
    exact hΦ.2 T _ _

theorem isPull_iff_comp (hΦ : Represents Φ) {T T' : Over (Sp R)} (h : T' ⟶ T) (x : T ⟶ Gt) (x' : T' ⟶ Gt) :
    GtPt.IsPull h.left (Φ T x) (Φ T' x') ↔ h ≫ x = x' :=
  ⟨fun H => (Φ T').injective (isPull_unique (hΦ.1 _ _ h x) H), fun H => H ▸ hΦ.1 _ _ h x⟩

theorem exists_represents [IsNoetherianRing R] (D : DegPre R) :
    ∃ (Gt : Over (Sp R)) (_ : GrpObj Gt) (_ : IsCommMonObj Gt) (Φ : ∀ T, (T ⟶ Gt) ≃ GtPt D T), Represents Φ ∧
      ∀ k : ℕ, 1 ≤ k → IsFinite (torsion Gt k).hom ∧ Flat (torsion Gt k).hom := by
  have hL := abelianSchemeLaws_all.1
  obtain ⟨H, _, _, hH⟩ := exists_isGt hL.globalFns (splitExt D)
  obtain ⟨Φ, hΦ⟩ := exists_points hL.globalFns hH
  refine ⟨H, inferInstance, inferInstance, Φ, hΦ, fun k hk => ?_⟩
  obtain ⟨h₁, h₂, -⟩ := hL.mulN _ D.P k hk
  have h₁' : IsFinite (𝟙 D.P.A ^ k).left := h₁
  have h₂' : Flat (𝟙 D.P.A ^ k).left := h₂
  rw [← MulEtaleDvr.mulN_eq_pow] at h₁' h₂'
  have P := MulEtaleDvr.isPullback_torsion D.P.A k
  exact isFinite_flat_torsion_of_isGt _ (splitExt D) H hH k hk (MorphismProperty.of_isPullback (P := @IsFinite) P h₁')
    (MorphismProperty.of_isPullback (P := @Flat) P h₂')

end Points

theorem isAdicColimit_of_isFinite {R : Type} [CommRing R] [IsLocalRing R] (hc : IsAdicComplete (maximalIdeal R) R)
    (N : Over (Sp R)) [IsFinite N.hom] [Flat N.hom] : IsAdicColimit (maximalIdeal R) N := by
  have : IsAffine N.left := isAffine_of_isAffineHom N.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (N.left.isoSpec.inv ≫ N.hom)
  have hf : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hl : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at hf
  rw [HasRingHomProperty.Spec_iff (P := @Flat)] at hl
  letI : Algebra R Γ(N.left, ⊤) := φ.hom.toAlgebra
  have : Module.Finite R Γ(N.left, ⊤) := hf
  have : Module.Flat R Γ(N.left, ⊤) := hl
  have H := isAdicColimit_of_finite_flat (maximalIdeal R) (RingHom.id R) (by rwa [Ideal.map_id])
    (fun a ha => ⟨1, by rwa [Ideal.map_id, pow_one]⟩) Γ(N.left, ⊤)
  exact IsAdicColimit.of_iso (Over.isoMk N.left.isoSpec.symm hφ.symm) H

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)}

theorem formalEq_iff {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) {T : Over (Sp R)} (x : T ⟶ G) (g : GtPt D.toPre T) :
    FlatIsoUnitGenerator.FormalEq U x g ↔ IsPointOf U g x := by
  rw [isPointOf_iff_thick]
  refine forall_congr' fun e => and_congr eq_comm (forall_congr' fun χ => ⟨fun h => ?_, fun h => ?_⟩) <;>
  exact corr_of_val D.toPre.P.isLB fun _ _ hJ => (val_corr hJ h (𝟙 _)).symm

end GlobalTheory.TorsionFormCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SpreadGeneric

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (h : A →+* C) (e : g.comp f = h) : spMap g ≫ spMap f = spMap h := by
  subst e
  exact (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

section Algebra
variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

def Near {R' : Type} [CommRing R'] (io : R →+* R') (χ : R' →+* K) (x : R') : Prop :=
  ∃ (F : R) (_ : F ≠ 0) (φ : R' →+* Localization.Away F) (ψ : Localization.Away F →+* K),
    φ.comp io = algebraMap R _ ∧ ψ.comp (algebraMap R _) = algebraMap R K ∧ ψ.comp φ = χ ∧ IsUnit (φ x)

theorem Near.shrink {R' : Type} [CommRing R'] {io : R →+* R'} {χ : R' →+* K} {y : R'} (h : Near io χ y)
    (x : R') (hx : χ x ≠ 0) : Near io χ x := by
  obtain ⟨F, hF, φ, ψ, h1, h2, h3, -⟩ := h
  obtain ⟨⟨a, ⟨s, n, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers F) (φ x)
  simp only at ha
  have hinj := IsFractionRing.injective R K
  have hK : ∀ r : R, ψ (algebraMap R _ r) = algebraMap R K r := fun r => RingHom.congr_fun h2 r
  have ha0 : a ≠ 0 := by
    rintro rfl
    have := congrArg ψ ha
    rw [map_mul, hK, hK, map_zero, ← RingHom.comp_apply, h3] at this
    rcases mul_eq_zero.1 this with h | h
    · exact hx h
    · exact pow_ne_zero n hF (hinj (h.trans (map_zero _).symm))
  have hFa : F * a ≠ 0 := mul_ne_zero hF ha0
  have hu : IsUnit (algebraMap R (Localization.Away (F * a)) (F * a)) :=
    IsLocalization.Away.algebraMap_isUnit (F * a)
  rw [map_mul] at hu
  have huK : IsUnit (algebraMap R K (F * a)) :=
    isUnit_iff_ne_zero.2 fun h => hFa (hinj (h.trans (map_zero _).symm))
  let ρ : Localization.Away F →+* Localization.Away (F * a) :=
    IsLocalization.Away.lift F (isUnit_of_mul_isUnit_left hu)
  have hρ : ρ.comp (algebraMap R _) = algebraMap R _ := IsLocalization.Away.lift_comp _ _
  let ψ' : Localization.Away (F * a) →+* K := IsLocalization.Away.lift (F * a) huK
  have hψ' : ψ'.comp (algebraMap R _) = algebraMap R K := IsLocalization.Away.lift_comp _ _
  have hc : ψ'.comp ρ = ψ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers F)
    rw [RingHom.comp_assoc, hρ, hψ', h2]
  refine ⟨F * a, hFa, ρ.comp φ, ψ', ?_, hψ', ?_, ?_⟩
  · rw [RingHom.comp_assoc, h1, hρ]
  · rw [← RingHom.comp_assoc, hc, h3]
  · have := congrArg ρ ha
    rw [map_mul, show ρ (algebraMap R _ a) = algebraMap R _ a from RingHom.congr_fun hρ a] at this
    exact isUnit_of_mul_isUnit_left (this ▸ isUnit_of_mul_isUnit_right hu)

omit [IsDomain R] [IsFractionRing R K] in
theorem Near.away {R' : Type} [CommRing R'] {io : R →+* R'} {χ : R' →+* K} {x : R'} (h : Near io χ x)
    (χ' : Localization.Away x →+* K) (e : χ'.comp (algebraMap R' _) = χ) :
    Near ((algebraMap R' (Localization.Away x)).comp io) χ' 1 := by
  obtain ⟨F, hF, φ, ψ, h1, h2, h3, h4⟩ := h
  have hρ : (IsLocalization.Away.lift (S := Localization.Away x) x h4).comp (algebraMap R' _) = φ :=
    IsLocalization.Away.lift_comp _ _
  refine ⟨F, hF, IsLocalization.Away.lift x h4, ψ, ?_, h2, ?_, by simp⟩
  · rw [← RingHom.comp_assoc, hρ, h1]
  · apply IsLocalization.ringHom_ext (Submonoid.powers x)
    rw [RingHom.comp_assoc, hρ, h3, e]

omit [IsFractionRing R K] in
theorem isDomain_away {f : R} (hf : f ≠ 0) : IsDomain (Localization.Away f) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)

theorem isFractionRing_away {f : R} (hf : f ≠ 0) (ψ : Localization.Away f →+* K)
    (e : ψ.comp (algebraMap R _) = algebraMap R K) :
    letI := ψ.toAlgebra
    IsFractionRing (Localization.Away f) K := by
  letI := ψ.toAlgebra
  haveI : IsScalarTower R (Localization.Away f) K := IsScalarTower.of_algebraMap_eq' e.symm
  exact IsFractionRing.isFractionRing_of_isLocalization (Submonoid.powers f) _ K
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)

end Algebra

theorem exists_spread : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) Mat κ (w w' : J) [Finite J] (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (t : TObj g (N' ^ 2) J b (spMap (algebraMap R K) ≫ spMap β)), t.HasTh (𝟙 _) (fun a => algebraMap R K (v a)) → t.Shape Mat κ → t.Prim w w' → ∃ (f : R) (_ : f ≠ 0) (t' : TObj g (N' ^ 2) J b (spMap (algebraMap R (Localization.Away f)) ≫ spMap β)) (ψ : Localization.Away f →+* K), ψ.comp (algebraMap R _) = algebraMap R K ∧ TMap t t' (spMap ψ) ∧ t'.HasTh (𝟙 _) (fun a => algebraMap R _ (v a)) ∧ t'.Shape Mat κ ∧ t'.Prim w w' := by
  intro l1 l2 o _ g N' J b Mat κ w w' _ R K _ _ _ _ _ _ β v t hth hsh hpr
  obtain ⟨f, hf, ψ₁, P', φ, e₁, hg, hpb, hL⟩ := GlobalTheory.T.exists_principallyPolarised_model_localizationAway R K t.pol
  haveI := isDomain_away hf
  letI := ψ₁.toAlgebra
  haveI := isFractionRing_away hf ψ₁ e₁
  have key : ∀ (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (φ : t.A.left ⟶ P'.A.left),
      s = spMap (algebraMap (Localization.Away f) K) ≫ spMap ((algebraMap R (Localization.Away f)).comp β) →
      IsGrpPullback t.A P'.A (spMap ψ₁) φ → LBIso t.L (P'.L.pull φ) →
      ∃ (f₁ : Localization.Away f) (_ : f₁ ≠ 0) (s' : Sp (Localization.Away f₁) ⟶ Sp o)
        (t' : TObj g (N' ^ 2) J b s') (ψ : Localization.Away f₁ →+* K),
        s' = spMap (algebraMap _ (Localization.Away f₁)) ≫ spMap ((algebraMap R (Localization.Away f)).comp β) ∧
        ψ.comp (algebraMap _ _) = ψ₁ ∧ TMap t t' (spMap ψ) := by
    rintro s t φ rfl h1 h2
    obtain ⟨f₁, h, t', ψ, h3, h4⟩ := GlobalTheory.T.thetaLevel_endomorphisms_spread_over_basicOpen l1 l2 o g (N' ^ 2) J b (Localization.Away f) K
      ((algebraMap R (Localization.Away f)).comp β) t P' φ hg h1 h2
    exact ⟨f₁, h, _, t', ψ, rfl, h3, h4⟩
  obtain ⟨f₁, hf₁, s₂, t₂, ψ₂, hs₂, e₂, hm⟩ := key _ t φ (by
    rw [spMap_comp_eq _ _ _ rfl, spMap_comp_eq _ _ _ rfl, ← RingHom.comp_assoc]
    exact congrArg (fun r => spMap (RingHom.comp r β)) e₁.symm) hpb hL
  haveI := isDomain_away hf₁
  letI := ψ₂.toAlgebra
  haveI := isFractionRing_away (K := K) hf₁ ψ₂ e₂
  let io : R →+* Localization.Away f₁ := (algebraMap (Localization.Away f) _).comp (algebraMap R _)
  have hio : ψ₂.comp io = algebraMap R K := by rw [← RingHom.comp_assoc, e₂, e₁]
  have hv : (fun a => algebraMap (Localization.Away f₁) K (io (v a))) = fun a => algebraMap R K (v a) :=
    funext fun a => RingHom.congr_fun hio (v a)
  obtain ⟨f₂, hf₂, H⟩ := GlobalTheory.T.exists_thetaPoint_shape_primitivity_near_generic l1 l2 o g N' J b Mat κ w w' (Localization.Away f₁) K s₂ _ t₂ t
    (fun a => io (v a)) hm (hv ▸ hth) hsh hpr
  have n0 : Near (algebraMap R (Localization.Away f)) ψ₁ 1 :=
    ⟨f, hf, RingHom.id _, ψ₁, rfl, e₁, rfl, isUnit_one⟩
  have n1 := (n0.shrink f₁ fun h =>
    hf₁ (IsFractionRing.injective (Localization.Away f) K (h.trans (map_zero _).symm))).away ψ₂ e₂
  obtain ⟨F, hF, ρ, ψ, h1, h2, h3, h4⟩ := n1.shrink f₂ fun h =>
    hf₂ (IsFractionRing.injective (Localization.Away f₁) K (h.trans (map_zero _).symm))
  obtain ⟨t', ht'⟩ := GlobalTheory.tObj_pull o g (N' ^ 2) J b _ _ s₂
    (spMap (algebraMap R (Localization.Away F)) ≫ spMap β) (spMap ρ) t₂ (by
      rw [hs₂, spMap_comp_eq _ _ _ rfl, spMap_comp_eq _ _ _ rfl, spMap_comp_eq _ _ _ rfl, ← h1])
  obtain ⟨c1, c2, c3⟩ := H _ ρ _ t' h4 ht'
  refine ⟨F, hF, t', ψ, h2, ?_, ?_, c2, c3⟩
  · refine ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g (N' ^ 2) J b _ _ _ _ _ _ t₂ t' t).2 (spMap ρ) (spMap ψ) ht').2 ?_
    rw [spMap_comp_eq _ _ _ h3]
    exact hm
  · have : (fun a => ρ (io (v a))) = fun a => algebraMap R (Localization.Away F) (v a) :=
      funext fun a => RingHom.congr_fun h1 (v a)
    exact this ▸ c1

end GlobalTheory.SpreadGeneric
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.EndBuild

theorem pow_val_natCast {A : Type} [Monoid A] {k : ℕ} (y : A) (hy : y ^ k = 1) (m : ℕ) :
    y ^ ((m : ZMod k)).val = y ^ m := by
  rw [ZMod.val_natCast, ← pow_eq_pow_mod m hy]

def labMap {g : ℕ} {J : Type} (k : ℕ) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (i : Option J) (h : Ix g k) : Ix g k :=
  i.elim (-h) (fun j i' => ((∑ c, (Mat j i' c : ZMod k).val * (h c).val : ℕ) : ZMod k))

theorem linComb_eq_prod {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ}
    (y : Fin r → (T ⟶ A)) (a : Fin r → ℕ) : Out.linComb y a = ∏ i, y i ^ a i := by
  rw [Out.linComb, List.prod_ofFn]

theorem lab_comp {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} [NeZero k] {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ} (ht : t.Shape Mat κ)
    (i : Option J) (h : Ix g k) :
    t.lab h ≫ (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A) = t.lab (labMap k Mat i h) := by
  haveI := t.ab.comm
  cases i with
  | none =>
    simp only [Option.elim, labMap]
    rw [GrpObj.comp_inv, Category.comp_id]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [TObj.lab, TObj.lab, linComb_eq_prod, linComb_eq_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun c _ => ?_
    rw [← pow_add, ← pow_val_natCast _ (t.torsion c)]
    simp
  | some j =>
    simp only [Option.elim, labMap]
    haveI := t.hom j
    have e : t.lab h ≫ t.act j = ∏ c, (t.pt c ≫ t.act j) ^ (h c).val := by
      rw [TObj.lab, linComb_eq_prod]
      have := map_prod (IsMonHom.monoidHom (t.act j) (Out.baseOver S)) (fun c => t.pt c ^ (h c).val) Finset.univ
      simp only [map_pow] at this
      exact this
    rw [e, TObj.lab, linComb_eq_prod]
    simp only [(ht j).1, TObj.lab, linComb_eq_prod, ← Finset.prod_pow, ← pow_mul]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [pow_val_natCast _ (t.torsion c), Finset.prod_pow_eq_pow_sum]

theorem graphIdeal_le {R σ₁ σ₂ : Type} [CommRing R] {Y Y' X₁ X₂ X₁' X₂' : Scheme.{0}} (s : Y ⟶ Sp R) (s' : Y' ⟶ Sp R)
    (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁) (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂)
    (M₁' : LB X₁') (th₁' : σ₁ → M₁'.Sec) (a₁' : Y' ⟶ X₁') (M₂' : LB X₂') (th₂' : σ₂ → M₂'.Sec) (a₂' : Y' ⟶ X₂')
    (e : Y ⟶ Y') (he : e ≫ s' = s)
    (h₁ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (w : σ₁ → T),
      SecCoord M₁ th₁ (y ≫ a₁) w → SecCoord M₁' th₁' (y ≫ e ≫ a₁') w)
    (h₂ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (w : σ₂ → T),
      SecCoord M₂ th₂ (y ≫ a₂) w → SecCoord M₂' th₂' (y ≫ e ≫ a₂') w) :
    graphIdeal s' M₁' th₁' a₁' M₂' th₂' a₂' ≤ graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ := by
  unfold graphIdeal
  refine le_iInf fun T => le_iInf fun _ => le_iInf fun β => le_iInf fun y => le_iInf fun v₁ => le_iInf fun v₂ =>
    le_iInf fun hy => ?_
  refine iInf_le_of_le T <| iInf_le_of_le inferInstance <| iInf_le_of_le β <| iInf_le_of_le (y ≫ e) <|
    iInf_le_of_le v₁ <| iInf_le_of_le v₂ <| iInf_le_of_le ⟨?_, ?_, ?_⟩ le_rfl
  · rw [Category.assoc, he, hy.1]
  · rw [Category.assoc]; exact h₁ _ _ _ hy.2.1
  · rw [Category.assoc]; exact h₂ _ _ _ hy.2.2

theorem graphIdeal_eq {R σ₁ σ₂ : Type} [CommRing R] {Y Y' X₁ X₂ X₁' X₂' : Scheme.{0}} (s : Y ⟶ Sp R) (s' : Y' ⟶ Sp R)
    (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁) (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂)
    (M₁' : LB X₁') (th₁' : σ₁ → M₁'.Sec) (a₁' : Y' ⟶ X₁') (M₂' : LB X₂') (th₂' : σ₂ → M₂'.Sec) (a₂' : Y' ⟶ X₂')
    (e : Y ⟶ Y') [IsIso e] (he : e ≫ s' = s)
    (h₁ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (w : σ₁ → T),
      SecCoord M₁ th₁ (y ≫ a₁) w ↔ SecCoord M₁' th₁' (y ≫ e ≫ a₁') w)
    (h₂ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (w : σ₂ → T),
      SecCoord M₂ th₂ (y ≫ a₂) w ↔ SecCoord M₂' th₂' (y ≫ e ≫ a₂') w) :
    graphIdeal s' M₁' th₁' a₁' M₂' th₂' a₂' = graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ := by
  refine le_antisymm (graphIdeal_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ e he (fun T _ y w => (h₁ T y w).1)
    (fun T _ y w => (h₂ T y w).1)) (graphIdeal_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ (inv e) (by rw [← he, IsIso.inv_hom_id_assoc])
    (fun T _ y w hw => ?_) (fun T _ y w hw => ?_))
  · rw [← Category.assoc, h₁]; simpa using hw
  · rw [← Category.assoc, h₂]; simpa using hw

theorem cut_fibre {o R K : Type} [CommRing o] [CommRing R] [Field K] {g N m : ℕ} [NeZero (N ^ 2)] {J : Type}
    {b : TBase o (N ^ 2)} {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ} (i : Option J) (Q : Polynomial ℚ) (d : ℕ)
    {s : Sp K ⟶ Sp o} (t : TObj g (N ^ 2) J b s) (ht : t.Shape Mat κ)
    (σ : Ix g (N ^ 2) → LB.Sec (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 _))))
    (hcut : ∀ (p q : Ix g (N ^ 2) → Ix g (N ^ 2) → K) (f : t.A ⟶ t.A), f = i.elim (𝟙 t.A)⁻¹ t.act →
      (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ N)).left (p h) ∧
        SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) ((t.lab h ≫ f) ^ N)).left (q h)) →
      CutBy (graphIdeal (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _) _ σ
        (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left) Q d (fun h i => p h i.1 * q h i.2))
    (Z : Over (Sp R)) (M : LB Z.left) (hM : M.IsLB) (th : Ix g (N ^ 2) → M.Sec)
    (sc : Ix g (N ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g (N ^ 2) → Ix g (N ^ 2) → R)
    (hp : ∀ h, SecCoord M th (sc h).left (p h)) (x : R →+* K) (φ : t.A.left ⟶ Z.left)
    (hφ : IsPullback φ t.A.hom Z.hom (spMap x))
    (hσ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t.A).left) (w : Ix g (N ^ 2) → T),
      SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ φ) w)
    (hl : ∀ h, (t.lab h ^ N).left ≫ φ = spMap x ≫ (sc h).left) :
    CutBy (graphIdeal (pullback.snd Z.hom (spMap x)) M th (pullback.fst _ _) M th
      (hφ.isoPullback.inv ≫ (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A).left ≫ φ)) Q d
      (fun h c => x (p h c.1 * p (labMap (N ^ 2) Mat i h) c.2)) := by
  have hpt : ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ N)).left (fun a => x (p h a)) := by
    intro h
    refine (hσ K _ _).2 ?_
    have e : (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ N)).left ≫ (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ φ =
        spMap x ≫ (sc h).left := by
      rw [← hl h, ← Category.assoc, ← Over.comp_left, lift_snd]
    have := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ M _ th R (sc h).left (p h) hM (hp h)).1 K x
    exact e ▸ this
  have H := hcut (fun h a => x (p h a)) (fun h a => x (p (labMap (N ^ 2) Mat i h) a)) _ rfl
    (fun h => ⟨hpt h, by rw [lab_comp t ht]; exact hpt _⟩)
  haveI : IsIso (snd (Over.mk (𝟙 (Sp K))) t.A).left :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 (Sp K)) t.A.hom))
  have hs : (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ t.A.hom = (fst (Over.mk (𝟙 (Sp K))) t.A).left :=
    (pullback.condition (f := 𝟙 (Sp K)) (g := t.A.hom)).symm.trans (Category.comp_id _)
  rw [graphIdeal_eq (fst (Over.mk (𝟙 (Sp K))) t.A).left (pullback.snd Z.hom (spMap x)) _ σ (𝟙 _) _ σ
    (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A))).left M th _ M th _
    ((snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ hφ.isoPullback.hom)]
  · simpa only [map_mul] using H
  · rw [Category.assoc, IsPullback.isoPullback_hom_snd]; exact hs
  · intro T _ y w
    rw [hσ, Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst, Category.id_comp]
  · intro T _ y w
    rw [hσ, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc _ _ φ,
      ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc]

theorem exists_endomorphisms : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) → ∃ F : Option J → (Z ⟶ Z), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), t'.Shape Mat κ → (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ i : Option J, φ ≫ (F i).left = (i.elim (𝟙 t'.A)⁻¹ t'.act : t'.A ⟶ t'.A).left ≫ φ) := by
  intro hL hL2 g J _ Mat κ n hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.graph_inversion_endomorphism_cut_bounded_degree hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b R _ _ _ β v Z I M th sc p hvd hPF hfib => ?_⟩
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨hrep, hsm, -, hp⟩ := hPF
  have hprop := (GlobalTheory.T.isProj_proper_relAmple_of_projectiveCoordinateRep R _ I Z M th hrep).2.1
  have hsm' : Smooth Z.hom := SmoothOfRelativeDimension.smooth g _
  have key : ∀ i : Option J, ∃ F : Z ⟶ Z, ∀ (K : Type) [Field K] (x : R →+* K) (f : pullback Z.hom (spMap x) ⟶ Z.left),
      (∃ (_ : IsAlgClosed K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left)
        (hφ : IsPullback φ t'.A.hom Z.hom (spMap x)), t'.Shape Mat κ ∧
        (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧
        (∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) ∧
        f = hφ.isoPullback.inv ≫ (i.elim (𝟙 t'.A)⁻¹ t'.act : t'.A ⟶ t'.A).left ≫ φ) →
      f = pullback.fst _ _ ≫ F.left := by
    intro i
    obtain ⟨Q, d, hQ⟩ := hj₀ j hj o b i
    refine GlobalTheory.T.exists_family_morphism_from_veryDense_graphs R _ _ (Ix g ((n ^ j) ^ 2)) Z Z I I M M th th p (fun h => p (labMap _ Mat i h)) Q d _
      hrep hrep hprop hprop hsm' ?_ ?_
    · rintro K _ x f ⟨_, t', φ, hφ, ht, ⟨σ, hE, hσ⟩, hl, rfl⟩
      refine ⟨?_, cut_fibre (m := n ^ 2) i Q d t' ht σ ?_ Z M hrep.1 th sc p hp x φ hφ hσ hl⟩
      · rw [Category.assoc, Category.assoc, hφ.w, ← Category.assoc (Option.elim _ _ _ : t'.A ⟶ t'.A).left, Over.w,
          ← Category.assoc, IsPullback.isoPullback_inv_snd]
      · have e : spMap x ≫ spMap β = spMap (x.comp β) := by rw [← Spec.map_comp]; rfl
        clear hσ hl hφ φ
        generalize spMap x ≫ spMap β = s at e t' ht σ hE
        subst e
        exact fun p' q' f hf h => hQ K (x.comp β) t' σ p' q' f ht hf hE h
    · intro q r hq hr
      obtain ⟨P, ⟨K, _, _, x, t', hx, ht, hth⟩, hP⟩ := hvd q r hq hr
      obtain ⟨φ, hφ, hσ, -, hl⟩ := hfib K x t' ht hth
      exact ⟨P, ⟨K, _, x, _, hx, inferInstance, t', φ, hφ, ht, hσ, hl, rfl⟩, hP⟩
  choose F hF using key
  refine ⟨F, fun K _ _ x t' φ ht hfb i => ?_⟩
  obtain ⟨hφ, hσ, -, hl⟩ := hfb
  have := hF i K x _ ⟨inferInstance, t', φ, hφ, ht, hσ, hl, rfl⟩
  rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_fst_assoc] at this
  exact this.symm

end GlobalTheory.ZM.EndBuild
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_family_addition_morphism_thetaLevel : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) → ∃ m : Z ⊗ Z ⟶ Z, (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ φ₂ : (t'.A ⊗ t'.A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[t'.A]).left ≫ φ) := by
  first | exact @GlobalTheory.ZM.BuildAdd.exists_add | exact GlobalTheory.ZM.BuildAdd.exists_add | (intros; apply GlobalTheory.ZM.BuildAdd.exists_add <;> assumption)
end
