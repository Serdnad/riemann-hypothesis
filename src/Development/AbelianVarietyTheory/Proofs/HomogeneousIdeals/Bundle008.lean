module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle007
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ContinuousAevalMvPolynomial
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOpenPartialHomeomorphAnalytic
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasRationalTorsionIffMemRange
import Aesop.Frontend.Tactic
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.Sheaves.Init
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace GlobalTheory.QCoh.Qcqs

universe u

namespace GlobalTheory.GaloisDescent


set_option backward.isDefEq.respectTransparency false in
theorem ideal_le_comap_appLE {X Y : Scheme.{u}} (f : Y ⟶ X) {J : X.IdealSheafData}
    {I : Y.IdealSheafData} (h : J.comap f ≤ I) (U : X.affineOpens) (V : Y.affineOpens)
    (e : V.1 ≤ f ⁻¹ᵁ U.1) : J.ideal U ≤ (I.ideal V).comap (f.appLE U V e).hom := by
  intro x hx
  have h1 : (I.subschemeι ≫ f).app U x = 0 :=
    (I.subschemeι ≫ f).ideal_ker_le U (Scheme.IdealSheafData.le_map_iff_comap_le.2 h U hx)
  rw [Ideal.mem_comap, ← I.ker_subschemeι_app V, RingHom.mem_ker, Scheme.Hom.app_eq_appLE,
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE,
    CommRingCat.comp_apply, h1, map_zero]

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {X Y : Scheme.{u}}
  {p : X ⟶ Spec (.of K)} {q : Y ⟶ Spec (.of L)} {π : Y ⟶ X}
  (H : IsPullback π q p (Spec.map (CommRingCat.ofHom (algebraMap K L)))) {G : Type*}

include H

theorem isPushout_app {U : X.Opens} (hU : IsAffineOpen U) :
    IsPushout (baseRingHom p U) (CommRingCat.ofHom (algebraMap K L)) (π.app U)
      (baseRingHom q (π ⁻¹ᵁ U)) := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := π ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [baseRingHom]
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · simp [baseRingHom]


set_option backward.isDefEq.respectTransparency false in
theorem idealSheaf_comap_map_of_stable (s : G → L →+* L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (a : G → (Y ⟶ Y)) (haπ : ∀ g, a g ≫ π = π)
    (haq : ∀ g, a g ≫ q = q ≫ Spec.map (CommRingCat.ofHom (s g)))
    (I : Y.IdealSheafData) (hI : ∀ g, I.comap (a g) ≤ I) : (I.map π).comap π = I := by
  have : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  refine le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun U : X.affineOpens => ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩) ?_ fun U => ?_
  · change ⨆ U : X.affineOpens, π ⁻¹ᵁ U.1 = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  · let := (π.app U).hom.toAlgebra
    let := (baseRingHom p U).hom.toAlgebra
    let := (baseRingHom q (π ⁻¹ᵁ U)).hom.toAlgebra
    let := (baseRingHom (π ≫ p) (π ⁻¹ᵁ U)).hom.toAlgebra
    have : IsScalarTower K Γ(X, U) Γ(Y, π ⁻¹ᵁ U) :=
      .of_algebraMap_eq fun r ↦ (app_baseRingHom π p U r).symm
    have : IsScalarTower K L Γ(Y, π ⁻¹ᵁ U) :=
      .of_algebraMap_eq fun r ↦ (baseRingHom_algebraMap (R := .of K) (L := .of L) H _ r).symm
    have hpo : Algebra.IsPushout K Γ(X, U) L Γ(Y, π ⁻¹ᵁ U) :=
      CommRingCat.isPushout_iff_isPushout.mp (isPushout_app H U.2)
    have e : ∀ g, π ⁻¹ᵁ U.1 ≤ a g ⁻¹ᵁ (π ⁻¹ᵁ U.1) := fun g => by
      rw [← Scheme.Hom.comp_preimage, haπ]
    have h1 : ∀ g, π.app U ≫ (a g).appLE _ _ (e g) = π.app U := fun g => by
      simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, haπ]
    have h2 : ∀ g, baseRingHom q (π ⁻¹ᵁ U) ≫ (a g).appLE _ _ (e g) =
        CommRingCat.ofHom (s g) ≫ baseRingHom q (π ⁻¹ᵁ U) := fun g => by
      rw [← baseRingHom_comp_SpecMap, ← haq]
      simp only [baseRingHom, Category.assoc, Scheme.Hom.appLE_comp_appLE]
    have key := ideal_map_comap_of_stable hpo.symm.out s hs
      (fun g => ((a g).appLE _ _ (e g)).hom.toAddMonoidHom) (fun g l x => by
        have h3 := congr($(h1 g) x)
        have h4 := congr($(h2 g) l)
        change (a g).appLE _ _ (e g) (baseRingHom q (π ⁻¹ᵁ U) l * π.app U x) =
          baseRingHom q (π ⁻¹ᵁ U) (s g l) * π.app U x
        rw [map_mul]
        exact congrArg₂ (· * ·) h4 h3)
      (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩)
      (fun g x hx => ideal_le_comap_appLE (a g) (hI g) ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩
        ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩ (e g) hx)
    rw [← key, Ideal.map_le_iff_le_comap]
    intro x hx
    have h5 := ideal_le_comap_appLE π (le_refl ((I.map π).comap π)) U
      ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩ le_rfl (x := x)
      (by rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom]; exact hx)
    rw [← Scheme.Hom.app_eq_appLE] at h5
    exact h5

theorem idealSheaf_map_comap (J : X.IdealSheafData) : (J.comap π).map π = J := by
  have : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    .of_isDominant _
  have h : IsSchemeTheoreticallyDominant (pullback.snd π J.subschemeι) :=
    .of_isPullback ((IsPullback.of_hasPullback π J.subschemeι).flip.paste_vert H).flip
  rw [Scheme.IdealSheafData.comap, Scheme.IdealSheafData.map_ker, pullback.condition,
    Scheme.Hom.ker_comp, h.ker_eq_bot, Scheme.IdealSheafData.map_bot,
    Scheme.IdealSheafData.ker_subschemeι]

theorem idealSheaf_comap_injective :
    Function.Injective fun J : X.IdealSheafData => J.comap π := fun J J' h => by
  rw [← idealSheaf_map_comap H J, ← idealSheaf_map_comap H J']
  exact congrArg (·.map π) h

noncomputable def twist (σ : L →ₐ[K] L) : Y ⟶ Y :=
  H.lift π (q ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
    rw [H.w, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact σ.comp_algebraMap.symm)

@[reassoc (attr := simp)]
theorem twist_fst (σ : L →ₐ[K] L) : twist H σ ≫ π = π := H.lift_fst _ _ _

theorem twist_snd (σ : L →ₐ[K] L) :
    twist H σ ≫ q = q ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := H.lift_snd _ _ _

theorem idealSheaf_stable_iff_exists_comap (s : G → L →ₐ[K] L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L)) (I : Y.IdealSheafData) :
    (∀ g, I.comap (twist H (s g)) ≤ I) ↔ ∃! J : X.IdealSheafData, J.comap π = I := by
  constructor
  · intro hI
    have h1 := idealSheaf_comap_map_of_stable H (fun g => (s g).toRingHom) hs
      (fun g => twist H (s g)) (fun g => twist_fst H _) (fun g => twist_snd H _) I hI
    exact ⟨_, h1, fun J hJ => idealSheaf_comap_injective H (hJ.trans h1.symm)⟩
  · rintro ⟨J, rfl, -⟩ g
    rw [← Scheme.IdealSheafData.comap_comp, twist_fst]

end GlobalTheory.GaloisDescent
end

section

namespace GlobalTheory.AffinePoints

open Topology Filter Set MvPolynomial
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {A : Type*} [CommRing A] [Algebra 𝕜 A] {d : ℕ}

structure IsAlgebraicChart (e : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜)) : Prop where
  exists_eq_div : ∃ (x : Fin d → A) (s : A), ∀ p ∈ e.source, p s ≠ 0 ∧ ∀ i, e p i = p (x i) / p s
  analyticOnNhd : ∀ a, AnalyticOnNhd 𝕜 (fun z => e.symm z a) e.target

variable [CompleteSpace 𝕜]

theorem exists_isAlgebraicChart_of_etale (g : MvPolynomial (Fin d) 𝕜 →ₐ[𝕜] A) (hg : g.Etale)
    (p : A →ₐ[𝕜] 𝕜) :
    ∃ e : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜), IsAlgebraicChart e ∧ p ∈ e.source ∧
      (e : (A →ₐ[𝕜] 𝕜) → Fin d → 𝕜) = coords g := by
  obtain ⟨e, hp, he, ha⟩ := exists_chart_of_etale g hg p
  refine ⟨e, ⟨⟨fun i => g (X i), 1, fun q _ => ⟨by simp, fun i => ?_⟩⟩, ha⟩, hp, he⟩
  rw [he]
  simp [coords]

theorem exists_isAlgebraicChart_of_away (s : A) (B : Type*) [CommRing B] [Algebra 𝕜 B]
    [Algebra A B] [IsScalarTower 𝕜 A B] [IsLocalization.Away s B]
    [Algebra.IsStandardSmoothOfRelativeDimension d 𝕜 B] (p : A →ₐ[𝕜] 𝕜) (hp : p s ≠ 0) :
    ∃ e : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜), IsAlgebraicChart e ∧ p ∈ e.source := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial d 𝕜 B
  have hj : IsOpenEmbedding (comap (IsScalarTower.toAlgHom 𝕜 A B) : (B →ₐ[𝕜] 𝕜) → (A →ₐ[𝕜] 𝕜)) :=
    isOpenEmbedding_comap_away s
  obtain ⟨q, rfl⟩ : p ∈ range (comap (IsScalarTower.toAlgHom 𝕜 A B) : (B →ₐ[𝕜] 𝕜) → (A →ₐ[𝕜] 𝕜)) := by
    rw [range_comap_away s]
    exact hp
  have : Nonempty (B →ₐ[𝕜] 𝕜) := ⟨q⟩
  obtain ⟨F, hFs, hFt, hFc⟩ : ∃ F : OpenPartialHomeomorph (B →ₐ[𝕜] 𝕜) (A →ₐ[𝕜] 𝕜),
      F.source = univ ∧ F.target = range (comap (IsScalarTower.toAlgHom 𝕜 A B)) ∧
      ⇑F = comap (IsScalarTower.toAlgHom 𝕜 A B) :=
    ⟨IsOpenEmbedding.toOpenPartialHomeomorph _ hj, by simp, by simp, by simp⟩
  have hinv : ∀ q', F.symm (comap (IsScalarTower.toAlgHom 𝕜 A B) q') = q' := fun q' => by
    have := F.left_inv (x := q') (by rw [hFs]; trivial)
    rwa [hFc] at this
  obtain ⟨eB, heB, hqB, -⟩ := exists_isAlgebraicChart_of_etale g hg q
  obtain ⟨xB, sB, hB⟩ := heB.exists_eq_div
  obtain ⟨⟨b, hb⟩, hxb⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers s) xB
  obtain ⟨⟨c, ⟨u, hu⟩⟩, hcu⟩ := IsLocalization.surj (Submonoid.powers s) sB
  have hxb' : ∀ i, ∃ a, algebraMap A B a = b • xB i := fun i => hxb i
  choose a ha using hxb'
  have hbu : IsUnit (algebraMap A B b) := IsLocalization.map_units B (⟨b, hb⟩ : Submonoid.powers s)
  have huu : IsUnit (algebraMap A B u) := IsLocalization.map_units B (⟨u, hu⟩ : Submonoid.powers s)
  refine ⟨F.symm.trans eB, ⟨⟨fun i => a i * u, c * b, ?_⟩, fun a' => ?_⟩, ?_⟩
  · rintro p' ⟨hp'1, hp'2⟩
    have hp'3 : p' ∈ F.target := hp'1
    rw [hFt] at hp'3
    obtain ⟨q', rfl⟩ := hp'3
    have hp'4 : F.symm (comap (IsScalarTower.toAlgHom 𝕜 A B) q') ∈ eB.source := hp'2
    rw [hinv] at hp'4
    have h1 : ∀ i, q' (xB i) = q' (algebraMap A B (a i)) / q' (algebraMap A B b) := fun i =>
      apply_eq_div_of_mul_eq q' hbu (by rw [ha i, Algebra.smul_def, mul_comm])
    have h2 : q' sB = q' (algebraMap A B c) / q' (algebraMap A B u) :=
      apply_eq_div_of_mul_eq q' huu hcu
    have hb0 : q' (algebraMap A B b) ≠ 0 := (hbu.map q').ne_zero
    have hu0 : q' (algebraMap A B u) ≠ 0 := (huu.map q').ne_zero
    have hs0 : q' sB ≠ 0 := (hB q' hp'4).1
    have hc0 : q' (algebraMap A B c) ≠ 0 := by
      intro h0
      rw [h2, h0, zero_div] at hs0
      exact hs0 rfl
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hinv, comap_apply,
      IsScalarTower.toAlgHom_apply, map_mul]
    refine ⟨mul_ne_zero hc0 hb0, fun i => ?_⟩
    rw [(hB q' hp'4).2 i, h1 i, h2]
    field_simp
  · have hfun : (fun z => (F.symm.trans eB).symm z a') = fun z => eB.symm z (algebraMap A B a') := by
      funext z
      simp [hFc, comap_apply]
    rw [hfun]
    exact (heB.analyticOnNhd _).mono fun z hz => hz.1
  · refine ⟨?_, ?_⟩
    · show _ ∈ F.target
      rw [hFt]
      exact mem_range_self q
    · show F.symm _ ∈ eB.source
      rw [hinv]
      exact hqB

end GlobalTheory.AffinePoints
end

section

namespace GlobalTheory

open WeierstrassCurve Polynomial

theorem j_mul_Δ {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    W.j * W.Δ = W.c₄ ^ 3 := by
  rw [WeierstrassCurve.j, ← coe_Δ', mul_right_comm, Units.inv_mul, one_mul]

section Saturation

variable {K : Type*} [Field K]

def powSaturation (S : Subring K) (p : ℕ) : Subring K where
  carrier := {x | ∃ n : ℕ, (p : K) ^ n * x ∈ S}
  mul_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨m + n, by convert S.mul_mem hm hn using 1; ring⟩
  one_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    convert S.add_mem (S.mul_mem (S.pow_mem (natCast_mem S p) n) hm)
      (S.mul_mem (S.pow_mem (natCast_mem S p) m) hn) using 1
    ring
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro x ⟨m, hm⟩
    exact ⟨m, by convert S.neg_mem hm using 1; ring⟩

theorem mem_powSaturation {S : Subring K} {p : ℕ} {x y : K} (n : ℕ) (hy : y ∈ S)
    (h : (p : K) ^ n * x = y) : x ∈ powSaturation S p :=
  ⟨n, h ▸ hy⟩

theorem mem_of_mem_powSaturation {S : Subring K} {p q : ℕ} (hpq : p.Coprime q) {x : K}
    (hp : x ∈ powSaturation S p) (hq : x ∈ powSaturation S q) : x ∈ S := by
  obtain ⟨m, hm⟩ := hp
  obtain ⟨n, hn⟩ := hq
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr (hpq.pow m n)
  have h : (u : K) * p ^ m + v * q ^ n = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) huv
  convert S.add_mem (S.mul_mem (intCast_mem S u) hm) (S.mul_mem (intCast_mem S v) hn) using 1
  linear_combination -x * h

theorem coeff_mem_variableChange (S : Subring K) {W : WeierstrassCurve K} {r s t : K}
    (h₁ : W.a₁ ∈ S) (h₂ : W.a₂ ∈ S) (h₃ : W.a₃ ∈ S) (h₄ : W.a₄ ∈ S) (h₆ : W.a₆ ∈ S)
    (hr : r ∈ S) (hs : s ∈ S) (ht : t ∈ S) {W' : WeierstrassCurve K}
    (e : (⟨1, r, s, t⟩ : VariableChange K) • W = W') :
    W'.a₁ ∈ S ∧ W'.a₂ ∈ S ∧ W'.a₃ ∈ S ∧ W'.a₄ ∈ S ∧ W'.a₆ ∈ S := by
  subst e
  simp only [variableChange_def, inv_one, Units.val_one, one_pow, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> aesop

end Saturation

section Models

variable (A : Type*) [CommRing A] {K : Type*} [Field K] [Algebra A K] [IsIntegrallyClosedIn A K]

variable {A} in
theorem mem_range_of_quartic {x c₀ c₁ c₂ c₃ : K} (h₀ : c₀ ∈ (algebraMap A K).range)
    (h₁ : c₁ ∈ (algebraMap A K).range) (h₂ : c₂ ∈ (algebraMap A K).range)
    (h₃ : c₃ ∈ (algebraMap A K).range) (h : x ^ 4 + c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀ = 0) :
    x ∈ (algebraMap A K).range := by
  obtain ⟨c₀, rfl⟩ := h₀
  obtain ⟨c₁, rfl⟩ := h₁
  obtain ⟨c₂, rfl⟩ := h₂
  obtain ⟨c₃, rfl⟩ := h₃
  apply IsIntegrallyClosedIn.algebraMap_eq_of_integral
  refine ⟨X ^ 4 + C c₃ * X ^ 3 + C c₂ * X ^ 2 + C c₁ * X + C c₀, by monicity!, ?_⟩
  simpa [eval₂_add, eval₂_mul, eval₂_pow] using h

variable [CharZero K] {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
  {W : WeierstrassCurve K} [W.IsElliptic]

theorem exists_integral_model_of_forms (hj : W.j ∈ (algebraMap A K).range) (hΔ : W.Δ = 1)
    {C₂ C₃ : VariableChange K} (hu₂ : C₂.u = 1) (hu₃ : C₃.u = 1) {P Q a b : K}
    (e₂ : C₂ • W = splitCurve P Q) (e₃ : C₃ • W = deuringCurve a b) :
    ∃ (C : VariableChange K) (W₀ : WeierstrassCurve A), C • W = W₀.baseChange K ∧ W₀.Δ = 1 := by
  have hinj : Function.Injective (algebraMap A K) := IsIntegralClosure.algebraMap_injective A A K
  set S := (algebraMap A K).range with hS
  have hjΔ := j_mul_Δ W
  have hrel := W.c_relation
  rw [hΔ] at hjΔ hrel
  have hc₄ : W.c₄ ∈ S := mem_range_of_quartic (zero_mem _) (neg_mem hj) (zero_mem _) (zero_mem _)
    (by linear_combination -W.c₄ * hjΔ)
  have hc₆ : W.c₆ ∈ S := mem_range_of_quartic (zero_mem _) (zero_mem _)
    (sub_mem (ofNat_mem _ 1728) (pow_mem hc₄ 3)) (zero_mem _)
    (by linear_combination W.c₆ ^ 2 * hrel)
  have p₄ := variableChange_c₄ W C₂
  have pΔ := variableChange_Δ W C₂
  have q₄ := variableChange_c₄ W C₃
  have q₆ := variableChange_c₆ W C₃
  have qΔ := variableChange_Δ W C₃
  rw [e₂, hu₂] at p₄ pΔ
  rw [e₃, hu₃] at q₄ q₆ qΔ
  simp only [inv_one, Units.val_one, one_pow, one_mul, hΔ, splitCurve_Δ, splitCurve_c₄,
    deuringCurve_Δ, deuringCurve_c₄] at p₄ pΔ q₄ q₆ qΔ
  replace q₆ : -a ^ 6 + 36 * a ^ 3 * b - 216 * b ^ 2 = W.c₆ := by
    rw [← q₆]
    simp only [deuringCurve, c₆, b₂, b₄, b₆]
    ring
  have hN : 16 * (P * Q) ∈ S := mem_range_of_quartic (zero_mem _) (ofNat_mem _ 256) (zero_mem _)
    (neg_mem hc₄) (by rw [← p₄]; linear_combination -256 * 16 * (P * Q) * pΔ)
  have hM : 4 * (P + Q) ∈ S := mem_range_of_quartic (zero_mem _) (zero_mem _)
    (neg_mem (add_mem hc₄ (mul_mem (ofNat_mem _ 3) hN))) (zero_mem _) (by rw [← p₄]; ring)
  have ha₂ : a ^ 2 ∈ S := mem_range_of_quartic (mul_mem (neg_mem (ofNat_mem _ 3)) (pow_mem hc₄ 2))
    (mul_mem (neg_mem (ofNat_mem _ 8)) hc₆) (mul_mem (neg_mem (ofNat_mem _ 6)) hc₄) (zero_mem _)
    (by rw [← q₄, ← q₆]; ring)
  have ha : a ∈ S := mem_range_of_quartic (zero_mem _) (zero_mem _) (neg_mem ha₂) (zero_mem _)
    (by ring)
  have hb : 27 * b ∈ S := mem_range_of_quartic (ofNat_mem _ 19683) (zero_mem _) (zero_mem _)
    (neg_mem (pow_mem ha 3)) (by linear_combination -19683 * qΔ)
  obtain ⟨r, s, t, hD⟩ : ∃ r s t : K, C₃ * C₂⁻¹ = ⟨1, r, s, t⟩ :=
    ⟨_, _, _, VariableChange.ext (by simp [VariableChange.mul_def, VariableChange.inv_def, hu₂, hu₃])
      rfl rfl rfl⟩
  have eD : (⟨1, r, s, t⟩ : VariableChange K) • splitCurve P Q = deuringCurve a b := by
    rw [← hD, ← e₂, ← e₃, mul_smul, inv_smul_smul]
  have d₁ := congrArg WeierstrassCurve.a₁ eD
  have d₂ := congrArg WeierstrassCurve.a₂ eD
  have d₃ := congrArg WeierstrassCurve.a₃ eD
  simp only [variableChange_def, splitCurve, deuringCurve, inv_one, Units.val_one] at d₁ d₂ d₃
  have hr : 12 * r ∈ S := by
    convert add_mem ha₂ hM using 1
    linear_combination 4 * d₂ + (2 * s + a) * d₁
  have ht : 54 * (t - 4 * r * s) ∈ S := by
    convert sub_mem hb (mul_mem (ofNat_mem _ 9) (mul_mem hr ha)) using 1
    linear_combination 27 * d₃ - 108 * r * d₁
  set W' := (⟨1, -4 * r, 0, -28 * (t - 4 * r * s)⟩ : VariableChange K) • deuringCurve a b with hW'
  have e' : (⟨1, -3 * r, s, -27 * (t - 4 * r * s)⟩ : VariableChange K) • splitCurve P Q = W' := by
    rw [hW', ← eD, ← mul_smul]
    congr 1
    simp only [VariableChange.mul_def, Units.val_one, mul_one]
    ext <;> dsimp only <;> ring
  have m₃ := coeff_mem_variableChange (powSaturation S 3) (W := deuringCurve a b)
    (mem_powSaturation 0 ha (by simp [deuringCurve])) (zero_mem _)
    (mem_powSaturation 3 hb (by simp only [deuringCurve]; norm_num)) (zero_mem _) (zero_mem _)
    (mem_powSaturation 1 (neg_mem hr) (by push_cast; ring)) (zero_mem _)
    (mem_powSaturation 3 (mul_mem (neg_mem (ofNat_mem _ 14)) ht) (by push_cast; ring)) hW'.symm
  have m₂ := coeff_mem_variableChange (powSaturation S 2) (W := splitCurve P Q)
    (zero_mem _) (mem_powSaturation 2 (neg_mem hM) (by simp only [splitCurve]; push_cast; ring))
    (zero_mem _) (mem_powSaturation 4 hN (by simp only [splitCurve]; push_cast; ring)) (zero_mem _)
    (mem_powSaturation 2 (neg_mem hr) (by push_cast; ring))
    (mem_powSaturation 1 ha (by push_cast; linear_combination d₁))
    (mem_powSaturation 1 (neg_mem ht) (by push_cast; ring)) e'
  have hc : Nat.Coprime 2 3 := by norm_num
  obtain ⟨W₀, hW₀⟩ := (isIntegral_of_exists_lift A
    (mem_of_mem_powSaturation hc m₂.1 m₃.1) (mem_of_mem_powSaturation hc m₂.2.1 m₃.2.1)
    (mem_of_mem_powSaturation hc m₂.2.2.1 m₃.2.2.1)
    (mem_of_mem_powSaturation hc m₂.2.2.2.1 m₃.2.2.2.1)
    (mem_of_mem_powSaturation hc m₂.2.2.2.2 m₃.2.2.2.2)).integral
  refine ⟨⟨1, -4 * r, 0, -28 * (t - 4 * r * s)⟩ * C₃, W₀, by rw [mul_smul, e₃, ← hW₀], hinj ?_⟩
  rw [← map_Δ, ← WeierstrassCurve.baseChange, ← hW₀, hW', variableChange_Δ, deuringCurve_Δ, qΔ]
  simp

theorem exists_integral_model (hj : W.j ∈ (algebraMap A K).range)
    (h : HasRationalTorsion W L 12) :
    ∃ (C : VariableChange K) (W₀ : WeierstrassCurve A), C • W = W₀.baseChange K ∧ W₀.Δ = 1 := by
  obtain ⟨δ, hδ⟩ := h.exists_pow_twelve_eq_Δ
  have hΔ := W.isUnit_Δ.ne_zero
  have hδ0 : δ ≠ 0 := by rintro rfl; simp [← hδ] at hΔ
  set C₁ : VariableChange K := ⟨Units.mk0 δ hδ0, 0, 0, 0⟩ with hC₁
  have h' := h.variableChange C₁
  obtain ⟨C₂, P, Q, hu₂, e₂⟩ := (h'.of_dvd (by norm_num : 2 ∣ 12)).exists_splitCurve
  obtain ⟨C₃, a, b, -, hu₃, e₃, -⟩ := (h'.of_dvd (by norm_num : 3 ∣ 12)).exists_deuringCurve
  obtain ⟨C, W₀, e, h₀⟩ := exists_integral_model_of_forms A (W := C₁ • W)
    (by rwa [variableChange_j]) (by rw [variableChange_Δ, ← hδ]; simp [hC₁, hδ0]) hu₂ hu₃ e₂ e₃
  exact ⟨C * C₁, W₀, by rw [mul_smul, e], h₀⟩

end Models

end GlobalTheory
end
