module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle044
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle030
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle042
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle037
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle045
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle038
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section

namespace GlobalTheory.LamF

theorem exists_pat_of_polAV : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (act : OAct (𝓞 E) P.A), (∀ a, LamEq P.L (act.act a) (𝟙 P.A) P.L (𝟙 P.A) (act.act (H.bar a))) → ∃ (T : PAT H (Sp R)) (e : T.t.G ≅ P.A), T.g = P.g ∧ Serre.IsLinearHom T.t.act act e.hom ∧ LamEq P.L e.hom e.hom T.t.PP.L (𝟙 T.t.G) (𝟙 T.t.G) := by
  intro laws E _ _ _ H R _ _ P act hadj
  have : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨L', hL', ⟨rig, hrig⟩, hsym, hamp, hk, hlam, prim⟩ :=
    exists_normalised_polarisation laws R P (act.act H.w0) (act.act (H.bar H.w0)) (act.hom _) (act.hom _)
      (by rw [← act.add, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, act.one]) (hadj H.w0)
  let PP : RigLB P.A := ⟨L', rig, hL', hrig⟩
  let P' : Out.PolAV (Sp R) :=
    { A := P.A, isAb := P.isAb, g := P.g, smoothDim := P.smoothDim, L := L', isLB := hL', rigid := ⟨rig, hrig⟩,
      sym := hsym, ample := hamp, ktriv := hk }
  obtain ⟨cub⟩ := (laws.cube _ P' PP rfl).1
  have sym : PP.IsSymmetric :=
    GlobalTheory.PrimNorm.isSymmetric_of_hasGen PP (exists_gen_neg_of_sym laws.globalFns P.isAb hL' hsym)
  have lb : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ P.A)) {L : LB P.A.left}, L.IsLB → (cubeLB P.A x L).IsLB :=
    fun x L hL => DVR.linComb_isLB _ hL _ _
  have pts := ((GlobalTheory.LamCalc.lamEq_calculus _ P.A P.A P.A P.A P.A L' P.L P.L hL' P.isLB P.isLB
    (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)).2.1 hlam).2.2.2.2
  simp only [Category.comp_id] at pts
  have adj : ∀ a, LBIso (cubeLB P.A ![fst P.A P.A ≫ act.act a, snd P.A P.A] L')
      (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ act.act (H.bar a)] L') := fun a =>
    LBIso.trans (lb _ hL') (lb _ P.isLB) (lb _ hL') (pts _ _ _)
      (LBIso.trans (lb _ P.isLB) (lb _ P.isLB) (lb _ hL')
        (by simpa only [LamEq, Category.comp_id] using hadj a) (pts _ _ _).symm)
  exact ⟨{ t := { G := P.A, semi := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ P.isAb, act := act, PP := PP, cub := cub,
                  sym := sym, adj := adj, prim := prim },
           ab := P.isAb, g := P.g, dim := P.smoothDim, sym := hsym, ample := hamp, ktriv := hk },
    Iso.refl _, rfl, Serre.IsLinearHom.id act, LBIso.symm hlam⟩

end GlobalTheory.LamF
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def kFun {H : Host E} (D : Datum H) (ε : ℤˣ) (x y : D.La) : OK H :=
  (((ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y) : ℤ) : OK H) + (((ε : ℤ) * D.EF x y : ℤ) : OK H) * wK H

theorem kFun_coe {H : Host E} (D : Datum H) (ε : ℤˣ) (x y : D.La) : ((kFun D ε x y : OK H) : 𝓞 E) =
    (((ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y) : ℤ) : 𝓞 E) + (((ε : ℤ) * D.EF x y : ℤ) : 𝓞 E) * H.w0 := by
  simp only [kFun, wK, Subalgebra.coe_add, Subalgebra.coe_mul, SubringClass.coe_intCast]

theorem kform_w0_sq (H : Host E) : H.w0 * H.w0 = H.w0 - (((1 + H.d) / 4 : ℕ) : 𝓞 E) := by
  have h := congrArg (fun a : OK H => (a : 𝓞 E)) (GlobalTheory.T.integers_of_cm_field_conj_structure E H).2.2.2.1
  simp only [wK, Subalgebra.coe_add, SubmonoidClass.coe_pow, SubringClass.coe_natCast] at h
  linear_combination h

theorem kform_bar_w0 (H : Host E) : H.bar H.w0 = 1 - H.w0 := by
  obtain ⟨br, h1, h2, -⟩ := (GlobalTheory.T.integers_of_cm_field_conj_structure E H).2.2.1
  have h := congrArg (fun a : OK H => (a : 𝓞 E)) h2
  simp only [Subalgebra.coe_add, h1, Subalgebra.coe_one] at h
  simp only [wK] at h
  linear_combination h

theorem kform_skew {H : Host E} (D : Datum H) (x y : D.La) : D.EF y x = - D.EF x y := by
  have h := D.alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, D.alt] at h
  linarith

theorem kFun_add_left {H : Host E} (D : Datum H) (ε : ℤˣ) (x x' y : D.La) :
    kFun D ε (x + x') y = kFun D ε x y + kFun D ε x' y := by
  simp only [kFun, smul_add, map_add (f := _), LinearMap.add_apply]
  push_cast; ring

theorem kFun_add_right {H : Host E} (D : Datum H) (ε : ℤˣ) (x y y' : D.La) :
    kFun D ε x (y + y') = kFun D ε x y + kFun D ε x y' := by
  simp only [kFun, map_add (f := _)]
  push_cast; ring

theorem kFun_zsmul {H : Host E} (D : Datum H) (ε : ℤˣ) (m : ℤ) (x y : D.La) :
    kFun D ε (m • x) y = (m : OK H) * kFun D ε x y := by
  simp only [kFun, smul_comm H.w0 m x, map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  push_cast; ring

theorem kFun_w0 {H : Host E} (D : Datum H) (ε : ℤˣ) (x y : D.La) :
    kFun D ε (H.w0 • x) y = wK H * kFun D ε x y := by
  apply Subtype.ext
  have hw : H.w0 • H.w0 • x = H.w0 • x - (((1 + H.d) / 4 : ℕ) : ℤ) • x := by
    rw [smul_smul, kform_w0_sq, sub_smul, Nat.cast_smul_eq_nsmul, natCast_zsmul]
  have h2 := kform_w0_sq H
  rw [Subalgebra.coe_mul, kFun_coe, kFun_coe, hw]
  simp only [map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, wK]
  generalize ((1 + H.d) / 4 : ℕ) = N at *
  push_cast
  linear_combination (-((ε : ℤ) : 𝓞 E) * (D.EF x y : 𝓞 E)) * h2

theorem kFun_smul {H : Host E} (D : Datum H) (ε : ℤˣ) (a : OK H) (x y : D.La) :
    kFun D ε (a • x) y = a * kFun D ε x y := by
  obtain ⟨⟨m, n⟩, rfl, -⟩ := (GlobalTheory.T.integers_of_cm_field_conj_structure E H).2.1 a
  have : ((m : OK H) + (n : OK H) * wK H) • x = m • x + n • H.w0 • x := by
    rw [add_smul, mul_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]; rfl
  simp only
  rw [this, kFun_add_left, kFun_zsmul, kFun_zsmul, kFun_w0]; ring

def kLin {H : Host E} (D : Datum H) (ε : ℤˣ) : D.La →ₗ[OK H] D.La →+ OK H where
  toFun x := AddMonoidHom.mk' (kFun D ε x) (kFun_add_right D ε x)
  map_add' x x' := by ext1 y; exact kFun_add_left D ε x x' y
  map_smul' a x := by ext1 y; exact kFun_smul D ε a x y

theorem kLin_apply {H : Host E} (D : Datum H) (ε : ℤˣ) (x y : D.La) : kLin D ε x y = kFun D ε x y := rfl

theorem kform_coeff_unique (H : Host E) {a b c d : ℤ}
    (h : (a : OK H) + (b : OK H) * wK H = (c : OK H) + (d : OK H) * wK H) : a = c ∧ b = d := by
  have := ((GlobalTheory.T.integers_of_cm_field_conj_structure E H).2.1 ((a : OK H) + (b : OK H) * wK H)).unique (y₁ := (a, b)) (y₂ := (c, d)) rfl h
  exact Prod.mk.inj this

theorem kLin_perfect {H : Host E} (D : Datum H) (ε : ℤˣ) (f : D.La →ₗ[OK H] OK H) :
    ∃! y, ∀ x, f x = kLin D ε x y := by
  have hε : (ε : ℤ) * ε = 1 := by rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  choose c hc using fun a => ((GlobalTheory.T.integers_of_cm_field_conj_structure E H).2.1 a).exists
  let b : D.La →+ ℤ := AddMonoidHom.mk' (fun x => -(ε : ℤ) * (c (f x)).2) (by
    intro x x'
    have : (((c (f (x + x'))).1 : ℤ) : OK H) + ((c (f (x + x'))).2 : OK H) * wK H =
        (((c (f x)).1 + (c (f x')).1 : ℤ) : OK H) + (((c (f x)).2 + (c (f x')).2 : ℤ) : OK H) * wK H := by
      rw [← hc, map_add (f := _)]
      have h1 := hc (f x)
      have h2 := hc (f x')
      push_cast
      linear_combination h1 + h2
    rw [(kform_coeff_unique H this).2]; ring)
  obtain ⟨y, hy⟩ := D.unimod.2 b.toIntLinearMap
  have hb : ∀ x, (ε : ℤ) * D.EF x y = (c (f x)).2 := by
    intro x
    rw [kform_skew, hy]
    change (ε : ℤ) * -(-(ε : ℤ) * (c (f x)).2) = _
    linear_combination (c (f x)).2 * hε
  have hint : ∀ x, ∃ m : ℤ, f x - kFun D ε x y = m := by
    intro x
    refine ⟨(c (f x)).1 - (ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y), ?_⟩
    have h1 := hc (f x)
    rw [kFun, hb]
    push_cast
    linear_combination h1
  refine ⟨y, fun x => ?_, fun y' hy' => ?_⟩
  · obtain ⟨m, hm⟩ := hint x
    obtain ⟨m', hm'⟩ := hint (wK H • x)
    rw [map_smul, kFun_smul, smul_eq_mul, ← mul_sub, hm] at hm'
    have : ((0 : ℤ) : OK H) + (m : OK H) * wK H = (m' : OK H) + ((0 : ℤ) : OK H) * wK H := by
      push_cast; linear_combination hm'
    rw [(kform_coeff_unique H this).2] at hm
    rw [kLin_apply, ← sub_eq_zero, hm, Int.cast_zero]
  · apply D.unimod.1
    ext x
    have h1 := (hc (f x)).symm.trans (hy' x)
    have h2 := (kform_coeff_unique H h1).2
    rw [kform_skew D x y', kform_skew D x y]
    have h3 := hb x
    linear_combination (ε : ℤ) * (h2 + h3) + (D.EF x y' - D.EF x y) * hε

theorem exists_kForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ), ∃ h : D.La →ₗ[OK H] D.La →+ OK H, IsKForm D ε (fun x y => h x y) ∧ (∀ h' : D.La → D.La → OK H, IsKForm D ε h' → h' = fun x y => h x y) ∧ (∀ x y, ((h y x : OK H) : 𝓞 E) = H.bar (h x y : OK H)) ∧ (∀ (s : 𝓞 E) x y, h (s • x) y = h x (H.bar s • y)) ∧ (∀ x, ((h x x : OK H) : 𝓞 E) = (((ε : ℤ) * D.EF (H.w0 • x) x : ℤ) : 𝓞 E)) ∧ (∀ f : D.La →ₗ[OK H] OK H, ∃! y, ∀ x, f x = h x y) ∧ ∃ (n : ℕ) (x y : Fin n → D.La), ∀ a, a = ∑ i, h a (y i) • x i := by
  intro E _ _ _ H D ε
  refine ⟨kLin D ε, kFun_coe D ε, fun h' hh => ?_, fun x y => ?_, fun s x y => ?_, fun x => ?_,
    kLin_perfect D ε, ?_⟩
  · funext x y
    exact Subtype.ext ((hh x y).trans (kFun_coe D ε x y).symm)
  · have h1 : D.EF (H.w0 • y) x = D.EF (H.w0 • x) y - D.EF x y := by
      rw [D.adj, kform_bar_w0, sub_smul, one_smul, map_sub, kform_skew D x y, kform_skew D (H.w0 • x) y]
      ring
    rw [kLin_apply, kLin_apply, kFun_coe, kFun_coe, h1, kform_skew D x y, map_add (f := _), map_mul, map_intCast,
      map_intCast, kform_bar_w0]
    push_cast; ring
  · rw [kLin_apply, kLin_apply, kFun, kFun, smul_comm H.w0 s x, D.adj, D.adj s]
  · rw [kLin_apply, kFun_coe, D.alt]
    push_cast; ring
  · obtain ⟨h1, h2, -⟩ := (GlobalTheory.T.integers_of_cm_field_conj_structure E H).2.2.2.2.2 D.La D.fin D.proj
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' (OK H) D.La
    obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
    choose y hy using fun i : Fin n => (kLin_perfect D ε ((LinearMap.proj i).comp s)).exists
    refine ⟨n, fun i => π (Pi.single i 1), y, fun a => ?_⟩
    have ha : π (s a) = a := LinearMap.congr_fun hs a

    conv_lhs => rw [← ha, ← Finset.univ_sum_single (s a), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hy, ← map_smul, ← Pi.single_smul, smul_eq_mul, _root_.mul_one]
    rfl

end GlobalTheory.CM
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.NormHom

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A C : Over S} {A' C' : Over S'}
  [GrpObj A] [GrpObj C] [GrpObj A'] [GrpObj C'] {φ : A'.left ⟶ A.left} {ψ : C'.left ⟶ C.left}

theorem push_inj (h : IsGrpPullback A' A f φ) {T : Over S'} {x y : T ⟶ A'}
    (e : pushHom h T x = pushHom h T y) : x = y :=
  Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))

theorem push_comp (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback C' C f ψ) {p : A ⟶ C} {p' : A' ⟶ C'}
    (e : p'.left ≫ ψ = φ ≫ p.left) {T : Over S'} (x : T ⟶ A') :
    pushHom h' T (x ≫ p') = pushHom h T x ≫ p :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, e, Category.assoc])

theorem exists_monHom_lift (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback C' C f ψ) (p : A ⟶ C) [IsMonHom p] :
    ∃ p' : A' ⟶ C', IsMonHom p' ∧ p'.left ≫ ψ = φ ≫ p.left := by
  obtain ⟨p', e⟩ : ∃ p' : A' ⟶ C', p'.left ≫ ψ = φ ≫ p.left :=
    ⟨Over.homMk (h'.1.lift (φ ≫ p.left) A'.hom (by rw [Category.assoc, Over.w, h.1.w])) (h'.1.lift_snd _ _ _),
      h'.1.lift_fst _ _ _⟩
  refine ⟨p', ?_, e⟩
  have h1 : (1 : 𝟙_ (Over S') ⟶ A') ≫ p' = 1 := by
    apply push_inj h'
    rw [push_comp h h' e, map_one, map_one, MonObj.one_comp]
  have h2 : (fst A' A' * snd A' A') ≫ p' = (fst A' A' ≫ p') * (snd A' A' ≫ p') := by
    apply push_inj h'
    rw [push_comp h h' e, map_mul, map_mul, MonObj.mul_comp, push_comp h h' e, push_comp h h' e]
  constructor
  · simpa [Hom.one_def] using h1
  · rw [Hom.mul_def, Hom.mul_def] at h2
    have e1 : lift (fst A' A' ≫ p') (snd A' A' ≫ p') = p' ⊗ₘ p' := by ext <;> simp
    simpa [e1] using h2
end

theorem isVecOver_comp {R R' : Type} [CommRing R] [CommRing R'] {s : R →+* R'} {A C : Over (Sp R)}
    {A' C' : Over (Sp R')} {φ : A'.left ⟶ A.left} {ψ : C'.left ⟶ C.left} {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'}
    (hv : IsVecOver s φ v v') {p : A ⟶ C} {p' : A' ⟶ C'} (e : p'.left ≫ ψ = φ ≫ p.left) :
    IsVecOver s ψ (v ≫ p) (v' ≫ p') := by
  unfold IsVecOver at hv ⊢
  rw [Over.comp_left, Over.comp_left, Category.assoc, e, ← Category.assoc, hv, Category.assoc]

theorem lieNormSq_comp : ThetaUnifAV → Out.Laws → ∀ (R : Type) [CommRing R] (P P' : Out.PolAV (Sp R)) (f : P.A ⟶ P'.A) (g : P.A ⟶ P.A) (v : epsR R ⟶ P.A) (a : R) (s : R →+* ℂ) (r r' : ℝ), IsMonHom f → IsMonHom g → LamEq P'.L f f P.L g (𝟙 P.A) → IsTangent v → IsLieComb ![a] ![v] (v ≫ g) → IsLieNormSq P v s r → IsLieNormSq P' (v ≫ f) s r' → r' = (s a).re * r := by
  rintro hU hL R _ P P' f g v a s r r' hf hg hlam hv hc ⟨Q, φ, v₁, u, Hm, χ, w, hφ, hv₁, hA, hw, rfl⟩
    ⟨Q', φ', v₁', u', Hm', χ', w', hφ', hv₁', hA', hw', rfl⟩
  obtain ⟨f₁, hf₁, ef⟩ := exists_monHom_lift hφ.2.1 hφ'.2.1 f
  obtain ⟨g₁, hg₁, eg⟩ := exists_monHom_lift hφ.2.1 hφ.2.1 g
  obtain ⟨-, -, -, -, t₁, t₂, -⟩ := GlobalTheory.T.appellHumbert_unif_tangent_weilPairing hU Q Q.g u Hm χ hA
  obtain ⟨-, -, -, -, t₁', t₂', -⟩ := GlobalTheory.T.appellHumbert_unif_tangent_weilPairing hU Q' Q'.g u' Hm' χ' hA'
  obtain ⟨F, hF, -, hFd, -⟩ :=
    GlobalTheory.HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L Q.g Q'.g u u' t₁' t₂' f₁ hf₁
  obtain ⟨G, hG, -, hGd, -⟩ :=
    GlobalTheory.HomLinear.exists_linear_of_isMonHom Q.A Q.A Q.isAb Q.isAb Q.L Q.L Q.g Q.g u u t₁ t₂ g₁ hg₁
  have ht : IsTangent v₁ := hv₁.isTangent hφ.2.1 hv
  have hlam₁ : LamEq Q'.L f₁ f₁ Q.L g₁ (𝟙 Q.A) :=
    GlobalTheory.T.isCubeLBPairingIso_baseChange _ _ (spMap s) P.A P.A P'.A P.A Q.A Q.A Q'.A Q.A φ φ φ' φ hφ.2.1.1.w hφ.2.1.1.w hφ'.2.1 hφ.2.1
      P'.L P.L Q'.L Q.L P'.isLB P.isLB Q'.isLB Q.isLB hφ'.2.2 hφ.2.2 f f g (𝟙 _) f₁ f₁ g₁ (𝟙 _) ef ef eg
      (by simp) hlam
  have hweil := GlobalTheory.T.weil_pairing_eq_of_isomorphic_cube_pairings hL ℂ Q Q Q' Q f₁ f₁ g₁ (𝟙 _) hf₁ hf₁ hg₁ inferInstance hlam₁
  have hherm := (GlobalTheory.T.weilEq_iff_hermForm_eq_complex hU hL Q Q Q' Q u u u' u Hm' Hm χ' χ hA' hA f₁ f₁ g₁ (𝟙 _) F F G LinearMap.id
    hF hF hG (fun z => by simp)).1 hweil w w
  have e₁ : v₁' = v₁ ≫ f₁ :=
    (existsUnique_isVecOver hφ'.2.1.1 (v ≫ f)).unique hv₁' (isVecOver_comp hv₁ ef)
  subst e₁
  have e₂ : w' = F w := (t₁' _ (hFd w v₁ ht hw).1).unique hw' (hFd w v₁ ht hw).2
  have hc₁ := (GlobalTheory.lieComb_baseChange R ℂ s P.A Q.A φ hφ.2.1 1 ![v] (v ≫ g) ![a] ![v₁] (v₁ ≫ g₁)
    (fun j => by fin_cases j; exact hv₁) hc).1 (isVecOver_comp hv₁ eg)
  have hd := GlobalTheory.UnifDifferential.isDiff_of_isLieComb Q.A Q.L Q.g 1 u ![w] ![v₁] _ _
    (fun j => by fin_cases j; exact ht) (fun j => by fin_cases j; exact hw) hc₁
  have e₃ : G w = s a • w := by
    have := (t₁ _ (hGd w v₁ ht hw).1).unique (hGd w v₁ ht hw).2 hd
    simpa using this
  have him : (hermForm Hm w w).im = 0 := by
    rw [← Complex.conj_eq_iff_im]
    have hH : ∀ i j, (starRingEnd ℂ) (Hm i j) = Hm j i := fun i j => hA.1.apply j i

    simp only [hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, Pi.star_apply,
    RCLike.star_def, Complex.conj_conj, hH]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e₂, hherm, e₃, LinearMap.id_apply]
  have e₄ : hermForm Hm (s a • w) w = s a * hermForm Hm w w := by
    rw [hermForm, hermForm, smul_dotProduct, smul_eq_mul]
  rw [e₄, Complex.mul_re, him]
  ring

end GlobalTheory.NormHom
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.SerreDim

theorem finrank_tensor_of_algebra (O M k B L : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [CommRing B] [Algebra O B] [Algebra k B]
    [Module.Finite k B] [AddCommGroup L] [Module k L] [Module O L] [Module B L] [IsScalarTower k B L]
    [IsScalarTower O B L] [SMulCommClass O k L] [Module.Finite k L] :
    Module.finrank k (L ⊗[O] M) = Module.finrank O M * Module.finrank k L := by
  have : IsArtinianRing B := IsArtinianRing.of_finite k B
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq B (B ⊗[O] M) (Module.finrank O M) fun P => by
    letI : Field (B ⧸ P.asIdeal) := Ideal.Quotient.field _
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange O B (B ⧸ P.asIdeal) (B ⧸ P.asIdeal) M).finrank_eq]
    exact TenDim.finrank_fibre O M _
  let e : L ⊗[O] M ≃ₗ[B] (Fin (Module.finrank O M) → L) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange O B B L M).symm ≪≫ₗ
      (b.equivFun.lTensor L) ≪≫ₗ TensorProduct.piScalarRight B B L _
  rw [(e.restrictScalars k).finrank_eq, Module.finrank_pi_fintype]
  simp

theorem finrank_tensor (O M k L : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [AddCommGroup L] [Module k L] [Module O L]
    [SMulCommClass O k L] [Module.Finite k L] :
    Module.finrank k (L ⊗[O] M) = Module.finrank O M * Module.finrank k L := by
  have : SMulCommClass k O L := SMulCommClass.symm _ _ _
  letI : Module (k ⊗[ℤ] O) L := TensorProduct.Algebra.module
  letI : Algebra O (k ⊗[ℤ] O) := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower k (k ⊗[ℤ] O) L := IsScalarTower.of_algebraMap_smul fun r x => by
    change (r ⊗ₜ[ℤ] (1 : O)) • x = _
    rw [TensorProduct.Algebra.smul_def, one_smul]
  have : IsScalarTower O (k ⊗[ℤ] O) L := IsScalarTower.of_algebraMap_smul fun r x => by
    change ((1 : k) ⊗ₜ[ℤ] r) • x = _
    rw [TensorProduct.Algebra.smul_def, one_smul]
  exact finrank_tensor_of_algebra O M k (k ⊗[ℤ] O) L

theorem dim_eq_of_isPullback {X Y S T X' S' : Scheme.{0}} {f : X ⟶ S} {g : Y ⟶ T} {f' : X' ⟶ S'} {a : X' ⟶ X}
    {b : S' ⟶ S} {c : X' ⟶ Y} {d : S' ⟶ T} (h : IsPullback a f' f b) (h' : IsPullback c f' g d)
    {n m : ℕ} {W : X.Opens} {V : Y.Opens} (hW : SmoothOfRelativeDimension n (W.ι ≫ f))
    (hV : SmoothOfRelativeDimension m (V.ι ≫ g)) (x : X') (hx : a x ∈ W) (hx' : c x ∈ V) : n = m := by
  have h₁ : SmoothOfRelativeDimension n ((a ⁻¹ᵁ W).ι ≫ f') :=
    (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
      ((isPullback_morphismRestrict a W).paste_vert h) hW
  have h₂ : SmoothOfRelativeDimension m ((c ⁻¹ᵁ V).ι ≫ f') :=
    (smoothOfRelativeDimension_isStableUnderBaseChange m).of_isPullback
      ((isPullback_morphismRestrict c V).paste_vert h') hV
  have e₁ : SmoothOfRelativeDimension (0 + n) ((a ⁻¹ᵁ W ⊓ c ⁻¹ᵁ V).ι ≫ f') := by
    rw [← Scheme.homOfLE_ι _ (inf_le_left : a ⁻¹ᵁ W ⊓ c ⁻¹ᵁ V ≤ a ⁻¹ᵁ W), Category.assoc]; infer_instance
  have e₂ : SmoothOfRelativeDimension (0 + m) ((a ⁻¹ᵁ W ⊓ c ⁻¹ᵁ V).ι ≫ f') := by
    rw [← Scheme.homOfLE_ι _ (inf_le_right : a ⁻¹ᵁ W ⊓ c ⁻¹ᵁ V ≤ c ⁻¹ᵁ V), Category.assoc]; infer_instance
  simpa using H1.dim_unique _ e₁ e₂ ⟨x, hx, hx'⟩

theorem isPullback_mul {S : Scheme.{0}} (G : Over S) [GrpObj G] :
    IsPullback (fst G G * snd G G).left (snd G G).left G.hom G.hom := by
  let e : G ⊗ G ≅ G ⊗ G :=
    { hom := lift (fst G G * snd G G) (snd G G)
      inv := lift (fst G G * (snd G G)⁻¹) (snd G G)
      hom_inv_id := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_mul, GrpObj.comp_inv]
      inv_hom_id := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_mul, GrpObj.comp_inv] }
  have h : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  refine h.of_iso ((Over.forget S).mapIso e.symm) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · change (fst G G ≫ 𝟙 _).left = (e.inv ≫ (fst G G * snd G G)).left
    congr 1
    simp [e, MonObj.comp_mul]
  · change (snd G G ≫ 𝟙 _).left = (e.inv ≫ snd G G).left
    congr 1
    simp [e]

theorem exists_dim_of_grpObj {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] [Smooth G.hom] :
    ∃ n, SmoothOfRelativeDimension n G.hom := by
  choose n W hW hd using H1.exists_dim G.hom
  let x₀ : G.left := η[G].left (default : PrimeSpectrum k)
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (n x₀)) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine ⟨n x₀, IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (n x₀)) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_⟩
  let p : G ⟶ G ⊗ G := lift 1 (𝟙 G)
  have p₁ : p ≫ fst G G = toUnit G ≫ η[G] := lift_fst _ _
  have p₂ : p ≫ (fst G G * snd G G) = 𝟙 G := by simp [p, MonObj.comp_mul]
  have q₁ : (fst G G).left (p.left y) = x₀ :=
    (congrArg (fun q : G ⟶ G => q.left y) p₁).trans
      (congrArg η[G].left (Subsingleton.elim (α := PrimeSpectrum k) _ _))
  have q₂ : (fst G G * snd G G).left (p.left y) = y := congrArg (fun q : G ⟶ G => q.left y) p₂
  have h : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  rw [dim_eq_of_isPullback h (isPullback_mul G) (hd x₀) (hd y) (p.left y) (q₁ ▸ hW x₀) (by rw [q₂]; exact hW y)]
  exact hd y

theorem dim_eq_field {k O M : Type} [Field k] [CommRing O] [IsDomain O] [Module.Finite ℤ O] [AddCommGroup M]
    [Module O M] [Module.Finite O M] [Module.Projective O M] {G A : Over (Sp k)} [GrpObj G] [IsCommMonObj G]
    [GrpObj A] [IsCommMonObj A] {a : OAct O G} {b : OAct O A} (t : Serre.IsTensor A b G a M) {g : ℕ}
    (hG : SmoothOfRelativeDimension g G.hom) {n : ℕ} (hA : SmoothOfRelativeDimension n A.hom) :
    n = Module.finrank O M * g := by
  obtain ⟨v, hv⟩ := TenDim.exists_isLieBasis G hG
  obtain ⟨w, hw⟩ := TenDim.exists_isLieBasis A hA
  have := Module.Finite.of_basis (Serre.Lie.basis a hv)
  have h := finrank_tensor O M k (Serre.Lie a)
  rwa [(t.lieEquivBase b).finrank_eq, Module.finrank_eq_card_basis (Serre.Lie.basis b hw),
    Module.finrank_eq_card_basis (Serre.Lie.basis a hv), Fintype.card_fin, Fintype.card_fin] at h

theorem smoothOfRelativeDimension_tensor :
    ∀ (S : Scheme.{0}) (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Projective O M] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (g : ℕ), Nonempty (Serre.IsTensor A b G a M) → SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension (Module.finrank O M * g) A.hom := by
  rintro S O _ _ _ M _ _ _ _ G A _ _ _ _ a b g ⟨t⟩ hG
  have : Smooth G.hom := hG.smooth
  have : Smooth A.hom := t.smooth
  choose n W hW hd using H1.exists_dim A.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (Module.finrank O M * g)) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (Module.finrank O M * g)) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let k := A.left.residueField y
  let z : Sp k ⟶ A.left := A.left.fromSpecResidueField y
  have hz : ∀ u, z u = y := fun u => Scheme.fromSpecResidueField_apply y _
  let x : Sp k ⟶ S := z ≫ A.hom
  let z' : Sp k ⟶ pullback A.hom x := pullback.lift z (𝟙 _) (Category.id_comp _).symm
  have : Smooth ((Over.pullback x).obj A).hom := inferInstanceAs (Smooth (pullback.snd A.hom x))
  obtain ⟨m, hm⟩ := exists_dim_of_grpObj ((Over.pullback x).obj A)
  have e₁ : n y = m := H1.dim_base (IsPullback.of_hasPullback A.hom x) (hd y) hm (z' (default : PrimeSpectrum k)) (by
    have e : z' ≫ pullback.fst A.hom x = z := pullback.lift_fst _ _ _
    have e' := (congrArg (fun q : Sp k ⟶ A.left => q (default : PrimeSpectrum k)) e).trans (hz _)
    exact (congrArg (fun u => u ∈ W y) e').mpr (hW y))
  have hG' : SmoothOfRelativeDimension g (pullback.snd G.hom x) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hG
  rw [← dim_eq_field (t.pullback x) hG' hm, ← e₁]
  exact hd y

end GlobalTheory.SerreDim
end
