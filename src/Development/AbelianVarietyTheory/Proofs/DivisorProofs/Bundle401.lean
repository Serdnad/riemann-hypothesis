module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.GlRes
public import GroundTheory.AutomorphicForms.GKModules.RightRegular
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle343
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle346
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle004

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.AwayCont

variable {A : Type} [CommRing A] (M : Submonoid A)

structure Idx (M : Submonoid A) where

  val : A
  mem : val ∈ M

instance : Preorder (Idx M) where
  le a b := ∃ t ∈ M, b.val = a.val * t
  le_refl a := ⟨1, M.one_mem, by simp⟩
  le_trans a b c := by
    rintro ⟨t, ht, h1⟩ ⟨s, hs, h2⟩
    exact ⟨t * s, M.mul_mem ht hs, by rw [h2, h1, mul_assoc]⟩

instance : IsDirected (Idx M) (· ≤ ·) where
  directed a b := ⟨⟨a.val * b.val, M.mul_mem a.mem b.mem⟩, ⟨b.val, b.mem, rfl⟩, ⟨a.val, a.mem, mul_comm _ _⟩⟩

instance : Nonempty (Idx M) := ⟨⟨1, M.one_mem⟩⟩

theorem isUnit_of_le {a b : Idx M} (h : a ≤ b) :
    IsUnit (algebraMap A (Localization.Away b.val) a.val) := by
  obtain ⟨t, -, ht⟩ := h
  have hb := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away b.val) b.val
  rw [show algebraMap A (Localization.Away b.val) b.val =
      algebraMap A _ a.val * algebraMap A _ t by rw [← map_mul, ← ht]] at hb
  exact isUnit_of_mul_isUnit_left hb

def trans {a b : Idx M} (h : a ≤ b) : Localization.Away a.val →+* Localization.Away b.val :=
  IsLocalization.Away.lift a.val (isUnit_of_le M h)

theorem trans_comp {a b : Idx M} (h : a ≤ b) :
    (trans M h).comp (algebraMap A _) = algebraMap A _ :=
  IsLocalization.Away.lift_comp _ _

theorem ext_away {a : A} {P : Type} [CommRing P] {f g : Localization.Away a →+* P}
    (hf : f.comp (algebraMap A _) = g.comp (algebraMap A _)) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers a) hf

def diag : Idx M ⥤ CommRingCat.{0} where
  obj a := CommRingCat.of (Localization.Away a.val)
  map {a b} h := CommRingCat.ofHom (trans M h.le)
  map_id a := by
    ext1; apply ext_away
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_id]
    rw [trans_comp]; rfl
  map_comp {a b c} f g := by
    ext1; apply ext_away
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp]
    rw [RingHom.comp_assoc, trans_comp, trans_comp, trans_comp]

def toLoc (a : Idx M) : Localization.Away a.val →+* Localization M :=
  IsLocalization.Away.lift a.val (IsLocalization.map_units (Localization M) (⟨a.val, a.mem⟩ : M))

theorem toLoc_comp (a : Idx M) : (toLoc M a).comp (algebraMap A _) = algebraMap A _ :=
  IsLocalization.Away.lift_comp _ _

def cocone : Cocone (diag M) where
  pt := CommRingCat.of (Localization M)
  ι := { app := fun a => CommRingCat.ofHom (toLoc M a)
         naturality := fun a b h => by
           ext1; apply ext_away
           simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp, diag, Functor.const_obj_map,
             CommRingCat.hom_id, RingHom.id_comp]
           rw [RingHom.comp_assoc, trans_comp, toLoc_comp]
           exact (toLoc_comp M a).symm }

end GlobalTheory.EtC.AwayCont
end

noncomputable section

namespace GlobalTheory.EtC.AwayCont

variable {A : Type} [CommRing A] (M : Submonoid A)

theorem toLoc_trans {a b : Idx M} (h : a ≤ b) : (toLoc M b).comp (trans M h) = toLoc M a :=
  ext_away (by rw [RingHom.comp_assoc, trans_comp, toLoc_comp, toLoc_comp])

theorem trans_trans {a b c : Idx M} (h : a ≤ b) (h' : b ≤ c) :
    (trans M h').comp (trans M h) = trans M (h.trans h') :=
  ext_away (by rw [RingHom.comp_assoc, trans_comp, trans_comp, trans_comp])

theorem kill (a : Idx M) (z : Localization.Away a.val) (hz : toLoc M a z = 0) :
    ∃ (b : Idx M) (h : a ≤ b), trans M h z = 0 := by
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers a.val) z
  have h1 : algebraMap A (Localization M) x = 0 := by
    have := congrArg (toLoc M a) hs
    rw [map_mul, hz, zero_mul, ← RingHom.comp_apply, toLoc_comp] at this
    exact this.symm
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff M (Localization M) x).mp h1
  let b : Idx M := ⟨a.val * c, M.mul_mem a.mem c.2⟩
  have hab : a ≤ b := ⟨c, c.2, rfl⟩
  refine ⟨b, hab, ?_⟩
  have hu := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away b.val) b.val
  have hb : b.val = a.val * c := rfl
  rw [hb, map_mul] at hu
  have hua : IsUnit (algebraMap A (Localization.Away b.val) a.val) := isUnit_of_mul_isUnit_left hu
  have huc : IsUnit (algebraMap A (Localization.Away b.val) c) := isUnit_of_mul_isUnit_right hu
  have hx : algebraMap A (Localization.Away b.val) x = 0 := by
    have : algebraMap A (Localization.Away b.val) c * algebraMap A (Localization.Away b.val) x = 0 := by
      rw [← map_mul, hc, map_zero]
    exact (huc.mul_right_eq_zero).mp this
  have hs' := congrArg (trans M hab) hs
  rw [map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply, trans_comp, hx] at hs'
  obtain ⟨k, hk⟩ := s.2
  have hus : IsUnit (algebraMap A (Localization.Away b.val) (s : A)) := by
    rw [← hk, map_pow]; exact hua.pow k
  exact (hus.mul_left_eq_zero).mp hs'

def isColimit : IsColimit (cocone M) := by
  haveI : ReflectsColimitsOfShape (Idx M) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (cocone M)) ?_ ?_)
  · intro (x : Localization M)
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    refine ⟨⟨s.1, s.2⟩, IsLocalization.mk' (Localization.Away s.1) a
      (⟨s.1, Submonoid.mem_powers _⟩ : Submonoid.powers s.1), ?_⟩
    show _ = toLoc M ⟨s.1, s.2⟩ _
    rw [eq_comm, IsLocalization.eq_mk'_iff_mul_eq]
    have e1 := RingHom.congr_fun (toLoc_comp M ⟨s.1, s.2⟩) s.1
    have e2 := RingHom.congr_fun (toLoc_comp M ⟨s.1, s.2⟩) a
    simp only [RingHom.comp_apply] at e1 e2
    rw [← e1, ← map_mul, IsLocalization.mk'_spec, e2]
  · intro i j (xi : Localization.Away i.val) (xj : Localization.Away j.val) h
    change toLoc M i xi = toLoc M j xj at h
    let k : Idx M := ⟨i.val * j.val, M.mul_mem i.mem j.mem⟩
    have hik : i ≤ k := ⟨j.val, j.mem, rfl⟩
    have hjk : j ≤ k := ⟨i.val, i.mem, mul_comm _ _⟩
    have hz : toLoc M k (trans M hik xi - trans M hjk xj) = 0 := by
      have e1 := RingHom.congr_fun (toLoc_trans M hik) xi
      have e2 := RingHom.congr_fun (toLoc_trans M hjk) xj
      simp only [RingHom.comp_apply] at e1 e2
      rw [map_sub, e1, e2, h, sub_self]
    obtain ⟨b, hkb, hb⟩ := kill M k _ hz
    refine ⟨b, homOfLE (hik.trans hkb), homOfLE (hjk.trans hkb), ?_⟩
    show trans M (hik.trans hkb) xi = trans M (hjk.trans hkb) xj
    rw [← trans_trans M hik hkb, ← trans_trans M hjk hkb, RingHom.comp_apply, RingHom.comp_apply,
      ← sub_eq_zero, ← map_sub]
    exact hb

end GlobalTheory.EtC.AwayCont
end

namespace GlobalTheory.EtC.AwayCont

theorem kill_of_loc : B1 → ∀ (q : ℕ) (A : Type) [CommRing A] (M : Submonoid A) (n i : ℤ), IsUnit (q : A) →
    ∀ m ∈ M, ∀ y : Ht q (sp (Localization.Away m)) n i, ∀ φ : Localization.Away m →+* Localization M,
    φ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap φ) _ _ y = 0 →
    ∃ m' ∈ M, ∀ ψ : Localization.Away m →+* Localization.Away (m * m'),
      ψ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap ψ) _ _ y = 0 := by
  intro hB q A _ M n i hq m hm y φ hφ hy
  let a : Idx M := ⟨m, hm⟩
  have hq' : IsUnit ((q : ℕ) : (diag M).obj a) := by
    have h0 : IsUnit ((q : ℕ) : Localization.Away m) := by
      simpa using hq.map (algebraMap A (Localization.Away m))
    exact h0
  have hφ' : ((cocone M).ι.app a).hom = φ := by
    show toLoc M a = φ
    exact ext_away (by rw [hφ]; exact toLoc_comp M a)
  have hy' : pull _ (spMap ((cocone M).ι.app a).hom) _ _ y = 0 := by
    rw [hφ']; exact hy
  obtain ⟨⟨k1, hk1⟩, f, hk⟩ := (hB q (diag M) (cocone M) (isColimit M) n i).2 a y hq' hy'
  obtain ⟨t, ht, hkt⟩ := f.le
  change k1 = m * t at hkt
  subst hkt
  refine ⟨t, ht, fun ψ hψ => ?_⟩
  have hψ' : ((diag M).map f).hom = ψ := by
    show trans M f.le = ψ
    exact ext_away (by rw [hψ]; exact trans_comp M f.le)
  rw [← hψ']
  exact hk

end GlobalTheory.EtC.AwayCont
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.quasiIso_chains_cechNerve_of_surjective : ∀ (R : Type) [CommRing R] {P Q : PSh} (φ : P ⟶ Q), (∀ U, Function.Surjective (φ.app U)) → QuasiIso ((chains R).map (show (Arrow.mk φ).cechNerve ⟶ disc.obj Q from (Arrow.mk φ).augmentedCechNerve.hom)) := by
  first | (exact @GlobalTheory.EtC.chains_cechNerve_quasiIso_of_surjective) | (exact GlobalTheory.EtC.chains_cechNerve_quasiIso_of_surjective) | (intros; apply GlobalTheory.EtC.chains_cechNerve_quasiIso_of_surjective  <;> assumption)
end

section

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic NormedSpace
open scoped ContDiff

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace GlobalTheory.HCA

theorem glRes_smooth_rightDeriv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    ∀ φ : Sm E a, ∀ x, (glH E a).IsSmoothFun (glRes φ.1 x) ∧
      ∀ X : glL E a, (glH E a).rightDeriv X (glRes φ.1 x) = glRes (lie E a (toL X.1) φ).1 x := by
  intro E _ _ _ a φ x
  let T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  have hT : ∀ M, T M = toL M := fun _ => rfl
  have key : ∀ (g : glG E a) (Y : glL E a), glRes φ.1 x (g * (glH E a).expG Y) =
      chart φ.1 x (T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * exp (Y : Matrix (Fin a) (Fin a) (Cinf E)))) := by
    intro g Y
    rw [hT]
    exact (chart_val φ.1 x ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) * ((glH E a).expG Y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ))).symm
  have hs : (glH E a).IsSmoothFun (glRes φ.1 x) := by
    rw [IsExpLieAlgebra.isSmoothFun_iff]
    intro g
    have e : (fun Y : glL E a => glRes φ.1 x (g * (glH E a).expG Y)) =
        chart φ.1 x ∘ fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * exp (Y : Matrix (Fin a) (Fin a) (Cinf E))) :=
      funext (key g)
    rw [e]
    have h1 : ContDiff ℝ ∞ (fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * exp (Y : Matrix (Fin a) (Fin a) (Cinf E)))) :=
      T.contDiff.comp (contDiff_const.mul ((contDiff_exp ℝ _).comp (glL E a).subtypeL.contDiff))
    exact (φ.2 x).comp_contDiff h1 fun Y =>
      ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) * ((glH E a).expG Y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ)).isUnit
  refine ⟨hs, fun X => funext fun g => ?_⟩
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (X : Matrix (Fin a) (Fin a) (Cinf E)) (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  have hc : HasDerivAt (fun t : ℝ => toL (((glH E a).expG (t • X) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) : Matrix (Fin a) (Fin a) (Cinf E)))
      (toL X.1) 0 := T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have h0 : (((glH E a).expG ((0 : ℝ) • X) : glG E a) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) = 1 := by
    ext : 1
    simp
  have h3 := hasDerivAt_curve φ (x * infGL E a (g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ))
    (fun t => ((glH E a).expG (t • X) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ)) (toL X.1) h0 hc
  have ef : (fun t : ℝ => glRes φ.1 x (g * (glH E a).expG (t • X))) = fun t : ℝ =>
      φ.1 (x * infGL E a (g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) *
        infGL E a ((glH E a).expG (t • X) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ)) := by
    funext t
    simp only [glRes, Subgroup.coe_mul, map_mul, mul_assoc]
  have h4 := (glH E a).hasDerivAt_rightDeriv hs X g
  rw [ef] at h4
  exact h4.unique h3

end GlobalTheory.HCA

end
end

section

open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.HeisUnit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


variable (k) in
def intInd (n d : ℕ) : Matrix (Fin n) (Fin d) k → ℂ := Set.indicator {Y | ∀ i j, Y i j ∈ 𝒪[k]} 1

def diagAt {n : ℕ} (x : kˣ) (i0 : Fin n) : GL (Fin n) k := SplitFlip.diagGL fun i => if i = i0 then x else 1

def cosetRep {n d : ℕ} (ϖ : kˣ) (i0 : Fin n) (T : Fin d → SplitFlip.Res (k := k) 1) : Matrix (Fin n) (Fin d) k :=
  Matrix.of fun i j => if i = i0 then -((ϖ : k)⁻¹ * ((Quotient.out (T j) : 𝒪[k]) : k)) else 0

theorem intInd_mem_SB (n d : ℕ) : intInd k n d ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : IsCompact {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := SplitFlip.isCompact_intMatrix
  have ho : IsOpen {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := SplitFlip.isOpen_intMatrix
  have hW : IsClopen {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := ⟨hc.isClosed, ho⟩
  refine ⟨?_, HasCompactSupport.intro' hc hW.isClosed fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]}
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp only [Set.mem_setOf_eq] at hx
    simp [intInd, Set.indicator_apply, hy, hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hx hy
    simp [intInd, Set.indicator_apply, hy, hx]

theorem intInd_zero (n d : ℕ) : intInd k n d 0 = 1 :=
  Set.indicator_of_mem (show (0 : Matrix (Fin n) (Fin d) k) ∈ {Y | ∀ i j, Y i j ∈ 𝒪[k]} from
    fun _ _ => zero_mem _) _

theorem det_diagAt {n : ℕ} (x : kˣ) (i0 : Fin n) : Matrix.GeneralLinearGroup.det (diagAt x i0) = x := by
  rw [diagAt, SplitFlip.det_diagGL, Fintype.prod_eq_single i0 (fun i hi => if_neg hi), if_pos rfl]

theorem diagAt_val {n : ℕ} (x : kˣ) (i0 : Fin n) :
    (diagAt x i0).val = Matrix.diagonal fun i => if i = i0 then (x : k) else 1 := by
  rw [diagAt, SplitFlip.diagGL_val]
  congr 1; funext i; split_ifs <;> simp

end GlobalTheory.HeisUnit
end
end

section

noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.WeilM

namespace GlobalTheory.RankFibre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


variable (k) in
def fullRankSB (a d : ℕ) : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ) where
  carrier := {Ψ | Ψ ∈ SB (Matrix (Fin a) (Fin d) k) ∧ ∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0}
  zero_mem' := ⟨(SB _).zero_mem, fun _ _ => rfl⟩
  add_mem' := fun hΦ hΨ => ⟨(SB _).add_mem hΦ.1 hΨ.1, fun Y hY => by simp [hΦ.2 Y hY, hΨ.2 Y hY]⟩
  smul_mem' := fun c Φ hΦ => ⟨(SB _).smul_mem c hΦ.1, fun Y hY => by simp [hΦ.2 Y hY]⟩

def coinv (ν β : kˣ →* ℂˣ) (a d : ℕ) : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ) :=
  Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
    Ψ ∈ SB (Matrix (Fin a) (Fin d) k) ∧ z = omA ν β g 1 Ψ - Ψ}

abbrev blocks (a b : ℕ) : (Σ x, Two (Fin a) (Fin b) x) ≃ Fin (a + b) := two (stdSum (rfl : a + b = a + b))

def parChar (ν β : kˣ →* ℂˣ) (a b : ℕ) : parab k (blocks a b) →* ℂˣ :=
  (deltaHalf k (Two (Fin a) (Fin b)) * ((detChar (Fin a) (ν * β)).comp (MonoidHom.fst _ _)).comp
      (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom *
    ((detChar (Fin b) β).comp (MonoidHom.snd _ _)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom).comp
    (leviProj k (blocks a b))

def indScal (ν β : kˣ →* ℂˣ) (a b : ℕ) : Submodule ℂ (GL (Fin (a + b)) k → ℂ) :=
  smoothPart (rightReg ℂ (GL (Fin (a + b)) k) ℂ) ⊓ indSpace (parab k (blocks a b)) (ofChar (parChar ν β a b))

variable [MeasurableSpace k] [BorelSpace k]

def fibre (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ) (x : GL (Fin (a + b)) k) : ℂ :=
  ∫ g : GL (Fin a) k, omA ν β 1 x Φ (g.val * X0 (k := k) finSumFinEquiv) * (ν (gdet g) : ℂ) *
    apow (gdet g) (((a + b : ℕ) : ℂ) / 2) ∂(haarVol (GlobalTheory.SplitWeil.KO k (Fin a)))

theorem fibre_omA (ν β : kˣ →* ℂˣ) (a b : ℕ) (h : GL (Fin (a + b)) k) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ)
    (x : GL (Fin (a + b)) k) : fibre ν β a b (omA ν β 1 h Φ) x = fibre ν β a b Φ (x * h) := by
  unfold fibre
  congr 1
  funext g
  rw [← omA_mul, one_mul]

end GlobalTheory.RankFibre
end
end

section

open ValuativeRel Matrix

theorem _root_.GlobalTheory.T.schwartzBruhat_vector_irreducible_translations_characters : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    {κ : Type} [Fintype κ] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    (∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (x * y) = 1) ↔ x ∈ 𝒪[k]) →
    ∀ W : Submodule ℂ ((κ → k) → ℂ), W ≤ GlobalTheory.WeilM.SB (κ → k) →
    (∀ φ ∈ W, ∀ v : κ → k, (fun x => φ (x + v)) ∈ W) →
    (∀ φ ∈ W, ∀ y : κ → k, (fun x => ψ0 (x ⬝ᵥ y) * φ x) ∈ W) →
    ∀ φ₀ ∈ W, φ₀ ≠ 0 → W = GlobalTheory.WeilM.SB (κ → k) := by
  first | exact @GlobalTheory.IrredSBVec.sb_irreducible_vec | exact GlobalTheory.IrredSBVec.sb_irreducible_vec | (intros; apply GlobalTheory.IrredSBVec.sb_irreducible_vec <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.totally_disconnected_product_locally_compact : ∀ {P Q P' Q' Z Z' : Type} [TopologicalSpace P] [T2Space P] [LocallyCompactSpace P]
    [TotallyDisconnectedSpace P] [TopologicalSpace Q] [T2Space Q] [LocallyCompactSpace Q] [TotallyDisconnectedSpace Q]
    [TopologicalSpace P'] [T2Space P'] [LocallyCompactSpace P'] [TotallyDisconnectedSpace P']
    [TopologicalSpace Q'] [T2Space Q'] [LocallyCompactSpace Q'] [TotallyDisconnectedSpace Q']
    [TopologicalSpace Z] [TopologicalSpace Z'] (eZ : Z ≃ₜ P × Q) (eZ' : Z' ≃ₜ P' × Q')
    (f : (P → ℂ) →ₗ[ℂ] (P' → ℂ)) (g : (Q → ℂ) →ₗ[ℂ] (Q' → ℂ)),
    Set.BijOn f (GlobalTheory.WeilM.SB P : Set (P → ℂ)) (GlobalTheory.WeilM.SB P' : Set (P' → ℂ)) →
    Set.BijOn g (GlobalTheory.WeilM.SB Q : Set (Q → ℂ)) (GlobalTheory.WeilM.SB Q' : Set (Q' → ℂ)) →
    ∃ h : (Z → ℂ) →ₗ[ℂ] (Z' → ℂ), Set.BijOn h (GlobalTheory.WeilM.SB Z : Set (Z → ℂ)) (GlobalTheory.WeilM.SB Z' : Set (Z' → ℂ)) ∧
      ∀ a ∈ GlobalTheory.WeilM.SB P, ∀ b ∈ GlobalTheory.WeilM.SB Q,
        h (fun z => a (eZ z).1 * b (eZ z).2) = fun z' => f a (eZ' z').1 * g b (eZ' z').2 := by
  first | exact @GlobalTheory.SBProdExt.exists_linear_bijOn_prod | exact GlobalTheory.SBProdExt.exists_linear_bijOn_prod | (intros; apply GlobalTheory.SBProdExt.exists_linear_bijOn_prod <;> assumption)
end

section

open MvPolynomial GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra

set_option autoImplicit false

namespace GlobalTheory.ChowSection

theorem totalDegree_of_isChowFormInt {k : Type} [Field k] {N e d : ℕ}
    {Q : Ideal (MvPolynomial (Fin N) k)} {g : MvPolynomial (Fin (e + 1) × Fin N) k}
    (h : IsChowFormInt Q e d g) : g.totalDegree = (e + 1) * d := by
  rw [((isMultiHomogeneous_iff_block.1 h.homog).isHomogeneous).totalDegree h.ne_zero]
  simp

end GlobalTheory.ChowSection
end

section

open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

theorem _root_.GlobalTheory.T.connectionMatrix_gramOperatorNorm_le : ∀ (g a : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (Bs : Fin a → Matrix (Fin g) (Fin g) ℝ) (Dm : Matrix (Fin g) (Fin g) ℂ) (s : Fin a → ℂ) (t : Fin a → ℝ) (c K W : ℝ), 0 < c → 0 ≤ K → 0 ≤ W → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ i, 0 < t i) → (∀ i x, ‖(t i • (Y⁻¹ * Bs i)) *ᵥ x‖ ≤ W * ‖x‖) → (∀ j k, ‖Dm j k‖ ≤ K) → opNorm 1 1 ((Y.map Complex.ofReal)⁻¹ * ((1 / (2 * Complex.I)) • (Dm + ∑ i, s i • (Bs i).map Complex.ofReal))) ≤ g * (g * K / c + W * ∑ i, ‖s i‖ / t i) := by
  first | exact @GlobalTheory.connMatrix_opNorm_le | exact GlobalTheory.connMatrix_opNorm_le | (intros; apply GlobalTheory.connMatrix_opNorm_le <;> assumption)
end

section

open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

theorem _root_.GlobalTheory.T.hodgeCurvature_dual_metric_pointwise_bound : ∀ (g a : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (Bs : Fin a → Matrix (Fin g) (Fin g) ℝ) (Dm : Matrix (Fin g) (Fin g) ℂ) (s : Fin a → ℂ) (t : Fin a → ℝ) (c K : ℝ), 0 < c → 0 ≤ K → Y.IsSymm → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ i, (Bs i).PosSemidef) → (∀ i, 0 < t i) → (∀ i x, t i * (x ⬝ᵥ Bs i *ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ j k, ‖Dm j k‖ ≤ K) → (Y.map Complex.ofReal).PosDef ∧ ∀ v, ‖form (Y.map Complex.ofReal)⁻¹ ((Dm + ∑ i, s i • (Bs i).map Complex.ofReal) *ᵥ v) ((Dm + ∑ i, s i • (Bs i).map Complex.ofReal) *ᵥ v)‖ ≤ (g * K / c + ∑ i, ‖s i‖ / t i) ^ 2 * gnorm (Y.map Complex.ofReal) v ^ 2 := by
  first | exact @GlobalTheory.HodgeCurvPoint.dual_bound | exact GlobalTheory.HodgeCurvPoint.dual_bound | (intros; apply GlobalTheory.HodgeCurvPoint.dual_bound <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cyclotomicPrimitiveRoots_filtered_colimit : ∀ (q : ℕ) (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → (∀ ζ : Prim q c.pt, ∃ (j : J) (ξ : Prim q (D.obj j)), Prim.map (c.ι.app j).hom ξ = ζ) ∧ ∀ (j : J) (ξ ξ' : Prim q (D.obj j)), Prim.map (c.ι.app j).hom ξ = Prim.map (c.ι.app j).hom ξ' → ∃ (k : J) (f : j ⟶ k), Prim.map (D.map f).hom ξ = Prim.map (D.map f).hom ξ' := by
  first | (exact @GlobalTheory.EtC.prim_filtered_colimit) | (exact GlobalTheory.EtC.prim_filtered_colimit) | (intros; apply GlobalTheory.EtC.prim_filtered_colimit  <;> assumption)
end
