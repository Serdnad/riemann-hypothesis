module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle431
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteConesPolarizedFanLevelStructure
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3004
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle680
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsaRos
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

theorem _root_.GlobalTheory.T.thetaKeyRule_isUnit_at_bad_level_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (κ : KeyRule), IsKeyRule κ → 1 ≤ Dw.p + Dw.q → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → ¬ l.GoodAt p → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (x : Sp T.Fr ⟶ Xo.X), x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom) → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)), SABMap t' Xo.univ.t x → SABMap t' G (spMap (algebraMap T.V T.Fr)) → ∀ (n : ℕ) (w : Fin n → (epsR T.V ⟶ G.G)), IsLieBasis w → ∀ (θ : G.PP.L.Sec), Generates (X := G.G) θ → ∀ (k : KeyIn T.Fr), IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr) → ∃ u : T.Vˣ, (κ T.Fr k : T.Fr) = algebraMap T.V T.Fr u := by
  first | exact @GlobalTheory.KeyBadPrime.key_unit_bad | exact GlobalTheory.KeyBadPrime.key_unit_bad | (intros; apply GlobalTheory.KeyBadPrime.key_unit_bad <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.E8Order

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

variable {R : Type} [CommRing R] [IsDomain R]

abbrev unitsR (R : Type) [CommRing R] [IsDomain R] : Subgroup (FractionRing R)ˣ :=
  (Units.map (algebraMap R (FractionRing R)).toMonoidHom).range

abbrev QR (R : Type) [CommRing R] [IsDomain R] := (FractionRing R)ˣ ⧸ unitsR R

abbrev cls : (FractionRing R)ˣ →* QR R := QuotientGroup.mk' (unitsR R)

theorem cls_eq_iff (x y : (FractionRing R)ˣ) :
    cls x = cls y ↔ ∃ u : Rˣ, (x : FractionRing R) = (y : FractionRing R) * algebraMap R (FractionRing R) u := by
  rw [eq_comm, QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨z, ⟨u, rfl⟩, hz⟩
    exact ⟨u, by rw [← hz]; rfl⟩
  · rintro ⟨u, hu⟩
    exact ⟨_, ⟨u, rfl⟩, Units.ext (by rw [hu]; rfl)⟩

theorem cls_unit (u : Rˣ) : cls (Units.map (algebraMap R (FractionRing R)).toMonoidHom u) = 1 :=
  (QuotientGroup.eq_one_iff _).2 ⟨u, rfl⟩

variable [IsLocalRing R]

def tq (D : DegPre R) (a b : D.X) : QR R :=
  cls (psiCoord D (a + b)) * (cls (psiCoord D a))⁻¹ * (cls (psiCoord D b))⁻¹

theorem cls_tauCoord {D : DegPre R} {a b : D.X} {x : (FractionRing R)ˣ} (hx : IsTauCoord D a b x) :
    cls x = tq D a b := by
  obtain ⟨u, hu⟩ := GlobalTheory.TauCoordQuot.main R D a b x _ _ _ hx (psiCoord_spec D (a + b)) (psiCoord_spec D a)
    (psiCoord_spec D b)
  have : x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u *
      (psiCoord D (a + b) * (psiCoord D a)⁻¹ * (psiCoord D b)⁻¹) := by
    ext; rw [hu]; simp <;> ring
  rw [this, map_mul, cls_unit, _root_.one_mul, tq, map_mul, map_mul, map_inv, map_inv]

theorem tq_symm (D : DegPre R) (a b : D.X) : tq D a b = tq D b a := by
  simp only [tq, add_comm a b]; exact mul_right_comm _ _ _

theorem tq_add_left (D : DegPre R) (hB : D.TauBimult) (a z b : D.X) : tq D (a + z) b = tq D a b * tq D z b := by
  obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
  obtain ⟨x', hx'⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D z b
  obtain ⟨x'', hx''⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D (a + (1 : ℕ) • z) b
  obtain ⟨u, hu⟩ := GlobalTheory.TauShift.main R D hB a z b 1 x x' x'' hx hx' hx''
  rw [one_smul] at hx''
  rw [← cls_tauCoord hx'', ← cls_tauCoord hx, ← cls_tauCoord hx', hu, map_mul, cls_unit, _root_.one_mul, pow_one, map_mul]

def tqHom (D : DegPre R) (hB : D.TauBimult) (a : D.X) : D.X →+ Additive (QR R) :=
  AddMonoidHom.mk' (fun b => Additive.ofMul (tq D a b)) fun b b' => by
    rw [tq_symm D a (b + b'), tq_add_left D hB, tq_symm D b a, tq_symm D b' a]; rfl

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsDiscreteValuationRing R → ∀ (D D' : DegPre R), D'.TauBimult → D'.PsiEven → D.TauBimult → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (ϖ : R) (β : LinearMap.BilinForm ℤ D.X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → (∀ a b' (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D a b' x → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * algebraMap R (FractionRing R) ϖ ^ (β a b')) → ∀ (c : Fin 8 → (D.X →+ D'.X)) (e : D'.X ≃+ (Fin 8 → D.X)), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → (∀ v a' b (x x' : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D (e a' v) b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D' a' (c v b) x' → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * (x' : FractionRing R)) → ∀ y r, PsiCoord D' y r → 0 ≤ qW W β (e y) ∧ Associated r (ϖ ^ (qW W β (e y)).toNat) := by
  intro R _ _ _ hR D D' hB' hE' hB W hW ϖ β hs hp hτ c e hsum hcomp y r hr
  haveI := hR
  have hq : 0 ≤ qW W β (e y) := GlobalTheory.Poinc.qW_nonneg_of_posW W hW.1 β hs hp (e y)
  refine ⟨hq, ?_⟩
  obtain ⟨s, hsd⟩ : ∃ s, s = e y := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : Fin 8 → D.X, t = fun v => ∑ u, (W + W.transpose) v u • s u := ⟨_, rfl⟩
  rw [← hsd] at hq ⊢
  have hsum2 : ∑ v, β (s v) (-(t v)) = -(2 * qW W β s) := by
    subst ht

    simp only [map_neg, map_sum, map_zsmul, smul_eq_mul, Finset.sum_neg_distrib, neg_inj]
    simp only [Matrix.add_apply, Matrix.transpose_apply, add_mul, Finset.sum_add_distrib, qW, two_mul]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [hs]
  have h1 : ∑ v, c v (t v) = y := by rw [ht, hsd]; exact hsum y
  have hy : -y = ∑ v, c v (-(t v)) := by
    rw [← h1]; simp only [map_neg, Finset.sum_neg_distrib]
  obtain ⟨x', hx'⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D' y (-y)
  have hcl : cls x' = tq D' y (-y) := cls_tauCoord hx'
  have hterm : ∀ v, tq D' y (c v (-(t v))) = tq D (s v) (-(t v)) := by
    intro v
    obtain ⟨a, ha⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D (e y v) (-(t v))
    obtain ⟨b, hb⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D' y (c v (-(t v)))
    obtain ⟨u, hu⟩ := hcomp v y (-(t v)) a b ha hb
    rw [← cls_tauCoord hb, hsd, ← cls_tauCoord ha]
    exact ((cls_eq_iff _ _).2 ⟨u, by rw [hu, mul_comm]⟩).symm
  have hprod : Additive.ofMul (tq D' y (-y)) = ∑ v, Additive.ofMul (tq D (s v) (-(t v))) := by
    have := map_sum (tqHom D' hB' y) (fun v => c v (-(t v))) Finset.univ
    rw [← hy] at this
    refine this.trans ?_
    exact Finset.sum_congr rfl fun v _ => congrArg Additive.ofMul (hterm v)
  obtain ⟨w0, hw0⟩ := GlobalTheory.PsiFromTauEven.tauCoord_mul_sq R D' hB' hE' y r hr x' hx'
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_pow two_ne_zero, mul_zero] at hw0
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 w0.ne_zero hw0.symm
  let ru : (FractionRing R)ˣ := toUnitK r hr0
  have hru : x' * ru ^ 2 = Units.map (algebraMap R (FractionRing R)).toMonoidHom w0 := by
    ext; simp [ru, toUnitK, hw0]
  have hcr : cls ru ^ 2 = (cls x')⁻¹ := by
    have := congrArg cls hru
    rw [map_mul, map_pow, cls_unit] at this
    exact eq_inv_of_mul_eq_one_right this
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hq
  rw [hn, Int.toNat_natCast]
  have final : ∀ ρ : (FractionRing R)ˣ, (ρ : FractionRing R) = algebraMap R (FractionRing R) (ϖ ^ n) →
      cls ru ^ 2 = cls ρ ^ 2 → Associated r (ϖ ^ n) := by
    intro ρ hρ h
    rw [← map_pow, ← map_pow] at h
    obtain ⟨u, hu⟩ := (cls_eq_iff _ _).1 h
    simp only [Units.val_pow_eq_pow_val, hρ, ru, toUnitK, Units.val_mk0, ← map_pow, ← map_mul] at hu
    have hsq : Associated ((ϖ ^ n) ^ 2) (r ^ 2) := ⟨u, (IsFractionRing.injective R (FractionRing R) hu).symm⟩
    exact (associated_of_dvd_dvd ((IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 hsq.dvd)
      ((IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 hsq.symm.dvd)).symm
  by_cases hϖ : ϖ = 0
  · have hβ0 : ∀ a b, β a b = 0 := by
      intro a b
      obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
      obtain ⟨u, hu⟩ := hτ a b x hx
      by_contra h
      rw [hϖ, map_zero, zero_zpow _ h, mul_zero] at hu
      exact x.ne_zero hu
    have hq0 : qW W β s = 0 := by simp [qW, hβ0]
    have htq : ∀ a b, tq D a b = 1 := by
      intro a b
      obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
      obtain ⟨u, hu⟩ := hτ a b x hx
      rw [← cls_tauCoord hx]
      have : x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u := by
        ext; rw [hu, hβ0, zpow_zero, _root_.mul_one]; rfl
      rw [this, cls_unit]
    have h1' : tq D' y (-y) = 1 := by
      apply Additive.ofMul.injective
      rw [hprod]; simp [htq]
    have hn0 : n = 0 := by omega
    subst hn0
    refine final 1 (by simp) ?_
    rw [hcr, hcl, h1']; simp
  · let ϖu : (FractionRing R)ˣ := toUnitK ϖ hϖ
    have htq : ∀ a b, tq D a b = cls ϖu ^ β a b := by
      intro a b
      obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
      obtain ⟨u, hu⟩ := hτ a b x hx
      rw [← cls_tauCoord hx, ← map_zpow]
      exact (cls_eq_iff _ _).2 ⟨u, by rw [hu, Units.val_zpow_eq_zpow_val]; simp [ϖu, toUnitK, mul_comm]⟩
    have hx'cl : cls x' = cls ϖu ^ (-(2 * qW W β s)) := by
      rw [hcl]; apply Additive.ofMul.injective; rw [hprod]
      simp only [htq, ofMul_zpow]
      rw [← Finset.sum_smul, hsum2]
    refine final (ϖu ^ n) (by simp [ϖu, toUnitK]) ?_
    rw [hcr, hx'cl, hn, map_pow, ← zpow_neg, neg_neg, show (2 * (n : ℤ)) = ((n * 2 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, pow_mul]

end GlobalTheory.Poinc.E8Order
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.RayInt

open ReciprocityTheory.ChartRestriction.G.Semi TopologicalSpace

attribute [local instance] SplitExt.free SplitExt.finite

theorem mem_chart_of_mem {S : Scheme.{0}} (E : SplitExt S) (j : E.ChartIdx) (b : E.B.left)
    (h : ∀ k, b ∈ (E.O (E.basis k)).L.U (j k)) : b ∈ E.chart j := by
  have e : E.chart j = Finset.univ.inf (fun k => (E.O (E.basis k)).L.U (j k)) :=
    (Finset.inf_univ_eq_iInf _).symm
  rw [e, ← SetLike.mem_coe, Opens.coe_finset_inf]
  simp only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true, Set.iInf_eq_iInter, Set.mem_iInter,
    Function.comp_apply, SetLike.mem_coe]
  exact h

theorem isIntegral_of_isGt (R : Type) [CommRing R] [IsDomain R] (E : SplitExt (Spec (CommRingCat.of R)))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (hG : E.IsGt G) (hs : Smooth G.hom) :
    IsIntegral G.left := by
  obtain ⟨d⟩ := hG
  have hB := E.isAbelian
  haveI : Smooth E.B.hom := hB.smooth
  haveI : GeometricallyConnected E.B.hom := hB.geomConnected
  have hSne : Nonempty (Spec (CommRingCat.of R)) := inferInstance
  have hBne : Nonempty E.B.left := ⟨(η[E.B] : 𝟙_ _ ⟶ E.B).left (show (𝟙_ (Over _)).left from hSne.some)⟩
  haveI : IrreducibleSpace E.B.left :=
    GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain R E.B ‹_› ‹_› hBne
  haveI : IsReduced E.B.left := GlobalTheory.isReduced_of_smooth_of_isReduced E.B.hom
  haveI : IsIntegral E.B.left := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : IsReduced G.left := GlobalTheory.isReduced_of_smooth_of_isReduced G.hom
  obtain ⟨b⟩ := hBne
  have hk : ∀ k, ∃ i, b ∈ (E.O (E.basis k)).L.U i := fun k => by
    have hb : b ∈ (⊤ : E.B.left.Opens) := trivial
    rw [← (E.O (E.basis k)).isLB.cover, Opens.mem_iSup] at hb
    exact hb
  choose j hj using hk
  have hbj : b ∈ E.chart j := mem_chart_of_mem E j b hj
  obtain ⟨V, hV, hbV, hVj⟩ := (Opens.isBasis_iff_nbhd.mp E.B.left.isBasis_affineOpens) hbj
  have hbV' : b ∈ V := hbV
  haveI : Nonempty V := ⟨⟨b, hbV'⟩⟩
  haveI := d.q_affine
  haveI := d.q_flat
  have hsurj := d.q_surjective
  set W : G.left.Opens := d.q.left ⁻¹ᵁ V with hWdef
  have hV : IsAffineOpen V := hV
  have hW : IsAffineOpen W := hV.preimage d.q.left
  have hbij := d.coord j V hV hVj
  haveI : IsDomain Γ(G.left, W) :=
    Function.Injective.isDomain (RingEquiv.ofBijective _ hbij).symm.toRingHom
      (RingEquiv.ofBijective _ hbij).symm.injective
  obtain ⟨g, hg⟩ := hsurj.surj b
  have hgW : g ∈ W := by show d.q.left g ∈ V; rw [hg]; exact hbV'
  haveI : Nonempty W := ⟨⟨g, hgW⟩⟩
  haveI : IsAffine W := hW
  haveI : IsDomain Γ(W, ⊤) :=
    Function.Injective.isDomain (W.topIso).commRingCatIsoToRingEquiv.toRingHom
      (W.topIso).commRingCatIsoToRingEquiv.injective
  haveI : IsIntegral W := isIntegral_of_isAffine_of_isDomain W
  have hirrW : IsIrreducible (W : Set G.left) := by
    have hI := (IrreducibleSpace.isIrreducible_univ W).image (⇑W.ι) (Scheme.Hom.continuous _).continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at hI
  have hη : genericPoint E.B.left ∈ V :=
    ((genericPoint_spec E.B.left).mem_open_set_iff V.isOpen).2 ⟨b, trivial, hbV'⟩
  have hcl : closure (W : Set G.left) = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨z', hz', e⟩ := Flat.generalizingMap d.q.left (genericPoint_specializes (d.q.left z))
    have hz'W : z' ∈ (W : Set G.left) := by show d.q.left z' ∈ V; rw [e]; exact hη
    exact closure_mono (Set.singleton_subset_iff.2 hz'W) (specializes_iff_mem_closure.mp hz')
  haveI : IrreducibleSpace G.left := by
    rw [irreducibleSpace_def]
    have := hirrW.closure
    rwa [hcl] at this
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem isIntegral_H : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), IsIntegral Y.H.left := by
  intro R _ _ _ _ Q O _ _ _ oa Y
  exact isIntegral_of_isGt R _ Y.H Y.isGt (GlobalTheory.RayTan.smooth_H R Q O oa Y)

end GlobalTheory.RayInt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.SymMono

def elem {r : ℕ} (a b : Fin r) : LinearMap.BilinForm ℤ (Fin r → ℤ) :=
  (LinearMap.mul ℤ ℤ).compl₁₂ (LinearMap.proj a) (LinearMap.proj b)

@[simp] theorem elem_apply {r : ℕ} (a b : Fin r) (u v : Fin r → ℤ) : elem a b u v = u a * v b := rfl

def symElem {r : ℕ} (a b : Fin r) : LinearMap.BilinForm ℤ (Fin r → ℤ) :=
  (if a ≤ b then elem a b else 0) + (if a < b then elem b a else 0)

theorem symElem_symm {r : ℕ} (a b : Fin r) (u v : Fin r → ℤ) : symElem a b u v = symElem a b v u := by
  unfold symElem
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h, h.le]; ring
  · simp; ring
  · simp [not_le.2 h, not_lt.2 h.le]

theorem ite_bil_apply {r : ℕ} (p : Prop) [Decidable p] (f : LinearMap.BilinForm ℤ (Fin r → ℤ)) (u v : Fin r → ℤ) :
    (if p then f else 0) u v = if p then f u v else 0 := by
  split_ifs <;> rfl

theorem sum_symElem {r : ℕ} (β : LinearMap.BilinForm ℤ (Fin r → ℤ)) (hβ : ∀ u v, β u v = β v u) :
    β = ∑ a, ∑ b, β (Pi.single a 1) (Pi.single b 1) • symElem a b := by
  refine LinearMap.BilinForm.ext_basis (Pi.basisFun ℤ (Fin r)) fun i j => ?_
  simp only [Pi.basisFun_apply, LinearMap.sum_apply, LinearMap.smul_apply, symElem,
    LinearMap.add_apply, smul_eq_mul]
  simp only [ite_bil_apply, elem_apply, Pi.single_apply, mul_add, Finset.sum_add_distrib, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul]
  simp only [← ite_and]
  rw [Fintype.sum_eq_single i (fun x hx => Fintype.sum_eq_zero _ (fun y => if_neg (by tauto))),
    Fintype.sum_eq_single j (fun x hx => Fintype.sum_eq_zero _ (fun y => if_neg (by tauto))),
    Fintype.sum_eq_single j (fun y hy => if_neg (by tauto)),
    Fintype.sum_eq_single i (fun y hy => if_neg (by tauto))]
  rcases le_or_gt i j with h | h
  · simp [h, not_lt.2 h]
  · simp [h, not_le.2 h, hβ (Pi.single i 1)]

end GlobalTheory.SymMono

namespace GlobalTheory.SymMono

theorem zpow_finsum {G J : Type} [CommGroup G] (g : G) (s : Finset J) (f : J → ℤ) :
    g ^ (∑ i ∈ s, f i) = ∏ i ∈ s, g ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

theorem symElem_mem {r : ℕ} (a b : Fin r) : symElem a b ∈ balForms (id : ℤ → ℤ) (Fin r → ℤ) :=
  mem_balForms_int.2 (symElem_symm a b)

theorem repr_self_eq_sum {r : ℕ} {I : Type} (ε : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))) (i k : I) :
    ε.repr (ε i) k = ∑ a, ∑ b, (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) (Pi.single a 1) (Pi.single b 1) *
      ε.repr ⟨symElem a b, symElem_mem a b⟩ k := by
  have he : ε i = ∑ a, ∑ b, (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) (Pi.single a 1) (Pi.single b 1) •
      (⟨symElem a b, symElem_mem a b⟩ : balForms (id : ℤ → ℤ) (Fin r → ℤ)) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact sum_symElem _ (mem_balForms_int.1 (ε i).2)
  conv_lhs => rw [he]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearEquiv.map_smul, Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]

theorem eq_of_prod_zpow_eq (F : Type) [Field F] (r : ℕ) (I : Type) [Fintype I]
    (ε : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))) (x y : I → F) (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (h : ∀ a b, ∏ i, x i ^ (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b =
      ∏ i, y i ^ (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b) : x = y := by
  classical
  set X : I → Fˣ := fun i => Units.mk0 (x i) (hx i) with hXd
  set Y : I → Fˣ := fun i => Units.mk0 (y i) (hy i) with hYd
  have hXY : ∀ a b, ∏ i, (X i / Y i) ^ ((ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b) = 1 := by
    intro a b
    rw [Finset.prod_congr rfl (fun i _ => div_zpow _ _ _), Finset.prod_div_distrib, div_eq_one]
    apply Units.ext
    simpa [X, Y, Units.coe_prod] using h a b
  funext k
  have hk : X k / Y k = 1 := by
    calc X k / Y k = ∏ i, (X i / Y i) ^ (ε.repr (ε i) k) := by
          simp [Finsupp.single_apply]
      _ = ∏ i, ∏ a, ∏ b, ((X i / Y i) ^ ((ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) (Pi.single a 1)
            (Pi.single b 1))) ^ (ε.repr ⟨symElem a b, symElem_mem a b⟩ k) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [repr_self_eq_sum, zpow_finsum]
          refine Finset.prod_congr rfl fun a _ => ?_
          rw [zpow_finsum]
          refine Finset.prod_congr rfl fun b _ => ?_
          rw [zpow_mul]
      _ = ∏ a, ∏ b, (∏ i, (X i / Y i) ^ ((ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) (Pi.single a 1)
            (Pi.single b 1))) ^ (ε.repr ⟨symElem a b, symElem_mem a b⟩ k) := by
          rw [Finset.prod_comm]
          refine Finset.prod_congr rfl fun a _ => ?_
          rw [Finset.prod_comm]
          refine Finset.prod_congr rfl fun b _ => ?_
          rw [Finset.prod_zpow]
      _ = 1 := by simp [hXY]
  simpa [X, Y] using congrArg Units.val (div_eq_one.1 hk)

end GlobalTheory.SymMono
end

section

open GlobalTheory.PolFan GlobalTheory.LocM

theorem _root_.GlobalTheory.T.finite_minimiser_systems_balanced_forms_upto_aut : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], IsPolFanOn bar φ Y → ∀ (n N : ℕ) [NeZero N], 3 ≤ N → ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)), ∃ S : Finset ((Fin n → ZMod N) → Y), ∀ b ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b x x) → ∃ e : Y ≃ₗ[O] Y, ∀ μ : (Fin n → ZMod N) → Y, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → pull e.toLinearMap b (μ cl) (μ cl) ≤ pull e.toLinearMap b α α) → μ ∈ S := by
  first | exact @GlobalTheory.Poinc.MinSysTypeBal.finite_minimiser_systems_upTo_aut | exact GlobalTheory.Poinc.MinSysTypeBal.finite_minimiser_systems_upTo_aut | (intros; apply GlobalTheory.Poinc.MinSysTypeBal.finite_minimiser_systems_upTo_aut <;> assumption)
end

section

open GlobalTheory.PolFan GlobalTheory.LocM

theorem _root_.GlobalTheory.T.exists_finite_cones_polarized_fan_level_structure : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], IsPolFanOn bar φ Y → ∀ (n N : ℕ) [NeZero N], 3 ≤ N → ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → ∀ b₀ ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b₀ x x) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b₀ (μ cl) (μ cl) ≤ b₀ α α) → ∃ (p : ℕ) (m : Fin p → ℕ) (γ : ∀ i, Fin (m i) → LinearMap.BilinForm ℤ Y), (∀ i, IsCone bar φ (γ i)) ∧ ∀ b' ∈ balForms bar Y, (∀ x, 0 ≤ b' x x) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) → ∃ (i : Fin p) (k : ℕ) (cf : Fin (m i) → ℕ), 0 < k ∧ k • b' = ∑ j, cf j • γ i j := by
  first | exact @GlobalTheory.UPoinc.CellCones.exists_finite_cones | exact GlobalTheory.UPoinc.CellCones.exists_finite_cones | (intros; apply GlobalTheory.UPoinc.CellCones.exists_finite_cones <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformization_base_change_complete_dvr : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀], AdmBase R₀ (maximalIdeal R₀) → ∀ (D₀ : DegData R₀ (maximalIdeal R₀)) (A₀ : PolAV (Sp (FractionRing R₀))) (G₀ : Over (Sp R₀)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal R₀) D₀ A₀ G₀) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R₀ →+* W), Function.Injective φ → IsLocalHom φ → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), IsGrpPullback GW G₀ (spMap φ) β → LBIso UW.LG.L (U₀.LG.L.pull β) → Nonempty (IsPullDeg φ D₀.toPre DW.toPre) := by
  first | exact @GlobalTheory.Mum.isPullDeg_of_trait_unif | exact GlobalTheory.Mum.isPullDeg_of_trait_unif | (intros; apply GlobalTheory.Mum.isPullDeg_of_trait_unif <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_latticeIso_of_two_padicAlgCl_uniformisations : ∀ {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω'] (S : ThetaSys o Ω) (S' : ThetaSys o' Ω') (ρ : S.Real) (ρ' : S'.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (y₁ : S'.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (u' : ρ'.UTest p y₁) (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a → IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a' → LBIso P₀.L (u.A.L.pull a) → LBIso P₀.L (u'.A.L.pull a') → ∃ e : u.D.toPre.X ≃+ u'.D.toPre.X, (∀ χ r, u.PsiNorm χ r ↔ u'.PsiNorm (e χ) r) ∧ ∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) (pk' : QkPt u'.D.toPre (PadicAlgCl p) m) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A) (w : Sp (PadicAlgCl p) ⟶ P₀.A.left), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' x' → w ≫ P₀.A.hom = 𝟙 _ → w ≫ a = x.left → w ≫ a' = x'.left → CongMod m pk'.y (e pk.y) := by
  first | exact @GlobalTheory.UnifTorsK.main | exact GlobalTheory.UnifTorsK.main | (intros; apply GlobalTheory.UnifTorsK.main <;> assumption)
end
