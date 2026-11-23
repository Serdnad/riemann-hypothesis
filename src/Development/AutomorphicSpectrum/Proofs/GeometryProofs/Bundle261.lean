module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle257
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle063
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle129
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle230
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle105
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle258
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle092
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle026
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle080
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPeriodProduct
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle259
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT

def zpLocSubring (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) [hp : Fact p.Prime] : Subring Ω where
  carrier := {x | ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)}
  mul_mem' := by
    rintro x y ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * a', b * b', ?_, ?_⟩
    · intro h; rcases hp.out.dvd_mul.1 h with h | h <;> contradiction
    · push_cast; rw [div_mul_div_comm]
  one_mem' := ⟨1, 1, hp.out.not_dvd_one, by simp⟩
  add_mem' := by
    rintro x y ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    have h0 : (b : Ω) ≠ 0 := by
      rintro h; exact hb (by rw [Nat.cast_eq_zero.1 h]; exact dvd_zero p)
    have h0' : (b' : Ω) ≠ 0 := by
      rintro h; exact hb' (by rw [Nat.cast_eq_zero.1 h]; exact dvd_zero p)
    refine ⟨a * b' + a' * b, b * b', ?_, ?_⟩
    · intro h; rcases hp.out.dvd_mul.1 h with h | h <;> contradiction
    · rw [div_add_div _ _ h0 h0']; push_cast; ring
  zero_mem' := ⟨0, 1, hp.out.not_dvd_one, by simp⟩
  neg_mem' := by
    rintro x ⟨a, b, hb, rfl⟩
    exact ⟨-a, b, hb, by push_cast; ring⟩

theorem rootModel_nefAt_of_hodgeCpt : FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [Fintype (CMType H)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω) (p : ℕ), p ∈ S → HTFree 𝔐 p → Fl.RootLines M.xdeg e → ∀ mu : Top.Wt (CMType H) (D.p + D.q), Top.Dominant mu → M.NefAt p mu 0 := by
  intro hF E _ _ _ H _ D l Xo c O _ β Y S M 𝔐 Fl e p hpS hfree hroot mu hmu
  rcases Nat.eq_zero_or_pos (D.p + D.q) with h0 | hpos
  · intro W _
    unfold Top.RootModel.curveDeg
    refine le_of_eq (Finset.sum_eq_zero fun j _ => ?_).symm
    cases j with
    | none => simp [Top.RootModel.coef]
    | some r => exact absurd r.2.2 (by omega)
  · haveI : Fact p.Prime := ⟨𝔐.S_prime p hpS⟩
    haveI : CharZero M.Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance
    let o := zpLocSubring M.Ω p
    letI : Algebra o M.Ω := o.subtype.toAlgebra
    have ho : ∀ x : M.Ω, x ∈ (algebraMap o M.Ω).range ↔
        ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : M.Ω) / (b : M.Ω) := by
      intro x
      change x ∈ o.subtype.range ↔ _
      rw [Subring.range_subtype]
      rfl
    have h1 := trivFlagMod_rootLines_model hF E H D l Xo c O β Y S M.Ω M.K M.ι M.y 𝔐 p hpS hpos o ho Fl
      M.xdeg e hfree hroot
    have hR := 𝔐.R_ge p hpS
    have h2 : ∀ τ, Num.TrivFlagMod o (p : o) M.y (D.p + D.q) (fun i => M.xdeg (τ, i)) := fun τ =>
      trivFlagMod_of_dvd o M.Ω M.K M.ι M.y _ _ _ _ (dvd_pow_self (p : o) (by omega)) (h1 τ)
    exact trivflag_nef_fibre (CMType H) (D.p + D.q) M p o ho h2 mu hmu

end GlobalTheory.CompanionTheory.Ar.HT
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec

section GenInj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem allWt_eq_zero_of_generic (h : GenFrEx Xo c) {e : Ix Dw → ℤ} {g : Rul Xo c}
    (hg : g ∈ GlobalTheory.AllWt.secZ Xo c e) (h0 : ∀ Z, evC h Z g = 0) : g = 0 := by
  set_option synthInstance.maxHeartbeats 200000 in
    obtain ⟨hL, -, -, hA'⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
    have hA := hA' h
    have hfield : ∀ (L : Type) [Field L] [Algebra c.F L] (w : FrPt Xo c L), evR Xo c g w = 0 := by
      intro L _ _ w
      obtain ⟨C, ψ, z, t', hz, hb⟩ := hA L w
      obtain ⟨q, χ, y₀, hy₀⟩ := hL.test C.R C.y
      have h1 : evR Xo c g C.yg = 0 := by
        rw [GlobalTheory.FlagTan.evR_frBor hg C.bor]
        have := h0 C.Z
        unfold evC at this
        rw [this, mul_zero]
      have h2 : χ (g q y₀) = 0 := by
        rw [GlobalTheory.FlagTan.evR_eq hg.1 (frMap_trans _ _ _ _ _ _ _ _ hy₀ C.gen)] at h1
        exact Subtype.ext h1
      have h3 : evR Xo c g z = 0 := by
        rw [GlobalTheory.FlagTan.evR_eq hg.1 (frMap_trans _ _ _ _ _ _ _ _ hy₀ hz), AlgHom.comp_apply, h2, map_zero]
      rw [GlobalTheory.FlagTan.evR_frBor hg hb, h3, mul_zero]
    funext p y
    have hred : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
    show g p y = 0
    refine IsNilpotent.eq_zero ?_
    rw [nilpotent_iff_mem_prime]
    intro P hP
    let φ : p.R →ₐ[c.F] P.ResidueField := IsScalarTower.toAlgHom c.F p.R P.ResidueField
    obtain ⟨w, hw⟩ := hL.bc _ _ φ y
    have h4 := hfield _ w
    rw [GlobalTheory.FlagTan.evR_eq hg.1 hw] at h4
    exact Ideal.algebraMap_residueField_eq_zero.1 h4

theorem mem_allWt_of_secZ {a : WZ E} {f : Rul Xo c} (hf : f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a) :
    f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a) := by
  refine ⟨hf.1, fun p t y y' hb => ?_⟩
  rw [hf.2 p t y y' hb, Units.coe_prod]

theorem mem_secZ_of_allWt {a : WZ E} {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a)) :
    f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a := by
  refine ⟨hf.1, fun p t y y' hb => ?_⟩
  rw [hf.2 p t y y' hb, Units.coe_prod]

theorem exZ_add (a b : WZ E) :
    GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw (a + b) = GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a + GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw b := by
  funext i
  cases i <;> simp [GlobalTheory.CompanionTheory.Ar.Rec.exZ]

theorem secZ_eq_zero_of_generic (h : GenFrEx Xo c) {a : WZ E} {f : Rul Xo c}
    (hf : f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a) (h0 : ∀ Z, evC h Z f = 0) : f = 0 :=
  allWt_eq_zero_of_generic h (mem_allWt_of_secZ hf) h0

theorem secZ_mul {a b : WZ E} {f g : Rul Xo c} (hf : f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a)
    (hg : g ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c b) : f * g ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (a + b) := by
  apply mem_secZ_of_allWt
  rw [exZ_add]
  exact GlobalTheory.AllWt.mul_mem_secZ (mem_allWt_of_secZ hf) (mem_allWt_of_secZ hg)

theorem one_mem_secZ_zero : (1 : Rul Xo c) ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) :=
  ⟨fun p q φ y z _ => by simp, fun p t y y' _ => by simp [GlobalTheory.CompanionTheory.Ar.Rec.exZ]⟩

theorem evC_mul_of_test {h : GenFrEx Xo c} (hT : GenFromTest Xo c h) (Z : Comp Xo c) (f g : Rul Xo c) :
    evC h Z (f * g) = evC h Z f * evC h Z g := by
  unfold evC evR evalAt
  rw [dite_eq_left (hT Z), dite_eq_left (hT Z), dite_eq_left (hT Z)]
  exact map_mul _ _ _

theorem evC_one_of_test {h : GenFrEx Xo c} (hT : GenFromTest Xo c h) (Z : Comp Xo c) :
    evC h Z (1 : Rul Xo c) = 1 := by
  unfold evC evR evalAt
  rw [dite_eq_left (hT Z)]
  exact map_one _

end GenInj

theorem sections_generic_indicators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → (∀ a, ∀ f ∈ secZ Xo c a, (∀ Z, evC h Z f = 0) → f = 0) ∧ (∀ a Z, ∀ f ∈ cuspOn U h a Z, evC h Z f = 0 → f = 0) ∧ (∀ a b, ∀ f ∈ secZ Xo c a, ∀ g ∈ secZ Xo c b, f * g ∈ secZ Xo c (a + b)) ∧ (∀ Z, e Z * e Z = e Z) ∧ (∀ Z Z', Z ≠ Z' → e Z * e Z' = 0) ∧ ∑ᶠ Z, e Z = 1 := by
  intro E _ _ _ H Dw l Xo c r U h e hC
  have hT := hC.genT
  have hz : ∀ Z, e Z ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) := fun Z => by
    have h1 := hC.e_sec Z
    rw [← GlobalTheory.CompanionTheory.Ar.Rec.secZ_nat] at h1
    have h2 : (fun x => ((((0 : (E →+* ℂ) × ℕ → ℕ)) x : ℕ) : ℤ)) = (0 : WZ E) := by
      funext x
      simp
    rwa [h2] at h1
  have hmul : ∀ {f g : Rul Xo c}, f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) →
      g ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) → f * g ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) := by
    intro f g hf hg
    have := secZ_mul hf hg
    rwa [add_zero] at this
  have heq : ∀ {f g : Rul Xo c}, f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) →
      g ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) → (∀ Z, evC h Z f = evC h Z g) → f = g := by
    intro f g hf hg hv
    refine sub_eq_zero.1 (secZ_eq_zero_of_generic h (Submodule.sub_mem _ hf hg) fun Z => ?_)
    rw [← evL_apply, map_sub, evL_apply, evL_apply, hv Z, sub_self]
  have hfin : Finite (Comp Xo c) := Formalism.L2.Pj.CompFin.finite_comp Xo c
  letI := Fintype.ofFinite (Comp Xo c)
  classical
  refine ⟨fun a f hf h0 => secZ_eq_zero_of_generic h hf h0, fun a Z f hf h0 => ?_,
    fun a b f hf g hg => secZ_mul hf hg, fun Z => ?_, fun Z Z' hne => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf
    refine secZ_eq_zero_of_generic h (Submodule.mem_inf.1 h1).1 fun Z' => ?_
    by_cases hZ : Z' = Z
    · rw [hZ]
      exact h0
    · have h3 := Submodule.mem_iInf _ |>.1 h2 Z'
      have h4 := Submodule.mem_iInf _ |>.1 h3 hZ
      exact h4
  · refine heq (hmul (hz Z) (hz Z)) (hz Z) fun Z' => ?_
    rw [evC_mul_of_test hT]
    by_cases hZ : Z' = Z
    · subst hZ
      rw [(hC.e_val Z').1, one_mul]
    · rw [(hC.e_val Z).2 Z' hZ, zero_mul]
  · refine heq (hmul (hz Z) (hz Z')) (Submodule.zero_mem _) fun Y => ?_
    have hzero : evC h Y (0 : Rul Xo c) = 0 := by
      rw [← evL_apply, map_zero]
    rw [evC_mul_of_test hT, hzero]
    by_cases hY : Y = Z
    · subst hY
      rw [(hC.e_val Z').2 Y hne, mul_zero]
    · rw [(hC.e_val Z).2 Y hY, zero_mul]
  · rw [finsum_eq_sum_of_fintype]
    refine heq (Submodule.sum_mem _ fun Z _ => hz Z) one_mem_secZ_zero fun Y => ?_

    rw [evC_one_of_test hT, ← evL_apply, map_sum, Finset.sum_eq_single Y]
    · rw [evL_apply]
      exact (hC.e_val Y).1
    · intro Z _ hZ
      rw [evL_apply]
      exact (hC.e_val Z).2 Y (Ne.symm hZ)
    · intro hY
      exact absurd (Finset.mem_univ Y) hY

end GlobalTheory.CompanionTheory.Ar.Rec
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

theorem exists_hodgeInnerProduct_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (V : Type) [AddCommGroup V] [Module ℂ V] (M : LieModel t.G z V), (∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' t z), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L) → ∃ h : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ, (∀ v w c, HodgeIP t.G t.PP.L z (M.pt v) (M.pt w) c ↔ c = h v w) ∧ (∀ v w, h w v = starRingEnd ℂ (h v w)) ∧ ∀ v, v ≠ 0 → 0 < (h v v).re := by
  intro E _ _ _ H X t z V _ _ M ⟨t', m, hP, hA⟩
  have hab : IsAbelianScheme t'.G := AbelianSchemeGerms.isAbelianScheme_of_proper t'.G t'.semi
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim ℂ t'.G hab
  obtain ⟨u₀, hc⟩ := GlobalTheory.T.exists_exp_chart_coordinates t'.G t'.PP.L g hab hA hg
  obtain ⟨u, Hm, χ, hex, hH, hχ, hlaw⟩ := GlobalTheory.T.theta_multiplier_normal_form t'.G t'.PP t'.cub g u₀
  obtain ⟨N, J, Θ, hN, hd, hq, hne, hsep⟩ := GlobalTheory.T.exists_theta_basis_of_factor t'.G t'.PP.L g u Hm χ t'.PP.isLB hab hA hlaw
  have hpos := GlobalTheory.T.theta_functions_finite_dim g u.Λ u.discrete u.full Hm χ N J Θ hH hχ hN hd hq hne hsep
  have hAH : u.IsAH Hm χ := ⟨hH, hpos, hχ, hlaw⟩
  obtain ⟨ht₁, ht₂⟩ := @GlobalTheory.TangentOrigin.tangent_bijection_of_values @GlobalTheory.valAt'_rules t'.G _ t'.PP.L g u
    (by simpa only [hex] using hc)
  obtain ⟨w₀, hw₀, -⟩ := m.lin
  have hL := t'.PP.isLB
  have hM := LB.isLB_pull t.PP.isLB m.φ
  let u₁ : HolUnif t'.G (t.PP.L.pull m.φ) g := GlobalTheory.ArchMetricCompare.carry u hL hM hw₀
  have hAH₁ : u₁.IsAH Hm χ := GlobalTheory.ArchMetricCompare.carry_isAH hL hM hw₀ hAH
  have ht₁' : ∀ v, IsTangent v → ∃! w, u₁.IsDiff w v := ht₁
  have ht₂' : ∀ w, ∃! v, IsTangent v ∧ u₁.IsDiff w v := ht₂
  have hcart : IsGrpPullback t'.G t.G z m.φ := m.cart
  obtain ⟨D, hD⟩ := GlobalTheory.T.tangent_space_equiv_hol_unif X t.G z V M t'.G m.φ _ g u₁ hcart ht₁' ht₂'
  choose x hxt hxφ hxd using hD
  let h : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun v w => (Real.pi : ℂ) * hermForm Hm (D w) (D v))
    (fun v v' w => by simp [hermForm, Matrix.mulVec_add, dotProduct_add, mul_add])
    (fun c v w => by
      simp [hermForm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]; ring)
    (fun v w w' => by simp [hermForm, add_dotProduct, mul_add])
    (fun c v w => by simp [hermForm, smul_dotProduct, smul_eq_mul]; ring)
  have hh : ∀ v w, h v w = (Real.pi : ℂ) * hermForm Hm (D w) (D v) := fun _ _ => rfl
  refine ⟨h, fun v w c => ⟨?_, ?_⟩, fun v w => ?_, fun v hv => ?_⟩
  · rintro ⟨-, -, -, A, _, φ, g', u', Hm', χ', v', w', a, b, h1, h2, h3, h4, h5, h6, rfl⟩
    have := GlobalTheory.T.hol_unif_compare_isogeny X t.G t.PP.L z t'.G A m.φ φ g g' u₁ u' Hm Hm' χ χ' t.PP.isLB hab hcart h1 ht₁' ht₂' hAH₁ h2
      (x w) (x v) w' v' (D w) (D v) b a (hxt w) (hxt v) (h4.trans (hxφ w).symm) (h3.trans (hxφ v).symm)
      (hxd w) (hxd v) h6 h5
    rw [hh, ← this]
    rfl
  · rintro rfl
    exact ⟨t.PP.isLB, M.tan v, M.tan w, t'.G, inferInstance, m.φ, g, u₁, Hm, χ, x v, x w, D v, D w, hcart, hAH₁,
      hxφ v, hxφ w, hxd v, hxd w, rfl⟩
  · rw [hh, hh, map_mul, Complex.conj_ofReal, GlobalTheory.CompanionTheory.Ar.conj_hermForm hH]
  · rw [hh, Complex.re_ofReal_mul]
    exact mul_pos Real.pi_pos (hpos _ (fun h0 => hv (D.map_eq_zero_iff.1 h0)))

end GlobalTheory.CompanionTheory.Ar
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.cm_pack_period_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (n : ℕ) (a : Fin n → PureType.lat hP (sgnRt H b)) (v : Vecs X.y n) (s : X.K →+* ℂ) (y' : Sp ℂ ⟶ Xo.XF c) (v' : Vecs y' n) (r : ℝ), τ (H.rt : E) = sgnRt H b → (∀ k, X.IsCMVec b τ (a k) (v k)) → y' = spMap s ≫ X.y → (∀ k, (v' k).left = spMap (dualMap s) ≫ (v k).left) → IsLieNormSq (Z b).C.P (Z b).C.v ((s.comp (IntermediateField.inclusion (X.hM b)).toRingHom).comp (algebraMap (𝓞 (Z b).M) (Z b).M)) r → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y') v' (Matrix.of fun k k' => r * ((X.ε b : ℤ) : ℂ) * s (X.β (tauE c τ ((H.rt : E) * sesq (FU.Di i) (a k) (a k'))))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.GInf.hodgeGram_cmVec | exact GlobalTheory.CompanionTheory.Ar.Fl.GInf.hodgeGram_cmVec | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.GInf.hodgeGram_cmVec <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.uniformization_iso_transfer : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (M : LB A.left) (M' : LB A'.left) (g : ℕ) (u : HolUnif A M g) (u' : HolUnif A' M' g) (e : A' ≅ A) [IsMonHom e.hom], IsAbelianScheme A → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → (∀ v, IsTangent v → ∃! w, u'.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u'.IsDiff w v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.TanIso.tangentCoords_of_iso | exact GlobalTheory.CompanionTheory.Ar.Sl.TanIso.tangentCoords_of_iso | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.TanIso.tangentCoords_of_iso <;> assumption)
end
