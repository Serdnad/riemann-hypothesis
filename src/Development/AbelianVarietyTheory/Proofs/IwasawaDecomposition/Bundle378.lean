module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle299
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle354
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle355
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.SchurW



theorem schurW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (t : T) (h h' : (R.HX t).H) (a a' : R.cX.W), IntegrableOn (fun g => star ⟪a, R.cX.ext ((R.HX t).e h) g⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') g⟫_ℂ) (R.fdX t) (R.νX t) ∧ (Module.finrank ℂ R.cX.W : ℂ) * ∫ g in R.fdX t, star ⟪a, R.cX.ext ((R.HX t).e h) g⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') g⟫_ℂ ∂(R.νX t) = ⟪a', a⟫_ℂ * ⟪h, h'⟫_ℂ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB t h h' a a'
  haveI : IsTopologicalGroup (GA D D.sp.X') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D D.sp.X') := ⟨rfl⟩
  haveI : Countable (GQ D.sp.X') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig D.sp.X'.gram
  have hμ := hB.models.νX t
  haveI := hμ.1.1
  have hc := hB.models.cX
  have hH := hB.models.HX t
  let J := (levEnv D.sp.X' R.βX (R.datXt t)).J
  let χ := (levEnv D.sp.X' R.βX (R.datXt t)).χ
  let Ω : Subgroup (GA D D.sp.X') := (lev D.sp.cm D.sp.X'.gram R.βX (R.datXt t)).comap (finE D.sp.X')
  have hK : ∀ g : GA D D.sp.X', g ∈ Ω ↔ (finHom D.sp.X').rangeRestrict g ∈ J := fun g => Iff.rfl
  have hΩo : IsOpen (Ω : Set (GA D D.sp.X')) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_level D.sp.X' R.βX (R.datXt t)] with κ hκ
    exact (hK κ).2 hκ.1
  have hΩ1 : R.νX t (Ω : Set (GA D D.sp.X')) = 1 := GlobalTheory.Mass.Levels.measure_comap_finE hμ.1
  have hF : ∀ x, (R.HX t).e x ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ J χ := fun x => by
    have := LinearMap.mem_range_self (R.HX t).e x
    rw [hH.2.1] at this
    exact this
  have hinv : ∀ (u : GA D D.sp.X') v, R.cX.ρ u⁻¹ (R.cX.ρ u v) = v := fun u v => by
    have := congrArg (fun T : Module.End ℂ R.cX.W => T v) (show R.cX.ρ u⁻¹ * R.cX.ρ u = 1 by rw [← map_mul, inv_mul_cancel, map_one])
    exact this
  have hext : ∀ f, f ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ J χ → ∀ (γ : GA D D.sp.X'), γ ∈ GQ D.sp.X' →
      ∀ g, R.cX.ext f (γ * g) = R.cX.ext f g := by
    intro f hf γ hγ g
    show R.cX.ρ (γ * g)⁻¹ (f ((finHom D.sp.X').rangeRestrict (γ * g))) = R.cX.ρ g⁻¹ (f ((finHom D.sp.X').rangeRestrict g))
    have := hf ⟨γ, hγ⟩ ((finHom D.sp.X').rangeRestrict g) 1
    simp only [OneMemClass.coe_one, mul_one, map_one, Units.val_one, one_smul] at this
    rw [map_mul]
    erw [this]
    show R.cX.ρ (γ * g)⁻¹ (R.cX.ρ γ _) = _
    rw [_root_.mul_inv_rev, map_mul]
    exact congrArg (R.cX.ρ g⁻¹) (hinv γ _)
  choose y' hy'1 hy'2 using fun c => GlobalTheory.DefiniteMult.exists_fin_lift D.sp.X' ((R.B.R t).pres.y c)
  have hnorm : ∀ k : J, ‖((χ k : ℂˣ) : ℂ)‖ = 1 := fun k => GlobalTheory.AdelicScalar.norm_levFn _ _ _
  have hloc : ∀ f, f ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ J χ → ∀ c, ∀ k (hk : k ∈ Ω),
      R.cX.ext f (y' c * k) = ((χ ⟨_, (hK k).1 hk⟩ : ℂˣ) : ℂ) • R.cX.ρ k⁻¹ (f ((R.B.R t).pres.y c)) := by
    intro f hf c k hk
    have e1 : (finHom D.sp.X').rangeRestrict (y' c * k) = (R.B.R t).pres.y c * (finHom D.sp.X').rangeRestrict k := by
      rw [MonoidHom.map_mul, hy'2]
    have e2 := GlobalTheory.DefiniteMult.adForms_level hf ((R.B.R t).pres.y c) ⟨_, (hK k).1 hk⟩
    have e3 : R.cX.ρ (y' c * k)⁻¹ = R.cX.ρ k⁻¹ := by
      rw [_root_.mul_inv_rev, map_mul, hc.1 _ (inv_mem (hy'1 c)), mul_one]
    show R.cX.ρ (y' c * k)⁻¹ (f ((finHom D.sp.X').rangeRestrict (y' c * k))) = _
    refine (congrArg (R.cX.ρ (y' c * k)⁻¹) ((congrArg f e1).trans e2)).trans ?_
    refine (map_smul _ _ _).trans ?_
    exact congrArg (_ • ·) (LinearMap.congr_fun e3 _)
  let φ : GA D D.sp.X' → ℂ := fun g =>
    star ⟪a, R.cX.ext ((R.HX t).e h) g⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') g⟫_ℂ
  have hpt : ∀ c, ∀ k ∈ Ω, φ (y' c * k) = star ⟪a, R.cX.ρ k⁻¹ ((R.HX t).e h ((R.B.R t).pres.y c))⟫_ℂ *
      ⟪a', R.cX.ρ k⁻¹ ((R.HX t).e h' ((R.B.R t).pres.y c))⟫_ℂ := by
    intro c k hk
    have key : ∀ z p q : ℂ, ‖z‖ = 1 → star (z * p) * (z * q) = star p * q := by
      intro z p q hz
      have e : star z * z = 1 := by
        rw [Complex.star_def, Complex.conj_mul', hz]; norm_num
      rw [star_mul']
      linear_combination (star p * q) * e
    have hz := hnorm ⟨_, (hK k).1 hk⟩
    refine (congrArg₂ (fun u v : ℂ => star u * v) (congrArg (inner ℂ a) (hloc _ (hF h) c k hk))
      (congrArg (inner ℂ a') (hloc _ (hF h') c k hk))).trans ?_
    simp only [inner_smul_right]
    exact key _ _ _ hz
  have hmeas : ∀ x y : R.cX.W, Measurable fun g => ⟪x, R.cX.ρ g y⟫_ℂ := fun x y =>
    (continuous_const.inner (hc.2.2.1 y)).measurable
  have hirr : ∀ U : Submodule ℂ R.cX.W, (∀ g ∈ Ω, U.map (R.cX.ρ g) ≤ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine hc.2.2.2.2 U fun g => ?_
    obtain ⟨a0, ha0, k0, hk0, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D D.sp.X').1 g
    rw [map_mul, hc.1 k0 hk0, mul_one]
    refine hU a0 ((hK a0).2 ?_)
    have e : (finHom D.sp.X').rangeRestrict a0 = 1 := Subtype.ext ha0
    exact e ▸ J.one_mem
  have hS := fun c => GlobalTheory.T.schur_orthogonality_subgroup_measure_one (R.νX t) Ω hΩo.measurableSet hΩ1 R.cX.ρ hc.2.1 hmeas hirr a a'
    ((R.HX t).e h ((R.B.R t).pres.y c)) ((R.HX t).e h' ((R.B.R t).pres.y c))
  have huniq : ∀ x : GA D D.sp.X', ∃! i, ∃ γ ∈ GQ D.sp.X', ∃ k ∈ Ω, x = γ * y' i * k := by
    intro x
    refine (existsUnique_congr fun i => ?_).1 ((R.B.R t).pres.reps ((finHom D.sp.X').rangeRestrict x))
    constructor
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, γ.2, (γ * y' i)⁻¹ * x, (hK _).2 ?_, by group⟩
      have e' : (finHom D.sp.X').rangeRestrict ((γ * y' i)⁻¹ * x) = k := by
        simp only [map_mul, map_inv, hy'2, e]
        change (Bridge.ratF D.sp.X' γ * _)⁻¹ * (Bridge.ratF D.sp.X' γ * _ * k) = _
        exact inv_mul_cancel_left _ _
      exact cast (congrArg (· ∈ J) e').symm k.2
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      refine ⟨⟨γ, hγ⟩, ⟨_, (hK k).1 hk⟩, ?_⟩
      simp only [map_mul, hy'2]
      rfl
  have hSet : ∀ c, {γ : GA D D.sp.X' | γ ∈ GQ D.sp.X' ∧ (y' c)⁻¹ * γ * y' c ∈ Ω} =
      Subtype.val '' (Bridge.stab (Bridge.ratF D.sp.X') J ((R.B.R t).pres.y c) : Set (GQ D.sp.X')) := by
    intro c
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, Bridge.mem_stab]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨γ, h1⟩, ?_, rfl⟩
      have := (hK _).1 h2
      simp only [map_mul, map_inv, hy'2] at this
      exact this
    · rintro ⟨δ, h2, rfl⟩
      refine ⟨δ.2, (hK _).2 ?_⟩
      simp only [map_mul, map_inv, hy'2]
      exact h2
  have hfinS : ∀ c, Finite (Bridge.stab (Bridge.ratF D.sp.X') J ((R.B.R t).pres.y c)) := fun c =>
    Finite.of_equiv _ ((R.B.R t).pres.stabI c).toEquiv
  have hfin : ∀ c, {γ : GA D D.sp.X' | γ ∈ GQ D.sp.X' ∧ (y' c)⁻¹ * γ * y' c ∈ Ω}.Finite := fun c => by
    rw [hSet]
    haveI := hfinS c
    exact (Set.toFinite _).image _
  have hcard : ∀ c, ({γ : GA D D.sp.X' | γ ∈ GQ D.sp.X' ∧ (y' c)⁻¹ * γ * y' c ∈ Ω}.ncard : ℂ) =
      (Nat.card (Bridge.stab (Bridge.ratF D.sp.X') J ((R.B.R t).pres.y c)) : ℂ) := fun c => by
    have e := congrArg Set.ncard (hSet c)
    rw [Set.ncard_image_of_injective _ Subtype.val_injective] at e
    exact (congrArg (Nat.cast : ℕ → ℂ) e).trans (congrArg (Nat.cast : ℕ → ℂ) (Nat.card_coe_set_eq _).symm)
  have hintc : ∀ c, IntegrableOn (fun k => φ (y' c * k)) Ω (R.νX t) := fun c =>
    (hS c).1.congr_fun (fun k hk => (hpt c k hk).symm) hΩo.measurableSet
  have hIc : ∀ c, ∫ k in (Ω : Set (GA D D.sp.X')), φ (y' c * k) ∂(R.νX t) =
      ∫ k in (Ω : Set (GA D D.sp.X')), star ⟪a, R.cX.ρ k⁻¹ ((R.HX t).e h ((R.B.R t).pres.y c))⟫_ℂ *
        ⟪a', R.cX.ρ k⁻¹ ((R.HX t).e h' ((R.B.R t).pres.y c))⟫_ℂ ∂(R.νX t) := fun c =>
    setIntegral_congr_fun hΩo.measurableSet fun k hk => hpt c k hk
  have hfl : ∀ γ : GA D D.sp.X', γ ∈ GQ D.sp.X' → ∀ x : GA D D.sp.X', φ (γ * x) = φ x := fun γ hγ x => by
    show star ⟪a, R.cX.ext ((R.HX t).e h) (γ * x)⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') (γ * x)⟫_ℂ =
      star ⟪a, R.cX.ext ((R.HX t).e h) x⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') x⟫_ℂ
    exact congrArg₂ (fun u v => star ⟪a, u⟫_ℂ * ⟪a', v⟫_ℂ) (hext _ (hF h) γ hγ x) (hext _ (hF h') γ hγ x)
  have U1 := GlobalTheory.T.integral_fundamentalDomain_eq_sum_doubleCoset_unfold (GA D D.sp.X') (R.νX t) (GQ D.sp.X') Ω (R.fdX t) hμ.2 hΩo _ y' huniq hfin φ hfl hintc
  refine ⟨U1.1, ?_⟩
  change (Module.finrank ℂ R.cX.W : ℂ) * ∫ g in R.fdX t, φ g ∂(R.νX t) = _
  refine (congrArg (_ * ·) U1.2).trans ?_
  refine Eq.trans ?_ (congrArg (⟪a', a⟫_ℂ * ·) (hH.2.2 h h').symm)
  simp only [Bridge.adInner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine (congrArg₂ (fun (u v : ℂ) => (Module.finrank ℂ R.cX.W : ℂ) * (u⁻¹ * v)) (hcard c) (hIc c)).trans ?_
  linear_combination ((Nat.card (Bridge.stab (Bridge.ratF D.sp.X') J ((R.B.R t).pres.y c)) : ℂ)⁻¹) * (hS c).2

end GlobalTheory.Mem.SchurW
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.LevToQ
end GlobalTheory.LevToQ

namespace GlobalTheory.LevToQ
theorem units_map_inv_val {K : Type} [Field K] (σ : K →+* ℂ) (u : Kˣ) :
    (((Units.map σ.toMonoidHom u)⁻¹ : ℂˣ) : ℂ) = σ ((u⁻¹ : Kˣ) : K) := by
  simp
end GlobalTheory.LevToQ



theorem GlobalTheory.LevToQ.levtoq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.models_cV → R.grp_red_L → ∀ (i : Fin D.R.m) (t : T) (Φ : Bridge.Gf (Vc D i) → (R.cV i).W), (R.cV i).ext Φ ∈ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) → ∀ (κ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q) (hu : (R.B.L i t).act_tie.red κ ∈ F.P0) (h : Bridge.Gf (Vc D i)), Φ (h * κ) = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) • D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) • Φ h := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hcV hred i t Φ hΦ κ hu h
  have hl := GlobalTheory.DefiniteMult.exists_fin_lift (Vc D i) (κ : Bridge.Gf (Vc D i))
  obtain ⟨k, hkG, hk⟩ := hl
  have hl' := GlobalTheory.DefiniteMult.exists_fin_lift (Vc D i) h
  obtain ⟨g, hgG, hg⟩ := hl'
  have hfk : finE (Vc D i) k = Formalism.UG.bc (swapAE D) (((κ : Bridge.Gf (Vc D i)) : GL _ _)) := by
    rw [finE_eq, ← hk]
    rfl
  have hκQ := κ.2
  have hpar : finE (Vc D i) k ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := by
    rw [hfk]; exact hκQ.1
  have hrt : Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) = R.eG ((R.B.L i t).act_tie.red κ) := by
    exact (congrArg (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t)) hfk).trans (hred i t κ).symm
  have hmem : Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) ∈ (R.levR F false).conj.H := by
    rw [hrt]
    show R.eG.symm (R.eG ((R.B.L i t).act_tie.red κ)) ∈ F.P0
    simpa using hu
  have hkS : k ∈ levS (Vc D i) (R.βV i) (datVP R i t (R.levR F false)) :=
    ⟨hkG, hpar, hmem⟩
  have hlaw := hΦ k hkS g
  have e1 : (R.cV i).ext Φ (g * k) = Φ (h * κ) := by
    show (R.cV i).ρ (g * k)⁻¹ (Φ ((finHom (Vc D i)).rangeRestrict (g * k))) = _
    have hrr : (finHom (Vc D i)).rangeRestrict (g * k) = h * (κ : Bridge.Gf (Vc D i)) := by
      rw [map_mul, hg]
      exact congrArg (h * ·) hk
    exact (LinearMap.congr_fun ((hcV i).1 _ ((GfC _).inv_mem ((GfC _).mul_mem hgG hkG))) _).trans
      ((Module.End.one_apply _).trans (congrArg Φ hrr))
  have e2 : (R.cV i).ext Φ g = Φ h := by
    show (R.cV i).ρ g⁻¹ (Φ ((finHom (Vc D i)).rangeRestrict g)) = _
    exact (LinearMap.congr_fun ((hcV i).1 _ ((GfC _).inv_mem hgG)) _).trans
      ((Module.End.one_apply _).trans (congrArg Φ hg))
  have hchi : levChi (Vc D i) (R.βV i) (datVP R i t (R.levR F false)) k =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) *
        D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
    have hw : (⟨R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)), hmem⟩ : F.P0) = ⟨_, hu⟩ :=
      Subtype.ext ((congrArg R.eG.symm hrt).trans (R.eG.symm_apply_apply _))
    have c1 : levChi (Vc D i) (R.βV i) (datVP R i t (R.levR F false)) k =
        ((Formalism.L2.DIV.levFn (R.βV i) (withP (R.datVt i t) (R.levR F false).conj) (finE (Vc D i) k) : ℂˣ) : ℂ) := rfl
    have c2 := levFn_withP (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (R.levR F false).conj (finE (Vc D i) k)
    have c3 := Formalism.L2.DIV.extendOne_of_mem (R.levR F false).conj.chi hmem
    have c4 : Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) k) = (levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ :=
      congrArg (Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t))) hfk
    have c5 : (((R.levR F false).conj.chi ⟨_, hmem⟩ : ℂˣ) : ℂ) =
        D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
      have d1 : (R.levR F false).conj.chi ⟨_, hmem⟩ = ((R.levR F false).chi ⟨_, hmem⟩)⁻¹ := rfl
      have d2 : (R.levR F false).chi ⟨_, hmem⟩ = Units.map D.what₂.embLL.toMonoidHom
          (F.ψ0 ⟨R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)), hmem⟩) := rfl
      have d3 : (((Units.map D.what₂.embLL.toMonoidHom (F.ψ0 ⟨_, hu⟩))⁻¹ : ℂˣ) : ℂ) =
          D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) :=
        (GlobalTheory.LevToQ.units_map_inv_val D.what₂.embLL (F.ψ0 ⟨_, hu⟩)).trans
          (congrArg (fun u : D.what₂.LLˣ => D.what₂.embLL (u : D.what₂.LL)) (MonoidHom.inv_apply F.ψ0 _).symm)
      exact (congrArg (fun u : ℂˣ => (u : ℂ)) (d1.trans (congrArg (·⁻¹) (d2.trans (congrArg (Units.map D.what₂.embLL.toMonoidHom) (congrArg F.ψ0 hw)))))).trans d3
    have c6 := congrArg (fun u : ℂˣ => (u : ℂ)) (c2.trans (congrArg₂ (· * ·) c3 c4))
    refine c1.trans (c6.trans ?_)
    exact (Units.val_mul _ _).trans ((congrArg (· * (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ)) c5).trans (mul_comm _ _))
  calc Φ (h * κ) = (R.cV i).ext Φ (g * k) := e1.symm
    _ = levChi (Vc D i) (R.βV i) (datVP R i t (R.levR F false)) k • (R.cV i).ext Φ g := hlaw
    _ = levChi (Vc D i) (R.βV i) (datVP R i t (R.levR F false)) k • Φ h := congrArg _ e2
    _ = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) *
        D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Φ h := congrArg (· • Φ h) hchi
    _ = _ := mul_smul _ _ _
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.MultLevelP

theorem multT_mono {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (hJ : J' ⊆ J) (hχ : ∀ k ∈ J', χ' k = χ k) :
    MultT θ M J χ ≤ MultT θ M J' χ' := by
  unfold MultT Mult
  exact Submodule.map_mono (Submodule.span_mono fun T hT =>
    ⟨hT.aut, hT.cusp, fun v k hk g => by rw [hχ k hk]; exact hT.lev v k (hJ hk) g, hT.equiv, hT.cont⟩)

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}

theorem levS_flag1_sub (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) : levS V β (flag1L L) ⊆ levS V β L := by
  rintro κ ⟨hκ, hp, hr⟩
  have e : Formalism.L2.DIV.rTup β L (finE V κ) = 1 := Subgroup.mem_bot.1 hr
  refine ⟨hκ, hp, ?_⟩
  show Formalism.L2.DIV.rTup β L (finE V κ) ∈ L.P.H
  rw [e]
  exact L.P.H.one_mem

theorem levChi_flag1 (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {κ : GA D V} (hκ : κ ∈ levS V β (flag1L L)) :
    levChi V β (flag1L L) κ = levChi V β L κ := by
  obtain ⟨-, -, hr⟩ := hκ
  have e : Formalism.L2.DIV.rTup β L (finE V κ) = 1 := Subgroup.mem_bot.1 hr
  have h1 : Formalism.L2.DIV.rTup β L (finE V κ) ∈ L.P.H := e ▸ L.P.H.one_mem
  have h := levFn_withP (β := β) (L := L) L.P (finE V κ)
  change Formalism.L2.DIV.levFn β L (finE V κ) = _ at h
  have e1 : (⟨_, h1⟩ : L.P.H) = 1 := Subtype.ext e
  unfold levChi
  rw [levFn_flag1, h, Formalism.L2.DIV.extendOne_of_mem _ h1, e1, map_one, one_mul]

end GlobalTheory.MultLevelP



theorem GlobalTheory.MultLevelP.exists_form_of_mult : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (Tm : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)), Tm ∈ Mult.MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) → ∃ Fn ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ, (∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), Fn (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Fn h) ∧ R.cX.toMap R.prX Fn = Tm := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB b t Tm hTm
  have hθ := hB.models.inf
  have hc := hB.models.cX
  have hpr := hB.models.prX
  have hp := GlobalTheory.DefiniteMult.allPlus_parB (V := D.sp.X') _ (Nat.sub_le _ _) R.MX
  have hT0 : Tm ∈ MultT R.θ R.MX (levS _ R.βX (flag1L (datXP R t (R.levR F b))))
      (levChi _ R.βX (flag1L (datXP R t (R.levR F b)))) :=
    GlobalTheory.MultLevelP.multT_mono R.θ R.MX (GlobalTheory.MultLevelP.levS_flag1_sub (β := R.βX) (datXP R t (R.levR F b)))
      (fun k hk => GlobalTheory.MultLevelP.levChi_flag1 (datXP R t (R.levR F b)) hk) hTm
  have e : flag1L (datXP R t (R.levR F b)) = flag1L (R.datXt t) := rfl
  have hT1 : Tm ∈ MultT R.θ R.MX (levS _ R.βX (flag1L (R.datXt t))) (levChi _ R.βX (flag1L (R.datXt t))) := by
    rw [← e]; exact hT0
  have X := GlobalTheory.DefiniteMult.exists_form (D := D) (V := D.sp.X') (M := R.MX) (θ := R.θ) (c := R.cX) (pr := R.prX) (β := R.βX) (L := R.datXt t) hθ hp hc hpr hT1
  obtain ⟨Fn, hFn, hmap⟩ := X
  refine ⟨Fn, hFn, ?_, hmap⟩
  rintro ⟨q, hqQ⟩ hq h
  obtain ⟨κ, hκκ⟩ := GlobalTheory.DefiniteMult.exists_fin_lift (D := D) D.sp.X' q
  have hκ := hκκ.1
  have hκq := hκκ.2
  obtain ⟨g, hg⟩ := (finHom D.sp.X').rangeRestrict_surjective h
  subst hg
  have hqQ' : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q := by rw [hκq]; exact hqQ
  have eQ : (⟨_, hqQ'⟩ : (levEnv D.sp.X' R.βX (R.datXt t)).Q) = ⟨q, hqQ⟩ := Subtype.ext hκq
  have hq' : (R.B.R t).act_tie.red ⟨_, hqQ'⟩ ∈ (F.lvl b).P :=
    (congrArg (fun x => (R.B.R t).act_tie.red x ∈ (F.lvl b).P) eQ).mpr hq
  have key : ∀ (x y : (levEnv D.sp.X' R.βX (R.datXt t)).Q), x = y → ∀ (hx : (R.B.R t).act_tie.red x ∈ (F.lvl b).P)
      (hy : (R.B.R t).act_tie.red y ∈ (F.lvl b).P),
      ((levEnv D.sp.X' R.βX (R.datXt t)).ch x : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hx⟩ : D.what₂.LLˣ) : D.what₂.LL) =
        ((levEnv D.sp.X' R.βX (R.datXt t)).ch y : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hy⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
    rintro x _ rfl hx hy
    rfl
  have hbr := GlobalTheory.T.mem_level_group_face_level_iff_flag_group D G Pl0 T A Ks R F hB.grp.red_R b t κ hκ
  have hκS : κ ∈ levS _ R.βX (datXP R t (R.levR F b)) := hbr.1.2 ⟨hqQ', hq'⟩
  have hχ := hbr.2 hqQ' hq'
  have hM := (mem_multT _ _ _ _ _).1 hTm
  have hlev : ∀ x g', Tm x (g' * κ) = levChi _ R.βX (datXP R t (R.levR F b)) κ * Tm x g' := by
    intro x g'
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have := (GlobalTheory.mult_value_left_cont_level R.θ R.MX _ _ _ hM v).2.2 κ hκS g'
      rw [map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]
      exact congrArg (r * ·) this
    | add x y hx hy => rw [map_add (f := _), Pi.add_apply, Pi.add_apply, hx, hy, mul_add]
  have hb := (GlobalTheory.DefiniteMult.pair_bijective hθ hp hc hpr).1
  have hext : R.cX.ext Fn (g * κ) = levChi _ R.βX (datXP R t (R.levR F b)) κ • R.cX.ext Fn g := by
    refine hb (LinearMap.ext fun x => ?_)
    have a1 : R.prX (R.cX.ext Fn (g * κ)) x = Tm x (g * κ) := congrFun (LinearMap.congr_fun hmap x) (g * κ)
    have a2 : R.prX (R.cX.ext Fn g) x = Tm x g := congrFun (LinearMap.congr_fun hmap x) g
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, a1, a2, hlev]
  change R.cX.ρ (g * κ)⁻¹ (Fn ((finHom D.sp.X').rangeRestrict (g * κ))) =
    levChi _ R.βX (datXP R t (R.levR F b)) κ • R.cX.ρ g⁻¹ (Fn ((finHom D.sp.X').rangeRestrict g)) at hext
  rw [GlobalTheory.DefiniteMult.rho_right_inv R.cX.ρ g (hc.1 _ (inv_mem hκ)), map_mul] at hext
  have inj : Function.Injective (R.cX.ρ g⁻¹) := fun a a' haa => by
    have := congrArg (R.cX.ρ g) haa
    rwa [GlobalTheory.DefiniteEnd.rho_inv_cancel, GlobalTheory.DefiniteEnd.rho_inv_cancel] at this
  calc Fn ((finHom D.sp.X').rangeRestrict g * q) = Fn ((finHom D.sp.X').rangeRestrict g * (finHom D.sp.X').rangeRestrict κ) :=
      congrArg (fun x => Fn ((finHom D.sp.X').rangeRestrict g * x)) hκq.symm
    _ = levChi _ R.βX (datXP R t (R.levR F b)) κ • Fn ((finHom D.sp.X').rangeRestrict g) :=
      inj (hext.trans ((R.cX.ρ g⁻¹).map_smul _ _).symm)
    _ = _ := congrArg (fun c : ℂ => c • Fn ((finHom D.sp.X').rangeRestrict g)) (hχ.trans (key _ _ eQ hq' hq))

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.DefiniteMult

theorem toMap_mem_levP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (Fn : Bridge.Gf D.sp.X' → R.cX.W), Fn ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ → (∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), Fn (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Fn h) → R.cX.toMap R.prX Fn ∈ Mult.MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB b t Fn hFn hP
  have h := GlobalTheory.DefiniteEnd.isMultMap_toMap hB.models.inf D.sp.X'_sig (GlobalTheory.DefiniteEnd.end_definite D) R.MX hB.models.cX
    hB.models.prX hFn
  refine (mem_multT R.θ R.MX _ _ _).2 (Submodule.subset_span ⟨h.aut, h.cusp, fun v k hk g => ?_, h.equiv, h.cont⟩)
  have hkC : k ∈ GfC D.sp.X' := hk.1
  obtain ⟨hiff, hchi⟩ := GlobalTheory.T.mem_level_group_face_level_iff_flag_group D G Pl0 T A Ks R F hB.grp.red_R b t k hkC
  have hh := hiff.1 hk
  obtain ⟨hq, hp⟩ := hh
  have hc := hchi hq hp
  have hd := hP ⟨_, hq⟩ hp ((finHom D.sp.X').rangeRestrict g)
  have e : Fn ((finHom D.sp.X').rangeRestrict (g * k)) =
      levChi _ R.βX (datXP R t (R.levR F b)) k • Fn ((finHom D.sp.X').rangeRestrict g) :=
    (congrArg Fn (map_mul _ g k)).trans (hd.trans (congrArg (· • Fn ((finHom D.sp.X').rangeRestrict g)) hc.symm))
  have e2 : R.cX.ext Fn (g * k) = levChi _ R.βX (datXP R t (R.levR F b)) k • R.cX.ext Fn g :=
    ((congrArg (R.cX.ρ (g * k)⁻¹) e).trans
      (LinearMap.congr_fun (rho_right_inv R.cX.ρ g (hB.models.cX.1 _ (inv_mem hkC))) _)).trans (map_smul _ _ _)
  exact (congrArg (fun w => R.prX w (PiTensorProduct.tprod ℂ v)) e2).trans (LinearMap.congr_fun (map_smul R.prX _ _) _)

end GlobalTheory.DefiniteMult

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalSymplecticPoints_self_annihilator : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (x : WO S T), (∀ γ ∈ ratL T S, ψ (symplO S T x γ) = 1) ↔ x ∈ ratL T S := by
  first | exact @GlobalTheory.RatAnnih.ratL_annihilator | exact GlobalTheory.RatAnnih.ratL_annihilator | (intros; apply GlobalTheory.RatAnnih.ratL_annihilator <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.definiteThetaIntegral_invariant_real_translate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (s : WO V W → ℂ) (F : GA D W → ℂ), IsWeilDatumO ψ V W χS χT ω → (∀ τ, (gramAt D W τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → IsThetaFunO ψ V W s → Continuous F → (∀ γ ∈ GQ W, ∀ h, F (γ * h) = F h) → ∀ k ∈ GinfC W, Lift.liftInt ν 𝓕 (thetaKO ω) (ω (1, k) s) (rTr W k F) = Lift.liftInt ν 𝓕 (thetaKO ω) s F := by
  first | exact @GlobalTheory.LiftShift.liftInt_shift | exact GlobalTheory.LiftShift.liftInt_shift | (intros; apply GlobalTheory.LiftShift.liftInt_shift <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelForm_complex_polynomial_identity : ∀ (D : D7) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m)
    (hU : UnfIsAll (O u μ) i) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (v : ValQ O u μ i) (v' : ValQ O u μ (i + 1))
    (h : evC O u μ (i + 1) v' = (D.chTw u μ).Kmap i c c' (evC O u μ i v)), MvPolynomial.map D.what₂.embLL (secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL) =
      MvPolynomial.C (((GL3Theta.rhoOf D (O u μ).mt i ((O u μ).dt i c) : ℂˣ) : ℂ) * ((GL3Theta.rhoOf' D (O u μ).mt i ((O u μ).dt (i + 1) c') : ℂˣ) : ℂ)) *
        jetMap (jetC (O u μ).dgen ((O u μ).Th i c c')) (fun _ => 0)
          (MvPolynomial.map D.what₂.embLL (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL))) := by
  first | exact @GlobalTheory.Mem.KerForm.complex_kform | exact GlobalTheory.Mem.KerForm.complex_kform | (intros; apply GlobalTheory.Mem.KerForm.complex_kform <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.support_degree_eq_of_mem_weightPolynomials : ∀ {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (ν : ι → Fin n → ℕ)
    (Q : MvPolynomial (ι × Fin n × Fin n) K) (hQ : Q ∈ WtPol K ν), ∀ e ∈ Q.support, ∀ τ, ∑ α, ∑ s, e (τ, α, s) = ∑ r, ν τ r := by
  first | exact @GlobalTheory.Mem.WtHomog.deg_eq_of_mem_wtPol | exact GlobalTheory.Mem.WtHomog.deg_eq_of_mem_wtPol | (intros; apply GlobalTheory.Mem.WtHomog.deg_eq_of_mem_wtPol <;> assumption)
end
