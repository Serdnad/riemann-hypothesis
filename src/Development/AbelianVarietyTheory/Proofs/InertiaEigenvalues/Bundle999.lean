module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle829
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle968
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle890
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle998
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle949
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle492
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle944
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConstTwistedSumFockVectorsPrincipalDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle940
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle836
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle969
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle938
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesVecFlatEqSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle971
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle902
public import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false



noncomputable section

namespace GlobalTheory.SeriesTie.NormRat

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}

theorem fixBase_of_fix (hRF : GlobalTheory.NT.RayField) {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F}
    {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {F : Face D A3.A}
    {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
    (hT : LawsJ T) (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F) (hfw : Nonempty (FWTie T Rl.toRealDat κ v₀))
    (hti : TieIn T Rl.toRealDat κ v₀) (hgal : IsGalois ℚ D.LL0) (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hroots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange)
    (j : Fin D.R.m) (τ : ℂ ≃+* ℂ) (hτ : ∀ z ∈ (embLL0 D).fieldRange, τ z = z) :
    FixBase T Rl.toRealDat j τ :=
  GlobalTheory.T.fixes_untwistedTupleData_of_fixes_smallField D Γ Pl0 I0 T0 A3 hRF T Rl cG S YS F κ v₀ hT hcore hfw hti hgal hval hray hroots j τ hτ

theorem exists_extC {G : Type} [Group G] [Fintype G] {T1 : Type} {A : FamIn D.what₂.LL G Pl0 T1 D.R.m} {T : CoreJ D}
    [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {j : Fin D.R.m} {Tp : Type} {tup : Tp → T1}
    (O : OMDat T.toCore R j Tp tup) : ∃ c : VsV D j ℂ →ₗ[ℂ] (R.cV j).W, ExtC R j (inC O.c') O.c0' c :=
  GlobalTheory.T.exists_complexLinear_extension_coefficientMap D G Pl0 T1 A T R j Tp tup O

theorem exists_ser_ne_zero {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {F : Face D A3.A}
    {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
    (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F) (hfw : Nonempty (FWTie T Rl.toRealDat κ v₀)) (hio : IoExt Rl.toRealDat)
    (j : Fin D.R.m) (hpins : OMPins T Rl.toRealDat κ v₀ O j) (hrow0 : OneMapRow0 T Rl.toRealDat κ v₀ O j)
    (hcusp : T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n ≠ ⊥)
    (c : VsV D j ℂ →ₗ[ℂ] (Rl.cV j).W) (hc : ExtC Rl.toRealDat j (inC (O j).c') (O j).c0' c)
    (u : ∀ ρ, lowT (Rl.MW j (sg0 D A3.A)) ρ) (hu : ∀ ρ, (u ρ : (Rl.MW j (sg0 D A3.A)).sm ρ) = v₀ j _ ρ) :
    ∃ (v : VsV D j D.what₂.LL) (x : VsV D j ℂ) (h : GA D (Vc D j)) (g : GA D (Wc D j)),
      (∀ m, ∃ q : ℚ, AddMonoidAlgebra.coeff (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) m = (q : D.what₂.LL)) ∧
      (x : Pol ℂ D.what₂.Tau (Vc D j).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) ∧
      h ∈ GfC (Vc D j) ∧ ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (c x) g ≠ 0 :=
  GlobalTheory.T.exists_thetaSeries_rational_vector_ne_zero_of_cuspForms D Γ Pl0 I0 T0 A3 T Rl F κ v₀ O hnV hcore hfw hio j hpins hrow0 hcusp c hc u hu

theorem expands_of_isRatPhase (hRF : GlobalTheory.NT.RayField) {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL]
    {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
    {F : Face D A3.A} {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)}
    {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
    (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (hT : LawsJ T) (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F)
    (hfw : Nonempty (FWTie T Rl.toRealDat κ v₀)) (hti : TieIn T Rl.toRealDat κ v₀) (hio : IoExt Rl.toRealDat)
    (hQ : QGuard Rl.toRealDat) (hgal : IsGalois ℚ D.LL0) (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hroots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange)
    {j : Fin D.R.m} (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j) (hpins : OMPins T Rl.toRealDat κ v₀ O j)
    (hfp : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV)
    {gramR c0R c0L} (hft : Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) Rl.Q (labLL D)
      (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L)
    (hbc : CoefficientBaseChange Rl.toRealDat j (O j).jL (inC (O j).c') (c0L j) (O j).c0')
    {u : ∀ ρ, lowT (Rl.MW j (sg0 D A3.A)) ρ} (hu : ∀ ρ, (u ρ : (Rl.MW j (sg0 D A3.A)).sm ρ) = v₀ j _ ρ) {ph₀ : ℂ}
    (hph : IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph₀)
    (c : VsV D j ℂ →ₗ[ℂ] (Rl.cV j).W) (hc : ExtC Rl.toRealDat j (inC (O j).c') (O j).c0' c)
    (v : VsV D j D.what₂.LL)
    (hv : ∀ m, ∃ q : ℚ, AddMonoidAlgebra.coeff (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) m = (q : D.what₂.LL))
    (x : VsV D j ℂ)
    (hx : (x : Pol ℂ D.what₂.Tau (Vc D j).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank))
    (h : GA D (Vc D j)) (hh : h ∈ GfC (Vc D j)) :
    ∃ (n : ℕ) (e : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n),
      Expands (O j) (κ j) (fun g => ph₀ * ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (c x) g) e f ∧
        ∀ k, e k ∈ (embLL0 D).fieldRange :=
  GlobalTheory.T.rationalPhaseThetaSeries_expands_cuspForms_smallField D Γ Pl0 I0 T0 A3 hRF T Rl cG S YS F κ v₀ O hnV hT hcore hfw hti hio hQ hgal hval hray hroots j hV hpins hfp gramR c0R c0L hft hbc u hu ph₀ hph c hc v hv x hx h hh

theorem fixed_of_expands {G : Type} [Group G] [Fintype G] {T1 : Type} {A : FamIn D.what₂.LL G Pl0 T1 D.R.m} {T : CoreJ D}
    [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {j : Fin D.R.m} {Tp : Type} {tup : Tp → T1}
    (O : OMDat T.toCore R j Tp tup) (κ : WeightFamilies.Wt D ((j : ℕ) + 1)) (τ : ℂ ≃+* ℂ) {Φ Ψ Ψ' : GA D (Wc D j) → ℂ} {a : ℂ}
    (hc : ConjFun O κ τ 1 Ψ Ψ') (hΨ : ∀ g, Ψ g = a * Φ g) (hΨ' : ∀ g, Ψ' g = a * Φ g) {n : ℕ} {e : Fin n → ℂ}
    {f : Fin n → T.toCore.cuspA ((j : ℕ) + 1) (wtA κ) κ.n} (he : Expands O κ Φ e f) (hτ : ∀ k, τ (e k) = e k)
    {g₀ : GA D (Wc D j)} (hg₀ : Φ g₀ ≠ 0) : τ a = a := by
  have h1 : Expands O κ Ψ (fun k => a * e k) f := by
    intro g
    rw [hΨ g, he g, Finset.mul_sum]
    simp only [mul_assoc]
  have h2 := hc.2 _ _ _ h1 g₀
  have h3 : a * Φ g₀ = τ a * Φ g₀ := by
    rw [← hΨ' g₀, h2, he g₀, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show 1 * τ (a * e k) * _ = _
    rw [one_mul, map_mul, hτ, mul_assoc]
  exact (mul_right_cancel₀ hg₀ h3).symm

theorem conjVec_self_of_rat (j : Fin D.R.m) (τ : ℂ ≃+* ℂ) (v : VsV D j D.what₂.LL)
    (hv : ∀ m, ∃ q : ℚ, AddMonoidAlgebra.coeff (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) m = (q : D.what₂.LL))
    (x : VsV D j ℂ)
    (hx : (x : Pol ℂ D.what₂.Tau (Vc D j).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)) :
    ConjVec j τ x x := by
  unfold ConjVec
  rw [hx]
  ext m
  obtain ⟨q, hq⟩ := hv m
  simp [MvPolynomial.coeff_map, hq]

end GlobalTheory.SeriesTie.NormRat
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



noncomputable section

namespace GlobalTheory.LiftClassSumTwist

open GlobalTheory.FlatVecSum GlobalTheory.LiftClassSumPrinc

theorem unitOff_inv {N : ℕ} {u : ℂ} (hu : UnitOff N u) : UnitOff N u⁻¹ := by
  obtain ⟨h0, n, h1, h2⟩ := hu
  exact ⟨inv_ne_zero h0, n, h2, by rwa [inv_inv]⟩

section General

variable {D : D7} {S T : HSp D}


open GlobalTheory.LevTransl in
theorem sum_om_fock {B : Base S T} (hB : B.Good) (hS : S.SigOK) {ψ : Twist D Circle} (hψ : ψ.Good) (hQ : B.admitted ψ.Q)
    {ω : PairRep S T} (hω : B.IsWeil ψ.chi ω) {F : Finset (Bridge.Gf S)} (hF : ∀ u ∈ F, u ∈ B.levJ ψ)
    (hU : ∀ κ ∈ B.levJ ψ, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ (princ B).levJ ψ) (P : PolF D T.rank S.rank) :
    ∑ u ∈ F.attach, ((B.levLam ψ ⟨u.1, hF u.1 u.2⟩ : ℂˣ) : ℂ) •
        ω ((((GlobalTheory.ClassRegroup.finEquiv S).symm u.1 : GfC S) : GA D S), 1) (B.F.fock ((princ B).vecFlat ψ) P) =
      (1 : ℂ) • B.F.fock (B.vecFlat ψ) P := by
  have hB0 := princ_good hB
  have hQ0 : (princ B).admitted ψ.Q := hQ
  have hf0 : IsThetaFunO B.F.ψ S T ((princ B).vecFlat ψ) :=
    GlobalTheory.GalLift.Vec.theta_of_thetaAt hB0.frame.vac.1 hB0.frame.vac.2.inf (Base.isThetaAt_vecAt hB0 hQ0 _) hB0.frame.vac.2.theta
  let g : {x // x ∈ F} → GA D S := fun u => (((GlobalTheory.ClassRegroup.finEquiv S).symm u.1 : GfC S) : GA D S)
  have hg : ∀ u, g u ∈ GfC S := fun u => ((GlobalTheory.ClassRegroup.finEquiv S).symm u.1).2
  have hk : ∀ u, Lev.finE S (g u) ∈ lev D.sp.cm S.gram B.F.βS (B.levS ψ) := fun u => (mem_levJ_iff B ψ u.1).1 (hF u.1 u.2)
  have inj : ∀ u v, rTup B.F.βS (B.levS ψ) (Lev.finE S (g u)) = rTup B.F.βS (B.levS ψ) (Lev.finE S (g v)) → u = v :=
    fun u v h => Subtype.ext (tup_inj hF hU u.2 v.2 h)
  have surj : ∀ p ∈ B.G.P.H, ∃ u, rTup B.F.βS (B.levS ψ) (Lev.finE S (g u)) = p := fun p hp => by
    obtain ⟨u, hu, e⟩ := tup_surj hF hU hB hQ hp
    exact ⟨⟨u, hu⟩, e⟩
  have hv := vec_sum hB hS hψ hQ hω g hg hk inj surj
  have hth : ∀ u ∈ (Finset.univ : Finset {x // x ∈ F}), IsThetaFunO B.F.ψ S T (ω (g u, 1) ((princ B).vecFlat ψ)) :=
    fun u _ => hω.om_pres _ _ hf0
  rw [one_smul, ← Finset.univ_eq_attach]
  calc _ = ∑ u, ((levFn B.F.βS (B.levS ψ) (Lev.finE S (g u)) : ℂˣ) : ℂ) •
        B.F.fock (ω (g u, 1) ((princ B).vecFlat ψ)) P :=
        Finset.sum_congr rfl fun u _ => by
          rw [levLam_eq B ψ u.1 (hF u.1 u.2)]
          exact congrArg₂ (· • ·) rfl (om_fock hB hω (hg u) hf0 P)
    _ = B.F.fock (∑ u, ((levFn B.F.βS (B.levS ψ) (Lev.finE S (g u)) : ℂˣ) : ℂ) •
        ω (g u, 1) ((princ B).vecFlat ψ)) P :=
        (GlobalTheory.SpecFac.pureTensorO_sum hB.frame.vac.1 hB.frame.vac.2.inf _ _ _ _ _ _ _ hth P).symm
    _ = _ := by rw [hv]


open GlobalTheory.ClassSumPrinc in
theorem classSum_princ {B : Base S T} (hB : B.Good) (hS : S.SigOK) {ψ : Twist D Circle} (hψ : ψ.Good) (hQ : B.admitted ψ.Q)
    {ω : PairRep S T} (hω : B.IsWeil ψ.chi ω) {m : ℕ} {h₀ : Fin m → GA D S} (hC₀ : IsClassSystem S ((princ B).levJ ψ) h₀)
    {I : Type} [Fintype I] {h : I → GA D S} (hC : IsClassSystem S (B.levJ ψ) h) {F : Bridge.Gf S → PolF D T.rank S.rank}
    (hFm : F ∈ B.formsC ψ) : (princ B).classSum ω ψ h₀ F = B.classSum ω ψ h F := by
  obtain ⟨hle, -⟩ := GlobalTheory.T.principalLevel_le_level_characters_agree B hB ψ hQ
  obtain ⟨Fs, hF, hFu⟩ := GlobalTheory.T.finite_coset_representatives_level B hB ψ hQ
  have hκ := sum_om_fock hB hS hψ hQ hω hF hFu
  have hinv := GlobalTheory.T.classSumTerms_invariant_principalLevel B hB hS ψ hψ hQ ω hω F hFm
  have hlaw := ((B.mem_formsC).1 hFm).2
  funext g
  rw [Base.classSum_apply, Base.classSum_apply, Finset.sum_apply, Finset.sum_apply]
  have key := GlobalTheory.T.classSum_regroup_finerLevel_cosets (Bridge.ratF S) (ratF_injective S) hle hF hFu (fun i => finPt S (h₀ i)) hC₀.reps
    (fun i => finPt S (h i)) hC.reps
    (fun y => series B.F ω ((princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g)
    (fun γ y => (hinv g).1 γ y) (fun k hk y => (hinv g).2 k hk y)
  simp only [symm_finPt S (hC₀.fin _), inner_sum B ψ ω hF hκ hlaw (hC.fin _), one_mul] at key
  simp only [Pi.smul_apply, smul_eq_mul, show (princ B).F = B.F from rfl]
  exact key

theorem classSum_weil {B : Base S T} (hB : B.Good) {ψ : Twist D Circle} (hQ : B.admitted ψ.Q) {ω ω' : PairRep S T}
    (hω : B.IsWeil ψ.chi ω) (hω' : B.IsWeil ψ.chi ω') {I : Type} [Fintype I] (h : I → GA D S)
    (F : Bridge.Gf S → PolF D T.rank S.rank) : B.classSum ω ψ h F = B.classSum ω' ψ h F := by
  rw [Base.classSum_apply, Base.classSum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [GlobalTheory.ConjGen.series_weil hB hQ hω hω']

theorem transl_mem_formsC {B : Base S T} {ψ : Twist D Circle} {z : Bridge.Gf S} (hz : z ∈ Subgroup.center (Bridge.Gf S))
    {F : Bridge.Gf S → PolF D T.rank S.rank} (hF : F ∈ B.formsC ψ) : (fun h => F (h * z)) ∈ B.formsC ψ := by
  obtain ⟨h1, h2⟩ := B.mem_formsC.1 hF
  refine B.mem_formsC.2 ⟨fun h => h1 _, fun γ h k => ?_⟩
  have e : Bridge.ratF S γ * h * (k : Bridge.Gf S) * z = Bridge.ratF S γ * (h * z) * (k : Bridge.Gf S) := by
    rw [mul_assoc _ (k : Bridge.Gf S) z, Subgroup.mem_center_iff.1 hz (k : Bridge.Gf S)]
    simp only [mul_assoc]
  show F (Bridge.ratF S γ * h * (k : Bridge.Gf S) * z) = _
  rw [e]
  exact h2 γ (h * z) k

end General


open Classical in
theorem thF_eq_princ {D : D7} (X : RealSide D) {j : Fin D.R.m} {B : Base (Vc D j) (Wc D j)} (hB : BaseOf X.R.toRealDat j B)
    {ψ : Twist D Circle} {t : X.T} (htup : IsTupOf X.R.toRealDat B ψ t) {c0 : ℂ} (hc0 : c0 ≠ 0) {z' : GA D (Vc D j)}
    (hz' : z' ∈ GfC (Vc D j)) (hzc : finPt (Vc D j) z' ∈ Subgroup.center (Bridge.Gf (Vc D j)))
    (hflat : c0 • X.R.ωP j t (z', 1) (X.R.vP j t) = (princ B).vecFlat ψ)
    {m : ℕ} {h₀ : Fin m → GA D (Vc D j)} (hcs : IsClassSystem (Vc D j) ((princ B).levJ ψ) h₀)
    (u : ∀ ρ, lowT (X.R.MW j (sg0 D X.A3.A)) ρ) (y : (X.R.HV j t).H) :
    X.R.thF j t y (fun ρ => (u ρ : ↥((X.R.MW j (sg0 D X.A3.A)).sm ρ))) =
      c0⁻¹ • (princ B).classSum (X.R.ωP j t) ψ h₀
        (fun h => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * finPt (Vc D j) z'))) := by
  have hC : GlobalTheory.Hk3.Core X.R.toRealDat X.F.lv2 :=
    ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.chain, X.char.thP⟩
  have hβ : (princ B).F.βS = X.R.βV j := hB.βS
  have hrW : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
  have hrV : (Vc D j).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have hJ : (princ B).levJ ψ = (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J := by
    unfold Base.levJ
    rw [hβ, lev_eq_of _ _ _ ((princ B).levS ψ)
      (Formalism.IndefR.Lev.flag1L (X.R.datVt j t)) (by show (Wc D j).rank = D.R.r; exact hrW)
      (by show (Vc D j).rank - (Wc D j).rank = D.R.t; omega) (by show B.G.Pg = X.R.Pg; exact hB.Pg)
      htup.2.symm rfl rfl]
    rfl
  have hrel : ((princ B).levJ ψ).relIndex (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J = 1 :=
    Subgroup.relIndex_eq_one.2 hJ.ge
  have hfin1 : ∀ k, Formalism.IndefR.FWT.fin (Vc D j) (h₀ k * z') = finPt (Vc D j) (h₀ k) * Formalism.IndefR.FWT.fin (Vc D j) z' :=
    fun k => map_mul _ _ _
  have hy : Bridge.IsReps (Bridge.ratF (Vc D j)) ((princ B).levJ ψ) (fun k => Formalism.IndefR.FWT.fin (Vc D j) (h₀ k * z')) := by
    rw [show (fun k => Formalism.IndefR.FWT.fin (Vc D j) (h₀ k * z')) = fun k => finPt (Vc D j) (h₀ k) * Formalism.IndefR.FWT.fin (Vc D j) z'
      from funext hfin1]
    exact isReps_mul_central _ _ _ hzc hcs.reps
  have hh : ∀ k, h₀ k * z' ∈ GfC (Vc D j) := fun k => mul_mem (hcs.fin k) hz'
  have hθ : IsInfFam X.R.θ := hC.models.inf
  have hvθ : IsThetaFunO X.R.ψ (Vc D j) (Wc D j) (X.R.vP j t) :=
    GlobalTheory.AdTh.MinorWeight.pure_one _ (X.R.vP j t) ▸ hC.thP.pt_theta j t 1
  funext g
  refine (hC.thP.thF j t).elim fun thP hPF => ?_
  have hx : (X.R.HV j t).e y ∈ Bridge.AdForms (Bridge.ratF (Vc D j)) (X.R.cV j).coef.ρ
      (levEnv _ (X.R.βV j) (X.R.datVt j t)).J (levEnv _ (X.R.βV j) (X.R.datVt j t)).χ :=
    (hC.models.HV j t).2.1.le (LinearMap.mem_range_self _ y)
  have hfin : ∀ k ∈ GfC (Vc D j), ∀ hk : Formalism.IndefR.FWT.fin (Vc D j) k ∈ Formalism.IndefR.FWT.levJ X.R.toRealDat j t, ∀ P,
      X.R.ωP j t (k, 1) (X.R.ptP j t P) =
      (((levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).χ ⟨Formalism.IndefR.FWT.fin (Vc D j) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • X.R.ptP j t P :=
    fun k hk hk' =>
    GlobalTheory.FiniteFock.om_pureTensorO_of_finite X.R.ψ X.R.θ (Vc D j) (Wc D j) _ _ (X.R.ωP j t) hC.models.inf
      (hC.thP.ωP j t) _ _ _ _ _ (hC.thP.pt_theta j t) k hk 1 (one_mem _) _
      (GlobalTheory.AdTh.LevelLawCore.omega_level_vP_core D X.Γ X.Pl0 X.T X.A3.A _ X.R.toRealDat X.F.lv2 hC j t k (X.std j) hk hk')
  have key := GlobalTheory.LiftUnfold.integral_theta (hC.thP.ωP j t) (D.sp.V_sig _) (hC.models.vpos j) (X.R.cV j) (hC.models.cV j)
    (X.R.βV j) (X.R.datVt j t) (fun _ => Iff.rfl) hx
    (pureTensorO X.R.ψ X.R.θ (Vc D j) (Wc D j) (fun _ => 1) (cart (X.R.MW j (sg0 D X.A3.A))) (X.R.BV j)
      (onb (X.R.MW j (sg0 D X.A3.A))) (X.R.vP j t) ∘ₗ X.R.ioP j (PiTensorProduct.tprod ℂ u)) (fun w => hC.thP.pt_theta j t _)
    (fun a ha w => (hC.thP.ioP j t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _)
    (hC.models.νV j t) _ (Fin m) (fun k => h₀ k * z') hJ.le (by rw [hrel]; exact one_ne_zero) hy hh g
  have h1 := congrFun (hPF.2 y u) g
  have h2 := hPF.1.eq ((X.R.extV j t).rangeRestrict y) (PiTensorProduct.tprod ℂ u) g
  refine h1.trans (h2.trans (Eq.trans ?_ (key.trans ?_)))
  · rfl
  exact sum_eq_classSum X.R.toRealDat j t hB ψ hc0 hz' hzc hflat (hC.thP.ωP j t) hθ
    hvθ h₀ _ hrel ((X.R.HV j t).e y) u g

theorem thF_eq_classSum : ∀ (D : D7) (X : RealSide D) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), B.Good → BaseOf X.R.toRealDat j B → ∀ (ψ : Twist D Circle) (t : X.T), ψ.Good → B.admitted ψ.Q → IsTupOf X.R.toRealDat B ψ t →
  ∀ ω : PairRep (Vc D j) (Wc D j), B.IsWeil ψ.chi ω → ∀ (I : Type) [Fintype I] (rep : I → GA D (Vc D j)), IsClassSystem (Vc D j) (B.levJ ψ) rep → ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ),
  ∃ (z : GA D (Vc D j)) (a : ℂ), IsCentAt j (X.R.Q t) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime X.R.toRealDat t) a ∧ ∀ y : (X.R.HV j t).H,
    (fun h => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y h)) ∈ B.formsC ψ →
    X.R.thF j t y (fun τ => (u τ : ↥((X.R.MW j (sg0 D X.A3.A)).sm τ))) =
      a • B.classSum ω ψ rep (fun h => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * finPt (Vc D j) z))) := by
  intro D X j B hG hB ψ t hψ hadm htup ω hω I _ rep hrep u
  have hC : GlobalTheory.Hk3.Core X.R.toRealDat X.F.lv2 :=
    ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.chain, X.char.thP⟩
  refine (GlobalTheory.FlatVecExist.flatVec_existsUnique D X.Γ X.Pl0 X.T X.A3.A _ X.R.toRealDat X.F.lv2 hC X.guard j t).1.elim
    fun f hf => ?_
  refine (GlobalTheory.T.flatVector_eq_unit_mul_centralTranslate_liftVector D X.Γ X.Pl0 X.T X.A3.A _ X.R.toRealDat X.F.lv2 hC X.guard j t (X.std j) f hf).elim fun z' hz =>
    hz.elim fun c0 hc => ?_
  have hflat : f = (princ B).vecFlat ψ := eq_vecFlat_princ hB htup hC.lev hG hψ hadm hf
  refine (exists_isClassSystem (princ B) (princ_good hG).frame ψ).elim fun m hm => hm.elim fun h₀ hcs => ?_
  have hzc : finPt (Vc D j) z' ∈ Subgroup.center (Bridge.Gf (Vc D j)) :=
    map_mem_center (finHom (Vc D j)).rangeRestrict (MonoidHom.rangeRestrict_surjective _) hc.1.1
  have hw : B.IsWeil ψ.chi (X.R.ωP j t) := hB.isWeil hC.thP.ωP htup
  refine ⟨z', c0⁻¹, hc.1, unitOff_inv hc.2.1, fun y hy => ?_⟩
  refine (thF_eq_princ X hB htup hc.2.1.1 hc.1.2.1 hzc (hc.2.2.symm.trans hflat) hcs u y).trans (congrArg (c0⁻¹ • ·) ?_)
  exact (classSum_princ hG (D.sp.V_sig _) hψ hadm hw hcs hrep (transl_mem_formsC hzc hy)).trans (classSum_weil hG hadm hw hω _ _)

end GlobalTheory.LiftClassSumTwist

end
end
