module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle238
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle078
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneMapOfOfPtIdent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1693
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2200
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle303
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdeleAt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeries
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle007
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle054
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle080
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle477
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle484
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle342
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle300
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeFramesRightTranslateDifferIntegralGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle500
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle032
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle499

@[expose] public section

section

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.LiftSpan

open _root_.Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.OneMapTuples GlobalTheory.OneMapAll GlobalTheory.FieldBC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
  {ι : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}




end GlobalTheory.LiftSpan

namespace GlobalTheory.LiftSpan

open _root_.Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.OneMapTuples GlobalTheory.OneMapAll

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


section Guard

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
  {ι : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}


set_option maxHeartbeats 1000000 in
theorem lam_geo_mem_span {O : OMDat T.toCore R i Unit fun _ => A.μ0} (hP : O.Pins κ v₀ ι x₀) (hspan : ClassSumsSpan O κ)
    {lam : AutQ (Wc D i) → ℂ} {z : G} {c0 : ℂ} (hid : PtIdent O κ lam z c0) :
    ∀ f ∈ cuspOver O κ, (fun q => lam q * geo O (fun _ => 1) z f q) ∈ Submodule.span ℂ (Set.range (liftQ R i v₀ A.μ0)) := by
  obtain ⟨ζ, -, hζ, h⟩ := hid ()
  intro f hf
  have hf' := hspan hf
  clear hf
  induction hf' using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨hg, x, hx, hgx⟩ := hg
    obtain ⟨y, hy⟩ := lift_of_plc hP hx
    have e : (fun q => lam q * geo O (fun _ => 1) z g q) = (c0 / ζ) • liftQ R i v₀ A.μ0 y := by
      funext q
      rw [Pi.smul_apply, smul_eq_mul, ← hy, div_mul_eq_mul_div, eq_div_iff (ne_zero_of_root hζ),
        h x hx g ((mem_cusp _ _ _ _ _ _).1 hg).1 hgx q]
      show lam q * (1 * rdQ O z g q) * _ = _
      ring
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  | zero =>
    have e : (fun q => lam q * geo O (fun _ => 1) z 0 q) = 0 := funext fun q => by
      have := geo_smul O (fun _ => 1) z 0 0 q
      rw [zero_smul] at this
      rw [this]
      simp
    rw [e]
    exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    convert Submodule.add_mem _ hf hg using 1
    funext q
    rw [geo_add, mul_add, Pi.add_apply]
  | smul a f _ hf =>
    convert Submodule.smul_mem _ (a : ℂ) hf using 1
    funext q
    rw [geo_smul, mul_left_comm, Pi.smul_apply, smul_eq_mul]



theorem liftsSpan_of_ptIdent {O : OMDat T.toCore R i Unit fun _ => A.μ0} (hP : O.Pins κ v₀ ι x₀) (hspan : ClassSumsSpan O κ)
    {O' : OMDat T.toCore R i T0 id} (hP' : O'.Pins κ v₀ ι x₀) (hlev : O'.lev = O.lev) (hex : ClsEx O' κ)
    {lam : AutQ (Wc D i) → ℂ} {z : G} {c0 c1 : ℂ} (hc1 : c1 ≠ 0) (hid : PtIdent O κ lam z c0) (hid' : PtIdent O' κ lam z c1) :
    LiftsSpan R i v₀ := by
  intro t y
  have e2 : O'.lev2 = O.lev2 := by funext g; simp only [OMDat.lev2, hlev]
  obtain ⟨x, hx, e⟩ := plc_of_lift hP' t y
  obtain ⟨f, hf, hfx, -⟩ := hex t x hx
  obtain ⟨s, -, -, h⟩ := hid' t
  have hf' := ((mem_cusp _ _ _ _ _ _).1 hf).1
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O'.hle).2 _ (T.U ((i : ℕ) + 1)) _ _ f hf
  have hs : ∀ k, fs k ∈ sec _ T.Q.c (wtA κ) (Vc D i).rank := fun k => ((mem_cusp _ _ _ _ _ _).1 (hfs k)).1
  have key : liftQ R i v₀ t y = ∑ k, (s / c1 * (as k : ℂ)) •
      fun q => lam q * geo O (fun _ => 1) z (GlobalTheory.FieldBC.rulBC O.hle (fs k)) q := by
    funext q
    have h1 : c1 * O'.thAd t x q = s * lam q * rdQ O' z f q := h x hx f hf' hfx q
    have h2 : 1 * rdQ O' z f q = _ := geo_of_isBC O' hP'.act.1 (fun _ => 1) z hf' hs hBC q
    rw [phi_eq O' O (fun _ _ => 1), e2, one_mul] at h2
    have h3 : ∀ k, geo O (fun _ => 1) z (GlobalTheory.FieldBC.rulBC O.hle (fs k)) q =
        O.phi (fun _ => 1) (actLev T.Q.c O.lev2 z (fs k)) q.out := fun k => by
      have hs1 : ∀ k', ![fs k] k' ∈ sec _ T.Q.c (wtA κ) (Vc D i).rank := fun k' => by
        rw [Subsingleton.elim k' 0]; exact hs k
      rw [geo_of_isBC O hP.act.1 _ z (GlobalTheory.FieldBCModel.rulBC_mem_sec O.hle (hs k)) hs1
        (GlobalTheory.FieldBCModel.isBC_rulBC O.hle (hs k).1)]
      simp only [Fin.sum_univ_one, Matrix.cons_val_zero, OneMemClass.coe_one, one_mul]
    refine mul_left_cancel₀ hc1 ?_
    rw [show liftQ R i v₀ t y = O'.thAd t x from e.symm, h1, h2]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  rw [key]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (lam_geo_mem_span hP hspan hid _
    (((GlobalTheory.FieldBC.rulBC_cusp _ _ _ _ _ _ _ O.hle _ (T.U ((i : ℕ) + 1)) _ _ _ (hs k)).2).2 (hfs k)))

end Guard


end GlobalTheory.LiftSpan
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.RealMove

open GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant (detPos detNeg vacChar)
open scoped ComplexOrder

variable {D : D7} {S T : HSp D}

theorem root_eq {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (hn : Even n) {g : GA D T} {x x' : (AE D)ˣ}
    (hx : IsDetRoot T g x) (hx' : IsDetRoot T g x') : χ x' = χ x := by
  obtain ⟨a, rfl⟩ := (GlobalTheory.Member.isDetRoot_laws D T).2.1 g x x' hx hx'
  obtain ⟨⟨η, hη⟩, h2⟩ := h
  obtain ⟨m, rfl⟩ := hn
  rw [map_mul, h2 η hη a, pow_add, ← mul_pow, GlobalTheory.VolHeckeCompare.IsEta_mul_self hη, one_pow, mul_one]

theorem om_compact (C : GlobalTheory.Ker.Ctx S T) {χS χT η : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO C.ψ S T χS χT om) (hη : IsEtaTilde D η)
    {s : Fam T} (hs : ∀ τ, IsCartanInv (gramAt D T τ) (s τ)) {k : GA D T} (hk : k ∈ GinfC T)
    (hc : ∀ τ, s τ * compAt C.θ τ (Formalism.L2.Theta.mt T k) = compAt C.θ τ (Formalism.L2.Theta.mt T k) * s τ)
    {y : (AE D)ˣ} (hy : IsDetRoot T k y) {f : WO S T → ℂ} (hf : IsThetaFunO C.ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO C.ψ S T) C.θ τ (cplxO 1 (s τ)) f) :
    om (1, k) f = (((χS y : Circle) : ℂ) * vacChar C.θ T s S.rank (fun _ => 0) k) • f := by
  have hdet : ∀ τ, (gramAt D T τ).det ≠ 0 := fun τ => by
    have := (hs τ).2.2.det_pos.ne'
    rw [Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  obtain ⟨y₀, hy₀, hv₀⟩ := GlobalTheory.OneMapRef.RealMove.exists_root C.inf T hdet k hk
  have hS : ∀ τ, IsCartanInv (gramAt D S τ) 1 := fun τ => by
    have e : gramAt D S τ = 1 := by
      unfold gramAt
      rw [C.m.gS]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [e]
    exact ⟨one_mul _, by simp, by rw [one_mul]; exact Matrix.PosDef.one⟩
  have h1 : IsDetRoot S 1 1 := by simp [IsDetRoot]
  rw [GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D C.ψ hW.std S T C.θ C.inf χS χT om η hη hW (fun _ => 1) s hS hs 1 (one_mem _) k hk
    (fun τ => by rw [one_mul, mul_one]) hc 1 y₀ h1 hy₀ f hf hv, root_eq hW.resS C.even hy₀ hy]
  congr 1
  obtain ⟨m, hm⟩ := C.even
  have e1 := hv₀ (η * (η ^ (S.rank + 1))⁻¹) (fun _ => -(m : ℤ)) fun τ => by
    have := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (hη.2.2.2 τ) (hη.2.2.2 τ) (S.rank + 1)
    convert this using 1
    rw [hm]
    push_cast
    ring
  have e2 : ((χT * (η ^ T.rank)⁻¹) 1)⁻¹ * (χS * (η ^ S.rank)⁻¹) y₀ = χS y₀ * (η * (η ^ (S.rank + 1))⁻¹) y₀ := by
    simp only [map_one, inv_one, one_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, pow_succ,
      mul_inv]
    rw [mul_left_comm (η y₀), mul_inv_cancel, mul_one]
  rw [e2, Circle.coe_mul, e1, mul_assoc, ← Finset.prod_mul_distrib, vacChar]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨p, -, hd⟩ := GlobalTheory.OneMapRef.RealMove.detPlus_one (n := S.rank) (s τ) (hs τ).1
  obtain ⟨d1, d2⟩ := hd (compAt C.θ τ (Formalism.L2.Theta.mt S 1⁻¹)) (compAt C.θ τ (Formalism.L2.Theta.mt T k)) (hc τ)
  have e3 : (compAt C.θ τ (Formalism.L2.Theta.mt S 1⁻¹)).det = 1 := by
    rw [GlobalTheory.OneMapRef.RealMove.det_compAt, inv_one]
    unfold Formalism.L2.Theta.mt
    rw [map_one, Units.val_one, Matrix.det_one, map_one, map_one]
  have e4 : (compAt C.θ τ (Formalism.L2.Theta.mt T k)).det ≠ 0 := by
    intro h0
    have h2 := congrArg det (GlobalTheory.Ker.ONBasis.compAt_unitary C τ k)
    rw [det_mul, h0, mul_zero] at h2
    exact hdet τ h2.symm
  have hc' := hc τ
  rw [d1, e3]
  generalize compAt C.θ τ (Formalism.L2.Theta.mt T k) = b at *
  have p1 : detPos (s τ) b = ((1 / 2 : ℂ) • (1 + s τ) * b + (1 / 2 : ℂ) • (1 - s τ)).det := by
    rw [detPos, Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul, hc', one_mul, mul_one]
  have p2 : detNeg (s τ) b = ((1 / 2 : ℂ) • (1 - s τ) * b + (1 / 2 : ℂ) • (1 + s τ)).det := by
    rw [detNeg, detPos, Matrix.mul_smul, Matrix.smul_mul, ← sub_eq_add_neg, sub_neg_eq_add, mul_sub, sub_mul, hc',
      one_mul, mul_one]
  rw [← p1, ← p2] at d2
  rw [← p1, d2]
  rw [d2] at e4
  have h0 := left_ne_zero_of_mul e4
  have e5 : S.rank / 2 = m := by omega
  rw [e5, zero_add, zero_sub, _root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast, zpow_natCast, hm,
    one_pow, mul_one, mul_pow, pow_add, mul_inv]
  have := pow_ne_zero m h0
  field_simp

theorem th_ne_zero (C : GlobalTheory.Ker.Ctx S T) {x : Frame C.X.Ψ T.rank}
    (hx : x ∈ C.X.dom) {φ : TF S.rank C.g} (hφ : GlobalTheory.SW.IsSB φ)
    (h0 : φ ≠ 0) : C.Th x φ ≠ 0 := by
  intro h
  obtain ⟨l1, l2, -⟩ := GlobalTheory.Ker.Ctx.th_laws D S T C x hx φ hφ
  have h3 : GlobalTheory.SW.IsSB ((0 : ℂ) • φ) := by
    rw [zero_smul]
    exact GlobalTheory.SW.isSB_zero
  refine h0 (((l1 _ h3).2 ?_).trans (zero_smul ℂ φ))
  rw [l2, h, smul_zero]

theorem th_zero (C : GlobalTheory.Ker.Ctx S T) {x : Frame C.X.Ψ T.rank}
    (hx : x ∈ C.X.dom) : C.Th x (0 : TF S.rank C.g) = 0 := by
  have h := (GlobalTheory.Ker.Ctx.th_laws D S T C x hx 0 GlobalTheory.SW.isSB_zero).2.1 0
  rwa [zero_smul, zero_smul] at h

theorem om_real (C : GlobalTheory.Ker.Ctx S T) {χS χT η : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO C.ψ S T χS χT om) (hη : IsEtaTilde D η)
    {a : GA D T} (ha : a ∈ GinfC T) {y : (AE D)ˣ} (hy : IsDetRoot T a y) {B : C.Bas} (hB : C.IsB B)
    {φ : TF S.rank C.g} (hφ : GlobalTheory.SW.IsSB φ) :
    om (1, a) (C.Th (C.xB B) φ) = ((χS y : Circle) : ℂ) • C.Th (C.xB (C.mvB a B)) φ := by
  obtain ⟨χ, -, χmul, hχ⟩ := GlobalTheory.FrameEquiv.exists_real_character D S T C om (GlobalTheory.Ker.isWeak_of_datum hW)
  have hJ := (GlobalTheory.Ker.onBasis_frame_period D S T C).2
  have hd := GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C hB
  by_cases h0 : φ = 0
  · rw [hχ a ha B hB φ hφ, h0, th_zero C
      (GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C ((hJ B hB).2.2.2.2.2 a).1), smul_zero, smul_zero]
  obtain ⟨hex, -, -, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D T
  choose rt hrt using hex
  have hne : ∀ g, ((χS (rt g) : Circle) : ℂ) ≠ 0 := fun g => Circle.coe_ne_zero _
  have key := GlobalTheory.FrameEquiv.mulFun_eq_one_of_eq_one_on_maxCompact D T C.θ C.inf (C.sB B)
    (fun τ => ((hJ B hB).2.2.1 τ).1) (fun u => χ u / (χS (rt u) : Circle))
    (fun u hu u' hu' => by
      simp only [χmul u hu u' hu']
      rw [root_eq hW.resS C.even (hmul _ _ _ _ (hrt u) (hrt u')) (hrt (u * u')), map_mul, Circle.coe_mul,
        mul_div_mul_comm])
    (fun k hk hc => by
      have e1 := om_compact C hW hη (fun τ => ((hJ B hB).2.2.1 τ).1) hk (fun τ => (hc τ).symm) (hrt k)
        (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hd φ hφ).1.1 ((GlobalTheory.Ker.fvec_Th_zero D S T C).2 B hB φ hφ).1
      have e2 := hχ k hk B hB φ hφ
      have e3 := GlobalTheory.FrameEquiv.CompactMove.Th_mvB D S T C B hB k hk hc φ hφ
      rw [← smul_smul, ← e3, e2] at e1
      have e4 := smul_left_injective ℂ (th_ne_zero C
        (GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C ((hJ B hB).2.2.2.2.2 k).1) hφ h0) e1
      show χ k / (χS (rt k) : Circle) = 1
      rw [e4, div_self (hne k)]) a ha
  rw [hχ a ha B hB φ hφ, (div_eq_one_iff_eq (hne a)).1 key, root_eq hW.resS C.even hy (hrt a)]



theorem zak_om_real : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (_hS : IsSet ψ θ S T hr X eT bas), ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → (∃ η, IsEtaTilde D η) → ∀ Z : Fam T, IsONeg T X.p0 Z → ∀ a ∈ GinfC T, ∀ y : (AE D)ˣ, IsDetRoot T a y → ∀ φ : TF S.rank g, GlobalTheory.SW.IsSB φ → ∀ f, Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f → Zak ψ θ hr eT bas idx (frOf hr eT (mvZ θ a Z)) (((χS y : Circle) : ℂ) • φ) (om (1, a) f) := by
  intro D S T r g hr ψ θ X eT bas idx hS χS χT om hW ⟨η, hη⟩ Z hZ a ha y hy φ hφ f hf
  obtain ⟨X', m, hq', bas', idx', hs, π, -, -, -, H⟩ := GlobalTheory.T.exists_conjugateModel_same_thetaFunctions D S T r g hr ψ θ X eT bas idx hS (r - X.p0)
    (Nat.add_sub_cancel' X.p0_le)
  set C := ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs with hC
  have hB := (H Z).1.1 hZ
  have em : (fun ρ => (mvZ θ a Z ρ).submatrix id π) = C.mvB a fun ρ => (Z ρ).submatrix id π := by
    funext ρ
    ext i j
    rfl
  have hB' := (((GlobalTheory.Ker.onBasis_frame_period D S T C).2 _ hB).2.2.2.2.2 a).1
  have hZ' : IsONeg T X.p0 (mvZ θ a Z) := (H _).1.2 (em ▸ hB')
  have hd := GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C hB
  have hd' := GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C hB'
  have e1 := (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hd φ hφ).2 f ((((H Z).2 hZ).2.1 φ f).2 hf)
  refine (((H _).2 hZ').2.1 _ _).1 ?_
  have hφ' : GlobalTheory.SW.IsSB (((χS y : Circle) : ℂ) • φ) := (isSB_algebra_haar_linear _ _ _ _ _ hφ hφ).2.1 _
  rw [em, e1, om_real C hW hη ha hy hB hφ, ← (GlobalTheory.Ker.Ctx.th_laws D S T C _ hd' φ hφ).2.1]
  exact (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hd' _ hφ').1

end GlobalTheory.OneMapRef.RealMove
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi.NearWd

theorem congE_of_cols {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (c : ℕ)
    (g g' : Sp E n ≃ₗ[E] Sp E n) (hg : g ∈ Formalism.L2.Col.GLint E n P)
    (h : ∀ j l : Fin n, IntAt P ((((qOf P : ℕ) : E) ^ c)⁻¹ * ((g⁻¹ * g') (Pi.single j (1 : E)) l - (Pi.single j (1 : E) : Sp E n) l))) :
    CongE P c g' g := by
  intro x hx
  have e1 : g (g⁻¹ (g' x)) = g' x := by
    show (g * g⁻¹) (g' x) = g' x
    rw [mul_inv_cancel]; rfl
  have e : (((qOf P : ℕ) : E) ^ c)⁻¹ • (g' x - g x) = g ((((qOf P : ℕ) : E) ^ c)⁻¹ • ((g⁻¹ * g') x - x)) := by
    rw [map_smul, map_sub]
    show _ = _ • (g (g⁻¹ (g' x)) - g x)
    rw [e1]
  rw [e]
  refine (hg _).2 ?_
  rw [stdAt, mem_localization_standardLattice] at hx ⊢
  intro l
  have hs := GlobalTheory.TopStep.apply_eq_sum ((g⁻¹ * g').toLinearMap - LinearMap.id) x l
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, Pi.sub_apply] at hs
  rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hs, Finset.mul_sum]
  refine Finset.sum_induction _ (IntAt P) (fun a b ha hb => ha.add hb) (by simpa using GlobalTheory.TopInv.intAt_nat (P := P) 0) fun j _ => ?_
  rw [mul_left_comm]
  exact (hx j).mul (h j l)

theorem congAt_of_near_same {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (Q : HeightOneSpectrum (𝓞 E)) (n : ℕ) (hn : 1 ≤ n) (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (k k' : GL (Fin N) E)
    (h : GlobalTheory.TwU.NearAt Q n y k) (h' : GlobalTheory.TwU.NearAt Q n y k') : GlobalTheory.TwU.CongAt Q n (GlobalTheory.TwU.ratA F (k⁻¹ * k')) := by
  have e : GlobalTheory.TwU.ratA F (k⁻¹ * k') = (y⁻¹ * GlobalTheory.TwU.ratA F k)⁻¹ * (y⁻¹ * GlobalTheory.TwU.ratA F k') := by
    rw [map_mul, map_inv]; group
  rw [e]
  exact GlobalTheory.CongProd.congAt_mul_prod _ _ _ _ _ _ _ (GlobalTheory.TwU.congAt_inv_pos_depth _ _ _ _ _ _ hn h) h'

theorem val_eq_of_congE {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) (j : ℕ) (hj : j < B.R.m) (b : (I.idx a).β j)
    (P : SBof I a) (g g' : Sp B.fields.E (B.R.N j) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N j)) (z z' : B.fields.K)
    (hz : GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) j P ((I.idx a).h j b P) g z)
    (hz' : GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) j P ((I.idx a).h j b P) g' z')
    (hgg : CongE P.1 ((I.cst a).D P) g' g) : z = z' := by
  classical
  have hL := hOk.idx_ok a
  obtain ⟨r, hr, hrx, rfl⟩ := hz
  obtain ⟨r', hr', hrx', rfl⟩ := hz'
  have hgC : g ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp j P.1 ((I.idx a).h j b P) := ⟨r, hr, hrx⟩
  have hgI : g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N j) P.1 := hL.int j b P hgC
  let G : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N j) P.1) := ⟨g, hgI⟩
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · have hred : ∀ x ∈ stdAt B.fields.E (B.R.N j) P.1, redV P.1 (g x) = (GlobalTheory.TopStep.redGL _ P.1 G).1.mulVec (redV P.1 x) :=
      fun x hx => GlobalTheory.TopStep.redV_redGL G hx
    have hmem : GlobalTheory.TopStep.redGL _ P.1 G ∈ ((I.idx a).levG j b ⟨P.1, hP⟩).H :=
      (hL.grpG j b ⟨P.1, hP⟩ _).2 ⟨g, hgC, hred⟩
    have hκ : (GlobalTheory.TopStep.redGL _ P.1 G)⁻¹ ∈ ((I.idx a).levG j b ⟨P.1, hP⟩).H := inv_mem hmem
    have hred' : ∀ x ∈ stdAt B.fields.E (B.R.N j) P.1, redV P.1 (g x) = (((GlobalTheory.TopStep.redGL _ P.1 G)⁻¹)⁻¹).1.mulVec (redV P.1 x) := by
      intro x hx
      rw [inv_inv]
      exact hred x hx
    rw [chiInv_at_type I hOk a j b P hP g g r hr hrx _ hκ hred' (congE_refl _ _ _),
      chiInv_at_type I hOk a j b P hP g' g r' hr' hrx' _ hκ hred' hgg]
  · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.mp P.2).resolve_left hP
    have hH : G ∈ ((I.idx a).levQ j b ⟨P.1, hQ⟩).H := by
      rw [hL.grpQ j b ⟨P.1, hQ⟩]
      exact Subgroup.mem_subgroupOf.2 hgC
    have hg1 : g = ((G⁻¹)⁻¹).1 := by rw [inv_inv]
    rw [chiInv_at_twist I hOk a j hj b P hQ g g r hr hrx G⁻¹ (inv_mem hH) hg1 (congE_refl _ _ _),
      chiInv_at_twist I hOk a j hj b P hQ g' g r' hr' hrx' G⁻¹ (inv_mem hH) hg1 hgg]

end GlobalTheory.Mem.Col2.QChi.NearWd

namespace GlobalTheory.Mem.Col2.QChi

theorem nearPair_val_unique : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (P : SBof I a)
    (x : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F))
    (g g' : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (z z' : B.fields.K),
    GlobalTheory.Mem.Col2.QChi.NearPair I l Z a v P x g z → GlobalTheory.Mem.Col2.QChi.NearPair I l Z a v P x g' z' → z = z' := by
  intro B X I hOk l Z a v P x g g' z z' h h'
  have hL := hOk.idx_ok a
  have hm := hL.hm
  have key : ∀ j, j = B.R.m - 2 + 1 → ∃ b : (I.idx a).β j, (I.idx a).h j b P = 1 := by
    rintro j rfl
    obtain ⟨b, -⟩ := hL.last_uniq
    exact ⟨b, hL.last_h b P⟩
  obtain ⟨b, hb⟩ := key (B.R.m - 1) (by omega)
  obtain ⟨hz, hn⟩ := h
  obtain ⟨hz', hn'⟩ := h'
  rw [← hb] at hz hz'
  have hD : 1 ≤ (I.cst a).D P := hL.cst_ok.D_pos P
  unfold NearV at hn hn'
  have hc := NearWd.congAt_of_near_same _ _ hD _ _ _ hn hn'
  have hgI : g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N (B.R.m - 1)) P.1 :=
    hL.int _ b P ((GlobalTheory.TwU.exists_midLev_iff _ _ _ _ _ _ _ g).1 ⟨z, hz⟩)
  exact NearWd.val_eq_of_congE I hOk a (B.R.m - 1) (by omega) b P g g' z z' hz hz'
    (NearWd.congE_of_cols P.1 _ g g' hgI (GlobalTheory.LevFrame.cols_of_congAt (sm I l Z) P.1 _ (g⁻¹ * g') (by rw [map_mul, map_inv]; exact hc)))

end GlobalTheory.Mem.Col2.QChi

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.WitTr



theorem kerT_entC_setDiv : ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B}
    (w : ColW B f T) (Z : w.Lt) (t : ColT w Z) (Y : DivX (w.D Z)) (Gy : G.LatInst (w.D Z))
    (ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy) (k : KerT t Y Gy ker)
    (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ),
    EntC k → ∃ k' : KerT (DivTr.colTTr w Z N h t) (DivTr.divTrZ w Z N h Y)
      (DivTr.latTrZ w Z N h Gy) (DivTr.kerTr w Z N h ker), EntC k' := by
  intro B f T w Z t Y Gy ker k N h hE
  exact ⟨DivTr.ktTr w Z N h k, DivTr.entC_tr w Z N h k hE⟩

end GlobalTheory.Mem.Top.Bl.WitTr
end
