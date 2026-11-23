module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle312
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2451
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Formalism.PieriBlockIdeals.LatticeInclusionRealSettingAlt
import Formalism.PieriBlockIdeals.MertensReciprocalElementary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.BigOn.Exp.TupLe.Swap

section Defs

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev ThAt (a : AE D) (b Φ f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) a
    (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 b Φ f


open Classical in
def adjDat (Q : Finset (Pl D.host.E)) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (a : AE D) (x : WO (Vc D i) (Wc D i)) : ℂ :=
  if IsHalf a x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
    omegaQ Q (Wc D i).rank ξR (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0


variable {R} in
open Classical in
def keepPart (t : T0) (Q' : Finset (Pl D.host.E)) : Finset (Pl D.host.E) := (R.Q t).filter fun P => P ∈ Q'


variable {R} in
open Classical in
def flipPart (t : T0) (Q' : Finset (Pl D.host.E)) : Finset (Pl D.host.E) := (R.Q t).filter fun P => P ∉ Q'

end Defs

theorem suppAt_mul' {D : D7} {V : HSp D} {e : AE D} {a b : GA D V} (ha : SuppAt e V a) (hb : SuppAt e V b) :
    SuppAt e V (a * b) := by
  intro i j
  have hm : mt V (a * b) = mt V a * mt V b := by first | rfl | simp [Formalism.L2.Theta.mt]
  have key : mt V a * mt V b - 1 = (mt V a - 1) * mt V b + (mt V b - 1) := by noncomm_ring
  rw [hm, key, Matrix.add_apply, Matrix.mul_apply, mul_add, Finset.mul_sum, hb i j]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ha i k]

end GlobalTheory.BigOn.Exp.TupLe.Swap
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaShiftSmooth

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levChi_flag_eq_one (R : RealDat D A Ks) (i : Fin D.R.m) (κ : GA D (Wc D i)) :
    levChi (Wc D i) (R.βW i) (flagL (R.datWp i R.triv)) κ = 1 := by
  have h2 : ext1 (flagL (R.datWp i R.triv)).P.H (flagL (R.datWp i R.triv)).P.chi
      (rTup (R.βW i) (flagL (R.datWp i R.triv)) (finE (Wc D i) κ)) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h2]
  have hs : (flagL (R.datWp i R.triv)).s = 0 := rfl
  have hQ : (flagL (R.datWp i R.triv)).Q = ∅ := rfl
  rw [hs, hQ]
  simp

theorem exists_translate (R : RealDat D A Ks) (hθ : IsInfFam R.θ) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (g0 : G0 R.Pg D.R.r) (κ' : GA D (Wc D i)) (hκ' : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')
    (X : MMap (R.MW i σ)) (hX : X ∈ R.Wall i σ) :
    ∃ U ∈ R.Wall i σ, ∀ v x, U v x = X v (x * κ') := by
  refine ⟨postOn (R.MW i σ) (actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0) X,
    GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity R.θ (R.MW i σ) hθ (R.βW i) (R.datWp i R.triv) g0 X hX _ fun _ => rfl, fun v x => ?_⟩
  have hT : HasType (Wc D i) (R.βW i) (R.datWp i R.triv) (X v) := fun k hk h =>
    (GlobalTheory.mult_value_left_cont_level R.θ (R.MW i σ) _ _ X hX v).2.2 k hk h
  have h1 := level_action_spec (V := Wc D i) (β := R.βW i) (L := R.datWp i R.triv) hT ⟨κ', hκ'⟩ κ' hκ' x
  rw [levChi_flag_eq_one, inv_one, one_mul] at h1
  exact h1

theorem translate_of_lowT (R : RealDat D A Ks) (hθ : IsInfFam R.θ) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (g0 : G0 R.Pg D.R.r) (κ' : GA D (Wc D i)) (hκ' : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')
    (X X' : MMap (R.MW i σ)) (hX : X ∈ R.Wall i σ) (hX' : X' ∈ R.Wall i σ)
    (h : ∀ (v : ∀ ρ, lowT (R.MW i σ) ρ) (x : GA D (Wc D i)), X' (fun ρ => v ρ) x = X (fun ρ => v ρ) (x * κ'))
    (v : (R.MW i σ).Vec) (x : GA D (Wc D i)) : X' v x = X v (x * κ') := by
  obtain ⟨U, hU, hUv⟩ := exists_translate R hθ i σ g0 κ' hκ' X hX
  have h0 : X' - U = 0 := GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ (R.MW i σ) R.θ hθ
    (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ (X' - U) (Submodule.sub_mem _ hX' hU) fun w => by
      funext z
      exact sub_eq_zero.2 ((h w z).trans (hUv _ z).symm)
  rw [sub_eq_zero.1 h0]
  exact hUv v x

theorem thF_shift_all : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → ∀ y y' : (R.HV i t).H, (∀ h, R.extV i t y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ)) → ∀ (v : (R.MW i (sg0 D A)).Vec) (x : GA D (Wc D i)), R.thF i t y' v x = R.thF i t y v (x * κ') := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hM hP i t g0 κ κ' hκ hκ' y y' hy
  exact translate_of_lowT R hM.inf i (sg0 D A) g0 κ' hκ' (R.thF i t y) (R.thF i t y') (hP.thF_mem i t y)
    (hP.thF_mem i t y') (GlobalTheory.T.thetaLift_intertwines_levelLifts_lowestKType R hL hM hP i t g0 κ κ' hκ hκ' y y' hy)

end GlobalTheory.ThetaShiftSmooth

end
end

section

open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameAut

theorem norm_val_of_orderDvd {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n)
    (v : HeightOneSpectrum (𝓞 E)) : ‖((χ.val v : ℂˣ) : ℂ)‖ = 1 := by
  have h1 : (χ.val v) ^ n = 1 := by
    have h2 := congrArg (fun ψ : Formalism.L2.Host.HChar E => ψ.val v) h
    simpa [Formalism.L2.Host.HChar.val, Formalism.L2.Host.HChar.locK, Formalism.L2.Host.HChar.loc] using h2
  have h3 : ((χ.val v : ℂˣ) : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h3 hn.ne'

theorem norm_sq_valTw_half {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (h : χ.IsUnitary)
    (v : HeightOneSpectrum (𝓞 E)) : ‖χ.valTw (1 / 2) v‖ ^ 2 = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  have h1 : ‖((χ.val v : ℂˣ) : ℂ)‖ = 1 := h _
  have hq : 0 < Ideal.absNorm v.asIdeal := Nat.pos_of_ne_zero fun e => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
  have hq' : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by exact_mod_cast hq
  rw [Formalism.L2.Host.HChar.valTw, norm_mul, h1, one_mul, Complex.norm_natCast_cpow_of_pos hq, Complex.neg_re, Complex.ofReal_re,
    ← Real.rpow_natCast, ← Real.rpow_mul hq'.le, ← Real.rpow_neg_one]
  norm_num

theorem norm_sq_firstValA {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam)
    (j : Fin D.R.m) (t : T) (P : Pl0) (hP : P ∈ A.ok t) :
    ‖D.what₂.embLL (Formalism.L2.Col.firstValA (A.muVal j t) A.etaVal A.q A.r P)‖ ^ 2 = (A.q P : ℝ) ^ A.r := by
  obtain ⟨hQ, -, -, h4⟩ := GlobalTheory.GoodPrimes.good_primes R F hL
  have hq := (h4 hF t P hP).2.2
  obtain ⟨gramR, c0R, c0L, hT⟩ := hF.tie
  have hP0 : P ∈ A.ok A.μ0 := by
    obtain ⟨h1, h2, h3⟩ := (hT.ok t P).1 hP
    refine (hT.ok _ P).2 ?_
    rw [hQ, Finset.coe_empty, Set.union_empty]
    exact ⟨h1, fun h => h2 (Or.inl h), fun Q h => h3 Q (Or.inl h)⟩
  have hmu : ‖D.what₂.embLL (A.muVal j t P : D.what₂.LL)‖ = 1 := by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    rw [hF.muVal j t P hP, Formalism.L2.Host.HChar.val_mul, Units.val_mul, norm_mul, norm_val_of_orderDvd _ hn ho, mul_one]
    exact (R.C.isMu0 j).unitary _
  have heta : ‖D.what₂.embLL (A.etaVal P : D.what₂.LL)‖ ^ 2 = (A.q P : ℝ)⁻¹ := by
    rw [hF.etaVal P hP0, hq]
    exact norm_sq_valTw_half _ R.C.isEta.unitary _
  have hq0 : (A.q P : ℝ) ≠ 0 := by
    rw [hq]
    exact_mod_cast fun e => (R.pl P).ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
  obtain ⟨s, hs⟩ : Odd A.r := hT.ranks.2.1 ▸ Formalism.L2.NTheta.odd_r D.R
  have hd : (A.r + 1) / 2 = s + 1 := by omega
  unfold Formalism.L2.Col.firstValA
  rw [hd, hs]
  simp only [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Units.val_inv_eq_inv_val, map_inv₀, norm_inv, hmu, inv_one, one_mul,
    mul_pow, heta, Complex.norm_natCast]
  field_simp
  ring

end GlobalTheory.FrameAut
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelCharExp

open Formalism.BasicNotions.TH Formalism.IndefR.Lev

theorem pow_of_dvd {G : Type} [Monoid G] {x : G} {n M : ℕ} (h : x ^ n = 1) (hd : n ∣ M) : x ^ M = 1 := by
  obtain ⟨k, rfl⟩ := hd
  rw [pow_mul, h, one_pow]

theorem prod_pow_eq_one {ι G : Type} [CommMonoid G] (s : Finset ι) (f : ι → G) (M : ℕ) (h : ∀ i ∈ s, f i ^ M = 1) :
    (∏ i ∈ s, f i) ^ M = 1 := by
  rw [← Finset.prod_pow]
  exact Finset.prod_eq_one h

theorem residue_char_pow {E : Type} [Field E] [NumberField E] (PP : Formalism.L2.DIV.Pl E) {LL : Type} [Monoid LL]
    (χ : (Formalism.L2.DIV.kP PP)ˣ →* LL) (u : (Formalism.L2.DIV.kP PP)ˣ) : χ u ^ Nat.card (Formalism.L2.DIV.kP PP)ˣ = 1 := by
  rw [← map_pow, pow_card_eq_one', map_one]

theorem card_units_pos {E : Type} [Field E] [NumberField E] (PP : Formalism.L2.DIV.Pl E) : 0 < Nat.card (Formalism.L2.DIV.kP PP)ˣ := by
  have : Finite (Formalism.L2.DIV.kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  exact Nat.card_pos


open Classical in
def expOf {D : D7} {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) : ℕ :=
  ∏ PP ∈ L.Pg ∪ L.Q, Nat.card (Formalism.L2.DIV.kP PP)ˣ

theorem expOf_pos {D : D7} {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) : 0 < expOf L :=
  Finset.prod_pos fun PP _ => card_units_pos PP

open Classical in
theorem levFn_flag1_pow {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (x : GL (Fin V.rank) (Lev.EAf D)) :
    Formalism.L2.DIV.levFn β (flag1L L) x ^ expOf L = 1 := by
  have h1 : Formalism.L2.DIV.ext1 (flag1L L).P.H (flag1L L).P.chi (Formalism.L2.DIV.rTup β (flag1L L) x) = 1 :=
    Formalism.IndefR.Lev.subgroupCharExtension_one_apply _ _
  unfold Formalism.L2.DIV.levFn
  rw [h1, one_mul, mul_pow]
  have hd : ∀ PP ∈ L.Pg ∪ L.Q, Nat.card (Formalism.L2.DIV.kP PP)ˣ ∣ expOf L := fun PP hP =>
    Finset.dvd_prod_of_mem (fun PP => Nat.card (Formalism.L2.DIV.kP PP)ˣ) hP
  rw [prod_pow_eq_one _ _ _ ?_, prod_pow_eq_one _ _ _ ?_, one_mul]
  · intro PP hP
    exact pow_of_dvd (residue_char_pow PP _ _) (hd PP (Finset.mem_union_right _ hP))
  · intro PP hP
    refine prod_pow_eq_one _ _ _ fun c _ => ?_
    exact pow_of_dvd (residue_char_pow PP _ _) (hd PP (Finset.mem_union_left _ hP))

theorem levEnv_chi_pow : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J), (levEnv V β L).χ k ^ expOf L = 1 := by
  intro D V β L k
  exact levFn_flag1_pow V β L _

end GlobalTheory.LevelCharExp

end

namespace GlobalTheory.LevelCharExp

end GlobalTheory.LevelCharExp
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem formalFibre_isRegularRing_of_essFiniteType :
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)]
      (R K : Type) [CommRing R] [IsLocalRing R] [Algebra Λ R] [Algebra.EssFiniteType Λ R]
      [Field K] [Algebra R K] [Algebra.EssFiniteType R K],
      (∀ a : Λ, algebraMap R K (algebraMap Λ R a) = 0 → a = 0) →
      IsRegularRing (AdicCompletion (maximalIdeal R) R ⊗[R] K) := by
  intro Λ _ _ _ _ R K _ _ _ _ _ _ _ hK
  obtain ⟨n, P, hP, φ, hφ⟩ := GlobalTheory.T.exists_surj_localization_mvPolynomial_of_essFiniteType_local Λ R
  let R₀ := Localization.AtPrime P
  letI : Algebra R₀ R := φ.toRingHom.toAlgebra
  letI : Algebra R₀ K := ((algebraMap R K).comp φ.toRingHom).toAlgebra
  haveI : IsScalarTower R₀ R K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsNoetherianRing R₀ := IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hsurj : Function.Surjective (algebraMap R₀ R) := hφ
  haveI : Algebra.FiniteType R₀ R := Algebra.FiniteType.of_surjective (Algebra.ofId R₀ R) hsurj
  haveI : Algebra.EssFiniteType R₀ R := inferInstance
  haveI : Algebra.EssFiniteType R₀ K := Algebra.EssFiniteType.comp R₀ R K
  have hK₀ : ∀ a : Λ, algebraMap R₀ K (algebraMap Λ R₀ a) = 0 → a = 0 := by
    intro a ha
    apply hK a
    have h1 : algebraMap R₀ K (algebraMap Λ R₀ a) = algebraMap R K (φ (algebraMap Λ R₀ a)) := rfl
    rw [h1, φ.commutes] at ha
    exact ha
  have hreg := GlobalTheory.T.isRegularRing_formal_fibre_mvPolynomial_perfect Λ n P K hK₀
  obtain ⟨e⟩ := GlobalTheory.T.nonempty_adicCompletion_tensor_ringEquiv_of_surjective R₀ R K hsurj
  exact IsRegularRing.of_ringEquiv e.symm

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.exists_dimSucc_generating_sections_infiniteField : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X] (p : X ⟶ Sp k) (L : LB X), L.IsLB → ∀ d : ℕ, topologicalKrullDim X ≤ d → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → ∃ s : Fin (d + 1) → L.Sec, ⨆ i, nonzeroLocus (s i) = ⊤ := by
  first | exact @GlobalTheory.GenCut.exists_generating_sections_of_dim_le | exact GlobalTheory.GenCut.exists_generating_sections_of_dim_le | (intros; apply GlobalTheory.GenCut.exists_generating_sections_of_dim_le <;> assumption)
end
