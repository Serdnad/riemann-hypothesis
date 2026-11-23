module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDefiniteUnitaryDoubleCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle197
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle001
public import Mathlib.NumberTheory.NumberField.CMField

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Formalism.L2.Host Formalism.UG
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace GlobalTheory.BCWords

section Linear

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a N c : ℕ} {n : Fin c → ℕ}

def tensorSp (V : ∀ i, Submodule ℂ (Sm E (n i))) : Submodule ℂ ((∀ i, GA E (n i)) → ℂ) :=
  Submodule.span ℂ {F | ∃ φ : ∀ i, V i, F = fun m => ∏ i, (φ i).1.1 (m i)}

end Linear

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end GlobalTheory.BCWords

end
end

section

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjTwist

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def IsRoot1 (z : ℂ) : Prop := ∃ n : ℕ, 0 < n ∧ z ^ n = 1

def UnitOff (N : ℕ) (u : ℂ) : Prop :=
  u ≠ 0 ∧ ∃ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ n * u) ∧ IsIntegral ℤ ((N : ℂ) ^ n * u⁻¹)

section Any

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def ConjTup (τ : ℂ ≃+* ℂ) (t t' : T0) : Prop :=
  R.Q t' = R.Q t ∧ ∀ x, ((R.xi t' x : Circle) : ℂ) = τ ((R.xi t x : Circle) : ℂ)


open Classical in
def omegaFlat {a b : ℕ} (Q : Finset (Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin a) (Fin b) (kP PP)) : ℂ :=
  if h : ∀ PP ∈ Q, IsUnit (topL r (y PP)).det then ∏ PP ∈ Q.attach, ((ξ PP.1 (h PP.1 PP.2).unit : ℂˣ) : ℂ) else 0


open Classical in
def IsFlatVec (i : Fin D.R.m) (t : T0) (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  ∃ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg ∧ IsIdemSum eQ (R.Q t) ∧
    IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg)
      (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i)
      (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg ∧
    IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) eQ
      (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 fg
      (fun x => if IsHalf eQ x ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) f

def IsCentAt (i : Fin D.R.m) (Q : Finset (Pl D.host.E)) (z : GA D (Vc D i)) : Prop :=
  z ∈ Subgroup.center (GA D (Vc D i)) ∧ z ∈ GfC (Vc D i) ∧ ∃ e : AE D, IsIdemSum e Q ∧ SuppAt e (Vc D i) z

def ser (i : Fin D.R.m) (t : T0) (f : WO (Vc D i) (Wc D i) → ℂ) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i))
    (w : (R.cV i).W) (g : GA D (Wc D i)) : ℂ :=
  thetaKO (R.ωP i t) h g (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i)
    (onb (R.MW i (sg0 D A))) f (R.ioP i (PiTensorProduct.tprod ℂ u) w))

theorem ser_vP (i : Fin D.R.m) (t : T0) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (w : (R.cV i).W)
    (g : GA D (Wc D i)) :
    ser R i t (R.vP i t) u h w g = thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w)) := rfl

def ConjVec (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (x x' : VsV D i ℂ) : Prop :=
  (x' : Pol ℂ D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (τ : ℂ →+* ℂ) (x : Pol ℂ D.what₂.Tau (Vc D i).rank)

def ExtC (i : Fin D.R.m) {K' : Type} [Field K'] (σ' : K' →+* ℂ) (c0 : VsV D i K' →ₛₗ[σ'] (R.cV i).W)
    (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) : Prop :=
  ∀ (v : VsV D i K') (v' : VsV D i ℂ),
    (v' : Pol ℂ D.what₂.Tau (Vc D i).rank) = MvPolynomial.map σ' (v : Pol K' D.what₂.Tau (Vc D i).rank) → c v' = c0 v

def ConjForm (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) (t t' : T0) (y : (R.HV i t).H)
    (y' : (R.HV i t').H) : Prop :=
  ∀ h : GA D (Vc D i), ∃ x x' : VsV D i ℂ, ConjVec i τ x x' ∧ (R.HV i t).e y (fin _ h) = c x ∧ (R.HV i t').e y' (fin _ h) = c x'

end Any

section Core

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)

structure FixBase (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) : Prop where
  core : ∀ a : T.Q.c.F, τ (a : ℂ) = (a : ℂ)
  host : ∀ (φ : D.host.E →+* ℂ) (x : D.host.E), τ (φ x) = φ x
  curve : GlobalTheory.CompRat.FixesCurve T.Q.H τ 1
  split : ∀ P : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
    τ ((((R.C.mu0 i * R.C.eta⁻¹).val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ)) =
      (((R.C.mu0 i * R.C.eta⁻¹).val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ)
  chi : ∀ PP ∈ R.Pg, ∀ x, τ ((R.chi ((i : ℕ) + 1) PP x : ℂˣ) : ℂ) = ((R.chi ((i : ℕ) + 1) PP x : ℂˣ) : ℂ)

variable {T R} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

def Expands (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (Φ : GA D (Wc D i) → ℂ) {n : ℕ} (a : Fin n → ℂ)
    (f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n) : Prop :=
  ∀ g, Φ g = ∑ k, a k * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
    O.phi (T.cE ((i : ℕ) + 1) O.s0) (f k : T.toCore.R ((i : ℕ) + 1)) g)

def ConjFun (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ) (ζ : ℂ) (Φ Φ' : GA D (Wc D i) → ℂ) : Prop :=
  (∃ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n), Expands O κ Φ a f) ∧
    ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n),
      Expands O κ Φ a f → Expands O κ Φ' (fun k => ζ * τ (a k)) f

def SameCover (O : OMDat T.toCore R i Tp tup) (a b : Tp) (e : O.Cl' a ≃ O.Cl' b) : Prop :=
  (∃ cx : Rul (O.dδ a).Xo₂ (O.dδ a).c₂, O.dδ b = { O.dδ a with cδ := cx }) ∧ HEq (O.U₂ b) (O.U₂ a) ∧ HEq (O.dict₂ b) (O.dict₂ a) ∧
    O.bad b = O.bad a ∧ O.vol b = O.vol a ∧
    ∀ k, O.Lh b (e k) = O.Lh a k ∧ O.La b (e k) = O.La a k ∧ O.Nc b (e k) = O.Nc a k ∧ O.gam b (e k) = O.gam a k

end Core

end GlobalTheory.ConjTwist
end
end

section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.UnitaryBC.ClassTransport
open scoped TensorProduct

namespace GlobalTheory.FormDict.Model

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

local notation3 "F₀" => maximalRealSubfield L

def kappa : AL L ≃+* FiniteAdeleRing (𝓞 L) L :=
  (Algebra.TensorProduct.comm F₀ L (FiniteAdeleRing (𝓞 F₀) F₀)).toRingEquiv.trans (GlobalTheory.LFun.finAdEquiv F₀ L)

theorem kappa_tmul (x : L) (a : FiniteAdeleRing (𝓞 F₀) F₀) :
    kappa L (x ⊗ₜ a) = GlobalTheory.AdeleBaseChange.adMap F₀ L a * algebraMap L _ x :=
  GlobalTheory.LFun.toFinAd_tmul a x

theorem kappa_conj (y : AL L) :
    kappa L (conjAL L y) = conjFin (IsCMField.complexConj L).toRingEquiv (kappa L y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul x a =>
    have hAd : conjFin (IsCMField.complexConj L).toRingEquiv
        (GlobalTheory.AdeleBaseChange.adMap F₀ L a) = GlobalTheory.AdeleBaseChange.adMap F₀ L a := by
      have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField L
      refine congrFun ((GlobalTheory.AdeleCharTwist.denseRange_fin (F := F₀)).equalizer
        ((continuous_conjFin _).comp (continuous_adMap F₀ L)) (continuous_adMap F₀ L)
        (funext fun k => ?_)) a
      simp only [Function.comp_apply]
      rw [GlobalTheory.AdeleBaseChange.adMap_algebraMap, conjFin_algebraMap]
      congr 1
      exact IsCMField.complexConj_apply_eq_self L k
    change kappa L ((IsCMField.complexConj L x) ⊗ₜ a) = _
    rw [kappa_tmul, kappa_tmul, map_mul, hAd, conjFin_algebraMap]
    rfl
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), map_add (f := _), hy, hz, map_add (f := _)]

def psi0 : GAf L n →* GL (Fin n) (FiniteAdeleRing (𝓞 L) L) :=
  (Matrix.GeneralLinearGroup.map (kappa L).toRingHom).comp (ReciprocityTheory.Aut.GA L n).subtype

theorem map_conjT (M : Matrix (Fin n) (Fin n) (AL L)) :
    (conjT (conjAL L) M).map (kappa L).toRingHom =
      Formalism.UG.cT (conjFin (IsCMField.complexConj L).toRingEquiv) (M.map (kappa L).toRingHom) :=
  Matrix.ext fun _ _ => kappa_conj L _

theorem unitaryFinitePointsToGLFiniteAdeles_isUnitary (x : GAf L n) :
    Formalism.UG.cT (conjFin (IsCMField.complexConj L).toRingEquiv) (psi0 L n x).val * (psi0 L n x).val = 1 := by
  have hx : x.1.val * conjT (conjAL L) x.1.val = 1 := x.2
  rw [mul_eq_one_comm] at hx
  change Formalism.UG.cT _ (x.1.val.map (kappa L).toRingHom) * x.1.val.map (kappa L).toRingHom = 1
  rw [← map_conjT, ← Matrix.map_mul, hx, Matrix.map_one _ (map_zero _) (map_one _)]

def j0 : GAf L n →* UA L n :=
  ((finGL L n).comp (psi0 L n)).codRestrict (UA L n) fun x => finGL_mem_UA _ (unitaryFinitePointsToGLFiniteAdeles_isUnitary L n x)

def finIso : FinIso L n where
  κ := kappa L
  left x := by rw [kappa_tmul, map_one, one_mul]
  right w v h := by
    have h' : w.under (𝓞 F₀) = v := HeightOneSpectrum.ext h
    subst h'
    refine ⟨GlobalTheory.LFun.complMap (rfl : w.under (𝓞 F₀) = _), GlobalTheory.LFun.InertChart.continuous_complMap _, fun a => ?_⟩
    rw [kappa_tmul, map_one, mul_one]
    rfl
  j := j0 L n
  fin x := MonoidHom.mem_ker.2 (pInf_finGL (psi0 L n x))
  loc x w s t := by
    have h : Matrix.GeneralLinearGroup.map (pFin L) (j0 L n x).1 = psi0 L n x := pFin_finGL _
    have h2 := congrArg (fun g : GL (Fin n) (Af L) => pLoc L w (g.val s t)) h
    exact h2
  onto g hgf := by
    have hg := g.2
    change Formalism.UG.cT (conjAd L) g.1.val * 1 * g.1.val = 1 at hg
    rw [Matrix.mul_one] at hg
    have hf : Formalism.UG.cT (conjFin (IsCMField.complexConj L).toRingEquiv)
        (Matrix.GeneralLinearGroup.map (pFin L) g.1).val * (Matrix.GeneralLinearGroup.map (pFin L) g.1).val = 1 := by
      have h := congrArg (fun M => M.map (pFin L)) hg
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
      exact h
    let u := Matrix.GeneralLinearGroup.map (kappa L).symm.toRingHom (Matrix.GeneralLinearGroup.map (pFin L) g.1)
    have hU : u.val.map (kappa L).toRingHom = (Matrix.GeneralLinearGroup.map (pFin L) g.1).val :=
      Matrix.ext fun i j => (kappa L).apply_symm_apply _
    have hmem : u ∈ ReciprocityTheory.Aut.GA L n := by
      change u.val * conjT (conjAL L) u.val = 1
      rw [mul_eq_one_comm]
      refine Matrix.map_injective (kappa L).injective ?_
      change Matrix.map _ (kappa L).toRingHom = Matrix.map 1 (kappa L).toRingHom
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), map_conjT, hU]
      exact hf
    refine ⟨⟨u, hmem⟩, Subtype.ext (ga_ext ?_ ?_)⟩
    · exact (pInf_finGL _).trans (MonoidHom.mem_ker.1 hgf).symm
    · exact (pFin_finGL _).trans (Units.ext hU)

variable {L n}

theorem kappa_eq (F G : FinIso L n) : F.κ = G.κ := by
  refine RingEquiv.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz]
  | tmul x a =>
    have e : x ⊗ₜ[F₀] a = (x ⊗ₜ[F₀] (1 : AFplus L)) * ((1 : L) ⊗ₜ[F₀] a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, F.left, G.left]
    congr 1
    refine FiniteAdeleRing.ext _ fun w => ?_
    obtain ⟨i, hi, h1⟩ := F.right w (w.under (𝓞 F₀)) rfl
    obtain ⟨i', hi', h2⟩ := G.right w (w.under (𝓞 F₀)) rfl
    have key : ∀ k : F₀, (1 : L) ⊗ₜ[F₀] (algebraMap F₀ (AFplus L) k) = (k : L) ⊗ₜ[F₀] (1 : AFplus L) := fun k => by
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
      rfl
    have : (i : _ → _) = i' := (HeightOneSpectrum.denseRange_algebraMap F₀ (w.under (𝓞 F₀))).equalizer hi hi'
      (funext fun k => by
        have a1 := h1 (algebraMap F₀ _ k)
        have a2 := h2 (algebraMap F₀ _ k)
        rw [key, F.left] at a1
        rw [key, G.left] at a2
        exact a1.symm.trans a2)
    change F.κ (1 ⊗ₜ a) w = G.κ (1 ⊗ₜ a) w
    rw [h1, h2, this]


end GlobalTheory.FormDict.Model

end
end
