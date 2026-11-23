module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ValRat
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.SatakeDualWeyl.Bundle001
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CuspRep ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem mem_integer_iff (x : w.adicCompletion E) : x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ Formalism.UG.Ov (F := E) w := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [Valuation.mem_integer_iff, ← map_one (valuation _), ← Valuation.vle_iff_le, Valuation.vle_iff_le Valued.v, map_one]
  rfl

theorem range_eq {K : Type} [Field K] {A B : Subring K} (h : A = B) (n : ℕ) :
    (Formalism.UG.bc (n := Fin n) B.subtype).range = (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap A K)).range := by
  subst h; rfl

theorem kgl_eq_ko (n : ℕ) : GlobalTheory.LFun.KGL w (n := n) = GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) :=
  range_eq (SetLike.ext fun x => mem_integer_iff w x) n

theorem isSpherical_of_hasSatGL (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {B : Multiset ℂˣ} (h : GlobalTheory.LFun.HasSatGL w ρ B) :
    GlobalTheory.SmGL.IsSpherical ρ := by
  have h1 := h.1
  unfold GlobalTheory.LGrp.IsSpherical at h1
  unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
  rwa [← kgl_eq_ko]

end GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel
end
end

section

noncomputable section

namespace GlobalTheory.TwV

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG
open scoped TensorProduct

def locSp {E : Type} [Field E] [NumberField E] (R : Type) {K : Type} [CommRing R] [Field K] [Algebra R K] (ρ : E →+* K) {N : ℕ}
    (L : Submodule (𝓞 E) (Fin N → E)) : Submodule R (Fin N → K) :=
  Submodule.span R ((fun (x : Fin N → E) k => ρ (x k)) '' (L : Set (Fin N → E)))

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}

def SplAlg (A : LocAt F E n G) : Prop :=
  ∀ v (x : (A.pl v).1.adicCompletion F), A.spl v ((1 : E) ⊗ₜ[F] x) = (x, x)

def LbAtB (A : LocAt F E n G) (Lb : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ v : Fin G.P.nV, locSp (G.P.W v) (A.iw v) Lb =
    colSpan (G.P.W v) ((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v))

def facQ (A : LocAt F E n G) (v : Fin G.P.nV) (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (G.P.Qq v) :=
  bc ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v) (bc (A.ph v) (bc (prV (E := E) (A.pl v).1) y))

def LatAdLoc (A : LocAt F E n G) (Lb : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v : Fin G.P.nV),
    locSp (G.P.W v) (A.iw v) (Formalism.L2.PairingIndexBounds.F.latAd y Lb) =
      (locSp (G.P.W v) (A.iw v) Lb).map (((facQ A v y : Matrix (Fin n) (Fin n) (G.P.Qq v)).mulVecLin).restrictScalars (G.P.W v))

end GlobalTheory.TwV

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Hk3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def labIn (n : ℕ) (s : List ℕ) : List ℤ :=
  s.map (fun a => (a : ℤ)) ++ List.replicate (n - 2 * s.length) 0 ++ (s.reverse.map fun a => -(a : ℤ))

def IsLabElt (V : HSp D) (P : Pl D.host.E) (d : List ℤ) (x : Bridge.Gf V) : Prop :=
  ∃ (e f : AE D) (ϖ : 𝓞 D.host.E) (α : GA D V), IsPrimeIdem P e f ∧ ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧ α ∈ GfC V ∧
    (x : GL _ _) = finHom V α ∧ SuppF V f α ∧ DivAt V e (ϖ : D.host.E) d α

def IsLocElt (V : HSp D) (P : Pl D.host.E) (x : Bridge.Gf V) : Prop :=
  ∃ (e f : AE D) (g : GA D V), IsPrimeIdem P e f ∧ g ∈ GfC V ∧ (x : GL _ _) = finHom V g ∧ SuppF V f g

def SphOp (V : HSp D) (P : Pl D.host.E) (d : List ℤ) (R : Finset (GA D V)) : Prop :=
  Hecke₂ V (KsphC V ∅) (fun _ => 1) ∅ P d R

def IsLab (V : HSp D) (P : Pl D.host.E) (d : List ℤ) : Prop := ∃ R, SphOp V P d R


open Classical in
def rep (V : HSp D) (P : Pl D.host.E) (d : List ℤ) : Finset (GA D V) :=
  if h : IsLab V P d then h.choose else ∅

def hyp (V : HSp D) (P : Pl D.host.E) : Set (GA D V) :=
  {k | k ∈ KsphC V ∅ ∧ ∃ e f, IsPrimeIdem P e f ∧ SuppF V f k}

def opOf {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (c : List ℤ →₀ ℂ) : Module.End ℂ M :=
  c.sum fun d z => z • ∑ γ ∈ rep V P d, π γ

def hk (V : HSp D) (P : Pl D.host.E) (c : List ℤ →₀ ℂ) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) :=
  c.sum fun d z => z • heckeLin V (rep V P d)

def hkF (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (c : List ℤ →₀ ℂ) (F : Bridge.Gf V → W) :
    Bridge.Gf V → W :=
  fun h => c.sum fun d z => z • ∑ γ ∈ rep V P d, F (h * (finHom V).rangeRestrict γ)

def dualC (c : List ℤ →₀ ℂ) : List ℤ →₀ ℂ := Finsupp.mapDomain dualLab c


open Classical in
def evC (V : HSp D) (P : Pl D.host.E) (a : List ℤ → ℂ) (c : List ℤ →₀ ℂ) : ℂ :=
  c.sum fun d z => if IsLab V P d then z * a d else 0

def splitC (n : ℕ) (z : ℕ → ℂ) : List ℤ →₀ ℂ := ∑ j ∈ Finset.range (n + 1), Finsupp.single (splitLab n j) (z j)

def UnrPl (P : Pl D.host.E) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ e f, IsPrimeIdem P e f → ∀ x : (AE D)ˣ, f * ((x : AE D) - 1) = (x : AE D) - 1 →
    finPart D (x : AE D) ∈ intAE D → finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1

def IsVacAt (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (P : Pl D.host.E) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ e f', IsPrimeIdem P e f' → ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True),
    IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f = f

section Pair

variable (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E)

def VacFix : Prop := ∀ f, IsVacAt ψ S T P f → ∀ k ∈ hyp S P, ∀ k' ∈ hyp T P, om (k, k') f = f

def Match (cS cT : List ℤ →₀ ℂ) : Prop :=
  ∀ f, IsVacAt ψ S T P f →
    opOf (om.comp (MonoidHom.inl _ _)) P cS f = opOf (om.comp (MonoidHom.inr _ _)) P cT f

def SphCorr : Prop :=
  VacFix ψ om P ∧ (∀ cT, ∃ cS, Match ψ om P cS cT) ∧ ∀ cS, ∃ cT, Match ψ om P cS cT

end Pair

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure Core (R : RealDat D A Ks) (F : Face D A) : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  chain : R.IsChain
  thP : R.IsThP

variable (R : RealDat D A Ks)

def Good (t : T) (P : Pl D.host.E) : Prop := ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P

def IsSF (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ v, v ∈ SF ↔ ∃ PP ∈ R.Pg, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal

def FixAll (t : T) (P : Pl D.host.E) : Prop :=
  (∀ k, k + 1 < D.R.m → VacFix R.ψ (R.ωY t k) P) ∧ VacFix R.ψ (R.ωX t) P ∧ ∀ i, VacFix R.ψ (R.ωP i t) P

def SchurAll : Prop :=
  (∀ t j, j < D.R.m → SchurMult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv)) (levChi _ (R.βY j) (R.datYt t j R.triv))
    (R.νY t j) (R.fdY t j)) ∧
  SchurMult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) R.ν0 R.fd0 ∧
  ∀ i, SchurMult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) (R.νW i) (R.fdW i)

def MatchE (t : T) (P : Pl D.host.E) (cX c0 : List ℤ →₀ ℂ) : Prop :=
  ∀ y y' : (R.HX t).H, (R.HX t).e y' = hkF D.sp.X' P cX ((R.HX t).e y) →
    R.HE.e (R.Th t y') = postOn (R.MY 0) (hk (Yc D 0) P c0) (R.HE.e (R.Th t y))

def MatchW (i : Fin D.R.m) (t : T) (P : Pl D.host.E) (cV cW : List ℤ →₀ ℂ) : Prop :=
  ∀ y y' : (R.HV i t).H, (R.HV i t).e y' = hkF (Vc D i) P cV ((R.HV i t).e y) →
    (R.HW i (sg0 D A)).e (R.thG i t y') = postOn (R.MW i (sg0 D A)) (hk (Wc D i) P cW) ((R.HW i (sg0 D A)).e (R.thG i t y))

def TwoSided (t : T) (P : Pl D.host.E) : Prop :=
  ((∀ cX, ∃ c0, MatchE R t P cX c0) ∧ ∀ c0, ∃ cX, MatchE R t P cX c0) ∧
    ∀ i, (∀ cV, ∃ cW, MatchW R i t P cV cW) ∧ ∀ cW, ∃ cV, MatchW R i t P cV cW

def EEc (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : Pl D.host.E → List ℤ → ℂ) : Submodule ℂ R.HE.H :=
  (partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF c).comap R.HE.e

def Wcc (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (i : Fin D.R.m) (c : Pl D.host.E → List ℤ → ℂ) :
    Submodule ℂ (R.HW i (sg0 D A)).H :=
  (R.Wat i (sg0 D A) R.triv ⊓
    partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF c).comap
      (R.HW i _).e

def eH (i : Fin D.R.m) : Module.End ℂ (R.HW i (sg0 D A)).H :=
  ∑ g, RealDat.eC (A := A) (sg0 D A) g • R.gW i (sg0 D A) g

def IsOpsE (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H) : Prop :=
  ∀ P, Good R A.μ0 P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (hk (Yc D 0) P c) (R.HE.e x)

def IsOpsW (i : Fin D.R.m) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HW i (sg0 D A)).H) : Prop :=
  ∀ P, Good R A.μ0 P → ∀ c x, (R.HW i _).e (h P c x) = postOn (R.MW i (sg0 D A)) (hk (Wc D i) P c) ((R.HW i _).e x)

def IsOpsX (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HX t).H) : Prop :=
  ∀ P, Good R t P → ∀ c x, (R.HX t).e (h P c x) = hkF D.sp.X' P c ((R.HX t).e x)

def IsOpsV (i : Fin D.R.m) (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i t).H) : Prop :=
  ∀ P, Good R t P → ∀ c x, (R.HV i t).e (h P c x) = hkF (Vc D i) P c ((R.HV i t).e x)

def NormalFam {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (ok : Pl D.host.E → Prop)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ H) : Prop :=
  (∀ P P', ok P → ok P' → ∀ c c', Commute (h P c) (h P' c')) ∧
    ∀ P, ok P → ∀ c, LinearMap.adjoint (h P c) = h P (dualC (Finsupp.mapRange star (star_zero ℂ) c))

end Real

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def locH (σ : L →+* L) (δ : L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L) : L :=
  δ * Matrix.trace (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (y.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * x)

structure LocPair (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ)
    {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M) : Prop where
  unr : Formalism.UG.IsUnramInv ϖ σ q
  odd : Odd q
  intS : JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L)
  intT : JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L)
  hermS : ∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i
  hermT : ∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i
  delta : Valued.v δ = 1 ∧ σ δ = -δ
  psi_int : ∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1
  psi_ne : ∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1
  rho_zero : ρ 0 = 1
  rho_mul : ∀ x y, ρ x * ρ y = ψ ((locH σ δ JS JT x y + σ (locH σ δ JS JT x y)) / 2) • ρ (x + y)
  span : Submodule.span ℂ {w | ∃ x s, (∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ u s = s) ∧ w = ρ x s} = ⊤
  norm : ∀ g h x, ω (g, h) * ρ x =
    ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x * (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) * ω (g, h)
  fix : ∀ (g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L)) (h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L)), (g : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    ∀ s, (∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ u s = s) → ω (g, h) s = s

def LocVac {n n' : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (s : M) : Prop :=
  ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ u s = s

end Local

end GlobalTheory.Hk3

end
end
