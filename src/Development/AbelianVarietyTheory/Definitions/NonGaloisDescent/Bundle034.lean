module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
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

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
open Formalism.L2.Host (embLL0)
open scoped TensorProduct




namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Scale

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks)

def IsScaleAt {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) (u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ)
    (c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (Rl.cV j).W) (c : ℂ) : Prop :=
  ∀ F : VV D.what₂.LL (FWT.lamV D j),
    harmFn (Wc D j).rank B.w B.F.BS (Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0 F)) =
      c • coefFn D.what₂.embLL (FWT.lamV D j) (F : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)

variable {Rl}

theorem IsScaleAt.ioP_eq {j : Fin D.R.m} {B : Base (Vc D j) (Wc D j)} {u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ}
    {c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (Rl.cV j).W} {c : ℂ} (h : IsScaleAt Rl B u c0 c)
    {H : Submodule ℂ (PolF D (Wc D j).rank (Vc D j).rank)}
    (hinj : ∀ P ∈ H, harmFn (Wc D j).rank B.w B.F.BS P = 0 → P = 0)
    {F : VV D.what₂.LL (FWT.lamV D j)} {P : PolF D (Wc D j).rank (Vc D j).rank} (hP : P ∈ H)
    (hio : Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0 F) ∈ H)
    (hPF : harmFn (Wc D j).rank B.w B.F.BS P =
      coefFn D.what₂.embLL (FWT.lamV D j) (F : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)) :
    Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0 F) = c • P :=
  sub_eq_zero.1 (hinj _ (H.sub_mem hio (H.smul_mem c hP)) (by rw [map_sub, map_smul, h F, hPF, sub_self]))

theorem RealPin.phase_mul_thetaKO {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw} (h : RealPin Rl cG ρ) (i : D.ntw.Tw)
    {j : Fin D.R.m} (b : Bool) {u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ} {w : (Rl.cV j).W}
    {P : PolF D (Wc D j).rank (Vc D j).rank} {c : ℂ} (hP : Rl.ioP j (PiTensorProduct.tprod ℂ u) w = c • P) (ph : ℂ)
    (om : PairRep (Vc D j) (Wc D j)) (s : GA D (Vc D j)) (f : WO (Vc D j) (Wc D j) → ℂ) :
    (fun g => ph * thetaKO om s g (harmVec Rl.toRealDat j u w f)) = (ph * c) • series (ρ.B i j b).F om f s P := by
  have e : harmVec Rl.toRealDat j u w f = (ρ.B i j b).F.fock f (c • P) := by
    rw [← hP, GlobalTheory.ExportSeries.Frame.fock, h.psi, h.inf, h.cartT, h.onbT, funext (h.onbS i j b)]
    rfl
  rw [e, mul_smul, ← map_smul]
  rfl

end Scale

section Phase

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (j : Fin D.R.m) {σ : T.Q.c.F →+* ℂ}
  (hV : T.V ((j : ℕ) + 1) σ = Wc D j)


variable {T j hV} in
theorem isRat_mul {C : Cover T ((j : ℕ) + 1) σ} {κ : WeightFamilies.Wt D ((j : ℕ) + 1)} {φ : GA D (Wc D j) → ℂ} (h : IsRat T j hV C κ φ)
    {a : ℂ} (ha : a ∈ C.σ₂.fieldRange) : IsRat T j hV C κ fun g => a * φ g := by
  obtain ⟨φ', h1, rfl⟩ := h
  obtain ⟨x, rfl⟩ := ha
  refine ⟨C.σ₂ x • φ', GlobalTheory.CoverRead.Test.smul_mem_ratForms C _ _ x h1, ?_⟩
  have key : ∀ {V W : HSp D} (e : V = W) (z : ℂ) (ψ : GA D V → ℂ), castDict e (z • ψ) = fun g => z * castDict e ψ g := by
    rintro V _ rfl z ψ
    rfl
  exact key hV _ _


variable {T R j hV} in
theorem seriesRatOn_mul {C : Cover T ((j : ℕ) + 1) σ} {κ : WeightFamilies.Wt D ((j : ℕ) + 1)} {u : ∀ τ, lowT (R.MW j (sg0 D A)) τ}
    {c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV j).W} {ph : ℂ} (h : SeriesRatOn T R j hV C κ u c0 ph)
    {a : ℂ} (ha : a ∈ C.σ₂.fieldRange) : SeriesRatOn T R j hV C κ u c0 (a * ph) := by
  intro s hs f hf w hw
  obtain ⟨h1, h2⟩ := h s hs f hf w hw
  refine ⟨?_, fun δ δc hδ => ⟨fun dd hdd => ?_, fun om hom => ?_⟩⟩
  · simpa only [mul_assoc] using isRat_mul h1 ha
  · simpa only [mul_assoc, mul_left_comm a] using isRat_mul ((h2 δ δc hδ).1 dd hdd) ha
  · simpa only [mul_assoc] using isRat_mul ((h2 δ δc hδ).2 om hom) ha

def IsRatPhase (κ : WeightFamilies.Wt D ((j : ℕ) + 1)) (u : ∀ τ, lowT (R.MW j (sg0 D A)) τ)
    (c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV j).W) (ph : ℂ) : Prop :=
  ∀ C : Cover T ((j : ℕ) + 1) σ, GoodCover T R j C κ.n → (embLL0 D).fieldRange ≤ C.σ₂.fieldRange →
    SeriesRatOn T R j hV C κ u c0 ph

variable {T R j hV}

theorem IsRatPhase.mul {κ : WeightFamilies.Wt D ((j : ℕ) + 1)} {u : ∀ τ, lowT (R.MW j (sg0 D A)) τ}
    {c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV j).W} {ph : ℂ} (h : IsRatPhase T R j hV κ u c0 ph)
    {a : ℂ} (ha : a ∈ (embLL0 D).fieldRange) : IsRatPhase T R j hV κ u c0 (a * ph) :=
  fun C hC hL => seriesRatOn_mul (h C hC hL) (hL ha)

end Phase

section Scalar

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1))
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {j : Fin D.R.m}
  (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j) (B : Base (Vc D j) (Wc D j))

def IsRatScalar (ν : ℂ) : Prop :=
  ∃ gramR c0R c0L, Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) Rl.Q (labLL D)
      (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L ∧
    ∃ u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ, (∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j _ τ) ∧
      ∃ c ph : ℂ, c ≠ 0 ∧ ‖ph‖ = 1 ∧ ν = ph * c ∧ IsScaleAt Rl B u (c0L j) c ∧
        IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph

variable {T Rl κ v₀ hV B}

theorem IsRatScalar.intro {gramR c0R c0L} (h : Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) Rl.Q (labLL D)
      (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L) {u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ}
    (hu : ∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j _ τ) {c ph : ℂ} (hc : c ≠ 0) (hph : ‖ph‖ = 1)
    (hs : IsScaleAt Rl B u (c0L j) c) (hr : IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph) :
    IsRatScalar T Rl κ v₀ hV B (ph * c) :=
  ⟨gramR, c0R, c0L, h, u, hu, c, ph, hc, hph, rfl, hs, hr⟩

theorem IsRatScalar.isScale {ν : ℂ} (h : IsRatScalar T Rl κ v₀ hV B ν) :
    ∃ c ph : ℂ, c ≠ 0 ∧ ‖ph‖ = 1 ∧ ν = ph * c ∧ IsScale Rl v₀ B c := by
  obtain ⟨g, cR, cL, h0, u, hu, c, ph, h1, h2, h3, h4, -⟩ := h
  exact ⟨c, ph, h1, h2, h3, g, cR, cL, h0, u, hu, h4⟩

theorem IsRatScalar.ne_zero {ν : ℂ} (h : IsRatScalar T Rl κ v₀ hV B ν) : ν ≠ 0 := by
  obtain ⟨c, ph, h1, h2, rfl, -⟩ := h.isScale
  exact mul_ne_zero (fun e => by simp [e] at h2) h1

theorem IsRatScalar.mul {ν : ℂ} (h : IsRatScalar T Rl κ v₀ hV B ν) {a : ℂ} (ha : a ∈ (embLL0 D).fieldRange) (h0 : ‖a‖ = 1) :
    IsRatScalar T Rl κ v₀ hV B (a * ν) := by
  obtain ⟨g, cR, cL, h1, u, hu, c, ph, h2, h3, rfl, h4, h5⟩ := h
  exact ⟨g, cR, cL, h1, u, hu, c, a * ph, h2, by rw [norm_mul, h0, h3, one_mul], (mul_assoc _ _ _).symm, h4, h5.mul ha⟩

end Scalar

end GlobalTheory.SeriesTie

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct




namespace GlobalTheory.TwInputs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure RealSide (D : D7) : Type 1 where
  Γ : Type
  [grp : Group Γ]
  [fin : Fintype Γ]
  Pl0 : Type
  I0 : Type
  T : Type
  A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m
  core : Formalism.L2.Pj.CoreJ D
  [alg : Algebra core.Q.c.F D.what₂.LL]
  R : RealDat3 D A3 core.Q.c.F
  F : Face3 D A3
  cG : G0 R.Pg D.R.r ≃* G0g D.nd
  geo : GlobalTheory.RealGeo.GeoHalf core R.toRealDat fun _ => 1
  char : R.Char3 F
  phs : ∀ j, R.phs j = 1
  guard : FWT.QGuard R.toRealDat
  valKs : GlobalTheory.RealGeo.ValKs R.toRealDat
  idem : ∀ g, D.what₂.embLL ((idemOf A3.A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)
  unif : R.toRealDat.LUnif
  integral : R.toRealDat.LIntegral
  inGeo : GlobalTheory.RealGeo.InGeo geo
  finT : Finite T
  host : HostHyp D
  std : ∀ j, FWT.VStd D j
  size : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV

attribute [instance] RealSide.grp RealSide.fin RealSide.alg

variable {D : D7}

structure FieldOk (X : RealSide D) : Prop where
  galois : IsGalois ℚ ↥D.LL0
  star : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0
  vals : Formalism.L2.Host.ValLL0 D X.R.C
  ray : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange
  roots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange
  split : D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK

structure SerSide (X : RealSide D) (E : IntegralHeckeForms.XD D) : Type 1 where
  S : NX.RatDat D.ntw
  YS : NX.NExpRealS X.R X.cG S
  sup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b),
    x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b
  H : NX.NExpRealH X.R X.cG S YS
  reads : GlobalTheory.ExportPin.Reads X.R X.cG S YS H.hL
  del : ∀ i b P, P ∉ D.ntw.S0 i → ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
    H.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (algebraMap (D.ntw.O0 i) (D.ntw.O i)
      ((if b then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i))
  Z : ExportTie YS X.geo.v₀
  U_eq : ∀ g : X.Γ, X.cG (X.R.eG g) ∈ D.nexp.U ↔ g ∈ X.F.P0
  psi_eq : ∀ i b (g : X.F.P0) (h : X.cG (X.R.eG g) ∈ D.nexp.U),
    Z.ρ.e i b (D.nexp.psiU i b ⟨_, h⟩ : (FractionRing (D.ntw.O i))ˣ) = (D.what₂.embLL (X.F.ψ0 g : D.what₂.LLˣ))⁻¹
  low : ∀ i (P : PlE D.host), ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK * (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') : ℕ) :
    𝓞 D.host.E) ∈ P.asIdeal → P ∈ D.ntw.S0 i
  Sb : ∀ i, ∀ P ∈ X.R.Sb, P ∈ D.ntw.S0 i
  B_range : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, LinearMap.range (D.nexp.embB i j b) =
    D.nexp.Bsup i j b ⊓ (V0 D.nexp i j b).restrictScalars (D.ntw.O i)
  hk_emb : ∀ i j b k P (x : D.ntw.B i j b), 1 ≤ j → j ≤ D.R.m → HkIdx i k P →
    D.nexp.embB i j b (D.ntw.hk i j b k P x) = D.nexp.hkF i j b k P (D.nexp.embB i j b x)
  hk_split : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P →
    ((LinearMap.charpoly (D.ntw.hk i j b k P)).map (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)))).Splits
  off : OffRange D
  all : ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b a, a ∈ E.Dat0 i j b

def BaseTup {X : RealSide D} {E : IntegralHeckeForms.XD D} (Y : SerSide X E) (i : D.ntw.Tw) : Prop :=
  ∀ j b, ∃ t : X.T, X.R.xi t = (Y.Z.ρ.B i j b).de.chi ∧ X.R.Q t = (Y.Z.ρ.B i j b).de.Q

structure GalSide (D : D7) : Type 1 where
  wd : GlobalTheory.RowTie.WDTie D.nd D.naut
  lab : GlobalTheory.HeightCounting.LabTrue D wd
  cf : CharFrame D
  chr : GlobalTheory.HeightCounting.CharSide D cf
  triple : GlobalTheory.Triple.IsTriple D
  lam : GlobalTheory.LamTie.LamDat D
  lamOk : lam.Ok
  lamTie : GlobalTheory.LamTie.IsLamTie D.ntw lam
  rank : 100 ≤ D.R.r
  primes : ∀ k, 2 * D.R.r ≤ D.host.g k

section Abstract

variable {ρ : Setup D.ntw} (hρ : ρ.Good) (rd : Rds D.nexp ρ)

structure Laws : Prop where
  faithful : ∀ i j b, Faithful (rd i j b)
  act : ∀ i j b, ActRead (rd i j b)
  hecke : ∀ i j b, HeckeRead (rd i j b)
  rat : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, Rat hρ (rd i j b)

def XiType : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b Q M, InRange D.ntw i Q → ∀ s h P, ρ.IsDatum i j b s h P →
  (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a x, rd i j b x = ρ.xi i j b D.nexp Q M h P a →
    x ∈ Fm0 D.nexp i ((j : ℕ) + 1) b

def XiBdd : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b s h P, ρ.IsDatum i j b s h P → ∃ c : ℕ, ∀ Q M, InRange D.ntw i Q →
  (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a x, rd i j b x = ρ.xi i j b D.nexp Q M h P a →
    ((D.ntw.l i : D.ntw.O i) ^ c) • x ∈ D.nexp.Bsup i ((j : ℕ) + 1) b

def SpanGood (i : D.ntw.Tw) : Prop := ∀ (j : Fin D.R.m) b, ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b,
  rd i j b x ∈ Submodule.span ℂ {f | ∃ s h P, ρ.IsDatum i j b s h P ∧ f = ρ.theta i j b h P}

def SumOnto (i : D.ntw.Tw) : Prop := ∀ (j : Fin D.R.m) b, ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b,
  ∃ F ∈ Submodule.span ℂ (ρ.mt i j b 0 ∅ 1 : Set (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank)),
    rd i j b x = ρ.sum i j b 0 ∅ 1 F

end Abstract

structure Inputs (D : D7) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) : Prop where
  a1 : BlochKatoReduction.adm1 (BlochKatoReduction.bk0 D)
  a2 : BlochKatoReduction.adm2 D
  a8 : BlochKatoReduction.adm8 D
  good : AllGood D.nexp
  sig : D.nexp.sig_all
  a9 : BlochKatoReduction.adm9 D N0
  a10 : BlochKatoReduction.adm10 D
  univChar : GlobalTheory.UnivChar.IsUnivChar D.nexp
  off : OffRange D
  rel : ThURel D.nexp
  l3 : IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp
  t4 : IntegralHeckeForms.admT4 D.nexp E
  type : TypeKept E
  univ : UnivSup D E
  supG : SupG D
  supFull : SupFull D
  supHk : SupHk D
  commG : CommG D
  comm : HkComm D
  ss : HkSS D
  hyp : ∀ i, D.ntw.NonzeroIndexPlace i → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) i

end GlobalTheory.TwInputs

end
end
