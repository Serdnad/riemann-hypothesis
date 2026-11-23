module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpFrame

open Formalism.CohomologicalDescent.DepthNonnegative

def Embeds (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam mu : ι → ℕ → ℕ) (ϖ : O) (Gm : Type) [AddCommGroup Gm]
    [Module (alg O N lam) Gm] : Prop :=
  ∃ ψ : Gm →+ (NablaT O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N mu))), Function.Injective ψ ∧
    (∀ (c : O) z, ψ (algebraMap O (alg O N lam) c • z) = c • ψ z) ∧
    (∀ g z y, ψ z = Submodule.Quotient.mk y → ψ (grpA O N lam g • z) = Submodule.Quotient.mk (grp O N mu g y)) ∧
    ∀ τ w (a : alg O N lam) (a' : Module.End O (NablaT O N mu)), IsProj O N lam τ w a → IsProj O N mu τ w a' →
      ∀ z y, ψ z = Submodule.Quotient.mk y → ψ (a • z) = Submodule.Quotient.mk (a' y)

def SubQ (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O) (Gm : Type) [AddCommGroup Gm]
    [Module (alg O N lam) Gm] : Prop :=
  ∃ (U : Submodule (alg O N lam) (NablaT O N lam)) (π : U →ₗ[alg O N lam] Gm), Function.Surjective π ∧
    ∀ (x : U) (y : NablaT O N lam), (x : NablaT O N lam) = ϖ • y → π x = 0

section Tests

variable (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O)




end Tests

theorem exists_intHom {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {J : Type} [Group J]
    (x : J →* GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) {β : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))} (hβ : β = 1)
    (h : ∀ κ, x κ ∈ Formalism.L2.DIV.St β) :
    ∃ y : J →* GL (Fin n) (Formalism.L2.Herm.intAf F E), ∀ κ a b, ((y κ).val a b : TensorProduct F E (Formalism.L2.Herm.Af F)) = (x κ).val a b := by
  subst hβ
  choose y hy using h
  have h2 : ∀ κ, Formalism.L2.DIV.intGL F E n (y κ) = x κ := fun κ => by simpa [Formalism.L2.DIV.frGL] using hy κ
  refine ⟨MonoidHom.mk' y fun κ κ' => Formalism.L2.DIV.intGL_injective (by rw [map_mul, h2, h2, h2, map_mul]), fun κ a b => ?_⟩
  exact congrArg (fun g : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)) => g.val a b) (h2 κ)

end GlobalTheory.ExpFrame

end

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts HidaSetting WInputsLink h0)
open GlobalTheory.ExpFrame

namespace GlobalTheory.ExpTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev presJ {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {K : Type} [Field K]
    [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (_ : Bridge.ClassPres ι S σ ρ J χ) : Subgroup G := J

abbrev presChi {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {K : Type} [Field K]
    [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι S σ ρ J χ) : presJ P →* ℂˣ := χ

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

def hkA (j : Fin D.R.m) (t : p.P.T) (i : (blk p j t).Pl × ℕ) : Finset (Bridge.Gf (Vc D j)) := (p.R.B.L j t).hecke.hA i

def levJ (j : Fin D.R.m) (t : p.P.T) : Subgroup (Bridge.Gf (Vc D j)) := presJ (K := D.what₂.LL) (p.R.B.L j t).pres

def levChi (j : Fin D.R.m) (t : p.P.T) : levJ p j t →* ℂˣ := presChi (p.R.B.L j t).pres

def plOf (j : Fin D.R.m) (t : p.P.T) (P : (blk p j t).Pl) : HeightOneSpectrum (𝓞 D.host.E) := p.R.pl ((blk p j t).pl P)

def matOf (j : Fin D.R.m) (g : Bridge.Gf (Vc D j)) :
    Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E) := g.1.val



structure Tied (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ} (F : Frame l D.what₂.Tau N) (e0 : D.what₂.LL →+* PadicAlgCl l)
    (ix : F.I → (blk p j t).Pl × ℕ) (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl l)) where

  rk : Fin N ≃o Fin (Vc D j).rank

  e : F.G ≃* Bridge.Gf (Vc D j)

  io : PadicAlgCl l ≃+* ℂ

  ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l)

  bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl l)

  sh : D.what₂.Tau → ℤ

  liftFrame_embedding_base : ∀ x, io (e0 x) = D.what₂.embLL x

  half : IsHalf inc

  lab : ∀ τ, inc τ = e0.comp (Links.labLL D τ) ∨ inc τ = cj (e0.comp (Links.labLL D τ))

  ev_rat : ∀ τ x, ev τ (1 ⊗ₜ[D.host.F] x) = inc τ x

  ev_int : ∀ τ (a : FiniteAdeleRing (𝓞 D.host.F) D.host.F), (∀ v, a v ∈ v.adicCompletionIntegers D.host.F) →
    ‖ev τ (a ⊗ₜ[D.host.F] 1)‖ ≤ 1

  rat : ∀ g, g ∈ F.Γ ↔ e g ∈ (Bridge.ratF (Vc D j)).range

  lev : ∀ g, g ∈ F.K ↔ e g ∈ levJ p j t

  kap : ∀ (κ : F.K) τ, (Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ)).val =
    ((bs τ)⁻¹).val * ((matOf j (e κ)).map (ev τ)).submatrix rk rk * (bs τ).val

  chi : ∀ (κ : F.K) (h : e κ ∈ levJ p j t),
    io (F.emb (F.chi κ) * ∏ τ, F.emb (F.kap κ τ).val.det ^ sh τ) * ((levChi p j t ⟨e κ, h⟩ : ℂˣ) : ℂ) = 1

  ix_inj : Function.Injective ix

  ix_range : ∀ i, i ∈ Set.range ix ↔ 1 ≤ i.2 ∧ i.2 ≤ N ∧ ((l : ℕ) : 𝓞 D.host.E) ∉ (plOf p j t i.1).asIdeal

  tr : ∀ i g, g ∈ F.tr i ↔ e g ∈ hkA p j t (ix i)

  cst : ∀ i, F.cst i = 1

theorem isHalf_lab {l : ℕ} [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) : IsHalf fun τ => e0.comp (Links.labLL D τ) := by
  let s : D.R.GG → (D.host.E →+* PadicAlgCl l) := fun g =>
    (e0.comp D.embE).comp (D.host.sigmaOf g : D.host.E →+* D.host.E)
  have hinj : Function.Injective s := fun g g' h =>
    (D.host.gal).symm.injective
      (AlgEquiv.ext fun x => (e0.comp D.embE).injective (RingHom.congr_fun h x))
  have hsurj : Function.Surjective s := by
    haveI := D.host.hostE_isGalois
    haveI : Finite (D.R.GG) := Finite.of_equiv _ (D.host.gal).toEquiv
    refine ((Nat.bijective_iff_injective_and_card s).2 ⟨hinj, ?_⟩).2
    rw [← Nat.card_congr (D.host.gal).toEquiv, IsGalois.card_aut_eq_finrank,
      Nat.card_eq_fintype_card, NumberField.Embeddings.card]
  have hcj : ∀ g, GlobalTheory.ExpFrame.cj (s g) = s (g * D.R.cc) := fun g => by
    ext x
    have h1 : IsCMField.complexConj D.host.E x = D.host.sigmaOf (D.R.cc) x := by
      apply D.host.φ₀.injective
      rw [IsCMField.complexEmbedding_complexConj]
      exact (D.host.conjE_apply D.host.φ₀ x).symm
    show (e0.comp D.embE) (D.host.sigmaOf g (IsCMField.complexConj D.host.E x)) = (e0.comp D.embE) (D.host.sigmaOf (g * _) x)
    rw [h1, Formalism.BasicNotions.Host.sigmaOf, Formalism.BasicNotions.Host.sigmaOf, Formalism.BasicNotions.Host.sigmaOf, map_mul]
    rfl
  refine ⟨fun τ τ' h => D.eTau.injective (Subtype.ext (hinj h)), fun τ τ' h => ?_, fun i => ?_⟩
  · have h1 := hinj ((hcj (D.eTau τ).1).symm.trans h)
    have hi := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau τ).2
    have hj := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau τ').2
    have h2 : (D.eTau τ').1.1.2 = (D.eTau τ).1.1.2 * (-1) := by rw [← h1]; rfl
    rw [hi, hj] at h2
    exact absurd h2 (by decide)
  · obtain ⟨g, rfl⟩ := hsurj i
    rcases Int.units_eq_one_or g.1.2 with hg | hg
    · refine ⟨D.eTau.symm ⟨g, (Formalism.HC.Frame.mem_Psi_iff _).2 hg⟩, Or.inl ?_⟩
      show s g = s (D.eTau (D.eTau.symm _)).1
      rw [Equiv.apply_symm_apply]
    · have hm : g * (D.R.cc)⁻¹ ∈ D.R.Psi := by
        refine (Formalism.HC.Frame.mem_Psi_iff _).2 ?_
        show g.1.2 * (-1)⁻¹ = 1
        rw [hg]; decide
      refine ⟨D.eTau.symm ⟨_, hm⟩, Or.inr ?_⟩
      show s g = GlobalTheory.ExpFrame.cj (s (D.eTau (D.eTau.symm _)).1)
      rw [Equiv.apply_symm_apply, hcj, inv_mul_cancel_right]

theorem levJ_eq (j : Fin D.R.m) (t : p.P.T) : levJ p j t = (levEnv (Vc D j) (p.R.βV j) (p.R.datVt j t)).J := rfl



omit p in
theorem mem_St_of_levEnv {V : Formalism.BasicNotions.TH.HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {Lv : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}
    {g : Bridge.Gf V} (h : g ∈ (levEnv V β Lv).J) : Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) g.1 ∈ St β := parLev_St h.1


omit p in
theorem exists_intHom_of {V : Formalism.BasicNotions.TH.HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} (hβ : β = 1) (J : Subgroup (Bridge.Gf V))
    (h : ∀ g ∈ J, Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) g.1 ∈ St β) :
    ∃ y : J →* GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E),
      ∀ κ a b, ((y κ).val a b : Formalism.IndefR.Lev.EAf D) = Formalism.IndefR.Lev.swapAE D (κ.1.1.val a b) :=
  exists_intHom ((Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D)).comp ((Bridge.Gf V).subtype.comp J.subtype)) hβ fun κ => h κ.1 κ.2

theorem exists_levInt (j : Fin D.R.m) (t : p.P.T) :
    ∃ y : levJ p j t →* GL (Fin (Vc D j).rank) (Formalism.L2.Herm.intAf D.host.F D.host.E),
      ∀ κ a b, ((y κ).val a b : Formalism.IndefR.Lev.EAf D) = Formalism.IndefR.Lev.swapAE D (matOf j κ.1 a b) :=
  exists_intHom_of (p.betaStd.1 j) (levJ p j t) fun _ h => mem_St_of_levEnv ((levJ_eq p j t).le h)



open Classical in
def FrameAt (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime], ∃ (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr) (R : Reads F W.lam (blk p j (p.R.mu w)) w)
    (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))), F.Ok ∧ Nonempty (Tied p j (p.R.mu w) F R.e0 R.ix inc)


open Classical in
def GalAt (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr) (R : Reads F W.lam (blk p j (p.R.mu w)) w)
    (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))), F.Ok → Tied p j (p.R.mu w) F R.e0 R.ix inc →
    GalSide (AlgebraicClosure D.host.E) inc P W F R.HasBlock

def SmallAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  (Formalism.EigenvalueLevelCeiling.plc w).Prime ∧ P.Nr + 1 < Formalism.EigenvalueLevelCeiling.plc w ∧ ¬ ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : ℤ) ∣ NumberField.discr D.host.E ∧
    (∀ i, subZ p j (p.R.mu w) ≤ (subZ p j (p.R.mu w)).comap ((blk p j (p.R.mu w)).op i)) ∧
    subZ p j (p.R.mu w) ≤ (blk p j (p.R.mu w)).ZH

end GlobalTheory.ExpTie

end
end

section



noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

namespace GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

structure HostNum (D : D7) (L : SizeData₂ D) (PP A M : ℝ) : Prop where
  big : M ≤ L.sc.L ∧ 10 ≤ L.sc.L ∧ L.sc.L ≤ L.sc.x ∧ 1 ≤ Real.log (Real.log L.sc.x)
  f8 : 8 ≤ D.R.f
  deg : Module.finrank ℚ D.host.E = 2 * D.R.f
  logfr : Real.log ((D.R.f : ℝ) * D.R.r) ≤ L.sc.L ∧ Real.log (D.R.nV : ℝ) ≤ L.sc.L
  logg : ∀ k, Real.log (D.host.g k : ℝ) ≤ 9 * L.sc.L + 1
  disc : Real.log |(discr D.host.E : ℝ)| ≤ 4 * D.R.f * L.sc.L
  logd : Real.log (D.host.d : ℝ) ≤ L.sc.L
  split : 5 ≤ D.host.splitBound
  cop : Nat.Coprime 15 (D.host.g 0 * D.host.g 1)
  ppLow : zBase L ^ 12 ≤ PP
  poly : 1 ≤ A ∧ PP ≤ L.sc.x ^ A ∧ (D.R.f : ℝ) * D.R.r * D.R.nV * L.sc.L ≤ L.sc.x ^ A
  room : (L.sc.x ^ A) ^ M ≤ L.sc.b
  low : Real.sqrt L.sc.b ≤ L.sc.w'' D.R.n

def wtsAt (PP : ℝ) (h0 : ℤ) (S eta : ℝ) (u1 : _root_.GlobalTheory.AllWt.Weight (dat p i)) :
    GlobalTheory.MeanTop.Wts (Psi p.T.Q.H) ((dat p i).p + (dat p i).q) :=
  { kc := D.R.k - 1, p := (dat p i).p, T := lenT p i PP, Dd := dimFlag (dat p i), c0 := cZero D ((i : ℕ) + 1), h0 := h0, S := S,
    eta := eta, b := 4 * L.sc.b, w := fun τ => (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ), u := uW p i, u1 := u1 }

theorem quo_iff (PP : ℝ) (h0 : ℤ) (S eta : ℝ) (u1 : _root_.GlobalTheory.AllWt.Weight (dat p i)) : Quo p i PP u1 ↔ (wtsAt p i PP h0 S eta u1).IsDiv :=
  Iff.rfl

structure WtNum (PP : ℝ) : Prop where
  sig : (dat p i).p = (D.R.sigW ((i : ℕ) + 1)).1 ∧ (dat p i).q = (D.R.sigW ((i : ℕ) + 1)).2 ∧ (dat p i).p + (dat p i).q = D.R.r
  card : Nat.card (Psi p.T.Q.H) = D.R.f
  dim : dimFlag (dat p i) = D.R.f * D.R.r.choose 2
  cols : (p.κ i).n = D.R.nV
  dom : Dom (wtA (p.κ i)) (p.κ i).n
  unit : unitE p = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x)
  om : |(ofRecord D L p.Del p.h0).logOm| ≤ 3 * L.sc.L
  up : ∀ τ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)| ≤ 4 * L.sc.b
  low : ∀ τ, L.sc.w'' D.R.n ≤ 2 * (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)
  what₂ : PP ^ 2 * D.R.r * D.R.m * D.R.k * (dimFlag (dat p i) : ℝ) ^ 3 ≤ L.sc.b ∧
    PP * lenT p i PP * (dimFlag (dat p i) : ℝ) ^ 2 * L.sc.L ≤ L.sc.b
  hyp : (i : ℕ) + 1 < D.R.m → ∃ (h0 : ℤ) (S eta : ℝ), 0 ≤ S ∧ 0 ≤ eta ∧ PP * (S + eta) ≤ 100 * L.sc.w'' D.R.n ∧
    4 * (lenT p i PP : ℤ) ^ 2 ≤ h0 ∧
    PP * lenT p i PP * D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * dimFlag (dat p i) ≤ h0 ∧
    ∀ u1, (wtsAt p i PP h0 S eta u1).Hyp

def HostN (M : ℝ) : Prop := Lifts fun Fm x _ ι _ _ PP A => HostNum (Fm.D x ι) (Fm.L x ι) PP A M

def WtN : Prop := Lifts fun _ _ _ _ p i PP _ => WtNum p i PP

end GlobalTheory.CovTop

end
end

section

set_option autoImplicit false


noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.RefSum

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) {c : Coeff l} {p : ℕ} [Fact p.Prime]

def FacBetween (la : PointsOfFlagModel.abelian₂ p c) (f : Lt1 Dw) (k : ℕ) (A B : ℝ) : Prop :=
  letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io,
    (A : EReal) ≤ nuFac p y f k ∧ (y.IsAlg → nuFac p y f k ≤ (B : EReal))

def NuBetween (la : PointsOfFlagModel.abelian₂ p c) (cx : Lt1 Dw → ℕ) (A B : ℝ) : Prop :=
  letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io,
    (A : EReal) ≤ nuP p y cx ∧ (y.IsAlg → nuP p y cx ≤ (B : EReal))


variable (c p) in
def OscLe (cx : Lt1 Dw → ℕ) (b : ℝ) : Prop :=
  ∀ la : PointsOfFlagModel.abelian₂ p c, ∃ A : ℕ, NuBetween Xo la cx A (A + b)


variable (Dw) in
def nCol : ℕ := 8 * ((∑ f : Lt1 Dw, 2 * rk f) / 8 + Fintype.card (Lt1 Dw) + 1)


variable (Dw) in
def shift (u : _root_.GlobalTheory.AllWt.Weight Dw) (n : ℕ) (τ : Psi H) : ℤ :=
  ((n / 2 : ℕ) : ℤ) + 1 - if h : 0 < Dw.p then u τ ⟨Dw.p - 1, by omega⟩ else 0


variable (Dw) in
def thA (u : _root_.GlobalTheory.AllWt.Weight Dw) (n : ℕ) : (E →+* ℂ) × ℕ → ℕ :=
  fun x => ((wtOf Dw (u + GlobalTheory.FlatLine.parWt Dw (shift Dw u n)) ((n / 2 : ℕ) : ℤ)).1 x).toNat

theorem eight_dvd_nCol : 8 ∣ nCol Dw := Dvd.intro _ rfl

theorem sum_le_nCol : ∑ f : Lt1 Dw, 2 * rk f ≤ nCol Dw := by
  unfold nCol; omega

theorem OscLe.mono {cx : Lt1 Dw → ℕ} {b b' : ℝ} (h : OscLe Xo c p cx b) (hb : b ≤ b') : OscLe Xo c p cx b' := fun la => by
  obtain ⟨A, hA⟩ := h la
  exact ⟨A, fun T io e ho y => ⟨(hA T io e ho y).1, fun ha => ((hA T io e ho y).2 ha).trans
    (EReal.coe_le_coe_iff.2 (by linarith))⟩⟩

def PrimeSum (S : Finset ℕ) (e : ℕ → ℝ) (s : ℝ) : Prop :=
  (∀ q ∈ S, q.Prime) ∧ (∀ q, 0 ≤ e q) ∧ (∀ q ∉ S, e q = 0) ∧ ∑ q ∈ S, e q * Real.log q ≤ s

end Free

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

abbrev aOf (u1 : _root_.GlobalTheory.AllWt.Weight (dat p i)) : (D.host.E →+* ℂ) × ℕ → ℕ := thA (dat p i) u1 (nCol (dat p i))

abbrev GOf (u1 : _root_.GlobalTheory.AllWt.Weight (dat p i)) : WTZ D.host.E := wtZ (aOf p i u1) (nCol (dat p i))

def SumAt (PP C : ℝ) (u1 : _root_.GlobalTheory.AllWt.Weight (dat p i)) : Prop :=
  ∃ (S : Finset ℕ) (e : ℕ → ℝ) (s : ℝ), PrimeSum S e s ∧ lenT p i PP * s ≤ C * unitE p ∧
    ∀ (q : ℕ) [Fact q.Prime], (∀ k, q ≠ D.host.g k) →
      OscLe (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c q (gap (dat p i) (aOf p i u1)) (e q)

def RefAt {l : Level p.T.Q.H} {Xo : Moduli (dat p i) l} {c : Coeff l} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
    (G : WTZ D.host.E) (PP C : ℝ) : Prop :=
  ∃ (S : Finset ℕ) (e : ℕ → ℝ) (s : ℝ), PrimeSum S e s ∧ lenT p i PP * s ≤ C * unitE p ∧
    ∀ q : ℕ, q.Prime → refExp_vp U (1 / 2500) G q ≤ (e q : EReal)

end Point

end GlobalTheory.RefSum

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace GlobalTheory.BigTop.Fun.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

variable {p : PtAt ex Csz} {CF : ℝ} (d : FunIn p CF)

theorem N_eq : d.O.N = GlobalTheory.ChiGrid.bigN D := by
  have := D.R.two_le_m
  show D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) = D.R.k + D.R.m * (D.R.t + (D.R.r + 6) + 1)
  have : D.R.r + 6 = D.R.k + D.R.m + 5 := by unfold Ranks.r; omega
  rw [this]

theorem nr_eq : d.O.nr = GlobalTheory.ChiGrid.nRk D := by
  have := D.R.two_le_m
  show D.R.k + D.R.m = D.R.r + 1
  unfold Ranks.r; omega

theorem s_eq : d.O.s = GlobalTheory.ChiGrid.sLen D := by
  have := D.R.two_le_m
  show D.R.k + D.R.m + 5 = D.R.r + 6
  unfold Ranks.r; omega

theorem PPF_eq (C b : ℝ) : d.O.PPF C b = GlobalTheory.ChiGrid.sizeP D C b := by
  unfold FunData.PPF GlobalTheory.ChiGrid.sizeP
  rw [nr_eq]; rfl

theorem Lc_eq : d.O.Lc = GlobalTheory.ChiGrid.cloudLen D := by
  classical
  have h : Fintype.card D.what₂.Tau = D.R.f := D.what₂.card_Tau
  unfold FunData.Lc GlobalTheory.ChiGrid.cloudLen
  refine le_antisymm (Finset.sup_le fun τ hτ => ?_) (Finset.sup_le fun τ _ => ?_)
  · have hτ' : τ < Fintype.card D.what₂.Tau := h ▸ Finset.mem_range.1 hτ
    refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun τ =>
      ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 - (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k).toNat)
      (Finset.mem_univ ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, hτ'⟩)))
    show (cloud D τ 2 - cloud D τ D.R.k).toNat = _
    simp only [cloud, dif_pos hτ']
  · refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun τ => (d.O.cl τ 2 - d.O.cl τ d.O.k).toNat)
      (Finset.mem_range.2 (show ((Fintype.equivFin D.what₂.Tau τ : Fin _) : ℕ) < D.R.f from h ▸ (Fintype.equivFin D.what₂.Tau τ).2)))
    show _ = (cloud D _ 2 - cloud D _ D.R.k).toNat
    simp only [cloud, dif_pos (Fintype.equivFin D.what₂.Tau τ).2, Fin.eta, Equiv.symm_apply_apply]

theorem ga_eq (C : ℝ) : d.O.ga C = GlobalTheory.ChiGrid.gap D C := by
  unfold FunData.ga GlobalTheory.ChiGrid.gap
  rw [N_eq, nr_eq, s_eq, Lc_eq d]; rfl

theorem ee_eq (h : Ideal.absNorm d.G.pl.v0.asIdeal = GlobalTheory.ChiGrid.q0 D) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    d.O.ee CF p.Z.b v = d.G.pl.depth ⟨1, CF, p.Z.b⟩ v := by
  unfold FunData.ee GlobalTheory.ChiGrid.Places.depth GlobalTheory.ChiGrid.depth0
  rw [PPF_eq]
  have e : d.O.qq d.O.sv0 = GlobalTheory.ChiGrid.q0 D := h
  rw [e]
  by_cases hv : v = d.G.pl.v0
  · rw [if_pos hv]; exact if_pos hv
  · rw [if_neg hv]; exact if_neg hv

end GlobalTheory.BigTop.Fun.Model

namespace GlobalTheory.BigTop.Fun.FieldProbe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

end GlobalTheory.BigTop.Fun.FieldProbe

end
end
