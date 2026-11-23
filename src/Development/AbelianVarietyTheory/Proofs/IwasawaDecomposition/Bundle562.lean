module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle384
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle059
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsReferenceTupleExtensionSpan
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle555
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle362
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle463
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle556
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle044
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle261

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open IsDedekindDomain NumberField

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem heckeFin : ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ)
    (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
    {χ : Formalism.L2.Host.HChar L | χ.HasInf φ n ∧ (∀ v, v ∉ S → χ.UnrAt v) ∧ ∀ v ∈ S, χ.LevelLe v N}.Finite :=
  GlobalTheory.LevelChars.heckeFin_of GlobalTheory.T.heckeChar_trivial_on_congruenceUnitIdeles GlobalTheory.T.rayClassGroup_idelic_finiteIndex

namespace KeyFiniteness

theorem levelLe_one_two {L : Type} [Field L] [NumberField L] {χ : Formalism.L2.Host.HChar L} {v : HeightOneSpectrum (𝓞 L)}
    (h : χ.LevelLe v 1) : χ.LevelLe v 2 := fun x hx hle =>
  h x hx (hle.trans (WithZero.exp_le_exp.2 (by norm_num)))

def Sv (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : Set (HeightOneSpectrum (𝓞 D.host.E)) :=
  {PP | (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v ∨ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ GlobalTheory.ChiGrid.S1 D}

def CS (D : D7) (c : ℝ) (v : HeightOneSpectrum (𝓞 D.host.F)) (a : Fin D.R.m) : Set (Formalism.L2.Host.HChar D.host.E) :=
  {χ | χ.HasInf (Formalism.L2.Host.embTau D) (fun τ => 2 * GlobalTheory.ChiGrid.cen D c τ (a.1 + 1)) ∧
      (∀ PP, PP ∉ Sv D v → χ.UnrAt PP) ∧ ∀ PP ∈ Sv D v, χ.LevelLe PP 2}

def Q0 (D : D7) : Set (HeightOneSpectrum (𝓞 D.host.F)) := {v | ((GlobalTheory.ChiGrid.q0 D : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}

def KS (D : D7) (c : ℝ) : Set (HeightOneSpectrum (𝓞 D.host.F) × HeightOneSpectrum (𝓞 D.host.E) × (Fin D.R.m → Formalism.L2.Host.HChar D.host.E)) :=
  ⋃ v ∈ Q0 D, {v} ×ˢ ({w | w.under (𝓞 D.host.F) = v} ×ˢ Set.pi Set.univ (CS D c v))

theorem KS_finite (D : D7) (c : ℝ) : (KS D c).Finite := by
  classical
  have hQ0 : (Q0 D).Finite := by
    refine (Formalism.L2.DIV.primesOf ((GlobalTheory.ChiGrid.q0 D : ℕ) : 𝓞 D.host.F)).finite_toSet.subset fun v hv => ?_
    exact Formalism.L2.DIV.mem_primesOf.2 ⟨Nat.cast_ne_zero.2 (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).1.ne_zero, hv⟩
  have hSv : ∀ v, (Sv D v).Finite := fun v => by
    refine ((Formalism.L2.Host.finite_aboveF (L := D.host.E) D.host.F v).union
      ((GlobalTheory.ChiGrid.S1 D).finite_toSet.biUnion fun u _ => Formalism.L2.Host.finite_aboveF (L := D.host.E) D.host.F u)).subset ?_
    rintro PP (h | h)
    · exact Or.inl h
    · exact Or.inr (Set.mem_biUnion (Finset.mem_coe.2 h) rfl)
  exact hQ0.biUnion fun v _ => (Set.finite_singleton v).prod
    ((Formalism.L2.Host.finite_aboveF (L := D.host.E) D.host.F v).prod
      (Set.Finite.pi fun a => heckeFin _ _ _ _ _ 2 (hSv v)))

theorem mem_KS {X : Stages} {T : Type} {L : Formalism.IndefR.Links.LevCh X.toD7 T} {sc : GlobalTheory.ChiGrid.Consts}
    (G : GlobalTheory.ChiGrid.GridData L sc) : gkeyOf G ∈ KS X.toD7 sc.cGap := by
  refine Set.mem_biUnion (x := G.pl.v0) G.pl.basePlace_over_qZero ⟨rfl, G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl)), fun a _ => ?_⟩
  have h1 : 1 ≤ a.1 + 1 := by omega
  have h2 : a.1 + 1 ≤ X.toD7.R.m := a.2
  refine ⟨G.ch.inf _ h1 h2, fun PP hPP => G.ch.unr _ h1 h2 PP fun h => hPP ?_, fun PP hPP => ?_⟩
  · rcases G.pl.mem_S0_of_sum_eq.1 h with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rcases hPP with h | h
    · exact levelLe_one_two (G.ch.lev0 _ h1 h2 PP h).1
    · exact (G.ch.lev1 _ h1 h2 PP h).1

theorem KS_transfer (X X₀ : Stages) (h : X.B.toPre = X₀.B.toPre) (c : ℝ) :
    ∀ κ ∈ KS X.toD7 c, ∃ κ' ∈ KS X₀.toD7 c, HEq κ κ' := by
  obtain ⟨⟨P1⟩, C1, W1, V1, S1', N1, G1⟩ := X
  obtain ⟨⟨P0⟩, C0, W0, V0, S0, N0, G0⟩ := X₀
  change P1 = P0 at h
  subst h
  exact fun κ hκ => ⟨κ, hκ, HEq.rfl⟩

end KeyFiniteness

open KeyFiniteness in
theorem gKeyFin : GKeyFin := by
  intro P c
  by_cases hP : ∃ X : Stages, X.B.toPre = P
  swap
  · exact ⟨∅, Set.finite_empty, fun X _ _ _ _ h _ => (hP ⟨X, h⟩).elim⟩
  obtain ⟨X₀, rfl⟩ := hP
  refine ⟨KS X₀.toD7 c, KS_finite _ _, ?_⟩
  rintro X T L sc G hX rfl
  exact KS_transfer X X₀ hX _ _ (mem_KS G)

end GlobalTheory.Mem.LiteralAutomorphy
end

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem evLgG_gridA_of_exGrid : ExGrid → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → EvLgG (GridA CF) := by
  classical
  intro h
  obtain ⟨CF0, hCF⟩ := h
  refine ⟨CF0, fun CF hC => ?_⟩
  refine ⟨1 / 100, by norm_num, fun eps C8 C5 c6 Cb _ _ _ _ => ?_⟩
  obtain ⟨x₀, hx⟩ := hCF eps CF hC
  refine ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ => ⟨0, fun cD _ => ⟨0, fun ch _ =>
    ⟨x₀, fun K _ _ _ hKe hKx _ => ?_⟩⟩⟩⟩
  have hS := fun (P : Pre) (f : Fr P) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) (hΞ : Ξ.Finite) =>
    hx K.s hKe hKx P f Ξ hΞ
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
    fun P f _ _ Ξ => if hΞ : Ξ.Finite then Classical.choose (hS P f Ξ hΞ) else ∅, ?_, ?_, ?_⟩
  · intro B f F z hz
    simp at hz
  · intro B f F F₀ Ξ z hz
    by_cases hΞ : Ξ.Finite
    · simp only [dif_pos hΞ] at hz
      exact (Classical.choose_spec (hS B f Ξ hΞ)).1 z hz
    · simp [dif_neg hΞ] at hz
  · intro B f T _ hHas _ _ C W V S N G
    have hfin := (GlobalTheory.Mem.Top.TwFin.tw_fin B f T).1
    have hspec := (Classical.choose_spec (hS B.toPre f (T.set f) hfin)).2
    refine hspec ⟨B, C, W, V, S, N, G⟩ f (T.set f) rfl HEq.rfl HEq.rfl ?_
    intro z hz
    have h2 := hHas.2 z
    simp only [dif_pos hfin] at h2
    exact h2 hz

end GlobalTheory.Mem.LiteralAutomorphy
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.HeightCounting.Up.GapAllStates

theorem gapR_allSt : AllSt fun _ _ _ _ _ _ x => ∀ (τ : (Dof x).what₂.Tau) (n : ℕ), n + 1 < (Dof x).R.r →
    100 * ((Dof x).R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt ((Dof x).hc τ) n - Formalism.L2.NTheta.lamAt ((Dof x).hc τ) (n + 1) :=
  Step.of_evG (EvG.imp (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)
    fun _ _ _ _ _ hK _ _ _ hO _ _ _ w _ _ x => (hK (w.st x.o.Z) hO).1.gapR)

end GlobalTheory.HeightCounting.Up.GapAllStates
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
  GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option genInjectivity false
set_option genSizeOfSpec false


namespace GlobalTheory.HeightCounting.RatSide

section Clauses

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def HeckeRd (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (Sb : Finset (PlE D.host))
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL ((ratDatR R cG kKs hk).WL j)) : Prop :=
  ∀ j k P α Rr, 1 ≤ j → j ≤ D.R.m → HkDat R Sb (idxOf D j) k P α Rr → ∀ x : Fin (R.nW (idxOf D j)) → D.what₂.LL,
    (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) (hL j k P x)) =
      hkNorm R (idxOf D j) k P • heckeOn (R.MW (idxOf D j) (sg0 D A3.A)) Rr
        ((R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x))

def LvlPsi (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) : Prop :=
  (∀ g : G, g ∈ F.P0 ↔ (R.eG.trans cG) g ∈ Formalism.IndefR.NX.U D.nd) ∧
    ∀ (u : F.P0) (hu : (R.eG.trans cG) u ∈ Formalism.IndefR.NX.U D.nd),
      (((psiUOf D.nd (NX.xiRed D) θ ⟨_, hu⟩ : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) = (((F.ψ0 u)⁻¹ : D.what₂.LLˣ) : D.what₂.LL)

end Clauses

section Rat

variable {D : D7}

def FormsC (S : RatDat D.ntw) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm ∧ FiniteDimensional S.Ks (FmK S j) ∧
    ∃ T : Finset (S.WL j), (∀ x ∈ T, x ∈ (S.A j).MK) ∧
      (∀ x ∈ (S.A j).MK, x ∈ (S.A j).WK ∧ x ∈ Submodule.span (𝓞 S.Ks) (T : Set (S.WL j))) ∧
      ∀ x ∈ (S.A j).WK, x ∈ Submodule.span S.Ks (T : Set (S.WL j))

def StabC (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ k P (x : S.WL j), x ∈ (S.A j).WK → hL j k P x ∈ (S.A j).WK

def IntC (S : RatDat D.ntw) (Sb : Finset (PlE D.host)) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) : Prop :=
  ∀ j k P, 1 ≤ j → j ≤ D.R.m → IsSplitPl D.host P → P ∉ Sb → k ≤ D.R.r → ∃ n : ℕ,
    ∀ x ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j)), x ∈ goodL D S θ j →
      (normV P) ^ n • hL j k P x ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j))

def SpanC (S : RatDat D.ntw) (Sb : Finset (PlE D.host)) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → goodL D S θ j ≤
    ⨆ σ ∈ {σ | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ}, goodL D S θ j ⊓ ⨅ (k : ℕ) (P : PlE D.host)
      (_ : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ Sb), Module.End.eigenspace (hL j k P) ((eig j σ k P : ↥D.LL0) : D.what₂.LL)

def lowSet (D : D7) : Set (PlE D.host) := {v | ∃ p ∈ lowAll D, p ≠ 0 ∧ ((p : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal}

theorem lowSet_finite (D : D7) : (lowSet D).Finite := by
  refine Set.Finite.subset (Set.Finite.biUnion (s := (((lowAll D).filter (· ≠ 0) : Finset ℕ) : Set ℕ)) (Finset.finite_toSet _)
    fun p hp => GlobalTheory.RowTie.placesOver_finite_of_ne_zero D.host.E p (Finset.mem_filter.1 hp).2) ?_
  rintro v ⟨p, hp, hp0, hv⟩
  exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hp, hp0⟩)) hv

def SbD (D : D7) : Finset (PlE D.host) := (lowSet_finite D).toFinset

theorem overSet_SbD (D : D7) : OverSet D (SbD D) (lowAll D) := by
  intro v hv
  obtain ⟨p, hp, -, hv⟩ := (lowSet_finite D).mem_toFinset.1 hv
  exact ⟨p, hp, hv⟩

end Rat

section State

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

def kKsOf (x : St P) : x.m.z.core.Q.c.F →+* ↥(Dof x).LL0 :=
  (algebraMap x.m.z.core.Q.c.F (Dof x).what₂.LL).codRestrict (Dof x).LL0 x.m.z.fieldValues_mem_fixedField

theorem hkOf (x : St P) (y : x.m.z.core.Q.c.F) :
    ((kKsOf x y : ↥(Dof x).LL0) : (Dof x).what₂.LL) = algebraMap x.m.z.core.Q.c.F (Dof x).what₂.LL y := rfl

abbrev SOf (x : St P) : RatDat (Dof x).ntw := ratDatR x.m.z.R x.m.z.cG (kKsOf x) (hkOf x)

end State

end GlobalTheory.HeightCounting.RatSide
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

theorem _root_.GlobalTheory.T.integralForms_referenceTuple_extension_span : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX
            (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T'
            {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX'
            (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (a
            : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg
            z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a
            • f) = φ a • L f) → (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L
            j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d
            : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X :=
            B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d'
            : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X :=
            B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) +
            1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ)
            ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X
            := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j'
            : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel
            (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1
            hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px)
            B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v
            | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD
            (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I
            (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) +
            1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F
            (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j'
            : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ)
            ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X :=
            B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr
            := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T
            Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts
            w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) +
            1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F
            (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) +
            1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X :=
            B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) → ∀ f' : ((famR
            (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg
            z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v
            | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms, (∀ c, (f' : ((famR (w'.st
            Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j'
            (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg
            z'.tr).A.μ0).S.Cl → ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v
            | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX'
            (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.V) c ∈ ((famR
            (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg
            z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v
            | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Nab c) ↔ f' ∈ Submodule.span (𝓞
            (w'.st Z').toD7.what₂.LL) (L '' {f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg
            z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg
            z.tr).A.μ0).S.Forms | ∀ c, (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg
            z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Cl → ((famR
            (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf
            w.I T Wt) z.Xg z.tr).A.μ0).S.V) c ∈ ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg
            z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg
            z.tr).A.μ0).S.Nab c})) := by
  first | exact @GlobalTheory.Mem.R3.DefLatBC.nab_ext | exact GlobalTheory.Mem.R3.DefLatBC.nab_ext | (intros; apply GlobalTheory.Mem.R3.DefLatBC.nab_ext <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

noncomputable section

namespace GlobalTheory.Mem.R3.IsotIndep

theorem gaL_finSum {D : D7} {G : Type} [Group G] [Fintype G] (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (eG : G ≃* G0 L.Pg L.r) (c0 : G → ℂ) :
    ∃ (s : Finset (GA D V)) (c : GA D V → ℂ), (∀ g ∈ s, g ∈ GfC V) ∧
      gaL V β L eG c0 = ∑ g ∈ s, c g • principalLevelFrame.rtA g := by
  classical
  let k : G → GA D V := fun g => if hx : ∃ κ, IsLevelLift V β L (eG g) κ then hx.choose else 1
  let a : G → ℂ := fun g =>
    if hx : ∃ κ, IsLevelLift V β L (eG g) κ then c0 g * (levChi V β (flagL L) hx.choose)⁻¹ else 0
  have hk : ∀ g, c0 g • actL V β L (eG g) = a g • principalLevelFrame.rtA (k g) := by
    intro g
    apply LinearMap.ext
    intro F
    funext h
    by_cases hx : ∃ κ, IsLevelLift V β L (eG g) κ
    · have e1 : a g = c0 g * (levChi V β (flagL L) hx.choose)⁻¹ := dif_pos hx
      have e2 : k g = hx.choose := dif_pos hx
      rw [e1, e2]
      show c0 g * actG0 V β L (eG g) F h = c0 g * (levChi V β (flagL L) hx.choose)⁻¹ * F (h * hx.choose)
      unfold actG0
      rw [dif_pos hx, mul_assoc]
    · have e1 : a g = 0 := dif_neg hx
      rw [e1, zero_smul]
      show c0 g * actG0 V β L (eG g) F h = 0
      unfold actG0
      rw [dif_neg hx]
      simp
  refine ⟨Finset.univ.image k, fun x => ∑ g ∈ Finset.univ.filter (fun g => k g = x), a g, ?_, ?_⟩
  · intro x hx
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hx
    by_cases h : ∃ κ, IsLevelLift V β L (eG g) κ
    · have e2 : k g = h.choose := dif_pos h
      rw [e2]
      exact h.choose_spec.1
    · have e2 : k g = 1 := dif_neg h
      rw [e2]
      exact one_mem _
  · have e0 : gaL V β L eG c0 = ∑ g, a g • principalLevelFrame.rtA (k g) := by
      unfold gaL
      exact Finset.sum_congr rfl fun g _ => hk g
    rw [e0]
    symm
    calc ∑ x ∈ Finset.univ.image k, (∑ g ∈ Finset.univ.filter (fun g => k g = x), a g) • principalLevelFrame.rtA x
        = ∑ x ∈ Finset.univ.image k, ∑ g ∈ Finset.univ.filter (fun g => k g = x), a g • principalLevelFrame.rtA (k g) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun g hg => ?_
          rw [(Finset.mem_filter.1 hg).2]
      _ = ∑ g, a g • principalLevelFrame.rtA (k g) :=
          Finset.sum_fiberwise_of_maps_to (fun g _ => Finset.mem_image_of_mem k (Finset.mem_univ g)) _



theorem isot_iSupIndep : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ i : Fin D.R.m, iSupIndep (fun σ : D.what₂.FT => D.what₂.isot ((i : ℕ) + 1) σ) := by
  intro hW hDS hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hHost i
  have hI : Inputs D := GlobalTheory.T.linksAnalyticHypotheses_of_weilRep_harishChandra hW hDS hHC hCR D
  have hB := hP.char.base
  have hT := Y.tied.lift
  have h0 := hB.models.νW i
  have hs := GlobalTheory.HilbertLevels.scaled (inv_pos.2 (GlobalTheory.HilbertLevels.nP_pos F.lv2 false)) h0.1.1 h0.2
  have hO := (GlobalTheory.T.rowFiniteTypes_isotypicParts_span_orthogonal D (Wc D i) _ R.θ (R.MW i (sg0 D A3.A)) (Y.PW i) Y.hF (R.βW i)
    (R.datWp i (R.levL F.lv2 false (sg0 D A3.A))) (R.eWf i (sg0 D A3.A)) _ (R.fdW i) hI (D.sp.W_sig _)
    hB.models.inf (Y.stdPsi.2 i) hs.1 hs.2 (gaL_finSum _ _ _ _ _)).2
  apply OrthogonalFamily.independent
  rw [orthogonalFamily_iff_pairwise]
  intro σ σ' hne
  rw [Function.onFun, Submodule.isOrtho_iff_inner_eq]
  intro u hu v hv
  have hu' := (hT.isot i σ u).1 hu
  have hv' := (hT.isot i σ' v).1 hv
  rw [Y.prtWE] at hu' hv'
  obtain ⟨a, ha, hau⟩ := hu'
  obtain ⟨b, hb, hbv⟩ := hv'
  have hni : ¬ (principalLevelFrame.rowRepR R.θ (Y.eFT σ)).Iso (principalLevelFrame.rowRepR R.θ (Y.eFT σ')) := fun h =>
    hne (Y.eFT.injective (principalLevelFrame.rowRepR_inj R.θ _ _ h))
  have key := hO _ _ hni a ha b hb
  rw [hT.mj i u v]
  unfold LiftReal.ipWc ipMT
  rw [← hau, ← hbv]
  refine mul_eq_zero_of_right _ ?_
  refine Eq.trans ?_ key
  congr 1
  · exact LinearEquiv.symm_apply_apply _ a
  · exact LinearEquiv.symm_apply_apply _ b

end GlobalTheory.Mem.R3.IsotIndep
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_character_allCharts_furtherPlaces : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∃ ψ : (∀ v : Q, ↥(⨆ β', ((K β').lev.Uloc v.1).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)) →* ℂˣ, ∀ β (κ : (K β).lev.U) (z : ∀ v : Q, ↥(⨆ β', ((K β').lev.Uloc v.1).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)), (∀ v : Q, reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (z v).1 = bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1) → (∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ψ z := by
  first | exact @GlobalTheory.Mem.Col2.QChi.exists_chi_further | exact GlobalTheory.Mem.Col2.QChi.exists_chi_further | (intros; apply GlobalTheory.Mem.Col2.QChi.exists_chi_further <;> assumption)
end
