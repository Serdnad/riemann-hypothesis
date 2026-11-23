module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle490
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle503
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle339
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalProductsTendstoFrameStabiliser
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle077
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle070
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle079
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipTopChain


open Classical in
theorem transport {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (k : ℕ)
    (P : Finset (Pl D.host.E)) (ψ : AddChar (AF D.host.F) ℂ) (e : AE D)
    {S S' : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛS' : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)}
    {X Y : LSp D} (hX : X = ⟨S, ΛS⟩) (hY : Y = ⟨S', ΛS'⟩)
    {βS : GL (Fin X.sp.rank) (EAf D)} {βT : GL (Fin Y.sp.rank) (EAf D)} {βS₀ : GL (Fin S.rank) (EAf D)}
    {βT₀ : GL (Fin S'.rank) (EAf D)} (h1 : HEq βS βS₀) (h2 : HEq βT βT₀)
    {f₀ g : WO X.sp Y.sp → ℂ} {f₀' g' : WO S S' → ℂ} (h3 : HEq f₀ f₀') (h4 : HEq g g')
    (ha : X.sp.rank = D.R.r + k * D.R.t) (hb : Y.sp.rank = D.R.r + (k + 1) * D.R.t)
    (ha' : S.rank = D.R.r + k * D.R.t) (hb' : S'.rank = D.R.r + (k + 1) * D.R.t)
    (Ω : Matrix (Fin S'.rank) (Fin S.rank) (EAf D) → ℂ)
    (hN : ∀ N, IsIntM N → Ω N = ∏ w ∈ P, stepFn L t w k
      ((N.map (cpt (D := D) w)).submatrix (Comparison₂.ixOf G t w hb') (Comparison₂.ixOf G t w ha')))
    (hθ : IsThetaAt ψ (symplO S S') (heisO ψ S S') e (latO S S' (ΛS : Set _) (ΛS' : Set _) fun _ => True) 1 f₀'
      (fun x => if IsHalf e x ∧ IsIntM (frMapO S S' βS₀ βT₀ x) then Ω (frMapO S S' βS₀ βT₀ x) else 0) g') :
    IsThetaAt ψ (symplO X.sp Y.sp) (heisO ψ X.sp Y.sp) e (latO X.sp Y.sp (X.lat : Set _) (Y.lat : Set _) fun _ => True) 1 f₀
      (fun x => if IsHalf e x ∧ IsIntM (Comparison₂.fr βT βS (x.map (toEAf D))) then
        ∏ w ∈ P, stepFn L t w k (((Comparison₂.fr βT βS (x.map (toEAf D))).map (cpt (D := D) w)).submatrix
          (Comparison₂.ixOf G t w hb) (Comparison₂.ixOf G t w ha)) else 0) g := by
  subst hX hY
  obtain rfl := eq_of_heq h1
  obtain rfl := eq_of_heq h2
  obtain rfl := eq_of_heq h3
  obtain rfl := eq_of_heq h4
  convert hθ using 2
  rename_i x
  by_cases h : IsHalf e x ∧ IsIntM (Comparison₂.fr βT βS (x.map (toEAf D)))
  · have h' : IsHalf e x ∧ IsIntM (frMapO S S' βS βT x) := h
    rw [if_pos h, if_pos h']
    exact (hN _ h.2).symm
  · have h' : ¬ (IsHalf e x ∧ IsIntM (frMapO S S' βS βT x)) := h
    rw [if_neg h, if_neg h']

end GlobalTheory.FlipTopChain

namespace GlobalTheory.FlipTopChain

theorem colY_eq_m {D : D7} {T : Type} (L : LevCh D T) : ∀ n, n = D.R.m → columnBlock L n = ⟨D.sp.X', L.ΛX⟩ := by
  rintro _ rfl; exact colY_m L

theorem colFrame_eq_m {D : D7} {T : Type} (L : LevCh D T) : ∀ n, n = D.R.m → HEq (colFrame L n) L.βX := by
  rintro _ rfl; exact colFrame_m L



theorem last_step_theta : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {large₂ : SizeData₂ D},
    HidaSetting large₂ R F → ∀ ch : Choice R, ch.Is → ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)) (hj : (j : ℕ) + 1 = D.R.m),
    HEq g (R.vX t) → ∃ e' : AE D, IsIdemSum e' (GlobalTheory.FlipTop.topPl R.toLevCh t) ∧
      IsThetaAt ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e' (latO (ch.G.pS (.mu t 0 j)) (ch.G.pT (.mu t 0 j)) (ch.G.latS (.mu t 0 j) : Set _) (ch.G.latT (.mu t 0 j) : Set _) fun _ => True) 1 (ch.rm.vT 0 j)
        (GlobalTheory.FlipTop.topFn ch.S.B t e' j (GlobalTheory.FlipTop.rank_col ch.G (by omega)) (GlobalTheory.FlipTop.rank_col ch.G (by omega))) g := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R F large₂ hS ch hch t j g hj hg
  obtain ⟨k, hk⟩ := j
  simp only at hj
  obtain rfl : k = D.R.m - 1 := by omega
  obtain ⟨-, e', he', hθ⟩ := hS.core.chain.vX t
  refine ⟨e', he', ?_⟩
  have hm : D.R.m - 1 < D.R.m := hk
  have hb' : D.sp.X'.rank = D.R.r + (D.R.m - 1 + 1) * D.R.t := by
    rw [hj]; exact D.sp.X'_rank
  have hN := (Comparison₂.local_factors ch.S.B t hS.core.lev).2.2 (D.R.m - 1) hm _ hb'
  have hchi : R.toLevCh.chi (D.R.m - 1 + 1) = R.toLevCh.chi D.R.m := by rw [hj]
  rw [hchi] at hN
  unfold GlobalTheory.FlipTop.topFn
  exact transport ch.G t (D.R.m - 1) _ ch.W.ψ e' (X := ch.G.node (.grid 0 (D.R.m - 1)))
    (Y := ch.G.node (.grid 0 (D.R.m - 1 + 1))) (colY_lt R.toLevCh hm) (colY_eq_m R.toLevCh _ hj)
    (colFrame_lt R.toLevCh hm) (colFrame_eq_m R.toLevCh _ hj) (hch.vac.2 _ hj) hg _ _ (Comparison₂.rank_Yc hm.le) hb' _ hN
    (hch.weil.ψ ▸ hθ)

end GlobalTheory.FlipTopChain

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.RatMoveJets

def RatCoord {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (g : GfC V)
    (U : Matrix.unitaryGroup (Fin V.rank) D.host.E) : Prop :=
  ∃ γ ∈ GQ V, finHom V γ = finHom V (g : GA D V) ∧
    Formalism.L2.Theta.mt V γ = (fr.1 * U.1 * (fr⁻¹ : GL (Fin V.rank) D.host.E).1).map (incA D)

section
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc}

def srcU : ∀ p : GlobalTheory.ChiGrid.Pair T, Matrix.unitaryGroup (Fin (G.V p.small).rank) D.host.E →
    Matrix.unitaryGroup (Fin (G.V p.big).rank) D.host.E → Matrix.unitaryGroup (Fin (G.pS p).rank) D.host.E
  | .chi _ _, _, U' => U'
  | .mu _ _ _, U, _ => U
  | .core _, _, U' => U'
  | .top _ _, U, _ => U

def tgtU : ∀ p : GlobalTheory.ChiGrid.Pair T, Matrix.unitaryGroup (Fin (G.V p.small).rank) D.host.E →
    Matrix.unitaryGroup (Fin (G.V p.big).rank) D.host.E → Matrix.unitaryGroup (Fin (G.pT p).rank) D.host.E
  | .chi _ _, U, _ => U
  | .mu _ _ _, _, U' => U'
  | .core _, U, _ => U
  | .top _ _, _, U' => U'

end

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def JetTh (ch : Choice R) (p : Pair T) (x : FinPt ch.G p.small) (y : FinPt ch.G p.big)
    (Θ : VC D (ch.G.pS p).rank (ch.G.pT p).rank → ℂ) : Prop :=
  ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ)

theorem jetKap_iff (ch : Choice R) (p : Pair T) (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ) :
    GlobalTheory.MovedKappaEx.JetKap ch p x y κ ↔ JetTh ch p x y (fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ)
      (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ)
        (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) :=
  Iff.rfl

end

end GlobalTheory.RatMoveJets
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.SplitMoveKappa

theorem qbar_of_root {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) : ζ ∈ TaylorLogMetric.Qbar := by
  have halg : IsAlgebraic ℚ ζ := by
    refine ⟨Polynomial.X ^ n - Polynomial.C 1, ?_, ?_⟩
    · exact Polynomial.X_pow_sub_C_ne_zero hn 1
    · simp [hζ]
  exact mem_algebraicClosure_iff.2 halg

theorem mod1All_root {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) : Mod1All ζ := by
  refine ⟨qbar_of_root hn hζ, fun σ => ?_⟩
  have h1 : (⟨ζ, qbar_of_root hn hζ⟩ : TaylorLogMetric.Qbar) ^ n = 1 := by ext; simpa using hζ
  have h2 : (σ ⟨ζ, qbar_of_root hn hζ⟩) ^ n = 1 := by rw [← map_pow, h1, map_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 (by rw [← norm_pow, h2, norm_one])

theorem lamC_mem {q : ℕ} [Fact q.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[q]) {x : ℂ} (h : x ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam x = lam ⟨x, h⟩ := dif_pos h

theorem unitAt_mul {q : ℕ} [Fact q.Prime] {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar)
    (ux : GlobalTheory.MovedKappaEx.UnitAt q x) (uy : GlobalTheory.MovedKappaEx.UnitAt q y) : GlobalTheory.MovedKappaEx.UnitAt q (x * y) := by
  intro lam
  have e : (⟨x * y, mul_mem hx hy⟩ : TaylorLogMetric.Qbar) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  have hx' := ux lam
  have hy' := uy lam
  rw [lamC_mem lam hx] at hx'
  rw [lamC_mem lam hy] at hy'
  rw [lamC_mem lam (mul_mem hx hy), e, map_mul, norm_mul, hx', hy', one_mul]

theorem unitAt_inv {q : ℕ} [Fact q.Prime] {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar)
    (ux : GlobalTheory.MovedKappaEx.UnitAt q x) : GlobalTheory.MovedKappaEx.UnitAt q x⁻¹ := by
  intro lam
  have e : (⟨x⁻¹, inv_mem hx⟩ : TaylorLogMetric.Qbar) = (⟨x, hx⟩ : TaylorLogMetric.Qbar)⁻¹ := rfl
  have hx' := ux lam
  rw [lamC_mem lam hx] at hx'
  rw [lamC_mem lam (inv_mem hx), e, map_inv₀, norm_inv, hx', inv_one]

theorem unitAt_root (q : ℕ) [Fact q.Prime] {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) :
    GlobalTheory.MovedKappaEx.UnitAt q ζ := by
  intro lam
  have h1 : (⟨ζ, qbar_of_root hn hζ⟩ : TaylorLogMetric.Qbar) ^ n = 1 := by ext; simpa using hζ
  have h2 : (lam ⟨ζ, qbar_of_root hn hζ⟩) ^ n = 1 := by rw [← map_pow, h1, map_one]
  rw [lamC_mem lam (qbar_of_root hn hζ)]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 (by rw [← norm_pow, h2, norm_one])

end GlobalTheory.SplitMoveKappa
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

namespace GlobalTheory.MovedKappaEx

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem



theorem mem_splitOff_of_suppSplit : ∀ {D : D7} (V : HSp D) (Q : Finset ℕ) (s : GfC V),
    GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) (∏ q ∈ Q, q) (finHom V s.1).1 → s ∈ GlobalTheory.MovedKappaEx.splitOff V Q := by
  classical
  intro D V Q s hs
  obtain ⟨g, hg⟩ := s
  let P : GA D V → Prop := fun x => ∃ h : x ∈ GfC V, (⟨x, h⟩ : GfC V) ∈ splitOff V Q
  have h1 : P 1 := ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
  have hmul : ∀ x y, P x → P y → P (x * y) := fun x y ⟨hx, mx⟩ ⟨hy, my⟩ =>
    ⟨Subgroup.mul_mem _ hx hy, Subgroup.mul_mem _ mx my⟩
  have hinj : Function.Injective (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D)) :=
    Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective
  obtain ⟨e₀, he1, he2, he3, he4⟩ := hs
  have heS : e₀ = GlobalTheory.LocalApprox.indA D.host.F he2.toFinset := by
    refine GlobalTheory.LocalApprox.af_ext _ fun w => ?_
    by_cases hw : w ∈ he2.toFinset
    · rw [GlobalTheory.LocalApprox.evalV_indA_of_mem _ hw]
      have hne : evalV D.host.F w e₀ ≠ 0 := he2.mem_toFinset.1 hw
      have h := congrArg (evalV D.host.F w) he1
      rw [map_mul] at h
      exact mul_left_cancel₀ hne (h.trans (mul_one _).symm)
    · rw [GlobalTheory.LocalApprox.evalV_indA_of_notMem _ hw]
      by_contra h
      exact hw (he2.mem_toFinset.2 h)
  have hsupp : ∀ i j, GlobalTheory.LocalApprox.idemE D he2.toFinset * (Formalism.L2.Theta.mt V g - 1) i j =
      (Formalism.L2.Theta.mt V g - 1) i j := by
    intro i j
    have e0 : GlobalTheory.LocalApprox.idemE D he2.toFinset = fj D e₀ := (congrArg (fj D) heS).symm
    rw [e0]
    refine GlobalTheory.UnitarySplit.parts_inj D _ _ ?_ ?_
    · have h5 : infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
        have h6 : (Formalism.L2.Theta.mt V g).map (infPart D) = 1 := congrArg Units.val (show infHom V g = 1 from hg)
        have h7 := congrFun (congrFun h6 i) j
        rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]
        refine h7.trans ?_
        by_cases e : i = j
        · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
      rw [RingHom.map_mul, h5, mul_zero]
    · have h5 : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = ((finHom V g).1 - 1) i j := by
        rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]
        congr 1
        by_cases e : i = j
        · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
      rw [RingHom.map_mul, h5]
      exact congrFun (congrFun he4 i) j
  have hgS : GlobalTheory.LocalApprox.cutAt V g he2.toFinset = g := by
    refine GlobalTheory.IdemSupport.mt_inj V ?_
    rw [GlobalTheory.LocalApprox.mt_cutAt]
    ext i j
    have h := hsupp i j
    rw [Matrix.sub_apply] at h
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    linear_combination h
  have hpl : ∀ v, pl D v = GlobalTheory.LocalApprox.idemE D {v} := fun v => by
    show fj D _ = fj D _
    congr 1
    refine GlobalTheory.LocalApprox.af_ext _ fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [evalV_singleV_same, GlobalTheory.LocalApprox.evalV_indA_of_mem _ (Finset.mem_singleton_self _)]
    · rw [evalV_singleV_ne _ v _ hw, GlobalTheory.LocalApprox.evalV_indA_of_notMem _ (Finset.notMem_singleton.2 hw)]
  have hv : ∀ v ∈ he2.toFinset, P (GlobalTheory.LocalApprox.cutAt V g {v}) := by
    intro v hvS
    have hv' := he3 v (he2.mem_toFinset.1 hvS)
    obtain ⟨e, he⟩ := _root_.GlobalTheory.MovedSplit.exists_splitAt D v hv'.1
    refine ⟨GlobalTheory.LocalApprox.cutAt_mem_GfC V g {v}, Subgroup.subset_closure ⟨e, (isSplitIdem_iff e).2 ⟨v, he⟩, ?_, ?_⟩⟩
    · intro q hq v' ε' hε' heq
      have hε : ε' = pairA D.host.F 0 (GlobalTheory.LocalApprox.indA D.host.F {v}) :=
        hinj (heq.symm.trans ((he.2.2).trans (hpl v)))
      obtain ⟨α, hα, hα1, hα0⟩ := hε'
      have hαv : α = GlobalTheory.LocalApprox.indA D.host.F {v} := congrArg Prod.snd (hα.symm.trans hε)
      have hvv : v' = v := by
        by_contra hne
        have := hα0 v (Ne.symm hne)
        rw [hαv, GlobalTheory.LocalApprox.evalV_indA_of_mem _ (Finset.mem_singleton_self _)] at this
        exact one_ne_zero this
      subst hvv
      intro hqm
      refine hv'.2 ?_
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun q : ℕ => q) hq
      have hk' : ((∏ q ∈ Q, q : ℕ) : 𝓞 D.host.F) = (q : 𝓞 D.host.F) * (k : 𝓞 D.host.F) := by
        rw [hk, Nat.cast_mul]
      rw [hk']
      exact Ideal.mul_mem_right _ _ hqm
    · intro i j
      rw [he.2.2, hpl v]
      exact GlobalTheory.LocalApprox.cutAt_supp V g {v} i j
  have key : ∀ t : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)), t ⊆ he2.toFinset →
      P (GlobalTheory.LocalApprox.cutAt V g t) := by
    intro t
    induction t using Finset.cons_induction with
    | empty => intro _; rw [GlobalTheory.LocalApprox.cutAt_empty]; exact h1
    | cons v t h ih =>
      intro hsub
      rw [GlobalTheory.LocalApprox.cutAt_cons]
      exact hmul _ _ (hv v (hsub (Finset.mem_cons_self _ _))) (ih ((Finset.subset_cons h).trans hsub))
  obtain ⟨_, hm⟩ := hgS ▸ key _ subset_rfl
  exact hm

end GlobalTheory.MovedKappaEx
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open Matrix

namespace GlobalTheory.RatSplitLat

theorem colLat_fg {K : Type} [Field K] [NumberField K] {n : ℕ} (B : GL (Fin n) K) : (colLat B).FG :=
  Submodule.fg_span (Set.finite_range _)

theorem colLat_span {K : Type} [Field K] [NumberField K] {n : ℕ} (B : GL (Fin n) K) :
    Submodule.span K ((colLat B : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K)) = ⊤ := by
  unfold colLat
  rw [Submodule.span_span_of_tower]
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ j, (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) j •
      (fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a j) := by
    funext a
    have := congrFun (show (B : Matrix (Fin n) (Fin n) K) *ᵥ (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) = x by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]) a
    conv_lhs => rw [← this]
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [hx]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem stab_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (H : AddSubgroup (Fin n → GlobalTheory.AdLat.RA F E)) (k : GL (Fin n) (GlobalTheory.AdLat.RA F E)) (N : ℕ)
    (h1 : ∀ z ∈ H, ∃ w ∈ H, k.1 *ᵥ z - z = N • w) (h2 : ∀ z ∈ H, (k⁻¹).1 *ᵥ z ∈ H) (y : Fin n → GlobalTheory.AdLat.RA F E) :
    y ∈ H ↔ k.1 *ᵥ y ∈ H := by
  constructor
  · intro hy
    obtain ⟨w, hw, e⟩ := h1 y hy
    rw [show k.1 *ᵥ y = (k.1 *ᵥ y - y) + y by abel, e]
    exact H.add_mem (H.nsmul_mem hw N) hy
  · intro hy
    have := h2 _ hy
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this



theorem exists_rat_split_lat : ∀ {D : D7} (V : HSp D) (B : GL (Fin V.rank) D.host.E) (N : ℕ), 0 < N → ∀ g : GfC V,
    ∃ r s k : GfC V, GlobalTheory.MovedKappaEx.RatFin V r ∧ GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom V s.1).1 ∧
      (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B) ↔
        Matrix.mulVec (Formalism.IndefR.Lev.finE V k.1).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B)) ∧ g = r * s * k := by
  intro D V B N hN g
  obtain ⟨-, -, -, -, c2, -, c1, gh, gd, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨γ', h', k', u1, u2, u3, hg, hs, hk, hki⟩ := GlobalTheory.T.exists_unitary_adelic_decomposition_split_support D.host.F D.host.E (GlobalTheory.Member.cF D) V.rank V.gramᵀ
    ⟨c2, c1, gh, gd⟩ (GlobalTheory.UnRep.Space.finrank_two D) (colLat B) (colLat_fg B) (colLat_span B) (finHom V g.1) N
    (GlobalTheory.UnRep.Space.isUnA_finHom V g.1) hN
  obtain ⟨-, -, -, lift, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  obtain ⟨r1, -, r3, -⟩ := GlobalTheory.Member.RatElt.rational_elements D V
  obtain ⟨h, hh, eh⟩ := lift h' u2
  obtain ⟨k, hk', ek⟩ := lift k' u3
  obtain ⟨γ, hγ⟩ := r3 γ' fun u v => by rw [GlobalTheory.UnRep.Space.herm_neg_eq, GlobalTheory.UnRep.Space.herm_neg_eq, u1]
  have eγ : (finHom V γ).1 = GlobalTheory.UnRep.fm D.host.F γ'.1 := GlobalTheory.Member.RatElt.fin_eq hγ
  have e : finHom V g.1 = finHom V γ * finHom V h * finHom V k := by
    apply Units.ext
    rw [hg, Units.val_mul, Units.val_mul, eγ, eh, ek]
  refine ⟨g * ⟨k, hk'⟩⁻¹ * ⟨h, hh⟩⁻¹, ⟨h, hh⟩, ⟨k, hk'⟩, ⟨γ, (r1 γ).2 ⟨γ', hγ⟩, ?_⟩, ?_, ?_, by rw [inv_mul_cancel_right, inv_mul_cancel_right]⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, map_mul, map_mul, map_inv, map_inv, e]
    rw [mul_inv_cancel_right, mul_inv_cancel_right]
  · change GlobalTheory.UnRep.SuppSplit _ N (finHom V h).1
    rw [eh]
    exact hs
  · intro v
    have key := GlobalTheory.StdFrames.hatL_of_hat (F := D.host.F) (colLat B) (colLat B) k'.1
      (stab_iff _ k' N hk hki) v
    have hm : (Formalism.IndefR.Lev.finE V k).1 =
        k'.1.map (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E) := by
      rw [← ek]; rfl
    refine key.trans (iff_of_eq ?_)
    exact congrArg (fun M => M *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B)) hm.symm

end GlobalTheory.RatSplitLat
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.rowChain_last_step_vector_eq_theta_of_datum : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {large₂ : SizeData₂ D},
    HidaSetting large₂ R F → ∀ ch : Choice R, ch.Is → ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)) (hj : (j : ℕ) + 1 = D.R.m),
    HEq g (R.vX t) → ∃ e' : AE D, IsIdemSum e' (GlobalTheory.FlipTop.topPl R.toLevCh t) ∧
      IsThetaAt ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e' (latO (ch.G.pS (.mu t 0 j)) (ch.G.pT (.mu t 0 j)) (ch.G.latS (.mu t 0 j) : Set _) (ch.G.latT (.mu t 0 j) : Set _) fun _ => True) 1 (ch.rm.vT 0 j)
        (GlobalTheory.FlipTop.topFn ch.S.B t e' j (GlobalTheory.FlipTop.rank_col ch.G (by omega)) (GlobalTheory.FlipTop.rank_col ch.G (by omega))) g := by
  first | exact @GlobalTheory.FlipTopChain.last_step_theta | exact GlobalTheory.FlipTopChain.last_step_theta | (intros; apply GlobalTheory.FlipTopChain.last_step_theta <;> assumption)

end
end
