module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle576
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle511
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle359
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle597
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle352
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathArgsOfNotMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle595
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle599
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle600
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle342
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle055
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

namespace GlobalTheory.TopLevelInv

theorem chrEq_mu_succ_succ : ∀ {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (j : ℕ), j + 1 < D.R.m → ChrEq (L.mu t (j + 1 + 1)) (muBase L (j + 1 + 1) * L.xiH t) ∧ ∀ P, (muBase L (j + 1 + 1) * L.xiH t).TameAt P := by
  intro D T L μ₀ hL t j hj
  have hm : ChrEq (L.mu0 (j + 1 + 1)) (muBase L (j + 1 + 1)) := by
    have := hL.mu0 ⟨j + 1, hj⟩
    simpa [muBase, hj] using this
  refine ⟨GlobalTheory.TowerCharRead.chrEq_mul hm (hL.xi t), fun P => ?_⟩
  have h1 : (muBase L (j + 1 + 1)).TameAt P := by
    rw [muBase, dite_eq_left hj]; exact (L.C.isMu0 ⟨j + 1, hj⟩).tame P
  exact Formalism.L2.Host.HChar.LevelLe.mul h1 (hL.xi_tame t P)

theorem mu_detAt_eq_prod_loc : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    ((L.mu t (j + 1 + 1) (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) : Circle) : ℂ) =
      ∏ w : locPl G t, (((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)) : ℂˣ) : ℂ) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he
  obtain ⟨hχ, htame⟩ := chrEq_mu_succ_succ hL t j hj
  obtain ⟨hinf, hin, hout⟩ := GlobalTheory.T.determinantIdeleAtIdempotent_idempotentPart_components he (G.V (.top (j + 1)))
    ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))))
  rw [GlobalTheory.T.unitaryIdeleChar_eq_prod_loc_of_tameAt hχ (locPl G t) (fun P _ => htame P) (fun P => gdet (kapAt S t j hj k P)) _ hinf
    (fun P hP => (hin P hP).trans (GlobalTheory.T.det_unitaryConj_atPlace_eq_det_latticeBasisComponent S t j hj k _ P)) hout]
  rw [← Finset.prod_coe_sort]
  rfl

end GlobalTheory.TopLevelInv
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FlipRun

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

theorem kerA_sum_of_grid {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) {ι : Type} (L : Finset ι) (w : ι → ℂ)
    (gs : ι → Sch G a) (g₀ : GA D (G.V a.src)) (h : GA D (G.V a.tgt)) :
    W.kerA a (∑ l ∈ L, w l • gs l) g₀ h = ∑ l ∈ L, w l * W.kerA a (gs l) g₀ h := by
  rcases ha with ⟨i, j, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ <;>

    simp [GridData.Weil.kerA, GridData.Weil.ker, thetaKO, map_sum, map_smul, Finset.sum_apply]

theorem liftA_sum_datum (M : Vol G) {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) {ι : Type} (L : Finset ι)
    (w : ι → ℂ) (gs : ι → Sch G a) (F : Fn G a.src) (hc : ∀ l ∈ L, LiftConv W M a (gs l) F) :
    liftA W M a (∑ l ∈ L, w l • gs l) F = ∑ l ∈ L, w l • liftA W M a (gs l) F := by
  funext h
  simp only [liftA_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, kerA_sum_of_grid ha, Finset.sum_mul]
  rw [integral_finsetSum _ fun l hl => ?_]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x => ?_)
    ring
  · have := (hc l hl h).const_mul (w l)
    refine this.congr (.of_forall fun x => ?_)
    simp only
    ring

theorem liftA_sum_form (M : Vol G) (a : Arrow T) (f : Sch G a) {ι : Type} (s : Finset ι) (w : ι → ℂ)
    (Fs : ι → Fn G a.src) (hc : ∀ k ∈ s, LiftConv W M a f (Fs k)) :
    liftA W M a f (∑ k ∈ s, w k • Fs k) = ∑ k ∈ s, w k • liftA W M a f (Fs k) := by
  funext h
  simp only [liftA_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum _ fun k hk => ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x => ?_)
    ring
  · have := (hc k hk h).const_mul (w k)
    refine this.congr (.of_forall fun x => ?_)
    simp only
    ring

theorem liftA_zero_form (M : Vol G) (a : Arrow T) (f : Sch G a) : liftA W M a f 0 = 0 := by
  have := liftA_smul W M a f 0 0
  rwa [zero_smul, zero_smul] at this

theorem sum_liftP_eq_zero {μ₀ : T} (hL : L.Is μ₀) (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}
    (he : IsIdemSum e (locPl G t)) (hC : CuspStep W M ρ t) {X : Node} :
    ∀ {Y : Node} (p : Path T X Y), OnGrid D.R.m t p → ∀ {ι : Type} (s : Finset ι) (c : ι → ℂ) (φ d : ι → PureT G p),
      (∀ k ∈ s, VecAll ρ e p (φ k) (d k)) → (∀ x : ArgT G p, HalfAll e p x → ∑ k ∈ s, c k * famProd p (φ k) x = 0) →
      ∀ (P : PolT G p) (F : Fn G X), IsCuspListed W.θ X F →
      ∑ k ∈ s, c k • liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) (d k) P) F = 0
  | _, .nil, _, ι, s, c, φ, d, _, hsum, P, F, _ => by
    have h0 : ∑ k ∈ s, c k = 0 := by
      have := hsum () trivial
      simpa [famProd] using this
    show ∑ k ∈ s, c k • F = 0
    rw [← Finset.sum_smul, h0, zero_smul]
  | _, .snoc a p, hg, ι, s, c, φ, d, hv, hsum, P, F, hF => by
    classical
    have ha : IsGridArrow D.R.m t a := hg.last
    have hmodel := GlobalTheory.FlipRun.exists_arrowModel (G := G) (t := t) ρ hL he ha
    rcases hmodel with ⟨Tm, h1, -, h3⟩
    have hmem : ∀ k ∈ s, (φ k).2 ∈ LocTensor.sbSpace e (latA G a) := fun k hk => ((h1 _ _).1 (hv k hk).2).1
    have hd2 : ∀ k ∈ s, (d k).2 = Tm (φ k).2 := fun k hk => ((h1 _ _).1 (hv k hk).2).2
    let b := Module.Basis.ofVectorSpace ℂ (LocTensor.sbSpace e (latA G a))
    let v : ι → LocTensor.sbSpace e (latA G a) := fun k => if h : (φ k).2 ∈ LocTensor.sbSpace e (latA G a) then ⟨_, h⟩ else 0
    have hv' : ∀ k ∈ s, ((v k : LocTensor.sbSpace e (latA G a)) : Sch G a) = (φ k).2 := fun k hk => by
      simp only [v, dite_eq_left (hmem k hk)]
    let r : ι → Module.Basis.ofVectorSpaceIndex ℂ (LocTensor.sbSpace e (latA G a)) → ℂ := fun k l => b.repr (v k) l
    let Ls := s.biUnion fun k => (b.repr (v k)).support
    have hexp : ∀ k ∈ s, (φ k).2 = ∑ l ∈ Ls, r k l • ((b l : LocTensor.sbSpace e (latA G a)) : Sch G a) := by
      intro k hk
      rw [← hv' k hk]
      conv_lhs => rw [← b.linearCombination_repr (v k)]
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun k => (b.repr (v k)).support) hk)
          (fun i (x : ℂ) => x • b i) (fun _ _ => zero_smul _ _), Submodule.coe_sum]
      rfl
    let Fk : ι → Fn G a.src := fun k => liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) (d k).1 P.1) F
    have cusp_zip : ∀ {Y : Node} (q : Path T X Y), OnGrid D.R.m t q →
        ∀ (φq dq : PureT G q), VecAll ρ e q φq dq → ∀ Q : PolT G q,
          IsCuspListed W.θ Y
            (liftP W M q (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) dq Q) F) := by
      intro Y q
      induction q with
      | nil =>
        intro _ _ _ _ _
        exact hF
      | snoc b q ih =>
        intro hq φq dq hvq Q
        exact (hC b hq.last e he φq.2 dq.2 hvq.2 Q.2 _ (ih hq.init φq.1 dq.1 hvq.1 Q.1)).2
    have hFk : ∀ k ∈ s, IsCuspListed W.θ a.src (Fk k) := fun k hk =>
      cusp_zip p hg.init (φ k).1 (d k).1 (hv k hk).1 P.1
    let g : Module.Basis.ofVectorSpaceIndex ℂ (LocTensor.sbSpace e (latA G a)) → Sch G a :=
      fun l => W.fock a.pair (Tm (b l)) P.2
    have hconv : ∀ l, ∀ k ∈ s, LiftConv W M a (g l) (Fk k) := fun l k hk =>
      (hC a hg.last e he (b l) (Tm (b l)) ((h1 _ _).2 ⟨(b l).2, rfl⟩) P.2 (Fk k) (hFk k hk)).1
    have hstep : ∀ k ∈ s, W.fock a.pair (d k).2 P.2 = ∑ l ∈ Ls, r k l • g l := by
      intro k hk

      rw [hd2 k hk, hexp k hk, map_sum]
      simp only [map_smul]
      exact GlobalTheory.SpecFac.pureTensorO_sum W.ψ_std W.θ_is _ _ _ _ Ls (r k) (fun l => Tm (b l))
        (fun l _ => h3 _ (b l).2) P.2
    have hIH : ∀ l, ∑ k ∈ s, (c k * r k l) • Fk k = 0 := by
      intro l
      refine sum_liftP_eq_zero hL M ρ t he hC p hg.init s (fun k => c k * r k l) (fun k => (φ k).1) (fun k => (d k).1)
        (fun k hk => (hv k hk).1) (fun x hx => ?_) P.1 F hF
      have hV : ∑ k ∈ s, (c k * famProd p (φ k).1 x) • v k = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        funext y
        rw [Finset.sum_apply]
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Submodule.coe_zero, Pi.zero_apply]
        rw [Finset.sum_congr rfl fun k hk => by rw [hv' k hk]]
        by_cases hy : IsHalf e y
        · have := hsum (x, y) ⟨hx, hy⟩
          rw [← this]
          refine Finset.sum_congr rfl fun k _ => ?_
          show _ = c k * (famProd p (φ k).1 x * (φ k).2 y)
          ring
        · refine Finset.sum_eq_zero fun k hk => ?_
          have : (φ k).2 y = 0 := by
            by_contra h0
            exact hy ((hmem k hk).1 y h0)
          rw [this, mul_zero]
      have := congrArg (fun z => b.repr z l) hV

      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
      map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [r]
      ring
    have hsum_lift :
        (∑ k ∈ s, c k • liftA W M a (W.fock a.pair (d k).2 P.2) (Fk k)) =
          ∑ k ∈ s, ∑ l ∈ Ls, (c k * r k l) • liftA W M a (g l) (Fk k) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hstep k hk, liftA_sum_datum M ha Ls (r k) g (Fk k) (fun l _ => hconv l k hk),
        Finset.smul_sum]
      simp only [smul_smul]
    show ∑ k ∈ s, c k • liftA W M a (W.fock a.pair (d k).2 P.2) (Fk k) = 0
    rw [hsum_lift, Finset.sum_comm]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← liftA_sum_form M a (g l) s (fun k => c k * r k l) Fk (fun k hk => hconv l k hk),
      hIH l, liftA_zero_form]

theorem liftT_tensE_expand (M : Vol G) {X Y : Node} (p : Path T X Y) (Q : PolE G →₀ ℂ) (τ : TotT G p) (F : Fn G X) :
    liftT W M p (tensE W p Q τ) F =
      ∑ P ∈ (Q.mapDomain fun P => restrictPol P p).support, (Q.mapDomain fun P => restrictPol P p) P •
        ∑ d ∈ τ.support, τ d • liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P) F := by
  unfold tensE tensT
  rw [Finsupp.sum, liftT_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finsupp.sum, liftT_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [liftT_single, mul_smul]

theorem liftT_tensE_eq_of_famProd : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ {W : G.Weil} (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}, IsIdemSum e (locPl G t) → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid D.R.m t p → ∀ (τ₁ τ₂ : TotT G p) (φ₁ φ₂ : PureT G p → PureT G p), (∀ d ∈ τ₁.support, GlobalTheory.FlipRun.VecAll ρ e p (φ₁ d) d) → (∀ d ∈ τ₂.support, GlobalTheory.FlipRun.VecAll ρ e p (φ₂ d) d) → (∀ x : GlobalTheory.FlipRun.ArgT G p, GlobalTheory.FlipRun.HalfAll e p x → (τ₁.sum fun d c => c * GlobalTheory.FlipRun.famProd p (φ₁ d) x) = τ₂.sum fun d c => c * GlobalTheory.FlipRun.famProd p (φ₂ d) x) → ∀ F : Fn G X, GlobalTheory.FlipRun.IsCuspListed W.θ X F → ∀ Q : GlobalTheory.FlipRun.PolE G →₀ ℂ, liftT W M p (GlobalTheory.FlipRun.tensE W p Q τ₁) F = liftT W M p (GlobalTheory.FlipRun.tensE W p Q τ₂) F := by
  intro D T L sc G μ₀ hL W M ρ t e he hC X Y p hg τ₁ τ₂ φ₁ φ₂ hv₁ hv₂ heq F hF Q
  classical
  rw [liftT_tensE_expand, liftT_tensE_expand]
  refine Finset.sum_congr rfl fun P _ => ?_
  congr 1
  have key := sum_liftP_eq_zero hL M ρ t he hC p hg (τ₁.support.disjSum τ₂.support)
    (Sum.elim (fun d => τ₁ d) fun d => -τ₂ d) (Sum.elim φ₁ φ₂) (Sum.elim id id)
    (by
      rintro (k | k) hk
      · exact hv₁ k (Finset.inl_mem_disjSum.1 hk)
      · exact hv₂ k (Finset.inr_mem_disjSum.1 hk))
    (fun x hx => by
      rw [Finset.sum_disjSum]
      have := heq x hx
      simp only [Finsupp.sum] at this
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, this, add_neg_cancel])
    P F hF
  rw [Finset.sum_disjSum] at key
  simp only [Sum.elim_inl, Sum.elim_inr, id, neg_smul, Finset.sum_neg_distrib] at key
  exact sub_eq_zero.1 ((sub_eq_add_neg _ _).trans key)

end GlobalTheory.FlipRun

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RealAvg

open MvPolynomial

variable {D : D7}

theorem substMat_mul (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ) (g₁ g₂ : GA D V) :
    substMat θ V m d (g₁ * g₂) = substMat θ V m d g₁ * substMat θ V m d g₂ := by
  ext k' k
  simp only [substMat, Matrix.mul_apply]
  have e : (fun τ => compAt θ τ (Formalism.L2.Theta.mt V (g₁ * g₂))) =
      (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g₁)) * (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g₂)) :=
    funext fun τ => GlobalTheory.StdUnn.CartanMove.compAt_mt_mul θ τ V g₁ g₂
  have e1 : (fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ)) = (fun _ => 1) * (fun _ => 1) := by
    funext τ; simp
  have e2 : GlobalTheory.CompactHowe.substF (fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ))
      (fun τ => compAt θ τ (Formalism.L2.Theta.mt V (g₁ * g₂))) (monomial k.1 1) =
      GlobalTheory.CompactHowe.substF (fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ))
        (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g₁))
        (GlobalTheory.CompactHowe.substF (fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ))
          (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g₂)) (monomial k.1 1)) := by
    rw [GlobalTheory.T.matrixFamilyBilateralSubstitution_comp_eq_mul, ← e, ← e1]
  rw [e2]
  conv_lhs => rw [eq_sum_mon (d := d) (GlobalTheory.CompactHowe.substF _ _ (monomial k.1 1))
    (fun k'' h => (GlobalTheory.T.mapDomain_fst_eq_of_coeff_matrixFamilyBilateralSubstitution_ne_zero _ _ _ _ h).trans k.2)]

  rw [map_sum, coeff_sum]
  refine Finset.sum_congr rfl fun k'' _ => ?_
  rw [map_smul, MvPolynomial.coeff_smul, smul_eq_mul, mul_comm]

theorem substMat_cont {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ)
    (k' k : Mon D m V.rank d) :
    Continuous (fun g : GinfC V => substMat θ V m d g.1 k' k) := by
  have hc := (GlobalTheory.T.coeff_matrixFamilyBilateralSubstitution_monomial_continuous_algebraic (ι := D.what₂.Tau) (N := m) (n := V.rank) k.1 k'.1).1
  have hm : Continuous fun g : GinfC V => (fun τ : D.what₂.Tau => compAt θ τ (Formalism.L2.Theta.mt V g.1)) :=
    continuous_pi fun τ =>
      (GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp ((GlobalTheory.RealWeil.continuous_mt V).1.comp continuous_subtype_val)
  have hp : Continuous fun g : GinfC V => ((fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ)),
      (fun τ : D.what₂.Tau => compAt θ τ (Formalism.L2.Theta.mt V g.1))) := continuous_const.prodMk hm
  have := hc.comp hp
  exact this

theorem substMat_alg (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ)
    (k' k : Mon D m V.rank d) (g : GA D V) (hg : ∀ τ a b, IsAlgebraic ℚ (compAt θ τ (Formalism.L2.Theta.mt V g) a b)) :
    IsAlgebraic ℚ (substMat θ V m d g k' k) := by
  have ha := (GlobalTheory.T.coeff_matrixFamilyBilateralSubstitution_monomial_continuous_algebraic (ι := D.what₂.Tau) (N := m) (n := V.rank) k.1 k'.1).2
    (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g)) (one_alg m) hg
  exact ha

theorem substMat_central (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ) (z : GA D V) (τ₀ : D.what₂.Tau) (ζ : ℂ)
    (h1 : compAt θ τ₀ (Formalism.L2.Theta.mt V z) = ζ • (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (h2 : ∀ ρ, ρ ≠ τ₀ → compAt θ ρ (Formalism.L2.Theta.mt V z) = 1) :
    substMat θ V m d z = (ζ ^ d τ₀) • (1 : Matrix (Mon D m V.rank d) (Mon D m V.rank d) ℂ) := by
  classical
  have e : (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt V z)) =
      fun ρ => if ρ = τ₀ then ζ • (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) else 1 := by
    funext ρ
    by_cases hρ : ρ = τ₀
    · subst hρ; rw [if_pos rfl, h1]
    · rw [if_neg hρ, h2 ρ hρ]
  ext k' k
  simp only [substMat, e, GlobalTheory.T.matrixFamilyBilateralSubstitution_scalar_monomial, MvPolynomial.coeff_smul, coeff_monomial, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  rw [show Finsupp.mapDomain Prod.fst k.1 = d from k.2]
  by_cases h : k' = k
  · subst h; simp
  · have h' : (k.1 : FVar D m V.rank →₀ ℕ) ≠ k'.1 := fun e => h (Subtype.ext e.symm)
    simp [h, h']

end GlobalTheory.RealAvg

namespace GlobalTheory.RealAvg

open MvPolynomial
open GlobalTheory.Grid (neg sgn ofSgn)

end GlobalTheory.RealAvg
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
open scoped Matrix

namespace GlobalTheory.RealColAct

theorem compAt_eq_infMat {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (h : GA D V) :
    compAt θ τ (Formalism.L2.Theta.mt V h) = infMat D.sp.cm.sig V.gram (θ τ) h := rfl

theorem realCol_surjective {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : HSpace.gram V = 1) :
    Function.Surjective (GlobalTheory.RealColAct.realCol θ hθ V hV) := by
  classical
  intro u
  have hex : ∀ τ, ∃ h : GA D V, IsAtTau θ V τ ((u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ) h := fun τ => by
    refine (GlobalTheory.PointAtPlace.existsUnique_isAtTau V τ θ hθ _ ?_).exists
    have hu := transpose_mem_unitary (u τ).2
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
    show _ * _ * _ = _
    rw [gramAt_of_gram_one hV, Matrix.mul_one, hu]
  choose hτ hhτ using hex
  have key : ∀ (L : List D.what₂.Tau), L.Nodup → ∀ ρ,
      compAt θ ρ (Formalism.L2.Theta.mt V (L.map hτ).prod) =
        if ρ ∈ L then ((u ρ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ) else 1 := by
    intro L
    induction L with
    | nil => intro _ ρ; simp only [List.map_nil, List.prod_nil, List.not_mem_nil, if_false]; exact GlobalTheory.StdUnn.CartanMove.compAt_mt_one θ ρ V
    | cons a L ih =>
      intro hL ρ
      rw [List.nodup_cons] at hL
      rw [List.map_cons, List.prod_cons, GlobalTheory.StdUnn.CartanMove.compAt_mt_mul, ih hL.2 ρ, compAt_eq_infMat]
      by_cases c : ρ = a
      · subst c
        rw [(hhτ ρ).2.1, if_neg hL.1, if_pos List.mem_cons_self, Matrix.mul_one]
      · rw [(hhτ a).2.2 ρ c, Matrix.one_mul]
        by_cases d : ρ ∈ L
        · rw [if_pos d, if_pos (List.mem_cons_of_mem a d)]
        · rw [if_neg d, if_neg (by simp [c, d])]
  let L := (Finset.univ : Finset D.what₂.Tau).toList
  have hmem : (L.map hτ).prod ∈ GinfC V := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
    exact (hhτ τ).1
  refine ⟨(⟨(L.map hτ).prod, hmem⟩ : GinfC V)⁻¹, ?_⟩
  funext ρ
  apply Subtype.ext
  rw [realCol_apply]
  simp only [InvMemClass.coe_inv, inv_inv]
  rw [key L (Finset.nodup_toList _) ρ, if_pos (Finset.mem_toList.2 (Finset.mem_univ ρ)), Matrix.transpose_transpose]

end GlobalTheory.RealColAct
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

theorem _root_.GlobalTheory.T.orientedPair_fockMaps_lie_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO M X → ℂ) →ₗ[ℂ] Pi), IsCoinvMap θ ω (algF ψ θ ε A B) Pi rf rl p →
  (∀ f, IsFinF ψ θ ε A B f → ∀ τ, ∀ Y ∈ lieAt X τ, ∀ P,
      p (fockF ψ θ ε A B f (GlobalTheory.RealQuot.actT ε A B eS τ Y P)) = rl τ Y (p (fockF ψ θ ε A B f P))) ∧
  (∀ f, IsFinF ψ θ ε A B f → ∀ P ∈ GlobalTheory.RealQuot.coinv ε A B eT, p (fockF ψ θ ε A B f P) = 0) ∧
  ∀ h ∈ GfC X, ∀ f, IsFinF ψ θ ε A B f → ∃ f', IsFinF ψ θ ε A B f' ∧
    ∀ P, rf h (p (fockF ψ θ ε A B f P)) = p (fockF ψ θ ε A B f' P) := by
  first | exact @GlobalTheory.RealQuot.oriented_maps | exact GlobalTheory.RealQuot.oriented_maps | (intros; apply GlobalTheory.RealQuot.oriented_maps <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.sqrt_absNorm_le_prod_norm_cmTypeEmbeddings : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (u : 𝓞 D.host.E), u ∈ 𝔪 → u ≠ 0 → Real.sqrt (Ideal.absNorm 𝔪) ≤ ∏ τ, ‖tauE D τ (u : D.host.E)‖ := by
  first | exact @GlobalTheory.CMNorm.sqrt_absNorm_le_prod_tauE | exact GlobalTheory.CMNorm.sqrt_absNorm_le_prod_tauE | (intros; apply GlobalTheory.CMNorm.sqrt_absNorm_le_prod_tauE <;> assumption)
end
