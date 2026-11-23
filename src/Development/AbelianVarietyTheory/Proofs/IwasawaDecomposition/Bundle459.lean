module

public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle443
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
public import Formalism.QuotientMetricDivisors.Statement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle395
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle003
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.InertJacobiLevels.Bundle001
public import Lean.Meta.ExprDefEq

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ChosenHalf

theorem isConjPl_unique (D : D7) {P w w' : PlE D.host} (h : IsConjPl D.host P w) (h' : IsConjPl D.host P w') :
    w = w' := by
  apply HeightOneSpectrum.ext
  ext y
  obtain ⟨x, hx⟩ := (RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv).surjective y
  have hy : (y : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [← hx]; rfl
  rw [← h x y hy, ← h' x y hy]

theorem not_isConjPl_self (D : D7) {P : PlE D.host} (hs : IsSplitPl D.host P) : ¬ IsConjPl D.host P P := by
  intro hc
  obtain ⟨x, hx, hy⟩ := hs
  have hyx : ((RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv x : 𝓞 D.host.E) : D.host.E) =
      D.host.conj (x : D.host.E) := rfl
  exact hy _ hyx ((hc x _ hyx).1 hx)

theorem overPl_unique (D : D7) {P : PlE D.host} {v v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))}
    (h : NG.OverPl P v) (h' : NG.OverPl P v') : v = v' :=
  HeightOneSpectrum.ext (h.symm.trans h')

theorem qpOf_half : ∀ (D : D7) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host), (∀ v, NG.OverPl (Pq v) v) →
    ∀ S : Finset (PlE D.host), (∀ P ∈ S, IsSplitPl D.host P) →
    (∀ P ∈ S, ∃ P' ∈ qpOf D Pq S, P' = P ∨ IsConjPl D.host P P') ∧ ∀ P ∈ qpOf D Pq S, ∀ P' ∈ qpOf D Pq S, ¬ IsConjPl D.host P P' := by
  classical
  intro D Pq hPq S hS
  have pair := GlobalTheory.T.comap_realSubfield_eq_iff_eq_or_isConjPlace D
  have memq : ∀ P, P ∈ qpOf D Pq S ↔ P ∈ S ∧ ∀ v, NG.OverPl P v → P = Pq v ∨ Pq v ∉ S := by
    intro P
    unfold qpOf
    rw [Finset.mem_filter]
  refine ⟨fun P hP => ?_, fun P hP P' hP' hc => ?_⟩
  · by_cases hq : P ∈ qpOf D Pq S
    · exact ⟨P, hq, Or.inl rfl⟩
    · have hn : ¬ ∀ v, NG.OverPl P v → P = Pq v ∨ Pq v ∉ S := fun h => hq ((memq P).2 ⟨hP, h⟩)
      push_neg at hn
      obtain ⟨v, hv, -, hin⟩ := hn
      refine ⟨Pq v, (memq _).2 ⟨hin, fun v' hv' => Or.inl ?_⟩, ?_⟩
      · rw [overPl_unique D (hPq v) hv']
      · rcases (pair P (Pq v)).1 (hv.trans (hPq v).symm) with h | h
        · exact Or.inl h.symm
        · exact Or.inr h
  · have hPS := ((memq P).1 hP).1
    have hP'S := ((memq P').1 hP').1
    let v := HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) P
    have hv : NG.OverPl P v := rfl
    have hv' : NG.OverPl P' v := ((pair P P').2 (Or.inr hc)).symm.trans hv
    have hqS : Pq v ∈ S := by
      rcases (pair P (Pq v)).1 (hv.trans (hPq v).symm) with h | h
      · rw [← h]; exact hPS
      · rw [← isConjPl_unique D hc h]; exact hP'S
    have e1 := qpOf_eq D Pq S hP hv hqS
    have e2 := qpOf_eq D Pq S hP' hv' hqS
    have e : P' = P := e2.trans e1.symm
    rw [e] at hc
    exact not_isConjPl_self D (hS P hPS) hc

end GlobalTheory.ChosenHalf
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.SideTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {y : Hd R} {b : Bool}
  {rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] {S : RowSide D EE} {n : ℕ} {bs : OrthonormalBasis (Fin n) ℂ EE} {ty : Fin n → D.what₂.FT}
  {jA : ∀ t, (Fin (rDim D A (levP F b).1 (levP F b).2 t) → D.what₂.LL) → S.Amb (y.tup t)}

def ids (hU : ∀ μ, Used0 D μ ↔ y.Us μ)
    (t : ChT y F b rep (Top := fun μ => ⟨S.Amb μ⟩) jA ⟨⟨EE⟩, fun μ j => ⟨S.Mult μ j⟩, S.multZero, S.multTop, S.io, n, bs, ty⟩) :
    RowIds S (y.C F) b where
  jE := (LinearEquiv.ofInjective t.jE t.jE_inj).trans (LinearEquiv.ofEq _ _ t.jE_range)
  jM μ hμ j h1 h2 := (LinearEquiv.ofInjective (t.jM μ j) (t.jM_inj μ ((hU μ).1 hμ) j h1 h2)).trans
    (LinearEquiv.ofEq _ _ (t.jM_range μ ((hU μ).1 hμ) j h1 h2))
  jX μ hμ := (S.multTop μ).toLinearEquiv.trans ((LinearEquiv.ofInjective (t.jX μ) (t.jX_inj μ ((hU μ).1 hμ))).trans
    (LinearEquiv.ofEq _ _ (t.jX_range μ ((hU μ).1 hμ))))
  prt π := y.prtE F b (rep π)

theorem real (hU : ∀ μ, Used0 D μ ↔ y.Us μ)
    (t : ChT y F b rep (Top := fun μ => ⟨S.Amb μ⟩) jA ⟨⟨EE⟩, fun μ j => ⟨S.Mult μ j⟩, S.multZero, S.multTop, S.io, n, bs, ty⟩) :
    RowSideReal S (y.C F) b (ids hU t) bs ty := by
  exact {
    parY j hj := by
      show Mult.parB (Ptw D) (min j D.R.m) = Mult.parB (Ptw D) j
      rw [min_eq_left (by have := y.hm; omega)]
    lvl μ _ := GlobalTheory.HilbertLevels.eec_le_cc R F y.tupT y.hm y.hTop b μ
    lvlP μ _ j _ h2 := GlobalTheory.HilbertLevels.ccp_le R F y.tupT y.hm y.hTop b μ (by have := y.hm; omega)
    lvlX μ _ := GlobalTheory.HilbertLevels.ccxp_le R F y.tupT y.hm y.hTop b μ
    ee x x' := t.jE_ip x x'
    mult μ hμ j h1 h2 x x' := t.jM_ip μ ((hU μ).1 hμ) j h1 h2 x x'
    multX _ μ hμ x x' := by
      rw [← (S.multTop μ).inner_map_map x x']
      exact t.jX_ip μ ((hU μ).1 hμ) _ _
    io0 _ μ hμ _ x v := by
      have hmem : t.jM μ 1 v ∈ (y.C F).CC b μ 1 :=
        GlobalTheory.HilbertLevels.ccp_le R F y.tupT y.hm y.hTop b μ (by have := D.R.two_le_m; omega) ((ids hU t).jM μ hμ 1 le_rfl (by have := D.R.two_le_m; omega) v).2
      have e := t.io0 μ ((hU μ).1 hμ) x v hmem
      refine e.trans ?_
      rfl
    io0X h := absurd h (by have := D.R.two_le_m; omega)
    io μ hμ _ j h1 h2 x v := by
      have hmem : t.jM μ (j + 1) v ∈ (y.C F).CC b μ (j + 1) :=
        GlobalTheory.HilbertLevels.ccp_le R F y.tupT y.hm y.hTop b μ (by omega) ((ids hU t).jM μ hμ (j + 1) (by omega) h2 v).2
      exact (t.io μ ((hU μ).1 hμ) j h1 h2 x v hmem).trans rfl
    ioTop h μ hμ _ x v := by
      have hmem : t.jX μ (S.multTop μ v) ∈ (y.C F).CCX b μ :=
        GlobalTheory.HilbertLevels.ccxp_le R F y.tupT y.hm y.hTop b μ ((ids hU t).jX μ hμ v).2
      exact (t.ioTop μ ((hU μ).1 hμ) x v _ (cast_heq _ _) hmem).trans rfl
    ft σ := by
      have h := t.ft (ty σ)
      have hs : bs σ ∈ Submodule.span ℂ (bs '' {σ' | ty σ' = ty σ}) := Submodule.subset_span ⟨σ, rfl, rfl⟩
      rw [h] at hs
      exact hs
    prt_disj π π' h := t.disj π π' h
  }

end GlobalTheory.Mem.R3.Rw.SideTie


open GlobalTheory.Mem.R3.Rw.SideTie in
theorem GlobalTheory.Mem.R3.Rw.rowSide_of_chainTie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), Inputs D → R.BaseW F → (∀ μ, Used0 D μ ↔ y.Us μ) → ∀ (b : Bool) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE) (n : ℕ) (bs : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) (jA : ∀ t, (Fin (rDim D A (levP F b).1 (levP F b).2 t) → D.what₂.LL) → S.Amb (y.tup t)) (t : ChT y F b rep (Top := fun μ => ⟨S.Amb μ⟩) jA ⟨⟨EE⟩, fun μ j => ⟨S.Mult μ j⟩, S.multZero, S.multTop, S.io, n, bs, ty⟩), ∃ I : RowIds S (y.C F) b, RowSideReal S (y.C F) b I bs ty ∧ (∀ π, I.prt π = y.prtE F b (rep π)) ∧ (∀ x, (I.jE x).1 = t.jE x) ∧ ∀ μ h x, (I.jX μ h x).1 = t.jX μ (S.multTop μ x) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F y _ _ hU b rep EE _ _ _ S n bs ty jA t
  exact ⟨ids hU t, real hU t, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.LiftRd

theorem liftTie_of_lfT : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), Inputs D → R.BaseW F → (∀ μ, Used0 D μ ↔ y.Us μ) → DV.LamDef D → ∀ (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (jL : ∀ (i : Fin D.R.m) t, (Fin (lDim D A F.P0 F.ψ0 i t) → D.what₂.LL) → D.what₂.Mt (y.tup t) ((i : ℕ) + 1)) (t : LfT y F rep (Mt := fun μ j => ⟨D.what₂.Mt μ j⟩) jL ⟨fun j => ⟨D.what₂.Mj j⟩, D.what₂.MjLat, D.what₂.thetaP, D.what₂.isot⟩), ∃ (I : LiftIds (y.L F)) (mj : GlobalTheory.RealGeo.MjTie R F), LiftTie (y.L F) I ∧ (∀ i π, I.prtW i π = y.prtW F i (rep π)) ∧ (∀ i x, (I.jMj i x).1 = t.jMj i x) ∧ (∀ μ h i x, (I.jMt μ h i x).1 = t.jMt μ i x) ∧ ∀ i x, mj.eW i x = t.eW i x := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F y hI hB hU hLam rep jL t
  let I : LiftIds (y.L F) :=
    { jMj := fun i =>
        (LinearEquiv.ofInjective (t.jMj i) (t.jMj_inj i)).trans (LinearEquiv.ofEq _ _ (t.jMj_range i))
      jMt := fun μ hμ i =>
        (LinearEquiv.ofInjective (t.jMt μ i) (t.jMt_inj μ ((hU μ).1 hμ) i)).trans
          (LinearEquiv.ofEq _ _ (t.jMt_range μ ((hU μ).1 hμ) i))
      prtW := fun i π => y.prtW F i (rep π) }
  refine ⟨I, ⟨t.eW, t.eW_range, t.eW_norm, t.eW_lat⟩, ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ => rfl⟩
  refine ⟨fun i => GlobalTheory.HilbertLevels.holW R F y.tupT y.hm y.hTop y.hinj i, fun i x x' => t.jMj_ip i x x',
    fun μ hμ i x x' => t.jMt_ip μ ((hU μ).1 hμ) i x x', ?_, fun i π v => t.isot i π v,
    fun i π π' h => t.disj i π π' h, ?_⟩
  · intro μ hμ i x w _ hw hthC hgood
    exact t.theta μ ((hU μ).1 hμ) i x _ w hw hthC hgood
  · intro μ _ i π c h0 hc
    rw [hLam μ ((i : ℕ) + 1) (by omega) i.2 π h0]
    exact DV.lamTr_of_scalar D μ _ π c h0 hc

end GlobalTheory.Mem.R3.Rw.LiftRd

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Df

open Formalism.L2.TwC

theorem norm_le_one_of_mem_clC' (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (PadicAlgCl l)) {z : ℂ_[l]}
    (hz : z ∈ clC l F) : ‖z‖ ≤ 1 := by
  have hm : z ∈ PadicComplexInt l := (Subring.mem_inf.1 hz).2
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff] at hm
  rw [PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff).2 hm

theorem exists_iC_of_clC (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    (F : IntermediateField ℚ_[l] (PadicAlgCl l)) (e : O ≃+* clC l F)
    (hratio : ∀ x ∈ clC l F, ∀ y ∈ clC l F, ‖x‖ ≤ ‖y‖ → x / y ∈ clC l F) :
    ∃ iC : FractionRing O →+* ℂ_[l],
      ∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap O (FractionRing O)).range := by
  let ψ : O →+* ℂ_[l] := (clC l F).subtype.comp e.toRingHom
  have hψ : Function.Injective ψ := fun a b h => e.injective (Subtype.ext h)
  let iC : FractionRing O →+* ℂ_[l] := IsFractionRing.lift hψ
  have hiC : ∀ a : O, iC (algebraMap O (FractionRing O) a) = ψ a := fun a => IsFractionRing.lift_algebraMap hψ a
  refine ⟨iC, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    have hb0 : algebraMap O (FractionRing O) b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have hψb : ψ b ≠ 0 := by
      rw [← hiC]; exact (map_ne_zero iC).2 hb0
    rw [map_div₀, hiC, hiC, norm_div, div_le_one (norm_pos_iff.2 hψb)] at hx
    have hmem := hratio _ (e a).2 _ (e b).2 hx
    refine ⟨e.symm ⟨_, hmem⟩, ?_⟩
    apply iC.injective
    rw [hiC, map_div₀, hiC, hiC]
    show ((e (e.symm ⟨_, hmem⟩) : clC l F) : ℂ_[l]) = _
    rw [e.apply_symm_apply]
    rfl
  · rintro ⟨a, rfl⟩
    rw [hiC]
    exact norm_le_one_of_mem_clC' l F (e a).2

end GlobalTheory.Mem.Df

namespace GlobalTheory.Mem.Df

open Formalism.L2.TwC

end GlobalTheory.Mem.Df
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.NonzeroPlacesOverPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain

theorem conjPl_injective {K : Type} [Field K] [StarRing K] :
    Function.Injective (Formalism.DivisionValues.conjPl (K := K)) := by
  intro v w h
  have h1 : Ideal.map (Formalism.DivisionValues.cO K) v.asIdeal = Ideal.map (Formalism.DivisionValues.cO K) w.asIdeal :=
    congrArg HeightOneSpectrum.asIdeal h
  have hb : Function.Bijective (Formalism.DivisionValues.cO K) := (Formalism.DivisionValues.cO K).bijective
  have h2 := congrArg (Ideal.comap (Formalism.DivisionValues.cO K)) h1
  rw [Ideal.comap_map_of_bijective _ hb, Ideal.comap_map_of_bijective _ hb] at h2
  exact HeightOneSpectrum.ext h2

theorem dual_fg {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ} (H : Matrix (Fin d) (Fin d) K)
    (hH : IsUnit H.det) (A : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsFullLattice K A) :
    (Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A).FG := by
  classical
  obtain ⟨S, hS⟩ := hA.toIsLattice.fg
  have hSm : ∀ a ∈ S, a ∈ A := fun a ha => hS ▸ Submodule.subset_span ha
  have mem : ∀ x, x ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A ↔
      ∀ y ∈ A, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = Formalism.DivisionValues.hform H y x := by
    intro x
    unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars, Submodule.mem_one]
  choose g hg using fun (x : Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A) (a : S) => (mem x).1 x.2 a (hSm a a.2)
  have inj : Function.Injective (algebraMap (𝓞 K) K) := FaithfulSMul.algebraMap_injective (𝓞 K) K
  let φ : Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A →ₗ[𝓞 K] (S → 𝓞 K) :=
    { toFun := g
      map_add' := fun x y => funext fun a => inj (by
        rw [hg, Submodule.coe_add, map_add (f := _), Pi.add_apply, map_add (f := _), hg, hg])
      map_smul' := fun s x => funext fun a => inj (by
        rw [hg, Submodule.coe_smul, ← algebraMap_smul K s (x : Fin d → K), map_smul]
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, map_mul, hg]) }
  have hφ : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : ∀ a ∈ S, Formalism.DivisionValues.hform H a x = 0 := by
      intro a ha
      rw [← hg x ⟨a, ha⟩, show g x ⟨a, ha⟩ = 0 from congrFun hx ⟨a, ha⟩, map_zero]
    have hL : ∀ a ∈ A, Formalism.DivisionValues.hform H a x = 0 := by
      intro a ha
      rw [← hS] at ha
      induction ha using Submodule.span_induction with
      | mem a ha => exact h0 a ha
      | zero => simp
      | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
      | smul s a _ ha => rw [← algebraMap_smul K s a, LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]
    have hV : ∀ a, Formalism.DivisionValues.hform H a x = 0 := by
      intro a
      have ha : a ∈ Submodule.span K (A : Set (Fin d → K)) := by rw [Submodule.IsFullLattice.span_eq_top (self := hA)]; trivial
      induction ha using Submodule.span_induction with
      | mem a ha => exact hL a ha
      | zero => simp
      | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
      | smul s a _ ha => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]
    have hM : Matrix.mulVec H (x : Fin d → K) = 0 := by
      funext i
      have := hV (Pi.single i 1)
      simpa [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Pi.single_apply, mul_comm] using this
    exact Subtype.ext (Matrix.eq_zero_of_mulVec_eq_zero hH.ne_zero hM)
  exact Module.Finite.iff_fg.1 (Module.Finite.of_injective φ hφ)

end GlobalTheory.Mem.NonzeroPlacesOverPrimes

namespace GlobalTheory.Mem.NonzeroPlacesOverPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem jw_finite_of_lat {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ} (H : Matrix (Fin d) (Fin d) K)
    (hH : IsUnit H.det) (A : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsFullLattice K A) :
    {w : HeightOneSpectrum (𝓞 K) | Formalism.DivisionValues.jw H w A ≠ 0}.Finite :=
  GlobalTheory.Mem.IdxFin.lidx_finite A _ hA.toIsLattice.fg (dual_fg H hH A hA)

theorem idx_finite_of_fg {K : Type} [Field K] [NumberField K] {d d' : ℕ} (M : Submodule (𝓞 K) (Fin d' → K))
    (θ : Matrix (Fin d') (Fin d) K) (L : Submodule (𝓞 K) (Fin d → K)) (hM : M.FG) (hL : L.FG) :
    {w : HeightOneSpectrum (𝓞 K) | Formalism.DivisionValues.idx w M (Formalism.DivisionValues.matLat θ L) ≠ 0}.Finite :=
  GlobalTheory.Mem.IdxFin.lidx_finite M _ hM (hL.map _)

end GlobalTheory.Mem.NonzeroPlacesOverPrimes

end
end
