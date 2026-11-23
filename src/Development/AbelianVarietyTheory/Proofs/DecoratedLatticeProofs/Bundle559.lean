module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle347
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle557
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle539
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle165
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle151
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle184
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle419
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem nonempty_orthDec_zero (D : D7) (S : HSp D) : Nonempty (OrthDec S S (diagSp D 0 ![] 0 0)) :=
  ⟨{ iA := 1
     iB := 0
     isoA := by simp
     isoB := funext fun i => Fin.elim0 i
     orth := funext fun i => Fin.elim0 i
     rank_add := rfl }⟩

private theorem s_finite_of_sigma_finite {X : Type} [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν] : SFinite ν :=
  inferInstance

theorem evalBF_of_descent : ∀ D : D7, Descent D → EvalBF D := by
  intro D hD ψ ρ B J s φ G Φ hφ hG hΦ ν₀ 𝓝₀ hν₀ h𝓝₀ h1
  obtain ⟨om', hom'⟩ := (hD ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W
  obtain ⟨j1, j2, j3⟩ := GlobalTheory.UnitU.topology D ρ
  have : BorelSpace (GA D J.W) := ⟨rfl⟩
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have := s.vW.haar
  have := s.vU.unit.1
  have : SigmaCompactSpace (UX D ρ) := inferInstance
  have : IsFiniteMeasureOnCompacts s.vU.ν := inferInstance
  have : IsLocallyFiniteMeasure s.vU.ν := inferInstance
  have : SigmaFinite s.vU.ν := inferInstance
  have : SFinite s.vU.ν := s_finite_of_sigma_finite s.vU.ν
  obtain ⟨hc0, hH0, hI0, hI, hF⟩ := GlobalTheory.T.fourierJacobi_measure_unitriangular_coordinates D ρ J s.vU ν₀ 𝓝₀ hν₀ h𝓝₀ h1
  obtain ⟨o⟩ := nonempty_orthDec_zero D J.W₀
  obtain ⟨⟨hc, hH⟩, -⟩ := GlobalTheory.T.fourierJacobi_bessel_groups_closed_haar_product D J.W J.W₀ J.W₀ (diagSp D 0 ![] 0 0) ρ J.d o J.vN.ν J.vN.𝓝 J.vN.unit
  obtain ⟨hcont, hinv⟩ := GlobalTheory.T.besselUnfolding_evaluationIntegrand_continuous_invariant D ψ ρ B J s om' hom' φ G Φ hφ hG hΦ
  have hrel := GlobalTheory.T.flatPeriod_eq_integral_evaluationPeriods D ψ ρ B J s om' hom' φ G Φ hφ hG hΦ
  have habs := GlobalTheory.T.evaluationForm_absolute_convergence D ψ ρ B J s om' hom' φ G Φ hφ hG hΦ
  have hU := GlobalTheory.T.besselPeriod_thetaLift_unfolding D hD ψ ρ B J s φ G Φ hφ hG hΦ
  rw [funext fun h => (hrel h).2] at hU
  exact GlobalTheory.T.invariant_integral_in_stages_alt (GA D J.W) s.vW.μ (radX J.d ⊔ J.d.emb0.range) (jacGrp J.d) hc0 hc
    (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀) J.μR hH0 hI0 (hH _ J.v0.haar) hI (UX D ρ) s.vU.ν (fun u => J.d.levi u.1)
    (J.d.continuous_levi.comp continuous_subtype_val).measurable hF _ hcont.measurable hinv (fun h => (hrel h).1) habs _ hU

end GlobalTheory.Unf
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocComb

open GlobalTheory.ExportSeries

theorem ratDatum_insert (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (hPP : PP ∉ P)
    (hs : SplitSet (insert PP P)) (c : WO S T →₀ ℂ) (Ξl : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ)
    (hloc : GlobalTheory.LocMod.IsLocFac D ψ S T PP c Ξl)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hSd : IsSelfDualC S ΛS) (hTd : IsSelfDualC T ΛT) (hSi : (ΛS : Set (Fin S.rank → D.host.E)) = intVec D S.rank)
    (hTi : (ΛT : Set (Fin T.rank → D.host.E)) = intVec D T.rank) (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ)
    (f₀ f : WO S T → ℂ) (h0 : IsThetaFunO ψ S T f₀) (h1 : IsLatVac (heisO ψ S T) (stdHom S T) f₀)
    (hf : IsRatDatum ψ S T (idem P) Ξ f₀ f) :
    IsRatDatum ψ S T (idem (insert PP P)) (fun γ => Ξ γ * Ξl γ) f₀ (comb ψ S T c f) := by
  obtain ⟨k, _, _, _, _, p, Y, Y', _, _, _, _, FS, FT, Ξk, hd, hat, hint, hSB, hcomb, hΞ⟩ := hloc
  have hP : SplitSet P := hs.mono (Finset.subset_insert _ _)
  have he : idem P + p.e = idem (insert PP P) := by
    rw [idem, idem, Finset.sum_insert hPP, idemAt_eq hat, add_comm]
  have hs' : IsIdemSum (idem P + p.e) (@insert _ _ (@Finset.instInsert _ (Classical.decEq _)) PP P) := by
    rw [he]
    convert hs.isIdemSum
  have key := GlobalTheory.T.rationalDatum_splitPlace_combination_mul_local D k p ψ hψ hd S T Y Y' FS FT P PP (idem P) hPP hat hP.isIdemSum hs' hint ΛS ΛT hSd hTd hSi hTi Ξ Ξk hSB c
    hcomb f₀ f h0 h1 hf
  rw [he] at key
  have hfun : (fun γ => Ξ γ * Ξk (FT.γ * γ.map p.pr * FS.β)) = fun γ => Ξ γ * Ξl γ :=
    funext fun γ => by rw [hΞ γ]
  rwa [hfun] at key

theorem ratDatum_list (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (P₀ Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (n : ℕ) (PPn : Fin n → Formalism.L2.DIV.Pl D.host.E)
    (hinj : Function.Injective PPn) (hQ : ∀ i, PPn i ∈ Q) (hdis : Disjoint P₀ Q) (hs : SplitSet (P₀ ∪ Q))
    (c : Fin n → WO S T →₀ ℂ) (Ξl : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ)
    (hloc : ∀ i, GlobalTheory.LocMod.IsLocFac D ψ S T (PPn i) (c i) (Ξl i))
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hSd : IsSelfDualC S ΛS) (hTd : IsSelfDualC T ΛT) (hSi : (ΛS : Set (Fin S.rank → D.host.E)) = intVec D S.rank)
    (hTi : (ΛT : Set (Fin T.rank → D.host.E)) = intVec D T.rank)
    (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (f₀ f : WO S T → ℂ) (h0 : IsThetaFunO ψ S T f₀)
    (h1 : IsLatVac (heisO ψ S T) (stdHom S T) f₀) (hf : IsRatDatum ψ S T (idem P₀) Ξ f₀ f) :
    ∀ L : List (Fin n), L.Nodup →
      IsRatDatum ψ S T (idem (P₀ ∪ (L.map PPn).toFinset)) (fun γ => Ξ γ * (L.map fun i => Ξl i γ).prod) f₀
        (L.foldr (fun i g => comb ψ S T (c i) g) f) := by
  intro L
  induction L with
  | nil =>
    intro _
    have : (fun γ => Ξ γ * (([] : List (Fin n)).map fun i => Ξl i γ).prod) = Ξ := funext fun γ => by simp
    simpa [this] using hf
  | cons i L ih =>
    intro hnd
    rw [List.nodup_cons] at hnd
    have hsub : P₀ ∪ ((i :: L).map PPn).toFinset ⊆ P₀ ∪ Q := by
      intro x hx
      rcases Finset.mem_union.1 hx with h | h
      · exact Finset.mem_union_left _ h
      · obtain ⟨j, -, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact Finset.mem_union_right _ (hQ j)
    have hins : P₀ ∪ ((i :: L).map PPn).toFinset = insert (PPn i) (P₀ ∪ (L.map PPn).toFinset) := by
      rw [List.map_cons, List.toFinset_cons, Finset.union_insert]
    have hnot : PPn i ∉ P₀ ∪ (L.map PPn).toFinset := by
      intro h
      rcases Finset.mem_union.1 h with h | h
      · exact Finset.disjoint_left.1 hdis h (hQ i)
      · obtain ⟨j, hj, hji⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact hnd.1 (hinj hji ▸ hj)
    have step := ratDatum_insert D ψ hψ S T _ (PPn i) hnot (hins ▸ hs.mono hsub) (c i) (Ξl i) (hloc i) ΛS ΛT hSd hTd hSi hTi _ f₀ _ h0 h1
      (ih hnd.2)
    rw [← hins] at step
    have hfun : (fun γ => Ξ γ * (L.map fun i => Ξl i γ).prod * Ξl i γ) =
        fun γ => Ξ γ * ((i :: L).map fun i => Ξl i γ).prod := funext fun γ => by
      rw [List.map_cons, List.prod_cons]; ring
    rw [hfun] at step
    simpa only [List.foldr_cons] using step

theorem ratDatum_foldr_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (P₀ Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (n : ℕ) (PPn : Fin n → Formalism.L2.DIV.Pl D.host.E), Function.Injective PPn → (∀ PP, PP ∈ Q ↔ ∃ i, PPn i = PP) → Disjoint P₀ Q → ∀ (c : Fin n → WO S T →₀ ℂ) (Ξl : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ), (∀ i, GlobalTheory.LocMod.IsLocFac D ψ S T (PPn i) (c i) (Ξl i)) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = intVec D S.rank → (ΛT : Set (Fin T.rank → D.host.E)) = intVec D T.rank → ∀ (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (f₀ f : WO S T → ℂ), IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → (∀ e₀, IsIdemSum e₀ P₀ → IsRatDatum ψ S T e₀ Ξ f₀ f) → ∀ e, IsIdemSum e (P₀ ∪ Q) → IsRatDatum ψ S T e (fun γ => Ξ γ * ∏ i, Ξl i γ) f₀ ((List.finRange n).foldr (fun i g => comb ψ S T (c i) g) f) := by
  intro D ψ hψ S T P₀ Q n PPn hinj hQ hdis c Ξl hloc ΛS ΛT hSd hTd hSi hTi Ξ f₀ f h0 h1 hrat e he
  have hs : SplitSet (P₀ ∪ Q) := ⟨e, he⟩
  have hQ' : ∀ i, PPn i ∈ Q := fun i => (hQ _).2 ⟨i, rfl⟩
  have hP₀ : SplitSet P₀ := hs.mono Finset.subset_union_left
  have key := ratDatum_list D ψ hψ S T P₀ Q n PPn hinj hQ' hdis hs c Ξl hloc ΛS ΛT hSd hTd hSi hTi Ξ f₀ f h0 h1
    (hrat _ hP₀.isIdemSum) (List.finRange n) (List.nodup_finRange n)
  have hset : ((List.finRange n).map PPn).toFinset = Q := by
    ext x
    simp only [List.mem_toFinset, List.mem_map, List.mem_finRange, true_and]
    exact ⟨fun ⟨i, hi⟩ => (hQ x).2 ⟨i, hi⟩, fun h => (hQ x).1 h⟩
  rw [hset, idem_eq he] at key
  have hfun : (fun γ => Ξ γ * ((List.finRange n).map fun i => Ξl i γ).prod) = fun γ => Ξ γ * ∏ i, Ξl i γ :=
    funext fun γ => by rw [Fin.prod_univ_def]
  rwa [hfun] at key

end GlobalTheory.LocComb
end
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.bessel_period_evaluation_unfolding_of_witt_descent : ∀ D : D7, Descent D → EvalBF D := by
  first | exact @GlobalTheory.Unf.evalBF_of_descent | exact GlobalTheory.Unf.evalBF_of_descent | (intros; apply GlobalTheory.Unf.evalBF_of_descent <;> assumption)

end
end
