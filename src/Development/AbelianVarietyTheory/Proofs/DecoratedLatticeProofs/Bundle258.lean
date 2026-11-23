module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle229
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle383
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle207
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle064
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.CommensuratedOfIsOpenIsCompact
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle015
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.KSplit

open GlobalTheory.FinPl.SetCut

variable {D : D7}

theorem idAt_mono {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) {a : AE D} (ha : a ∈ idAt D P) : a ∈ idAt D P' := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha ⊢
  exact ⟨ha.1, fun w hw => ha.2 w fun h' => hw (h w h')⟩

theorem latV_mono (V : HSp D) (L : Lat V) {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) : latV V L P ≤ latV V L P' := by
  apply AddSubgroup.closure_mono
  rintro y ⟨α, hα, h0, r⟩
  exact ⟨α, hα, fun v hv => h0 v fun h' => hv (h v h'), r⟩

theorem mul_mem_idAt {P R : Pl D → Prop} {c : AE D} (hc : ∀ w, ¬ R w → compAt D w c = 0) {a : AE D}
    (ha : a ∈ idAt D P) : c * a ∈ idAt D (fun p => P p ∧ R p) := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha ⊢
  refine ⟨by rw [RingHom.map_mul, ha.1, mul_zero], fun w hw => ?_⟩
  rw [RingHom.map_mul]
  by_cases h : R w
  · rw [ha.2 w fun h' => hw ⟨h', h⟩, mul_zero]
  · rw [hc w h, zero_mul]

theorem smul_mem_latV (V : HSp D) (L : Lat V) {P R : Pl D → Prop} (β : Af D.host.F) (hβ : β ∈ intAf D.host.F)
    (h0 : ∀ v, ¬ R v → evalV D.host.F v β = 0) {y : Fin V.rank → AE D} (hy : y ∈ latV V L P) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) • y ∈ latV V L (fun p => P p ∧ R p) := by
  have main : latV V L P ≤ (latV V L (fun p => P p ∧ R p)).comap
      (DistribSMul.toAddMonoidHom (Fin V.rank → AE D) (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β))) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hα0, a, ha, x, hx, rfl⟩
    refine AddSubgroup.subset_closure ⟨β * α, fun v => by rw [map_mul]; exact mul_mem (hβ v) (hα v), fun v hv => ?_,
      a, ha, x, hx, ?_⟩
    · rw [map_mul]
      by_cases h : R v
      · rw [hα0 v fun h' => hv ⟨h', h⟩, mul_zero]
      · rw [h0 v h, zero_mul]
    · funext i
      change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      congr 1
      exact Prod.ext (mul_zero _) rfl
  exact main hy

theorem indQ_int (Q : Finset (Pl D)) : indQ D Q ∈ intAf D.host.F := by
  intro v
  rw [evalV_indQ]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem indQc_int (Q : Finset (Pl D)) : 1 - indQ D Q ∈ intAf D.host.F := by
  intro v
  rw [map_sub, map_one]
  exact sub_mem (one_mem _) (indQ_int Q v)

abbrev eQ (Q : Finset (Pl D)) : AE D := algebraMap (AF D.host.F) (AE D) (idemQ D Q)

theorem eQ_off (Q : Finset (Pl D)) (w : Pl D) (hw : ¬ w ∈ Q) : compAt D w (eQ Q) = 0 := by
  rw [(parts_idemQ Q).2 w, if_neg hw]

theorem one_sub_eQ_off (Q : Finset (Pl D)) (w : Pl D) (hw : ¬ w ∉ Q) : compAt D w (1 - eQ Q) = 0 := by
  rw [RingHom.map_sub, RingHom.map_one, (parts_idemQ Q).2 w, if_pos (not_not.1 hw), sub_self]

theorem eQ_mul_of_in {P : Pl D → Prop} (Q : Finset (Pl D)) {a : AE D} (ha : a ∈ idAt D (fun p => P p ∧ p ∈ Q)) :
    eQ Q * a = a :=
  (mem_idAt_Q_iff Q a).1 (idAt_mono (fun _ h => h.2) ha)

theorem eQ_mul_of_out {P : Pl D → Prop} (Q : Finset (Pl D)) {a : AE D} (ha : a ∈ idAt D (fun p => P p ∧ p ∉ Q)) :
    eQ Q * a = 0 := by
  classical
  refine (mem_idOff_iff_mul (· ∈ Q) _ (parts_idemQ Q).1 (fun w => by convert (parts_idemQ Q).2 w) a).1 ?_
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]
  intro w hw
  exact ((mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere _ _ _).1 ha).2 w fun h => h.2 hw

theorem one_sub_mul_eq {P : Pl D → Prop} (Q : Finset (Pl D)) {a : AE D} (ha : a ∈ idAt D P) :
    (1 - eQ Q) * a = algebraMap (AF D.host.F) (AE D) (idemQc D Q) * a := by
  rw [← sub_eq_zero]
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha
  apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
  · rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, ha.1, mul_zero, mul_zero, sub_zero]
  · intro w
    rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, (parts_idemQ Q).2 w,
      (parts_idemQc Q).2 w]
    split_ifs
    · rw [sub_self, sub_self]
    · rw [sub_zero, sub_self]

theorem mem_latV_iff_parts (V : HSp D) (L : Lat V) (P : Pl D → Prop) (Q : Finset (Pl D)) {y : Fin V.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D P) :
    y ∈ latV V L P ↔ eQ Q • y ∈ latV V L (fun p => P p ∧ p ∈ Q) ∧
      (1 - eQ Q) • y ∈ latV V L (fun p => P p ∧ p ∉ Q) := by
  constructor
  · intro h
    refine ⟨smul_mem_latV V L (indQ D Q) (indQ_int Q) (fun v hv => by rw [evalV_indQ, if_neg hv]) h, ?_⟩
    have e : (1 - eQ Q) • y = algebraMap (AF D.host.F) (AE D) (idemQc D Q) • y :=
      funext fun i => one_sub_mul_eq Q (hy i)
    rw [e]
    exact smul_mem_latV V L (1 - indQ D Q) (indQc_int Q)
      (fun v hv => by rw [map_sub, map_one, evalV_indQ, if_pos (not_not.1 hv), sub_self]) h
  · rintro ⟨h1, h2⟩
    have e : y = eQ Q • y + (1 - eQ Q) • y := by rw [← add_smul, add_sub_cancel, one_smul]
    rw [e]
    exact add_mem (latV_mono V L (fun _ h => h.1) h1) (latV_mono V L (fun _ h => h.1) h2)

theorem mt_mul (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := rfl

theorem mt_inj (V : HSp D) {a b : GA D V} (h : mt V a = mt V b) : a = b :=
  Subtype.ext (Units.ext h)

theorem mulVec_mem (V : HSp D) {I : Ideal (AE D)} (M : Matrix (Fin V.rank) (Fin V.rank) (AE D))
    {y : Fin V.rank → AE D} (hy : ∀ i, y i ∈ I) (i : Fin V.rank) : (M *ᵥ y) i ∈ I := by
  simp only [Matrix.mulVec, dotProduct]
  exact I.sum_mem fun j _ => I.mul_mem_left _ (hy j)

section Ring

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem cut_sub_one (c : A) (M : Matrix n n A) : c • M + (1 - c) • (1 : Matrix n n A) - 1 = c • (M - 1) := by
  module

theorem cut_mulVec (c : A) (M : Matrix n n A) (y : n → A) (hy : c • y = y) :
    (c • M + (1 - c) • (1 : Matrix n n A)) *ᵥ y = M *ᵥ y := by
  rw [add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, ← mulVec_smul, hy, sub_smul, hy, one_smul, sub_self, add_zero]

theorem cut_mul_cut (c : A) (hc : c * c = c) (M : Matrix n n A) :
    (c • M + (1 - c) • (1 : Matrix n n A)) * ((1 - c) • M + (1 - (1 - c)) • (1 : Matrix n n A)) = M := by
  have h1 : c * (1 - c) = 0 := by linear_combination -hc
  have h2 : (1 - c) * c = 0 := by linear_combination -hc
  have h3 : (1 - c) * (1 - c) = 1 - c := by linear_combination hc
  simp only [sub_sub_cancel, add_mul, mul_add, smul_mul_smul_comm, h1, h2, h3, hc, zero_smul, mul_one, one_mul,
    zero_add, add_zero]
  module

theorem prod_parts (c : A) (a b : Matrix n n A) (ha : c • (a - 1) = a - 1) (hb : c • (b - 1) = 0) (y : n → A) :
    c • ((a * b) *ᵥ y) = a *ᵥ (c • y) ∧ (1 - c) • ((a * b) *ᵥ y) = b *ᵥ ((1 - c) • y) := by
  have h1 : c • b = c • (1 : Matrix n n A) := by rw [← sub_eq_zero, ← smul_sub, hb]
  have h2 : (1 - c) • a = (1 - c) • (1 : Matrix n n A) := by
    rw [← sub_eq_zero, ← smul_sub, sub_smul, ha, one_smul, sub_self]
  constructor
  · rw [← smul_mulVec, ← mul_smul_comm, h1, mul_smul_comm, mul_one, smul_mulVec, mulVec_smul]
  · rw [← smul_mulVec, ← smul_mul_assoc, h2, smul_mul_assoc, one_mul, smul_mulVec, mulVec_smul]

end Ring

theorem inK_cut (V : HSp D) (L : Lat V) {P R : Pl D → Prop} (ε : AF D.host.F) (hε : ε * ε = ε)
    (hoff : ∀ w, ¬ R w → compAt D w (algebraMap (AF D.host.F) (AE D) ε) = 0)
    (hone : ∀ a ∈ idAt D (fun p => P p ∧ R p), algebraMap (AF D.host.F) (AE D) ε * a = a)
    (hlat : ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ idAt D P) → y ∈ latV V L P →
      algebraMap (AF D.host.F) (AE D) ε • y ∈ latV V L (fun p => P p ∧ R p))
    {κ : GA D V} (hκ : InK V L P κ) : InK V L (fun p => P p ∧ R p) (cutG V ε hε κ) := by
  have key : ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ idAt D (fun p => P p ∧ R p)) →
      (y ∈ latV V L (fun p => P p ∧ R p) ↔ y ∈ latV V L P) := by
    intro y hy
    refine ⟨fun h => latV_mono V L (fun _ h => h.1) h, fun h => ?_⟩
    have e : algebraMap (AF D.host.F) (AE D) ε • y = y := funext fun i => hone _ (hy i)
    have := hlat y (fun i => idAt_mono (fun _ h => h.1) (hy i)) h
    rwa [e] at this
  refine ⟨(mem_congGrp_iff V _ _).2 fun i j => ?_, fun y hy => ?_⟩
  · rw [mt_cutG, cut_sub_one]
    exact mul_mem_idAt hoff ((mem_congGrp_iff V _ _).1 hκ.1 i j)
  · have e : algebraMap (AF D.host.F) (AE D) ε • y = y := funext fun i => hone _ (hy i)
    rw [mt_cutG, cut_mulVec _ _ _ e, key y hy, key _ (mulVec_mem V _ hy)]
    exact hκ.2 y fun i => idAt_mono (fun _ h => h.1) (hy i)

theorem inK_iff_prod : ∀ (D : D7) (V : HSp D) (L : Lat V) (P : Pl D → Prop) (Q : Finset (Pl D)) (κ : GA D V),
    InK V L P κ ↔ ∃ a b, InK V L (fun p => P p ∧ p ∈ Q) a ∧ InK V L (fun p => P p ∧ p ∉ Q) b ∧ κ = a * b := by
  intro D V L P Q κ
  have e1 : algebraMap (AF D.host.F) (AE D) (1 - idemQ D Q) = 1 - eQ Q := by rw [map_sub, map_one]
  constructor
  · intro hκ
    refine ⟨cutG V _ (idemQ_mul_self Q) κ, cutG V _ (one_sub_idemQ_mul_self Q) κ,
      inK_cut V L _ _ (eQ_off Q) (fun a ha => eQ_mul_of_in Q ha)
        (fun y hy h => ((mem_latV_iff_parts V L P Q hy).1 h).1) hκ,
      inK_cut V L _ _ (by rw [e1]; exact one_sub_eQ_off Q)
        (fun a ha => by rw [e1, sub_mul, eQ_mul_of_out Q ha, one_mul, sub_zero])
        (fun y hy h => by rw [e1]; exact ((mem_latV_iff_parts V L P Q hy).1 h).2) hκ, mt_inj V ?_⟩
    rw [mt_mul, mt_cutG, mt_cutG, e1]
    exact (cut_mul_cut _ (by rw [← map_mul, idemQ_mul_self]) _).symm
  · rintro ⟨a, b, ha, hb, rfl⟩
    have hA := (mem_congGrp_iff V _ _).1 ha.1
    have hB := (mem_congGrp_iff V _ _).1 hb.1
    refine ⟨mul_mem ((mem_congGrp_iff V _ _).2 fun i j => idAt_mono (fun _ h => h.1) (hA i j))
      ((mem_congGrp_iff V _ _).2 fun i j => idAt_mono (fun _ h => h.1) (hB i j)), fun y hy => ?_⟩
    have hp := prod_parts (eQ Q) (mt V a) (mt V b) (Matrix.ext fun i j => eQ_mul_of_in Q (hA i j))
      (Matrix.ext fun i j => eQ_mul_of_out Q (hB i j)) y
    rw [mem_latV_iff_parts V L P Q hy, mem_latV_iff_parts V L P Q (mulVec_mem V _ hy), mt_mul, hp.1, hp.2]
    exact and_congr (ha.2 _ fun i => mul_mem_idAt (eQ_off Q) (hy i))
      (hb.2 _ fun i => mul_mem_idAt (one_sub_eQ_off Q) (hy i))

end GlobalTheory.FinPl.KSplit

end
end

section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SphSmooth

open GlobalTheory.SiegelSet (IsRealLine lineDer)

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem isRealLine_oneP (hθ : IsInfFam θ) (V : HSp D) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    IsRealLine D.sp.cm.sig V.gram (oneP θ V τ X) := by
  refine ⟨placeOf D τ, embOverOf D τ, X, hX, fun t => ?_⟩
  obtain ⟨x, hx⟩ := exists_archEquiv_eq V (embOverOf D τ) rfl
    (GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) hX t)
  refine ⟨x, ?_, ?_⟩
  · rw [oneP, ← hx, atTau_archEquiv hθ V _ rfl x]
  · rw [GlobalTheory.Orb.archMat_eq_archEquiv _ (isCMExt_host D), hx]

theorem mem_smFun_of_isSm (hθ : IsInfFam θ) {f : GA D V → ℂ} (h : GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram f) :
    f ∈ SmFun θ V :=
  fun k τs Xs hX g => h k (fun i => oneP θ V (τs i) (Xs i)) (fun i => isRealLine_oneP hθ V (hX i)) g

def derSpan (V : HSp D) (f : GA D V → ℂ) : Submodule ℂ (GA D V → ℂ) :=
  Submodule.span ℂ {g | ∃ l : List (ℝ → GA D V), (∀ γ ∈ l, IsRealLine D.sp.cm.sig V.gram γ) ∧ g = l.foldr lineDer f}

theorem derSpan_le (hθ : IsInfFam θ) {f : GA D V → ℂ} (hf : f ∈ SmFun θ V) : derSpan V f ≤ SmFun θ V := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨l, hl, rfl⟩
  induction l with
  | nil => exact hf
  | cons γ l ih =>
    obtain ⟨p, hp, rfl⟩ := (hl γ List.mem_cons_self).eq_oneP hθ
    exact GlobalTheory.Mem.AutSpace.Rder_mem (ih fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)) hp

end GlobalTheory.SphSmooth

end
end

section

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CentreComm

open GlobalTheory.Mem.AutSpace

variable {D : D7} {θ : InfFam D} {V : HSp D}


variable (θ V) in
def CommOnSm (A B : (GA D V → ℂ) → (GA D V → ℂ)) : Prop := ∀ f ∈ SmFun θ V, A (B f) = B (A f)

theorem lin_sum {T : (GA D V → ℂ) → (GA D V → ℂ)} (hT : LinOnSm θ V T) {α : Type} (s : Finset α)
    (g : α → GA D V → ℂ) (hg : ∀ a ∈ s, g a ∈ SmFun θ V) : T (∑ a ∈ s, g a) = ∑ a ∈ s, T (g a) := by
  induction s using Finset.induction_on with
  | empty => simpa using hT.smul 0 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hT.add _ (hg a (by simp)) _
      (Submodule.sum_mem _ fun b hb => hg b (by simp [hb])), ih fun b hb => hg b (by simp [hb])]

theorem comm_foldr {T : (GA D V → ℂ) → (GA D V → ℂ)} {α : Type} (A : α → (GA D V → ℂ) → (GA D V → ℂ))
    (l : List α) (hl : ∀ a ∈ l, LinOnSm θ V (A a)) (hc : ∀ a ∈ l, CommOnSm θ V T (A a)) :
    CommOnSm θ V T fun f => l.foldr (fun a g => A a g) f := by
  induction l with
  | nil => exact fun _ _ => rfl
  | cons a l ih =>
    intro f hf
    have h2 := linOnSm_foldr A l fun b hb => hl b (by simp [hb])
    simp only [List.foldr_cons]
    rw [hc a (by simp) _ (h2.mem f hf), ih (fun b hb => hl b (by simp [hb])) (fun b hb => hc b (by simp [hb])) f hf]

theorem comm_gelf {T : (GA D V → ℂ) → (GA D V → ℂ)} (hT : LinOnSm θ V T) {τ : D.what₂.Tau}
    (hc : ∀ Z, CommOnSm θ V T (RderC θ V τ Z)) (k : ℕ) : CommOnSm θ V T (gelf θ V τ k) := by
  have hl : ∀ idx : Fin (k + 1) → Fin V.rank, ∀ S ∈ (List.ofFn fun a : Fin (k + 1) =>
      RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)), LinOnSm θ V S ∧ CommOnSm θ V T S := fun idx S hS => by
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hS
    exact ⟨linOnSm_RderC τ _, hc _⟩
  intro f hf
  simp only [gelf]
  rw [lin_sum hT _ _ fun idx _ => (linOnSm_foldr (fun S => S) _ fun S hS => (hl idx S hS).1).mem f hf]
  exact Finset.sum_congr rfl fun idx _ =>
    comm_foldr (fun S => S) _ (fun S hS => (hl idx S hS).1) (fun S hS => (hl idx S hS).2) f hf

theorem gelf_RderC (hθ : IsInfFam θ) (τ τ' : D.what₂.Tau) (k : ℕ) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    CommOnSm θ V (gelf θ V τ k) (RderC θ V τ' Z) := by
  intro f hf
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ' Z
  simp only [RderC]
  rw [(linOnSm_gelf τ k).add _ (Rder_mem hf h1) _ (Submodule.smul_mem _ _ (Rder_mem hf h2)), (linOnSm_gelf τ k).smul,
    GlobalTheory.CuspLie.gelf_Rder hθ h1 hf, GlobalTheory.CuspLie.gelf_Rder hθ h2 hf]

end GlobalTheory.CentreComm

end
end

section

open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

noncomputable section

namespace GlobalTheory.ZonalBorel

open GlobalTheory.PRep Formalism.UG

section Abstract

variable {G X V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup V] [Module ℂ V]

theorem exists_fixed_sum_eq {ρ : Representation ℂ G X} {π : Representation ℂ G V} (hρ : IsSmooth ρ)
    {K : Subgroup G} (hK : IsCompact (K : Set G)) (f : ρ.IntertwiningMap π) (hf : Function.Surjective f)
    (E : X →ₗ[ℂ] ℂ) (hE : ∀ u : X, (∀ x ∈ K, ρ x u = u) → E u = 0 → u = 0) {v : V} (hv : v ∈ fixed π K)
    (l : Module.Dual ℂ V) (hlv : l v = 1) :
    ∃ z : X, (∀ x ∈ K, ρ x z = z) ∧ E z = 1 ∧ ∀ S : Finset (G ⧸ K), (∀ x ∈ K, ∀ c ∈ S, x • c ∈ S) →
      ∑ c ∈ S, l (π c.out v) = ∑ c ∈ S, E (ρ c.out z) := by
  obtain ⟨u, rfl⟩ := hf v
  obtain ⟨w, hw, hfw⟩ := IwahoriOnto.exists_fixed_map_eq hρ hK f.toLinearMap u fun h hh => by
    show f (ρ h u) = f u
    rw [f.isIntertwining]
    simpa using hv ⟨h, hh⟩
  have hw' : ∀ x ∈ K, ρ x w = w := fun x hx => by simpa using hw ⟨x, hx⟩
  have hfw' : f w = f u := hfw
  have hEw : E w ≠ 0 := fun h => by
    have h0 := hE w hw' h
    rw [h0, map_zero] at hfw'
    rw [← hfw', map_zero] at hlv
    exact zero_ne_one hlv
  refine ⟨(E w)⁻¹ • w, fun x hx => by rw [map_smul, hw' x hx], by simp [hEw], fun S hS => ?_⟩
  set z := (E w)⁻¹ • w with hz
  have hzK : ∀ x ∈ K, ρ x z = z := fun x hx => by rw [hz, map_smul, hw' x hx]
  have hEz : E z = 1 := by simp [hz, hEw]
  have hfz : f z = (E w)⁻¹ • f u := by rw [hz, map_smul, hfw']
  have h1 := hE (∑ c ∈ S, ρ c.out z - (∑ c ∈ S, E (ρ c.out z)) • z)
    (fun x hx => by rw [map_sub, Rep.sum_fixed ρ K hzK S hS x hx, map_smul, hzK x hx])
    (by rw [map_sub, map_sum, map_smul, hEz, smul_eq_mul, mul_one, sub_self])
  have h2 := congrArg (fun y => l (f y)) (sub_eq_zero.1 h1)
  have hI : ∀ c : G ⧸ K, f (ρ c.out z) = π c.out (f z) := fun c => f.isIntertwining _ _ _ _

  simp only [map_sum, map_smul, hI, hfz, smul_eq_mul, hlv, mul_one] at h2
  rw [← Finset.mul_sum] at h2
  exact (mul_right_injective₀ (inv_ne_zero hEw)).eq_iff.1 (h2.trans (mul_comm _ _))

end Abstract

theorem exists_isBorelSph_hAct_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (α : Fin n → ℂˣ), HasSatake π α → ∀ ω : GL (Fin n) k → ℂ, IsZonal π (KO k (Fin n)) ω → ∃ φ : GL (Fin n) k → ℂ, IsBorelSph k (fun i : Fin n => (α i : ℂ) * (((resCard k : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ)) φ ∧ ∀ g, Formalism.UG.hAct (KO k (Fin n)) (Formalism.UG.dosetInd ℂ (KO k (Fin n)) g) ω 1 = Formalism.UG.hAct (KO k (Fin n)) (Formalism.UG.dosetInd ℂ (KO k (Fin n)) g) φ 1 := by
  intro k _ _ _ _ n V _ _ π α ⟨_, _hs, S, f, hf⟩ ω ⟨v, hv, l, _hl, hlv, hω⟩
  have hsm : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth ⟨S, .id _, Function.surjective_id⟩ (isSmooth_parInd _ _)
  let E : S.toSubmodule →ₗ[ℂ] ℂ := ⟨⟨fun u => u.1.1.1 1, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  have hr : ∀ u : S.toSubmodule, (∀ x ∈ KO k (Fin n), S.toRepresentation x u = u) →
      ∀ g, ∀ x ∈ KO k (Fin n), u.1.1.1 (g * x) = u.1.1.1 g := fun u h g x hx =>
    congrArg (fun z : S.toSubmodule => z.1.1.1 g) (h x hx)
  obtain ⟨z, hzK, hEz, key⟩ := exists_fixed_sum_eq hsm SplitFlip.isCompact_KO f hf E (fun u h h0 => by
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun g => ?_)))
    obtain ⟨b, hb, x, hx, rfl⟩ := iwasawa_blockTriangular k (Fin n) Fin.val g
    have h1 := parInd_law _ _ u.1 ⟨b, (mem_borel _).2 hb⟩ 1
    have h2 : u.1.1.1 1 = 0 := h0
    rw [h2, map_zero, smul_zero, mul_one] at h1
    exact (hr u h b x hx).trans h1) hv l hlv
  refine ⟨fun g => z.1.1.1 g, ⟨hr z hzK, fun b hb t ht => ?_⟩, fun g => ?_⟩
  · have h1 := Rep.law α z.1 b hb t ht 1
    have h2 : z.1.1.1 1 = 1 := hEz
    rwa [h2, mul_one, mul_one] at h1
  · have hK : IsCommensurated (KO k (Fin n)) :=
      PI.UnitaryGroupMassFormula.AdIndexEq.commensurated_of_isOpen_isCompact _ SplitFlip.isOpen_KO SplitFlip.isCompact_KO
    have hfin := Formalism.UG.P.finite_support_cosets hK (Formalism.UG.Final.DosetIndMem _ (KO k (Fin n)) ℂ g).2
    have hmem : ∀ c : GL (Fin n) k ⧸ KO k (Fin n), c ∈ hfin.toFinset ↔
        c.out ∈ DoubleCoset.doubleCoset g (KO k (Fin n) : Set (GL (Fin n) k)) (KO k (Fin n)) := fun c => by
      simp [dosetInd]
    have hT : ∀ x ∈ KO k (Fin n), ∀ c ∈ hfin.toFinset, x • c ∈ hfin.toFinset := by
      intro x hx c hc
      obtain ⟨a, ha, rfl⟩ := (GlobalTheory.ChainOnto.out_mem_doubleCoset_iff g c).1 ((hmem c).1 hc)
      refine (hmem _).2 ((GlobalTheory.ChainOnto.out_mem_doubleCoset_iff g _).2 ⟨x * a, mul_mem hx ha, ?_⟩)
      rw [mul_assoc]
      rfl
    have e : ∀ F : GL (Fin n) k → ℂ, hAct (KO k (Fin n)) (dosetInd ℂ (KO k (Fin n)) g) F 1 =
        ∑ c ∈ hfin.toFinset, F c.out := by
      intro F
      rw [hAct, finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
      · refine Finset.sum_congr rfl fun c hc => ?_
        rw [dosetInd, Set.indicator_of_mem ((hmem c).1 hc), one_mul, Pi.one_apply, one_smul]
      · intro c hc
        rw [Function.mem_support] at hc
        refine (hmem c).2 ?_
        by_contra h
        rw [dosetInd, Set.indicator_of_notMem h, zero_smul] at hc
        exact hc rfl
    rw [e, e]
    refine ((Finset.sum_congr rfl fun c _ => hω c.out).trans (key _ hT)).trans
      (Finset.sum_congr rfl fun c _ => ?_)
    show z.1.1.1 (1 * c.out) = _
    rw [one_mul]

end GlobalTheory.ZonalBorel
end
end
