module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle264
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle312
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2200
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle373
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle010
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1923
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle562
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle247
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftIdeal

def conjO (D : D7) : 𝓞 D.host.E ≃+* 𝓞 D.host.E :=
  RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv

theorem coe_conjO (D : D7) (x : 𝓞 D.host.E) :
    ((conjO D x : 𝓞 D.host.E) : D.host.E) = IsCMField.complexConj D.host.E (x : D.host.E) := rfl

theorem conjO_conjO (D : D7) (x : 𝓞 D.host.E) : conjO D (conjO D x) = x := by
  apply RingOfIntegers.ext
  rw [coe_conjO, coe_conjO]
  simp

theorem star_eq (D : D7) (x : D.host.E) : star x = IsCMField.complexConj D.host.E x := rfl

theorem conjI_eq_map (D : D7) (I : Ideal (𝓞 D.host.E)) :
    conjI I = I.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
  unfold conjI
  rw [Ideal.map]
  congr 1
  ext a
  constructor
  · rintro ⟨b, hb, h⟩
    refine ⟨b, hb, RingOfIntegers.ext ?_⟩
    rw [h]
    rfl
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩

theorem map_map_conjO (D : D7) (I : Ideal (𝓞 D.host.E)) :
    (I.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)).map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) = I := by
  rw [Ideal.map_map]
  have : ((conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)).comp (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) = RingHom.id _ :=
    RingHom.ext fun x => conjO_conjO D x
  rw [this, Ideal.map_id]

end GlobalTheory.LiftIdeal

end

noncomputable section

namespace GlobalTheory.LiftIdeal

open GlobalTheory.LiftLevel

theorem isMaximal_map (D : D7) (PP : Formalism.L2.DIV.Pl D.host.E) :
    (PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)).IsMaximal := by
  haveI := PP.isMaximal
  exact Ideal.map_isMaximal_of_equiv (conjO D)

theorem liftI_eq (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) :
    liftI Pg Q = ∏ PP ∈ Pg ∪ Q, PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
  unfold liftI
  exact Finset.prod_congr rfl fun PP _ => conjI_eq_map D _

theorem conjI_liftI (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) :
    conjI (liftI Pg Q) = ∏ PP ∈ Pg ∪ Q, PP.asIdeal := by
  rw [conjI_eq_map, liftI_eq]
  have := map_prod (Ideal.mapHom (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E))
    (fun PP : Formalism.L2.DIV.Pl D.host.E => PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)) (Pg ∪ Q)
  simp only [Ideal.mapHom_apply] at this
  rw [this]
  exact Finset.prod_congr rfl fun PP _ => map_map_conjO D _

theorem map_ne {D : D7} {e : AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S)
    {PP PP' : Formalism.L2.DIV.Pl D.host.E} (hP : PP ∈ S) (hP' : PP' ∈ S) :
    PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≠ PP'.asIdeal := by
  intro h
  refine GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he PP hP PP' hP' fun c hc => ?_
  refine ⟨conjO D c, h ▸ Ideal.mem_map_of_mem _ hc, ?_⟩
  rw [coe_conjO, star_eq]

theorem liftI_props : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), Pg.Nonempty →
    (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → IsIdemSum e (Pg ∪ Q) →
    GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ ∧ GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ ∧
      IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) ∧
      IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) := by
  intro D Pg Q e hne h2 he
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨P0, hP0⟩ := hne
    intro htop
    have hle : liftI Pg Q ≤ P0.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
      rw [liftI_eq]
      exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_union_left _ hP0))
    rw [htop] at hle
    exact (isMaximal_map D P0).ne_top (top_le_iff.1 hle)
  · rw [liftI_eq, ← Ideal.zero_eq_bot]
    refine Finset.prod_ne_zero_iff.2 fun PP _ => ?_
    rw [Ne, Ideal.zero_eq_bot,
      Ideal.map_eq_bot_iff_of_injective (f := (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)) (conjO D).injective]
    exact PP.ne_bot
  · rw [conjI_liftI, liftI_eq]
    refine IsCoprime.prod_left fun PP hP => IsCoprime.prod_right fun PP' hP' => ?_
    exact Ideal.isCoprime_iff_sup_eq.2
      ((isMaximal_map D PP).coprime_of_ne PP'.isMaximal (map_ne he hP hP'))
  · rw [liftI_eq]
    refine IsCoprime.prod_left fun PP hP => Ideal.isCoprime_iff_sup_eq.2 ?_
    have h2' : (2 : 𝓞 D.host.E) ∉ PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
      rw [Ideal.map_comap_of_equiv, Ideal.mem_comap, map_ofNat]
      exact h2 PP (Finset.mem_union.1 hP)
    exact (isMaximal_map D PP).out.2 _ (left_lt_sup.2 fun hle => h2' (hle (Ideal.mem_span_singleton_self 2)))

end GlobalTheory.LiftIdeal

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairLift.LowCusp

variable {D : D7}

theorem multT_ind {W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S)
    (J : Set (GA D W)) (χ : GA D W → ℂ) (P : (GA D W → ℂ) → Prop) (h0 : P 0)
    (hadd : ∀ φ φ', P φ → P φ' → P (φ + φ')) (hsmul : ∀ (c : ℂ) φ, P φ → P (c • φ))
    (hcusp : ∀ φ, IsAutFunSm θ W φ → IsCuspFun W φ → P φ)
    (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M) : P (F v) := by
  obtain ⟨T, hT, rfl⟩ := hF
  have key : ∀ w : M.Vec, P (T w) := by
    induction hT using Submodule.span_induction with
    | mem T hT => exact fun w => hcusp _ (hT.aut w) (hT.cusp w)
    | zero => intro w; simpa using h0
    | add T T' _ _ h h' => intro w; simpa using hadd _ _ (h w) (h' w)
    | smul c T _ h => intro w; simpa using hsmul c _ (h w)
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c w =>
    simpa using hsmul c _ (key w)
  | add x y hx hy =>
    simpa using hadd _ _ hx hy

theorem liftInt_add' {G H S : Type*} [MeasurableSpace H] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {s : S}
    {φ φ' : H → ℂ} {g : G} (h : IntegrableOn (fun x => th g x s * φ x) 𝓕 ν)
    (h' : IntegrableOn (fun x => th g x s * φ' x) 𝓕 ν) :
    Lift.liftInt ν 𝓕 th s (φ + φ') g = Lift.liftInt ν 𝓕 th s φ g + Lift.liftInt ν 𝓕 th s φ' g := by
  unfold Lift.liftInt
  rw [← integral_add h h']
  simp only [Pi.add_apply, mul_add]

theorem liftInt_smul' {G H S : Type*} [MeasurableSpace H] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {s : S}
    (c : ℂ) (φ : H → ℂ) (g : G) :
    Lift.liftInt ν 𝓕 th s (c • φ) g = c * Lift.liftInt ν 𝓕 th s φ g := by
  unfold Lift.liftInt
  rw [← integral_const_mul]
  congr 1
  funext h
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_left_comm (th g h s) c (φ h)

theorem liftInt_zero' {G H S : Type*} [MeasurableSpace H] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {s : S}
    (g : G) : Lift.liftInt ν 𝓕 th s (0 : H → ℂ) g = 0 := by
  simp [Lift.liftInt]

structure CtGood {V V' W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ))
    (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (κ : Measure (NI V C)) (𝓝 : Set (NI V C))
    (f : WO V W → ℂ) (f' : WO V' W → ℂ) (g : GA D V) (c : ℂ) (φ : GA D W → ℂ) : Prop where
  integ : ∀ g₁, IntegrableOn (fun h => thetaKO ω g₁ h f * φ h) 𝓕 ν
  integ' : IntegrableOn (fun h => thetaKO ω' 1 h f' * φ h) 𝓕 ν
  mean : IntegrableOn (fun n : NI V C => Lift.liftInt ν 𝓕 (thetaKO ω) f φ ((n : GA D V) * g)) 𝓝 κ
  eq : ∫ n in 𝓝, Lift.liftInt ν 𝓕 (thetaKO ω) f φ ((n : GA D V) * g) ∂κ =
    c * Lift.liftInt ν 𝓕 (thetaKO ω') f' φ 1

section CtGood

variable {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)}
  {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {κ : Measure (NI V C)} {𝓝 : Set (NI V C)}
  {f : WO V W → ℂ} {f' : WO V' W → ℂ} {g : GA D V} {c : ℂ}

theorem CtGood.zero : CtGood C ω ω' ν 𝓕 κ 𝓝 f f' g c 0 := by
  refine ⟨fun g₁ => ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp [liftInt_zero']
  · simp [liftInt_zero']

theorem CtGood.add {φ φ' : GA D W → ℂ} (h : CtGood C ω ω' ν 𝓕 κ 𝓝 f f' g c φ)
    (h' : CtGood C ω ω' ν 𝓕 κ 𝓝 f f' g c φ') : CtGood C ω ω' ν 𝓕 κ 𝓝 f f' g c (φ + φ') := by
  have e : (fun n : NI V C => Lift.liftInt ν 𝓕 (thetaKO ω) f (φ + φ') ((n : GA D V) * g)) =
      fun n : NI V C => Lift.liftInt ν 𝓕 (thetaKO ω) f φ ((n : GA D V) * g) +
        Lift.liftInt ν 𝓕 (thetaKO ω) f φ' ((n : GA D V) * g) :=
    funext fun n => liftInt_add' (h.integ _) (h'.integ _)
  refine ⟨fun g₁ => ?_, ?_, ?_, ?_⟩
  · refine ((h.integ g₁).add (h'.integ g₁)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp [mul_add]
  · refine (h.integ'.add h'.integ').congr (Filter.Eventually.of_forall fun x => ?_)
    simp [mul_add]
  · rw [e]; exact h.mean.add h'.mean
  · rw [e, integral_add h.mean h'.mean, h.eq, h'.eq, liftInt_add' h.integ' h'.integ', mul_add]

theorem CtGood.smul {φ : GA D W → ℂ} (a : ℂ) (h : CtGood C ω ω' ν 𝓕 κ 𝓝 f f' g c φ) :
    CtGood C ω ω' ν 𝓕 κ 𝓝 f f' g c (a • φ) := by
  have e : (fun n : NI V C => Lift.liftInt ν 𝓕 (thetaKO ω) f (a • φ) ((n : GA D V) * g)) =
      fun n : NI V C => a * Lift.liftInt ν 𝓕 (thetaKO ω) f φ ((n : GA D V) * g) :=
    funext fun n => liftInt_smul' a φ _
  refine ⟨fun g₁ => ?_, ?_, ?_, ?_⟩
  · refine ((h.integ g₁).const_mul a).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  · refine (h.integ'.const_mul a).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  · rw [e]; exact h.mean.const_mul a
  · rw [e, integral_const_mul, h.eq, liftInt_smul']; ring

end CtGood

theorem constTerm_eq_zero (hct : TowerConstTerm D) (hP : GlobalTheory.Published.CuspRapidDecay)
    {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B)
    {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {χS χT χT' : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)}
    (hω : IsWeilDatumO ψ V W χS χT ω) (hω' : IsWeilDatumO ψ V' W χS χT' ω')
    {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν)
    {S : D.what₂.Tau → SPar} (M : DSModel W S) (J : Set (GA D W)) (χ : GA D W → ℂ)
    (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M)
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (hlow : ∀ f', IsThetaFunO ψ V' W f' → Lift.liftInt ν 𝓕 (thetaKO ω') f' (F v) 1 = 0)
    (κ : Measure (NI V C)) (𝓝 : Set (NI V C)) (hκ : κ.IsHaarMeasure) (h𝓝 : IsFundamentalDomain (NIQ V C) 𝓝 κ)
    (g : GA D V) : ∫ n in 𝓝, Lift.liftInt ν 𝓕 (thetaKO ω) f (F v) ((n : GA D V) * g) ∂κ = 0 := by
  obtain ⟨μ, 𝓨, hc⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank r
  have form := hct V V' W r C B hs ψ χS χT χT' ω ω' hω hω' μ 𝓨 hc ν 𝓕 hν h𝓕 κ 𝓝 hκ h𝓝
  have h0 : GlobalTheory.Grow.RapidDec W (0 : GA D W → ℂ) :=
    ⟨fun _ _ _ => rfl, continuous_const, fun N => ⟨0, fun g => by simp⟩⟩
  have hc0 : IsCuspFun W (0 : GA D W → ℂ) := fun _ _ _ _ _ _ _ _ => by simp
  have ht := (form 0 h0 hc0 f hf g).2.2.1
  have good : CtGood C ω ω' ν 𝓕 κ 𝓝 f (res V V' W C B μ 𝓨 (ω (g, 1) f)) g (((κ 𝓝).toReal : ℝ) : ℂ) (F v) := by
    refine multT_ind θ M J χ _ CtGood.zero (fun _ _ h h' => h.add h') (fun a _ h => h.smul a) (fun φ ha hcu => ?_) F hF v
    obtain ⟨-, -, -, h1, h2, h3, h4⟩ := form φ (GlobalTheory.Size.rapidDecSm_of_cuspForm hP hθ ha hcu).rapidDec hcu f hf g
    exact ⟨h1, h2, h3, h4⟩
  rw [good.eq, hlow _ ht, mul_zero]

end GlobalTheory.PairLift.LowCusp

namespace GlobalTheory.PairLift

theorem cuspAll_of_lowAll : ∀ (D : D7) (X : ProvA), Inputs D X → LowAll D X → CuspAll D X := by
  intro D X hI hL S S' aS aT hR V W _M M' θ ψ hθ ω hω ν 𝓕 hν h𝓕 F hF v f hf r C hC κ 𝓝 hκ h𝓝 g
  obtain ⟨V', B, hs, hsig⟩ := GlobalTheory.T.exists_lowerWittTower_isotropicSplitEmbedding D V S _M r C hC
  obtain ⟨χS, χT, hW, hexp⟩ := hω
  obtain ⟨η, hη⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  have hpar : V.rank % 2 = V'.rank % 2 := by rw [hs.rank]; omega
  obtain ⟨ω', hω'⟩ := GlobalTheory.T.exists_weilDatum_of_splittingCharacters D ψ hW.std V' W χS χT ⟨η, hη.1, hη.2.2.2, hη.2.2.1, hη.2.1⟩ hW.hecS hW.hecT
    (resEta_parity hW.resS hpar) hW.resT
  refine LowCusp.constTerm_eq_zero hI.const hI.decay hs hθ hW hω' hν h𝓕 M' ∅ 1 F hF v hf
    (fun f' hf' => ?_) κ 𝓝 hκ h𝓝 g
  exact congrFun (hL S S' aS aT hR r V' W M' θ ψ hθ hC.1 hsig ω' ⟨χS, χT, hω', hexp⟩ ν 𝓕 hν h𝓕 F hF v f' hf') 1

end GlobalTheory.PairLift

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

namespace GlobalTheory.SmallDat.ThBox

theorem isThetaFunO_mul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T S₁ T₁ S₂ T₂ : HSp D} (p₁ : WO S T →+ WO S₁ T₁)
    (p₂ : WO S T →+ WO S₂ T₂) (c₁ : Continuous p₁) (c₂ : Continuous p₂)
    (hs : ∀ x y, symplO S T x y = symplO S₁ T₁ (p₁ x) (p₁ y) + symplO S₂ T₂ (p₂ x) (p₂ y))
    (r₁ : ∀ γ, ∃ γ', p₁ (ratW T S γ) = ratW T₁ S₁ γ') (r₂ : ∀ γ, ∃ γ', p₂ (ratW T S γ) = ratW T₂ S₂ γ')
    (hi : ∀ u, u.map (infPart D) = 0 → (p₁ u).map (infPart D) = 0 ∧ (p₂ u).map (infPart D) = 0)
    (hf : ∀ u, u.map (finPart D) = 0 → (p₁ u).map (finPart D) = 0 ∧ (p₂ u).map (finPart D) = 0)
    {f₁ : WO S₁ T₁ → ℂ} {f₂ : WO S₂ T₂ → ℂ} (h₁ : IsThetaFunO ψ S₁ T₁ f₁) (h₂ : IsThetaFunO ψ S₂ T₂ f₂) :
    IsThetaFunO ψ S T fun u => f₁ (p₁ u) * f₂ (p₂ u) := by
  have hH : ∀ x y, symplOH S T x y = symplOH S₁ T₁ (p₁ x) (p₁ y) + symplOH S₂ T₂ (p₂ x) (p₂ y) := fun x y => by
    unfold symplOH
    rw [hs, mul_add]
  refine ⟨fun γ w => ?_, ?_, (h₁.cont.comp c₁).mul (h₂.cont.comp c₂), fun k L hL hL0 w => ?_⟩
  · obtain ⟨γ₁, e₁⟩ := r₁ γ
    obtain ⟨γ₂, e₂⟩ := r₂ γ
    rw [map_add (f := _), map_add (f := _), hH, e₁, e₂, h₁.quasi, h₂.quasi, neg_add, AddChar.map_add_eq_mul]
    ring
  · obtain ⟨U₁, o₁, hU₁⟩ := h₁.level
    obtain ⟨U₂, o₂, hU₂⟩ := h₂.level
    refine ⟨U₁.comap p₁ ⊓ U₂.comap p₂, (o₁.preimage c₁).inter (o₂.preimage c₂), fun u hu h0 => funext fun w => ?_⟩
    have a₁ := congrFun (hU₁ (p₁ u) hu.1 (hi u h0).1) (p₁ w)
    have a₂ := congrFun (hU₂ (p₂ u) hu.2 (hi u h0).2) (p₂ w)
    unfold heisO at a₁ a₂ ⊢
    beta_reduce
    rw [← a₁, ← a₂, hH, map_add (f := p₁), map_add (f := p₂), AddChar.map_add_eq_mul]
    ring
  · simp only [map_add (f := _)]
    exact (h₁.smooth k (p₁.comp L) (c₁.comp hL) (fun t => (hf _ (hL0 t)).1) (p₁ w)).mul
      (h₂.smooth k (p₂.comp L) (c₂.comp hL) (fun t => (hf _ (hL0 t)).2) (p₂ w))

theorem mulG_map_zero {D : D7} {R : Type} [CommRing R] (φ : AE D →+* R) (S : HSp D) {n : ℕ}
    (x : Matrix (Fin n) (Fin S.rank) (AE D)) (h : x.map φ = 0) : (mulG S x).map φ = 0 := by
  rw [GlobalTheory.BigDat.mulG_eq, Matrix.map_mul, h, Matrix.zero_mul]

theorem continuous_mulG {D : D7} (S : HSp D) {n : ℕ} : Continuous (mulG S (n := n)) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  exact continuous_id.matrix_mul continuous_const

theorem mulG_rat {D : D7} (S : HSp D) {n : ℕ} (x : Matrix (Fin n) (Fin S.rank) D.host.E) :
    mulG S (x.map (incA D)) = (x * S.gram).map (incA D) := by
  rw [GlobalTheory.BigDat.mulG_eq, Matrix.map_mul]

theorem infPart_cA {D : D7} (x : AE D) :
    infPart D (cA D x) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem finPart_cA {D : D7} (x : AE D) :
    finPart D (cA D x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem maps_map_zero {R : Type} [CommRing R] (φ : AE D →+* R) (hφ : ∀ x, φ x = 0 → φ (cA D x) = 0) (t : T)
    (e : Num G i j) (u : PtS G i j) (h : u.map φ = 0) : (mapA t e u).map φ = 0 ∧ (mapB e u).map φ = 0 := by
  have h0 : ∀ a b, φ (u a b) = 0 := fun a b => congrFun (congrFun h a) b
  refine ⟨mulG_map_zero φ _ _ (Matrix.ext fun a b => h0 _ _), ?_⟩
  have h2 := mulG_map_zero φ (spV₁ G i j) ((u.submatrix id fun k => e (.inr k)).map (cA D))
    (Matrix.ext fun a b => hφ _ (h0 _ _))
  exact Matrix.ext fun a b => (map_neg φ _).trans (neg_eq_zero.2 (congrFun (congrFun h2 a) b))

theorem continuous_mapA (t : T) (e : Num G i j) : Continuous (mapA t e) :=
  (continuous_mulG (spW₁ G i j)).comp (continuous_id.matrix_submatrix id fun k => e (.inl k)).matrix_transpose

theorem continuous_mapB (e : Num G i j) : Continuous (mapB e) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  exact ((continuous_mulG (spV₁ G i j)).comp ((continuous_id.matrix_submatrix id fun k => e (.inr k)).matrix_map
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D))).neg

theorem mapA_rat (t : T) (e : Num G i j)
    (γ : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) D.host.E) :
    ∃ γ', mapA t e (γ.map (incA D)) = ratW (G.pT (.mu t i j)) (G.pS (.mu t i j)) γ' :=
  ⟨_, mulG_rat (spW₁ G i j) (γ.submatrix id fun k => e (.inl k))ᵀ⟩

theorem mapB_rat (e : Num G i j)
    (γ : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) D.host.E) :
    ∃ γ', mapB e (γ.map (incA D)) = ratW (G.pT (.chi i j)) (G.pS (.chi i j)) γ' :=
  ⟨-_, (congrArg Neg.neg (mulG_rat (spV₁ G i j) ((γ.submatrix id fun k => e (.inr k)).map star))).trans
    (Matrix.map_neg _ (map_neg (incA D)) _).symm⟩

theorem thetaS_box : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (t : T) (i j : ℕ) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X → IsTriple Bs Γ X om om' →
    (∀ Φ ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), ∀ Φ' ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), GlobalTheory.SmallDat.thetaS Γ W.ψ (Φ + Φ') = GlobalTheory.SmallDat.thetaS Γ W.ψ Φ + GlobalTheory.SmallDat.thetaS Γ W.ψ Φ') ∧
    (∀ Φ ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), ∀ Φ' ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), GlobalTheory.SmallDat.thetaS Γ W.ψ Φ = GlobalTheory.SmallDat.thetaS Γ W.ψ Φ' → Φ = Φ') ∧
    ∀ (f₁ : GlobalTheory.SmallDat.HomA G t i j → ℂ) (f₂ : GlobalTheory.SmallDat.HomB G i j → ℂ), IsThetaFunO W.ψ _ _ f₁ → IsThetaFunO W.ψ _ _ f₂ →
      ∃ Φ ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), GlobalTheory.SmallDat.thetaS Γ W.ψ Φ = GlobalTheory.SmallDat.boxS t e f₁ f₂ := by
  intro D T L sc G W M t i j e Bs Γ X om om' h hT
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.hermitianSelfDualLatticeSpace_form_hermitian_nondeg_unimodular D Bs hT.base _ Γ.V' _ _ hT.geo.hV'
  obtain ⟨hJ, L', hL, h4, h5, h6⟩ := GlobalTheory.T.skewHermitian_neg_traceZero_inv_hermitian_unimodular D Bs hT.base _ Γ.W _ _ hT.geo.hW
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  let T₀ := GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hT.geo.hV'.lat.toIsLattice h3 (fun _ => (0, 0))
  let S₀ := GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 L' hL h6 (fun _ => (0, 0))
  have eA : Γ.V'.J = T₀.gramᵀ := by rw [GlobalTheory.WeilSchrodinger.gram_hspOf]; rfl
  have eB : (-1 : AE D) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S₀.gram⁻¹) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    have e1 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
    have e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Γ.W.J = -Γ.W.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
    show (-1 : AE D) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (-D.host.xi0 • Γ.W.J⁻¹)⁻¹)
    rw [e1, e2]
    funext a b
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  have hψ : IsStdChar D W.ψ (-1) := h.ψ ▸ GlobalTheory.T.isStdChar_neg_one_of_standardTraceAdelicAddChar D Bs.ψ hT.base.std
  obtain ⟨ha, hi, hs⟩ := GlobalTheory.ThetaTransform.thetaTr_bij (S := S₀) (T := T₀) Γ.M'.co hψ eA eB hT.geo.hM'.rat
  refine ⟨ha, hi, fun f₁ f₂ hf₁ hf₂ => (hs _).1 ?_⟩
  exact isThetaFunO_mul (S := S₀) (T := T₀) (AddMonoidHom.mk' (mapA t e) (mapA_add t e))
    (AddMonoidHom.mk' (mapB e) (mapB_add e)) (continuous_mapA t e) (continuous_mapB e)
    (fun x y => (GlobalTheory.ThetaTransform.symplO_eq_symp eA eB x y).trans (sympS_eq t e Γ h.JW₁ h.JWW x y))
    (mapA_rat t e) (mapB_rat e)
    (maps_map_zero (infPart D) (fun x hx => by rw [infPart_cA, hx, map_zero]) t e)
    (maps_map_zero (finPart D) (fun x hx => by rw [finPart_cA, hx, map_zero]) t e) hf₁ hf₂

end GlobalTheory.SmallDat.ThBox

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weilAction_schrodingerModel_finiteIdempotent : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → infPart D a = 0 → ∀ g h, (∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → ∀ (f₀ Φ f : WO S T → ℂ) (c d : ℂ), IsThetaFunO ψ S T f₀ → IsThetaAt ψ (symplO S T) (heisO ψ S T) a (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Φ f → c ≠ 0 → om (g, h) f₀ = c • f₀ → (∀ x, Φ (actO S T g h x) = d * Φ x) → d • om (g, h) f = c • f := by
  first | exact @GlobalTheory.SchrMove.smul_om_eq | exact GlobalTheory.SchrMove.smul_om_eq | (intros; apply GlobalTheory.SchrMove.smul_om_eq <;> assumption)
end
