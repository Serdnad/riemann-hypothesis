module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle472
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle196
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle241
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle484
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle186
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorsBijectiveAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle471
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle226
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle180
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle168
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle338
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle385
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle486
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle468
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle500
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle480
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle479
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle481
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LiftsAtLevel

variable {D : D7}

theorem combAt_mono {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) {S T : HSp D} {c : WO S T →₀ ℂ} (hc : CombAt P c) :
    CombAt P' c :=
  fun u hu a b => AllBij.idAt_mono h (hc u hu a b)

theorem comb_pureTensorO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} (hstd : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {c : WO S T →₀ ℂ} (hc : IsFinComb c) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (comb ψ S T c f) φ = comb ψ S T c (pureTensorO ψ θ S T sS sT BS BT f φ) := by
  classical
  have e : ∀ g : WO S T → ℂ, comb ψ S T c g =
      ∑ i, c (c.support.equivFin.symm i) • heisO ψ S T (c.support.equivFin.symm i) g := by
    intro g
    unfold comb
    rw [← Finset.sum_coe_sort c.support]
    exact Fintype.sum_equiv c.support.equivFin _ _ (fun x => by simp)
  have key := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D ψ θ S T hstd hθ sS sT BS BT f hf c.support.card
    (fun i => c (c.support.equivFin.symm i)) (fun i => (c.support.equivFin.symm i : WO S T))
    (fun i => hc _ (c.support.equivFin.symm i).2) φ).1
  rw [e, e, key]

theorem vac_pureTensorO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {x : DefSp S} {y : DefSp T}
    {f₀ : WO S T → ℂ} (hvac : IsVacO ψ θ S T x.s y.s x.L y.L f₀) (P : Pl D → Prop)
    (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    Vac ψ S T x.L y.L P (pureTensorO ψ θ S T x.s y.s x.B y.B f₀ φ) := by
  have hth : ∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T x.s y.s x.B y.B f₀ φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hvac.1 hvac.2.inf x.s x.B y.s y.B hvac.2.theta φ
  have hle : latO S T (x.L : Set _) (y.L : Set _) P ≤ latO S T (x.L : Set _) (y.L : Set _) fun _ => True :=
    GlobalTheory.PlaceTensor.latO_mono fun _ _ => trivial
  refine ⟨hth φ, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have hu' := hle hu
    exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hvac.2.inf x.s y.s x.B y.B f₀ hth (2 • u)
      (GlobalTheory.VacGood.infPart_latO (AddSubgroup.nsmul_mem _ hu' 2)) (hvac.2.lat.1 u hu') φ
  · have hu' := hle hu
    exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hvac.2.inf x.s y.s x.B y.B f₀ hth u
      (GlobalTheory.VacGood.infPart_latO hu') (hvac.2.lat.2 e he u hu' hh) φ

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sOp_ram {ι : Type} {p : ι → SplitPt D k} (hinj : Function.Injective fun i => (p i).v) {S : HSp D} {n : Type}
    [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k) (χ₀ : ι → AddChar k Circle)
    (hχ : ∀ i, HasConductor (χ₀ i) 1) (ε : 𝓀[k]ˣ) (i : ι) {φ : GA D S → ℂ}
    (hφ : IsContAut S φ ∧ ∀ i', RamAt (β i') (Q i') φ) :
    IsContAut S (sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) ε φ) ∧
      ∀ i', RamAt (β i') (Q i') (sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) ε φ) := by
  obtain ⟨hbij, -, c, c', hc, -⟩ := GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination D k (p i) n q (χ₀ i) (hχ i) _ rfl ε S (β i) (Q i)
  have hT : ∀ φ, sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) ε φ = AllBij.act (Finsupp.mapDomain (β i).gl c) φ :=
    fun φ => (hc φ).trans (AllBij.sum_rep_eq _ _ _)
  have hC := AllBij.mapDomain_mem _ (AllBij.gl_mem (β i)) c
  refine ⟨by rw [hT]; exact AllBij.isContAut_act _ hφ.1, fun i' => ?_⟩
  rcases eq_or_ne i' i with rfl | hne
  · exact hbij.mapsTo (hφ.2 i')
  · rw [hT]
    exact AllBij.ramAt_act _ _ _ (fun x hx g => AllBij.grpAt_comm S (fun e => hne (hinj e)) (hC x hx)
      (AllBij.gl_mem _ g)) (hφ.2 i')

theorem foldr_ram {ι : Type} {p : ι → SplitPt D k} (hinj : Function.Injective fun i => (p i).v) {S : HSp D} {n : Type}
    [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k) (χ₀ : ι → AddChar k Circle)
    (hχ : ∀ i, HasConductor (χ₀ i) 1) (ε : ι → 𝓀[k]ˣ) (l : List ι) {φ : GA D S → ℂ}
    (hφ : IsContAut S φ ∧ ∀ i', RamAt (β i') (Q i') φ) :
    IsContAut S (l.foldr (fun i φ' => sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) (ε i) φ') φ) ∧
      ∀ i', RamAt (β i') (Q i') (l.foldr (fun i φ' => sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) (ε i) φ') φ) := by
  induction l with
  | nil => exact hφ
  | cons i l ih => exact sOp_ram hinj β Q q χ₀ hχ (ε i) i ih

theorem isIdele_idele (p : SplitPt D k) (x : kˣ) : p.IsIdele x (p.idele x) := by
  unfold SplitPt.IsIdele
  rw [SplitPt.idele_val]
  ring

end Local

theorem chrPow_mul_neg (μ : (AE D)ˣ →* Circle) (a : (AE D)ˣ) (e : ℤ) : chrPow μ a e * chrPow μ a (-e) = 1 := by
  simp only [chrPow, ← Circle.coe_mul, _root_.zpow_neg, mul_inv_cancel, Circle.coe_one]

end GlobalTheory.SeeSaw.LiftsAtLevel

namespace GlobalTheory.SeeSaw.LiftsAtLevel


open GlobalTheory.FinPl.ValDbl in
theorem pt_over {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} {v : VCom c} {o : TDat c k ι} {t : Tup c} {w : VTup t} (hc : c.Is) (ht : t.Is) (hv : v.Is) (hVF : VForm v w)
    (hSh : ShapeOff v o) (j : ℕ) (hj : j < D.R.m) (α : t.Ch j) (γ : t.Ch (j + 1))
    (P : PolF D (c.X (j + 1)).rank (c.X j).rank) (i : ι) :
    ∃ f₀, Over c.ψ (o.β j i) (o.β (j + 1) i) (c.x j).L (c.x (j + 1)).L f₀ (phiOne (o.Q j i) (o.Q (j + 1) i))
      ((t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P) := by
  have hk := ht.ker j hj α γ
  have hvac : IsVacO c.ψ c.θ (c.X j) (c.X (j + 1)) (c.x j).s (c.x (j + 1)).s (c.x j).L (c.x (j + 1)).L (c.vac j) := hk.vac
  have hstd := hc.std
  have hxS := hc.x j hj.le
  have hxT := hc.x (j + 1) hj
  set f := pureTensorO c.ψ c.θ (c.X j) (c.X (j + 1)) (c.x j).s (c.x (j + 1)).s (c.x j).B (c.x (j + 1)).B (c.vac j) P
    with hfdef
  have hfV : ∀ Pp, Vac c.ψ _ _ (c.x j).L (c.x (j + 1)).L Pp f := fun Pp => vac_pureTensorO hvac Pp P
  have hpt : (t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P =
      comb c.ψ _ _ (w.dQ j α γ) (comb c.ψ _ _ (v.dG j) (comb c.ψ _ _ (v.dT j) f)) := by
    show pureTensorO c.ψ c.θ (c.X j) (c.X (j + 1)) (c.x j).s (c.x (j + 1)).s (c.x j).B (c.x (j + 1)).B
      (comb c.ψ _ _ (t.dd j α γ) (c.vac j)) P = _
    rw [comb_pureTensorO hstd hc.inf _ _ _ _ hvac.2.theta (c := t.dd j α γ) hk.fin P]
    exact hVF.dd j hj α γ f (hfV fun _ => True).1
  have hrep := hSh.rep j hj f (hfV _)
  have hpl : Places o.p o.I (· ∈ v.tP) :=
    ⟨hSh.pre.nodup, hSh.pre.all, hSh.pre.inj, hSh.pre.tP, fun i => (hSh.pre.char i).2⟩
  have hAC := (GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D k ι o.p o.I (· ∈ v.tP) hpl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) c.ψ hstd
    (c.X j) (c.X (j + 1)) (o.β j) (o.β (j + 1)) (c.x j).L (c.x (j + 1)).L hxS.sd hxT.sd
    (fun i => phiOne (o.Q j i) (o.Q (j + 1) i))).2.2
  have hdG : CombAt (fun x => ¬ x ∈ v.tP) (v.dG j) :=
    combAt_mono (fun x hx ht' => Finset.disjoint_left.1 hv.disj hx ht') (hv.atG j).2.1
  have hdQ : CombAt (fun x => ¬ x ∈ v.tP) (w.dQ j α γ) :=
    combAt_mono (fun x hx ht' => Finset.disjoint_left.1 hVF.disjT hx ht') ((hVF.atQ j).2.2 α γ)
  obtain ⟨hV1, hO1⟩ := hAC (v.dG j) hdG f (hfV _)
  obtain ⟨hV2, hO2⟩ := hAC (w.dQ j α γ) hdQ _ hV1
  have hO := hO2 _ (hO1 _ hrep)
  obtain ⟨g, hg, -⟩ := overAll_last hstd (fun i => (hSh.pre.char i).2) hSh.pre.inj o.I hSh.pre.nodup _ _
    (fun j' => vac_at ((hSh.pre.tP _).2 ⟨j', rfl⟩) hV2) hO i (hSh.pre.all i)
  exact ⟨g, hpt ▸ hg⟩

end GlobalTheory.SeeSaw.LiftsAtLevel


open GlobalTheory.SeeSaw.LiftsAtLevel in
theorem GlobalTheory.SeeSaw.liftS_of_exact : ∀ (D : D7) (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom c) (o : TDat c k ι) (t : Tup c) (w : VTup t), LiftExact D → c.Is → t.Is → v.Is → VForm v w → ShapeOff v o → (∀ j, j < D.R.m → ∃ μ, IsWeilDatumO c.ψ _ _ μ μ (t.kom j) ∧ ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D μ (o.p i).v) → LiftS o t := by
  intro D c k _ _ _ _ ι v o t w hLE hc ht hv hVF hSh hμ j hj α γ P φ hφ
  obtain ⟨μ, hW, hU⟩ := hμ j hj
  have hxS := hc.x j hj.le
  have hxT := hc.x (j + 1) hj
  have hk := ht.ker j hj α γ
  have hφ' : IsContAut (c.X j) φ ∧ ∀ i, RamAt (o.β j i) (o.Q j i) φ := hφ
  set F := (t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P with hF
  have hOv := pt_over hc ht hv hVF hSh j hj α γ P
  have hlift : ∀ φ', (t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) P φ' =
      liftT (t.kom j) (c.x j).vol.μ (c.x j).vol.𝓕 φ' F := fun φ' => rfl

  have hram : ∀ φ', (IsContAut (c.X j) φ' ∧ ∀ i, RamAt (o.β j i) (o.Q j i) φ') →
      liftT (t.kom j) (c.x j).vol.μ (c.x j).vol.𝓕 φ' F ∈ o.Ram (j + 1) := by
    intro φ' h'
    refine ⟨?_, fun i => ?_⟩
    · rw [← hlift]
      exact (GlobalTheory.SeeSaw.LiftSumProof.liftSum D c.ψ c.θ hc.inf _ _ (c.x j) (c.x (j + 1)) hxS hxT _ hk P).2.1 φ' h'.1
    · obtain ⟨f₀, hf₀⟩ := hOv i
      obtain ⟨c₀, -, H⟩ := GlobalTheory.T.ramifiedThetaLift_commutes_splitPlace_operators D k (o.p i) (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) o.q (o.χ i) (o.hχ i) c.ψ
        (c.X j) (c.X (j + 1)) hxS.cpt (c.x j).vol μ μ (t.kom j) hW (hU i) (hU i) (o.β j i) (o.β (j + 1) i) (o.Q j i)
        (o.Q (j + 1) i)
      exact (H _ _ f₀ F hf₀ φ' (h'.2 i)).1
  refine ⟨by rw [hlift]; exact hram φ hφ', fun η => ?_⟩

  have key : ∀ l : List ι, l.foldr (fun i φ' => sOp (o.β (j + 1) i) (o.Q (j + 1) i) o.q (resChar (o.χ i) (o.hχ i) o.q) (η i) φ')
        (liftT (t.kom j) (c.x j).vol.μ (c.x j).vol.𝓕 φ F) =
      ((((resCard k : ℝ) ^ ((((c.X (j + 1)).rank : ℝ) - (c.X j).rank) / 2) : ℝ) : ℂ) ^ l.length) •
        liftT (t.kom j) (c.x j).vol.μ (c.x j).vol.𝓕
          (l.foldr (fun i φ' => sOp (o.β j i) (o.Q j i) o.q (resChar (o.χ i) (o.hχ i) o.q) (η i) φ') φ) F := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.foldr_cons, List.length_cons]
      rw [ih, GlobalTheory.FinPl.ValDbl.sOp_smul]
      obtain ⟨e, -, hE⟩ := hLE k (o.p i) o.q (o.χ i) (o.hχ i)
      obtain ⟨f₀, hf₀⟩ := hOv i
      have hr := (foldr_ram hSh.pre.inj (o.β j) (o.Q j) o.q o.χ o.hχ η l hφ').2 i
      rw [hE (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) c.ψ (c.X j) (c.X (j + 1)) hxS.cpt (c.x j).vol μ μ (t.kom j) hW
        (hU i) (hU i) (o.β j i) (o.β (j + 1) i) (o.Q j i) (o.Q (j + 1) i) _ (isIdele_idele (o.p i) o.q.unit) _ _ f₀ F hf₀ _ hr
        (η i), mul_assoc, chrPow_mul_neg, mul_one, smul_smul, pow_succ]
      simp only [Fintype.card_fin]
  simp only [TDat.S, TDat.cL, hlift]
  exact key o.I
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.mem_chainLevel_iff_carriesLattice_offLevel : ∀ (D : D7) (c : GlobalTheory.ChainOnto.Com D) (j : ℕ) (s : GlobalTheory.ChainOnto.PiLocalization₂ D), s.Is c j → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ c.S → ∀ κ ∈ grpAt s.V (· = v), κ ∈ levS s.V s.β s.L ↔ Moves s.V κ s.Λ s.Λ (· = v) := by
  first | exact @GlobalTheory.Core.Mi.LevChain.mem_levS_iff_moves | exact GlobalTheory.Core.Mi.LevChain.mem_levS_iff_moves | (intros; apply GlobalTheory.Core.Mi.LevChain.mem_levS_iff_moves <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfProd

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.AdForm GlobalTheory.ExportSeries

variable {D : D7}

private theorem selfDual_isFullLattice {D : D7} : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
  intro V Λ hΛ
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hΛ.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
    ∑ i, ∑ j, star (x i) * V.gram i j * y j
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
  have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
    carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : D.host.E) + c = _
      rw [hb, hc]
      simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : D.host.E) * _ = _
      ring }
  have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
    apply (hΛ.2 _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    obtain ⟨b, hb⟩ := hxP
    refine ⟨b, ?_⟩
    rw [hb]
    dsimp only [f, Pi.smul_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    Submodule.subset_span hy
  have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
    (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
  change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
    ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this





theorem stepVec_of_prod : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ S.rank) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f₀ : WO S T → ℂ) (dG dQ : WO S T →₀ ℂ), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → Disjoint Pg Q → (∀ PP ∈ Pg, ∀ PP' ∈ Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')) → (∃ e : AE D, IsIdemSum e (Pg ∪ Q)) → GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) dG → GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ Q, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) dQ → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B) χj ∅ (fun _ => 1) f₀ (comb ψ S T dG f₀) → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B) χj Q ξ f₀ (comb ψ S T dQ f₀) → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (datY S.rank r t j hr Pg Q P χ ξ Frm.B) χj Q ξ f₀ (comb ψ S T dQ (comb ψ S T dG f₀)) := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT r t j hr Pg Q P χ χj ξ f₀ dG dQ hS hT _ _ hdisj hunder hex hdG hdQ hG hQv
  obtain ⟨hvac, eG, heG, hthG⟩ := hG
  obtain ⟨-, eQ, heQ, hthQ⟩ := hQv
  obtain ⟨e, he⟩ := hex
  change IsIdemSum eG (Pg ∪ ∅) at heG
  change IsIdemSum eQ (∅ ∪ Q) at heQ
  rw [Finset.union_empty] at heG
  rw [Finset.empty_union] at heQ
  have heq : e = eG + eQ := by
    obtain ⟨⟨es, hes, hsum⟩, -⟩ := heQ
    have := GlobalTheory.IdemSumAdd.idemSum_union D eG e Pg Q es hdisj hes heG he
    rw [this, hsum]
  subst heq
  refine ⟨hvac, eG + eQ, he, ?_⟩
  have hGG := idemSum_mul_self heG
  have hQQ := idemSum_mul_self heQ
  have hee := idemSum_mul_self he
  have hGQ : eG * eQ = 0 := by
    have h2 : (2 : AE D) * (eG * eQ) = 0 := by
      have h := hee
      rw [add_mul, mul_add, mul_add, hGG, hQQ, mul_comm eQ eG] at h
      linear_combination h
    have h2' : (2 : AE D) = algebraMap D.host.F (AE D) 2 := (map_ofNat _ 2).symm
    calc eG * eQ = algebraMap D.host.F (AE D) (1 / 2) * ((2 : AE D) * (eG * eQ)) := by
          rw [← mul_assoc, h2', ← map_mul, show (1 / 2 : D.host.F) * 2 = 1 by norm_num, map_one, one_mul]
      _ = 0 := by rw [h2, mul_zero]
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
      a • u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := fun a ha u hu =>
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu
  obtain ⟨K, hK, hC⟩ := exists_nsmul_of_frMapO (selfDual_isFullLattice S ΛS hS) (selfDual_isFullLattice T ΛT hT) βS βT
  have hsbG := isSBHalf_of_red eG _ (frMapO S T βS βT) (frMapO_add βS βT) (exists_den_frMapO hS.1.fg hT.1.fg βS βT)
    ⟨K, hK, fun t ht => hC t (infPart_of_half (infPart_idemSum heG) ht)⟩ Pg
    (fun y => omegaG (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B) χj y *
      omegaQ ∅ (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B).r (fun _ => 1) 1 y) fun y y' h => by
      rw [omegaG_congr _ χj y y' h, omegaQ_congr ∅ _ _ 1 y y' fun PP hP => absurd hP (Finset.notMem_empty PP)]
  have hsbQ := isSBHalf_of_red eQ _ (frMapO S T βS βT) (frMapO_add βS βT) (exists_den_frMapO hS.1.fg hT.1.fg βS βT)
    ⟨K, hK, fun t ht => hC t (infPart_of_half (infPart_idemSum heQ) ht)⟩ Q
    (fun y => omegaG (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B) χj y *
      omegaQ Q (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B).r ξ 1 y) fun y y' h => by
      rw [omegaG_congr _ χj y y' fun PP hP => absurd hP (Finset.notMem_empty PP), omegaQ_congr Q _ _ 1 y y' h]
  refine ⟨(GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hvac.1 S T ΛS ΛT hS hT (Pg ∪ Q) (eG + eQ) he f₀
    hvac.2.theta hvac.2.lat).1, fun Tm hTm => ?_⟩
  have hTG := isPlaceModel_comp_restrictHalf hGG hQQ hGQ hΛ hTm
  have hTm' := hTm
  rw [add_comm eG eQ] at hTm'
  have hTQ := isPlaceModel_comp_restrictHalf hQQ hGG (by rw [mul_comm, hGQ]) hΛ hTm'
  have hvG := hthG.2 _ hTG
  have hvQ := hthQ.2 _ hTQ
  have hL1 := isPlaceModel_prodHalf hGG hQQ hGQ hΛ hsbQ hTm
  have hbase : ∀ Ψ : WO S T → ℂ, prodHalf eG eQ Ψ (halfInd eG (latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) = restrictHalf eQ eG (latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Ψ := fun Ψ => by
    funext x
    simp only [prodHalf_apply, restrictHalf_apply, add_comm eG eQ]
    ring
  rw [hbase, ← LinearMap.comp_apply, ← hvQ] at hL1
  have hd : ∀ PP ∈ Pg, ¬ (fun p => ∃ PP ∈ Q, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) :=
    fun PP hP ⟨PP', hP', h⟩ => hunder PP hP PP' hP' h
  have hL2 := GlobalTheory.T.supportedTranslatesCombination_commutes_schrodinger D ψ hvac.1 S T _ eG Pg _ heG hd dQ hdQ f₀ _ (combL ψ S T dQ ∘ₗ
    (Tm ∘ₗ restrictHalf eG eQ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)))
    hTG fun Φ => by rw [LinearMap.comp_apply, combL_apply]
  have hu := placeModel_eq hvac.1 hS hT hGG (infPart_idemSum heG) hL1 hL2 hsbG
  rw [LinearMap.comp_apply, LinearMap.comp_apply, combL_apply, ← hvG] at hu
  rw [← hu]
  beta_reduce
  congr 1
  funext x
  exact (GlobalTheory.T.stepDatum_eq_mul_halves D S T βS βT r t j hr Pg Q P χ χj ξ eG eQ heG heQ hGQ x).symm

end GlobalTheory.HalfProd

end
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.siegelHeightFinitePlace_doublingEmbedding_le_one : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (v : FinPl D) (y : Gv A v), hgtFin D.sp.cm.sig (dblSp A).gram L v (ioAt A v y) ≤ 1 := by
  first | exact @GlobalTheory.Core.Rk.IP.hgtFin_ioAt_le_one | exact GlobalTheory.Core.Rk.IP.hgtFin_ioAt_le_one | (intros; apply GlobalTheory.Core.Rk.IP.hgtFin_ioAt_le_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.ChainTw.linModel_theta : ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι ι', IsChart s k φ ι → IsChart s' (k + 1) φ ι' → ∀ μS μT ξl : (Fv D.host.F v)ˣ →* ℂˣ, (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μS y = Circle.toUnits (c.chS (k + 1) x)) → (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μT y = Circle.toUnits (c.chT (k + 1) x)) → LiftsChar φ PP ξl (w.ξ PP) → ∀ P, ∃ (W : Submodule ℂ (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → ℂ)) (hW : ∀ g h, ∀ u ∈ W, GlobalTheory.ParHecke.omTwo μS μT g h u ∈ W) (hΦ : datum ξl⁻¹ ∈ W) (T : W →ₗ[ℂ] (WO s.V s'.V → ℂ)), T ⟨_, hΦ⟩ = p.pt P ∧ (∀ u, IsThetaFunO c.ψ s.V s'.V (T u)) ∧ ∀ g h (u : W), p.ω (ι g, ι' h) (T u) = T ⟨_, hW g h u u.2⟩ := by
  intro D hG c w hw k hk s s' hs hs' p hp PP hPP v φ hφ ι ι' hι hι' μS μT ξl hS hT hξ P
  obtain ⟨m, X, hX⟩ := GlobalTheory.Size.exists_isCovolOne s.V s'.V
  obtain ⟨hW, hΦ, T, h1, h2, h3, h4⟩ :=
    GlobalTheory.T.linearModel_splitPlace_twist_schwartzBruhat D hG c w hw k hk s s' hs hs' p hp PP hPP v φ hφ ι ι' hι hι' μS μT ξl hS hT hξ P m X hX
  exact ⟨_, hW, hΦ, T, h1, h2, h3⟩
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.twistedChain_coefficient_supported_principal_level : ∀ D : D7, ForStepQ D fun c w _ s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ P (g : GA D s.V), coefW p.ω m X (p.pt P) g ≠ 0 → ∀ v ∈ w.S₀, gAt s.V (.inl v) g ∈ Lev.levG s.V s.β s.L := by
  first | exact @GlobalTheory.TwSuppLev.supp_at_principal | exact GlobalTheory.TwSuppLev.supp_at_principal | (intros; apply GlobalTheory.TwSuppLev.supp_at_principal <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer

theorem _root_.GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop), (∀ v, P v → Tame D v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT v) → ∀ f, Vac ψ S T LS LT P f → ∀ κ κ', InK S LS P κ → InK T LT P κ' → om (κ, κ') f = f := by
  first | exact @GlobalTheory.StabSetFix.stab_fix_vac | exact GlobalTheory.StabSetFix.stab_fix_vac | (intros; apply GlobalTheory.StabSetFix.stab_fix_vac <;> assumption)
end
