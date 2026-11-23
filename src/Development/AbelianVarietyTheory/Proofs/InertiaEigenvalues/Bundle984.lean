module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle030
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2598
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramePinSmul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle649
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle248
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle983
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle033
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle068
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.Unframe

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Lev ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HeckeSup GlobalTheory.RealGeo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev moveForms {LL Ks WL G : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] {W : (LL →+* ℂ) → Type}
    [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] [Group G]
    (B : Arith.FormsL LL Ks WL W G) (w : (LL →+* ℂ) → G) : Arith.FormsL LL Ks WL W G :=
  { B with j := fun σ => (B.j σ).comp (B.ρ (w σ)) }

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

abbrev moveR {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → G) : RealDat D A Ks :=
  updFW R R.nW fun i => moveForms (R.FW i) (w i)

variable {T : CoreJ D} [iA : Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}


open Classical in
variable (T) in
def overEmb (w : Fin D.R.m → (T.Q.c.F →+* ℂ) → G) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : G :=
  if GoodEmb T.Q.c (res T σ) then w i (res T σ) else w i (resC T σ)

section Half

variable (B : GeoHalf T R fun _ => 1) (c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ)
  (w : Fin D.R.m → (T.Q.c.F →+* ℂ) → G)

def Moves : Prop :=
  ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
    ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (B.κ i)) (B.κ i).n,
      phiC (setCE T c') hV (wtA (B.κ i)) f = phiC T hV (wtA (B.κ i)) (actLev T.Q.c (B.O i).lev2 (w i σ) f)

variable {B c' w}

theorem rho_e (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (i : Fin D.R.m) (g : G) (f : Cu T B.κ i) :
    (R.FW i).ρ g ((B.fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) =
      (B.fw.e i ⟨actLev T.Q.c (B.O i).lev2 g f, hK i g f f.2⟩ : (R.FW i).WK) :=
  (((B.rhoGeo i).1 (hK i) g f).choose_spec).symm


theorem ev_move (hJ : JEvExists T R B.κ B.v₀) (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (hM : Moves B c' w) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hσ : GoodEmb T.Q.c (res T σ)) (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (f : Cu T B.κ i) :
    (R.HW i σ).e ((R.FW i).j σ ((R.FW i).ρ (overEmb T w i σ) ((B.fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)))
      (B.v₀ i σ) = phiC (setCE T c') hV (wtA (B.κ i)) (f : T.R ((i : ℕ) + 1)) := by
  rw [overEmb, if_pos hσ, rho_e hK, hM i _ hσ hV f f.2]
  exact B.fw.evaluates hJ i σ hσ hV ⟨_, hK i _ f f.2⟩


theorem bar_move (hJ : JEvBar T R B.κ) (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (hM : Moves B c' w) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hσ : ¬ GoodEmb T.Q.c (res T σ)) (hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i) :
    ∃ v : (R.MW i σ).Vec, IsUnitV v ∧ ∀ f : Cu T B.κ i,
      (R.HW i σ).e ((R.FW i).j σ ((R.FW i).ρ (overEmb T w i σ) ((B.fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL))) v =
        fun g => starRingEnd ℂ (phiC (setCE T c') hV (wtA (B.κ i)) (f : T.R ((i : ℕ) + 1)) g) := by
  obtain ⟨v, hv, h⟩ := (B.bar i σ hσ hV).1 (hJ i σ hσ hV)
  refine ⟨v, hv, fun f => ?_⟩
  rw [overEmb, if_neg hσ, rho_e hK, hM i _ (good_resC T hσ) hV f f.2]
  exact h ⟨_, hK i _ f f.2⟩



def tieMove (hL : LawsJ (setCE T c')) (hJ : JEvExists T R B.κ B.v₀) (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (hM : Moves B c' w) :
    @FWTie D G _ _ Pl0 T0 A (setCE T c') iA (moveR R (overEmb T w)) B.κ B.v₀ :=
  @FWTie.mk D G _ _ Pl0 T0 A (setCE T c') iA (moveR R (overEmb T w)) B.κ B.v₀ B.fw.alg_eq B.fw.e B.fw.ks B.fw.kap B.fw.pt
    B.fw.nrm_eq hL B.fw.chiR B.fw.hv₀ B.fw.x0
    (fun i σ hσ hV h => absurd ⟨((R.FW i).j σ).comp ((R.FW i).ρ (overEmb T w i σ)), ev_move hJ hK hM i σ hσ hV⟩ h)
    (fun i σ hσ hV _ => ev_move hJ hK hM i σ hσ hV)



theorem exists_geoHalf_move (hL : LawsJ (setCE T c')) (hI : InGeo B) (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (hM : Moves B c' w)
    (hF : @Fired D G _ _ Pl0 T0 A (setCE T c') iA R B.κ B.v₀ B.O fun _ => 1) :
    ∃ B' : @GeoHalf D G _ _ Pl0 T0 A (setCE T c') iA (moveR R (overEmb T w)) fun _ => 1,
      @GeoHalf.v₀ D G _ _ Pl0 T0 A (setCE T c') iA _ _ B' = B.v₀ := by
  have hF' := @Half.fired_upd D G _ _ Pl0 T0 A (setCE T c') iA R B.κ B.v₀ R.nW (fun i => moveForms (R.FW i) (overEmb T w i)) B.O _ hF
  refine ⟨@GeoHalf.mk D G _ _ Pl0 T0 A (setCE T c') iA (moveR R (overEmb T w)) _ B.κ B.v₀ (tieMove hL hI.jEvExists hK hM)
    (fun i σ hσ hV => ?_) (fun i => @Half.updO D G _ _ Pl0 T0 A (setCE T c') iA R _ _ _ _ _ (B.O i))
    (fun i => @Half.omPins_upd D G _ _ Pl0 T0 A (setCE T c') iA R B.κ B.v₀ _ _ B.O i (B.pins i)) B.rhoGeo
    (fun i σ hσ hV _ => hF'.2 i σ hσ hV) (fun i _ => ⟨1, hF'.1 i⟩) (fun i _ _ => hF'.1 i), rfl⟩
  obtain ⟨v, hv, h⟩ := bar_move hI.jEvBar hK hM i σ hσ hV
  exact ⟨fun _ => ⟨v, hv, h⟩, fun h' => absurd ⟨v, hv, (tieMove hL hI.jEvExists hK hM).jK i σ, h⟩ h'⟩

end Half

omit iA in
theorem phiC_setCE_of_eq {c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ} {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D}
    (hV : T.V j σ = W) (e : c' j σ = T.cE j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC (setCE T c') hV a f = phiC T hV a f := by
  funext h
  rw [_root_.GlobalTheory.HeckeSup.phiC_apply, _root_.GlobalTheory.HeckeSup.phiC_apply]
  exact congrArg (fun c => (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * adel W (castDict hV (T.dict j σ))
      (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) c) (rdU (T.U j σ) f) h) e



theorem exists_framed_half (hP : GlobalTheory.Published.CuspRapidDecay) (hsz : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) {F : Face D A}
    (hC : GlobalTheory.Core5 R F) (B : GeoHalf T R fun _ => 1) (hU : R.LUnif) (hI : InGeo B) :
    ∃ (c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → G),
      (∀ i σ, w i σ ∈ Subgroup.center G) ∧
      (∀ (i : Fin D.R.m) hV, @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin D G _ _ Pl0 T0 A (setCE T c') iA R i T.σ₀ hV) ∧
      ∃ B' : @GeoHalf D G _ _ Pl0 T0 A (setCE T c') iA (moveR R w) fun _ => 1,
        @GeoHalf.v₀ D G _ _ Pl0 T0 A (setCE T c') iA _ _ B' = B.v₀ := by
  classical
  choose c1 z hz hO hfr hs using exists_shift hP hsz hC B hU hI.jEvExists
  have ht : TieIn T R B.κ B.v₀ := ⟨B.fw.laws, B.fw.alg_eq, B.fw.kap, B.fw.hv₀, B.fw.chiR, B.fw.x0⟩
  have hpb : T.pb = R.C.P.pb :=
    GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R B.fw.laws.toLawsM hC.lev ((B.pins ⟨0, by have := D.R.two_le_m; omega⟩).2.tuple ()).half
  have hx := GlobalTheory.T.exists_equivariant_unit_constants_goodEmbedding T R B.κ B.v₀ B.O hC.lev ht hpb B.pins
  have H : ∀ (n : ℕ) (σ : T.Q.c.F →+* ℂ), ∃ c : (T.U (n + 1) σ).Comp → ℂ, ∀ hn : n < D.R.m,
      (σ = T.σ₀ → HEq c (c1 ⟨n, hn⟩)) ∧ (σ ≠ T.σ₀ → c = T.cE (n + 1) σ) := by
    intro n σ
    by_cases hσ : σ = T.σ₀
    · subst hσ
      by_cases hn : n < D.R.m
      · exact ⟨c1 ⟨n, hn⟩, fun _ => ⟨fun _ => HEq.rfl, fun h => absurd rfl h⟩⟩
      · exact ⟨fun _ => 1, fun h => absurd h hn⟩
    · exact ⟨T.cE (n + 1) σ, fun _ => ⟨fun h => absurd h hσ, fun _ => rfl⟩⟩
  choose c hc using H
  have h0 : ∀ i : Fin D.R.m, c i T.σ₀ = c1 i := fun i => eq_of_heq ((hc i T.σ₀ i.2).1 rfl)
  have h1 : ∀ (i : Fin D.R.m) σ, σ ≠ T.σ₀ → c i σ = T.cE ((i : ℕ) + 1) σ := fun i σ => (hc i σ i.2).2
  let c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ :=
    fun j => Nat.casesOn (motive := fun j => ∀ σ : T.Q.c.F →+* ℂ, (T.U j σ).Comp → ℂ) j (fun _ _ => 1) c
  let w : Fin D.R.m → (T.Q.c.F →+* ℂ) → G := fun i σ => if σ = T.σ₀ then z i else 1
  have hK : ∀ i, ActKeeps (κ := B.κ) B.O i := fun i g f hf => by
    obtain ⟨k, hk, -⟩ := (B.pins i).2.lift.lev g
    exact ((hO i).1 g k hk f hf).1
  have hL : LawsJ (setCE T c') := lawsJ_setCE B.fw.laws fun j hj σ hσ => by
    cases j with
    | zero => exact fun _ => norm_one
    | succ n =>
      by_cases e : σ = T.σ₀
      · subst e
        have h : CUnit (c1 ⟨n, hj.2⟩) := (hO ⟨n, hj.2⟩).2.1.2.2.2.1
        rw [← h0 ⟨n, hj.2⟩] at h
        exact h
      · have h := B.fw.laws.cUnit _ hj σ hσ
        have e2 : c n σ = T.cE (n + 1) σ := h1 ⟨n, hj.2⟩ σ e
        rw [← e2] at h
        exact h
  have hM : Moves B c' w := fun i σ hσ hV f hf => by
    by_cases e : σ = T.σ₀
    · subst e
      rw [show w i T.σ₀ = z i from if_pos rfl]
      funext h
      rw [_root_.GlobalTheory.HeckeSup.phiC_apply, _root_.GlobalTheory.HeckeSup.phiC_apply]
      have h2 := hs i f hf h
      rw [← h0 i] at h2
      exact congrArg (_ * ·) h2
    · rw [show w i σ = 1 from if_neg e, phiC_setCE_of_eq hV (h1 i σ e)]
      have h2 := rho_e hK i 1 ⟨f, hf⟩
      rw [map_one] at h2
      have h3 := congrArg Subtype.val ((B.fw.e i).injective (Subtype.ext h2))
      exact congrArg _ h3
  have hF : @Fired D G _ _ Pl0 T0 A (setCE T c') iA R B.κ B.v₀ B.O fun _ => 1 := by
    refine ⟨fun i => ?_, fun i σ hσ hV => ?_⟩
    · have h := hO i
      rw [← h0 i] at h
      exact h
    · by_cases e : σ = T.σ₀
      · subst e
        have h := GlobalTheory.RealGeoConst.eqAt_base T R B.κ B.v₀ hC.lev ht i (B.O i) (c1 i) (hO i).1 hV
        rw [← h0 i] at h
        exact h
      · have h := B.equivAll i σ hσ hV (hx i σ hσ hV)
        rw [← h1 i σ e] at h
        exact h
  refine ⟨c', overEmb T w, fun i σ => ?_, fun i hV => hfr i c' (h0 i) hV, exists_geoHalf_move hL hI hK hM hF⟩
  have key : ∀ s, w i s ∈ Subgroup.center G := fun s => by
    by_cases e : s = T.σ₀
    · rw [show w i s = z i from if_pos e]
      exact hz i
    · rw [show w i s = 1 from if_neg e]
      exact one_mem _
  unfold overEmb
  split_ifs
  · exact key _
  · exact key _

end GlobalTheory.Unframe
end
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspBound

theorem exists_mul_mem_closure {O K Ω : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [Field Ω] [Algebra K Ω] (S : Set Ω) {x : Ω} (hx : x ∈ Algebra.adjoin K S) :
    ∃ κ : O, κ ≠ 0 ∧ algebraMap K Ω (algebraMap O K κ) * x ∈
      Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ S) := by
  have hmem : ∀ u : O, algebraMap K Ω (algebraMap O K u) ∈
      Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ S) :=
    fun u => Subring.subset_closure (Or.inl ⟨u, rfl⟩)
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    exact ⟨1, one_ne_zero, by rw [map_one, map_one, one_mul]; exact Subring.subset_closure (Or.inr hx)⟩
  | algebraMap r =>
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) r
    have hb0 : algebraMap O K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
    rw [← map_mul, mul_div_cancel₀ _ hb0]
    exact hmem a
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, h1⟩ := hx
    obtain ⟨t, ht, h2⟩ := hy
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have e : algebraMap K Ω (algebraMap O K (s * t)) * (x + y) =
        algebraMap K Ω (algebraMap O K t) * (algebraMap K Ω (algebraMap O K s) * x) +
        algebraMap K Ω (algebraMap O K s) * (algebraMap K Ω (algebraMap O K t) * y) := by
      simp only [map_mul]; ring
    rw [e]
    exact add_mem (mul_mem (hmem t) h1) (mul_mem (hmem s) h2)
  | mul x y _ _ hx hy =>
    obtain ⟨s, hs, h1⟩ := hx
    obtain ⟨t, ht, h2⟩ := hy
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have e : algebraMap K Ω (algebraMap O K (s * t)) * (x * y) =
        (algebraMap K Ω (algebraMap O K s) * x) * (algebraMap K Ω (algebraMap O K t) * y) := by
      simp only [map_mul]; ring
    rw [e]
    exact mul_mem h1 h2

theorem inV_iff' (T : CDVR) (x : T.Fr) : InV T x ↔ 0 ≤ vV T.V x := by
  by_cases h0 : x = 0
  · subst h0; simp [InV, vV]
  have hne := valV_ne_zero (V := T.V) h0
  constructor
  · rintro ⟨a, rfl⟩
    have h1 : valV T.V (algebraMap T.V T.Fr a) ≤ 1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a
    have h2 := (WithZero.log_le_log hne one_ne_zero).2 h1
    rw [WithZero.log_one] at h2
    unfold vV; omega
  · intro h
    have h4 : valV T.V x ≤ 1 := by
      refine (WithZero.log_le_log hne one_ne_zero).1 ?_
      rw [WithZero.log_one]
      unfold vV at h
      omega
    exact IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h4

theorem inV_of_overLa' {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {T : CDVR}
    {io : K →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) (a : (la.valuation K).valuationSubring) : InV T (io a) := by
  rw [inV_iff', ho.2]
  refine mul_nonneg (Nat.cast_nonneg e) ?_
  by_cases h0 : (a : K) = 0
  · simp [h0, vLa]
  have hne : la.valuation K (a : K) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have h2 := (WithZero.log_le_log hne one_ne_zero).2 a.2
  rw [WithZero.log_one] at h2
  unfold vLa; omega

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem inV_iff_of_frBor {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) {T : CDVR}
    {io : c.F →+* T.Fr} (y y' : IntFr Xo c T io) (t : Ix Dw → T.Frˣ)
    (h : letI := io.toAlgebra; FrBor t y.1 y'.1) : InV T (evI y f) ↔ InV T (evI y' f) := by
  obtain ⟨hE, hU, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have h1 := unitIndep_of hE.wt hU a n f hf T io y y' t h 1
  have key : ∀ x : T.Fr, InV T x ↔ 0 ≤ nval T.V 1 x := fun x => by
    by_cases h0 : x = 0
    · subst h0; simp [nval_zero, InV]
    · rw [nval_of_ne h0, inV_iff', EReal.coe_nonneg]; simp
  rw [key, key, h1]

theorem inV_of_mem_B {O : Type} [CommRing O] {β : O →+* c.F} (P : GlobalTheory.Reg.PChart Xo c β) {e : P.Ω} {T : CDVR}
    {io : c.F →+* T.Fr} (ψ : P.R e →+* T.Fr) (hψ : ∀ k, ψ (algebraMap c.F _ k) = io k) (hO : ∀ a, InV T (io (β a)))
    (hg : ∀ g : P.R e, (g : P.Ω) ∈ P.gens → InV T (ψ g)) (s : P.R e) (hs : (s : P.Ω) ∈ P.B) : InV T (ψ s) := by
  have hle : P.B ≤ (((algebraMap T.V T.Fr).range.comap ψ).map (P.R e).val.toRingHom) := by
    refine Subring.closure_le.2 ?_
    rintro w (⟨o, rfl⟩ | hw)
    · refine ⟨algebraMap c.F _ (β o), ?_, rfl⟩
      show ψ (algebraMap c.F _ (β o)) ∈ (algebraMap T.V T.Fr).range
      rw [hψ]; exact hO o
    · exact ⟨⟨w, Algebra.subset_adjoin (Or.inr hw)⟩, hg _ hw, rfl⟩
  obtain ⟨w, hw, hw'⟩ := hle hs
  obtain rfl : w = s := Subtype.ext hw'
  exact hw

end GlobalTheory.CuspBound

namespace GlobalTheory.CuspBound


set_option maxHeartbeats 1000000 in
theorem exists_bddAll_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∃ κ : c.F, κ ≠ 0 ∧ BddAll Xo c la κ f := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro E _ _ _ H Dw l Xo c r U hU la p hp hpl hg a n f hd hf
    obtain ⟨J, hJ, P, hC, hreg⟩ := GlobalTheory.T.exists_integral_chart_cover_cuspForm_no_pole E H Dw l Xo c r U hU la p hp hpl hg a n f hd hf
    haveI := Fintype.ofFinite J
    choose κ hκ0 hκ using fun j =>
      exists_mul_mem_closure (O := (la.valuation c.F).valuationSubring) (K := c.F) ((P j).gens : Set (P j).Ω) (hreg j)
    have hF := cusp_le_sec Xo c U a n hf
    refine ⟨algebraMap (la.valuation c.F).valuationSubring c.F (∏ j, κ j), ?_, ?_⟩
    · exact (map_ne_zero_iff _ (IsFractionRing.injective _ c.F)).2 (Finset.prod_ne_zero_iff.2 fun j _ => hκ0 j)
    intro T io m ho y _
    letI := io.toAlgebra
    obtain ⟨hE, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
    have hev := GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a n f hF
    let W : ValuationSubring T.Fr := (valV T.V).valuationSubring
    have hW : ∀ x, x ∈ W ↔ InV T x := fun x =>
      ⟨fun h => IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h,
        by rintro ⟨a, rfl⟩; exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a⟩
    have hO : ∀ a : (la.valuation c.F).valuationSubring, InV T (io (algebraMap _ c.F a)) := fun a => inV_of_overLa' ho a
    obtain ⟨j, e, he, ψ, z, t, hgW, hz, ht⟩ := hC T.Fr W (fun a => (hW _).2 (hO a)) y.1
    have hzI : Integral T io z := (P j).int e he T io ψ (fun a => hO a) (fun g hg => (hW _).1 (hgW g hg)) z hz
    let z' : IntFr Xo c T io := ⟨z, hE.test _ z, hzI⟩
    set κ' := algebraMap (la.valuation c.F).valuationSubring c.F (∏ j, κ j) with hκ'
    rw [← evI_smul, inV_iff_of_frBor (Submodule.smul_mem _ κ' hF) y z' t ht, evI_smul]
    show InV T (io κ' * evR Xo c f z)
    rw [(hev _).1 _ ψ _ _ hz]
    let s : (P j).R e := algebraMap c.F _ κ' * evR Xo c f ((P j).y e he)
    have hs : ψ s = io κ' * ψ (evR Xo c f ((P j).y e he)) := by
      simp only [s, map_mul, AlgHom.commutes]; rfl
    rw [← hs]
    refine inV_of_mem_B (P j) ψ.toRingHom (fun k => ψ.commutes k) hO
      (fun g hg => (hW _).1 (hgW g hg)) s ?_
    have hyg : evR Xo c f (P j).yg = ((P j).R e).val (evR Xo c f ((P j).y e he)) :=
      (hev _).1 _ ((P j).R e).val _ _ ((P j).gen e he)
    obtain ⟨d, hd'⟩ : κ j ∣ ∏ i, κ i := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    have e1 : ((s : (P j).R e) : (P j).Ω) = algebraMap c.F (P j).Ω (algebraMap _ c.F d) *
        (algebraMap c.F (P j).Ω (algebraMap _ c.F (κ j)) * evR Xo c f (P j).yg) := by
      rw [hyg]
      simp only [s, hκ', hd', map_mul, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_val]
      ring
    rw [e1]
    exact mul_mem (Subring.subset_closure (Or.inl ⟨d, rfl⟩)) (hκ j)

end GlobalTheory.CuspBound
end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries
open CategoryTheory


theorem _root_.GlobalTheory.T.exists_scalar_levelCover_analyticFibre : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (C : Cover T j σ), C.d.IsLev → C.σ₂.comp C.inc = σ → ∀ (y : FrPt (T.Q.Xo j) T.Q.c (CAt σ)) (y₂ : FrPt C.d.Xo₂ C.d.c₂ (CAt C.σ₂)), (y₂.x : Sp ℂ ⟶ C.d.Xo₂.X) ≫ C.d.r = (y.x : Sp ℂ ⟶ (T.Q.Xo j).X) → (∀ τ i, (y₂.u τ i : Sp (DualNumber ℂ) ⟶ C.d.Xo₂.univ.t.G.left) ≫ C.d.m.φ = (y.u τ i : Sp (DualNumber ℂ) ⟶ (T.Q.Xo j).univ.t.G.left)) → ∃ t : ℂ, t ≠ 0 ∧ (∀ (n : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ), ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ : Rul C.d.Xo₂ C.d.c₂, C.IsPull f f₂ → toC (evR C.d.Xo₂ C.d.c₂ f₂ y₂) = t ^ n * toC (evR (T.Q.Xo j) T.Q.c f y)) ∧ ∀ (r g : ℕ) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 (T.Q.Dw j)) (x : Frame X.Ψ r) (L : Lt D.host.E r) (mk : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ ϑ : (Fin g → ℂ) → ℂ, (letI : Algebra T.Q.c.F ℂ := σ.toAlgebra; ∃ A : AnFib X bas idx e x L y, A.Marked mk ∧ A.Reads 1 y.s ϑ) → (letI : Algebra C.d.c₂.F ℂ := C.σ₂.toAlgebra; ∃ A₂ : AnFib X bas idx e x L y₂, A₂.Reads 1 y₂.s (fun z => t * ϑ z)) := by
  first | exact @GlobalTheory.CoverFibScalar.exists_scalar_fib | exact GlobalTheory.CoverFibScalar.exists_scalar_fib | (intros; apply GlobalTheory.CoverFibScalar.exists_scalar_fib <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.goodModelVector_eq_classSum_baseLevel : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j t, GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.GoodRangeAt X.R.toRealDat j t) →
    ∀ i, BaseTup Y i → ∀ (j : Fin D.R.m) (b : Bool), ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.goodModel X.R.toRealDat j,
      (∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (κ : GA D (Wc D j)),
        Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b u) κ → ∀ g,
        (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) (g * κ) =
          Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) *
          (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) g) →
      ∃ F ∈ Submodule.span ℂ (Y.Z.ρ.mt i j b 0 ∅ 1 : Set (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank)),
        (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) = Y.Z.ρ.sum i j b 0 ∅ 1 F := by
  first | exact @GlobalTheory.TypeClassSum.goodModel_eq_classSum | exact GlobalTheory.TypeClassSum.goodModel_eq_classSum | (intros; apply GlobalTheory.TypeClassSum.goodModel_eq_classSum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rationalHeckeOperators_adelicReading : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → ∀ (D : D7) (X : RealSide D), ∀ (S : RatDat D.ntw) (YS : NExpRealS X.R X.cG S), ∃ hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j), (∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j)) ∧ (∀ j P, hL j 0 P = 1) ∧ GlobalTheory.ExportPin.Reads X.R X.cG S YS hL := by
  first | exact @GlobalTheory.HeckeFamRead.exists_family_reads | exact GlobalTheory.HeckeFamRead.exists_family_reads | (intros; apply GlobalTheory.HeckeFamRead.exists_family_reads <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie

theorem _root_.GlobalTheory.T.heckeQuotient_integral_framed_point_complete_field : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), HeckeStable YS iC b j := by
  first | exact @GlobalTheory.HeckeStableAt.heckeStable | exact GlobalTheory.HeckeStableAt.heckeStable | (intros; apply GlobalTheory.HeckeStableAt.heckeStable <;> assumption)
end
