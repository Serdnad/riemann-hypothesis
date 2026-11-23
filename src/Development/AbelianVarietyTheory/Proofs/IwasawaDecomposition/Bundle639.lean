module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle505
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle007
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle076
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle081
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupActsByLiftTranslationPrincipalType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCuspIsThClsDOfPre
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.Meromorphic.Order
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult
open GlobalTheory.RealGeo GlobalTheory.OneMapAll GlobalTheory.AdTh

namespace GlobalTheory.Mem.R3.Rw.GeoTies

theorem eq_of_span {H ι X : Type} [AddCommGroup H] [Module ℂ H] {M : ι → Type} [∀ t, AddCommGroup (M t)] [∀ t, Module ℂ (M t)]
    (θ : H →ₗ[ℂ] ((∀ t, M t) →ₘₗ[ℂ] (X → ℂ))) (v : ∀ t, M t) (a b : X) (c : ℂ) {S : Set H} (hS : Submodule.span ℂ S = ⊤)
    (h : ∀ y ∈ S, θ y v a = c * θ y v b) (y : H) : θ y v a = c * θ y v b := by
  have hy : y ∈ Submodule.span ℂ S := hS ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => simp
  | add y y' _ _ h h' =>
    simp only [map_add (f := _), add_apply, Pi.add_apply]
    linear_combination h + h'
  | smul a y _ h =>
    simp only [map_smul, smul_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination a * h

theorem span_image {H H' : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup H'] [Module ℂ H'] (e : H ≃ₗ[ℂ] H') {S : Set H}
    (hS : Submodule.span ℂ S = ⊤) : Submodule.span ℂ (e '' S) = ⊤ := by
  have := congrArg (Submodule.map (e : H →ₗ[ℂ] H')) hS
  rwa [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at this

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section One

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

def adOver (O : OMDat C R i Tp tup) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c')
    (g : GA D (Wc D i)) : ℂ :=
  cc (O.dict g).1 * (O.mu g * rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) f (O.dict g).1 (O.dict g).2)

theorem adOver_of_isBC (O : OMDat C R i Tp tup) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) {m : ℕ}
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'} {as : Fin m → O.c'.F} {fs : Fin m → Rul (C.Q.Xo ((i : ℕ) + 1)) C.Q.c}
    (h : IsBC O.hle f as fs) (g : GA D (Wc D i)) : adOver O cc f g = ∑ k, (as k : ℂ) * O.phi cc (fs k) g := by
  have h2 := GlobalTheory.PhaseRational.rdU_of_isBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c') h (O.dict g).1 (O.dict g).2
  refine (congrArg (fun w => cc (O.dict g).1 * (O.mu g * w)) h2).trans ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show cc _ * (O.mu _ * ((as k : ℂ) * _)) = (as k : ℂ) * (cc _ * O.mu _ * _)
  ring

theorem adOver_act (O : OMDat C R i Tp tup) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} (hn : κ.n = (Vc D i).rank)
    (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c O.lev2) {cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ} (hE : O.EquivAt κ cc)
    {z : G} {k : GA D (Wc D i)} (hk : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG z) k)
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'} (hf : f ∈ cuspOver O κ) (g : GA D (Wc D i)) :
    adOver O cc (actLev O.c' O.lev2 z f) g =
      (∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG z PP)) : ℂˣ) : ℂ)) * adOver O cc f (g * k) := by
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).2 _ (C.U ((i : ℕ) + 1)) _ _ f hf
  have h1 := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hact).2 _ _ z m as fs f ((mem_cusp _ _ _ _ _ _).1 hf).1
    (fun l => ((mem_cusp _ _ _ _ _ _).1 (hfs l)).1) hBC
  rw [adOver_of_isBC O cc h1, adOver_of_isBC O cc hBC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [(hE z k hk (fs l) (by rw [hn]; exact hfs l)).2 g]
  ring

end One

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {i : Fin D.R.m}

def LiftIsSum (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : (R.MW i (sg0 D A)).Vec)
    (cc : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (z : G) (ζ : ℂ) (y : (R.HV i A.μ0).H) : Prop :=
  ∃ h J x f, RepsR R i A.μ0 h (O.bad ()) J (O.Lh ()) (O.gam ()) (O.vol ()) ∧ Place R i A.μ0 h O.c0' y x ∧
    f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank ∧ IsSum O () x f ∧
    ∀ q : AutQ (Wc D i), R.thF i A.μ0 y v₀ q.out =
      ζ * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * adOver O cc (actLev O.c' O.lev2 z f) q.out



theorem oneMapOf_of_span (hR : PreChar R) (hchi : R.grp_chiW) (hT : Formalism.IndefR.FWT.TieIn T R κ v₀)
    (O : OMDat T.toCore R i Unit (fun _ => A.μ0))
    (hF : O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) {cE : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ}
    (hU : ∀ k, ‖cE k‖ = 1) (hE : O.EquivAt (κ i) cE) {z : G} (hz : z ∈ Subgroup.center G) {ζ : ℂ}
    (hζL : ζ ∈ D.what₂.embLL.toRatAlgHom.fieldRange) (hζ : ∃ m : ℕ, 0 < m ∧ ζ ^ m = 1)
    (hS : Submodule.span ℂ {y | LiftIsSum O (κ i) (v₀ i (sg0 D A)) cE z ζ y} = ⊤) :
    O.OneMapOf (κ i) (v₀ i (sg0 D A)) cE 1 := by
  have hio : IoExt R := GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A T.Q.c.F R hR.lev hR.fam hR.models hR.thP
  have hn : (κ i).n = (Vc D i).rank :=
    (hT.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm
  obtain ⟨cc₀, -, u, -, -, hser, -⟩ := exists_ccIs_equivAt_serOf_tie D G Pl0 T0 A T R κ v₀ hR hT hio i _ _ O hP
  generalize u • cc₀ = cc at hser
  have hex := GlobalTheory.ClassSumRule.exists_cusp_isThClsD_ofPre GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R κ v₀ hR hT i _ _ O hP ()
  obtain ⟨k, hk, -⟩ := hP.lift.lev z
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) := ⟨_, rfl⟩
  obtain ⟨χ, hχ⟩ : ∃ χ : ℂ, χ = ∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG z PP)) : ℂˣ) : ℂ) :=
    ⟨_, rfl⟩
  have hcc : ∀ c, cc c ≠ 0 := fun c => norm_ne_zero_iff.1 ((hser.1 c).trans_ne one_ne_zero)
  have key : ∀ h J x f y, RepsR R i A.μ0 h (O.bad ()) J (O.Lh ()) (O.gam ()) (O.vol ()) → Place R i A.μ0 h O.c0' y x →
      f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) O.c' (wtA (κ i)) (Vc D i).rank → IsSum O () x f → ∀ g,
      ζ * s * adOver O cE (actLev O.c' O.lev2 z f) g = ζ * χ * (cE (O.dict (g * k)).1 / cc (O.dict (g * k)).1) *
        R.thF i A.μ0 y (v₀ i (sg0 D A)) (g * k) := by
    intro h J x f y hr hy hf hx g
    obtain ⟨f₁, hf₁, hx₁⟩ := hex x
    have e : f = f₁ := isSum_unique hP () hf ((mem_cusp _ _ _ _ _ _).1 hf₁).1 hx hx₁
    have h1 := adOver_act O hn hP.act.1 hE hk (e ▸ hf₁ : f ∈ cuspOver O (κ i)) g
    have h2 := (one_mul _).symm.trans (hser.2.2 () h J hr y x hy f hf hx (g * k))
    rw [h1, h2, ← hχ, ← hs, adOver]
    have := hcc (O.dict (g * k)).1
    field_simp
  have all : ∀ y (q : AutQ (Wc D i)), R.thF i A.μ0 y (v₀ i (sg0 D A)) q.out =
      ζ * χ * (cE (O.dict (q.out * k)).1 / cc (O.dict (q.out * k)).1) * R.thF i A.μ0 y (v₀ i (sg0 D A)) (q.out * k) := by
    intro y q
    refine eq_of_span (R.thF i A.μ0) _ _ _ _ hS (fun y hy => ?_) y
    obtain ⟨h, J, x, f, h1, h2, h3, h4, h5⟩ := hy
    rw [h5 q, ← hs]
    exact key h J x f y h1 h2 h3 h4 _
  have hid : GlobalTheory.PhaseRational.IdentityAt O (κ i) cE 1 := by
    obtain ⟨h, J, hr, -, hA, hPl⟩ := (hP.tuple ()).reps
    refine ⟨hU, norm_one, z, hz, fun t => ⟨ζ, hζL, hζ, fun x hx => ⟨hex x, fun f hf hc q => ?_⟩⟩⟩
    obtain ⟨x₀, hx₀⟩ := (hPl x).1 hx
    have h1 := (all _ q).trans (key h J x f _ hr hx₀ hf hc q.out).symm
    rw [one_mul, hA _ x hx₀]
    refine h1.trans ?_
    rw [hs, mul_right_comm ζ (cE _), mul_assoc (ζ * _) (cE _)]
    rfl
  exact ⟨hE, ⟨hF.ge, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).2 _ _,
    (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hP.act.1).2, hid⟩,
    GlobalTheory.PhaseRational.phRat_of_identity O (κ i) _ cE 1 () rfl hF hP hT.laws.toLawsM (hT.kap i (D.eTau.symm 1)).2.2 hchi
      hR.thP.thF_mem hR.thP.thG hE hid⟩



theorem lift_of_oneMapOf (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
    {ι x₀} (hP : O.Pins κ v₀ ι x₀) {cE : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ} (h : O.OneMapOf κ v₀ cE 1) :
    ∃ z ∈ Subgroup.center G, ∃ ζ ∈ D.what₂.embLL.toRatAlgHom.fieldRange, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      ∃ h J, RepsR R i A.μ0 h (O.bad ()) J (O.Lh ()) (O.gam ()) (O.vol ()) ∧ ∀ y₀ : A.fam.amb.FL i A.μ0, ∃ x f,
        Place R i A.μ0 h O.c0' (jVx R i A.μ0 y₀) x ∧ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank ∧ IsSum O () x f ∧
        ∀ q : AutQ (Wc D i), R.thF i A.μ0 (jVx R i A.μ0 y₀) v₀ q.out =
          ζ * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * adOver O cE (actLev O.c' O.lev2 z f) q.out := by
  obtain ⟨-, ⟨-, -, -, -, -, z, hz, h1⟩, -⟩ := h
  obtain ⟨ζ, hζL, hζ, h1⟩ := h1 ()
  obtain ⟨h, J, hr, hPx, hA, hPl⟩ := (hP.tuple ()).reps
  refine ⟨z, hz, ζ, hζL, hζ, h, J, hr, fun y₀ => ?_⟩
  obtain ⟨x, hx⟩ := hPx y₀
  obtain ⟨⟨f, hf, hc⟩, h2⟩ := h1 x ((hPl x).2 ⟨y₀, hx⟩)
  have hf' := ((mem_cusp _ _ _ _ _ _).1 hf).1
  refine ⟨x, f, hx, hf', hc, fun q => ?_⟩
  have h3 := h2 f hf' hc q
  rw [one_mul, hA _ x hx, mul_right_comm ζ (cE _), mul_assoc (ζ * _) (cE _)] at h3
  exact h3

theorem exists_equiv_lift {V : HSp D} {S S' : D.what₂.Tau → SPar} {M : DSModel V S} {M' : DSModel V S'} (hM : ModelSame M M')
    {Γ W W' : Type} {nW : NormedAddCommGroup W} {nW' : NormedAddCommGroup W'} {iW : InnerProductSpace ℂ W}
    {iW' : InnerProductSpace ℂ W'} (h1 : HEq W' W) (h2 : HEq nW' nW) (h3 : HEq iW' iW) {H : HMod (Γ → W)} {H' : HMod (Γ → W')}
    (hH : HEq H' H) {θ : H.H →ₗ[ℂ] MMap M} {θ' : H'.H →ₗ[ℂ] MMap M'} (hθ : HEq θ' θ) {v : M.Vec} {v' : M'.Vec} (hv : HEq v' v) :
    ∃ e : H.H ≃ₗ[ℂ] H'.H, ∀ y, HEq (e y) y ∧ θ' (e y) v' = θ y v := by
  cases h1; cases h2; cases h3; cases hH
  cases M; cases M'
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hM
  dsimp only at a1 a2 a3 a4 a5 a6 a7
  cases a1; cases a2; cases a3; cases a4; cases a5; cases a6; cases a7
  have e1 : θ' = θ := eq_of_heq hθ
  have e2 : v' = v := eq_of_heq hv
  exact ⟨LinearEquiv.refl _ _, fun y => ⟨HEq.rfl, by rw [e1, e2]; rfl⟩⟩

theorem adOver_rulBC {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type}
    {tup : Tp → T0} (O : OMDat C R i Tp tup) (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c O.lev2)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff C.Q.l) (hle : O.c'.F ≤ c.F) (h₃ : C.Q.c.F ≤ c.F) {lev} (hlev : lev = O.lev)
    (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (z : G) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'} (hf : f ∈ sec _ O.c' a n) (g : GA D (Wc D i)) :
    cc (O.dict g).1 * (O.mu g * rdU (unfBC h₃ (C.U ((i : ℕ) + 1)) (inC c))
      (actLev c (fun g => (lev g, LinearMap.id)) z (GlobalTheory.FieldBC.rulBC hle f)) (O.dict g).1 (O.dict g).2) =
      adOver O cc (actLev O.c' O.lev2 z f) g := by
  subst hlev
  obtain ⟨m, as, fs, hfs, h⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).1 a n f hf
  have h1 := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hact).2 a n z m as fs f hf hfs h
  have h2 := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ h₃ _ _ hact).2 a n z m _ fs _ (GlobalTheory.FieldBCModel.rulBC_mem_sec hle hf) hfs
    (isBC_rulBC_trans O.hle hle h₃ hf h)
  have e1 := GlobalTheory.PhaseRational.rdU_of_isBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c') h1 (O.dict g).1 (O.dict g).2
  have e2 := GlobalTheory.PhaseRational.rdU_of_isBC h₃ (C.U ((i : ℕ) + 1)) (inC c) h2 (O.dict g).1 (O.dict g).2
  exact congrArg (fun w => cc (O.dict g).1 * (O.mu g * w)) (e2.trans e1.symm)

end GlobalTheory.Mem.R3.Rw.GeoTies

end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc

theorem not_eventually_re_pos_of_periodic {f : ℂ → ℂ} {M : ℝ} (hM : 0 < M) (hper : Function.Periodic f M)
    (hd : ∀ᶠ z in imTop, DifferentiableAt ℂ f z) (h0 : Tendsto f imTop (𝓝 0)) :
    ¬ ∀ᶠ z in imTop, 0 < (f z).re := by
  intro hpos
  set F := Function.Periodic.cuspFunction M f with hF
  have hF0 : F 0 = 0 := Function.Periodic.cuspFunction_zero_of_zero_at_inf hM h0
  have hd0 : DifferentiableAt ℂ F 0 :=
    Function.Periodic.differentiableAt_cuspFunction_zero hM hper hd
      (Filter.ZeroAtFilter.boundedAtFilter (l := comap Complex.im atTop) (f := f) h0)
  have hd1 : ∀ᶠ q in 𝓝[≠] 0, DifferentiableAt ℂ F q :=
    Function.Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero hM hper hd
  have hp1 : ∀ᶠ q in 𝓝[≠] (0 : ℂ), 0 < (F q).re := by
    filter_upwards [(Function.Periodic.invQParam_tendsto hM).eventually hpos, self_mem_nhdsWithin] with q hq hq0
    rwa [hF, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq0]
  have hd2 : ∀ᶠ q in 𝓝 (0 : ℂ), DifferentiableAt ℂ (fun z => Complex.exp (-F z)) q := by
    filter_upwards [eventually_nhdsWithin_iff.mp hd1] with q hq
    by_cases hq0 : q = 0
    · subst hq0; exact hd0.neg.cexp
    · exact (hq hq0).neg.cexp
  have hmax : IsLocalMax (norm ∘ fun z => Complex.exp (-F z)) 0 := by
    filter_upwards [eventually_nhdsWithin_iff.mp hp1] with q hq
    by_cases hq0 : q = 0
    · subst hq0; exact le_rfl
    · have := hq hq0
      simp only [Function.comp, Complex.norm_exp, hF0, Complex.neg_re, Real.exp_le_exp]
      simpa using this.le
  have hc := Complex.eventually_eq_of_isLocalMax_norm hd2 hmax
  obtain ⟨q, hq1, hq2⟩ := (hp1.and (hc.filter_mono nhdsWithin_le_nhds)).exists
  have := congrArg norm hq2
  simp only [Complex.norm_exp, hF0, Complex.neg_re, Real.exp_eq_exp] at this
  simp at this
  exact hq1.ne' this

theorem not_tendsto_re_atTop_of_periodic {L : ℂ → ℂ} {T M : ℝ} (hM : 0 < M)
    (hd : DifferentiableOn ℂ L {w | T < w.im}) (hper : ∀ w : ℂ, T < w.im → L (w + M) = L w) :
    ¬ Tendsto (fun w => (L w).re) imTop atTop := by
  intro ht
  have hT : ∀ᶠ w in imTop, T < w.im := (tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)
  have hopen : IsOpen {w : ℂ | T < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hpos : ∀ᶠ w in imTop, 0 < (L w).re := ht.eventually (eventually_gt_atTop 0)
  classical
  set f : ℂ → ℂ := fun w => if T < w.im then (L w)⁻¹ else 0 with hf
  have hfe : ∀ w : ℂ, T < w.im → f w = (L w)⁻¹ := fun w hw => if_pos hw
  refine not_eventually_re_pos_of_periodic (f := f) hM ?_ ?_ ?_ ?_
  · intro w
    by_cases hw : T < w.im
    · have hw' : T < (w + M).im := by simpa using hw
      rw [hfe _ hw, hfe _ hw', hper w hw]
    · have hw' : ¬ T < (w + M).im := by simpa using hw
      simp only [hf, if_neg hw, if_neg hw']
  · filter_upwards [hT, hpos] with w hw hw0
    have hne : L w ≠ 0 := fun h => by simp [h] at hw0
    refine ((hd.differentiableAt (hopen.mem_nhds hw)).inv hne).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hw] with z hz using hfe z hz
  · have h1 : Tendsto (fun w => ‖L w‖) imTop atTop :=
      tendsto_atTop_mono (fun w => Complex.re_le_norm (L w)) ht
    have h2 : Tendsto (fun w => (L w)⁻¹) imTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_inv]
      exact h1.inv_tendsto_atTop
    refine h2.congr' ?_
    filter_upwards [hT] with w hw using (hfe w hw).symm
  · filter_upwards [hT, hpos] with w hw hw0
    have hne : L w ≠ 0 := fun h => by simp [h] at hw0
    rw [hfe w hw, Complex.inv_re]
    exact div_pos hw0 (Complex.normSq_pos.mpr hne)

theorem tendsto_zero_of_norm_eq_mul_exp_periodic :
    ∀ (p L h a b : ℂ → ℂ) (T r : ℝ) (M n : ℕ) (ζ : ℂ), 0 < M → 0 < n → ζ ^ n = 1 → 0 < r → DifferentiableOn ℂ p {w | T < w.im} → DifferentiableOn ℂ L {w | T < w.im} → (∀ w : ℂ, T < w.im → p (w + M) = ζ * p w ∧ L (w + M) = L w ∧ ‖h (eTwoPi w)‖ = ‖p w‖ * ‖Complex.exp (L w)‖) → Tendsto p imTop (𝓝 0) → DifferentiableOn ℂ a (Metric.ball (0 : ℂ) r) → DifferentiableOn ℂ b (Metric.ball (0 : ℂ) r) → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → b u ≠ 0 ∧ h u * b u = a u) → Tendsto h (𝓝[≠] 0) (𝓝 0) := by
  intro p L h a b T r M n ζ hM _ _ hr _ hL hw hp ha hb hab
  have hball : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hr
  have hmer : MeromorphicAt h 0 := by
    refine ((ha.analyticAt hball).meromorphicAt.div (hb.analyticAt hball).meromorphicAt).congr ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin] with u hu hu0
    obtain ⟨h1, h2⟩ := hab u hu hu0
    simp only [Pi.div_apply]
    rw [← h2, mul_div_cancel_right₀ _ h1]
  rw [tendsto_zero_iff_meromorphicOrderAt_pos hmer]
  by_contra hord
  rw [not_lt] at hord
  have hne : ∀ᶠ u in 𝓝[≠] (0 : ℂ), h u ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hmer).mp (fun ht => by simp [ht] at hord)
  obtain ⟨c, hc⟩ : ∃ c, Tendsto h⁻¹ (𝓝[≠] 0) (𝓝 c) := by
    rw [tendsto_nhds_iff_meromorphicOrderAt_nonneg hmer.inv, meromorphicOrderAt_inv]
    induction hk : meromorphicOrderAt h 0 with
    | top => simp
    | coe k =>
      rw [hk] at hord
      have hk0 : k ≤ 0 := by exact_mod_cast hord
      have : (0 : ℤ) ≤ -k := by omega
      exact_mod_cast this
  have he : Tendsto eTwoPi imTop (𝓝[≠] 0) := by
    refine (Function.Periodic.qParam_tendsto (h := 1) one_pos).congr fun w => ?_
    simp [Function.Periodic.qParam, eTwoPi]
  have hT : ∀ᶠ w in imTop, T < w.im := (tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)
  refine not_tendsto_re_atTop_of_periodic (M := (M : ℝ)) (by exact_mod_cast hM) hL
    (fun w hw' => by simpa using (hw w hw').2.1) ?_
  rw [← tendsto_neg_atBot_iff, ← Real.tendsto_exp_comp_nhds_zero]
  have h1 := hp.norm.mul (hc.comp he).norm
  simp only [norm_zero, zero_mul] at h1
  refine h1.congr' ?_
  filter_upwards [hT, he.eventually hne] with w hw' hw0
  have h2 := (hw w hw').2.2
  have h3 : ‖h (eTwoPi w)‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  simp only [Function.comp, Pi.inv_apply, norm_inv]
  rw [Complex.norm_exp] at h2
  rw [Real.exp_neg, ← div_eq_mul_inv, div_eq_iff h3, h2]
  field_simp

end GlobalTheory.ShFam.BdArc
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

noncomputable section

namespace GlobalTheory.ShFam.BdArc

theorem exists_basicOpen_subset_of_pt {A : Type} [CommRing A] (f : A →+* ℂ) (U : Set (Sp A)) (hU : IsOpen U)
    (h : ∀ s, spMap f s ∈ U) :
    ∃ a : A, f a ≠ 0 ∧ Set.range (spMap (algebraMap A (Localization.Away a))) ⊆ U := by
  let s₀ : PrimeSpectrum ℂ := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨_, ⟨a, rfl⟩, h1, h2⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := A)).exists_subset_of_mem_open (h s₀) hU
  refine ⟨a, ?_, ?_⟩
  · intro h0
    apply h1
    show f a ∈ (⊥ : Ideal ℂ)
    simp [h0]
  · have := PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
    rintro _ ⟨s, rfl⟩
    apply h2
    show _ ∈ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A))
    rw [← this]
    exact ⟨s, rfl⟩

theorem exists_hol_away {A : Type} [CommRing A] (ψ : ℂ → (A →+* ℂ)) (V : Set ℂ)
    (hψ : ∀ b, DifferentiableOn ℂ (fun u => ψ u b) V) (a : A) (ha : ∀ u ∈ V, ψ u a ≠ 0) (u₀ : ℂ) (h₀ : u₀ ∈ V) :
    ∃ ev : ℂ → (Localization.Away a →+* ℂ), (∀ u ∈ V, (ev u).comp (algebraMap A _) = ψ u) ∧
      ∀ t, DifferentiableOn ℂ (fun u => ev u t) V := by
  classical
  let ev : ℂ → (Localization.Away a →+* ℂ) := fun u =>
    if h : u ∈ V then IsLocalization.Away.lift a (g := ψ u) (Ne.isUnit (ha u h))
    else IsLocalization.Away.lift a (g := ψ u₀) (Ne.isUnit (ha u₀ h₀))
  have hev : ∀ u ∈ V, (ev u).comp (algebraMap A _) = ψ u := fun u hu => by
    simp only [ev, dif_pos hu]
    exact IsLocalization.Away.lift_comp a _
  refine ⟨ev, hev, fun t => ?_⟩
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj a t
  refine (((hψ b).div ((hψ a).pow n) fun u hu => pow_ne_zero n (ha u hu))).congr fun u hu => ?_
  have h1 := congrArg (ev u) hb
  have h2 : ∀ z, ev u (algebraMap A _ z) = ψ u z := fun z => RingHom.congr_fun (hev u hu) z
  rw [map_mul, map_pow, h2, h2] at h1
  show _ = ψ u b / ψ u a ^ n
  rw [eq_div_iff (pow_ne_zero n (ha u hu)), h1]

theorem spMap_comp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem dualMap_comp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) :=
  by
    ext z <;> simp [dualMap]

theorem spMap_dualMap_sq {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    spMap (dualMap f) ≫ spMap (algebraMap A (DualNumber A)) = spMap (algebraMap B (DualNumber B)) ≫ spMap f := by
  rw [spMap_comp_comp, spMap_comp_comp]
  congr 1
  exact RingHom.ext fun z => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem arc_descends_to_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)), IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → ∀ u₀ ∈ Metric.ball (0 : ℂ) r, u₀ ≠ 0 → ∃ (R : Type) (_ : CommRing R) (xR : Sp R ⟶ Xo.X) (vR : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)) (ev : ℂ → (R →+* ℂ)) (V : Set ℂ), IsOpen V ∧ u₀ ∈ V ∧ (∀ t, DifferentiableOn ℂ (fun u => ev u t) V) ∧ ∀ u ∈ V, (y u).x = spMap (show R →+* CAt σ from ev u) ≫ xR ∧ ∀ τ i, (y u).u τ i = spMap (dualMap (show R →+* CAt σ from ev u)) ≫ vR τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ A _ φ x fr ψ r y harc hm u₀ hu₀ hne
  haveI := Z.jQ_open
  obtain ⟨a, ha, hsub⟩ := exists_basicOpen_subset_of_pt (ψ u₀) (x ⁻¹' Set.range Z.jQ)
    ((IsOpenImmersion.isOpen_range Z.jQ).preimage x.continuous) (fun s => by
      have h := (hm u₀ hu₀ hne).1
      refine ⟨GlobalTheory.AllWt.ptF (y u₀) s, ?_⟩
      exact (congrArg (fun g => g s) h :))
  have hopen : IsOpen {u | u ∈ Metric.ball (0 : ℂ) r ∧ ψ u a ≠ 0} :=
    ((harc.1.2 a).continuousOn).isOpen_inter_preimage Metric.isOpen_ball (isOpen_ne (x := (0 : ℂ)))
  let V : Set ℂ := {u | u ∈ Metric.ball (0 : ℂ) r ∧ ψ u a ≠ 0} ∩ {u | u ≠ 0}
  obtain ⟨ev, hev, hd⟩ := exists_hol_away ψ V (fun b => (harc.1.2 b).mono fun u hu => hu.1.1) a
    (fun u hu => hu.1.2) u₀ ⟨⟨hu₀, ha⟩, hne⟩
  let R := Localization.Away a
  let ι : A →+* R := algebraMap A R
  have hr : Set.range (spMap ι ≫ x) ⊆ Set.range Z.jQ := by
    rintro _ ⟨s, rfl⟩
    exact hsub ⟨s, rfl⟩
  let x' : Sp R ⟶ Xo.XF c := IsOpenImmersion.lift Z.jQ (spMap ι ≫ x) hr
  have hx' : x' ≫ Z.jQ = spMap ι ≫ x := IsOpenImmersion.lift_fac _ _ _
  have P : IsPullback Z.m.φ Z.oF.t.G.hom Z.t.G.hom (Z.jQ ≫ genι Z) := Z.m.cart.1
  have hw : ∀ τ i, (spMap (dualMap ι) ≫ fr.v τ i) ≫ Z.t.G.hom =
      (spMap (algebraMap R (DualNumber R)) ≫ x') ≫ Z.jQ ≫ genι Z := fun τ i => by
    rw [Category.assoc, (fr.tan τ i).1, ← Category.assoc, spMap_dualMap_sq, Category.assoc, Category.assoc,
      ← Category.assoc x', hx', Category.assoc]
  refine ⟨R, inferInstance, x' ≫ pullback.fst _ _, fun τ i => P.lift _ _ (hw τ i) ≫ Z.m0.toSABMap.φ, ev, V,
    hopen.inter isOpen_ne, ⟨⟨hu₀, ha⟩, hne⟩, hd, fun u hu => ?_⟩
  obtain ⟨h1, h2⟩ := hm u hu.1.1 hu.2
  let e : R →+* CAt σ := ev u
  have he : e.comp ι = (show A →+* CAt σ from ψ u) := hev u hu
  have hp : GlobalTheory.AllWt.ptF (y u) = spMap e ≫ x' := by
    rw [← cancel_mono Z.jQ, h1, Category.assoc, hx', ← Category.assoc, spMap_comp_comp, he]
  refine ⟨?_, fun τ i => ?_⟩
  · show _ = spMap e ≫ x' ≫ _
    rw [← Category.assoc, ← hp]
    exact (pullback.lift_fst _ _ _).symm
  · obtain ⟨w, hw1, hw2, hw3⟩ := h2 τ i
    show _ = spMap (dualMap e) ≫ P.lift _ _ (hw τ i) ≫ _
    rw [← hw2, ← Category.assoc]
    congr 1
    apply P.hom_ext
    · rw [hw3, Category.assoc, P.lift_fst, ← Category.assoc, spMap_comp_comp, dualMap_comp_comp, he]
    · rw [hw1, Category.assoc, P.lift_snd, ← Category.assoc, spMap_dualMap_sq, Category.assoc, hp]

end GlobalTheory.ShFam.BdArc
end
end
