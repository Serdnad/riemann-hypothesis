module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle462
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle415
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle502
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle503
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharpoly
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle276
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypesIdempotentCoefficients
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle289
import Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle205
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsWeilOnOfCoord
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle322
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle312
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle327
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle196
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030

@[expose] public section

section

noncomputable section

open GlobalTheory.Mem.R3.Tr Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe

theorem of_heq_cast {α β : Sort _} {y : β} {x : α} (P : α → Prop) (h : HEq y x) (hx : P x) :
    P (cast (type_eq_of_heq h) y) := by
  cases h
  exact hx



theorem sAtL_exists_ofDiv : ∀ (B : Base) (C : Cols B) (a : Late B C) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] (R : RealDat a.D A Ks) (F : Face a.D A) (F0 : ∀ u, Forms0 a.D u) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (s : SAt R F eE F0) (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ) (F₁ : ∀ u, Forms0 (reL a (New.ofDiv a.D N hh)).D u), SameL a (New.ofDiv a.D N hh) F0 F₁ → ∃ s' : SAtL a (New.ofDiv a.D N hh) R F eE F₁, SAtL.pt a (New.ofDiv a.D N hh) s' = tL a (New.ofDiv a.D N hh) s.t := by
  intro B C a G' _ _ Pl0 T A Ks _ _ iK R F F0 eE s N hh F₁ hS
  have hF : FinX (reY (New.ofDiv a.D N hh) s.P.Y) := finX_reY a.D (New.ofDiv a.D N hh) s.P.X s.P.Y s.P.fin
  have h : SameForms0LevelsAndValues (New.ofDiv a.D N hh) F0 ((by with_unfolding_all exact (F₁ :))) := hS
  obtain ⟨S', hj⟩ := SRest.exists_re_ofDiv N hh s.S h hF
  have hsee := mvSee a (New.ofDiv a.D N hh) R F s.P.X s.P.inst s.t s.see
  have hev := mvEv_holds a (New.ofDiv a.D N hh) R F s.P.X s.P.inst s.P.G s.t s.c s.ev
  have hrow := mvRowJ a (New.ofDiv a.D N hh) R s.P.X s.P.inst s.P.G s.t eE s.S.j s.rowJ
  letI := alg (reL a (New.ofDiv a.D N hh)) iK
  have hrow' := of_heq_cast (fun j : a.D.what₂.EE ≃ₗᵢ[ℂ] EEC s.P.X s.P.G =>
      RowJ (real (reL a (New.ofDiv a.D N hh)) R) (eL a (New.ofDiv a.D N hh) R eE) (XL a (New.ofDiv a.D N hh) s.P.X)
        (hL a (New.ofDiv a.D N hh) s.P.inst) (gdL a (New.ofDiv a.D N hh) s.P.G) (tL a (New.ofDiv a.D N hh) s.t)
        (jL a (New.ofDiv a.D N hh) j)) hj hrow
  let s' : SAt (real (reL a (New.ofDiv a.D N hh)) R) (face (reL a (New.ofDiv a.D N hh)) F) (eL a (New.ofDiv a.D N hh) R eE) F₁ :=
    { P := (by with_unfolding_all exact (s.P.re (New.ofDiv a.D N hh) h hF :))
      S := (by with_unfolding_all exact (S' :))
      t := tL a (New.ofDiv a.D N hh) s.t
      c := s.c
      c_pos := s.c_pos
      see := (by with_unfolding_all exact (hsee :))
      ev := (by with_unfolding_all exact (hev :))
      rowJ := (by with_unfolding_all exact (hrow' :)) }
  exact ⟨s', (by with_unfolding_all exact (Eq.refl (tL a (New.ofDiv a.D N hh) s.t) :))⟩

end GlobalTheory.Mem.SRe

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.liftsCompatible_otherLaterStages_of_sameChoices : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → ∀ (Φ : Type) (rep : Φ → _) (Mt : C.Tup → ℕ → Hs) (l : LfD B.O (B.embLL.comp B.OtoLL) C.Tup Φ Mt) jL (t : LfT y F rep (Mt := Mt) jL l) jL', HEq jL' jL → ∃ t' : @LfT b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) Φ ((by with_unfolding_all exact (rep :))) Mt jL' l, letI := alg b iK; HEq t'.eW t.eW ∧ HEq t'.jMt t.jMt := by
  first | exact @GlobalTheory.Mem.R3.Rw.lfT_of_same | exact GlobalTheory.Mem.R3.Rw.lfT_of_same | (intros; apply GlobalTheory.Mem.R3.Rw.lfT_of_same <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Bare

open GlobalTheory.MemN GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.Mem.TypePl Polynomial

def cenPull {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    Subalgebra.center ℂ (MonoidAlgebra ℂ H) →ₐ[ℂ] Subalgebra.center ℂ (MonoidAlgebra ℂ G) :=
  ((MonoidAlgebra.domCongr ℂ ℂ e.symm : MonoidAlgebra ℂ H →ₐ[ℂ] MonoidAlgebra ℂ G).comp
    (Subalgebra.center ℂ (MonoidAlgebra ℂ H)).val).codRestrict _ fun z => by
      rw [Subalgebra.mem_center_iff]
      intro b
      obtain ⟨c, rfl⟩ := (MonoidAlgebra.domCongr ℂ ℂ e.symm).surjective b
      change _ * MonoidAlgebra.domCongr ℂ ℂ e.symm z = MonoidAlgebra.domCongr ℂ ℂ e.symm z * _
      rw [← map_mul, ← map_mul, Subalgebra.mem_center_iff.1 z.2 c]

theorem coeff_cenPull {G H : Type} [Group G] [Group H] (e : G ≃* H) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ H)) (g : G) :
    (cenPull e z : MonoidAlgebra ℂ G).coeff g = (z : MonoidAlgebra ℂ H).coeff (e g) :=
  MonoidAlgebra.coeff_domCongr (R := ℂ) e.symm (z : MonoidAlgebra ℂ H) g

theorem cenPull_eq {G H : Type} [Group G] [Group H] (e : G ≃* H) {z : Subalgebra.center ℂ (MonoidAlgebra ℂ H)}
    {z' : Subalgebra.center ℂ (MonoidAlgebra ℂ G)}
    (h : ∀ g, (z' : MonoidAlgebra ℂ G).coeff g = (z : MonoidAlgebra ℂ H).coeff (e g)) : cenPull e z = z' := by
  apply Subtype.ext
  ext g
  rw [coeff_cenPull, h]

attribute [local instance] GlobalTheory.Mem.Top.factType



def reser {R : Ranks} {H : Host R} {what₂ rows' : Rows.Data R} {N : NData R H what₂} {N' : NData R H rows'} {A : NAut N} {A' : NAut N'}
    (T : NTypes A) (T' : NTypes A')
    (a : ∀ μ, Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) →ₐ[ℂ] Module.End ℂ (what₂.Amb μ))
    (b : ∀ μ j, Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) →ₐ[ℂ] Module.End ℂ (what₂.Mt μ j)) : NTypes A :=
  { T with
    eSer := T'.eSer
    eSer_idem := T'.eSer_idem
    eSer_central := T'.eSer_central
    eSer_orth := T'.eSer_orth
    eSer_zero := T'.eSer_zero
    eSer_sum := T'.eSer_sum
    cenAmb := a
    cenMt := b }

theorem goodElement_mem_center_groupAlgebra {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (T : NTypes A) :
    T.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) := by
  haveI : ∀ k, NeZero (H.g k) := fun k => ⟨(H.g_prime k).ne_zero⟩
  exact (TypesInhab.good_sum (I := Σ k : Fin 2, N.PlG k) (P := fun kv => Fin R.r → ZMod (H.g kv.1))
    (fun kv p => T.eSer kv.1 (Formalism.CyclotomicNorms.monicOf p))
    (fun a => T.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))) T.e0 (fun g => rfl)
    (fun _ _ => T.eSer_idem _ _) (fun _ _ => T.eSer_central _ _)
    (fun _ p q hpq => T.eSer_orth _ _ _ fun h => hpq (funext fun i => by
      rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt p i, h, Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]))).1

theorem exists_nStage_act {B : Base} {C C₀ : Cols B} {W₀ : RowsRest B C₀} (N₀ : NStage B C₀ W₀) {f : Fr B.toPre}
    (h₀ : GrpTrue N₀ f) (W : RowsRest B C) (hsha : ShaOK B.toPre W.shaLen) (heta : ∀ j w, W.etaJ j w = 0)
    {G : Type} [Group G] (e₀ : G ≃* G0g N₀.nd)
    (a : ∀ μ, Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Module.End ℂ (W.Amb μ))
    (b : ∀ μ j, Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Module.End ℂ (W.Mt μ j))
    (ha : ∀ z : Subalgebra.center ℂ (MonoidAlgebra ℂ G),
      (∀ g, (z : MonoidAlgebra ℂ G).coeff g = N₀.ntypes.e0.coeff (e₀ g)) → (∀ μ, W.eOp μ = a μ z) ∧ ∀ μ j, W.eMt μ j = b μ j z) :
    ∃ N : NStage B C W, IsEmpty N.nd.Loc ∧ GrpTrue N f ∧
      (∀ μ z, N.ntypes.cenAmb μ z = a μ (cenPull (e₀.trans (grpEquiv N₀.naut N.naut)) z)) ∧
      ∀ μ j z, N.ntypes.cenMt μ j z = b μ j (cenPull (e₀.trans (grpEquiv N₀.naut N.naut)) z) := by
  obtain ⟨ldat, hsha⟩ := hsha
  let nd := trueLayer B C W f.W ldat hsha
  have hE : IsEmpty nd.Loc := ⟨fun i : Empty => i.elim⟩
  let A : NAut nd := GaloisStage.nAut nd (fun k v => above f.P (nd.g_split k) v)
    (fun k v => div_over f.P (above_div _ _ v)) (fun k => above_injective f.P (nd.g_split k))
    (fun k v v' => not_isConjPl f.P (nd.g_split k) (above_div _ _ v) (above_div _ _ v'))
  have hl : ∀ k w (p : A.LP w), A.items₂ k w p = (X - 1) ^ A.lpDim p := fun _ _ _ => rfl
  have hi : ∀ w (p : A.LP w) σ, A.inePol p σ = (X - 1) ^ A.lpDim p := fun _ _ _ => rfl
  choose tg htg using fun (k : Fin 2) (v : nd.PlG k) =>
    GlobalTheory.TameInertiaGen.exists_tameGenAt B.host.E nd.Om (A.plGw k v) (nd.plOm.1 (A.plGw k v)) (nd.plOm.2 _)
  choose s hs using fun k : Fin 2 => SerInhab.exists_isSer B.R.r (B.host.g k) B.toPre.restRowsFiniteGroupCard (B.host.g_prime k)
    B.toPre.restRowsFiniteGroupCard_pos ((dvd_pow_self _ (GaloisStage.f_pos B.R).ne').trans
      (Finset.dvd_prod_of_mem (fun k : Fin 2 => (Nat.card (GL (Fin B.R.r) (ZMod (B.host.g k)))) ^ B.R.f)
        (Finset.mem_univ k)))
  obtain ⟨T₀⟩ : Nonempty (NTypes A) := ⟨TypesInhab.types0 hl hi B.g_cond B.BB_disj tg htg s hs⟩
  obtain ⟨L⟩ := locStage_inhabited
  obtain ⟨ω, -⟩ := TypesInhab.exists_char (A := MonoidAlgebra ℂ (G0g nd)) 0 one_ne_zero (by simp)
  let eR : G ≃* G0g nd := e₀.trans (grpEquiv N₀.naut A)
  let T : NTypes A := reser (retype T₀ hl hi (fun k => labDat (B.host.g k)) ω) N₀.ntypes
    (fun μ => (a μ).comp (cenPull eR)) (fun μ j => (b μ j).comp (cenPull eR))
  have hT : TypesTrue T f.P f.W :=
    ⟨fun k v => above_div f.P (nd.g_split k) v, fun _ => rfl, fun _ _ _ => rfl, fun k p => h₀.ser k p⟩
  have hco : ∀ g, T.e0.coeff (grpEquiv N₀.naut A g) = N₀.ntypes.e0.coeff g := TypesTrue.typeIdempotent_coeff_across_layers h₀ hT
  have hc : T.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g nd)) := goodElement_mem_center_groupAlgebra T
  have hz := ha (cenPull eR ⟨T.e0, hc⟩) fun g => (coeff_cenPull eR _ g).trans (hco (e₀ g))
  have htie : T.IdempotentMatchesAction := by
    refine ⟨fun μ => ?_, fun μ j => ?_⟩
    · rw [NTypes.onAmb, dite_eq_left hc]
      exact hz.1 μ
    · rw [NTypes.onMt, dite_eq_left hc]
      exact hz.2 μ j
  have hy : ∀ x, ∃ y : ↥B.LL0, B.embLL (y : B.LL) = T.e0.coeff x := fun x => by
    obtain ⟨g, rfl⟩ := (grpEquiv N₀.naut A).surjective x
    exact ⟨_, (N₀.nStage_trivialCharacter_coeff_eq g).trans (hco g).symm⟩
  choose e hee using hy
  let tw := GaloisStage.nTw B.LL0 nd
  have hT' : IsEmpty tw.Tw := ⟨fun i : Empty => i.elim⟩
  obtain ⟨Y, hY, ⟨th⟩⟩ := exists_nexp_nth_of_isEmpty B C W nd tw hT' e
  exact ⟨{
    toLocStage := L
    nd := nd
    ntw := tw
    naut := A
    nbc := GaloisStage.nBC A
    nexp := Y
    ntypes := T
    nStage_trivialCharacter_compat := htie
    nStage_trivialCharacter_coeff_eq := fun g => by rw [hY]; exact hee g
    nth := th
    nbr := fun i => hE.elim i
    nbr_ind := fun i => hE.elim i
    self_good := fun i => hE.elim i
    ntwbr := fun i => hT'.elim i
    ntwbr_ind := fun i => hT'.elim i
    loc_tie := fun i => hE.elim i
    bc_tie := fun i => hE.elim i
    rbar_tie := fun i => hE.elim i
    mtpar_tie := fun i => hE.elim i
    Z_tie := fun i => hE.elim i
    Zgood_tie := fun i => hE.elim i
    etaJ_tie := fun j w _ _ => (heta j w).trans (Finset.sum_eq_zero fun i _ => hE.elim i).symm },
    hE, hT, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem read_unique {E : Type} [Field E] [NumberField E] {S : Finset (Pl E)} {r p : ℕ} (g : ∀ P : S, GL (Fin r) (kP P.1))
    {S' : Finset (Pl E)} (g' : ∀ P : S', GL (Fin r) (kP P.1))
    (hg : ∀ (P : Pl E) (h : P ∈ S) (h' : P ∈ S'), g' ⟨P, h'⟩ = g ⟨P, h⟩) (P : S) (P' : S') (hP : P.1 = P'.1)
    (i : ZMod p ≃+* kP P.1) (i' : ZMod p ≃+* kP P'.1) {x x' : GL (Fin r) (ZMod p)}
    (h : g P = Formalism.UG.bc (i : ZMod p →+* kP P.1) x) (h' : g' P' = Formalism.UG.bc (i' : ZMod p →+* kP P'.1) x') : x = x' := by
  obtain ⟨P, hS⟩ := P
  obtain ⟨P', hS'⟩ := P'
  dsimp only at hP
  subst hP
  rw [hg P hS hS', h, Subsingleton.elim (i' : ZMod p →+* kP P) (i : ZMod p →+* kP P)] at h'
  ext a b
  exact i.injective (congrArg (fun u : GL (Fin r) (kP P) => (u : Matrix (Fin r) (Fin r) (kP P)) a b) h')

theorem e_eq_act {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] {O : Type} [CommRing O] {φ : O →+* ℂ}
    {σ : K →+* ℂ} {m : Mat1 K G} {s : Sp1 O φ G} (t : Tie1 σ m s) {e : MonoidAlgebra K G} (h : m.Laws σ e)
    (z : Subalgebra.center ℂ (MonoidAlgebra ℂ G)) (hz : ∀ g, σ (e.coeff g) = (z : MonoidAlgebra ℂ G).coeff g) :
    s.e = s.act z := by
  refine LinearMap.ext_on_range t.forms.span fun i => ?_
  rw [t.forms.op_eq, t.cen z e hz, h.E_eq]

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

theorem exists_bare {K : Ctx} (P : Pre2 K w) :
    ∃ N : NStage B w.C (P.q.W (fun _ _ => 0) fun _ _ => le_rfl), IsEmpty N.nd.Loc ∧ GrpTrue N f ∧
      ∀ V S G, GrpAt (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.I ∧
        ∀ eR, StdIso (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.px eR → CenIs P.q.p N eR := by
  letI := P.z.alg
  let e₀ : Gc B w.px ≃* G0g P.Z₀.N.nd := P.z.R.eG.trans P.z.cG
  have hgood : ∀ g, B.embLL ((idemOf P.z.Xg).coeff g) = P.Z₀.N.ntypes.e0.coeff (e₀ g) := P.z.good.2
  obtain ⟨N, hE, hN, hA, hM⟩ := exists_nStage_act P.Z₀.N P.grp (P.q.W (fun _ _ => 0) fun _ _ => le_rfl) P.q.sha
    (fun _ _ => rfl) e₀ (fun μ => (P.q.p.sA true μ).act) (fun μ j => (P.q.p.sL μ j).act) fun z hz =>
      ⟨fun μ => e_eq_act (P.q.t.tA true μ) (P.q.t.lawsA true μ) z fun g => (hgood g).trans (hz g).symm,
       fun μ j => e_eq_act (P.q.p.tL μ j) (P.q.t.lawsL μ j) z fun g => (hgood g).trans (hz g).symm⟩
  have hpl : ∀ k v, P.Z₀.N.naut.plGw k ((plEquiv P.Z₀.N.naut N.naut k).symm v) = N.naut.plGw k v := fun k v => by
    rw [← TypesTrue.plGw_plEquiv P.grp hN, Equiv.apply_symm_apply]
  refine ⟨N, hE, hN, fun V S G => ⟨?_, fun eR hR => ?_⟩⟩
  · obtain ⟨plg, hp⟩ := P.grpAt.pl
    obtain ⟨hc, hi⟩ := GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent
      (w.st (RowPk.Over.Z (q := P.q) ⟨_, _, V, S, N, G⟩)).toD7
    refine ⟨⟨(Equiv.sigmaCongrRight fun k => (plEquiv P.Z₀.N.naut N.naut k).symm).trans plg, fun kv => ?_⟩, hi, hc⟩
    exact ⟨(hp ⟨kv.1, _⟩).1.trans (hpl kv.1 kv.2), (hp ⟨kv.1, _⟩).2⟩
  · have he : e₀.trans (grpEquiv P.Z₀.N.naut N.naut) = eR := by
      obtain ⟨plg, iso, h1, h2⟩ := hR
      obtain ⟨plg₀, iso₀, k1, -, -, k2⟩ := P.z.pins.keep.grp
      refine MulEquiv.ext fun g => funext fun kv => ?_
      exact (read_unique g (P.z.R.eG g) (P.z.idG g) (plg kv) (plg₀ ⟨kv.1, (plEquiv P.Z₀.N.naut N.naut kv.1).symm kv.2⟩)
        ((h1 kv).trans ((k1 ⟨kv.1, _⟩).trans (hpl kv.1 kv.2)).symm) (iso kv) (iso₀ ⟨kv.1, _⟩) (h2 g kv) (k2 g ⟨kv.1, _⟩)).symm
    subst he
    exact ⟨fun μ z z' hz x => by rw [hA, cenPull_eq _ hz], fun μ j z z' hz x => by rw [hM, cenPull_eq _ hz]⟩

theorem stepW_bare : StepW (pinAnd HasPk) fun K B f T w => ∀ (P : Pre2 K w), ∃ N : NStage B w.C (P.q.W (fun _ _ => 0) fun _ _ => le_rfl), IsEmpty N.nd.Loc ∧ GrpTrue N f ∧ ∀ V S G, GrpAt (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.I ∧ ∀ eR, StdIso (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.px eR → CenIs P.q.p N eR :=
  StepW.of_all fun _ _ _ _ _ _ _ _ P => exists_bare P

end GlobalTheory.Mem.R3.Rw.Bare

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WeilOriented

theorem exists_isWeilDatumO_of_rank_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (χ χ' : IdC D) (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)), AdmE V W χ χ' → IsWeilOn ψ V W χ χ' om → ∃ omO : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ), IsWeilDatumO ψ V W χ χ' omO ∧ ∀ (p : GA D V × GA D W) (Φ : ThS ψ V W), omO p (fun x => Φ.1 (toTWsmall V W x)) = fun x => (om p Φ).1 (toTWsmall V W x) := by
  intro D ψ hψ V W χ χ' om ha hw
  have hr : V.rank ≤ W.rank := ha.1.le
  obtain ⟨e, hc, hcs, he, hrat, hsm, hheis, hth, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W hr
  let E : (WA V W → ℂ) ≃ₗ[ℂ] (WO V W → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ e.toEquiv
  obtain ⟨omO, hom⟩ := exists_extend (ThS ψ V W) E om
  have hom' : ∀ p (Φ : ThS ψ V W), omO p (fun x => Φ.1 (e x)) = fun x => (om p Φ).1 (e x) := hom
  have hsurj : ∀ f, IsThetaFunO ψ V W f → ∃ Φ : ThS ψ V W, f = fun x => Φ.1 (e x) := fun f hf => by
    have e1 : f = fun x => (fun y => f (e.symm y)) (e x) := by funext x; simp
    refine ⟨⟨fun y => f (e.symm y), mem_ThS.2 ((hth ψ _).1 ?_)⟩, e1⟩
    rw [← e1]; exact hf
  have hTh : ∀ Φ : ThS ψ V W, IsThetaFunO ψ V W fun x => Φ.1 (e x) := fun Φ => (hth ψ _).2 (mem_ThS.1 Φ.2)
  have hact : ∀ g h x, e (actO V W g h x) = actHom V W g h (e x) := fun g h x => by
    rw [he, he]; exact (GlobalTheory.OrientedSmall.bridgeSmall D V W hr).2 g h x
  refine ⟨omO, ⟨hψ, ha.2.1.1, ha.2.2.1.1, ha.2.2.2.1, ha.2.2.2.2, fun p f hf => ?_, fun g h w₀ f hf => ?_,
    fun γ hγ γ' hγ' f hf => ?_, fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_,
    fun ε hε g h hg hh x y hx hy => ?_⟩, fun p Φ => ?_⟩
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    rw [hom']; exact hTh _
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    let Φ' : ThS ψ V W := ⟨Heisenberg₂ ψ V W (e w₀) Φ.1,
      mem_ThS.2 (GlobalTheory.Mem.ThetaClosed.isThetaFun_heis hψ (mem_ThS.1 Φ.2) _)⟩
    rw [hheis, hom', hheis, hact, ← hw.Heisenberg₂ g h (e w₀) Φ Φ' rfl]
    exact hom' _ Φ'
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    rw [hom']
    simp only [map_zero]
    exact hw.aut γ hγ γ' hγ' Φ
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    simp only [hom']
    exact hw.cont Φ (e w)
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    rw [hom']
    obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
    obtain ⟨j1, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D V W
    have : BorelSpace (WA V W) := ⟨rfl⟩
    have : BorelSpace (WO V W) := ⟨rfl⟩
    obtain ⟨ν, hν, hF, hint⟩ := GlobalTheory.exists_isAddHaarMeasure_isAddFundamentalDomain_preimage (WA V W) (WO V W) e.symm hcs
      (by simpa using hc) (ratL V W) (ratL W V) (fun x => by rw [← hrat, e.apply_symm_apply]) μ 𝓕 hμ h𝓕
    refine lintegral_eq_of_integral_eq (ratL W V) hK hcov (hTh _).cont (hTh _).cont (norm_periodic hψ (hTh _))
      (norm_periodic hψ (hTh _)) hμ h𝓕 ?_
    rw [← hint, ← hint]
    simp only [e.apply_symm_apply]
    exact hw.unit ν _ hν hF p Φ
  · obtain ⟨r, hr0, hℓ⟩ := hw.split ε hε g h hg hh x y hx hy
    refine ⟨r, hr0, fun ℓ hinv f hf => ?_⟩
    obtain ⟨Φ, rfl⟩ := hsurj f hf
    have := hℓ (ℓ ∘ₗ E.toLinearMap ∘ₗ (ThS ψ V W).subtype) (fun u hu Ψ Ψ' hΨ => ?_) Φ
    · rw [hom']
      unfold splitFac at this
      rw [if_pos hr] at this
      exact this
    · have hu' : cA D ε • e.symm u = e.symm u := by
        apply e.injective
        rw [hsm, e.apply_symm_apply]
        exact Matrix.ext hu
      have := hinv (e.symm u) (fun i j => congrFun (congrFun hu' i) j) _ (hTh Ψ)
      rw [hheis, e.apply_symm_apply, ← hΨ] at this
      exact this
  · simp only [← he]
    exact hom' p Φ

end GlobalTheory.Mem.WeilOriented
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (ChrEq)
open Formalism.L2.Host (HChar)
open scoped TensorProduct

namespace GlobalTheory.TowerCharRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem chrEq_mul {c c' : (AE D)ˣ →* Circle} {χ χ' : HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ') :
    ChrEq (c * c') (χ * χ') := by
  refine ⟨⟨h.1.1.mul h'.1.1, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]
  · rw [MonoidHom.mul_apply, Circle.coe_mul, h.2 P e he k x hx, h'.2 P e he k x hx, ← Units.val_mul]
    rfl

theorem exists_thetaChrTied (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch)
    (X : ThetaX D) (T : ThetaTied D X) (hR : ChrRead T C Tp.xi) :
    ∃ H : Formalism.L2.Host.ThetaChrTied D C nch Tp X, ∀ c, ChrEq (T.eChr c) (H.eChr c) := by
  obtain ⟨u1, u2, u3⟩ := GlobalTheory.ChrEqUnique.chrEq_unique D
  have hc : ∀ c, IsHeckeChar D (T.eChr c) ∧ ∀ τ, ∃ a, HasInfExp D (T.eChr c) τ a := fun c => by
    have : T.eChr c ∈ Set.range T.eChr := ⟨c, rfl⟩
    rwa [T.eChr_range] at this
  choose e he using fun c => GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D (T.eChr c) (hc c).1
  have hmul : ∀ a b, e (a * b) = e a * e b := fun a b =>
    u1 _ _ _ (he (a * b)) (by rw [map_mul]; exact chrEq_mul (he a) (he b))
  have hinf : ∀ c, (e c).HasInfQ (Formalism.L2.Host.embTau D) (X.infTy c) := fun c =>
    (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ D _ _ _ (he c)).1 (T.infTy c)
  refine ⟨⟨MonoidHom.mk' e hmul, fun a b hab => T.eChr_inj (u2 _ _ _ (he a) ?_), fun χ => ⟨?_, ?_⟩, hinf,
    fun μ j => u1 _ _ _ (he _) (hR.chr μ j), u1 _ _ _ (he _) hR.eta⟩, he⟩
  · have hab' : e a = e b := hab
    rw [hab']
    exact he b
  · rintro ⟨c, rfl⟩
    exact ⟨u3 _ _ (he c), _, hinf c⟩
  · rintro ⟨hu, a, ha⟩
    obtain ⟨c, hcχ⟩ := GlobalTheory.CharTransport.exists_chrEq D χ hu
    have hm : c ∈ Set.range T.eChr := by
      rw [T.eChr_range]
      exact ⟨hcχ.1, fun τ => ⟨a τ, (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ D _ _ _ hcχ).2 ha τ⟩⟩
    obtain ⟨x, rfl⟩ := hm
    exact ⟨x, u1 _ _ _ (he x) hcχ⟩

end GlobalTheory.TowerCharRead

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.OrientedCoord GlobalTheory.Mem.WeilTransport
open scoped TensorProduct

namespace GlobalTheory.Mem.WeilEqRank

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isCoord_coord (S T : HSp D) (hr : S.rank ≤ T.rank) : IsCoord S T S T (coord S T) := {
  cont := continuous_coord S T
  cont' := continuous_coord_symm S T
  sympl := symplOH_eq S T hr
  rat x := by
    constructor
    · rintro ⟨γ, rfl⟩
      exact ⟨(γ * S.gram⁻¹)ᵀ, (coord_ratW S T γ).symm⟩
    · rintro ⟨γ, hγ⟩
      have hγ' : ratW S T γ = coord S T x := hγ
      refine ⟨γᵀ * S.gram, ?_⟩
      change ratW T S _ = x
      rw [← coord_symm_ratW, hγ', AddEquiv.symm_apply_apply]
  inf x := ⟨coord_map_zero S T _ x, fun h => by
    simpa only [AddEquiv.symm_apply_apply] using coord_symm_map_zero S T _ _ h⟩
  fin x := ⟨coord_map_zero S T _ x, fun h => by
    simpa only [AddEquiv.symm_apply_apply] using coord_symm_map_zero S T _ _ h⟩
  part a x h i j := by
    show a * ∑ k, x j k * incA D (S.gram⁻¹ k i) = ∑ k, x j k * incA D (S.gram⁻¹ k i)
    simp only [Finset.mul_sum, ← mul_assoc, h] }

theorem weilOnEqEx_of_weilRepresentation : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ D : D7, WeilOnEqEx D := by
  intro hP D ψ hψ V W χ χ' ⟨hr, h1, h2, h3, h4⟩
  obtain ⟨om, H⟩ := hP D ψ V W χ χ' hψ h1.1 h2.1 h3 h4
  refine exists_isWeilOn_of_coord (isCoord_coord V W hr.le) H (MonoidHom.id _) continuous_id
    (fun g h x => (GlobalTheory.OrientedSmall.bridgeSmall D V W hr.le).2 g h x) (fun _ a _ b => ⟨a, b⟩)
    fun e g h hg hh x y hx hy => ⟨x, y, hg, hh, hx, hy, ?_⟩
  unfold splitFacO splitFac
  rw [if_pos hr.le]

end GlobalTheory.Mem.WeilEqRank

end
end
