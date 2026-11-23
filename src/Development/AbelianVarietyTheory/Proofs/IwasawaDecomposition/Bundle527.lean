module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsBaseLevelLiftReadAtBaseEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle517
import Formalism.LocalToGlobal.Columns.CoefficientsModP.BaseCh
import Formalism.LocalToGlobal.Columns.ColumnsProofs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle284
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle477
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle519
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.LiftRead

theorem read_of_span {L L' : Type} [Field L] [Field L'] (φ : L →+* L') (σ : L →+* ℂ) (σ' : L' →+* ℂ) (hφ : ∀ x, σ' (φ x) = σ x)
    {n n' : ℕ} (hn : n = n') {H H' : Type} (nH : NormedAddCommGroup H) (nH' : NormedAddCommGroup H')
    (iH : InnerProductSpace ℂ H) (iH' : InnerProductSpace ℂ H') (hH : H' = H) (h1 : HEq nH' nH) (h2 : HEq iH' iH)
    (j : (Fin n → L) →ₛₗ[σ] H) (j' : (Fin n' → L') →ₛₗ[σ'] H') (S : Set (Fin n → L)) (hS : Submodule.span L S = ⊤)
    (hj : ∀ y ∈ S, ∃ y' : Fin n' → L', (∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → σ' (y' k') = σ (y k)) ∧ HEq (j' y') (j y))
    (x : Fin n → L) (x' : Fin n' → L') (hx : ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)) :
    HEq (j' x') (j x) := by
  subst hn hH
  cases h1
  cases h2
  have e : x' = fun k => φ (x k) := funext fun k => hx k k rfl
  subst e
  clear hx
  refine heq_of_eq ?_
  have hx : x ∈ Submodule.span L S := hS ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨y', a, b⟩ := hj y hy
    have e : (fun k => φ (y k)) = y' := funext fun k => σ'.injective ((hφ _).trans (a k k rfl).symm)
    rw [e]
    exact eq_of_heq b
  | zero =>
    have e : (fun k => φ ((0 : Fin n → L) k)) = 0 := by funext k; simp
    rw [e, map_zero, map_zero]
  | add y z _ _ hy hz =>
    have e : (fun k => φ ((y + z) k)) = (fun k => φ (y k)) + fun k => φ (z k) := by funext k; simp
    rw [e, map_add (f := _), map_add (f := _), hy, hz]
  | smul a y _ hy =>
    have e : (fun k => φ ((a • y) k)) = φ a • fun k => φ (y k) := by funext k; simp
    rw [e, map_smulₛₗ, map_smulₛₗ, hy, hφ]



theorem hmod_fields {B B' : Base} (q : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt}
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    {S : (w.st Z).toD7.what₂.Tau → SPar} {S' : (w'.st Z').toD7.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel (Wc (w.st Z).toD7 i) S) (M' : Formalism.IndefR.Mult.DSModel (Wc (w'.st Z').toD7 i') S')
    (a : HEq M'.H M.H) (b : HEq M'.nacg M.nacg) (c : HEq M'.ips M.ips) (d : HEq M'.σ M.σ) (l : HEq M'.lam M.lam) (e : HEq M'.ε M.ε)
    (g : HEq M'.fr M.fr) (X : HMod (Formalism.IndefR.Mult.MMap M)) (X' : HMod (Formalism.IndefR.Mult.MMap M')) (hX : HEq X' X) :
    X'.H = X.H ∧ HEq X'.nH X.nH ∧ HEq X'.iH X.iH := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  cases M
  cases M'
  dsimp only at a b c d l e g
  cases a; cases b; cases c; cases d; cases l; cases e; cases g
  have e' : X' = X := eq_of_heq hX
  subst e'
  exact ⟨rfl, HEq.rfl, HEq.rfl⟩



theorem read_extN {B B' : Base} (q : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok}
    {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl} {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'}
    (hE : ExtN z z') (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j')
    (φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL)
    (hφ : ∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x)
    (x : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (x' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)
    (hx : ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)) :
    HEq ((z'.R.FW j').j (w'.st Z').toD7.what₂.embLL x') ((z.R.FW j).j (w.st Z).toD7.what₂.embLL x) := by
  have hk := hE.κ j j' hj
  have hc : ↥(z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n) =
      ↥(z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n) := (by with_unfolding_all exact ((cusp_type_congr (P₁ := B.toPre) (P₂ := B'.toPre) q (congrArg (· + 1) hj) hk.2.2
      hE.H hE.l hE.c hE.Dw hE.Xo hE.U hk.1 hk.2.1) :))
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := congrArg (fun P : Pre => P.R.m) q
  have hn : z.R.nW j = z'.R.nW j' := GlobalTheory.Mem.R3.LiftForms.nat_eq_of_heq hm hE.nW j j' hj
  obtain ⟨a, b, c, d, l, e, g, -, hW, -, hr⟩ := hE.MW j j' hj
  obtain ⟨h0, h1, h2⟩ := hmod_fields q j j' hj _ _ a b c d l e g _ _ hW
  obtain ⟨m, bs, hb, -, -, -, hsp⟩ := z.geo.fw.ks j
  refine read_of_span φ _ _ hφ hn _ _ _ _ h0 h1 h2 _ _ (Set.range bs) hsp ?_ x x' hx
  rintro _ ⟨i, rfl⟩
  obtain ⟨u, hu⟩ := (z.geo.fw.e j).surjective ⟨bs i, hb i⟩
  have hu' : bs i = (z.geo.fw.e j u : (z.R.FW j).WK).1 := (congrArg Subtype.val hu).symm
  rw [hu']
  exact ⟨(z'.geo.fw.e j' (cast hc.symm u) : (z'.R.FW j').WK).1, hE.forms j j' hj u _ (cast_heq _ _), hr u _ (cast_heq _ _)⟩



theorem read_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (x : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (x' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL), (∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)) → HEq ((z'.R.FW j').j (w'.st Z').toD7.what₂.embLL x') ((z.R.FW j).j (w.st Z).toD7.what₂.embLL x)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ _ Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ hExt j j' hj φ hφ x x' hx => ?_
  exact read_extN hE.1 hExt j j' hj φ hφ x x' hx

end GlobalTheory.Mem.R3.LiftRead

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.DefLatBC

theorem csum_res_symm {K : Type} [Field K] [NumberField K] [StarRing K] (S : Formalism.L2.Col.GSD K) (h : S.Ok)
    (f : (S.toCSD h).Forms) (c : S.Cl) :
    (((S.res h).symm f : S.EqFun) : S.D → S.V) (Quotient.out c) = (f.1 : S.Cl → S.V) c :=
  congrArg (fun u : (S.toCSD h).Forms => (u.1 : S.Cl → S.V) c) ((S.res h).apply_symm_apply f)

theorem csum_round_bc (X : Formalism.L2.Col.Fields) {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)
    (hstar : ∀ x, ι (star x) = star (ι x))
    (e : X.Tau → X.E →+* L) (he : ∀ τ, ι.comp (X.emb τ) = e τ) {n : ℕ} (lam : X.Tau → DomWeight n)
    {SG₁ SG₂ : Finset (HeightOneSpectrum (𝓞 X.E))} (hS : SG₂ = SG₁)
    (Λ₁ : Formalism.L2.Col.LevFam X.E X.K n SG₁) (Λ₂ : Formalism.L2.Col.LevFam X.E L n SG₂)
    (hH : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), (Λ₂ ⟨w.1, hw⟩).H = (Λ₁ w).H)
    (c₁ : X.K →+* ℂ) (c₂ : L →+* ℂ) (hc : ∀ x, c₂ (ι x) = c₁ x)
    (h₁ : (Formalism.L2.Col.formGSD (Formalism.L2.Col.roundPk X lam fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₁) => d.1.N) Λ₁).Ok)
    (h₂ : (Formalism.L2.Col.formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields))
      (Formalism.L2.Col.roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields) lam
        fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₂) => d.1.N) Λ₂).Ok)
    (f g : (Formalism.L2.Col.GSD.toCSD _ h₁).Forms) (f' g' : (Formalism.L2.Col.GSD.toCSD _ h₂).Forms)
    (hf : ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map c₂ (((Formalism.L2.Col.GSD.res _ h₂).symm f').1 d₂).1)
      (MvPolynomial.map c₁ (((Formalism.L2.Col.GSD.res _ h₁).symm f).1 d₁).1))
    (hg : ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map c₂ (((Formalism.L2.Col.GSD.res _ h₂).symm g').1 d₂).1)
      (MvPolynomial.map c₁ (((Formalism.L2.Col.GSD.res _ h₁).symm g).1 d₁).1)) :
    (Formalism.L2.Col.GSD.toCSD _ h₂).csum f'.1 g'.1 = ι ((Formalism.L2.Col.GSD.toCSD _ h₁).csum f.1 g.1) := by
  subst hS
  have he' : e = fun τ => ι.comp (X.emb τ) := funext fun τ => (he τ).symm
  subst he'
  obtain ⟨H₂, l₂, rfl⟩ : ∃ (H₂ : ∀ w : ↥SG₂, Subgroup (GL (Fin n) (𝓞 X.E ⧸ w.1.asIdeal))) (l₂ : ∀ w, ↥(H₂ w) →* Lˣ),
      Λ₂ = fun w => ⟨H₂ w, l₂ w⟩ := ⟨fun w => (Λ₂ w).H, fun w => (Λ₂ w).lam, rfl⟩
  have hH' : H₂ = fun w => (Λ₁ w).H := funext fun w => hH w w.2
  subst hH'
  have key : ∀ (p : Pol X.K X.Tau n) (q : Pol L X.Tau n), HEq (MvPolynomial.map c₂ q) (MvPolynomial.map c₁ p) →
      q = MvPolynomial.map ι p := by
    intro p q h
    apply MvPolynomial.map_injective c₂ c₂.injective
    rw [eq_of_heq h, MvPolynomial.map_map, show c₂.comp ι = c₁ from RingHom.ext hc]
  unfold CSD.csum

  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, map_inv₀, map_natCast]
  have a1 := key _ _ (hf (Quotient.out c) (Quotient.out c) HEq.rfl)
  have a2 := key _ _ (hg (Quotient.out c) (Quotient.out c) HEq.rfl)
  have b1 := csum_res_symm _ h₁ f c
  have b2 := csum_res_symm _ h₁ g c
  have b3 := csum_res_symm _ h₂ f' c
  have b4 := csum_res_symm _ h₂ g' c
  have a1' : (f'.1 c).1 = MvPolynomial.map ι (f.1 c).1 :=
    (congrArg Subtype.val b3).symm.trans (a1.trans (congrArg (fun v => MvPolynomial.map ι (Subtype.val v)) b1))
  have a2' : (g'.1 c).1 = MvPolynomial.map ι (g.1 c).1 :=
    (congrArg Subtype.val b4).symm.trans (a2.trans (congrArg (fun v => MvPolynomial.map ι (Subtype.val v)) b2))
  have hp := (baseChangePairingV_holds X.E X.K L ι hstar X.Tau n X.emb lam 1 (f.1 c) (g.1 c) (f'.1 c) (g'.1 c) a1' a2').2
  exact congrArg₂ (· * ·) rfl hp

theorem glue_inv_H_of_empty {E K L : Type} [Field E] [NumberField E] [Field K] [Field L] {n : ℕ}
    {SG₁ Q₁ SG₂ Q₂ : Finset (HeightOneSpectrum (𝓞 E))} (hQ₁ : Q₁ = ∅) (hQ₂ : Q₂ = ∅)
    (A₁ : Formalism.L2.Col.LevFam E K n SG₁) (B₁ : Formalism.L2.Col.LevFam E K n Q₁)
    (A₂ : Formalism.L2.Col.LevFam E L n SG₂) (B₂ : Formalism.L2.Col.LevFam E L n Q₂)
    (hA : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), (A₂ ⟨w.1, hw⟩).H = (A₁ w).H) :
    ∀ (w : ↥(Formalism.L2.Col.uSG SG₁ Q₁)) (hw : w.1 ∈ Formalism.L2.Col.uSG SG₂ Q₂),
      ((A₂.glue B₂).inv ⟨w.1, hw⟩).H = ((A₁.glue B₁).inv w).H := by
  intro w hw
  have h1 : w.1 ∈ SG₁ := by
    have := w.2
    simp only [Formalism.L2.Col.uSG, hQ₁, Finset.union_empty] at this
    exact this
  have h2 : w.1 ∈ SG₂ := by
    have := hw
    simp only [Formalism.L2.Col.uSG, hQ₂, Finset.union_empty] at this
    exact this
  show ((A₂.glue B₂) ⟨w.1, hw⟩).H = ((A₁.glue B₁) w).H
  rw [Formalism.L2.Col.LevFam.glue_of_mem _ _ _ h2, Formalism.L2.Col.LevFam.glue_of_mem _ _ _ h1]
  exact hA ⟨w.1, h1⟩ h2



theorem csum_refTuple {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂}
    (w₁ : ColW B₁ f₁ T₁) (w₂ : ColW B₂ f₂ T₂) (W₁ : Set B₁.places.Pl) (W₂ : Set B₂.places.Pl)
    (hpre : B₂.toPre = B₁.toPre) (hp : HEq w₂.px w₁.px) (j₁ j₂ : ℕ) (hj : j₁ = j₂)
    (ι : B₁.LL →+* B₂.LL) (hι : ∀ x, B₂.embLL (ι x) = B₁.embLL x)
    (h₁ : (Formalism.L2.Col.mtKGSD (Pr := B₁.primes w₁.px) B₁.wts w₁.I.Ch w₁.I.sel (mu0F (X := B₁.fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).Ok) (h₂ : (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₂).Ok)
    (f g : (Formalism.L2.Col.GSD.toCSD _ h₁).Forms) (f' g' : (Formalism.L2.Col.GSD.toCSD _ h₂).Forms)
    (hf : ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map (B₂.embLL : B₂.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₂).symm f').1 d₂).1)
      (MvPolynomial.map (B₁.embLL : B₁.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₁).symm f).1 d₁).1))
    (hg : ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map (B₂.embLL : B₂.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₂).symm g').1 d₂).1)
      (MvPolynomial.map (B₁.embLL : B₁.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₁).symm g).1 d₁).1)) :
    (Formalism.L2.Col.GSD.toCSD _ h₂).csum f'.1 g'.1 = ι ((Formalism.L2.Col.GSD.toCSD _ h₁).csum f.1 g.1) := by
  subst hj
  have hstar : ∀ x, ι (star x) = star (ι x) := by
    intro x
    apply B₂.embLL.injective
    rw [hι, B₂.starLL_cx, hι, B₁.starLL_cx]
  cases B₁ with | mk P₁ =>
  cases B₂ with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  have hpx : w₂.px = w₁.px := eq_of_heq hp
  refine csum_round_bc (baseOfColW w₁).fields ι hstar (baseOfColW w₂).tauLL ?_ ((baseOfColW w₁).wts.lamV j₁) ?_
    (Formalism.L2.Col.mtTyKK w₁.I.Ch w₁.I.sel (mu0F (X := (baseOfColW w₁).fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).inv
    (Formalism.L2.Col.mtTyKK w₂.I.Ch w₂.I.sel (mu0F (X := (baseOfColW w₂).fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₁).inv
    ?_ (baseOfColW w₁).embLL
    (baseOfColW w₂).embLL hι h₁ h₂ f g f' g' hf hg
  · intro τ
    ext x
    apply (baseOfColW w₂).embLL.injective
    have h1 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w₁) τ)
    have h2 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w₂) τ)
    simp only [Formalism.L2.Col.Fields.embC, RingHom.comp_apply] at h1 h2
    rw [RingHom.comp_apply, hι]
    exact h1.trans h2.symm
  · refine (rowLevelPrimes_colTuples_eq_vGs w₂ W₂).trans (Eq.trans ?_ (rowLevelPrimes_colTuples_eq_vGs w₁ W₁).symm)
    rw [hpx]
    rfl
  · exact glue_inv_H_of_empty (twistRamifiedPrimes_empty_colTuples w₁ W₁) (twistRamifiedPrimes_empty_colTuples w₂ W₂) _ _ _ _ fun w hw => rfl



theorem csum_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) → (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) → ∀ f g : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms, ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.csum (L f : ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Cl → ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.V) (L g) = φ (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.csum f g)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ hp Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' hj φ hφ L _ hL a b => ?_
  exact csum_refTuple w w' Wt {v | B'.places.resChar v ∈ T'.pl} hE.1 hp ((j : ℕ) + 1) ((j' : ℕ) + 1) (by rw [hj]) φ hφ
    (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))
    (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))
    a b (L a) (L b) (hL a) (hL b)

end GlobalTheory.Mem.R3.DefLatBC
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.DefLatBC.LiftExt


open _root_.Formalism.L2.Col in

private theorem liftHom_reidx (X : Fields) {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)
    (e : X.Tau → X.E →+* L) (he : ∀ τ, ι.comp (X.emb τ) = e τ) {n : ℕ} (lam₁ lam₂ : X.Tau → DomWeight n)
    (hl : lam₂ = lam₁) {SG₁ SG₂ : Finset (HeightOneSpectrum (𝓞 X.E))} (hS : SG₂ = SG₁)
    (Λ₁ : LevFam X.E X.K n SG₁) (Λ₂ : LevFam X.E L n SG₂)
    (hΛ : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), Λ₂ ⟨w.1, hw⟩ = (Λ₁ w).coefMap ι)
    (c₁ : X.K →+* ℂ) (c₂ : L →+* ℂ) (hc : ∀ x, c₂ (ι x) = c₁ x) :
    ∃ Lf : (formGSD (roundPk X lam₁ fun d : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₁) => d.1.N) Λ₁).EqFun →+
      (formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Fields))
        (roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Fields) lam₂
          fun d : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₂) => d.1.N) Λ₂).EqFun,
      (∀ (a : X.K) ψ, Lf (a • ψ) = ι a • Lf ψ) ∧
      ∀ ψ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map c₂ ((Lf ψ).1 d₂).1) (MvPolynomial.map c₁ (ψ.1 d₁).1) := by
  subst lam₂
  subst SG₂
  have hΛ' : Λ₂ = Λ₁.coefMap ι := funext fun w => hΛ w w.2
  subst hΛ'
  have hmem : ∀ ψ : (formGSD (roundPk X lam₁ fun d : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₁) => d.1.N) Λ₁).EqFun,
      (fun d => hfsJ ι lam₁ (ψ.1 d)) ∈ (formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Fields))
        (roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Fields) lam₁
          fun d : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₁) => d.1.N) (Λ₁.coefMap ι)).EqFun := by
    intro ψ
    obtain ⟨φ₂, h⟩ := GlobalTheory.Mem.R3.Tr.levelFamily_coefficientChange_liftRound X ι e he lam₁ Λ₁ (Λ₁.coefMap ι) (fun w => rfl)
      (fun w h₁ h₂ hh => by
        have : h₁ = h₂ := Subtype.ext hh
        subst this
        rfl) ψ
    have : (fun d => hfsJ ι lam₁ (ψ.1 d)) = φ₂.1 := funext fun d => Subtype.ext (h d).symm
    rw [this]
    exact φ₂.2
  refine ⟨{ toFun := fun ψ => ⟨fun d => hfsJ ι lam₁ (ψ.1 d), hmem ψ⟩, map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩
  · apply Subtype.ext
    funext d
    exact map_zero _
  · intro ψ χ
    apply Subtype.ext
    funext d
    exact map_add _ _ _
  · intro a ψ
    apply Subtype.ext
    funext d
    exact hfsJ_smul ι lam₁ a (ψ.1 d)
  · intro ψ d₁ d₂ hd
    cases hd
    apply heq_of_eq
    show MvPolynomial.map c₂ (MvPolynomial.map ι (ψ.1 d₁).1) = _
    rw [MvPolynomial.map_map]
    have hc' : c₂.comp ι = c₁ := RingHom.ext hc
    rw [hc']


open _root_.Formalism.L2.Col in
private theorem formsLift_of_eqFunLift {K₁ K₂ : Type} [Field K₁] [NumberField K₁] [StarRing K₁] [Field K₂] [NumberField K₂] [StarRing K₂]
    (ι : K₁ →+* K₂) (S₁ : GSD K₁) (S₂ : GSD K₂) (h₁ : S₁.Ok) (h₂ : S₂.Ok) (Lf : S₁.EqFun →+ S₂.EqFun)
    (hLf : ∀ (a : K₁) ψ, Lf (a • ψ) = ι a • Lf ψ) :
    ∃ L : (S₁.toCSD h₁).Forms →+ (S₂.toCSD h₂).Forms, (∀ (a : K₁) f, L (a • f) = ι a • L f) ∧
      ∀ f, (S₂.res h₂).symm (L f) = Lf ((S₁.res h₁).symm f) := by
  refine ⟨(S₂.res h₂).toLinearMap.toAddMonoidHom.comp (Lf.comp (S₁.res h₁).symm.toLinearMap.toAddMonoidHom),
    fun a f => ?_, fun f => ?_⟩
  · show S₂.res h₂ (Lf ((S₁.res h₁).symm (a • f))) = ι a • S₂.res h₂ (Lf ((S₁.res h₁).symm f))
    rw [map_smul, hLf, map_smul]
  · show (S₂.res h₂).symm (S₂.res h₂ (Lf ((S₁.res h₁).symm f))) = _
    exact LinearEquiv.symm_apply_apply _ _



private theorem eqFun_lift {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T)
    (w' : ColW B' f' T') (W : Set B.places.Pl) (W' : Set B'.places.Pl) (hpre : B'.toPre = B.toPre) (hf : HEq f' f)
    (hpx : HEq w'.px w.px) (j j' : ℕ) (hj : j = j') (ι : B.fields.K →+* B'.fields.K) (hι : ∀ x, B'.embLL (ι x) = B.embLL x) :
    ∃ Lf : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T W))).1 j).EqFun →+ (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' W'))).1 j').EqFun,
      (∀ (a : B.fields.K) ψ, Lf (a • ψ) = ι a • Lf ψ) ∧
      ∀ ψ d d', HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((Lf ψ).1 d').1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (ψ.1 d).1) := by
  subst hj
  cases B with | mk P₁ =>
  cases B' with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  have ef : f' = f := eq_of_heq hf
  have ep : w'.px = w.px := eq_of_heq hpx
  have hv : ((baseOfColW w').primes w'.px).vGs = ((baseOfColW w).primes w.px).vGs := by
    rw [ep]
    rfl
  have hι' : ∀ x, (baseOfColW w').embLL (ι x) = (baseOfColW w).embLL x := hι
  refine liftHom_reidx (baseOfColW w).fields ι (baseOfColW w').tauLL ?_ _ _ rfl ?_ _ _ ?_ (baseOfColW w).embLL
    (baseOfColW w').embLL hι
  · intro τ
    ext x
    apply (baseOfColW w').embLL.injective
    have h1 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w) τ)
    have h2 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w') τ)
    simp only [Formalism.L2.Col.Fields.embC, RingHom.comp_apply] at h1 h2
    exact (hι' _).trans (h1.trans h2.symm)
  · exact (rowLevelPrimes_colTuples_eq_vGs w' W').trans (hv.trans (rowLevelPrimes_colTuples_eq_vGs w W).symm)
  · refine glue_inv_coefMap_of_empty ι (twistRamifiedPrimes_empty_colTuples w W) (twistRamifiedPrimes_empty_colTuples w' W') _ _ _ _ ?_
    intro p hp
    refine levKV_coefMap_of ι p.1 (fun s => w.I.Ch.chi s p) (fun s => w'.I.Ch.chi s ⟨p.1, hp⟩) ?_ _ _ _ _
    intro s c
    apply (baseOfColW w').embLL.injective
    refine Eq.trans ?_ (hι' _).symm
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 (baseOfColW w).fields.E ⧸ p.1.asIdeal)
    have hy0 : ((y : 𝓞 (baseOfColW w).fields.E) : (baseOfColW w).fields.E) ≠ 0 := by
      intro h0
      have h0' : y = 0 := RingOfIntegers.coe_injective (h0.trans (by simp))
      rw [h0', map_zero] at hy
      exact c.ne_zero hy.symm
    have e1 := GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi w' s ⟨p.1, hp⟩ c y (Units.mk0 _ hy0) rfl hy.symm
    have e2 := GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi w s p c y (Units.mk0 _ hy0) rfl hy.symm
    have eC : w'.I.C = w.I.C := w'.C_eq.trans (ef.trans w.C_eq.symm)
    rw [eC] at e1
    exact e1.trans e2.symm



private theorem forms_lift {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T)
    (w' : ColW B' f' T') (W : Set B.places.Pl) (W' : Set B'.places.Pl) (hpre : B'.toPre = B.toPre) (hf : HEq f' f)
    (hpx : HEq w'.px w.px) (j j' : ℕ) (hj : j = j') (ι : B.fields.K →+* B'.fields.K) (hι : ∀ x, B'.embLL (ι x) = B.embLL x)
    (h₁ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T W))).1 j).Ok) (h₂ : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' W'))).1 j').Ok) :
    ∃ L : (Formalism.L2.Col.GSD.toCSD _ h₁).Forms →+ (Formalism.L2.Col.GSD.toCSD _ h₂).Forms,
      (∀ (a : B.fields.K) ψ, L (a • ψ) = ι a • L ψ) ∧
      ∀ ψ d d', HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₂).symm (L ψ)).1 d').1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₁).symm ψ).1 d).1) := by
  obtain ⟨Lf, hs, hc⟩ := eqFun_lift w w' W W' hpre hf hpx j j' hj ι hι
  obtain ⟨L, hL, hr⟩ := formsLift_of_eqFunLift ι _ _ h₁ h₂ Lf hs
  refine ⟨L, hL, fun ψ d d' hd => ?_⟩
  rw [hr]
  exact hc _ d d' hd

end GlobalTheory.Mem.R3.DefLatBC.LiftExt


theorem _root_.GlobalTheory.T.exists_semilinearFormsLift_sameComplexValues : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms, (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) ∧ (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1))) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE hf _ hp Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' hj φ hφ => ?_
  exact GlobalTheory.Mem.R3.DefLatBC.LiftExt.forms_lift w w' Wt {v | B'.places.resChar v ∈ T'.pl} hE.1 hf hp ((j : ℕ) + 1) ((j' : ℕ) + 1)
    (by rw [hj]) φ hφ
    (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))
    (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conj_level_conjCharacter_symmetricLevel : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (eR : G' ≃* G0g D.nd) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ x : X.B.I.E, HEq (X.ιE x) x) → R.toLevCh.Is A.μ0 → (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) → (∀ kv, R.C.P.Div kv.1 (plg kv).1) → (∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)) → ∀ (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsGenericPsi R.Pg ψ0 → ∀ π : Equiv.Perm (Fin D.R.r), IsSymOrd D.R.rS D.R.k π → ∀ (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E), IsRedHom X red → FixRed X red b → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∃ c : G0g D.nd, ∀ k ∈ X.B.I.Kset, (k ∈ X.K2 ↔ reord π (R.eG (eR.symm (c⁻¹ * red k * c))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H) ∧ ∀ hk : reord π (R.eG (eR.symm (c⁻¹ * red k * c))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H, (((PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).chi ⟨_, hk⟩ : ℂˣ) : ℂ) = star (X.chi2 k) := by
  first | exact @GlobalTheory.Mem.SymFrame.conj_symLevel | exact GlobalTheory.Mem.SymFrame.conj_symLevel | (intros; apply GlobalTheory.Mem.SymFrame.conj_symLevel <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.penultimateChart_localGroup_mem_nearLevelSet : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Q → ∀ β (x : (K β).lev.Uloc v), x.1 ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v := by
  first | exact @GlobalTheory.Mem.Col2.QChi.mem_nearSet_chart | exact GlobalTheory.Mem.Col2.QChi.mem_nearSet_chart | (intros; apply GlobalTheory.Mem.Col2.QChi.mem_nearSet_chart <;> assumption)
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

theorem _root_.GlobalTheory.T.formsLift_extendedData_carries_classSum : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) → (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) → ∀ f g : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms, ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.csum (L f : ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Cl → ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.V) (L g) = φ (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.csum f g)) := by
  first | exact @GlobalTheory.Mem.R3.DefLatBC.csum_ext | exact GlobalTheory.Mem.R3.DefLatBC.csum_ext | (intros; apply GlobalTheory.Mem.R3.DefLatBC.csum_ext <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

theorem _root_.GlobalTheory.T.reading_coordinatewiseImage_eq_extendedData : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (x : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (x' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL), (∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)) → HEq ((z'.R.FW j').j (w'.st Z').toD7.what₂.embLL x') ((z.R.FW j).j (w.st Z).toD7.what₂.embLL x)) := by
  first | exact @GlobalTheory.Mem.R3.LiftRead.read_ext | exact GlobalTheory.Mem.R3.LiftRead.read_ext | (intros; apply GlobalTheory.Mem.R3.LiftRead.read_ext <;> assumption)

end
end
