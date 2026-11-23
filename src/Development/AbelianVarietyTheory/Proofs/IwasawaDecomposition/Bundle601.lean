module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle264
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle195
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle937
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle416
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle484
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle596
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle271
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle262
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle597
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle278
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle599
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle269
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle257
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverSplit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

noncomputable section

namespace GlobalTheory.FrameTypes

open ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.CenFrame


def IsBlockUpperUnipotentMatrix {k : Type} [CommRing k] {n : ℕ} (r : ℕ) (x : GL (Fin n) k) : Prop :=
  ∀ i j : Fin n, (r ≤ i.val → j.val < r → x.val i j = 0) ∧ (i.val < r → j.val < i.val → x.val i j = 0) ∧
    (i.val < r → i = j → x.val i j = 1)

theorem blkUni_one {k : Type} [CommRing k] {n : ℕ} (r : ℕ) : IsBlockUpperUnipotentMatrix r (1 : GL (Fin n) k) := by
  intro i j
  refine ⟨fun h1 h2 => ?_, fun _ h2 => ?_, fun _ h2 => ?_⟩
  · rw [Units.val_one, Matrix.one_apply_ne]; rintro rfl; omega
  · rw [Units.val_one, Matrix.one_apply_ne]; rintro rfl; omega
  · rw [Units.val_one, h2, Matrix.one_apply_eq]

theorem IsBlockUpperUnipotentMatrix.blk2 {k : Type} [CommRing k] {n r : ℕ} {x : GL (Fin n) k} (h : IsBlockUpperUnipotentMatrix r x) : x ∈ blockTri (blk2 r) := by
  refine mem_blockTri.2 fun i j hij => ?_
  unfold Formalism.L2.DIV.blk2 at hij
  refine (h i j).1 ?_ ?_ <;> split_ifs at hij <;> omega

theorem IsBlockUpperUnipotentMatrix.blkOf {k : Type} [CommRing k] {n r t : ℕ} (hn : n ≤ r + t) {x : GL (Fin n) k} (h : IsBlockUpperUnipotentMatrix r x) :
    x ∈ blockTri (blkOf r t) := by
  refine mem_blockTri.2 fun i j hij => ?_
  unfold Formalism.L2.DIV.blkOf at hij
  have hi := i.2
  by_cases h1 : i.val < r
  · rw [if_pos h1] at hij; omega
  · rw [if_neg h1, Nat.div_eq_of_lt (show i.val - r < t by omega)] at hij
    refine (h i j).1 (by omega) ?_
    by_contra h2
    rw [if_neg h2] at hij
    exact absurd hij (not_lt.2 (Nat.succ_le_succ (Nat.zero_le _)))

theorem IsBlockUpperUnipotentMatrix.unip {k : Type} [CommRing k] {n r : ℕ} (hr : r ≤ n) {x : GL (Fin n) k} (h : IsBlockUpperUnipotentMatrix r x) :
    upperLeftBlock hr x ∈ unip k r := by
  refine ⟨mem_blockTri.2 fun i j hij => ?_, fun i => ?_⟩
  · rw [upper_block_val_submatrix hr h.blk2]
    exact (h _ _).2.1 i.2 hij
  · rw [upper_block_val_submatrix hr h.blk2]
    exact (h _ _).2.2 i.2 rfl

variable {D : D7}

theorem isConjPl_of_under (s : SplitPlace D.host.E) {PP : PlE D.host} (hne : PP ≠ s.w)
    (h : HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) PP = s.v) : Formalism.IndefR.Lev.IsConjPl (D := D) PP s.w := by
  rcases Formalism.L2.eq_or_eq_conjPlE s.w PP ((congrArg HeightOneSpectrum.asIdeal h).trans s.w_under.symm) with e | e
  · exact absurd e hne
  · intro c hc
    rw [e, Formalism.L2.mem_conjPlE] at hc
    refine ⟨_, hc, ?_⟩
    rw [IsCMField.coe_ringOfIntegersComplexConj, GlobalTheory.TypePlaces.star_eq_conj, GlobalTheory.SplitPlaceOver.host_conj_eq']

theorem mem_level {V : TH.HSp D} {n : ℕ} (hn : V.rank = n) {hF : D.host.F = maximalRealSubfield D.host.E}
    {P : Formalism.IndefR.principalLevelFrame.RowPsi V n} (hP : StdFrame hF P) {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hB : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1)
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (hrt : V.rank ≤ L.r + L.t)
    (hH : ∀ g : G0 L.Pg L.r, (∀ PP, g PP ∈ unip (kP PP.1) L.r) → g ∈ L.P.H)
    (s : SplitPlace D.host.E) (hsep : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP s.w)
    {φ : Os s →+* kP s.w} {b : GL (Fin n) (kP s.w)} (hfr : FrameRed hn P β s φ b)
    {κ : GAf D.host.E n} (hU : κ ∈ Umax D.host.E n) (hT : TrivOutside {s.v} κ) {y : GL (Fin n) (Os s)} (hy : IsCompOf s κ y) :
    (IsBlockUpperUnipotentMatrix L.r (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹) → P.ψ κ ∈ Formalism.IndefR.Links.levS V β L) ∧
    (Matrix.GeneralLinearGroup.map φ y = 1 →
      P.ψ κ ∈ Formalism.IndefR.Links.levS V β L ∧ Formalism.IndefR.Lev.levChi V β L (P.ψ κ) = 1) := by
  have hS := (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hB (P.into κ)).2 ((hP.2 κ).1 hU)
  have hred : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ s.w → redFn β PP (Formalism.IndefR.Lev.finE V (P.ψ κ)) = 1 := by
    intro PP hPP hne
    refine GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {(_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)} hS (fun u hu => ?_) (Finset.mem_singleton_self _)
    rw [Finset.mem_singleton.1 hu]
    exact GlobalTheory.NonSplitLevel.projV_eq_one hP κ PP (hT _ fun e => hsep PP hPP (isConjPl_of_under s hne e))
  have hent : ∀ i j : Fin V.rank, (redFn β s.w (Formalism.IndefR.Lev.finE V (P.ψ κ))).val i j =
      (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val (Fin.cast hn i) (Fin.cast hn j) :=
    fun i j => hfr κ hU y hy (Fin.cast hn i) (Fin.cast hn j)
  refine ⟨fun hb => ?_, fun h1 => ?_⟩
  · have hall : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → IsBlockUpperUnipotentMatrix L.r (redFn β PP (Formalism.IndefR.Lev.finE V (P.ψ κ))) := by
      intro PP hPP
      by_cases e : PP = s.w
      · subst e
        intro i j
        rw [hent]
        have hb' := hb (Fin.cast hn i) (Fin.cast hn j)
        exact ⟨hb'.1, hb'.2.1, fun h1 h2 => hb'.2.2 h1 (congrArg _ h2)⟩
      · rw [hred PP hPP e]; exact blkUni_one _
    exact ⟨P.into κ, mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, hS, fun PP h => (hall PP (Or.inl h)).blkOf hrt,
      fun PP h => (hall PP (Or.inr h)).blk2⟩, hH _ fun PP => (hall PP.1 (Or.inl PP.2)).unip L.hr⟩⟩
  · have hall : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → redFn β PP (Formalism.IndefR.Lev.finE V (P.ψ κ)) = 1 := by
      intro PP hPP
      by_cases e : PP = s.w
      · subst e
        refine Units.ext (Matrix.ext fun i j => ?_)
        rw [hent, h1, mul_one, mul_inv_cancel, Units.val_one, Units.val_one, Matrix.one_apply, Matrix.one_apply]
        exact if_congr (Fin.cast_injective hn).eq_iff rfl rfl
      · exact hred PP hPP e
    refine ⟨⟨P.into κ, GlobalTheory.LevSplit.mem_lev_of_red _ _ β L _ (GlobalTheory.LevSplit.finE_mem_UA V _) hS hall⟩, ?_⟩
    unfold Formalism.IndefR.Lev.levChi
    rw [GlobalTheory.LevSplit.levFn_eq_one β L _ hall, Units.val_one]

section Read
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : Formalism.IndefR.Links.RealDat3 D A3 Ks}
  {F : Formalism.IndefR.Links.Face3 D A3} {X0 : BaseLevelRowSide D} {Y : Read R.toRealDat F.lv2 X0} {M : MtFam D}



theorem exists_fn (ad : MtAd Y M) (μ : D.what₂.Tup) (hμ : Formalism.IndefR.RecTie.Used0 D μ) (k : Fin D.R.m)
    (hnt : Nontrivial (D.what₂.Mt μ ((k : ℕ) + 1))) :
    ∃ f : GAf D.host.E D.R.nV → ℂ, f ≠ 0 ∧
      (∀ κ (h : κ ∈ (M μ (k.1 + 1) (by omega) (by omega)).J) g,
        f (g * κ) = (((M μ (k.1 + 1) (by omega) (by omega)).χ ⟨κ, h⟩ : ℂˣ) : ℂ) * f g) ∧
      ∀ κ, (ad.PV k).ψ κ ∈ levS _ (R.toRealDat.βV k)
          (Formalism.IndefR.RecTie.datVP R.toRealDat k (Y.tupT μ) (R.toRealDat.levR F.lv2 false)) →
        ∀ g, f (g * κ) = levChi _ (R.toRealDat.βV k)
          (Formalism.IndefR.RecTie.datVP R.toRealDat k (Y.tupT μ) (R.toRealDat.levR F.lv2 false)) ((ad.PV k).ψ κ) * f g := by
  obtain ⟨x, hx⟩ := exists_ne (0 : D.what₂.Mt μ ((k : ℕ) + 1))
  have hr : (M μ (k.1 + 1) (by omega) (by omega)).real x ≠ 0 := fun e =>
    hx ((M μ (k.1 + 1) _ _).real_inj (e.trans (map_zero _).symm))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hr
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero ℂ hg₀
  have hm : (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).real x ∈ NG.TypeSp (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).wt.ρ
      (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).J (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).χ :=
    (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).real_range ▸ LinearMap.mem_range_self _ x
  refine ⟨fun g => l ((M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).real x g), fun e => hl (congrFun e g₀), fun κ h g => ?_, fun κ hJ g => ?_⟩
  · have e := congrFun (hm.2 ⟨κ, h⟩) g
    exact (congrArg l e).trans (map_smul l _ _)
  · have e1 := ad.read _ hμ k x (g * κ)
    have e2 := ad.read _ hμ k x g
    have e3 := (Y.IL.jMt _ hμ k x).2.2 _ hJ ((ad.PV k).ψ g)
    rw [← map_mul] at e3
    have e4 := e1.trans (e3.trans (congrArg _ e2.symm))
    rw [← map_smul] at e4
    exact (congrArg l ((ad.eW _ hμ k).injective e4)).trans (map_smul l _ _)



theorem types_of (ad : MtAd Y M) {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {Q : D.what₂.places.Pl → Finset (PlE D.host)}
    (hin : MtInput D M tup Q) {μ0 : T} (hlev : R.toRealDat.toLevCh.Is μ0) (hgl : R.toRealDat.grp_levels F.lv2)
    (i : D.nd.Loc) (μ : D.what₂.Tup) (k : Fin D.R.m) (hμ : μ = D.nd.mu i) (hnt : Nontrivial (D.what₂.Mt μ ((k : ℕ) + 1)))
    (s : SplitPlace D.host.E) (φ : Os s →+* kP s.w) (b : GL (Fin D.R.nV) (kP s.w)) (hs : s.w ∈ R.Pg)
    (hw : ∃ kk v, s.w = D.naut.plGw kk v) (hfr : FrameRed (GlobalTheory.FrameBlockDiagonal.rankV D k) (ad.PV k) (R.βV k) s φ b) :
    ∃ (f : GAf D.host.E D.R.nV → ℂ) (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ)
      (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ)
      (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ),
      f ≠ 0 ∧ NG.IsPsi0 s ψ₀ ∧ NG.LevelUni J χ s D.R.r ψ₀ ξ ∧ (∀ κ (h : κ ∈ J) g, f (g * κ) = ((χ ⟨κ, h⟩ : ℂˣ) : ℂ) * f g) ∧
      ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → ∀ y : GL (Fin D.R.nV) (Os s), IsCompOf s κ y →
        (IsBlockUpperUnipotentMatrix D.R.r (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹) → ∃ c : ℂ, ∀ g, f (g * κ) = c * f g) ∧
        (Matrix.GeneralLinearGroup.map φ y = 1 → ∀ g, f (g * κ) = f g) := by
  have hu : Formalism.IndefR.RecTie.Used0 D μ := hμ ▸ Model.used_loc i
  rw [D.nd.mu_w i] at hμ
  subst hμ
  obtain ⟨kk, v, hv⟩ := hw
  obtain ⟨ψ₀, ξ, h1, -, h2⟩ := hin.uni (D.nd.w i) k kk v s hv
  obtain ⟨f, hf, hJ, hL⟩ := exists_fn ad _ hu k hnt
  obtain ⟨c, hc⟩ := hlev.βV k
  rw [one_pow] at hc
  obtain ⟨ψ0, -, hP0, -⟩ := hgl
  refine ⟨f, _, _, ψ₀, ξ, hf, h1, h2, hJ, fun κ hU hT y hy => ?_⟩
  have key := mem_level (GlobalTheory.FrameBlockDiagonal.rankV D k) (ad.std k) hc
    (Formalism.IndefR.RecTie.datVP R.toRealDat k (Y.tupT (D.what₂.muTw (D.nd.w i))) (R.toRealDat.levR F.lv2 false))
    (le_of_eq (GlobalTheory.FrameBlockDiagonal.rankV D k))
    (fun g hg => by
      show g ∈ (R.toRealDat.levR F.lv2 false).H
      rw [hP0]
      exact fun PP _ => hg PP)
    s (fun PP hPP => GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hlev _ hPP (Or.inl hs)) hfr hU hT hy
  refine ⟨fun hb => ⟨_, hL κ (key.1 hb)⟩, fun h1 g => ?_⟩
  rw [hL κ (key.2 h1).1 g, (key.2 h1).2, one_mul]

end Read


end GlobalTheory.FrameTypes

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowAct

section Forms

variable {Xf : Formalism.L2.Col.Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 Xf.E))}
  (C : Formalism.L2.Col.CoefPk Xf n (Formalism.L2.Col.DecoSet (E := Xf.E) (n := n) (ST := ST) (SG := SG))) (Λ : Formalism.L2.Col.LevFam Xf.E Xf.K n SG)

theorem eqFun_smul_grp (φ : (Formalism.L2.Col.formGSD C Λ).EqFun) (u : Λ.grp) (a : Formalism.L2.Col.GLG (E := Xf.E) (n := n) (SG := SG))
    (d : Formalism.L2.Col.DecoSet (E := Xf.E) (n := n) (ST := ST) (SG := SG)) :
    (φ : Formalism.L2.Col.DecoSet (E := Xf.E) (n := n) (ST := ST) (SG := SG) → C.V) (((1 : Formalism.L2.Col.UF Xf.E n), (u : Formalism.L2.Col.GLG (E := Xf.E) (n := n) (SG := SG)) * a) • d) =
      ((Λ.chr u : Xf.Kˣ) : Xf.K) • (φ : Formalism.L2.Col.DecoSet (E := Xf.E) (n := n) (ST := ST) (SG := SG) → C.V) (((1 : Formalism.L2.Col.UF Xf.E n), a) • d) := by
  have e := φ.2 ((1, u) : Formalism.L2.Col.FormG Λ) (((1 : Formalism.L2.Col.UF Xf.E n), a) • d)
  have e' : ((1, u) : Formalism.L2.Col.FormG Λ) • (((1 : Formalism.L2.Col.UF Xf.E n), a) • d) =
      ((1 : Formalism.L2.Col.UF Xf.E n), (u : Formalism.L2.Col.GLG (E := Xf.E) (n := n) (SG := SG)) * a) • d := by
    show ((1 : Formalism.L2.Col.UF Xf.E n), (u : Formalism.L2.Col.GLG (E := Xf.E) (n := n) (SG := SG))) • (((1 : Formalism.L2.Col.UF Xf.E n), a) • d) = _
    rw [smul_smul, Prod.mk_mul_mk, one_mul]
  rw [e'] at e
  rw [e]
  show ((Λ.chr u : Xf.Kˣ) : Xf.K) • C.rho 1 _ = _
  rw [map_one]
  rfl

end Forms

theorem semilin_inv_smul {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    {σ : K →+* ℂ} (m : V →ₛₗ[σ] W) (k : K) (c : ℂˣ) (hk : σ k = c) (x : V) :
    m x = ((c⁻¹ : ℂˣ) : ℂ) • m (k • x) := by
  rw [LinearMap.map_smulₛₗ, hk, smul_smul, Units.inv_mul, one_smul]

end GlobalTheory.Mem.R3.RowAct

namespace GlobalTheory.Mem.R3.RowAct

theorem act_tie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∀ t, ∀ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t P →
      ∃ a : Bridge.ActTie (Bridge.ratF X.toD7.sp.X') P (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q (levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch ((famR X I hX U Xg tr).A.leftGroupActionRight t),
        ∀ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
          eG (a.red q) = rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgram hTie hinner t P hRD
  refine ⟨{
      red := eG.symm.toMonoidHom.comp (rTupQ X.toD7.sp.X' L.βX (L.datXt t))
      red_surj := ?_
      red_ker := ?_
      act_eq := ?_ }, ?_⟩
  · intro g
    have key := GlobalTheory.Mem.R3.FlagOnto.exists_flag_rTup X px I hX U L hI hV hL t (eG g)
    obtain ⟨q, hq⟩ := key
    refine ⟨q, ?_⟩
    have e : rTupQ X.toD7.sp.X' L.βX (L.datXt t) q = eG g := hq
    show eG.symm (rTupQ X.toD7.sp.X' L.βX (L.datXt t) q) = g
    rw [e, MulEquiv.symm_apply_apply]
  · intro q
    have e := rTupQ_eq_one_iff X.toD7.sp.X' L.βX (L.datXt t) q
    show eG.symm (rTupQ X.toD7.sp.X' L.βX (L.datXt t) q) = 1 ↔ _
    exact (MulEquiv.map_eq_one_iff eG.symm).trans e
  · intro g κ hκ f
    obtain ⟨m, hm⟩ := hRD
    obtain ⟨u, hdeco, hch⟩ := GlobalTheory.T.decoratedRowLattices_flagLevel_rightTranslation X px I hX U L eG hI hV hL hG t κ
    have hg : eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf X.toD7.sp.X') : GL _ _))) = g := hκ
    rw [hg] at hdeco
    funext h
    have e1 := hm ((famR X I hX U Xg tr).A.leftGroupActionRight t g f) h
    have e2 := hm f (h * (κ : Bridge.Gf X.toD7.sp.X'))
    refine e1.trans ?_
    refine Eq.trans ?_ (congrArg (fun v => (((((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch κ)⁻¹ : ℂˣ) : ℂ)) • v) e2).symm
    have e3 : ((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm
        ((famR X I hX U Xg tr).A.leftGroupActionRight t g f) = Formalism.L2.Col.g0HatRepEqFunX X.B.wts I.Ch I.sel t.1 g
          (((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f) :=
      LinearEquiv.symm_apply_apply _ _
    have e4 := eqFun_smul_grp _ _ (((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f)
      u (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R) g)⁻¹ (RowAd.decoAd X I t h)
    refine (congrArg (fun ψ : (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).EqFun =>
      m ((ψ : (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).D → (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).V)
        (RowAd.decoAd X I t h))) e3).trans ?_
    refine (semilin_inv_smul m _ _ hch _).trans ?_
    refine congrArg (fun v => (((((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch κ)⁻¹ : ℂˣ) : ℂ)) • m v) ?_
    exact e4.symm.trans (congrArg _ (hdeco h).symm)
  · intro q
    have e : eG (eG.symm (rTupQ X.toD7.sp.X' L.βX (L.datXt t) q)) = rTupQ X.toD7.sp.X' L.βX (L.datXt t) q :=
      MulEquiv.apply_symm_apply _ _
    exact e

end GlobalTheory.Mem.R3.RowAct
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.DTheta

theorem stepLev_holds : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → GlobalTheory.Mem.R3.DTheta.StepLev R.toRealDat F.lv2 := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH b t k hk y hy
  have hx0 := (R.ioY t k y).2
  have hT := Formalism.IndefR.Eqv.contAt_of_mem ((mem_multT _ _ _ _ _).1 hx0)
  have hx := hx0
  rw [mem_multT, GlobalTheory.MultMem.mem_mult_iff] at hx ⊢
  refine ⟨hx.aut, hx.cusp, ?_, hx.equiv, hx.cont⟩
  intro v κ hκ g
  obtain ⟨κ', hκ', hω⟩ := GlobalTheory.Mem.R3.DTheta.StepLevLift.stepLev_lift D G Pl0 I0 T A3 Ks R F cG hP hH b t k hk κ hκ
  have hpt := GlobalTheory.T.weilFock_vector_eigen_of_finite_step_eigen D G Pl0 I0 T A3 Ks R F cG hP hH t k hk κ hκ.1 κ' hκ'.1 _ hω
  have hval := GlobalTheory.Mem.R3.DTheta.stepLev_change D G Pl0 I0 T A3 Ks R F cG hP hH b t k hk κ κ' hκ' _ hpt y hy
  set x := (R.ioY t k y).1 with hxdef
  set c0 := levChi (Yc D k) (R.βY k) (R.datYt t k (R.toRealDat.levR F.lv2 b)) κ with hc0
  set c1 := levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) κ' with hc1
  have hne : c1 ≠ 0 := by rw [hc1]; unfold levChi; exact Units.ne_zero _
  let u : MMap (R.MY k) := (LinearMap.funLeft ℂ ℂ (fun h : GA D (Yc D k) => h * κ)).compMultilinearMap
    (PiTensorProduct.lift.symm x) - c0 • PiTensorProduct.lift.symm x
  have hu : Formalism.IndefR.Eqv.ContAt (R.MY k) u := by
    intro τ v' z
    obtain ⟨ℓ₁, s₁, e₁⟩ := hT τ v' (z * κ)
    obtain ⟨ℓ₂, s₂, e₂⟩ := hT τ v' z
    refine ⟨ℓ₁ + (-c0) • ℓ₂, GlobalTheory.MultMem.sobCont_add s₁ (GlobalTheory.MultMem.sobCont_smul _ s₂), fun w => ?_⟩
    simp only [u, LinearMap.add_apply, LinearMap.smul_apply, e₁, e₂, MultilinearMap.sub_apply,
      MultilinearMap.smul_apply, LinearMap.compMultilinearMap_apply, Pi.sub_apply, Pi.smul_apply,
      LinearMap.funLeft_apply, smul_eq_mul]
    ring
  have hz : ∀ φ w, PiTensorProduct.lift u (R.ItY k φ w) = 0 := by
    intro φ w
    have e : PiTensorProduct.lift u = (LinearMap.funLeft ℂ ℂ (fun h : GA D (Yc D k) => h * κ)) ∘ₗ x - c0 • x := by
      apply PiTensorProduct.ext
      ext v'
      simp [u]
    rw [e]
    funext g'
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply,
      LinearMap.funLeft_apply, smul_eq_mul, Pi.zero_apply]
    rw [hval φ w g']
    field_simp
    ring
  have h0 := GlobalTheory.Mem.R3.StepUniq.eq_zero_of_vanish_it hC.1 hC.2.1 D G Pl0 I0 T A3 Ks R F cG hP hH t k hk u hu hz
  have h1 := congrFun (congrArg (fun U : MMap (R.MY k) => U v) h0) g
  simp only [u, MultilinearMap.sub_apply, MultilinearMap.smul_apply, LinearMap.compMultilinearMap_apply, Pi.sub_apply,
    Pi.smul_apply, LinearMap.funLeft_apply, smul_eq_mul, MultilinearMap.zero_apply, Pi.zero_apply] at h1
  linear_combination h1

end GlobalTheory.Mem.R3.DTheta
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2



namespace GlobalTheory.Mem.R3.LiftBrg

theorem mem_sgL_iff (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hL : LevOf X I U L) (t : TupU I U) (PP : Pl X.toD7.host.E) :
    PP ∈ sgL X I U t ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t := by
  rw [hL.Pg, hL.Q t, Col2.ColIn.Q, tup_ixOf I t]
  classical
  exact Finset.mem_union

theorem isSplitSet_sgL : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ t : TupU I U, Formalism.L2.DIV.IsSplitSet (LiftBrg.sgL X I U t) := by
  intro X px I U L _ hL t PP h PP' h' hc
  have hc' : Formalism.IndefR.Lev.IsConjPl (D := X.toD7) PP PP' := fun c hm =>
    ⟨Formalism.DivisionValues.cO X.toD7.host.E c, (hc c (Formalism.DivisionValues.cO X.toD7.host.E c) rfl).1 hm, rfl⟩
  exact GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL.is t ((mem_sgL_iff X I U L hL t PP).1 h)
    ((mem_sgL_iff X I U L hL t PP').1 h') hc'

end GlobalTheory.Mem.R3.LiftBrg
end
