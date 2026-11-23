module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
public import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle371
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle427
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle271
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle553
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.HeightCounting.HeckeLaw

theorem delAt_unr {D : D7} (C : CharFrame D) (i : D.ntw.Tw) {P : PlE D.host} (hP : P ∉ D.ntw.S0 i) :
    (C.delAt (D.ntw.l i)).UnrAt P := by
  have h : ¬ OverP D.host (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) P := fun hk =>
    hP (D.ntw.primes_subset_exceptional i (by rw [← Finset.mem_coe, D.ntw.pD_eq]; exact hk))
  unfold CharFrame.delAt
  split_ifs at h ⊢
  · exact C.isDel'.unr P h
  · exact C.isDel.unr P h

theorem del_values {B : Base} {δ : Fld.FieldDat B.toPre} {f : Fr B.toPre} (h : B.KsExact δ f) :
    f.del.ValuesIn 0 B.KstoC ∧ f.del'.ValuesIn 0 B.KstoC := by
  have h1 : Fld.charField f ≤ B.KsC := ((Fld.listField_le_iff δ f).1 (le_of_eq (Eq.symm h))).2.2.2.2.1
  rw [Fld.valuesIn_iff, Fld.valuesIn_iff, B.imField_KstoC]
  exact ⟨((le_sup_right.trans le_sup_left).trans le_sup_left).trans h1, (le_sup_right.trans le_sup_left).trans h1⟩

theorem delAt_mem {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) {hX : B.fields.Ok} {Wt : Set B.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt) (i : (w.st Z).toD7.ntw.Tw) (P : PlE (w.st Z).toD7.host) (hP : P ∉ (w.st Z).toD7.ntw.S0 i) :
    ∃ s : z.core.Q.c.F, (w.st Z).toD7.what₂.embLL (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL s) =
      (((z.R.C.delAt ((w.st Z).toD7.ntw.l i)).val P : ℂˣ) : ℂ) := by
  have hC : z.R.C = Fr.at (w.st Z) f := z.lev.C.trans (congrArg _ w.C_eq)
  have hu := delAt_unr z.R.C i hP
  have hv : (z.R.C.delAt ((w.st Z).toD7.ntw.l i)).ValuesIn 0 B.KstoC := by
    rw [hC]
    unfold CharFrame.delAt
    split_ifs
    · exact (del_values w.exact).2
    · exact (del_values w.exact).1
  obtain ⟨y, hy⟩ := hv P hu
  obtain ⟨s, hs⟩ := z.Ks_le y.1 y.2
  refine ⟨s, ?_⟩
  rw [hs]
  refine Eq.trans (show _ = B.KstoC y from rfl) (hy.trans ?_)
  simp [HChar.valTw]

end GlobalTheory.HeightCounting.HeckeLaw
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem valLL0_colW {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) :
    ValLL0 (w.D Z) (TC.cf w.I w.l Z) := by
  rcases w with ⟨px, I, ok, C_eq, S_eq, xi_range, pins, l, l0, δ, exact, fld, val⟩
  subst C_eq
  exact val _ _ _ _ _ _

end GlobalTheory.HeightCounting.Up
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.RankSize

theorem rank_ge_hundred : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), 100 ≤ (w.D Z).R.r := by
  refine ⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ =>
    ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨100, fun K _ _ _ _ hx _ => ?_⟩⟩⟩⟩⟩
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp_all, by simp_all,
    fun B f _ hO _ _ _ _ T w Z => ?_⟩
  show 100 ≤ B.R.r
  obtain ⟨sp, hT, hY, hA, hV, hz, hB, -⟩ := hO
  have hRK : B.toPre.R = K.P.R := by rw [hB]; rfl
  have hR : GlobalTheory.EX.RankVal K.s B.toPre.R := hRK ▸ K.ok.rank
  obtain ⟨-, -, ⟨hk, -⟩, -⟩ := hR
  have hx1 := K.s.one_lt_alt
  have he := K.s.eps_pos
  have hk1 : K.s.x ≤ (B.toPre.R.k : ℝ) := by
    calc K.s.x = K.s.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ K.s.x ^ (9 / 2 + 10 * K.s.eps) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      _ ≤ _ := hk
  have h100 : (100 : ℝ) ≤ (B.toPre.R.k : ℝ) := hx.trans hk1
  have hk100 : 100 ≤ B.toPre.R.k := by exact_mod_cast h100
  have h2m := B.toPre.R.two_le_m
  have hmk := B.toPre.R.m_add_three_le_k
  have hkr : B.toPre.R.k ≤ B.toPre.R.r := by unfold Ranks.r; omega
  exact hk100.trans hkr

end GlobalTheory.Mem.RankSize
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.Top.Bl

theorem two_mul_r_le_g_level : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), ∀ k,
    2 * (w.D Z).R.r ≤ (w.D Z).host.g k := by
  refine evG_all fun K => lg_all K fun B f T hO _ T' w Z k => ?_
  obtain ⟨sp, hT, hY, hA, hV, hz, hB, -⟩ := hO
  have hR' : B.toPre.R = K.P.R := by rw [hB]; rfl
  have hg : B.toPre.host.g = K.P.H.g := by rw [hB]; rfl
  show 2 * B.R.r ≤ B.host.g k
  rw [show B.host.g k = K.P.H.g k from congrFun hg k, show B.R.r = K.P.R.r from by rw [hR']]
  have hgk : ((K.P.R.k : ℝ) * K.s.b) ^ 8 ≤ (K.P.H.g k : ℝ) := (K.ok.val.2.2.2.2.1 k).1
  have hb : 1 ≤ K.s.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [K.s.one_lt_alt]) _)
  have hk0 : (0 : ℝ) ≤ K.P.R.k := Nat.cast_nonneg _
  have hkb : (K.P.R.k : ℝ) ^ 8 ≤ (K.P.H.g k : ℝ) :=
    le_trans (pow_le_pow_left₀ hk0 (le_mul_of_one_le_right hk0 hb) 8) hgk
  have hk8 : (K.P.R.k) ^ 8 ≤ K.P.H.g k := by exact_mod_cast hkb
  have h2k : 2 ≤ K.P.R.k := by
    have := K.P.R.f_le_k
    have : 0 < K.P.R.ord := K.P.R.ord_pos
    omega
  have hr : 2 * K.P.R.r ≤ 4 * K.P.R.k := by
    have := K.P.R.m_add_three_le_k
    simp only [Ranks.r]
    omega
  have h4 : 4 * K.P.R.k ≤ K.P.R.k ^ 8 := by
    calc 4 * K.P.R.k ≤ K.P.R.k ^ 7 * K.P.R.k := by
          apply Nat.mul_le_mul_right
          calc 4 ≤ 2 ^ 7 := by norm_num
            _ ≤ K.P.R.k ^ 7 := Nat.pow_le_pow_left h2k 7
      _ = K.P.R.k ^ 8 := by ring
  omega

end GlobalTheory.Mem.Top.Bl
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.DefSpaces

theorem v_isDefinite : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), ∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ((w.D Z).sp.V j).IsDefinite := by
  refine (GlobalTheory.Mem.Top.evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev).imp fun K _ _ _ _ hK =>
    GlobalTheory.Mem.Top.GroupRetwisting.lg_all K fun B f _ hO _ T w Z j hj1 hj2 => ?_
  obtain ⟨hV, -⟩ := hK (w.st Z) hO
  have hm : (w.st Z).toD7.R.m = (w.D Z).R.m := rfl
  have hp := GlobalTheory.RepsObj.isPosDef_of_vStd (D := (w.st Z).toD7) ⟨j - 1, by omega⟩ (hV ⟨j - 1, by omega⟩)
  change ((w.st Z).toD7.sp.V j).IsDefinite
  intro τ
  left
  have e : j - 1 + 1 = j := by omega
  have := hp τ
  simp only [Formalism.IndefR.Links.Vc, e] at this
  exact this

end GlobalTheory.Mem.DefSpaces
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.SelSideW

theorem plMap_refl {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Formalism.L2.Host.CT.plMap (RingEquiv.refl E) P = P := by
  ext x
  exact Formalism.L2.Host.CT.mem_plMap (RingEquiv.refl E) P x


open Classical in
theorem image_refl {E : Type} [Field E] [NumberField E] (f : E ≃+* E) (hf : f = RingEquiv.refl E)
    (S : Finset (HeightOneSpectrum (𝓞 E))) : S.image (Formalism.L2.Host.CT.plMap f) = S := by
  subst hf
  rw [show Formalism.L2.Host.CT.plMap (RingEquiv.refl E) = id from funext plMap_refl, Finset.image_id]


open Classical in
theorem qe_image_congr {D : D7} {X X' : Formalism.L2.Col.Fields} (hX : X = X') {s : Formalism.L2.Ker.Seam D X} {s' : Formalism.L2.Ker.Seam D X'}
    (hs : HEq s s') {S S' : Set ℕ} (hS : S = S') {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)} (hsel : HEq sel sel')
    {tup : D.what₂.Tup → Formalism.L2.DIV.Tup X.F X.E X.K S} {tup' : D.what₂.Tup → Formalism.L2.DIV.Tup X'.F X'.E X'.K S'} (htup : HEq tup tup')
    (μ : D.what₂.Tup) :
    (Col.QE sel (tup μ : DIV.Chr X.F X.E X.K)).image (Host.CT.plMap s.iE) =
      (Col.QE sel' (tup' μ : DIV.Chr X'.F X'.E X'.K)).image (Host.CT.plMap s'.iE) := by
  subst hX
  subst hS
  cases hs
  cases hsel
  cases htup
  rfl


open Classical in
theorem qe_image_std {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt)
    {L : SizeData₂ (w.D Z)} {hT : GatTies (w.D Z)} {Gi : Formalism.MainNotions.G.Inst (w.D Z) L} {Gl : Formalism.MainNotions.G.LatInst (w.D Z)}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.D Z)} {cX : ExtraC} {ex : Extra (w.D Z) L hT Gi Gl Kc Yd cX}
    (t : Formalism.L2.Ker.KerEntTied ex) (h : TC.StdKer w.I w.l Z t) (μ : (w.D Z).what₂.Tup) :
    (Col.QE t.sel (t.tup μ : DIV.Chr t.X.F t.X.E t.X.K)).image (Host.CT.plMap t.seam.iE) = w.I.Q μ := by
  rw [qe_image_congr h.X_eq h.seam h.S h.sel h.tup μ]
  exact image_refl _ rfl _

end GlobalTheory.Mem.R3.SelSideW

namespace GlobalTheory.Mem.R3.SelSideW


end GlobalTheory.Mem.R3.SelSideW
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.HypCMRec

theorem hypCM_all (D : D7) : SphericalInertData.HypCM D := by
  refine ⟨?_, GlobalTheory.DesignBC.two_le_finrank D, fun w hw h2 => hw (GlobalTheory.DesignBC.isSplitPl_of_two_mem D w h2)⟩
  letI := D.host.cmStar
  exact D.sp.cm.cmUnram

theorem hypCM_at_record : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), SphericalInertData.HypCM (w.D Z) :=
  evG_all fun K => lg_all K fun _ _ _ _ _ _ _ _ => hypCM_all _

end GlobalTheory.Mem.HypCMRec

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.HostEFK

theorem hypEFK_ev : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), SphericalInertData.HypEFK (w.D Z) :=
  evG_all fun K => lg_all K fun B f T _ _ T' w Z => GlobalTheory.DesignBC.hypEFK (w.D Z)

end GlobalTheory.Mem.HostEFK
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.SwapN

open GlobalTheory.Mem.Top.TypesTrue

theorem heq_apply_cast {X : Type*} {P P' : Fin 2 → Type} (h : P = P') {a : ∀ k, P k → X} {a' : ∀ k, P' k → X}
    (ha : HEq a a') (k : Fin 2) (v : P k) : a' k (cast (congrFun h k) v) = a k v := by
  subst h
  obtain rfl := eq_of_heq ha
  rfl

theorem cen_transport {r : ℕ} {g : Fin 2 → ℕ} {P P' : Fin 2 → Type} (h : P = P') {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    {c : ∀ i, Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1)))) →ₐ[ℂ]
      Module.End ℂ (E i)}
    {c' : ∀ i, Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1)))) →ₐ[ℂ]
      Module.End ℂ (E i)}
    (hc : HEq c c')
    (e : (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1))) ≃* (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1))))
    (he : ∀ x k v, e x ⟨k, cast (congrFun h k) v⟩ = x ⟨k, v⟩) (i : ι) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1)))))
    (z₁ : Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1))))) (hz : ∀ x, (z₁ : MonoidAlgebra ℂ _).coeff (e x) =
      (z : MonoidAlgebra ℂ _).coeff x) : c i z = c' i z₁ := by
  subst h
  obtain rfl := eq_of_heq hc
  have he' : ∀ x, e x = x := fun x => funext fun kv => he x kv.1 kv.2
  congr 1
  apply Subtype.ext
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun x => ?_
  have := hz x
  rw [he'] at this
  exact this.symm

theorem cen_transport₂ {r : ℕ} {g : Fin 2 → ℕ} {P P' : Fin 2 → Type} (h : P = P') {ι κ : Type*} {E : ι → κ → Type*}
    [∀ i j, AddCommGroup (E i j)] [∀ i j, Module ℂ (E i j)]
    {c : ∀ i j, Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1)))) →ₐ[ℂ]
      Module.End ℂ (E i j)}
    {c' : ∀ i j, Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1)))) →ₐ[ℂ]
      Module.End ℂ (E i j)}
    (hc : HEq c c')
    (e : (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1))) ≃* (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1))))
    (he : ∀ x k v, e x ⟨k, cast (congrFun h k) v⟩ = x ⟨k, v⟩) (i : ι) (j : κ) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1)))))
    (z₁ : Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1))))) (hz : ∀ x, (z₁ : MonoidAlgebra ℂ _).coeff (e x) =
      (z : MonoidAlgebra ℂ _).coeff x) : c i j z = c' i j z₁ := by
  subst h
  obtain rfl := eq_of_heq hc
  have he' : ∀ x, e x = x := fun x => funext fun kv => he x kv.1 kv.2
  congr 1
  apply Subtype.ext
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun x => ?_
  have := hz x
  rw [he'] at this
  exact this.symm

theorem mem_center_map {G G' : Type*} [Monoid G] [Monoid G'] (φ : MonoidAlgebra ℂ G ≃ₐ[ℂ] MonoidAlgebra ℂ G')
    {a : MonoidAlgebra ℂ G} (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) : φ a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G') := by
  rw [Subalgebra.mem_center_iff] at ha ⊢
  intro b
  obtain ⟨b, rfl⟩ := φ.surjective b
  rw [← map_mul, ← map_mul, ha b]

end GlobalTheory.Mem.R3.Rw.SwapN

namespace GlobalTheory.Mem.R3.Rw.SwapN

theorem fits_swap : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)), GrpTrue N f → N.nd.PlG = x.o.N.nd.PlG → HEq N.naut.plGw x.o.N.naut.plGw → HEq N.ntypes.cenAmb x.o.N.ntypes.cenAmb → HEq N.ntypes.cenMt x.o.N.ntypes.cenMt → GrpAt (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.I ∧ ∀ eR, StdIso (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.px eR → CenIs P.q.p N eR := by
  intro K B f T w P x N hG hP hw hA hM
  have hG' : GrpTrue x.o.N f := x.fits.grp
  obtain ⟨⟨plg, hplg⟩, hidem, hcen⟩ := x.fits.grpAt
  let e := grpEquiv N.naut x.o.N.naut
  have hco : ∀ g, x.o.N.ntypes.e0.coeff (e g) = N.ntypes.e0.coeff g := GrpTrue.typeIdempotent_coeff_across_layers hG hG'
  let φ := MonoidAlgebra.domCongr ℂ ℂ e
  have hφ : ∀ (a : MonoidAlgebra ℂ (G0g N.nd)) g, (φ a).coeff (e g) = a.coeff g := by
    intro a g
    simp [φ]
  have he0 : N.ntypes.e0 = φ.symm x.o.N.ntypes.e0 := by
    apply MonoidAlgebra.coeff_injective
    refine Finsupp.ext fun g => ?_
    show _ = (MonoidAlgebra.domCongr ℂ ℂ e.symm x.o.N.ntypes.e0).coeff g
    rw [MonoidAlgebra.coeff_domCongr, MulEquiv.symm_symm, hco]
  have hpe : ∀ k v, plEquiv N.naut x.o.N.naut k v = cast (congrFun hP k) v := by
    intro k v
    show (plF x.o.N.naut k).symm (plF N.naut k v) = _
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    rw [plF_apply, plF_apply, heq_apply_cast hP hw k v]
  have he : ∀ (g : G0g N.nd) k v, e g ⟨k, cast (congrFun hP k) v⟩ = g ⟨k, v⟩ := by
    intro g k v
    rw [grpEquiv_apply, ← hpe, Equiv.symm_apply_apply]
  refine ⟨⟨⟨(Equiv.sigmaCongrRight fun k => plEquiv N.naut x.o.N.naut k).trans plg, fun kv => ?_⟩, ?_, ?_⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := hplg ⟨kv.1, plEquiv N.naut x.o.N.naut kv.1 kv.2⟩
    refine ⟨?_, h2⟩
    exact h1.trans (TypesTrue.plGw_plEquiv hG hG' kv.1 kv.2)
  · show IsIdempotentElem N.ntypes.e0
    rw [he0]
    exact hidem.map φ.symm
  · show N.ntypes.e0 ∈ _
    rw [he0]
    exact mem_center_map φ.symm hcen
  · rintro eR ⟨plg1, iso1, hpl1, hact1⟩
    have hstd : StdIso (w.st x.o.Z) w.px (eR.trans e) := by
      refine ⟨(Equiv.sigmaCongrRight fun k => (plEquiv N.naut x.o.N.naut k).symm).trans plg1,
        fun kv => iso1 ⟨kv.1, (plEquiv N.naut x.o.N.naut kv.1).symm kv.2⟩, fun kv => ?_, fun g kv => ?_⟩
      · refine (hpl1 ⟨kv.1, (plEquiv N.naut x.o.N.naut kv.1).symm kv.2⟩).trans ?_
        have := TypesTrue.plGw_plEquiv hG hG' kv.1 ((plEquiv N.naut x.o.N.naut kv.1).symm kv.2)
        exact ((congrArg (x.o.N.naut.plGw kv.1) (Equiv.apply_symm_apply (plEquiv N.naut x.o.N.naut kv.1) kv.2)).symm.trans
          this).symm
      · exact hact1 g _
    have hc := x.fits.cen _ hstd
    have hz1 : ∀ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N.nd))), φ (z : MonoidAlgebra ℂ (G0g N.nd)) ∈
        Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g x.o.N.nd)) := fun z => mem_center_map φ z.2
    refine ⟨fun μ z z' hz xx => ?_, fun μ j z z' hz xx => ?_⟩
    · have h1 := hc.amb μ ⟨_, hz1 z⟩ z' (fun g => by
        show _ = (φ (z : MonoidAlgebra ℂ (G0g N.nd))).coeff (e (eR g))
        exact (hz g).trans (hφ _ _).symm) xx
      rw [cen_transport hP hA e he μ z ⟨_, hz1 z⟩ (fun g => hφ _ g)]
      exact h1
    · have h1 := hc.mt μ j ⟨_, hz1 z⟩ z' (fun g => by
        show _ = (φ (z : MonoidAlgebra ℂ (G0g N.nd))).coeff (e (eR g))
        exact (hz g).trans (hφ _ _).symm) xx
      rw [cen_transport₂ hP hM e he μ j z ⟨_, hz1 z⟩ (fun g => hφ _ g)]
      exact h1

end GlobalTheory.Mem.R3.Rw.SwapN
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.fittingLaterStages_row_is_constructionState : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), ∀ o : P.q.Over, o.Fits → o.G = P.Z₀.G → o.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) → BkLaw (w.D o.Z) → ∃ x : St P, x.o = o := by
  exact @GlobalTheory.Mem.R3.Rw.st_of_fits
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.untwisted_adelic_data_saturated_over_fixed_field : GlobalTheory.Published.GreenCuspidal → DatExS → LowerUnitaryCaseCondition → DatExt0 → StepW Pinned fun K B f T w => T = TwDat.untw B T.pl → ∃ (Z : w.Lt) (hX : B.fields.Ok) (z : Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}), GIs2 K w Z.G ∧ GrpTrue Z.N f ∧ GrpAt (w.st Z) w.I ∧ DV.KapDef (w.D Z) ∧ Fine z ∧ (∀ v ∈ z.W1 (F0K K.s (w.D Z)), B.places.resChar v ∈ T.pl) ∧ (∀ v, v ∉ z.W1 (F0K K.s (w.D Z)) → T.psi v = 1) ∧ ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D Z) v v' → v ∈ z.W1 (F0K K.s (w.D Z)) → v' ∈ z.W1 (F0K K.s (w.D Z)) := by
  first | exact @GlobalTheory.Mem.R3.Rw.UntwSat.dat_saturated_of_untw | exact GlobalTheory.Mem.R3.Rw.UntwSat.dat_saturated_of_untw | (intros; apply GlobalTheory.Mem.R3.Rw.UntwSat.dat_saturated_of_untw <;> assumption)
end
