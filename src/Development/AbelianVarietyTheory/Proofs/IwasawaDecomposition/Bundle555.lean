module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle025
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle081
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle082
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle384
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmHostRootComplexEqPmSqrt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIrreducibleComponentsWeberValues
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle545
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle904
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ZeroDegreeOfPinFor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle893
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle920
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle891
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle551
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.Columns.MtHeckeKv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceSupportLevelStandardCoordinates
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsWeilOnOfCoord
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle549
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle552
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
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle004
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

open GlobalTheory.Mem.R3 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links




theorem side_mk_eq_upd {D : D7} {nch : NChoice D} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {J : Formalism.L2.Pj.CoreJ D} [Algebra J.Q.c.F D.what₂.LL] (R : RealDat3 D A3 J.Q.c.F)
    (kap : ℝ) (lam : type_of% R.lam3) (err : type_of% R.err0) (P0 P0' : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (ψ0' : P0' →* D.what₂.LLˣ)
    (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (v v' : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec)
    (S S' : Formalism.IndefR.NX.RatDat D.ntw) (Y : Formalism.IndefR.NX.NExpRealS ((R.updS kap lam).withErr err) cG S)
    (Y' : Formalism.IndefR.NX.NExpRealS R cG S') (cf : Formalism.L2.Host.CharFrame D) (tp : Formalism.L2.Host.TupTied D R.C nch)
    (tp' : Formalism.L2.Host.TupTied D cf nch) (hP : P0 = P0') (hψ : HEq ψ0 ψ0') (hv : HEq v v') (hS : HEq S S') (hfi : HEq Y.fi Y'.fi)
    (heF : HEq Y.eF Y'.eF) (hcf : R.C = cf) (htp : HEq tp tp') :
    ({ G := G, Pl0 := Pl0, I0 := I0, T := T, A3 := A3, J := J, R := (R.updS kap lam).withErr err, P0 := P0, ψ0 := ψ0, cG := cG, v₀ := v, S := S, YS := Y, cf := R.C, tp := tp } : Side D nch) =
      Side.upd { G := G, Pl0 := Pl0, I0 := I0, T := T, A3 := A3, J := J, R := R, P0 := P0', ψ0 := ψ0', cG := cG, v₀ := v', S := S', YS := Y', cf := cf, tp := tp' } kap lam err := by
  subst hP hcf
  cases eq_of_heq hψ
  cases eq_of_heq hv
  cases eq_of_heq hS
  cases eq_of_heq htp
  obtain ⟨fi, _, _, _, eF, _, _⟩ := Y
  obtain ⟨fi', _, _, _, eF', _, _⟩ := Y'
  replace hfi : fi = fi' := (eq_of_heq hfi)
  replace heF : eF = eF' := (eq_of_heq heF)
  subst hfi heF
  rfl



theorem side_eq_upd {D : D7} {O : Obj D} (x : R3.TwIn O.ex) (s : Side D O.ex.nch) (kap : ℝ) (lam : type_of% s.R.lam3)
    (err : type_of% s.R.err0) (F : Face3 D s.A3) (Sx : Formalism.IndefR.NX.RatDat D.ntw) (YS : Formalism.IndefR.NX.NExpRealS x.R x.cG Sx)
    (Tp : Formalism.L2.Host.TupTied D x.R.C O.ex.nch)
    (pack : (⟨x.G, x.grp, x.fin, x.Pl0, x.I0, x.T, x.A3, x.core, x.alg, x.R, x.F, x.cG⟩ :
      Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
        (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : Formalism.L2.Pj.CoreJ D)
        (_ : Algebra C.Q.c.F D.what₂.LL) (R : RealDat3 D A3 C.Q.c.F) (_ : Face3 D A3),
        G0 R.Pg D.R.r ≃* G0g D.nd) =
      ⟨s.G, s.grp, s.fin, s.Pl0, s.I0, s.T, s.A3, s.J, s.alg, (s.R.updS kap lam).withErr err, F, s.cG⟩)
    (hP : F.P0 = s.P0) (hψ : HEq F.ψ0 s.ψ0) (hv : HEq x.geo.v₀ s.v₀) (hS : HEq Sx s.S) (hfi : HEq YS.fi s.YS.fi)
    (heF : HEq YS.eF s.YS.eF) (hcf : s.R.C = s.cf) (htp : HEq Tp s.tp) :
    ({ G := x.G, Pl0 := x.Pl0, I0 := x.I0, T := x.T, A3 := x.A3, J := x.core, R := x.R, P0 := x.F.P0, ψ0 := x.F.ψ0, cG := x.cG, v₀ := x.geo.v₀, S := Sx, YS := YS, cf := x.R.C, tp := Tp } : Side D O.ex.nch) = s.upd kap lam err := by
  obtain ⟨G, Pl0, I0, T, A3, J, R, P0, ψ0, cG, v₀, S, Y, cf, tp⟩ := s
  obtain ⟨G', Pl0', I0', T', A3', core, R', F', cG', geo⟩ := x
  cases pack
  exact side_mk_eq_upd R kap lam err _ _ _ _ cG _ _ _ _ _ _ _ _ _ hP hψ hv hS hfi heF hcf htp


end GlobalTheory.PlugPt
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.FieldSize GlobalTheory.FinalJoin
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.CoverAt

theorem exists_finset_weberIn (r : ℂ) (M : ℕ) (hM : M ≠ 0) : ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), H.rt0 = r →
      ∀ F : IntermediateField ℚ ℂ, (∀ z ∈ S, z ∈ F) → WeberIn H F M := by
  by_cases h : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), H.rt0 = r
  · obtain ⟨E₀, _, _, _, H₀, h₀⟩ := h
    obtain ⟨L₀, hL₀⟩ := GlobalTheory.FinalJoin.CurveField.exists_periodPair H₀
    obtain ⟨hfin, halg, -⟩ := weberSet_finite_algebraic_permuted L₀ M (Nat.pos_of_ne_zero hM)
      (GlobalTheory.CompRat.Weber.g₂_ne_zero H₀ L₀ hL₀) (GlobalTheory.CompRat.Weber.g₃_ne_zero H₀ L₀ hL₀)
    refine ⟨hfin.toFinset, fun z hz => halg (GlobalTheory.WeberField.invariant_isAlgebraic H₀ L₀ hL₀) z (hfin.mem_toFinset.1 hz), ?_⟩
    intro E _ _ _ H hH F hF L hL
    have hw : ∀ s, GlobalTheory.CompRat.wC H s = GlobalTheory.CompRat.wC H₀ s := fun s => by
      unfold GlobalTheory.CompRat.wC
      rw [hH, h₀]
    have e : weberSet L M = weberSet L₀ M :=
      GlobalTheory.FieldSize.SmallField.weberSet_congr (Submodule.ext fun z => by
        rw [hL z, hL₀ z]
        simp only [hw]) M
    have hs : ∀ z ∈ weberSet L M, z ∈ F := fun z hz => hF z (hfin.mem_toFinset.2 (e ▸ hz))
    exact ⟨hs _ (Set.mem_insert _ _), fun s hs' => hs _ (Set.mem_insert_of_mem _ ⟨_, (hL _).2 ⟨s, rfl⟩, hs', rfl⟩)⟩
  · exact ⟨∅, by simp, fun E _ _ _ H hH => absurd ⟨E, _, _, _, H, hH⟩ h⟩


open Classical in
def WeberLev (B : Base) (f : Fr B.toPre) (T : TwDat B) : Prop :=
  ∀ S : Finset (HeightOneSpectrum (𝓞 B.host.E)), (∀ Q ∈ S, ∃ χ ∈ T.set f, ¬ χ.UnrAt Q) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
      H.rt0 = B.host.φ₀ B.host.sqrtMinusD →
      WeberIn H B.LLC (B.host.g 0 * B.host.g 1 * ∏ q ∈ S.image (fun Q => Nat.card (kP Q)), q)


open Classical in
theorem lg_weberLev (K : Ctx) : large₂ K WeberLev := by
  have h : ∀ (P : Pre) (Ξ : Set (HChar P.host.E)), ∃ Z : Finset ℂ, (∀ z ∈ Z, IsAlgebraic ℚ z) ∧
      ({Q : HeightOneSpectrum (𝓞 P.host.E) | ∃ χ ∈ Ξ, ¬ χ.UnrAt Q}.Finite →
        ∀ S : Finset (HeightOneSpectrum (𝓞 P.host.E)), (∀ Q ∈ S, ∃ χ ∈ Ξ, ¬ χ.UnrAt Q) →
        ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
          H.rt0 = P.host.φ₀ P.host.sqrtMinusD → ∀ F : IntermediateField ℚ ℂ, (∀ z ∈ Z, z ∈ F) →
          WeberIn H F (P.host.g 0 * P.host.g 1 * ∏ q ∈ S.image (fun Q => Nat.card (kP Q)), q)) := by
    intro P Ξ
    have hne : ∀ S : Finset (HeightOneSpectrum (𝓞 P.host.E)),
        P.host.g 0 * P.host.g 1 * ∏ q ∈ S.image (fun Q => Nat.card (kP Q)), q ≠ 0 := fun S => by
      refine mul_ne_zero (mul_ne_zero (P.host.g_prime 0).ne_zero (P.host.g_prime 1).ne_zero) ?_
      rw [Finset.prod_ne_zero_iff]
      intro q hq
      obtain ⟨Q, -, rfl⟩ := Finset.mem_image.1 hq
      exact GlobalTheory.Plug.TwistLevels.card_residueField_ne_zero Q
    choose Z hZ hZ' using fun S => exists_finset_weberIn (P.host.φ₀ P.host.sqrtMinusD) _ (hne S)
    by_cases hA : {Q : HeightOneSpectrum (𝓞 P.host.E) | ∃ χ ∈ Ξ, ¬ χ.UnrAt Q}.Finite
    · refine ⟨hA.toFinset.powerset.biUnion Z, fun z hz => ?_, fun _ S hS E _ _ _ H hH F hF => ?_⟩
      · obtain ⟨S, -, hz⟩ := Finset.mem_biUnion.1 hz
        exact hZ S z hz
      · exact hZ' S E H hH F fun z hz => hF z (Finset.mem_biUnion.2
          ⟨S, Finset.mem_powerset.2 fun Q hQ => hA.mem_toFinset.2 (hS Q hQ), hz⟩)
    · exact ⟨∅, by simp, fun h => absurd h hA⟩
  choose Z hZ hZ' using h
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun P _ _ _ Ξ => Z P Ξ, by simp,
    fun P _ _ _ Ξ => hZ P Ξ, fun B f T _ hH _ _ S hS E _ _ _ H hr => ?_⟩
  refine hZ' B.toPre (T.set f) ?_ S hS E H hr _ hH.2
  refine ((GlobalTheory.Mem.Top.TwFin.tw_fin B f T).1.biUnion fun χ hχ => GlobalTheory.Plug.TwistLevels.ram_finite B f T χ hχ).subset ?_
  rintro Q ⟨χ, hχ, hr⟩
  exact Set.mem_biUnion (x := χ) hχ hr



theorem coverField_of_weberLev {B : Base} {f : Fr B.toPre} {T : TwDat B} (hW : WeberLev B f T) (w : ColW B f T) (Z : w.Lt)
    (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : R3.Dat (w.st Z) w.I hX T Wt) :
    GlobalTheory.TwistField.CoverField z.core z.R.toRealDat := by
  intro i t l₂ _ hM hA Xo₂ c₂ hc
  have hP : z.core.Q.Pins := z.geo.fw.laws.pins
  have hS : ∀ Q ∈ z.R.Q t, ∃ χ ∈ T.set f, ¬ χ.UnrAt Q := fun Q hQ =>
    ⟨z.R.xiH t, by
      rw [z.lev.xiH t, ← w.xi_range]
      exact ⟨_, rfl⟩, (z.lev.is.Q_ram t Q).2 (Or.inl hQ)⟩
  have hw := hW (z.R.Q t) hS _ z.core.Q.H hP.1.2.2.1
  have hlev : l₂.M = B.host.g 0 * B.host.g 1 * GlobalTheory.TwistField.tupPrime z.R.toRealDat t := by
    rw [hM, show z.core.Q.l.M = _ from hP.2.1.1]
    rfl
  have hw' : WeberIn z.core.Q.H c₂.F l₂.M := by
    rw [hlev, hc]
    exact hw
  refine GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_weberIn _ z.core.Q hP ((i : ℕ) + 1) ⟨Nat.succ_le_succ (Nat.zero_le _), i.2⟩ l₂ Xo₂ c₂
    l₂.M (lt_of_lt_of_le (by norm_num) l₂.three_le) ?_ (Or.inl hw')
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.M', hA, Nat.lcm_one_right]

end GlobalTheory.Mem.Top.Bl.CoverAt

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



noncomputable section

namespace GlobalTheory.HeightCounting.SerCopy

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem hkAd_step (R : RealDat3 D A3 Ks) (Sb : Finset (PlE D.host)) (i' i : Fin D.R.m) (h : i' = i) (k : ℕ) (P : PlE D.host)
    (f : Module.End D.what₂.LL (Fin (R.nW i') → D.what₂.LL))
    (hAd : ∀ α Rr, HkDat R Sb i' k P α Rr → ∀ x : Fin (R.nW i') → D.what₂.LL,
      (R.HW i' (sg0 D A3.A)).e ((R.FW i').j (sg0 D A3.A) (f x)) =
        hkNorm R i' k P • Mult.heckeOn (R.MW i' (sg0 D A3.A)) Rr ((R.HW i' (sg0 D A3.A)).e ((R.FW i').j (sg0 D A3.A) x)))
    (α : GA D (Wc D i)) (Rr : Finset (GA D (Wc D i))) (hd : HkDat R Sb i k P α Rr) (x : Fin (R.nW i') → D.what₂.LL) :
    (R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) ((SideTies.fiOf R i' i h).e (f x))) =
      hkNorm R i k P • Mult.heckeOn (R.MW i (sg0 D A3.A)) Rr
        ((R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) ((SideTies.fiOf R i' i h).e x))) := by
  subst h
  exact hAd α Rr hd x

variable {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw}

theorem heckeAt_of_scaledAt (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    {ρ : Setup D.ntw} (hpin : RealPin Rl cG ρ) (hIs : Rl.toRealDat.toLevCh.Is A3.A.μ0)
    (hA : Rl.AllPlaces) (hρ : ρ.Good) {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)}
    {u} (hδ : IsDeltaInv ρ u) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ)
    (hs : NX.HeckeStabR S ((j : ℕ) + 1) (hL ((j : ℕ) + 1))) {k : ℕ} {P : PlE D.host} (hk : HkIdx i k P)
    (hr : ∀ (α : GA D (Wc D j)) (R : Finset (GA D (Wc D j))), IsHeckeAt (Wc D j) P k α →
      Bridge.IsDC (Formalism.IndefR.Lev.levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv)) α R → ∀ x : S.WL ((j : ℕ) + 1),
        (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e (hL ((j : ℕ) + 1) k P x))) =
          ((((Rl.C.mu0 j).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (Formalism.L2.DIV.kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹) •
            Mult.heckeOn (Rl.MW j (sg0 D A3.A)) R ((Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e x))))
    {f g : D.nexp.Fm i ((j : ℕ) + 1) b}
    (e1 : YS.eF i _ b (Nat.le_add_left _ _) j.2 g = (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k •
      NX.hkFR S i _ b (hL _) hs k P (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)) :
    HeckeAt (realRd YS v₀ hρ i j b ν) k P f g := by
  rintro α R z ⟨hα, hR, hz⟩
  funext x
  rw [Setup.hecke_apply]
  have hδ' := hδ i j b k P hk α z hα hz
  obtain ⟨hk1, hkr, hsp, hP⟩ := hk
  have ho := GlobalTheory.ExportPin.Model.covered_of_allPlaces Rl hIs hA i P hP hsp
  have hR' : Bridge.IsDC (Formalism.IndefR.Lev.levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv)) α R :=
    GlobalTheory.PrincipalLevel.levK_eq_levG hpin i j b ▸ hR
  have hw : ∀ w, evW YS v₀ j (hL ((j : ℕ) + 1) k P w) =
      ((((Rl.C.mu0 j).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (Formalism.L2.DIV.kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹) •
        fun x => ∑ γ ∈ R, evW YS v₀ j w (x * γ) := by
    intro w
    have := hr α R hα hR' w
    exact congrArg (fun T => T (v₀ j _)) this
  have hmu : (((ρ.B i j b).mu0 z : Circle) : ℂ) = (((Rl.C.mu0 j).val P : ℂˣ) : ℂ) ^ k := by
    rw [hpin.mu0 i j b]
    refine GlobalTheory.HeckeDetChar.chi_detAt (hIs.mu0 j) (Q := Rl.Pg) ?_ ?_ ?_ hα hz
    · have := (hρ.base i j b).unram
      rwa [hpin.Pg i j b, hpin.mu0 i j b] at this
    · obtain ⟨Q, h1, -, h3⟩ := (hρ.base i j b).places.split
      exact hpin.Pg i j b ▸ h3.mono h1
    · have hA' : Rl.Sb = Rl.Pg := hA
      rw [← hA']; exact ho
  have hrk : (Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  change ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 g) x = _
  rw [e1]
  erw [evK_smul YS v₀ hρ i j b ((algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k)]
  erw [evK_hkFR YS v₀ hρ i j b (hL ((j : ℕ) + 1)) hs k P R _ hw]
  have he : ρ.e i b ((algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k) = ρ.eO i b (u i b P) ^ k := by
    rw [map_pow]; rfl
  have hm : (((ρ.B i j b).mu z : Circle) : ℂ) =
      (((ρ.B i j b).mu0 z : Circle) : ℂ) * (((ρ.B i j b).de.chi z : Circle) : ℂ) := by
    rw [Base.mu, MonoidHom.mul_apply, Circle.coe_mul]
  have hr1 : ∀ y, realRd YS v₀ hρ i j b ν f y =
      ν⁻¹ * evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f) y := fun _ => rfl
  have hq : normV P = Nat.card (Formalism.L2.DIV.kP P) := rfl
  simp only [hr1, Pi.smul_apply, smul_eq_mul, he, hδ', hm, hmu, hrk, hq]
  rw [← Finset.mul_sum]
  ring

theorem heckeRead_ysOf : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0) (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) hL eig θ (Bs : SideB D cf Rw low Pq (ratDatR R cG kKs hk) hL eig θ) (Sb : Finset (PlE D.host)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good), RealPin R cG ρ → R.toRealDat.toLevCh.Is A3.A.μ0 → R.AllPlaces → GlobalTheory.HeightCounting.SerCopy.HkAd R Sb hL → (∀ i, Sb ⊆ D.ntw.S0 i) → ∀ i j b ν, HeckeRead (realRd (GlobalTheory.HeightCounting.SerCopy.ysOf Bs) v₀ hρ i j b ν) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ R cG kKs hk cf Rw low Pq hL eig θ Bs Sb v₀ ρ hρ hpin hIs hA hAd hSb i j b ν
  refine heckeRead_iff.2 fun k P hk' f => ?_
  refine heckeAt_of_scaledAt (ysOf Bs) v₀ hpin hIs hA hρ (HeckePinRead.isDeltaInv_uD hρ hpin) i j b ν
    (Bs.hs _ (Nat.le_add_left _ _) j.2) hk' ?_ ?_
  · intro α Rr hα hR x
    obtain ⟨hk1, hkr, hsp, hP⟩ := hk'
    have hd : HkDat R Sb j k P α Rr :=
      { split := hsp
        offS := fun h => hP (hSb i h)
        odd := fun h2 => hP (hρ.goodSetup_placesOverTwo_subset i h2)
        le := hkr
        elt := hα
        reps := hR }
    exact hkAd_step R Sb _ j (idxOf_succ D j) k P (hL ((j : ℕ) + 1) k P)
      (fun α' Rr' hd' x' => hAd ((j : ℕ) + 1) k P α' Rr' (Nat.le_add_left _ _) j.2 hd' x') α Rr hd x
  · have hu : Bs.cHk i b P = HeckePinRead.uD D i b P := by
      rw [Bs.cHk_del i b P hk'.2.2.2 (HeckePinRead.frobU D P) (HeckePinRead.frobU_spec D P)]
      cases b <;> rfl
    rw [← hu]
    exact Bs.hkEq i _ b (Nat.le_add_left _ _) j.2 k P f hk'.2.2.2 hk'.2.2.1 hk'.2.1

end GlobalTheory.HeightCounting.SerCopy

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
open Formalism.L2.DIV Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.HeightCounting.SideCopy.LamCopy
open GlobalTheory.Mem.R3.Tr



set_option maxRecDepth 100000 in
theorem lam_copy : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyAll D D' ι e → ∀ {cf : CharFrame D} {cf' : CharFrame D'}, SameFrame cf cf' → (∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z) → ∃ Z : GlobalTheory.LamTie.LamDat D', Z.Ok ∧ Z.Teich ∧ Z.C = cf' ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D' ∧ GlobalTheory.LamTie.IsLamTieFull D'.ntw Z := by
  rintro D D' ι e h cf cf' ⟨f1, f2, f3, f4⟩ ⟨⟨C, q, w0, c, chi⟩, hOk, hT, rfl, hq, hF⟩
  have he : ∀ x : ↥D'.LL0, D'.what₂.embLL (x : D'.what₂.LL) = D.what₂.embLL (e x : D.what₂.LL) := fun x => (h.cp.embLL0_eq x).symm
  have nOm := h.cp.gal.Om
  have ninstOm := h.cp.gal.instOm
  have nalgOm := h.cp.gal.algOm
  have nplOm := h.cp.gal.plOm
  have nPlG := h.cp.gal.PlG
  have hR := h.cp.gal.R
  have hhost := h.cp.gal.host
  have hTau := h.cp.Tau
  have heTau := h.cp.eTau
  have hhc := h.cp.hc
  have hinW1 := h.cp.inW1
  have hemb0 := h.cp.emb0
  have hTw := h.cp.set.Tw
  obtain ⟨xcc, _, _, _, _, xalgO0, xtopO0, _, _, _, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, _, xhEig, _, _, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h.cp.set
  have hjL := h.jL
  have hs2 := h.s2
  have hlamG := h.lamG
  have hXv := h.Xv
  have hqs := h.qs
  have hl := h.cp.set.l
  have hO0 := h.cp.set.O0
  have hcrO0 := h.cp.set.crO0
  have hab := h.cp.set.abelian₂
  have hsideL := h.cp.set.sideL
  have hO := h.cp.set.O
  have hcrO := h.cp.set.crO
  have halgO := h.cp.set.algO
  have hS0 := h.cp.set.S0
  cases D; cases D'
  dsimp only at hR hhost
  subst hR; subst hhost
  rename Rows.Data _ => r1; cases r1; rename Rows.Data _ => r2; cases r2
  dsimp only at hTau
  subst hTau
  dsimp only at heTau hhc
  subst heTau; subst hhc
  rename NData _ _ _ => nd1; cases nd1
  rename NData _ _ _ => nd2; cases nd2
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  rename NTw _ _ _ _ _ => n1; cases n1
  rename NTw _ _ _ _ _ => n2; cases n2
  dsimp only at xcc
  subst xcc
  dsimp only at hTw hl hO0 hcrO0 hab hsideL hO hcrO halgO hS0
  subst hTw; subst hl; subst hO0; subst hcrO0; subst hab; subst hsideL; subst hO; subst hcrO; subst hS0
  dsimp only at xalgO0 xtopO0 xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS xhEig xRCG xgrpRCG xfinRCG xart xth hjL hs2 hlamG hXv hqs halgO
  subst xalgO0; subst xtopO0; subst halgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst xhEig; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  subst hjL; subst hs2; subst hlamG; subst hXv; subst hqs
  cases C; cases cf'  
  dsimp only at f1 f2 f3 f4
  subst f1; subst f2; subst f3; subst f4
  refine ⟨⟨_, q, w0, c, chi⟩, ⟨(by with_unfolding_all exact (hOk.places :)), (by with_unfolding_all exact (hOk.aux :)), (by with_unfolding_all exact (hOk.big :))⟩, (by with_unfolding_all exact (hT :)), rfl, (by with_unfolding_all exact (hq :)), fun i hi => ?_⟩
  obtain ⟨t0, j, t1, t2⟩ := hF i ((hinW1 i i HEq.rfl).2 hi)
  refine ⟨(by with_unfolding_all exact (t0 :)), (by with_unfolding_all exact (j :)), fun x => ?_, (by with_unfolding_all exact (t2 :))⟩
  exact (congrArg j (he x)).trans ((t1 (e x)).trans ((by with_unfolding_all exact ((congrArg (GlobalTheory.ToricDenom.toBar _ i) (eq_of_heq (hemb0 i i HEq.rfl x))) :))))

end GlobalTheory.HeightCounting.SideCopy.LamCopy
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

theorem _root_.GlobalTheory.T.splitPlaceSupport_level_standardCoordinates : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (v : HeightOneSpectrum (𝓞 X.toD7.host.F)) (Pb : HeightOneSpectrum (𝓞 X.toD7.host.E)) (hPb : Formalism.L2.Col.conjPrime₂ Pb = x.1.1.1) (hv : Formalism.L2.Col.IsOver v Pb) (g : Bridge.Gf (Vc X.toD7 i)) (u : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) (hg : castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((g : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹),
    ((envL X I hX U Xg tr L cV i t).isLoc x g ↔
      ∀ w : HeightOneSpectrum (𝓞 X.toD7.host.F), w ≠ v →
        Formalism.UG.bc (Formalism.UG.prV (E := X.toD7.host.E) w) (u : GL (Fin X.B.R.nV) (EA X)) = 1) ∧
    ((envL X I hX U Xg tr L cV i t).isLoc x g →
      (g ∈ (envL X I hX U Xg tr L cV i t).lev.J ↔ u ∈ Formalism.L2.Col.mhlKv X.toD7.sp.cm X.B.R.nV v)) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.SplitLoc.loc_iff | exact GlobalTheory.Mem.R3.LiftBrg.SplitLoc.loc_iff | (intros; apply GlobalTheory.Mem.R3.LiftBrg.SplitLoc.loc_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th

namespace GlobalTheory.Mem.WeilExists

theorem weilEx_of_weilRepresentation : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ D : D7, WeilEx D := fun h D =>
  weilEx_of
    (GlobalTheory.Mem.WeilTransport.weilCoreEx_of_datum D fun ψ hψ S T χS χT h1 h2 h3 h4 => h D ψ S T χS χT hψ h1 h2 h3 h4)
    (GlobalTheory.T.weilRepresentationRules_hold D)

end GlobalTheory.Mem.WeilExists
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.linksAnalyticHypotheses_of_weilRep_harishChandra : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, Inputs D := by
  first | exact @GlobalTheory.LinksInputs.inputs_of_hypotheses | exact GlobalTheory.LinksInputs.inputs_of_hypotheses | (intros; apply GlobalTheory.LinksInputs.inputs_of_hypotheses <;> assumption)
end
