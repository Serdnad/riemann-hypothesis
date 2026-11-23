module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2192
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.Columns.Bundle012
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.LocalToGlobal.IndefiniteReal.Bundle006
import Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartFamily
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.CoordRat
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle517
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle518
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
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.ActExt

open Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.LevelActionPinned
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

private theorem congr_of_two_lifts {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1)
    {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} (hL : V.rank = L.r) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} (hM0 : M ≠ 0) {Mb Mh : Ideal (𝓞 D.host.E)}
    (hMb : Mb = ∏ PP ∈ L.Pg, PP.asIdeal) (hM : Mb * Mh = Ideal.span {(M : 𝓞 D.host.E)}) (hcop : Mb ⊔ Mh = ⊤)
    {g0 : Formalism.L2.DIV.G0 L.Pg L.r} {u u' : La →ₗ[𝓞 D.host.E] La}
    (hu : ∃ κ, Lev.IsLevelLift V β L g0 κ ∧ ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (u a)) - (finHom V κ).1.mulVec (finVec V (ι a)) = M • w)
    (hu' : ∃ κ, Lev.IsLevelLift V β L g0 κ ∧ ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (u' a)) - (finHom V κ).1.mulVec (finVec V (ι a)) = M • w) (a : La) :
    u' a - u a ∈ Mb • (⊤ : Submodule (𝓞 D.host.E) La) := by
  obtain ⟨κ, hκ, h1⟩ := hu
  obtain ⟨κ', hκ', h1'⟩ := hu'
  have hM₁ : (∏ PP ∈ L.Pg, PP.asIdeal) * Mh = Ideal.span {(M : 𝓞 D.host.E)} := by rw [← hMb, hM]
  have hMm : (M : 𝓞 D.host.E) ∈ Mb :=
    Ideal.mul_le_left (I := Mb) (J := Mh) (by rw [hM]; exact Ideal.mem_span_singleton_self _)
  have hst := mulVec_mem_of_St hβ (Formalism.L2.DIV.parLev_St hκ.2.1)
  have hd := Lev.lift_div_mem hκ hκ'
  obtain ⟨s, hs, v, hv, huv⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ Mb ⊔ Mh)
  have hva : v • a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La) := Submodule.smul_mem_smul hv Submodule.mem_top
  obtain ⟨w₁, hw₁, e₁⟩ := h1 _ hva
  obtain ⟨w₂, hw₂, e₂⟩ := h1' _ hva
  obtain ⟨w₃, hw₃, e₃⟩ := lift_one_congr (L := L) hβ hL hι hM₁ hd.2.1 (Subgroup.mem_bot.1 hd.2.2) _ hva
  have e₄ : (finHom V κ').val = (finHom V κ).val * (finHom V (κ⁻¹ * κ')).val := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  have e₅ : fvec V ι (u' (v • a) - u (v • a)) = M • (w₂ - w₁ + (finHom V κ).val *ᵥ w₃) := by
    have e₁' : fvec V ι (u (v • a)) - (finHom V κ).val *ᵥ fvec V ι (v • a) = M • w₁ := e₁
    have e₂' : fvec V ι (u' (v • a)) - (finHom V κ').val *ᵥ fvec V ι (v • a) = M • w₂ := e₂
    rw [smul_add, smul_sub, ← Matrix.mulVec_smul, ← e₁', ← e₂', ← e₃, map_sub, e₄, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    abel
  obtain ⟨x, hx⟩ := exists_eq_nsmul hι hM0 _ _ (add_mem (sub_mem hw₂ hw₁) (hst _ hw₃)) e₅
  have e₆ : u' a - u a = s • (u' a - u a) + (M : 𝓞 D.host.E) • x := by
    rw [Nat.cast_smul_eq_nsmul, ← hx, map_smul, map_smul, ← smul_sub, ← add_smul, huv, one_smul]
  rw [e₆]
  exact add_mem (Submodule.smul_mem_smul hs Submodule.mem_top) (Submodule.smul_mem_smul hMm Submodule.mem_top)

private theorem latEmb_iota {D : D7} (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) : LatEmb (Wc D i) (iotaW T i) := by
  have key : ∀ (V : HSp D) (_ : T.V ((i : ℕ) + 1) T.toCore.σ₀ = V) (hr : V.rank = D.R.r),
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) := by
    rintro V rfl hr
    obtain ⟨_, -, -, -, -, -, -, hemb, -⟩ := hT.adPin _ (inR i) _ T.toCore.good_σ₀
    exact hemb
  exact key _ (hT.spaceW _ (inR i) _ T.toCore.good_σ₀) (rank_Wc i)

private theorem act_heq_of_equal_data {D : D7} (i : Fin D.R.m)
    {β β' : ∀ i, GL (Fin (Wc D i).rank) (Lev.EAf D)} (eβ : β' = β)
    {Λ : Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E)} (hβ : IsSDFrame (Wc D i) (β i) Λ 1)
    {Pg Pg' : Finset (Formalism.L2.DIV.Pl D.host.E)} (eP : Pg' = Pg)
    {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (hH : H' = H) {l : Level H} {l' : Level H'} (hl : HEq l' l)
    {c : Coeff l} {c' : Coeff l'} (hc : HEq c' c) {Dw : ℕ → Datum H} {Dw' : ℕ → Datum H'} (hDw : HEq Dw' Dw)
    {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'} (hXo : HEq Xo' Xo)
    {ι : ∀ j, (Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)} {ι' : ∀ j, (Dw' j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)}
    (hι : HEq ι' ι)
    (hemb : LatEmb (Wc D i) (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ ι ((i : ℕ) + 1)))
    (hMb : l.Mb = ∏ PP ∈ Pg, PP.asIdeal)
    {G : Type} [Group G] {eG : G ≃* G0 Pg D.R.r} {eG' : G ≃* G0 Pg' D.R.r} (heG : HEq eG' eG)
    {lev : G → (Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Dw ((i : ℕ) + 1)).La}
    {lev' : G → (Dw' ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Dw' ((i : ℕ) + 1)).La}
    (hlev : ∀ g, ∃ κ, Lev.IsLevelLift (Wc D i) (β i)
        (datY _ D.R.r D.R.t 0 (r_le_rank_Wc i) Pg ∅ (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.B) (eG g) κ ∧
      ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) (Dw ((i : ℕ) + 1)).La), ∃ w ∈ latGHat (Wc D i) 1,
        finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ ι ((i : ℕ) + 1)) (lev g a)) -
          (finHom (Wc D i) κ).1.mulVec
            (finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ ι ((i : ℕ) + 1)) a)) = l.M • w)
    (hlev' : ∀ g, ∃ κ, Lev.IsLevelLift (Wc D i) (β' i)
        (datY _ D.R.r D.R.t 0 (r_le_rank_Wc i) Pg' ∅ (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.B) (eG' g) κ ∧
      ∀ a ∈ Mfr l' • (⊤ : Submodule (𝓞 D.host.E) (Dw' ((i : ℕ) + 1)).La), ∃ w ∈ latGHat (Wc D i) 1,
        finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ ι' ((i : ℕ) + 1)) (lev' g a)) -
          (finHom (Wc D i) κ).1.mulVec
            (finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ ι' ((i : ℕ) + 1)) a)) = l'.M • w)
    (g : G) (r : Rul (Xo ((i : ℕ) + 1)) c) (r' : Rul (Xo' ((i : ℕ) + 1)) c') (hr : HEq r' r) :
    HEq (actLev (Xo := Xo' ((i : ℕ) + 1)) c' (fun g => (lev' g, LinearMap.id)) g r')
      (actLev (Xo := Xo ((i : ℕ) + 1)) c (fun g => (lev g, LinearMap.id)) g r) := by
  subst eβ eP hH
  obtain rfl := eq_of_heq hl
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hDw
  obtain rfl := eq_of_heq hXo
  obtain rfl := eq_of_heq hι
  obtain rfl := eq_of_heq heG
  obtain rfl := eq_of_heq hr
  have key : ∀ g a, lev' g a - lev g a ∈ l'.Mb • (⊤ : Submodule (𝓞 D.host.E) (Dw' ((i : ℕ) + 1)).La) := fun g a =>
    congr_of_two_lifts
      (L := datY _ D.R.r D.R.t 0 (r_le_rank_Wc i) Pg' ∅ (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.B)
      hβ (rank_Wc i) hemb (by have := l'.three_le; omega) hMb l'.prod l'.coprime (hlev g) (hlev' g) a
  have e : (fun {S : Type} [CommRing S] [Algebra c'.F S] (g : G) (y y' : FrPt (Xo' ((i : ℕ) + 1)) c' S) =>
        levActR (Xo := Xo' ((i : ℕ) + 1)) (c := c') (fun g => (lev' g, LinearMap.id)) g y y') =
      fun {S : Type} [CommRing S] [Algebra c'.F S] (g : G) (y y' : FrPt (Xo' ((i : ℕ) + 1)) c' S) =>
        levActR (Xo := Xo' ((i : ℕ) + 1)) (c := c') (fun g => (lev g, LinearMap.id)) g y y' := by
    funext S _ _ g y y'
    exact propext (GlobalTheory.LevelActionOfLifts.levR_congr (key g) y y')
  unfold actLev
  rw [e]

private theorem geo_facts {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {ph : Fin D.R.m → ℂ}
    (B : GlobalTheory.RealGeo.GeoHalf T R ph) (i : Fin D.R.m) :
    LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) (B.O i).lev ∧ T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal ∧ LatEmb (Wc D i) (iotaW T i) :=
  ⟨(B.pins i).2.lift.lev, ((B.pins i).2.tuple ()).half.1, latEmb_iota T B.fw.laws i⟩

end GlobalTheory.Mem.R3.ActExt


theorem _root_.GlobalTheory.T.levelActions_on_liftRules_extendedData : StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px), HEq g' g →
        ∀ (r : z.core.R ((j : ℕ) + 1)) (r' : z'.core.R ((j' : ℕ) + 1)), HEq r' r →
          HEq (Formalism.L2.Pj.actLev z'.core.Q.c (z'.geo.O j').lev2 g' r') (Formalism.L2.Pj.actLev z.core.Q.c (z.geo.O j).lev2 g r) := by
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE hf _ hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ hx j j' hj g g' hg r r' hr => ?_
  obtain ⟨h1, h3, h4⟩ := GlobalTheory.Mem.R3.ActExt.geo_facts z.geo j
  obtain ⟨h2, -, -⟩ := GlobalTheory.Mem.R3.ActExt.geo_facts z'.geo j'
  have h5 := z.lev.is.βW j
  have hB := hE.1
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have e : j' = j := Fin.ext hj.symm
  subst e
  cases w with | mk px => ?_
  cases w' with | mk px' => ?_
  dsimp only at hpx px px'
  cases hpx
  have eg : g' = g := eq_of_heq hg
  subst eg
  exact GlobalTheory.Mem.R3.ActExt.act_heq_of_equal_data j' (eq_of_heq hx.βW) h5 (eq_of_heq hx.Pg) (eq_of_heq hx.H)
    hx.l hx.c hx.Dw hx.Xo hx.iota h4 h3 hx.eG h1 h2 g' r r' hr
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.DefLatBC

theorem unipotentBaseLevelChar_map_coefficientField {E : Type} [Field E] [NumberField E] {K K' : Type} [Field K] [Field K'] (φ : K →+* K') (Pg : Finset (Pl E)) (r : ℕ)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) K) (ψ' : ∀ PP : Pl E, AddChar (kP PP) K') (h : ∀ PP c, ψ' PP c = φ (ψ PP c))
    (g : G0 Pg r) (hg : g ∈ (P0 Pg r ψ).H) (hg' : g ∈ (P0 Pg r ψ').H) :
      ((((P0 Pg r ψ').chi⁻¹ ⟨g, hg'⟩ : K'ˣ)) : K') = φ (((P0 Pg r ψ).chi⁻¹ ⟨g, hg⟩ : Kˣ) : K) := by
  simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]
  congr 1
  unfold P0 LevelP.ofLocal at *
  dsimp only
  rw [MonoidHom.finsetProd_apply, MonoidHom.finsetProd_apply, Units.coe_prod, Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun PP _ => ?_
  exact h _ _

theorem exists_int_of_mem_vGs {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} (hPr : Pr.Ok) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ Pr.vGs) (x : 𝓞 X.E ⧸ P.asIdeal) : ∃ b : ℤ, x = b := by
  classical
  have h : ∃ i, P ∈ Pr.vG i := by
    unfold Formalism.L2.Col.Primes.vGs at hP
    rcases Finset.mem_union.1 hP with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := h
  have hc : Nat.card (𝓞 X.E ⧸ P.asIdeal) = Pr.g i := by
    rw [← hPr.vG_norm i P hi, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 X.E ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ (hPr.g_prime i).ne_zero)
  exact Formalism.L2.Col.owedC_exists_int (hPr.g_prime i) hc x

theorem baseLevels_correspond_weilAdditiveChars {B B' : Base} {px : PreX B.toPre} {px' : PreX B'.toPre} (I : ColIn B px) (I' : ColIn B' px')
    (hB : B'.toPre = B.toPre) (hpx : HEq px' px) (hPr : (B.primes px).Ok) (hw : I.Ch.WeilTied B.embLL B.host.xi0)
    (hw' : I'.Ch.WeilTied B'.embLL B'.host.xi0)
    (φ : B.LL →+* B'.LL) (hφ : ∀ x, B'.embLL (φ x) = B.embLL x) (e : Gc B px ≃* Gc B' px') (he : ∀ g, HEq (e g) g) :
    ∃ hP : lev0 I' = (lev0 I).map e.toMonoidHom, ∀ h : lev0 I,
      (((chr0 I')⁻¹ ⟨e h, hP ▸ Subgroup.mem_map_of_mem e.toMonoidHom h.2⟩ : B'.LLˣ) : B'.LL) =
        φ (((chr0 I)⁻¹ h : B.LLˣ) : B.LL) := by
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  obtain rfl : px' = px := eq_of_heq hpx
  have he' : e = MulEquiv.refl _ := MulEquiv.ext fun g => eq_of_heq (he g)
  subst he'
  refine ⟨(Subgroup.map_id _).symm, fun h => ?_⟩
  refine unipotentBaseLevelChar_map_coefficientField φ _ _ (psiC I) (psiC I') (fun PP c => ?_) h.1 h.2 h.2
  unfold psiC
  split_ifs with hP hQ hQ
  · obtain ⟨b, hb⟩ := exists_int_of_mem_vGs hPr hP (Formalism.L2.Col.redP PP P'.host.xi0 * c)
    apply RingHom.injective (Base.embLL _)
    exact (hw' ⟨PP, hP⟩ c b hb).trans ((hφ _).trans (hw ⟨PP, hP⟩ c b hb)).symm
  · exact absurd hP hQ
  · exact absurd hQ hP
  · rw [AddChar.one_apply, AddChar.one_apply, map_one]



theorem lev_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (e : Gc B w.px ≃* Gc B' w'.px), (∀ g, HEq (e g) g) → ∃ hP : ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.lvlA z'.F.P0 z'.F.ψ0).P = ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).P.map e.toMonoidHom, ∀ h : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).P, ((((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.lvlA z'.F.P0 z'.F.ψ0).ψ ⟨e h, hP ▸ Subgroup.mem_map_of_mem e.toMonoidHom h.2⟩ : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL) = φ (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).ψ h : (w.st Z).toD7.what₂.LL)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' _ φ hφ e he => ?_
  exact baseLevels_correspond_weilAdditiveChars w.I w'.I hE.1 hpx w.l.pr w.ok.weil w'.ok.weil φ hφ e he

end GlobalTheory.Mem.R3.DefLatBC

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftMatBase

section Gen

open Formalism.IndefR.CxPass LevelOperators

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 K G Pl0 I0 Ty T m} {X : CxData A3.fam3.amb3}
  {P1 : Subgroup G} {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)}
  {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)} {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}

theorem dnLevL_of_ratZL {s : ℕ} (hok : A3.fam3.Ok3 s) {gW : ∀ j, Representation ℂ G (X.W j)}
    (Hs : ∀ j t, Hyp A3.fam3.base3.v0.embedding (X.jL j t) (A3.fam3.F.L j t).r (fun g => X.opLC j t (Sum.inr g)) (gW j)
      (X.θ' j t))
    (hRZ : ∀ j t, Submodule.span ℂ ((X.jL j t) '' (X.Zl j t : Set (A3.fam3.amb3.FL j t))) =
      LinearMap.range (LinearMap.adjoint (X.θ' j t)))
    {cv : CrdV A3.fam3.amb3} {b : Bool} (P : Subgroup G) (ψ : P →* Kˣ)
    (hv : ∀ j t, cv.v0L X.zs b j t = BlockGood.goodR (A3.fam3.F.L j t) (A3.fam3.F.lvlA P ψ))
    (hE : LevelTypeOfLifts A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW b P ψ) :
    X.DnLevL cv b := by
  intro j t
  rintro _ ⟨u, hu, rfl⟩
  have hu0 : u ∈ Submodule.span ℂ (X.jL j t '' (BlockGood.goodR (A3.fam3.F.L j t) (A3.fam3.F.lvlA P ψ) : Set _)) := by
    have := hu
    unfold CxData.goodPartComplexPoints at this
    rwa [hv j t] at this
  rw [lift_good_part_complex_eq_range_family (Hs j t) (hv j t)] at hu
  rw [hE j]
  refine ⟨?_, ?_⟩
  · have hle : LinearMap.range (opV A3.fam3.base3.v0.embedding (fun g => X.opLC j t (Sum.inr g))
          (goodAt (A3.fam3.F.lvlA P ψ).X (A3.fam3.F.lvlA P ψ).P (A3.fam3.F.lvlA P ψ).ψ)) ≤
        LinearMap.range (opV A3.fam3.base3.v0.embedding (fun g => X.opLC j t (Sum.inr g))
          (goodAt (A3.fam3.F.lvlA ⊥ 1).X (A3.fam3.F.lvlA ⊥ 1).P (A3.fam3.F.lvlA ⊥ 1).ψ)) := by
      have e1 : goodAt (A3.fam3.F.lvlA ⊥ 1).X (A3.fam3.F.lvlA ⊥ 1).P (A3.fam3.F.lvlA ⊥ 1).ψ = idemOf A3.fam3.F.X :=
        goodAt_bot A3.fam3.F.X _
      rw [e1]
      exact (Hs j t).range_le A3.fam3.F.X P ψ⁻¹
    obtain ⟨u', hu', hΘ⟩ := (Hs j t).dn _ (opF_goodAt_idem _ (A3.fam3.F.lvlA ⊥ 1).X hok.ok2.irr _ _) (hle hu)
    rw [← (Hs j t).ratLev (hRZ j t) _ (opF_goodAt_idem _ (A3.fam3.F.lvlA ⊥ 1).X hok.ok2.irr _ _)] at hu'
    have hZeq : ((LinearMap.range (LinearMap.adjoint (X.θ' j t))).comap (X.jL j t) ⊓
          LinearMap.range (opF (A3.fam3.F.L j t).r (goodAt (A3.fam3.F.lvlA ⊥ 1).X (A3.fam3.F.lvlA ⊥ 1).P (A3.fam3.F.lvlA ⊥ 1).ψ))) =
        LinearMap.range ((A3.fam3.F.L j t).toF (A3.fam3.F.lvlA ⊥ 1) (X.Zl j t)) := by
      rw [range_toF, goodR_eq]
      rfl
    rw [hZeq] at hu'
    have h2 : Submodule.span ℂ (X.jL j t '' (LinearMap.range ((A3.fam3.F.L j t).toF (A3.fam3.F.lvlA ⊥ 1) (X.Zl j t)) :
          Set _)) ≤ LinearMap.range (lin (X.uL (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t)) := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨cpt A3.fam3.base3.v0.embedding x, (X.jL_toL (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t x).symm⟩
    obtain ⟨c, hc⟩ := h2 hu'
    show X.θ' j t u ∈ principalFormsSubspace A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) j
    refine Submodule.mem_iSup_of_mem t ?_
    rw [← hΘ, ← hc, ← X.tC_eq]
    exact ⟨c, rfl⟩
  · show X.θ' j t u ∈ typeSubspace A3 X j (gW j) P ψ⁻¹
    unfold typeSubspace
    rw [Submodule.mem_iInf]
    intro h
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    refine (Hs j t).type (h : G) (((ψ⁻¹) h : Kˣ) : K) _ (fun x hx => ?_) hu0
    rw [goodR_eq] at hx
    exact opF_goodAt_type _ _ hok.ok2.irr P ψ⁻¹ h x hx

end Gen

section Conc

open Formalism.IndefR.CxPass

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem tC_single_mem (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hL : Rw.HoldsL R F)
    (j : Fin D.R.m) (k : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ j A3.A.μ0)) :
    (R.toCx3 F).tC F.cr false j A3.A.μ0 (Pi.single k 1) ∈ LinearMap.range ((R.toCx3 F).w0C false j) := by
  have kL := RealDat3.kFormL_of (F := F) hC.base.models
  have jL := RealDat3.jIsoL_of (F := F) hC.base.models
  have rz : ∀ j t, Submodule.span ℂ (((R.toCx3 F).jL j t) '' ((R.toCx3 F).Zl j t : Set (A3.fam3.amb3.FL j t))) =
      LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' j t)) := fun j t => by
    obtain ⟨N, ψ, hψ, hr⟩ := hL.liftTest j
    exact Formalism.IndefR.Rat.range_adjoint_rat A3.fam3.base3.v0.embedding ((R.toCx3 F).jL j t)
      ((cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1).hL j t) _ (kL j t).1 (kL j t).2 (jL j t) _ ψ hψ (fun i x => hr t i x)
  have hdn : (R.toCx3 F).DnLevL (cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1) false :=
    dnLevL_of_ratZL (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) hL.ok
      (fun j t => lift_hypotheses_of_unitary hL.ok kL (cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1) (fun _ _ _ _ => rfl) jL hL.gUnit.2 hL.gEquiv.2 j t)
      rz F.P0 F.ψ0 (fun _ _ => rfl) hL.levW
  rw [Formalism.IndefR.Cx.CxData.tC, Formalism.IndefR.Cx.lin_single]
  exact hdn j _ ⟨_, Submodule.subset_span ⟨_, lift_coordinates_in_good_part_family (P0 := F.P0) (ψ0 := F.ψ0) (P1 := F.P1) (ψ1 := F.ψ1)
    (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) (R.toCx3 F) false j _ (Pi.single k 1), rfl⟩, rfl⟩

theorem liftMatC_isRat (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hL : Rw.HoldsL R F) (j : Fin D.R.m) :
    Formalism.IndefR.Cx.IsRat A3.fam3.base3.v0.embedding ((R.toCx3 F).liftMatC F.cr false j A3.A.μ0) := by
  intro i k
  obtain ⟨N, ψ, hψ, hr, hbase⟩ := hL.liftTestB j
  have hinj := (R.toCx3 F).principal_form_injective false (RealDat3.kForm_of (F := F) hL.unif false) (RealDat3.ewNorm false)
    (RealDat.nP_pos false) j
  have hmem := tC_single_mem R F hC hL j k
  obtain ⟨a, ha⟩ := Formalism.IndefR.Rat.coord_rat _ ψ hψ ((R.toCx3 F).w0C false j) hinj (fun i l => hbase i l)
    (Formalism.IndefR.Cx.solve ((R.toCx3 F).w0C false j) ((R.toCx3 F).tC F.cr false j A3.A.μ0 (Pi.single k 1)))
    (fun i' => by
      rw [Formalism.IndefR.Cx.solve_spec _ hmem, Formalism.IndefR.Cx.CxData.tC, Formalism.IndefR.Cx.lin_single]
      exact hr _ _ _) i
  exact ⟨a, by simpa [Formalism.IndefR.Cx.CxData.liftMatC, Formalism.IndefR.Cx.relMat] using ha⟩

theorem liftMatrix_computes_lift_rational (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hL : Rw.HoldsL R F) (j : Fin D.R.m)
    (x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ j A3.A.μ0) → D.what₂.LL) :
    (R.toCx3 F).w0C false j (Formalism.IndefR.Cx.cpt A3.fam3.base3.v0.embedding
        (((R.toCx3 F).liftMat F.cr false j A3.A.μ0).mulVec x)) =
      (R.toCx3 F).tC F.cr false j A3.A.μ0 (Formalism.IndefR.Cx.cpt A3.fam3.base3.v0.embedding x) := by
  rw [Formalism.IndefR.Cx.cpt_mulVec, Formalism.IndefR.Cx.CxData.liftMat, Formalism.IndefR.Cx.kMat_map _ (liftMatC_isRat R F hC hL j)]
  exact Formalism.IndefR.Cx.relMat_spec _ _ (tC_single_mem R F hC hL j) _

end Conc


theorem baseLevelLiftMatrix_solves_relation_extendedData : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ x : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL, (z.R.toCx3 z.F).w0C false j (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding ((s0Of z.R z.F).θ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 *ᵥ x)) = (z.R.toCx3 z.F).tC z.F.cr false j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding x)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ => ?_
  intro B f T w _ _ _ _ Z hX Wt z _ _ _ hHL _ _ _ _ _ _ _ _ _ _ _ _ _ x
  exact liftMatrix_computes_lift_rational z.R z.F z.pins.char hHL _ x

end GlobalTheory.Mem.R3.LiftMatBase
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

theorem GlobalTheory.Mem.R3.DefLatBC.typePrimeFiniteGroup_heq_of_eq_preData (B B' : Base) (px : PreX B.toPre) (px' : PreX B'.toPre) (h : B'.toPre = B.toPre) (hp : HEq px' px) :
    ∃ e : Gc B px ≃* Gc B' px', ∀ g, HEq (e g) g := by
  cases B
  cases B'
  dsimp only at h
  subst h
  cases hp
  exact ⟨MulEquiv.refl _, fun g => HEq.rfl⟩

theorem GlobalTheory.Mem.R3.DefLatBC.gc_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ e : Gc B w.px ≃* Gc B' w'.px, ∀ g, HEq (e g) g) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ hp => ?_
  intros
  exact GlobalTheory.Mem.R3.DefLatBC.typePrimeFiniteGroup_heq_of_eq_preData B B' w.px w'.px hE.1 hp
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem _root_.GlobalTheory.T.finiteHom_eq_of_frames_keep_matrices : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P P' : principalLevelFrame.RowPsi V n), GlobalTheory.MtRead.IdFrame hF P → GlobalTheory.MtRead.IdFrame hF P' → ∀ g, (finHom V).rangeRestrict (P.ψ g) = (finHom V).rangeRestrict (P'.ψ g) := by
  first | exact @GlobalTheory.FrameFinPart.finHom_eq_of_idFrame | exact GlobalTheory.FrameFinPart.finHom_eq_of_idFrame | (intros; apply GlobalTheory.FrameFinPart.finHom_eq_of_idFrame <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

theorem _root_.GlobalTheory.T.definiteThetaLift_continuous_invariant_hasDerivAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → (∀ τ, (gramAt D S τ).PosDef) → ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)), (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h) → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → (Continuous (lift om ν 𝓕 fun h => L (F h)) ∧ ∀ γ ∈ GQ T, ∀ g, lift om ν 𝓕 (fun h => L (F h)) (γ * g) = lift om ν 𝓕 (fun h => L (F h)) g) ∧ ∀ τ, ∀ Y ∈ lieAt T τ, ∃ L' : X →ₗ[ℂ] (WO S T → ℂ), (∀ x, IsThetaFunO ψ S T (L' x)) ∧ (∀ x h g, HasDerivAt (fun t : ℝ => thetaKO om h (g * oneP θ T τ Y t) (L x)) (thetaKO om h g (L' x)) 0) ∧ ∀ g, HasDerivAt (fun t : ℝ => lift om ν 𝓕 (fun h => L (F h)) (g * oneP θ T τ Y t)) (lift om ν 𝓕 (fun h => L' (F h)) g) 0 := by
  first | exact @GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt | exact GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt | (intros; apply GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt <;> assumption)
end
