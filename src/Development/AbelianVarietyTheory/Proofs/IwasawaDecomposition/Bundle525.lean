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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.ChiExt

theorem res_unique {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {P : Pl E} {c c' : (kP P)ˣ →* ℂˣ}
    (h : ∀ (a : 𝓞 E) (k : Eˣ) (u : (kP P)ˣ), (k : E) = a → (u : kP P) = Ideal.Quotient.mk _ a → c u = χ.locK P k)
    (h' : ∀ (a : 𝓞 E) (k : Eˣ) (u : (kP P)ˣ), (k : E) = a → (u : kP P) = Ideal.Quotient.mk _ a → c' u = χ.locK P k) : c = c' := by
  ext1 u
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  have ha0 : (a : E) ≠ 0 := by
    intro h0
    have : a = 0 := by exact_mod_cast h0
    exact u.ne_zero (by rw [← ha, this, map_zero])
  exact (h a (Units.mk0 _ ha0) u rfl ha.symm).trans (h' a (Units.mk0 _ ha0) u rfl ha.symm).symm

theorem prod_eq {B B' : Base} (hB : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} (hf : HEq f' f)
    {px : PreX B.toPre} {px' : PreX B'.toPre} (hpx : HEq px' px) (j : Fin B.R.m) (j' : Fin B'.R.m) (hj : (j : ℕ) = j')
    {Pg : Finset (Pl B.host.E)} {Pg' : Finset (Pl B'.host.E)} (hPg : HEq Pg' Pg)
    (eG : Gc B px ≃* G0 Pg B.R.r) (eG' : Gc B' px' ≃* G0 Pg' B'.R.r) (heG : HEq eG' eG)
    (c : ∀ PP : Pl B.host.E, (kP PP)ˣ →* ℂˣ) (c' : ∀ PP : Pl B'.host.E, (kP PP)ˣ →* ℂˣ)
    (h : ∀ PP ∈ Pg, ∀ (a : 𝓞 B.host.E) (k : B.host.Eˣ) (u : (kP PP)ˣ), (k : B.host.E) = a → (u : kP PP) = Ideal.Quotient.mk _ a →
      (c PP)⁻¹ u = (f.mu0 j).locK PP k)
    (h' : ∀ PP ∈ Pg', ∀ (a : 𝓞 B'.host.E) (k : B'.host.Eˣ) (u : (kP PP)ˣ), (k : B'.host.E) = a → (u : kP PP) = Ideal.Quotient.mk _ a →
      (c' PP)⁻¹ u = (f'.mu0 j').locK PP k)
    (g : Gc B px) (g' : Gc B' px') (hg : HEq g' g) :
    ∏ PP : Pg', ((c' PP.1 (Matrix.GeneralLinearGroup.det (eG' g' PP)) : ℂˣ) : ℂ) =
      ∏ PP : Pg, ((c PP.1 (Matrix.GeneralLinearGroup.det (eG g PP)) : ℂˣ) : ℂ) := by
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  obtain rfl : px' = px := eq_of_heq hpx
  obtain rfl : f' = f := eq_of_heq hf
  obtain rfl : Pg' = Pg := eq_of_heq hPg
  obtain rfl : eG' = eG := eq_of_heq heG
  obtain rfl : g' = g := eq_of_heq hg
  obtain rfl : j = j' := Fin.ext hj
  refine Finset.prod_congr rfl fun PP _ => ?_
  have e : c' PP.1 = c PP.1 := inv_injective (res_unique (h' PP.1 PP.2) (h PP.1 PP.2))
  rw [e]
  rfl



theorem chi_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px), HEq g' g → (((z'.R.toRealDat.FW j').chi g' : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL) = φ (((z.R.toRealDat.FW j).chi g : (w.st Z).toD7.what₂.LLˣ) : (w.st Z).toD7.what₂.LL)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE hf _ hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ hx j j' hj φ hφ g g' hg => ?_
  apply RingHom.injective (w'.st Z').toD7.what₂.embLL
  refine (z'.pins.char.base.grp.chiW j' g').trans (Eq.trans ?_ ((hφ _).trans (z.pins.char.base.grp.chiW j g)).symm)
  have hC : z.R.toLevCh.C.mu0 j = f.mu0 j := by
    rw [z.lev.C, w.C_eq]; rfl
  have hC' : z'.R.toLevCh.C.mu0 j' = f'.mu0 j' := by
    rw [z'.lev.C, w'.C_eq]; rfl
  exact prod_eq hE.1 hf hpx j j' hj hx.Pg z.R.eG z'.R.eG hx.eG (z.R.chi ((j : ℕ) + 1)) (z'.R.chi ((j' : ℕ) + 1))
    (fun PP hP => hC ▸ z.lev.is.chi j PP hP) (fun PP hP => hC' ▸ z'.lev.is.chi j' PP hP) g g' hg

end GlobalTheory.Mem.R3.ChiExt

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


open _root_.Formalism.L2.Col in
theorem repCSD_lift_of_reading {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
    (S : GSD K) (S' : GSD K') (hS : S.Ok) (hS' : S'.Ok) {A A' : Type} [Group A] [Group A']
    (ρ : Representation K A S.EqFun) (ρ' : Representation K' A' S'.EqFun) {T T' : Type} (rd : S.V → T) (rd' : S'.V → T')
    (hrd' : Function.Injective rd') (L : (S.toCSD hS).Forms → (S'.toCSD hS').Forms)
    (hC : ∀ (f : (S.toCSD hS).Forms) (d : S.D) (d' : S'.D), HEq d' d →
      HEq (rd' ((((S'.res hS').symm (L f) : S'.EqFun) : S'.D → S'.V) d')) (rd ((((S.res hS).symm f : S.EqFun) : S.D → S.V) d)))
    (hex : ∀ d' : S'.D, ∃ d : S.D, HEq d' d) (a : A) (a' : A') (t : S.D → S.D) (t' : S'.D → S'.D)
    (hρ : ∀ (φ : S.EqFun) d, (ρ a φ : S.D → S.V) d = (φ : S.D → S.V) (t d))
    (hρ' : ∀ (φ : S'.EqFun) d, (ρ' a' φ : S'.D → S'.V) d = (φ : S'.D → S'.V) (t' d))
    (ht : ∀ (d : S.D) (d' : S'.D), HEq d' d → HEq (t' d') (t d)) (f : (S.toCSD hS).Forms) :
    S'.repCSD hS' ρ' a' (L f) = L (S.repCSD hS ρ a f) := by
  apply (S'.res hS').symm.injective
  apply Subtype.ext
  funext d'
  apply hrd'
  obtain ⟨d, hd⟩ := hex d'
  have e1 : (S'.res hS').symm (S'.repCSD hS' ρ' a' (L f)) = ρ' a' ((S'.res hS').symm (L f)) := by
    simp [GSD.repCSD]
  have e2 : (S.res hS).symm (S.repCSD hS ρ a f) = ρ a ((S.res hS).symm f) := by
    simp [GSD.repCSD]
  rw [e1, hρ']
  have h1 := hC f (t d) (t' d') (ht d d' hd)
  have h2 := hC (S.repCSD hS ρ a f) d d' hd
  rw [e2, hρ] at h2
  exact eq_of_heq (h1.trans h2.symm)

end GlobalTheory.Mem.R3.DefLatBC

namespace GlobalTheory.Mem.R3.DefLatBC


open _root_.Formalism.L2.Col in
theorem decoratedLattice_translates_heq_of_eq_primes {X : Fields} {n r : ℕ} (h : r ≤ n) {SG Q Q' : Finset (HeightOneSpectrum (𝓞 X.E))} (hQ : Q' = Q) :
    (∀ d' : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := uSG SG Q'), ∃ d : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := uSG SG Q), HEq d' d) ∧
    ∀ (g : G0 X.E SG r) (d : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := uSG SG Q)) (d' : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := uSG SG Q')), HEq d' d →
      HEq (((1 : UF X.E n), (extGLG Q' (diagonalEmbeddingProduct SG h g))⁻¹) • d') (((1 : UF X.E n), (extGLG Q (diagonalEmbeddingProduct SG h g))⁻¹) • d) := by
  subst hQ
  exact ⟨fun d' => ⟨d', HEq.rfl⟩, fun g d d' hd => by cases hd; rfl⟩


open _root_.Formalism.L2.Col in
theorem decoratedLattice_translates_heq_of_eq_preData (B B' : Base) (px : PreX B.toPre) (px' : PreX B'.toPre) (h : B'.toPre = B.toPre) (hp : HEq px' px)
    (sel : HeightOneSpectrum (𝓞 B.fields.F) → HeightOneSpectrum (𝓞 B.fields.E))
    (sel' : HeightOneSpectrum (𝓞 B'.fields.F) → HeightOneSpectrum (𝓞 B'.fields.E)) {S S' : Set ℕ}
    (mu : Tup B.fields.F B.fields.E B.fields.K S) (mu' : Tup B'.fields.F B'.fields.E B'.fields.K S')
    (hQ : QE sel (mu : Chr B.fields.F B.fields.E B.fields.K) = ∅)
    (hQ' : QE sel' (mu' : Chr B'.fields.F B'.fields.E B'.fields.K) = ∅) :
    (∀ d' : DecoSet (E := B'.fields.E) (n := B'.R.nV) (ST := ∅) (SG := rowSG (B'.primes px') sel' mu'),
      ∃ d : DecoSet (E := B.fields.E) (n := B.R.nV) (ST := ∅) (SG := rowSG (B.primes px) sel mu), HEq d' d) ∧
    ∀ (g : Gc B px) (g' : Gc B' px'), HEq g' g → ∀ (d : DecoSet (E := B.fields.E) (n := B.R.nV) (ST := ∅) (SG := rowSG (B.primes px) sel mu))
      (d' : DecoSet (E := B'.fields.E) (n := B'.R.nV) (ST := ∅) (SG := rowSG (B'.primes px') sel' mu')), HEq d' d →
      HEq (((1 : UF B'.fields.E B'.R.nV), (unipotentGroupBlockEmbedding (B'.primes px') sel' mu' (r_le_nV B'.R) g')⁻¹) • d')
        (((1 : UF B.fields.E B.R.nV), (unipotentGroupBlockEmbedding (B.primes px) sel mu (r_le_nV B.R) g)⁻¹) • d) := by
  cases B
  cases B'
  dsimp only at h
  subst h
  cases hp
  refine ⟨fun d' => (decoratedLattice_translates_heq_of_eq_primes (r_le_nV _) (hQ'.trans hQ.symm)).1 d', fun g g' hg d d' hd => ?_⟩
  have e := eq_of_heq hg
  subst e
  exact (decoratedLattice_translates_heq_of_eq_primes (r_le_nV _) (hQ'.trans hQ.symm)).2 _ d d' hd

end GlobalTheory.Mem.R3.DefLatBC


theorem GlobalTheory.Mem.R3.DefLatBC.act_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (e : Gc B w.px ≃* Gc B' w'.px), (∀ g, HEq (e g) g) → ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) → (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) → ∀ (g : Gc B w.px) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).r (e g) (L f) = L (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).r g f)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ hp Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' _ φ _ e he L _ hC g f0 => ?_
  have hP := GlobalTheory.Mem.R3.DefLatBC.decoratedLattice_translates_heq_of_eq_preData B B' w.px w'.px hE.1 hp w.I.sel w'.I.sel
    (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1
    (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1
    (Formalism.L2.Col.twistPrimes_trivialTuple_empty _ _) (Formalism.L2.Col.twistPrimes_trivialTuple_empty _ _)
  have hinj : Function.Injective fun v : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V => MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) v.1 :=
    (MvPolynomial.map_injective _ (B'.embLL : B'.fields.K →+* ℂ).injective).comp Subtype.val_injective
  exact GlobalTheory.Mem.R3.DefLatBC.repCSD_lift_of_reading (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)) (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)) (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1)) (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1)) (Formalism.L2.Col.unipotentRightActionFormsV (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)) (Formalism.L2.Col.unipotentRightActionFormsV (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1))
    (fun v => MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) v.1) _ hinj (fun x => L x) hC hP.1 g (e g) _ _ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun d d' hd => hP.2 g (e g) (he g) d d' hd) f0
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.GoodIdemBC

theorem bc_injective {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (ψ : A →+* B)
    (hψ : Function.Injective ψ) : Function.Injective (Formalism.UG.bc (n := n) ψ) := by
  intro x y h
  apply Units.ext
  have h' := congrArg Units.val h
  ext i j
  exact hψ (congrFun (congrFun h' i) j)

theorem eq_of_bc_heq {E : Type} [Field E] [NumberField E] {q r : ℕ} {P1 P2 : Pl E} (h : P1 = P2)
    (ψ1 : ZMod q ≃+* kP P1) (ψ2 : ZMod q ≃+* kP P2) (x y : GL (Fin r) (ZMod q))
    (hxy : HEq (Formalism.UG.bc (ψ1 : ZMod q →+* kP P1) x) (Formalism.UG.bc (ψ2 : ZMod q →+* kP P2) y)) : x = y := by
  subst h
  have e : (ψ1 : ZMod q →+* kP P1) = ψ2 := Subsingleton.elim _ _
  rw [e] at hxy
  exact bc_injective _ ψ2.injective (eq_of_heq hxy)

theorem eG_app_heq {E1 E2 : Type} [Field E1] [Field E2] [NumberField E2] {r : ℕ} {S S' : Finset (HeightOneSpectrum (𝓞 E1))}
    {Pg Pg' : Finset (Pl E2)} (hS : S' = S) (hPg : Pg' = Pg) (eG : Formalism.L2.Col.G0 E1 S r ≃* G0 Pg r)
    (eG' : Formalism.L2.Col.G0 E1 S' r ≃* G0 Pg' r) (he : HEq eG' eG) (g : Formalism.L2.Col.G0 E1 S r) (g' : Formalism.L2.Col.G0 E1 S' r)
    (hg : HEq g' g) (p : Pg) (p' : Pg') (hp : (p' : Pl E2) = p) : HEq (eG' g' p') (eG g p) := by
  subst hS hPg
  cases he
  cases hg
  rw [Subtype.ext hp]



theorem idemOf_coeff_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px), HEq g' g → (idemOf z'.Xg).coeff g' = φ ((idemOf z.Xg).coeff g)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all ?_
  intro K B' f' T' w' hO hFo hP' B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' hEx j j' hj φ hφ g g' hg
  have k1 := z.good.2 g
  have k2 := z'.good.2 g'
  obtain ⟨plg, iso, hplg, -, -, hiso⟩ := z.pins.keep.grp
  obtain ⟨plg', iso', hplg', -, -, hiso'⟩ := z'.pins.keep.grp
  apply (w'.st Z').B.embLL.injective
  refine k2.trans (Eq.trans ?_ ((hφ _).trans k1).symm)
  obtain ⟨P, r⟩ := B
  obtain ⟨P', r'⟩ := B'
  obtain ⟨h1, -⟩ := hE
  dsimp only at h1
  subst h1
  cases hf
  have hp := eq_of_heq hpx
  have hPg := eq_of_heq hEx.Pg
  have key : (z'.R.eG.trans z'.cG) g' = grpEquiv Z.N.naut Z'.N.naut ((z.R.eG.trans z.cG) g) := by
    funext kv'
    obtain ⟨k, v'⟩ := kv'
    obtain ⟨v, rfl⟩ := (plEquiv Z.N.naut Z'.N.naut k).surjective v'
    refine Eq.trans ?_ (grpEquiv_apply' _ _ _ k v).symm
    have hpl : (plg' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩).1 = (plg ⟨k, v⟩).1 := by
      rw [hplg' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩, hplg ⟨k, v⟩]
      exact TypesTrue.plGw_plEquiv hG hG' k v
    refine eq_of_bc_heq hpl (iso' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩) (iso ⟨k, v⟩) _ _ ?_
    refine (heq_of_eq (hiso' g' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩)).symm.trans
      ((eG_app_heq ?_ hPg _ _ hEx.eG g g' hg _ _ hpl).trans (heq_of_eq (hiso g ⟨k, v⟩)))
    exact hp ▸ rfl
  rw [key]
  exact TypesTrue.typeIdempotent_coeff_across_layers hG hG' _

end GlobalTheory.Mem.R3.GoodIdemBC

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section
namespace GlobalTheory.Mem.R3.MKExt
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem cusp_match {E : Type} [Field E] [NumberField E] [IsCMField E] {H H' : Host E} {Dw : ℕ → Datum H}
    {Dw' : ℕ → Datum H'} {l : Level H} {l' : Level H'} {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'}
    {c : Coeff l} {c' : Coeff l'} {r : ℕ} {U : ∀ j (σ : c.F →+* ℂ), Unf (Xo j) c σ r}
    {U' : ∀ j (σ : c'.F →+* ℂ), Unf (Xo' j) c' σ r} (hH : H' = H) (hDw : HEq Dw' Dw) (hl : HEq l' l)
    (hXo : HEq Xo' Xo) (hc : HEq c' c) (hU : HEq U' U) {j j' : ℕ} (hj : j' = j) {a a' : (E →+* ℂ) × ℕ → ℕ} {n n' : ℕ}
    (ha : a' = a) (hn : n' = n) (f' : cusp (Xo' j') c' (U' j') a' n') :
    ∃ f : cusp (Xo j) c (U j) a n, HEq f' f ∧
      ((∀ la, ∀ v ∈ valSet (Xo' j') c' (algCls (Xo' j') c') la, 0 ≤ v (f' : Rul (Xo' j') c')) ↔
        (∀ la, ∀ v ∈ valSet (Xo j) c (algCls (Xo j) c) la, 0 ≤ v (f : Rul (Xo j) c))) := by
  subst hH; cases hDw; cases hl; cases hXo; cases hc; cases hU; subst ha; subst hn; subst hj
  exact ⟨f', HEq.rfl, Iff.rfl⟩

theorem cusp_match' {E : Type} [Field E] [NumberField E] [IsCMField E] {H H' : Host E} {Dw : ℕ → Datum H}
    {Dw' : ℕ → Datum H'} {l : Level H} {l' : Level H'} {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'}
    {c : Coeff l} {c' : Coeff l'} {r : ℕ} {U : ∀ j (σ : c.F →+* ℂ), Unf (Xo j) c σ r}
    {U' : ∀ j (σ : c'.F →+* ℂ), Unf (Xo' j) c' σ r} (hH : H' = H) (hDw : HEq Dw' Dw) (hl : HEq l' l)
    (hXo : HEq Xo' Xo) (hc : HEq c' c) (hU : HEq U' U) {j j' : ℕ} (hj : j' = j) {a a' : (E →+* ℂ) × ℕ → ℕ} {n n' : ℕ}
    (ha : a' = a) (hn : n' = n) (f : cusp (Xo j) c (U j) a n) :
    ∃ f' : cusp (Xo' j') c' (U' j') a' n', HEq f' f ∧
      ((∀ la, ∀ v ∈ valSet (Xo' j') c' (algCls (Xo' j') c') la, 0 ≤ v (f' : Rul (Xo' j') c')) ↔
        (∀ la, ∀ v ∈ valSet (Xo j) c (algCls (Xo j) c) la, 0 ≤ v (f : Rul (Xo j) c))) := by
  subst hH; cases hDw; cases hl; cases hXo; cases hc; cases hU; subst ha; subst hn; subst hj
  exact ⟨f, HEq.rfl, Iff.rfl⟩

theorem extendByZero_eq_of_heq_families {Tau : Type} (p : ℕ → ℕ) {j j' : ℕ} (hj : j' = j) {a : Tau → Fin (p j) → ℕ}
    {a' : Tau → Fin (p j') → ℕ} (h : HEq a' a) (t : Tau) : ext0 (a' t) = ext0 (a t) := by
  subst hj; cases h; rfl

section Comparison₂
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem nrm_le_one_iff (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m)
    (f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) :
    (∀ la (y : (R.FW i).Pt la), (R.FW i).nrm la y (fw.e i f) ≤ 1) ↔
      ∀ la, ∀ v ∈ valSet (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (algCls (T.Q.Xo ((i : ℕ) + 1)) T.Q.c) la,
        0 ≤ v (f : T.R ((i : ℕ) + 1)) := by
  constructor
  · intro h la v hv
    have h1 := h la ((fw.pt i la).symm ⟨v, hv⟩)
    rw [fw.nrm_eq, Core.nrmM_le_one_iff, Equiv.apply_symm_apply] at h1
    exact h1
  · intro h la y
    rw [fw.nrm_eq, Core.nrmM_le_one_iff]
    exact h la _ (fw.pt i la y).2

end Comparison₂

end GlobalTheory.Mem.R3.MKExt

namespace GlobalTheory.Mem.R3.MKExt
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor



theorem mk_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ((z'.R.FW j').MK : Set (Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)) = {x' | ∃ x ∈ (z.R.FW j).MK, ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)}) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ _ Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ hN j j' hj φ hφ => ?_
  obtain ⟨hB, -⟩ := hE
  clear * - hB hN hj φ hφ
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have hH : z'.core.Q.H = z.core.Q.H := eq_of_heq hN.H
  have hκ := hN.κ j j' hj
  have ha : wtA (z'.geo.κ j') = wtA (z.geo.κ j) := by
    funext x
    unfold wtA
    refine Finset.sum_congr rfl fun t _ => ?_
    have e1 : ext0 ((z'.geo.κ j').aP t) = ext0 ((z.geo.κ j).aP t) :=
      extendByZero_eq_of_heq_families (fun i => ((w.st Z).toD7.R.sigW (i + 1)).1) hj.symm hκ.1 t
    have e2 : ext0 ((z'.geo.κ j').aM t) = ext0 ((z.geo.κ j).aM t) :=
      extendByZero_eq_of_heq_families (fun i => ((w.st Z).toD7.R.sigW (i + 1)).2) hj.symm hκ.2.1 t
    rw [e1, e2]
    rfl
  have hj1 : (j' : ℕ) + 1 = (j : ℕ) + 1 := by rw [hj]
  have M1 := fun f' => cusp_match hH hN.Dw hN.l hN.Xo hN.c hN.U hj1 ha hκ.2.2 f'
  have M2 := fun f => cusp_match' hH hN.Dw hN.l hN.Xo hN.c hN.U hj1 ha hκ.2.2 f
  have hn : z'.R.nW j' = z.R.nW j :=
    (congrFun (eq_of_heq hN.nW) j').trans (congrArg z.R.nW (Fin.ext hj.symm))
  have hinj : Function.Injective (w'.st Z').toD7.what₂.embLL := RingHom.injective _
  ext x'
  simp only [SetLike.mem_coe, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨f', he'⟩ : ∃ f', z'.geo.fw.e j' f' = ⟨x', h1⟩ := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    obtain ⟨f, hff, hP⟩ := M1 f'
    have hI' : ∀ la (y : (z'.R.FW j').Pt la), (z'.R.FW j').nrm la y (z'.geo.fw.e j' f') ≤ 1 := by
      rw [he']; exact h2
    have hI := hP.1 ((nrm_le_one_iff z'.geo.fw j' f').1 hI')
    have hx' : ((z'.geo.fw.e j' f' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) = x' :=
      congrArg Subtype.val he'
    refine ⟨((z.geo.fw.e j f : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL),
      ⟨(z.geo.fw.e j f).2, (nrm_le_one_iff z.geo.fw j f).2 hI⟩, fun k k' hk => ?_⟩
    have h3 := hN.forms j j' hj f f' hff k k' hk
    apply hinj
    rw [hφ]
    exact (congrArg (fun v => (w'.st Z').toD7.what₂.embLL (v k')) hx').symm.trans h3
  · rintro ⟨x, ⟨h1, h2⟩, hrel⟩
    obtain ⟨f, he⟩ : ∃ f, z.geo.fw.e j f = ⟨x, h1⟩ := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    obtain ⟨f', hff, hP⟩ := M2 f
    have hI : ∀ la (y : (z.R.FW j).Pt la), (z.R.FW j).nrm la y (z.geo.fw.e j f) ≤ 1 := by
      rw [he]; exact h2
    have hI' := hP.2 ((nrm_le_one_iff z.geo.fw j f).1 hI)
    have hx : ((z.geo.fw.e j f : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) = x :=
      congrArg Subtype.val he
    have hx' : x' = ((z'.geo.fw.e j' f' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) := by
      funext k'
      have hk : ((Fin.cast hn k' : Fin (z.R.nW j)) : ℕ) = k' := rfl
      have h3 := hN.forms j j' hj f f' hff (Fin.cast hn k') k' hk
      have h4 := hrel (Fin.cast hn k') k' hk
      apply hinj
      rw [h4]
      exact (hφ _).trans ((congrArg (fun v => (w.st Z).toD7.what₂.embLL (v (Fin.cast hn k'))) hx).symm.trans h3.symm)
    subst hx'
    exact ⟨(z'.geo.fw.e j' f').2, (nrm_le_one_iff z'.geo.fw j' f').2 hI'⟩

end GlobalTheory.Mem.R3.MKExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcNormal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def KeyAtVia {Y : Model Xo c β} (M : GChart Y) {R : Type} [CommRing R] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U)
    (x : KeyIn R) (φ : x.P.A.left ⟶ Y.t.G.left) : Prop :=
  ∃ (he : eSec x.P.A ≫ φ = z ≫ eSec Y.t.G) (w : LB.Iso x.P.L (Y.t.PP.L.pull φ)) (hg : x.P.g = M.n),
    IsGrpPullback x.P.A Y.t.G z φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ z he Y.t.PP.L Y.t.PP.rig) ∧
    (∀ (j : (Y.t.PP.L.pull φ).ι) (i : x.P.L.ι)
      (h : (Y.t.PP.L.pull φ).U j ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U (j PUnit.unit))),
      (φ.appLE _ _ h).hom (M.θ (j PUnit.unit)) =
        (show Γ(x.P.A.left, (Y.t.PP.L.pull φ).U j ⊓ x.P.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (x.th.f i)) ∧
    ∀ i, (x.v i).left ≫ φ = spMap (dualMap (ev z M.U hz)) ≫ M.v₀ (i.cast hg)

def ArcFib (Y : Model Xo c β) (bF : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left) (u : HolUnif x.P.A x.P.L g) : Prop :=
  ∀ z, ∃ ψ : Sp ℂ ⟶ Y.oF.t.G.left, ψ ≫ Y.m0.toSABMap.φ = (Fu.ex i P z).left ∧
    ψ ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF ∧ (u.ex z).left ≫ φ = ψ ≫ Y.m.φ

end GlobalTheory.ArcNormal
end
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

theorem _root_.GlobalTheory.T.finiteGroupCharactersOnLiftForms_extendedData : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px), HEq g' g → (((z'.R.toRealDat.FW j').chi g' : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL) = φ (((z.R.toRealDat.FW j).chi g : (w.st Z).toD7.what₂.LLˣ) : (w.st Z).toD7.what₂.LL)) := by
  exact GlobalTheory.Mem.R3.ChiExt.chi_ext

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

theorem _root_.GlobalTheory.T.formsLift_extendedData_intertwines_finiteGroup : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (e : Gc B w.px ≃* Gc B' w'.px), (∀ g, HEq (e g) g) → ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) → (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) → ∀ (g : Gc B w.px) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).r (e g) (L f) = L (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).r g f)) := by
  exact GlobalTheory.Mem.R3.DefLatBC.act_ext

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

theorem _root_.GlobalTheory.T.goodIdempotent_coeffs_correspond_fieldEmbedding : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px), HEq g' g → (idemOf z'.Xg).coeff g' = φ ((idemOf z.Xg).coeff g)) := by
  exact @GlobalTheory.Mem.R3.GoodIdemBC.idemOf_coeff_ext

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

theorem _root_.GlobalTheory.T.supLattice_extendedData_eq_coordinatewiseImage : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ((z'.R.FW j').MK : Set (Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)) = {x' | ∃ x ∈ (z.R.FW j).MK, ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)}) := by
  first | exact @GlobalTheory.Mem.R3.MKExt.mk_ext | exact GlobalTheory.Mem.R3.MKExt.mk_ext | (intros; apply GlobalTheory.Mem.R3.MKExt.mk_ext <;> assumption)

end
end
