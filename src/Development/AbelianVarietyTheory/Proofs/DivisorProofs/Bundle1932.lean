module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LevelVectorSizeBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle330
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1894
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle029
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle221
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.curvaturePowerSums_dbarCohomologous : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r] [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ k, DbarCoh A (powFld A G k) (powFld A G' k) := by
  first | exact @GlobalTheory.ChernCalc.PowCoh.dbarCoh_powFld | exact GlobalTheory.ChernCalc.PowCoh.dbarCoh_powFld | (intros; apply GlobalTheory.ChernCalc.PowCoh.dbarCoh_powFld <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

theorem _root_.GlobalTheory.T.hilbertSamuel_filtration_at_good_sections : Quoted → ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ), GeoHyp X Λ₀ → ∀ (δ : ℕ) (f : MvPolynomial (Fin (X.D + 1) × Fin X.N) F) (Q : MvPolynomial (Fin X.D × Fin X.N) F), (∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin X.D → Fin X.N → E), aeval (fun p : Fin X.D × Fin X.N => s p.1 p.2) Q ≠ 0 → SimpleAt X.toTuple δ f E s) → ∀ s : Fin X.D → Fin X.N → F, eval (fun p : Fin X.D × Fin X.N => s p.1 p.2) Q ≠ 0 → (sysOf X Λ₀).FlatAt δ f s := by
  first | exact @GlobalTheory.HSShort.flatAt_of_simpleAt | exact GlobalTheory.HSShort.flatAt_of_simpleAt | (intros; apply GlobalTheory.HSShort.flatAt_of_simpleAt <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Module MeasureTheory
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.IndefR.Mult
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.Survey.LevelVectorSizeBounds
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowTopCore

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem g_mem_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) {PP : Pl D.host.E} (hP : PP ∈ R.Pg) :
    ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  obtain ⟨k, hk⟩ := (h.lev.Pg PP).1 hP
  refine ⟨k, ?_⟩
  have h1 := R.C.P.pb_over k
  rw [← hk] at h1
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (D.host.g k : ℕ) ∈ PP.asIdeal := h1
  simpa using h2


open Classical in
theorem isConjChars_base_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) :
    IsConjChars R i t (RingEquiv.refl ℂ) (R.toLevCh.mu t ((i : ℕ) + 1)) R.eta
      (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) := by
  refine ⟨_, _, isGalConj_refl _ _, isGalConj_refl _ _, ⟨(h.thP.ωP i t).hecS, ?_⟩, h.lev.eta, ?_⟩
  · intro P e he k x hx
    have a := (h.lev.mu0 i).2 P e he k x hx
    have b := (h.lev.xi t).2 P e he k x hx
    show (((R.mu0 ((i : ℕ) + 1) x * R.xi t x : Circle)) : ℂ) = (((R.C.mu0 i).locK P k * (R.xiH t).locK P k : ℂˣ) : ℂ)
    rw [Circle.coe_mul, a, b, Units.val_mul]
  · intro PP hPP a k u hk hu
    have ha : a ∉ PP.asIdeal := fun ha => u.ne_zero (hu.trans (Ideal.Quotient.eq_zero_iff_mem.2 ha))
    show _ = (R.C.mu0 i).locK PP k * (R.xiH t).locK PP k
    by_cases hg : PP ∈ R.Pg
    · obtain ⟨l, hl⟩ := g_mem_ofCore R h hg
      have hun : (R.xiH t).UnrAt PP := by
        by_contra hn
        rcases (h.lev.Q_ram t PP).1 hn with hq | ⟨PP', hq, hc⟩
        · obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP hq
          exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
        · obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP' hq
          obtain ⟨c', hc1, hc2⟩ := hc _ (q_mem hq2)
          have : c' = (q : 𝓞 D.host.E) := by
            apply NumberField.RingOfIntegers.coe_injective
            rw [map_natCast]
            have h3 : (c' : D.host.E) = (q : D.host.E) := by simpa using hc2
            exact h3
          exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (this ▸ hc1)
      simp only [if_pos hg]
      rw [locK_eq_one hun a k hk ha, mul_one]
      exact h.lev.chi i PP hg a k u hk hu
    · have hq : PP ∈ R.Q t := hPP.resolve_left hg
      obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP hq
      have hun : (R.C.mu0 i).UnrAt PP := (R.C.isMu0 i).unr PP fun l hl =>
        not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
      simp only [if_neg hg]
      rw [locK_eq_one hun a k hk ha, one_mul]
      exact h.lev.xiR t PP hq a k u hk hu


open Classical in
theorem isLevelVec_base_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) :
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i R.triv) (R.Q t)
      (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (R.vacP i) (R.vP i t) := by
  have h1 := h.thP.vP i t
  unfold Datum.IsThPVecOf at h1
  unfold IsLevelVec
  have hQ : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
      Datum.omegaQ (R.Q t) (Wc D i).rank (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (-1) y =
        Datum.omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y := by
    intro y
    unfold Datum.omegaQ
    split_ifs with hy
    · refine Finset.prod_congr rfl fun PP _ => ?_
      have hn : PP.1 ∉ R.Pg := fun hg => by
        obtain ⟨l, hl⟩ := g_mem_ofCore R h hg
        obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP.1 PP.2
        exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
      simp only [if_neg hn]
    · rfl
  simp only [omegaG_triv, hQ]
  exact h1


open Classical in
theorem chr_base_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) :
    chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) R.triv
      (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP)) = (levEnv _ (R.βV i) (R.datVt i t)).χ := by
  ext1 x
  refine levFn_congr (R.βV i) D.R.r (r_le_V i) D.R.t 1 R.Pg (R.Q t) R.triv
    (fun _ PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (fun _ PP => (R.chi ((i : ℕ) + 1) PP)⁻¹)
    (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (R.xiR t) ?_ ?_ _
  · intro c PP hP
    simp only [if_pos hP]
  · intro PP hP
    have hn : PP ∉ R.Pg := fun hg => by
      obtain ⟨l, hl⟩ := g_mem_ofCore R h hg
      obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP hP
      exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
    simp only [if_neg hn]

theorem exists_lift_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) :
    ∃ th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H, ∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i t x :=
  GlobalTheory.BaseScalar.exists_factor (R.HW i (sg0 D A)).e (R.thF i t) (R.Wall i (sg0 D A)) (h.models.HW i (sg0 D A)).1
    (h.models.HW i (sg0 D A)).2.1 (h.thP.thF_mem i t)

theorem isLift_of_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0)
    (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H) (hth : ∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i t x) :
    IsLift R i (sg0 D A) (R.ωP i t) (R.ptP i t) (R.cV i) (R.ioP i) (R.νV i t) (R.fdV i t) (R.HV i t) th := by
  refine (h.thP.thF i t).elim fun thP hP => ?_
  unfold IsLift
  intro x v g
  have a := GlobalTheory.BaseScalar.integrableOn_of_isThetaLift hP.1 x (PiTensorProduct.tprod ℂ v) g
  have c := (congrFun (hP.2 x v) g).trans a.2
  refine ⟨a.1, ?_⟩
  rw [hth x]
  exact c

theorem scalar_of_lift_ofCore {F : Face D A} (hA : GlobalTheory.LowRow.AdelC R F) (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (b : ℝ)
    (hb : Sizes D i b) (t : T0) (ht : PrimeToHost R t)
    (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H)
    (hth : IsLift R i (sg0 D A) (R.ωP i t) (R.ptP i t) (R.cV i) (R.ioP i) (R.νV i t) (R.fdV i t) (R.HV i t) th)
    (ev : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (hev : typePart R i (sg0 D A) t R.triv ev ≠ ⊥) :
    ∃ l : ℝ, 0 < l ∧ (∀ x ∈ typePart R i (sg0 D A) t R.triv ev, th (adjLev R.triv th x) = (l : ℂ) • x) ∧
      mainTerm D i (sg0 D A) - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b ≤ Real.log l := by
  have hσ : IsEmbOverK D (sg0 D A) (RingEquiv.refl ℂ) := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]; exact isEmbOverK_base
  have key := hA h i b hb t ht _ _ hσ R.triv (isLocal_triv R) _ _ _ (isConjChars_base_ofCore R h i t) (R.ωP i t) (h.thP.ωP i t)
    (onb (R.MW i (sg0 D A))) (fun ρ => GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.isONBasis_onb _ ρ _ (h.models.order i ρ)) _ _ (isLevelVec_base_ofCore R h i t)
    (h.thP.pt_theta i t) (R.cV i) (h.models.cV i) (R.ioP i) (by rw [delta_base R]; exact h.thP.ioP i t)
    (R.νV i t) (R.fdV i t) (h.models.νV i t) _ (R.B.L i t).pres.y (R.B.L i t).pres.reps (R.HV i t)
    (by rw [chr_base_ofCore R h]; exact h.models.HV i t)
  exact key.2 th hth ev hev

theorem scalar_on_part_ofCore {F : Face D A} (hA : GlobalTheory.LowRow.AdelC R F) (h : GlobalTheory.Hk3.Core R F)
    (hp : PrimeToHost R A.μ0) (i : Fin D.R.m) (b : ℝ) (hb : Sizes D i b)
    (th : (R.HV i A.μ0).H →ₗ[ℂ] (R.HW i (sg0 D A)).H) (hth : ∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i A.μ0 x)
    (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) :
    ∃ l : ℝ, Real.exp (lowB D i b) ≤ l ∧
      ∀ y ∈ GlobalTheory.LiftLower.partH R i (sg0 D A) c, th (LinearMap.adjoint th y) = (l : ℂ) • y := by
  have e := GlobalTheory.LiftLower.typePart_base h.lev i (sg0 D A) c
  have h1 := scalar_of_lift_ofCore R hA h i b hb A.μ0 hp th (isLift_of_ofCore R h i A.μ0 th hth) c
  have h2 := GlobalTheory.BaseScalar.adjLev_triv R th
  have h3 : lowB D i b ≤ mainTerm D i (sg0 D A) -
      8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b := sub_le_sub_right (GlobalTheory.LowTopBound.hookPlus_le_mainTerm R i) _
  exact GlobalTheory.LowTopBound.scalar_of_ne_bot th _ _ h2 _ _ e _ _ h3 h1

theorem lowTop_ofCore : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ (s : ℕ) (b : ℝ),
    GlobalTheory.LowRow.AdelC R F → GlobalTheory.Hk3.Core R F → A.fam.Ok s → PrimeToHost R A.μ0 → (∀ i, Sizes D i b) → GlobalTheory.BigOn.LowTop R b := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F s b hA h _ hp hb i l x hx hl hxl
  obtain ⟨th, hth⟩ := exists_lift_ofCore R h i A.μ0
  have hinj : Function.Injective (R.HW i (sg0 D A)).e := (h.models.HW i (sg0 D A)).1
  have hS : ∀ y, R.thG i A.μ0 y = GlobalTheory.LiftLower.projH R i (sg0 D A) (th y) := fun y => by
    have a1 := h.thP.thG i A.μ0 y
    have a2 := GlobalTheory.LiftLower.e_projH h.models.gW i (sg0 D A) (th y)
    have a3 := congrArg (Formalism.IndefR.Mult.postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A))) (hth y)
    exact hinj (a1.trans (a3.symm.trans a2.symm))
  have hid := GlobalTheory.LiftScalarCompare.eC_idem (R := R) h.grp.record
  have hu := GlobalTheory.gW_norm_eq R h.models.HW h.models.gW h.models.νW i (sg0 D A)
  have htop := GlobalTheory.T.principalLevel_eigenparts_and_conjugate_characters.1 R F (GlobalTheory.Core5.of_core h) i (sg0 D A)
    (GlobalTheory.LiftLower.schurMult_of_models R h.models.HW i (sg0 D A))
  have htop' : (⨆ c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D, GlobalTheory.LiftLower.partH R i (sg0 D A) c) = ⊤ :=
    top_le_iff.1 (htop.ge.trans (iSup_mono fun c => iSup_le fun _ => le_rfl))
  have hm := GlobalTheory.mul_norm_sq_le_norm_adjoint_sq_of_spanning_parts th _ (Real.exp (lowB D i b)) htop'
    (scalar_on_part_ofCore R hA h hp i b (hb i) th hth)
  have key := GlobalTheory.LowTopBound.le_eigenvalue th (R.thG i A.μ0) (GlobalTheory.LiftLower.projH R i (sg0 D A)) _ l hS
    (GlobalTheory.LowTopBound.idem_apply (R.gW i (sg0 D A)) hid)
    (fun x hx y => GlobalTheory.LiftScalarCompare.adjoint_idem (R.gW i (sg0 D A)) hu hid hx y) hm x hx hl hxl
  exact (Real.le_log_iff_exp_le hl).2 key

end GlobalTheory.LowTopCore

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem _root_.GlobalTheory.T.twisted_kernel_class_scalar_integral_standard : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (∀ PP ∈ Ps, (((O i).bad () : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h yd → ∃ c1 : D.what₂.LL, D.what₂.embLL c1 * (((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) * ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) : ℂ))⁻¹) = (((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * ((Λ.mIdx N D.R.r : ℂ))⁻¹ * ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) : ℂ))⁻¹ * (Λ.zCard N D.R.r : ℂ)) ∧ ∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c1) := by
  first | exact @GlobalTheory.TwistClassScalar.twist_class_scalar | exact GlobalTheory.TwistClassScalar.twist_class_scalar | (intros; apply GlobalTheory.TwistClassScalar.twist_class_scalar <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ProdMeas

theorem exists_isFinMeas {D : D7} (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) [∀ v, (μf v).IsHaarMeasure]
    (h1 : ∀ᶠ v in cofinite, μf v (Kv V v) = 1) : ∃ ν, IsFinMeas V μf ν := by
  obtain ⟨ν, hν⟩ := (existsUnique_isRestrictedProdFinPts D.sp.cm.sig V.gram (frameLat V) μf h1).exists
  refine ⟨ν, hν.2.2.1, fun ff hf => ?_⟩
  let S := (eventually_cofinite.1 (hf.2.and h1)).toFinset
  have hS : ∀ v ∉ S, ff v = unitLoc _ _ (frameLat V) v ∧ μf v (Kv V v) = 1 := fun v hv => by
    simpa only [S, Finite.mem_toFinset, mem_setOf_eq, not_not] using hv
  rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ fun v hv => by_contra fun h => hv (by
    rw [(hS v h).1, unitLoc]
    refine (integral_indicator_const _ (isOpen_stabLoc _ _ _ v).measurableSet).trans ?_
    rw [Measure.real, (hS v h).2, ENNReal.toReal_one, one_smul]; rfl)]
  have hcount : Countable (HeightOneSpectrum (𝓞 D.host.F)) := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum _
  have hsf : ∀ w : Empty, SigmaFinite (w.elim : Measure PUnit.{1}) := fun w => w.elim
  have key := (GlobalTheory.RestrMeas.IsCylProd.integral_tensor_indicator (𝕜 := ℂ) (fa := fun w => w.elim) (ff := ff) hν.2.2.2
    (fun w => w.elim) (fun v => ((continuous_proj _ _ v).comp continuous_subtype_val).measurable)
    (fun v => (isOpen_stabLoc _ _ _ v).measurableSet) (fun x => eventually_proj_mem_stabLoc _ _ _ x.1)
    (S := S) (fun v hv => (hS v hv).2) (fun v hv => (hS v hv).1) (fun w => w.elim)
    fun v _ => (hf.1 v).1.continuous.integrable_of_hasCompactSupport (hf.1 v).2).2
  letI : IsEmpty Empty := ⟨Empty.elim⟩
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul] at key
  exact key

end GlobalTheory.ProdMeas

namespace GlobalTheory.ProdMeas

theorem exists_prod_of_haar : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure]
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) →
    (∃ μa, IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ) ∧ ∃ ν, IsFinMeas V μf ν := by
  intro D V μ _ μf hf h1
  haveI := hf
  refine ⟨?_, exists_isFinMeas V μf h1⟩
  obtain ⟨μ₀, h₀⟩ := (existsUnique_isRestrictedProd D.sp.cm.sig V.gram (frameLat V) (fun _ => Measure.haar) μf h1).exists
  haveI := h₀.haar
  have he : μ = Measure.haarScalarFactor μ μ₀ • μ₀ := Measure.isMulLeftInvariant_eq_smul μ μ₀
  have hc : Measure.haarScalarFactor μ μ₀ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at he
    exact (NeZero.ne μ) he
  classical
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace D.host.F))
  rw [he]
  exact ⟨_, h₀.smul_arch w hc⟩

end GlobalTheory.ProdMeas
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrMultTransport

section Density

open GlobalTheory.AdelicU GlobalTheory.PlaceGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))

theorem exists_levelOff_subset [Submodule.IsFullLattice E L] (N : Set (GAd σ J)) (hN : IsOpen N)
    (h1 : (1 : GAd σ J) ∈ N) : ∃ S, (levelOff σ J L S : Set (GAd σ J)) ⊆ N := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun S : Finset (HeightOneSpectrum (𝓞 F)) => (levelOff σ J L S : Set (GAd σ J)) \ N)
    (fun S S' => ⟨S ∪ S', Set.diff_subset_diff_left (levelOff_anti σ J L Finset.subset_union_left),
      Set.diff_subset_diff_left (levelOff_anti σ J L Finset.subset_union_right)⟩)
    (fun S => Set.diff_nonempty.2 (hcon S))
    (fun S => (isCompact_levelOff σ J L S).diff hN)
    (fun S => ((isCompact_levelOff σ J L S).diff hN).isClosed)
  rw [Set.mem_iInter] at hg
  have e : g = 1 := GAd_ext σ J
    (fun w => by rw [mem_finPts_iff_forall.1 (mem_levelOff.1 (hg ∅).1).1 w, map_one])
    fun v => by rw [(mem_levelOff.1 (hg {v}).1).2.1 v (Finset.mem_singleton_self v), map_one]
  exact (hg ∅).2 (e ▸ h1)

end Density

theorem dense_locFin (D : D7) (V : HSp D) :
    Dense ((⨆ v, (locFin V v).range : Subgroup (GfC V)) : Set (GfC V)) := by
  classical
  haveI hL : Submodule.IsFullLattice D.host.E (stdLattice D.host.E V.rank) := isLattice_stdLattice
  set H : Subgroup (GfC V) := ⨆ v, (locFin V v).range with hH
  have hemb : ∀ v x, GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v x ∈ H.map (GfC V).subtype := fun v x =>
    ⟨locFin V v x, Subgroup.mem_iSup_of_mem v ⟨x, rfl⟩, rfl⟩
  intro g
  rw [mem_closure_iff]
  intro o ho hgo
  obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.1 ho
  let N : Set (GA D V) := (fun k => (g : GA D V) * k⁻¹) ⁻¹' U
  have hN : IsOpen N := hU.preimage (continuous_const.mul continuous_inv)
  have h1 : (1 : GA D V) ∈ N := by simpa [N] using hgo
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.TrMultTransport.exists_levelOff_subset D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) N hN h1
  have hf := Filter.eventually_cofinite.1
    (GlobalTheory.AdelicU.eventually_proj_mem_stabLoc D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) (g : GA D V))
  set S' := S₀ ∪ hf.toFinset with hS'
  set x := embAt D.sp.cm.sig V.gram S' (projAt D.sp.cm.sig V.gram S' (g : GA D V)) with hx
  have hxm := GlobalTheory.AdelicU.mem_atPts.1 (embAt_mem D.sp.cm.sig V.gram S' (projAt D.sp.cm.sig V.gram S' (g : GA D V)))
  have hgfin : (g : GA D V) ∈ GlobalTheory.AdelicU.finPts D.sp.cm.sig V.gram := g.2
  have hrest : (partAway D.sp.cm.sig V.gram S' (g : GA D V) : GA D V) ∈
      levelOff D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) S' := by
    refine mem_levelOff.2 ⟨mul_mem (inv_mem hxm.1) hgfin, mem_awayPts.1 (partAway _ _ S' (g : GA D V)).2, fun v hv => ?_⟩
    change proj D.sp.cm.sig V.gram v ((embAt _ _ S' (projAt _ _ S' (g : GA D V)))⁻¹ * (g : GA D V)) ∈ _
    rw [map_mul, map_inv, hxm.2 v hv, inv_one, one_mul]
    by_contra hc
    exact hv (Finset.mem_union_right _ (hf.mem_toFinset.2 hc))
  have hp : (partAway D.sp.cm.sig V.gram S' (g : GA D V) : GA D V) ∈ N :=
    hS₀ (GlobalTheory.PlaceGen.levelOff_anti _ _ _ Finset.subset_union_left hrest)
  have hxe : (g : GA D V) * (partAway D.sp.cm.sig V.gram S' (g : GA D V) : GA D V)⁻¹ = x := by
    exact mul_inv_eq_of_eq_mul (embAt_mul_partAway D.sp.cm.sig V.gram S' (g : GA D V)).symm
  have hxH : x ∈ H.map (GfC V).subtype :=
    GlobalTheory.PlaceGen.piCoprod_mem (fun v : S' => GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v) _ _ (fun v y => hemb v y) _
  obtain ⟨y, hy, hye⟩ := hxH
  refine ⟨y, ?_, hy⟩
  show (y : GA D V) ∈ U
  have : (y : GA D V) = x := hye
  rw [this, ← hxe]
  exact hp

theorem finLoc_transport {D : D7} {V V' : HSp D}
    (j : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v) (Φ : GfC V ≃ₜ* GfC V')
    (hΦ : ∀ v g, Φ (locFin V v g) = locFin V' v (j v g)) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC V) :
    finLoc V' v (Φ g) = j v (finLoc V v g) := by
  let f₁ : GfC V →* Gv V' v := (finLoc V' v).comp Φ.toMulEquiv.toMonoidHom
  let f₂ : GfC V →* Gv V' v := (j v).toMulEquiv.toMonoidHom.comp (finLoc V v)
  have hc : ∀ {W : HSp D}, Continuous (finLoc W v) := fun {W} =>
    (continuous_proj D.sp.cm.sig W.gram v).comp continuous_subtype_val
  have c₁ : Continuous f₁ := hc.comp Φ.continuous
  have c₂ : Continuous f₂ := (j v).continuous.comp hc
  have hle : (⨆ u, (locFin V u).range) ≤ MonoidHom.eqLocus f₁ f₂ := iSup_le fun u => by
    rintro _ ⟨x, rfl⟩
    show finLoc V' v (Φ (locFin V u x)) = j v (finLoc V v (locFin V u x))
    rw [hΦ]
    by_cases h : v = u
    · subst h
      simp [finLoc]
    · simp [finLoc, proj_emb_ne _ _ h]
  have := Set.EqOn.closure (s := ((⨆ u, (locFin V u).range : Subgroup (GfC V)) : Set (GfC V)))
    (fun x hx => hle hx) c₁ c₂
  rw [(dense_locFin D V).closure_eq] at this
  exact this (Set.mem_univ g)

theorem transport :
    ∀ (D : D7) (V V' : HSp D) (j : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v),
      (∀ v g, j v g ∈ Kv V' v ↔ g ∈ Kv V v) → ∀ Φ : GfC V ≃ₜ* GfC V',
      (∀ v g, Φ (locFin V v g) = locFin V' v (j v g)) →
      (∀ ff g, finFn V' (transfer j ff) (Φ g) = finFn V ff g) ∧
      ∀ μf ν, IsFinMeas V μf ν → IsFinMeas V' (fun v => (μf v).map (j v)) (ν.map Φ) := by
  intro D V V' j hK Φ hΦ
  have h1 : ∀ ff g, finFn V' (transfer j ff) (Φ g) = finFn V ff g := fun ff g => by
    refine finprod_congr fun v => ?_
    have := finLoc_transport j Φ hΦ v g
    simp only [finLoc, MonoidHom.comp_apply, Subgroup.coe_subtype] at this
    simp only [GlobalTheory.Orb.transfer, Function.comp_apply, this, ContinuousMulEquiv.symm_apply_apply]
  refine ⟨h1, fun μf ν hν => ?_⟩
  haveI := hν.1
  refine ⟨Φ.isHaarMeasure_map ν, fun ff' hff' => ?_⟩
  let ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ := fun v => ff' v ∘ j v
  have ht : GlobalTheory.Orb.transfer j ff = ff' := funext fun v => funext fun y => by
    simp [ff, GlobalTheory.Orb.transfer]
  have hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff := by
    have := hff'.transfer (fun v => (j v).symm) (Filter.Eventually.of_forall fun v g => by
      have := hK v ((j v).symm g)
      rw [ContinuousMulEquiv.apply_symm_apply] at this
      exact this.symm)
    convert this using 1
    funext v y
    simp [ff, GlobalTheory.Orb.transfer]
  have hm : MeasurableEmbedding (⇑Φ) := Φ.toHomeomorph.measurableEmbedding
  rw [hm.integral_map]
  have e1 : ∀ g, finFn V' ff' (Φ g) = finFn V ff g := fun g => by
    rw [← h1 ff g, ht]
  simp only [e1, hν.2 ff hff]
  refine finprod_congr fun v => ?_
  have hjm : MeasurableEmbedding (⇑(j v)) := (j v).toHomeomorph.measurableEmbedding
  show _ = ∫ x, ff' v x ∂(μf v).map (j v)
  rw [hjm.integral_map]
  rfl
end TrMultTransport
end GlobalTheory
end
end
