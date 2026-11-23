module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle181
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimeToHostCore
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeRatioPosOfPublished
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.InputsHecke
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle184
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle383
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle377
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle380
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle381
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.SelfDualFullLattice

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.VacSub

theorem exists_vacG_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ Γ ≤ latO S T (LS : Set _) (LT : Set _) (fun _ => True), ∃ f, VacG ψ S T Γ f ∧ f ≠ 0 := by
  intro D ψ hψ S T LS LT dS dT Γ hΓ
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hc : ∀ (V : HSp D) τ, ∃ s, IsCartanInv (gramAt D V τ) s := fun V τ =>
    GlobalTheory.Mem.ThetaNonzero.exists_isCartanInv (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ)
      (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  choose s hs using hc
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T (s S) (s T) (hs S) (hs T) LS LT dS dT
  obtain ⟨h1, h2, -⟩ := hf 1
  simp only [one_mul] at h1 h2
  exact ⟨f, ⟨h1, fun u hu => h2.1 u (hΓ hu), fun e he u hu hh => h2.2 e he u (hΓ hu) hh⟩, f0⟩

end GlobalTheory.AscFin.VacSub
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.LiftOntoGood

theorem mem_range_of_fixed {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (th : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y)
    (hsa : LinearMap.adjoint e = e) (hid : e * e = e) (hfix : ∀ y, e (th y) = th y)
    (hinj : ∀ v, e v = v → LinearMap.adjoint th v = 0 → v = 0) (x : Y) (hx : e x = x) : x ∈ LinearMap.range th := by
  have hcomp : e ∘ₗ th = th := LinearMap.ext hfix
  rw [← Submodule.orthogonal_orthogonal (LinearMap.range th)]
  intro v hv
  have hv0 : LinearMap.adjoint th v = 0 := by
    refine ext_inner_left ℂ fun z => ?_
    rw [LinearMap.adjoint_inner_right, inner_zero_right]
    exact hv _ (LinearMap.mem_range_self _ z)
  have h1 : LinearMap.adjoint th (e v) = 0 := by
    have e2 : LinearMap.adjoint th (e v) = LinearMap.adjoint (e ∘ₗ th) v := by
      rw [LinearMap.adjoint_comp, hsa, LinearMap.comp_apply]
    rw [e2, hcomp, hv0]
  have h2 : e (e v) = e v := by rw [← Module.End.mul_apply, hid]
  have h3 : e v = 0 := hinj (e v) h2 h1
  rw [← hx, ← LinearMap.adjoint_inner_left, hsa, h3, inner_zero_left]



theorem goodW_le_range : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → UpInjW R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → R.toRealDat.LUnif → ∀ j, U2.goodW A3 (R.toCx3 F) j ≤ LinearMap.range ((R.toCx3 F).θ' j A3.A.fam.μ0) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hUp _ _ hU j
  have hM : R.toRealDat.IsModels := hC.base.models
  have hC3 := RealDat3.characterisation_of_weak hC hEx
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  have hsa : LinearMap.adjoint (GlobalTheory.Hk3.eH R.toRealDat j) = GlobalTheory.Hk3.eH R.toRealDat j :=
    GlobalTheory.LiftScalarL.adjoint_eH R.toRealDat hM hX j
  have hc : ∀ g, ∑ a, RealDat.eC (A := A3.A) (sg0 D A3.A) a * RealDat.eC (A := A3.A) (sg0 D A3.A) (a⁻¹ * g) =
      RealDat.eC (A := A3.A) (sg0 D A3.A) g := fun g => GlobalTheory.Hk3.conv_map_idem _ (idemOf_mul_self A3.A.X hX) (sg0 D A3.A) g
  have hidem : GlobalTheory.Hk3.eH R.toRealDat j * GlobalTheory.Hk3.eH R.toRealDat j = GlobalTheory.Hk3.eH R.toRealDat j :=
    GlobalTheory.Hk3.sum_rep_idem _ _ hc
  have hinj := (hM.HW j (sg0 D A3.A)).1
  have hrange := (hM.HW j (sg0 D A3.A)).2.1
  have hfixth : ∀ y, GlobalTheory.Hk3.eH R.toRealDat j (R.thG j A3.A.μ0 y) = R.thG j A3.A.μ0 y := by
    intro y
    have hm := hC3.thP.thF_mem j A3.A.μ0 y
    rw [← hrange] at hm
    obtain ⟨x0, hx0⟩ := hm
    have e1 : R.thG j A3.A.μ0 y = GlobalTheory.Hk3.eH R.toRealDat j x0 := by
      apply hinj
      rw [hC3.thP.thG j A3.A.μ0 y, ← hx0, GlobalTheory.LiftScalarL.e_eH R.toRealDat hM j x0]
    rw [e1, ← Module.End.mul_apply, hidem]
  have key := mem_range_of_fixed (R.thG j A3.A.μ0) (GlobalTheory.Hk3.eH R.toRealDat j) hsa hidem hfixth (hUp j A3.A.μ0)
  intro w hw
  have hw' : w ∈ LinearMap.range ((R.toCx3 F).w0C false j) := hw
  rw [GlobalTheory.LevelRange.range_w0C_eq R F hOk hC hU false j] at hw'
  obtain ⟨x, rfl⟩ : ∃ x : (R.HW j (sg0 D A3.A)).H, Tw.mk (twAt D.what₂.embLL A3.A.v0) x = w := ⟨w, rfl⟩
  have hgood : (R.HW j (sg0 D A3.A)).e x ∈
      R.toRealDat.Wat j (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A)) := hw'
  have hfix : GlobalTheory.Hk3.eH R.toRealDat j x = x := by
    apply hinj
    rw [GlobalTheory.LiftScalarL.e_eH R.toRealDat hM j]
    exact GlobalTheory.LiftScalarCompare.postOn_of_good hgood
  obtain ⟨y, hy⟩ := key _ hfix
  have hne : cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) ≠ 0 := by
    intro h0
    have := congrArg norm h0
    rw [norm_cj, (hC.phase j).1, norm_zero] at this
    exact one_ne_zero this
  refine ⟨Tw.mk (twAt D.what₂.embLL A3.A.v0) ((cj (twAt D.what₂.embLL A3.A.v0) (R.phs j))⁻¹ • y), ?_⟩
  show cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.thG j A3.A.μ0 ((cj (twAt D.what₂.embLL A3.A.v0) (R.phs j))⁻¹ • y) = x
  rw [map_smul, smul_inv_smul₀ hne, hy]

end GlobalTheory.LiftOntoGood
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto.QuotL

variable {D : D7}

theorem trivialOnF {c : Com D} (hc : c.Is) {k : ℕ} (hk : k < c.m) :
    GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter.TrivialOnF (c.χ k) := fun a => by
  obtain ⟨⟨η, hη⟩, h⟩ := (hc.hecke k hk).2
  exact (h η hη a).trans (pow_zero _)

theorem quotL_entire_ne_zero : ∀ (D : D7) (c : Com D), c.Is → ∀ i j : ℕ, i < j → j < c.m →
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))))
        (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.χ i * (c.χ j)⁻¹) w}) z) ∧
      ∀ n : ℕ, 1 ≤ n → Λ n ≠ 0 := by
  intro D c hc i j hij hj
  have hi : i < c.m := hij.trans hj
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hexp : ∃ (τ : D.what₂.Tau) (e e' : ℚ), HasInfExp D (c.χ i) τ (-e) ∧
      HasInfExp D (c.χ j) τ (-e') ∧ e ≠ e' :=
    ⟨τ, -(c.a i τ), -(c.a j τ), by rw [neg_neg]; exact hc.exp i hi τ, by rw [neg_neg]; exact hc.exp j hj τ,
      fun h => hc.ne i j hij hj τ (neg_injective h)⟩
  have R := GlobalTheory.HeckeRatio.heckeRatioPos D (c.χ i) (c.χ j) (hc.hecke i hi).1 (hc.hecke j hj).1
    (trivialOnF hc hi) (trivialOnF hc hj) hexp
  obtain ⟨Λ, hL, -⟩ := (R 0).2 c.S
  obtain ⟨hd, hp⟩ := hL
  refine ⟨Λ, hd, fun z hz => ?_, fun n h1 h0 => ?_⟩
  · have hunr : ∀ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))),
        GlobalTheory.LFun.UnrAt (c.χ i * (c.χ j)⁻¹) w := fun w hw =>
      (hc.unr i hi w hw).mul (hc.unr j hj w hw).inv
    have hoff : ∀ P, OffS D c.S P ↔ P ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) :=
      fun P => (GlobalTheory.HeckeRatio.offS_iff c.S P).trans Iff.rfl
    let e := Equiv.subtypeEquivRight hoff
    have k := hp z hz
    rw [GlobalTheory.HeckeRatio.lfac_eq] at k
    have k2 : HasProd (fun w : {w // w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))} =>
        GlobalTheory.LFun.locL (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.χ i * (c.χ j)⁻¹) w}) w.1 z) (Λ z) := by
      refine (e.hasProd_iff).1 (k.congr_fun fun P => ?_)
      have hu := hunr P.1 ((hoff P.1).1 P.2)
      rw [GlobalTheory.LFun.lfac_eq_locL (Formalism.IndefR.ThmB.InputsHecke.isCMExt D)]
      simp only [Function.comp_apply, e, Equiv.subtypeEquivRight_apply_coe, GlobalTheory.LFun.locL,
        GlobalTheory.LFun.charFam_of_unrAt hu]
    exact k2.tprod_eq.symm
  · obtain ⟨Λn, hLn, hpos⟩ := (R n).2 c.S
    have hEq : Λ = Λn := GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter.IsPartialL.unique ⟨hd, hp⟩ hLn
    have := (hpos n h1 le_rfl).2
    rw [← hEq, h0, Complex.zero_re] at this
    exact lt_irrefl _ this

end GlobalTheory.EvenOnto.QuotL

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto

theorem val_eq_zero_imp (D : D7) : MetEx D → ForStage D fun c _ s => ∀ (x : s.CC c) w, w ≠ 0 → PiLocalization₂.val x w = 0 → x = 0 := by
  intro hM c hc j hj s hs x w hw hx
  obtain ⟨ipD, ip, hm⟩ := hM c hc j hj s hs
  have h1 := hm.schur x x w w
  have h0 : Lift.pet s.ν s.fd ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) = 0 := by
    have hx' : (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w = 0 := hx
    rw [hx']
    simp [Lift.pet]
  rw [h0] at h1
  have hD : ipD w w ≠ 0 := by
    intro h
    have := hm.posD w hw
    rw [h] at this
    simp at this
  have hip : ip x x = 0 := by
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact h
    · exact absurd h hD
  by_contra hne
  have := hm.pos x hne
  rw [hip] at this
  simp at this


open GlobalTheory.LFun.ParLin in
theorem isPar_add_smul : ∀ (D : D7) (c : Com D) (s : PiLocalization₂ D), (∀ (u u' : s.CC c) B B' (a : ℂ), IsPar u B → IsPar u' B' →
    (∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))), B w = B' w) →
    u + a • u' ≠ 0 → IsPar (u + a • u') B) ∧ ∀ (u : s.CC c) B (a : ℂ), IsPar u B → a ≠ 0 → IsPar (a • u) B := by
  intro D c s
  have cne : ∀ f : GA D s.V → ℂ, f ≠ 0 → (fun g => conj (f g)) ≠ 0 := fun f hf h0 =>
    hf (funext fun g => by simpa using congrFun h0 g)
  refine ⟨fun u u' B B' a hu hu' hB h0 => ⟨h0, fun v hv => ?_⟩, fun u B a hu ha => ⟨smul_ne_zero ha hu.1, fun v hv => ?_⟩⟩
  · have hval : PiLocalization₂.val (u + a • u') v = PiLocalization₂.val u v + a • PiLocalization₂.val u' v := by simp [PiLocalization₂.val]
    have hc : (fun g => conj (PiLocalization₂.val (u + a • u') v g)) =
        (fun g => conj (PiLocalization₂.val u v g)) + (conj a) • (fun g => conj (PiLocalization₂.val u' v g)) := by
      funext g; simp [hval]
    unfold ParFun
    rw [hc]
    by_cases h1 : PiLocalization₂.val u v = 0
    · have h2 : a • PiLocalization₂.val u' v ≠ 0 := by rw [hval, h1, zero_add] at hv; exact hv
      have ha : a ≠ 0 := fun e => h2 (by simp [e])
      have hu'v : PiLocalization₂.val u' v ≠ 0 := fun e => h2 (by simp [e])
      have hz : (fun g => conj (PiLocalization₂.val u v g)) = 0 := by funext g; simp [h1]
      rw [hz, zero_add]
      exact paramFun_smul (paramFun_of_agree (hu'.2 v hu'v) hB) (by simpa using ha)
    · by_cases h2 : a • PiLocalization₂.val u' v = 0
      · have hz : (conj a) • (fun g => conj (PiLocalization₂.val u' v g)) = 0 := by
          funext g
          have := congrFun h2 g
          simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
          rw [← map_mul, this, map_zero]
        rw [hz, add_zero]
        exact hu.2 v h1
      · have ha : a ≠ 0 := fun e => h2 (by simp [e])
        have hu'v : PiLocalization₂.val u' v ≠ 0 := fun e => h2 (by simp [e])
        refine paramFun_add (hu.2 v h1) (paramFun_smul (paramFun_of_agree (hu'.2 v hu'v) hB) (by simpa using ha)) ?_
        rw [← hc]
        exact cne _ hv
  · have hval : PiLocalization₂.val (a • u) v = a • PiLocalization₂.val u v := by simp [PiLocalization₂.val]
    have hu0 : PiLocalization₂.val u v ≠ 0 := fun e => hv (by rw [hval, e, smul_zero])
    have hc : (fun g => conj (PiLocalization₂.val (a • u) v g)) = (conj a) • (fun g => conj (PiLocalization₂.val u v g)) := by
      funext g; simp [hval]
    unfold ParFun
    rw [hc]
    exact paramFun_smul (hu.2 v hu0) (by simpa using ha)

theorem vanish_and_parLin : ∀ D : D7, MetEx D → (ForStage D fun c _ s => ∀ (x : s.CC c) w, w ≠ 0 → PiLocalization₂.val x w = 0 → x = 0) ∧ ∀ (c : Com D) (s : PiLocalization₂ D), (∀ (u u' : s.CC c) B B' (a : ℂ), IsPar u B → IsPar u' B' → (∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))), B w = B' w) → u + a • u' ≠ 0 → IsPar (u + a • u') B) ∧ ∀ (u : s.CC c) B (a : ℂ), IsPar u B → a ≠ 0 → IsPar (a • u) B :=
  fun D hM => ⟨val_eq_zero_imp D hM, isPar_add_smul D⟩

end GlobalTheory.EvenOnto
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer.CoefMeas

theorem measurable_coef : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v a : ∀ τ, M.H τ), Measurable (coef θ M (congLev D.sp.cm V.gram Λ 𝔪) v a) := by
  intro D θ hθ V S M Λ 𝔪 hΛ h𝔪 v a
  classical
  have h1 := GlobalTheory.SepPer.CoefCont.continuous_coefR D θ hθ V S M v a
  have hfull : Submodule.IsFullLattice D.host.E Λ := by
    exact Formalism.IndefR.Datum.IsSelfDualC.isFullLattice V Λ hΛ
  have h2 := (congLev_open_compact V hfull h𝔪).1
  unfold coef
  exact Measurable.ite h2.measurableSet h1.measurable measurable_const

end GlobalTheory.SepPer.CoefMeas
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

theorem _root_.GlobalTheory.T.norm_levelIndicatorCoefficientTest_le_decay : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v : ∀ τ, M.H τ), KDecay M v → ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : GA D V, ‖coef θ M K v b x‖ ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ := by
  first | exact @GlobalTheory.PoinTerm.norm_coef_le | exact GlobalTheory.PoinTerm.norm_coef_le | (intros; apply GlobalTheory.PoinTerm.norm_coef_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.coefficientPoincareSeries_move_real_point : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v₀ : ∀ τ, M.H τ) (g₀ : GA D V), g₀ ∈ GinfC V → ∀ c g : GA D V, poin θ M K v₀ (g₀⁻¹ * c) v₀ (g * g₀) = poin θ M K (fun τ => M.rep τ (cmp θ τ g₀) (v₀ τ)) c (fun τ => M.rep τ (cmp θ τ g₀) (v₀ τ)) g := by
  first | exact @GlobalTheory.PoinConj.poin_conj | exact GlobalTheory.PoinConj.poin_conj | (intros; apply GlobalTheory.PoinConj.poin_conj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

theorem _root_.GlobalTheory.T.decayWeight_oneParamTranslate_le_const_mul : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ → ∀ N : ℕ, ∃ L : ℝ, 0 ≤ L ∧ ∀ (x : GA D V) (t : ℝ), |t| < 1 → ∏ τ', ((1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) ^ N)⁻¹ ≤ L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ N)⁻¹ := by
  first | exact @GlobalTheory.OnePDecay.decay_oneP | exact GlobalTheory.OnePDecay.decay_oneP | (intros; apply GlobalTheory.OnePDecay.decay_oneP <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_ideal_smul_adelicPointRationalLattice : ∀ (D : D7) (V : HSp D) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → ∀ (x : GA D V) (y : Fin V.rank → D.host.E), (Lev.finE V x⁻¹).1 *ᵥ (fun i => y i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) → y ∈ 𝔪 • latAt Λ x := by
  first | exact @GlobalTheory.SepLatIdeal.mem_smul_latAt | exact GlobalTheory.SepLatIdeal.mem_smul_latAt | (intros; apply GlobalTheory.SepLatIdeal.mem_smul_latAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.continuous_realPlacesMatrixCoefficientProduct : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (v a : ∀ τ, M.H τ), Continuous (coefR θ M v a) := by
  first | exact @GlobalTheory.SepPer.CoefCont.continuous_coefR | exact GlobalTheory.SepPer.CoefCont.continuous_coefR | (intros; apply GlobalTheory.SepPer.CoefCont.continuous_coefR <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latticeSum_longVectors_decayWeight_le : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (B : Fr V) (g : GA D V) (L : Lat V) (R : ℝ), 1 ≤ V.rank → 1 < R → (∀ w ∈ L, w ≠ 0 → R ≤ ∏ τ, nrm θ B g τ w) → ∀ s : Finset (Fin V.rank → D.host.E), (∀ w ∈ s, w ∈ L ∧ w ≠ 0) → ∑ w ∈ s, ∏ τ, (((1 + nrm θ B g τ w) / 3) ^ (2 * V.rank + 5))⁻¹ ≤ Real.exp ((6 * (V.rank : ℝ) + 9) * Fintype.card D.what₂.Tau) / R := by
  first | exact @GlobalTheory.SepPer.latSum_le | exact GlobalTheory.SepPer.latSum_le | (intros; apply GlobalTheory.SepPer.latSum_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.one_le_norm_rational_translate : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (B : Fr V) (x : GA D Y) (γ : GA D V) (z : Fin V.rank → D.host.E), γ ∈ GQ V → mt V γ *ᵥ ratV (zv d) = ratV z → ∀ τ, 1 ≤ nrm θ B (stabilizerEmbedding d x) τ z := by
  first | exact @GlobalTheory.SepPer.MajDom.one_le_nrm | exact GlobalTheory.SepPer.MajDom.one_le_nrm | (intros; apply GlobalTheory.SepPer.MajDom.one_le_nrm <;> assumption)
end
