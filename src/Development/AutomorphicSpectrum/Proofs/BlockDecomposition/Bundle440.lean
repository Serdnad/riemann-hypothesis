module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle410
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle197
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle423
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Multiset.Functor
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host
open PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.ClosedInvariantMeet

theorem exists_space (hG2a : G2a) (hG2b : G2b) (hG2c : G2c) {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    {a : ℕ} (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ)
    (S : Finset (Pl E)) (B : Pl E → Multiset ℂˣ) (hB : ∀ w, w ∉ S → (B w).card = a)
    (H : Submodule ℂ (L2 (latticeGL E a) μ)) (hH : IsSubrep (R (latticeGL E a) μ) H) :
    ∃ Y : Submodule ℂ (XB E a), YOK ψ S Y ∧ ∀ φ : XB E a, φ ∈ Y ↔
      (Good ψ (a - 1) φ ∧ ∀ γ g, φ (ratGL E a γ * g) = φ g) ∧
        (∃ h : MemL2Quotient (latticeGL E a) μ φ, h.toL2 ∈ H) ∧ ∀ w, w ∉ S → SatFn w (B w) φ := by
  obtain ⟨Y0, c0, s0, m0⟩ := hG2a E a ψ hψ
  obtain ⟨YH, cH, sH, mH⟩ := hG2b E a μ H hH
  have hw := fun w (hw : w ∉ S) => hG2c E a w (B w) (hB w hw)
  choose! Yw cw sw mw using hw
  have mem : ∀ φ : XB E a, φ ∈ Y0 ⊓ YH ⊓ ⨅ w, ⨅ (_ : w ∉ S), Yw w ↔
      (φ ∈ Y0 ∧ φ ∈ YH) ∧ ∀ w, w ∉ S → φ ∈ Yw w := fun φ => by
    simp only [Submodule.mem_inf, Submodule.mem_iInf]
  refine ⟨Y0 ⊓ YH ⊓ ⨅ w, ⨅ (_ : w ∉ S), Yw w, ⟨?_, ?_, ?_⟩, fun φ => ?_⟩
  · have e : ((Y0 ⊓ YH ⊓ ⨅ w, ⨅ (_ : w ∉ S), Yw w : Submodule ℂ (XB E a)) : Set (XB E a)) =
        ((Y0 : Set (XB E a)) ∩ YH) ∩ ⋂ w, ⋂ (_ : w ∉ S), (Yw w : Set (XB E a)) := by
      ext φ
      simp only [SetLike.mem_coe, mem, Set.mem_inter_iff, Set.mem_iInter]
    rw [e]
    exact (c0.inter cH).inter (isClosed_iInter fun w => isClosed_iInter fun h => cw w h)
  · intro g hg φ hφ
    obtain ⟨⟨h0, h1⟩, h2⟩ := (mem φ).1 hφ
    exact (mem _).2 ⟨⟨s0 g φ h0, sH g φ h1⟩, fun w h => sw w h g (hg w h) φ (h2 w h)⟩
  · intro φ hφ
    exact ((m0 φ).1 ((mem φ).1 hφ).1.1).1
  · rw [mem, m0, mH]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2⟩
      exact ⟨h0, h1, fun w h => (mw w h φ).1 (h2 w h)⟩
    · rintro ⟨h0, h1, h2⟩
      exact ⟨⟨h0, h1⟩, fun w h => (mw w h φ).2 (h2 w h)⟩

theorem eq_of_wh (hG5 : G5) (hG13 : WhittakerVanishingImpliesZero) {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (S : Finset (Pl E)) (hc : ∀ w, w ∉ S → Cond ψ w) (B : Pl E → Multiset ℂˣ)
    (hYs : ∀ w, w ∉ S → ∃ Z : Submodule ℂ (XB E a), ∀ φ, φ ∈ Z ↔ SatFn w (B w) φ)
    (hY0 : ∃ Z : Submodule ℂ (XB E a), ∀ φ : XB E a, φ ∈ Z ↔ Good ψ (a - 1) φ ∧ ∀ γ g, φ (ratGL E a γ * g) = φ g)
    {φ φ' : XB E a} (h : (Good ψ (a - 1) φ ∧ ∀ γ g, φ (ratGL E a γ * g) = φ g) ∧ ∀ w, w ∉ S → SatFn w (B w) φ)
    (h' : (Good ψ (a - 1) φ' ∧ ∀ γ g, φ' (ratGL E a γ * g) = φ' g) ∧ ∀ w, w ∉ S → SatFn w (B w) φ')
    (hW : ∀ g, MirS S g → InS S g → Wh ψ φ g = Wh ψ φ' g) : φ = φ' := by
  obtain ⟨Z, hZ⟩ := hY0
  have d0 : φ - φ' ∈ Z := Z.sub_mem ((hZ φ).2 h.1) ((hZ φ').2 h'.1)
  have hd := (hZ _).1 d0
  have e := hG13 E a ψ hψ S hc (φ - φ') hd.1 hd.2
    (fun w hw => ⟨B w, by
      obtain ⟨Z', hZ'⟩ := hYs w hw
      exact (hZ' _).1 (Z'.sub_mem ((hZ' φ).2 (h.2 w hw)) ((hZ' φ').2 (h'.2 w hw)))⟩)
    (fun g h1 h2 => by
      obtain ⟨Λ, hΛ⟩ := (hG5 E a ψ hψ).1 g
      rw [← hΛ _ hd.1, map_sub, hΛ _ h.1.1, hΛ _ h'.1.1, hW g h1 h2, sub_self])
  exact sub_eq_zero.1 e

theorem meet_of_steps : S2 → MirabolicColumnBlock → G0 → G1 → AlmostEverywhereSpherical → G2a → G2b → G2c → G5 → G5b → FourierInductionSteps → G8 → StandardCharacterExists → WhittakerVanishingImpliesZero → Meet := by
  intro _ hS10 hG0 hG1 hG1b hG2a hG2b hG2c hG5 _ hG7i hG8 hG10 hG13 E _ _ _ a μ _ _ π π' H H' hn hn' hH hH' hm hm' hss
  obtain ⟨ψ, hψ, hcond⟩ := hG10 E
  obtain ⟨φ0, hφ0, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨φ0', hφ0', h0'⟩ := (Submodule.ne_bot_iff _).1 π'.ne_bot
  obtain ⟨x, hx, hxs, hxl⟩ := hG1 E a π hn φ0 hφ0
  obtain ⟨x', hx', hxs', hxl'⟩ := hG1 E a π' hn' φ0' hφ0'
  have hev := hcond.and (hss.and ((hG1b E a π hn φ0 hφ0 x hx).and (hG1b E a π' hn' φ0' hφ0' x' hx')))
  obtain ⟨S, hS⟩ : ∃ S : Finset (Pl E), ∀ w, w ∉ S → Cond ψ w ∧
      (∃ B, (CG.mk π).HasSat w B ∧ (CG.mk π').HasSat w B) ∧
      (∀ B, (CG.mk π).HasSat w B → SatFn w B x) ∧ (∀ B, (CG.mk π').HasSat w B → SatFn w B x') :=
    ⟨(Filter.eventually_cofinite.1 hev).toFinset, fun w hw => by
      by_contra h
      exact hw ((Set.Finite.mem_toFinset _).2 h)⟩
  have hBex := fun w (hw : w ∉ S) => (hS w hw).2.1
  choose! B hB using hBex
  have hcard : ∀ w, w ∉ S → (B w).card = a := fun w hw => CG.HasSat.card (hB w hw).1
  have hc : ∀ w, w ∉ S → Cond ψ w := fun w hw => (hS w hw).1
  obtain ⟨Y, hYok, hY⟩ := exists_space hG2a hG2b hG2c μ hψ S B hcard H hH
  obtain ⟨Y', hYok', hY'⟩ := exists_space hG2a hG2b hG2c μ hψ S B hcard H' hH'

  have hxY : x ∈ Y := by
    refine (hY x).2 ⟨⟨?_, ?_⟩, ?_, fun w hw => (hS w hw).2.2.1 _ (hB w hw).1⟩
    · rw [hx]; exact _root_.GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ φ0 (π.cusp _ hφ0)
    · rw [hx]; exact (π.cusp _ hφ0).1.left
    · rw [hx]; exact hm φ0 hφ0
  have hxY' : x' ∈ Y' := by
    refine (hY' x').2 ⟨⟨?_, ?_⟩, ?_, fun w hw => (hS w hw).2.2.2 _ (hB w hw).2⟩
    · rw [hx']; exact _root_.GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ φ0' (π'.cusp _ hφ0')
    · rw [hx']; exact (π'.cusp _ hφ0').1.left
    · rw [hx']; exact hm' φ0' hφ0'
  have hx0 : x ≠ 0 := fun e => h0 (Subtype.ext (by rw [← hx, e]; rfl))
  have hx0' : x' ≠ 0 := fun e => h0' (Subtype.ext (by rw [← hx', e]; rfl))
  obtain ⟨φ₁, hφ₁, hs₁, hl₁, hw₁⟩ := hG8 E a ψ hψ S hc Y hYok x hxY hx0 hxs (hxl S)
    fun w hw => ⟨B w, ((hY x).1 hxY).2.2 w hw⟩
  obtain ⟨φ₂, hφ₂, hs₂, hl₂, hw₂⟩ := hG8 E a ψ hψ S hc Y' hYok' x' hxY' hx0' hxs' (hxl' S)
    fun w hw => ⟨B w, ((hY' x').1 hxY').2.2 w hw⟩
  have hst : St ψ S Y Y' 0 (fun _ => 0) := by
    refine ⟨φ₁, hφ₁, φ₂, hφ₂, hs₁, hs₂, hl₁, hl₂, by rw [hw₁]; exact one_ne_zero, fun g hg => ?_⟩
    have e : g = 1 := by
      obtain ⟨-, -, -, -, -, hext, -⟩ := hG0 E a
      refine hext g 1 ?_ fun w => ?_
      · rw [map_one]; exact (hS10 _ a 0).2.1 _ hg.1
      · rw [map_one]; exact (hS10 _ a 0).2.1 _ (hg.2 w)
    rw [e, hw₁, hw₂]
  obtain ⟨φ, hφ, φ', hφ', -, -, -, -, hw, hag⟩ := hG7i E a ψ hψ S Y Y' hYok hYok' hst
  have hφm := (hY φ).1 hφ
  have hφm' := (hY' φ').1 hφ'
  obtain ⟨Z, -, -, hZ⟩ := hG2a E a ψ hψ
  have heq : φ = φ' := by
    refine eq_of_wh hG5 hG13 hψ S hc B (fun w hw => ?_) ⟨Z, hZ⟩ ⟨hφm.1, hφm.2.2⟩
      ⟨hφm'.1, hφm'.2.2⟩ fun g hg hi => hag g ⟨hg.1, fun w => ?_⟩
    · obtain ⟨Z', -, -, hZ'⟩ := hG2c E a w (B w) (hcard w hw)
      exact ⟨Z', hZ'⟩
    · by_cases hw : w ∈ S
      · simpa only [if_pos hw] using hg.2 w hw
      · simp only [if_neg hw]
        rw [hi w hw]
        exact (hS10 _ a 0).2.2.1
  subst heq
  obtain ⟨h, hhH⟩ := hφm.2.1
  obtain ⟨h', hhH'⟩ := hφm'.2.1
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    obtain ⟨Λ, hΛ⟩ := (hG5 E a ψ hψ).1 1
    exact hw (by rw [← hΛ _ hφm.1.1, map_zero])
  have hne : h.toL2 ≠ 0 := toL2_ne_zero h φ.continuous fun e => hφ0 (DFunLike.coe_injective e)
  intro hbot
  have hmem : h.toL2 ∈ H ⊓ H' := ⟨hhH, hhH'⟩
  rw [hbot] at hmem
  exact hne ((Submodule.mem_bot _).1 hmem)

end GlobalTheory.CompanionTheory.ClosedInvariantMeet

end
end

section

noncomputable section

open NumberField IsDedekindDomain Filter GlobalTheory.CuspRep GlobalTheory.LFun Formalism.L2.Host PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.StrongMultOne

theorem spherical_almost_everywhere_of_bounded : G1 → AlmostEverywhereSpherical := by
  intro g1 E _ _ _ a π hN φ hφ x hx
  have hex : ∀ v : π.V, ∃ y : XB E a, (y : GA E a → ℂ) = v.1.1 := fun v =>
    (g1 E a π hN v.1 v.2).imp fun _ h => h.1
  choose f hf using hex
  let ι : π.V →ₗ[ℂ] XB E a :=
    { toFun := f
      map_add' := fun u v => by
        refine DFunLike.coe_injective ?_
        rw [BoundedContinuousFunction.coe_add, hf, hf, hf]
        rfl
      map_smul' := fun c v => by
        refine DFunLike.coe_injective ?_
        funext g
        rw [hf]
        change _ = c • f v g
        rw [congrFun (hf v) g]
        rfl }
  have hι : ∀ v, (ι v : GA E a → ℂ) = v.1.1 := hf
  filter_upwards [AeFix.eventually_mem_fixed E a π ⟨φ, hφ⟩] with w hw B hB
  by_cases h0 : x = 0
  · exact Or.inl h0
  refine Or.inr ?_
  have hxι : ι ⟨φ, hφ⟩ = x := DFunLike.coe_injective ((hι _).trans hx.symm)
  have hne : (⟨φ, hφ⟩ : π.V) ≠ 0 := fun e => h0 (by rw [← hxι, e, map_zero])
  have hsat : IsSatVecGL w (π.locRep w) ⟨φ, hφ⟩ B := hB.2 _ hw hne
  have hint : ∀ g y, ι (π.locRep w g y) = repW a w g (ι y) := fun g y => by
    refine DFunLike.coe_injective ?_
    funext h
    rw [hι]
    change _ = (ι y) (h * fl a w g)
    have := congrFun (hι y) (h * fl a w g)
    rw [this]
    rfl
  have := hsat.map ι hint (by rw [hxι]; exact h0)
  rwa [hxι] at this

end GlobalTheory.CompanionTheory.StrongMultOne

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.CompanionTheory.MPDict
open GlobalTheory.ArithmeticHeightTower ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem charZero_genericPt {n' m : ℕ} {n : Fin (m + 1) → ℕ} {Y : Scheme.{0}} [IsIntegral Y]
    {j : Y ⟶ MP ℤ (m + 1) (consN n' n)} {e : ℕ} (hvar : GlobalTheory.IsArithVar (j ≫ qpStr n' m n) e) :
    CharZero ((MP ℤ (m + 1) (consN n' n)).residueField (j (genericPoint Y))) := by
  haveI h0 : CharZero Γ(Y, ⊤) := hvar.charZero
  have hinj : Function.Injective ((Y.residue (genericPoint Y)).hom.comp
      (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom) :=
    (Y.residue (genericPoint Y)).hom.injective.comp (germ_injective_of_isIntegral Y _ _)
  haveI h1 : CharZero (Y.residueField (genericPoint Y)) := charZero_of_injective_ringHom hinj
  exact (RingHom.charZero_iff (j.residueFieldMap (genericPoint Y)).hom.injective).2 h1

theorem charZero_image (n' m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n))
    [hx : CharZero ((MP ℤ (m + 1) (consN n' n)).residueField x)] :
    CharZero ((MP ℤ m n).residueField (qpSnd n' m n x)) := by
  let F : MP ℤ (m + 1) (consN n' n) ⟶ MP ℤ m n := qpSnd n' m n
  exact (RingHom.charZero_iff (F.residueFieldMap x).hom.injective).2 hx

theorem dim_closure_genericPt {n' m : ℕ} {n : Fin (m + 1) → ℕ} {Y : Scheme.{0}} [IsIntegral Y]
    {j : Y ⟶ MP ℤ (m + 1) (consN n' n)} [IsClosedImmersion j] {e : ℕ}
    (hvar : GlobalTheory.IsArithVar (j ≫ qpStr n' m n) e) :
    topologicalKrullDim (closure ({j (genericPoint Y)} : Set (MP ℤ (m + 1) (consN n' n)))) = ((e + 1 : ℕ) : _) := by
  have hrange : Set.range j = closure {j (genericPoint Y)} := by
    have h₁ := (genericPoint_spec Y).image j.continuous
    rw [Set.image_univ, j.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  exact (topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange).trans hvar.dim_eq

end GlobalTheory.CompanionTheory.MPDict
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.TwUnits

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (h'' : W ≤ U) (x : Γ(X, U)ˣ) :
    Semi.res h' (Semi.res h x) = Semi.res h'' x := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom x.val) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_div_g {X : Scheme.{0}} (T L : LB X) (p q : T.ι × L.ι) {W : X.Opens}
    (h : W ≤ (T.U p.1 ⊓ L.U p.2) ⊓ (T.U q.1 ⊓ L.U q.2)) (h₁ : W ≤ T.U p.1 ⊓ T.U q.1) (h₂ : W ≤ L.U p.2 ⊓ L.U q.2) :
    Semi.res h ((LB.div T L).g p q) = Semi.res h₁ (T.g p.1 q.1) * (Semi.res h₂ (L.g p.2 q.2))⁻¹ :=
  (map_mul (Semi.res h) _ _).trans (congrArg₂ (· * ·) (res_res' _ _ h₁ _)
    ((map_inv (Semi.res h) _).trans (congrArg (·⁻¹) (res_res' _ _ h₂ _))))

theorem iso_law {X : Scheme.{0}} {L T : LB X} {w : LB.Iso L T} (hw : w.IsGen) (p q : T.ι × L.ι) {W : X.Opens}
    (hp : W ≤ T.U p.1 ⊓ L.U p.2) (hq : W ≤ T.U q.1 ⊓ L.U q.2) (h₁ : W ≤ T.U p.1 ⊓ T.U q.1)
    (h₂ : W ≤ L.U p.2 ⊓ L.U q.2) :
    Semi.res hp (w.s p) = Semi.res h₁ (T.g p.1 q.1) * (Semi.res h₂ (L.g p.2 q.2))⁻¹ * Semi.res hq (w.s q) := by
  have e := congrArg (Semi.res (le_inf hp hq)) (hw p q)
  exact ((res_res' _ _ hp _).symm.trans e).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (res_div_g T L p q (le_inf hp hq) h₁ h₂) (res_res' _ _ hq _)))

theorem res_pull_g (k : Fin (m + 1)) (j j' : PUnit → Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ ((O1 ℤ (n k)).pull (pr ℤ m n k)).U j ⊓ ((O1 ℤ (n k)).pull (pr ℤ m n k)).U j')
    (h' : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (j PUnit.unit) ⊓ chart ℤ (n k) (j' PUnit.unit))) :
    Semi.res h (((O1 ℤ (n k)).pull (pr ℤ m n k)).g j j') = blockUnit (j PUnit.unit) (j' PUnit.unit) h' := by
  have e := linComb_punit_g (O1 ℤ (n k)) (pr ℤ m n k) 1 j j'
  rw [zpow_one] at e
  exact (congrArg (Semi.res h) e).trans (res_res' _ _ h' _)

def twIdx (b : Fin m) (t : ℤ) (c : ∀ k, Bk n k) : (twB m n b t).ι :=
  Prod.mk (fun _ => c b.succ) (fun _ => c 0)

theorem mchart_le_U (b : Fin m) (t : ℤ) (c : ∀ k, Bk n k) : mchart c ≤ (twB m n b t).U (twIdx b t c) :=
  fun _ hx => ⟨Set.mem_iInter.2 fun _ => mchart_le c _ hx, Set.mem_iInter.2 fun _ => mchart_le c _ hx⟩

theorem blk_le {c c' : ∀ k, Bk n k} {W : (MP ℤ m n).Opens} (hW : W ≤ mchart c ⊓ mchart c') (k : Fin (m + 1)) :
    W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)) :=
  fun _ hx => ⟨mchart_le c k (hW hx).1, mchart_le c' k (hW hx).2⟩

theorem res_twB_g (b : Fin m) (t : ℤ) (c c' : ∀ k, Bk n k) {W : (MP ℤ m n).Opens} (hW : W ≤ mchart c ⊓ mchart c')
    (h : W ≤ (twB m n b t).U (twIdx b t c) ⊓ (twB m n b t).U (twIdx b t c')) :
    Semi.res h ((twB m n b t).g (twIdx b t c) (twIdx b t c')) =
      blockUnit (c b.succ) (c' b.succ) (blk_le hW b.succ) * blockUnit (c 0) (c' 0) (blk_le hW 0) ^ t := by
  have h₁ : W ≤ ((O1 ℤ (n b.succ)).pull (pr ℤ m n b.succ)).U (fun _ => c b.succ) ⊓
      ((O1 ℤ (n b.succ)).pull (pr ℤ m n b.succ)).U (fun _ => c' b.succ) :=
    le_inf (fun _ hx => h hx |>.1.1) (fun _ hx => h hx |>.2.1)
  have h₂ : W ≤ ((O1 ℤ (n 0)).pull (pr ℤ m n 0)).U (fun _ => c 0) ⊓
      ((O1 ℤ (n 0)).pull (pr ℤ m n 0)).U (fun _ => c' 0) :=
    le_inf (fun _ hx => h hx |>.1.2) (fun _ hx => h hx |>.2.2)
  have e₁ := res_pull_g b.succ (fun _ => c b.succ) (fun _ => c' b.succ) h₁ (blk_le hW b.succ)
  have e₂ := res_pull_g 0 (fun _ => c 0) (fun _ => c' 0) h₂ (blk_le hW 0)
  have e₃ : (Semi.res h₂ (((O1 ℤ (n 0)).pull (pr ℤ m n 0)).g (fun _ => c 0) (fun _ => c' 0)) ^ (-t))⁻¹ =
      blockUnit (c 0) (c' 0) (blk_le hW 0) ^ t := by
    rw [zpow_neg, inv_inv]
    exact congrArg (· ^ t) e₂
  exact (res_div_g _ _ (twIdx b t c) (twIdx b t c') h h₁ h₂).trans (congrArg₂ (· * ·) e₁
    ((congrArg (·⁻¹) (map_zpow (Semi.res h₂) _ (-t))).trans e₃))

theorem blockUnit_self {k : Fin (m + 1)} (i : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) i)) : blockUnit i i h = 1 := by
  rw [blockUnit, ratioUnit_self, map_one, map_one]

theorem prod_zpow_single {G : Type*} [CommGroup G] (f : Fin (m + 1) → G) (p q : Fin (m + 1)) (t : ℤ) :
    ∏ k, f k ^ ((Pi.single p 1 + t • Pi.single q 1 : Fin (m + 1) → ℤ) k) = f p * f q ^ t := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zpow_add, Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_eq_single p (fun k _ hk => by simp [hk]) (by simp)]
    simp
  · rw [Finset.prod_eq_single q (fun k _ hk => by simp [hk]) (by simp)]
    simp

variable {B : LB (MP ℤ m n)} {b : Fin m} {t : ℤ}

def uOf (w : LB.Iso B (twB m n b t)) (i : B.ι) (c : ∀ k, Bk n k) : Γ(MP ℤ m n, B.U i ⊓ mchart c)ˣ :=
  Semi.res (le_inf (inf_le_right.trans (mchart_le_U b t c)) inf_le_left) (w.s (twIdx b t c, i))

theorem res_uOf (w : LB.Iso B (twB m n b t)) (i : B.ι) (c : ∀ k, Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ B.U i ⊓ mchart c) (h' : W ≤ (twB m n b t).U (twIdx b t c) ⊓ B.U i) :
    Semi.res h (uOf w i c) = Semi.res h' (w.s (twIdx b t c, i)) :=
  res_res' _ _ h' _

theorem frame_uOf {w : LB.Iso B (twB m n b t)} (hw : w.IsGen) (i j : B.ι) (c : ∀ k, Bk n k) :
    Semi.res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        B.U i ⊓ B.U j ⊓ mchart c ≤ B.U j ⊓ mchart c) (uOf w j c) =
      Semi.res (inf_le_left : B.U i ⊓ B.U j ⊓ mchart c ≤ B.U i ⊓ B.U j) (B.g i j) *
        Semi.res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          B.U i ⊓ B.U j ⊓ mchart c ≤ B.U i ⊓ mchart c) (uOf w i c) := by
  have hc : B.U i ⊓ B.U j ⊓ mchart c ≤ mchart c ⊓ mchart c := le_inf inf_le_right inf_le_right
  have hU := (inf_le_right : B.U i ⊓ B.U j ⊓ mchart c ≤ mchart c).trans (mchart_le_U b t c)
  have hi : B.U i ⊓ B.U j ⊓ mchart c ≤ (twB m n b t).U (twIdx b t c) ⊓ B.U i :=
    le_inf hU (inf_le_left.trans inf_le_left)
  have hj : B.U i ⊓ B.U j ⊓ mchart c ≤ (twB m n b t).U (twIdx b t c) ⊓ B.U j :=
    le_inf hU (inf_le_left.trans inf_le_right)
  have e := iso_law hw (twIdx b t c, i) (twIdx b t c, j) hi hj (le_inf hU hU) inf_le_left
  rw [res_twB_g b t c c hc, blockUnit_self, blockUnit_self, one_zpow, one_mul, one_mul] at e
  rw [res_uOf w j c _ hj, res_uOf w i c _ hi]
  exact (eq_inv_mul_iff_mul_eq.1 e).symm

theorem mono_uOf (hB : B.IsLB) {w : LB.Iso B (twB m n b t)} (hw : w.IsGen) (i : B.ι) (c c' : ∀ k, Bk n k) :
    Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
        B.U i ⊓ (mchart c ⊓ mchart c') ≤ B.U i ⊓ mchart c) (uOf w i c) =
      Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
        B.U i ⊓ (mchart c ⊓ mchart c') ≤ B.U i ⊓ mchart c') (uOf w i c') *
      ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
        ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
          B.U i ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^
        (Pi.single b.succ 1 + t • Pi.single 0 1 : Fin (m + 1) → ℤ) k := by
  have hc : B.U i ⊓ (mchart c ⊓ mchart c') ≤ mchart c ⊓ mchart c' := inf_le_right
  have hU := (inf_le_right.trans inf_le_left : B.U i ⊓ (mchart c ⊓ mchart c') ≤ mchart c).trans (mchart_le_U b t c)
  have hU' := (inf_le_right.trans inf_le_right : B.U i ⊓ (mchart c ⊓ mchart c') ≤ mchart c').trans (mchart_le_U b t c')
  have hs : Semi.res (le_inf inf_le_left inf_le_left : B.U i ⊓ (mchart c ⊓ mchart c') ≤ B.U i ⊓ B.U i) (B.g i i) = 1 :=
    Units.ext (LB.resG_g_self hB i _)
  have hi : B.U i ⊓ (mchart c ⊓ mchart c') ≤ (twB m n b t).U (twIdx b t c) ⊓ B.U i := le_inf hU inf_le_left
  have hi' : B.U i ⊓ (mchart c ⊓ mchart c') ≤ (twB m n b t).U (twIdx b t c') ⊓ B.U i := le_inf hU' inf_le_left
  have e := iso_law hw (twIdx b t c, i) (twIdx b t c', i) hi hi' (le_inf hU hU') (le_inf inf_le_left inf_le_left)
  rw [res_twB_g b t c c' hc] at e
  change _ = _ * (Semi.res _ (B.g i i))⁻¹ * _ at e
  rw [hs, inv_one, mul_one] at e
  rw [res_uOf w i c _ hi, res_uOf w i c' _ hi',
    prod_zpow_single (fun k => blockUnit (c k) (c' k) (blk_le hc k)) b.succ 0 t]
  exact e.trans (mul_comm _ _)

theorem exists_units : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (B : LB (MP ℤ m n)) (c : Fin m) (t : ℤ), B.IsLB → LBIso B (twB m n c t) →
  ∃ u : ∀ (i : B.ι) (c' : ∀ k, Bk n k), Γ(MP ℤ m n, B.U i ⊓ mchart c')ˣ,
    (∀ i j c',
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          B.U i ⊓ B.U j ⊓ mchart c' ≤ B.U j ⊓ mchart c') (u j c') =
        res (inf_le_left : B.U i ⊓ B.U j ⊓ mchart c' ≤ B.U i ⊓ B.U j) (B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            B.U i ⊓ B.U j ⊓ mchart c' ≤ B.U i ⊓ mchart c') (u i c')) ∧
    (∀ i (c' c'' : ∀ k, Bk n k),
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ B.U i ⊓ mchart c') (u i c') =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ B.U i ⊓ mchart c'') (u i c'') *
        ∏ k, blockUnit (c' k) (c'' k) (fun _ hx =>
          ⟨mchart_le c' k hx.2.1, mchart_le c'' k hx.2.2⟩ :
            B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c' k) ⊓ chart ℤ (n k) (c'' k))) ^ (Pi.single c.succ 1 + t • Pi.single 0 1 : Fin (m + 1) → ℤ) k) := by
  rintro m n B c t hB ⟨w, hw⟩
  exact ⟨uOf w, frame_uOf hw, mono_uOf hB hw⟩

end GlobalTheory.CompanionTheory.MPDict.TwUnits
end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.Clozel

theorem qdet_restrict {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) {n : ℕ}
    (X : Fin n → Fin n → Module.End ℂ S) (Y : Fin n → Fin n → Module.End ℂ V)
    (h : ∀ i j (x : S), (X i j x : V) = Y i j x) (w : ℂ) (x : S) :
    (Formalism.REAL.qdet X w x : V) = Formalism.REAL.qdet Y w x := by
  let P : Subalgebra ℂ (Module.End ℂ S × Module.End ℂ V) :=
    { carrier := {z | ∀ x : S, (z.1 x : V) = z.2 x}
      mul_mem' := fun {p q} hp hq x => by
        show ((p.1 (q.1 x) : S) : V) = p.2 (q.2 x)
        rw [hp, hq]
      add_mem' := fun {p q} hp hq x => by
        show ((p.1 x + q.1 x : S) : V) = p.2 x + q.2 x
        rw [Submodule.coe_add, hp, hq]
      algebraMap_mem' := fun c x => rfl }
  let Z : Fin n → Fin n → Module.End ℂ S × Module.End ℂ V := fun i j => (X i j, Y i j)
  have hZ : Formalism.REAL.qdet Z w ∈ P := by
    refine P.sum_mem fun σ _ => P.mul_mem (intCast_mem P _) (P.list_prod_mem fun y hy => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hy
    refine P.add_mem ?_ (fun x => h _ _ x)
    split_ifs
    · exact P.algebraMap_mem _
    · exact P.zero_mem
  have h1 : (Formalism.REAL.qdet Z w).1 = Formalism.REAL.qdet X w :=
    map_qdet (AlgHom.fst ℂ (Module.End ℂ S) (Module.End ℂ V)) Z w
  have h2 : (Formalism.REAL.qdet Z w).2 = Formalism.REAL.qdet Y w :=
    map_qdet (AlgHom.snd ℂ (Module.End ℂ S) (Module.End ℂ V)) Z w
  rw [← h1, ← h2]
  exact hZ x

theorem qdet_EopV_val : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (τ : E →+* ℂ) (u : ℂ) (φ : π.V),
    (Formalism.REAL.qdet (EopV π τ) (u + ((a : ℂ) - 1) / 2) φ).1 = cap τ u φ.1 := by
  intro E _ _ _ a π τ u φ
  exact qdet_restrict π.V (EopV π τ) (Eop τ) (fun i j x => GlobalTheory.T.lie_operator_vector_eq E a π τ i j x) _ φ

end GlobalTheory.CompanionTheory.Clozel
end
