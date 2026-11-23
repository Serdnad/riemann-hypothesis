module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle039
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle296
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle299
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle288
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1977
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1706
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1600
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1995
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalUnitaryActionPreserves
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem key_value_of_nf : ∀ κ : Rule, Homog (fun _ => 1) κ → ThetaOne κ → ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (Mx : Matrix (Fin g) (Fin g) ℂ), NF x hg u τ a b c (fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) → Mx.det ≠ 0 ∧ (κ ℂ x : ℂ) * c ^ 8 = Mx.det ^ 4 := by
  intro κ hH hT g x hg u τ a b c Mx h
  subst hg
  obtain ⟨h₁, h₂, ha, hb, hc, hΛ, hr, hs, hd⟩ := h
  have hW := GlobalTheory.KeyFormulaCompare.det_ne_zero x u ((2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx) hd
  have hM : Mx.det ≠ 0 := by
    rw [Matrix.det_smul] at hW
    exact right_ne_zero_of_mul hW
  refine ⟨hM, ?_⟩
  have hN : KeyPow.NormalAt x τ Mx a b c := ⟨u, h₁, h₂, hΛ, hr, hs, hd⟩
  obtain ⟨P, hg, rig, hr', th, hth, v, hv⟩ := x
  obtain ⟨th₀, hth₀, v₀, hv₀, h₀, e₁, e₂⟩ := KeyConst.exists_rescale _ _ _ _ _ _ _ _ _ _ _ _ _ hc hM hN
  obtain ⟨u₀, t₁, t₂, t₃, t₄, t₅, t₆⟩ := (KeyPow.normalAt_one_iff _ _ _ _).1 h₀
  have h₃ := hH ℂ P hg rig hr' th₀ hth₀ v₀ hv₀ th hth v hv c Mx e₁ e₂
  have h₄ := hT _ u₀ _ _ _ t₁ t₂ ha hb t₃ t₄ t₅ t₆
  rw [h₄, Units.val_one, _root_.mul_one] at h₃
  rw [mul_comm]
  exact h₃.trans (_root_.mul_one _)

end GlobalTheory.MBLow.Cl
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.LocFix

theorem fixed_ne_bot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π →
    (∀ v, HasWeightAt π v.embedding (lam v)) → π ⊓ fixed (RF E n) (globLev S K') ≠ ⊥ →
    ∀ w ∈ S, ∀ σ : SmIrr (UL n w), IsCompU π w σ → fixed σ.ρ (K' w) ≠ ⊥ := by
  intro E _ _ _ hU n _ S hS lam K' hK' π hπ _ hne w hw σ hσ
  classical
  obtain ⟨p, hp, -, f, hf0, hfm, hf⟩ := hσ
  obtain ⟨e, he⟩ := GlobalTheory.BCT.LocCompU.exists_equiv hU n w
  have hpe : ∀ x, p x = e x := fun x => Subtype.ext ((hp x).trans (he x).symm)
  have hps : Function.Surjective p := fun g => ⟨e.symm g, by rw [hpe, e.apply_symm_apply]⟩
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  let π' : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  let F : Representation.IntertwiningMap (σ.ρ.comp p) (π'.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict π hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h =>
    hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
  have hσirr := GlobalTheory.BCT.LocCompU.isIrreducible_comp_of_surjective σ.ρ p hps σ.irred
  have htop := (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) π σ.V σ.V π'.rep (locU n w).subtype
    (σ.ρ.comp p) (σ.ρ.comp p) π'.isIrreducible_rep hσirr hσirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1

  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hφπ : φ ∈ π := (Submodule.mem_inf.1 hφ).1
  have hφfix : φ ∈ fixed (RF E n) (globLev S K') := (Submodule.mem_inf.1 hφ).2

  have hfixx : ∀ x : locU n w, p x ∈ K' w → RU E n (x : UA E n) φ = φ := by
    intro x hx
    have hxfin : (x : UA E n) ∈ finU (E := E) (n := n) := (Subgroup.mem_inf.1 x.2).1
    have hy : (⟨x, hxfin⟩ : finU (E := E) (n := n)) ∈ globLev S K' := by
      simp only [globLev, Subgroup.mem_iInf]
      intro w' hw'
      rw [Subgroup.mem_comap, Subgroup.mem_map]
      by_cases hww : w' = w
      · subst hww
        exact ⟨p x, hx, hp x⟩
      · have hund : w'.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) :=
          fun h => hww ((hS w).unique ⟨hw', h⟩ ⟨hw, rfl⟩)
        have h1 : cLoc w' (x : UA E n) = 1 := by
          have h2 := (Subgroup.mem_inf.1 x.2).2
          rw [Subgroup.mem_iInf] at h2
          exact Subgroup.mem_iInf.1 (h2 w') hund
        exact ⟨1, (K' w').one_mem, by simp [h1]⟩
    have h3 : RF E n ⟨x, hxfin⟩ φ = φ := by simpa using hφfix ⟨_, hy⟩
    exact h3
  have hmem : (⟨φ, hφπ⟩ : π) ∈ ⨆ F : Representation.IntertwiningMap (σ.ρ.comp p) (π'.rep.comp (locU n w).subtype),
      LinearMap.range F.toLinearMap := by
    rw [htop]; trivial
  obtain ⟨c, hc, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hmem
  choose u hu using fun i => LinearMap.mem_range.1 (hc i)
  let ρK : Representation ℂ (K' w) σ.V := σ.ρ.comp (K' w).subtype
  have hsumF : ∀ g : K' w, ∑ i ∈ c.support, (i.toLinearMap : σ.V →ₗ[ℂ] π) (ρK g (u i)) =
      (((1 : K' w →* ℂˣ) g : ℂˣ) : ℂ) • (⟨φ, hφπ⟩ : π) := by
    intro g
    have hpx : p (e.symm g) = g := by rw [hpe, e.apply_symm_apply]
    have hterm : ∀ i ∈ c.support, (i.toLinearMap : σ.V →ₗ[ℂ] π) (ρK g (u i)) = π'.rep (e.symm g : UA E n) (c i) := by
      intro i _
      have h1 := LinearMap.congr_fun (i.isIntertwining' (e.symm g)) (u i)
      simp only [LinearMap.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at h1
      rw [hpx] at h1
      rw [← hu i]
      exact h1

    rw [Finset.sum_congr rfl hterm, ← map_sum]
    have hs : ∑ i ∈ c.support, c i = (⟨φ, hφπ⟩ : π) := hsum
    rw [hs]
    apply Subtype.ext
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact hfixx (e.symm g) (by rw [hpx]; exact g.2)
  let H : Subgroup (K' w) := ⨅ i ∈ c.support, GlobalTheory.LocVec.stabSub ρK (u i)
  have hHo : IsOpen (H : Set (K' w)) := by
    simp only [H, Subgroup.coe_iInf]
    refine isOpen_biInter_finset fun i _ => ?_
    have : (GlobalTheory.LocVec.stabSub ρK (u i) : Set (K' w)) =
        (fun g : K' w => (g : UL n w)) ⁻¹' {x | σ.ρ x (u i) = u i} := rfl
    rw [this]
    exact (σ.smooth (u i)).preimage continuous_subtype_val
  have hKc := (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).2
  haveI : H.FiniteIndex := GlobalTheory.LocVec.finiteIndex_of_isOpen (K' w) hKc (fun g hg => (hK'.1 w).2.1 hg) H hHo
  obtain ⟨v, hv0, hv⟩ := GlobalTheory.LocVec.exists_eigen_of_sum ρK (1 : K' w →* ℂˣ) H (fun h _ => MonoidHom.mem_ker.2 rfl)
    c.support u (fun i hi h hh => (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hh i) hi))
    (fun i => (i.toLinearMap : σ.V →ₗ[ℂ] π)) ⟨φ, hφπ⟩ (fun h => hφ0 (congrArg Subtype.val h)) hsumF
  have hvmem : v ∈ fixed σ.ρ (K' w) := fun h => hv h
  intro hb
  rw [hb] at hvmem
  exact hv0 ((Submodule.mem_bot ℂ).1 hvmem)

end GlobalTheory.BCT.LocFix
end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.GradedPull

theorem ratVal_zero' {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} (y : CxPts X.str σ) :
    ratVal (0 : X.Fn) y = 0 := by
  have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial (0 : Γ(X.X, ⊤))
  rw [map_zero, ev_eq mem_ptsIn_top, map_zero] at e
  exact e

theorem ofValues_ddc_eq {n : ℕ} {p u : V n → ℝ} {Φ : V n → V n} {g : V n → ℂ} {z w : V n} (hw : Φ z = w)
    (hu : ContDiffAt ℝ 2 u w) (hΦ : ContDiffAt ℂ 2 Φ z) (hg : ∀ᶠ v in 𝓝 z, DifferentiableAt ℂ g v) (h0 : g z ≠ 0)
    (h : p =ᶠ[𝓝 z] fun v => u (Φ v) - Real.log (‖g v‖ ^ 2)) :
    (ofValues (ddc p z) : Alt n) = pull (fderiv ℂ Φ z) (ofValues (ddc u w) : Ev n) := by
  subst hw
  obtain ⟨U, hU, hUo, hz⟩ := eventually_nhds_iff.1 hg
  have hg2 : ContDiffAt ℂ 2 g z := ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n g U hUo
    fun v hv => (hU v hv).differentiableWithinAt).contDiffAt (hUo.mem_nhds hz)).of_le (by norm_cast)
  have hs : IsSesq (ddc u (Φ z)) := by
    constructor <;> intros <;> simp [ddc] <;> ring
  rw [GlobalTheory.SecForm.pull_ofValues _ _ hs]
  congr 2
  funext ξ η
  have h1 : ContDiffAt ℝ 2 (fun v => u (Φ v)) z := hu.comp z (hΦ.restrict_scalars ℝ)
  have h2 : ContDiffAt ℝ 2 (fun v => Real.log (‖g v‖ ^ 2)) z :=
    ((hg2.restrict_scalars ℝ).norm_sq ℂ).log (by simpa using h0)
  rw [ddc, ddc, leviForm_congr h, leviForm_sub h1 h2, leviForm_log_normSq_eq_zero hg2 h0, sub_zero,
    leviForm_comp_holo hu hΦ]

theorem grF_eq_pull : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ (ε : Fin Y.dim ≃ Fin X.dim ⊕ Cell m) (x : (atlas Y σ).Pt), x.pt ∈ cellSet E E' φ f hf c A u → ∀ r : Root m, (grF E' (pullGram E H φ f hf) r x : Alt Y.dim) = pull (fderiv ℂ (cellMap ε f hf c u ∘ x.ch.symm) x.crd) (ofValues (ddc (cellPot ε (fun v => H A (c.e.symm v)) r) (cellMap ε f hf c u x.pt)) : Ev Y.dim) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR c A u H hH ε x hx r
  have hM := GlobalTheory.T.isFlaggedBundleMetric_pullGram_refinement F σ X Y ι m E E' φ f hf hR H hH
  set B₀ := (E'.nonempty (under x.pt)).choose with hB₀
  have hB₀m : B₀ ∈ E'.S (under x.pt) := (E'.nonempty (under x.pt)).choose_spec
  set B := upM u * A.map φ with hB
  have hT : ∀ w : CxPts Y.str σ, B ∈ E'.S (under w) → B₀ ∈ E'.S (under w) →
      HolUnitAt (atlas Y σ) (fun z => ((B₀ * B⁻¹) r.1).map (ratVal · z)) w ∧
      ∀ i j : Fin (m r.1), i < j → ((B₀ * B⁻¹) r.1).map (ratVal · w) i j = 0 := by
    intro w hAw hBw
    have hp := ((Fr.mem_iff hAw).1 hBw) r.1
    refine ⟨GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values F σ Y (m r.1) ((B₀ * B⁻¹) r.1) w (fun i j => mem_O_ratOf.1 (hp.1 i j)) hp.2.1
      (mem_O_ratOf.1 hp.2.2.1), fun i j hij => ?_⟩
    rw [Matrix.map_apply, hp.2.2.2 i j i.2 hij]
    exact ratVal_zero' w
  have hne : ∀ w : CxPts Y.str σ, B ∈ E'.S (under w) → B₀ ∈ E'.S (under w) →
      ((B₀ * B⁻¹) r.1).map (ratVal · w) r.2 r.2 ≠ 0 := fun w h1 h2 => by
    obtain ⟨hol, tri⟩ := hT w h1 h2
    have := hol.1.ne_zero
    rw [Matrix.det_of_lowerTriangular _ (fun i j hij => tri i j hij)] at this
    exact Finset.prod_ne_zero_iff.1 this r.2 (Finset.mem_univ _)
  have hπ : Continuous (ptMap σ f hf) := by
    unfold ptMap
    apply GlobalTheory.Points.PtsOver.continuous_map
  have hAπ : A ∈ E.S (under (ptMap σ f hf x.pt)) := hx.1.1
  have hsm := ((GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m 0 E H (isMetricFr_of_isMetricOn hH) _ A hAπ r.1).2 c hx.2).self_of_nhds
  have hb : bsL ε (cellMap ε f hf c u x.pt) = c.e (ptMap σ f hf x.pt) := bsL_pt _ _ _
  have hu := (GlobalTheory.T.contDiffAt_flagCellGradedLinePotential ι m Y.dim X.dim ε (fun v => H A (c.e.symm v)) (cellMap ε f hf c u x.pt) r
    (by rw [hb]; exact hsm.2) (by rw [hb]; exact fun i j => (hsm.1 i j).of_le (by norm_cast))).1
  have hl : x.ch.symm x.crd = x.pt := x.ch.left_inv x.2
  have ht : Tendsto x.ch.symm (𝓝 x.crd) (𝓝 x.pt) := by
    have := x.ch.continuousAt_symm (x.ch.map_source x.2)
    rwa [ContinuousAt, x.ch.left_inv x.2] at this
  have e1 : ∀ᶠ z in 𝓝 x.pt, InCell E E' φ f A u (under z) :=
    (isOpen_ptsIn (p := Y.str) (σ := σ) ⟨_, (GlobalTheory.T.isOpen_flagBundleCell_and_coords_regular F X Y ι m E E' φ f hR A u).1⟩).mem_nhds (mem_ptsIn.2 hx.1)
      |> fun h => Filter.mem_of_superset h fun z hz => mem_ptsIn.1 hz
  have e2 := GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ Y ι m m E' x.pt B₀ hB₀m
  have e3 : ∀ᶠ z in 𝓝 x.pt, ptMap σ f hf z ∈ c.e.source := hπ.continuousAt.eventually (c.e.open_source.mem_nhds hx.2)
  refine ofValues_ddc_eq (g := fun v => ((B₀ * B⁻¹) r.1).map (ratVal · (x.ch.symm v)) r.2 r.2)
    (congrArg (cellMap ε f hf c u) hl) hu (GlobalTheory.T.flagCellCoordinates_contDiffAt_etaleChart F σ X Y ι m E E' φ f hf hR c A u _ ε x hx)
    ((hT _ hx.1.2 hB₀m).1.2 x.1.1 x.2 r.2 r.2) (by rw [hl]; exact hne _ hx.1.2 hB₀m) ?_
  filter_upwards [ht.eventually e1, ht.eventually e2, ht.eventually e3] with v h1 h2 h3
  obtain ⟨hol, tri⟩ := hT _ h1.2 h2
  have hpd := hM.posDef _ B h1.2 r.1
  have e := hM.trans _ B h1.2 B₀ h2 r.1
  have e' := (GlobalTheory.T.gramLowerTriangularFactor_lowerTriangular_conj _ _ _ hpd tri hol.1).2 r.2
  have hpos := ((GlobalTheory.T.gramLowerTriangularFactor_posDef_properties _ _ hpd).2.1 r.2).1
  have eg := congrFun (GlobalTheory.T.pullGram_flagCell_frame F σ X Y ι m E E' φ f hf hR c A u H hH _ h1) r.1
  have ec : cellPot ε (fun v => H A (c.e.symm v)) r (cellMap ε f hf c u (x.ch.symm v)) =
      -Real.log (grD (pullGram E H φ f hf B (x.ch.symm v) r.1) r.2) := by
    rw [hB, eg, cellPot, cellMap, bsL_pt, fb_pt, c.e.left_inv h3]
  show -Real.log (grD (pullGram E H φ f hf B₀ (x.ch.symm v) r.1) r.2) =
    cellPot ε (fun v => H A (c.e.symm v)) r (cellMap ε f hf c u (x.ch.symm v)) - _
  rw [ec, e]
  erw [e']
  rw [Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 (hne _ h1.2 h2))) hpos.ne']
  ring

end GlobalTheory.FlagCell2.GradedPull
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.CellDens

theorem dens_smul {n : ℕ} (c : ℂ) (β : Alt n) : dens (c • β) = c * dens β := by
  simp [dens, mul_div_assoc]

theorem dens_blocks (n d : ℕ) (J T : Type) [Fintype J] [Fintype T] (ε : Fin n ≃ Fin d ⊕ J) (lev : J → T) (ρ : T → ℕ)
    (K : T → Fin n → Fin n → ℂ) (r : T → ℕ) (hr : ∀ t, r t = Fintype.card {j // lev j = t})
    (hK : ∀ t j, lev j ≠ t → ρ t ≤ ρ (lev j) → ∀ b, K t (ε.symm (.inr j)) b = 0 ∧ K t b (ε.symm (.inr j)) = 0)
    (α : Alt d) :
    dens (pull (bsL ε) α * ((∏ t, (∑ a, ∑ b, (kappa * K t a b) • sym (a, b)) ^ r t : Ev n) : Alt n)) =
      dens α * ∏ t, ((r t).factorial / (Real.pi : ℂ) ^ r t *
        (Matrix.of fun a b : {j // lev j = t} => K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1))).det) := by
  rw [GlobalTheory.T.topDegreeDensity_blockTriangular_diagonalBlocks n d J T ε lev ρ (fun t a b => kappa * K t a b) r hr
    (fun t j h1 h2 b => by simp [(hK t j h1 h2 b).1, (hK t j h1 h2 b).2]) α]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 (t : T) : (∑ a : {j // lev j = t}, ∑ b : {j // lev j = t},
      (kappa * K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1))) • sym (ε.symm (.inr a.1), ε.symm (.inr b.1)) : Ev n) ^ r t =
      ((r t).factorial / (Real.pi : ℂ) ^ r t *
        (Matrix.of fun a b : {j // lev j = t} => K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1))).det) •
        ∏ a : {j // lev j = t}, (Complex.I / 2) • sym (ε.symm (.inr a.1), ε.symm (.inr a.1)) := by
    have h := GlobalTheory.T.dzWedgeDzbar_sum_pow_card_eq_factorial_det_prod n {j // lev j = t} (fun a => ε.symm (.inr a.1))
      (fun a b hab => Subtype.ext (Sum.inr_injective (ε.symm.injective hab)))
      (kappa • Matrix.of fun a b : {j // lev j = t} => K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1)))
    rw [Matrix.det_smul, ← hr t] at h
    refine Eq.trans h ?_
    rw [Finset.prod_smul, Finset.prod_const, Finset.card_univ, ← hr t, smul_smul]
    congr 1
    have hk : kappa = (Real.pi : ℂ)⁻¹ * (Complex.I / 2) := by
      rw [kappa]; field_simp
    rw [hk, mul_pow, inv_pow]
    ring
  simp only [h1]
  rw [Finset.prod_smul, Fintype.prod_fiberwise lev
    (fun j => (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j))), Subalgebra.coe_smul, mul_smul_comm, dens_smul,
    GlobalTheory.T.topDegreeDensity_baseForm_mul_fibreVolume n d J ε α, mul_comm]

theorem cellPot_add {ι : Type} {m : ι → ℕ} {n d : ℕ} (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (x : Root m)
    (j : Cell m) (h1 : j.root ≠ x) (h2 : x.2.val ≤ j.root.2.val) (z : V n) (c : ℂ) :
    cellPot ε G x (z + c • coordVec (ε.symm (.inr j))) = cellPot ε G x z := by
  have hb : bsL ε (z + c • coordVec (ε.symm (.inr j))) = bsL ε z := by
    ext a
    simp [bsL_apply, coordVec]
  have hf (j' : Cell m) (h : j' ≠ j) : fb ε (z + c • coordVec (ε.symm (.inr j))) j' = fb ε z j' := by
    simp [fb, coordVec, h]
  unfold cellPot
  rw [hb]
  congr 2
  refine GlobalTheory.T.gradedSquaredLength_upperUnitriangular_gram_eq_of_agree _ _ _ _ _ fun s hs => hf _ ?_
  rintro rfl
  exact h1 (Sigma.ext rfl (heq_of_eq (le_antisymm hs h2)))

theorem dens_cellForm : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (a : V d → Alt d) (w : V n), (∀ τ, (G (bsL ε w) τ).PosDef) → (∀ τ, MContDiffAt 2 (fun v => G v τ) (bsL ε w)) → dens (cellForm ε G a w) = dens (a (bsL ε w)) * (fibDens (G (bsL ε w)) (fb ε w) : ℝ) := by
  intro ι _ m n d ε G a w hG hC
  have e : cellFib ε G w = ∏ x : Root m, (∑ p, ∑ q,
      (kappa * -leviForm (cellPot ε G x) w (coordVec p) (coordVec q)) • sym (p, q)) ^ (m x.1 - 1 - x.2 : ℕ) := by
    simp only [cellFib, fibrePoint, map_prod, map_pow, map_neg, map_X, aeval_X, ofValues, ddc, mul_neg, neg_smul,
      Finset.sum_neg_distrib]
  have hk : kappa ≠ 0 := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [kappa, hπ]
  rw [cellForm, e, dens_blocks n d (Cell m) (Root m) ε Cell.root (fun x => x.2.val)
    (fun x p q => -leviForm (cellPot ε G x) w (coordVec p) (coordVec q)) (fun x => m x.1 - 1 - x.2)
    (fun x => by convert (GlobalTheory.T.gradedLine_potential_hessian_det_own_row ι m n d ε G w x (hG _) (hC _)).1.symm) ?_]
  · congr 1
    rw [fibDens, Fintype.prod_sigma, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← GlobalTheory.T.prod_fubiniStudy_densities_eq_flagCell_invariant_density _ _ (hG τ), Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.ofReal_mul]
    congr 1
    · push_cast
      rfl
    · convert (GlobalTheory.T.gradedLine_potential_hessian_det_own_row ι m n d ε G w ⟨τ, i⟩ (hG _) (hC _)).2 <;> rfl
  · intro x j h1 h2 b
    have h := GlobalTheory.T.ddcLeviForm_eq_zero_of_complexLine_invariant n (cellPot ε G x) w (coordVec (ε.symm (.inr j))) (coordVec b)
      (GlobalTheory.T.contDiffAt_flagCellGradedLinePotential ι m n d ε G w x (hG _) (hC _)).1 (cellPot_add ε G x j h1 h2)
    simp only [ddc, mul_eq_zero, hk, false_or] at h
    simp [h.1, h.2]

end GlobalTheory.FlagCell2.CellDens
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.double_scaling_local_equivariance : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd → GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd → ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∃ χd : (Fv F v)ˣ → ℂ, ∀ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v),
        cd p = χd (GlobalTheory.SplitFlip.gdet (GlobalTheory.DblScal.locMatD t c p)) := by
  first | exact @GlobalTheory.DblScal.scalar_factors_through_det | exact GlobalTheory.DblScal.scalar_factors_through_det | (intros; apply GlobalTheory.DblScal.scalar_factors_through_det <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.local_unitary_group_surjects_general_linear_right : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (h' : GL (Fin (a + a')) (Fv F v)), ∃ h ∈ UAt σ G.W (evFin F v), (mat h).map (piW t) = h'.1 := by
  first | exact @GlobalTheory.SkewLevi.surj_at_place | exact GlobalTheory.SkewLevi.surj_at_place | (intros; apply GlobalTheory.SkewLevi.surj_at_place <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Classical

theorem _root_.GlobalTheory.T.triple_lattice_invariant_schwartz_global : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (w : Pl (F := F)) (Ψ : (Fin a' × Fin (a + a') → AF F) → ℂ), Ψ ∈ schA F (Fin a' × Fin (a + a')) →
    (∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) →
      G.M'.co.rho B.ψ γ Ψ = c • Ψ) →
    ∀ (m : ℕ) (f : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ : Fin m → ∀ v : Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ),
    (∀ i v, φ i v ∈ SB (Fin a' × Fin (a + a') → Fv F v)) →
    (∀ i, ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1) →
    Ψ = ∑ i, pure (f i) (φ i) →
    ∃ g : Fin m → (Fin a' × Fin (a + a') → Fv F w) → ℂ, (∀ i, g i ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧
      (∀ i, ∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) →
        Acts (evFin F w) (G.M'.co.rho B.ψ γ) (g i) (c • g i)) ∧
      Ψ = ∑ i, pure (f i) (Function.update (φ i) w (g i)) := by
  first | exact @GlobalTheory.VacAvg.avg_eigen | exact GlobalTheory.VacAvg.avg_eigen | (intros; apply GlobalTheory.VacAvg.avg_eigen <;> assumption)
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.induced_full_rank_irreducible : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
    ∀ N : Submodule ℂ (GL (Fin d) k → ℂ), N ≤ GlobalTheory.FullRankCoinv.indSp k n d ν →
      (∀ f ∈ N, ∀ h₀ : GL (Fin d) k, (fun h => f (h * h₀)) ∈ N) → N = ⊥ ∨ N = GlobalTheory.FullRankCoinv.indSp k n d ν := by
  first | exact @GlobalTheory.FullRankCoinv.indSp_irreducible | exact GlobalTheory.FullRankCoinv.indSp_irreducible | (intros; apply GlobalTheory.FullRankCoinv.indSp_irreducible <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.triple_local_unitary_action_preserves : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v : Pl (F := F), ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
    ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ →
    ∀ μ : @Measure (Fin a × Fin (a + a') → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ x, ‖φ₁ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.LocalUnitaryL2.lintegral_eq | exact GlobalTheory.LocalUnitaryL2.lintegral_eq | (intros; apply GlobalTheory.LocalUnitaryL2.lintegral_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.FourBoundsAtBundles

end GlobalTheory.Fc.FourBoundsAtBundles

namespace GlobalTheory.Fc.FourBoundsAtBundles

open GlobalTheory.Fc.R1

theorem evW_of_atAll {Bd : BdT} {q : BdP Bd} {𝒜 : FamClass} {σ : RawSel Bd 𝒜} (h : AtAll q 𝒜 σ) : Ind.EvW q 𝒜 σ :=
  Closed.of_all fun Fm _ hc => Ind.ev_of_atAll h Fm (w3_a hc)

end GlobalTheory.Fc.FourBoundsAtBundles
end
