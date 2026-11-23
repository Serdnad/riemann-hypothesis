module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle164
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDiagonalEntryTorusIntegralOfFlatMapNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle193
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormal
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle129
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle329
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle356
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle305
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle307
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle306
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLiftInvariance
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open GlobalTheory.FinPl.LastDiag (add_smul_mx exists_idemAt jX_pX_mem_latA mxAt_smul smul_eq_self smul_isHalf' symplO_add_right')
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastDiagonalEntry_torus_integral_of_flatMap_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → J.d.levi t ∈ grpAt J.W (· = v) → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 → ∀ i : Fin ρ, i.1 + 1 = ρ → t.1 i i - 1 ∈ intAt D (· = v) := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf t ht htG hne i hi
  have mxAt_mul_left : ∀ {D : D7} {P : Pl D → Prop} {a b c : ℕ} (y : Mx D a b) {x : Mx D b c} (hx : MxAt P x),
      MxAt P (y ⬝ x) := by
    intro D P a b c y x hx i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)

  have mxAt_mul_right : ∀ {D : D7} {P : Pl D → Prop} {a b c : ℕ} {x : Mx D a b} (hx : MxAt P x) (y : Mx D b c),
      MxAt P (x ⬝ y) := by
    intro D P a b c x hx y i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

  have wittExtZero_inclusionX_mem_homLatticeCompletion : ∀ {D : D7} {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (dS : HypDec S S₀ ρ) (dT : HypDec T T₀ σ) {LS : Lat S}
      {LS₀ : Lat S₀} {LT : Lat T} {LT₀ : Lat T₀} {v : Pl D} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
      (hS₀ : IsSelfDualC S₀ LS₀) (hmS : MonoAt dS LS LS₀ v) (hmT : MonoAt dT LT LT₀ v) {w : WO S₀ T}
      (hw : w ∈ latO S₀ T (LS₀ : Set _) (LT : Set _) (· = v)),
      dS.ext0 T (dT.incX S₀ (dT.pX ⬝ w)) ∈ latO S T (LS : Set _) (LT : Set _) (· = v) := by
    intro D S S₀ T T₀ ρ σ dS dT LS LS₀ LT LT₀ v hS hT hS₀ hmS hmT w hw
    have hx := GlobalTheory.FinPl.LatMem.latO_mxAt hw
    refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT (· = v) _).2 ⟨?_, fun y hy => ?_⟩
    · rw [HypDec.matrixExtendByZero_apply, HypDec.incX_apply]
      exact mxAt_mul_right (mxAt_mul_left _ (mxAt_mul_left _ hx)) _
    · change (dT.jX * (dT.pX * w) * dS.p0) *ᵥ y ∈ latA T LT (· = v)
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have h1 : dS.p0 *ᵥ y ∈ latV S₀ LS₀ (· = v) := ((hmS y).1 hy).2.2
      exact jX_pX_mem_latA dT hmT (GlobalTheory.FinPl.LatMem.latO_maps hS₀ hw h1)

  have wittExtZero_inclusionX_smul : ∀ {D : D7} {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (dS : HypDec S S₀ ρ) (dT : HypDec T T₀ σ) (c : AE D)
      (ξ : Mx D σ S₀.rank),
      dS.ext0 T (dT.incX S₀ (c • ξ)) = c • dS.ext0 T (dT.incX S₀ ξ) := by
    intro D S S₀ T T₀ ρ σ dS dT c ξ
    rw [HypDec.matrixExtendByZero_apply, HypDec.matrixExtendByZero_apply, HypDec.incX_apply, HypDec.incX_apply, Matrix.mul_smul, Matrix.smul_mul]

  have incAdj_smul : ∀ {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (c : AE D) (y : Mx D S.rank ρ),
      d.incAdj S (c • y) = cA D c • d.incAdj S y := by
    intro D T T₀ ρ d S c y
    rw [HypDec.incAdj_apply, HypDec.incAdj_apply, HypDec.incY_apply, HypDec.incY_apply, adj_smul, Matrix.smul_mul,
      smul_comm (incA D (-D.host.xi0⁻¹)) (cA D c), Matrix.mul_smul]

  have symplO_incAdj_proj : ∀ {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (z : Mx D S.rank ρ) (w : WO S T),
      symplO S T (d.incAdj S z) w = symplO S T (d.incAdj S z) (d.incX S (d.pX ⬝ w)) := by
    intro D T T₀ ρ d S z w
    have key : hO S T (d.incAdj S z) w = hO S T (d.incAdj S z) (d.incX S (d.pX ⬝ w)) := by
      rw [d.hO_coordT S, d.hO_coordT S]
      simp only [HypDec.incAdj_apply, HypDec.incY_apply, HypDec.incX_apply, ← Matrix.mul_assoc, HypDec.pX_jY,
        HypDec.p0_jY, HypDec.pY_jY, HypDec.pX_jX, HypDec.p0_jX, HypDec.pY_jX, Matrix.zero_mul, Matrix.one_mul]
      simp [pairT, hO]
    rw [symplO, symplO, key]

  have fix_char : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J)
      {P : Pl D → Prop} {𝔉 : (WO B.V J.W → ℂ) → (WO B.V₀ J.W₀ → ℂ)} (h𝔉 : IsFlatBF s P 𝔉) {f : WO B.V J.W → ℂ}
      (hθ : IsThetaFunO ψ B.V J.W f) (t : GL (Fin ρ) (AE D)) (hne : 𝔉 (s.om (1, J.d.levi t) f) ≠ 0)
      (ξ : Mx D ρ B.V₀.rank) (hξ : MxAt P ξ) (hfix : heisO ψ B.V J.W (B.d.ext0 J.W (J.d.incX B.V₀ ξ)) f = f),
      ψ (symplO B.V₀ J.W (J.d.incAdj B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ))) (J.d.incX B.V₀ (t.1 ⬝ ξ))) = 1 := by
    intro D ψ ρ B J s P 𝔉 h𝔉 f hθ t hne ξ hξ hfix
    have hg : IsThetaFunO ψ B.V J.W (s.om (1, J.d.levi t) f) := s.weil.om_pres _ _ hθ
    have hact : actO B.V J.W 1 (J.d.levi t) (B.d.ext0 J.W (J.d.incX B.V₀ ξ)) =
        B.d.ext0 J.W (J.d.incX B.V₀ (t.1 ⬝ ξ)) := by
      rw [actO_eq, inv_one, mt_one, Matrix.mul_one, HypDec.matrixExtendByZero_apply, HypDec.matrixExtendByZero_apply, HypDec.incX_apply,
        HypDec.incX_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, HypDec.levi_jX]
    have h1 := s.weil.om_heis 1 (J.d.levi t) (B.d.ext0 J.W (J.d.incX B.V₀ ξ)) f hθ
    rw [hfix, hact] at h1
    have h3 := h𝔉.Heisenberg₂.iso _ hg (t.1 ⬝ ξ) (mxAt_mul_left _ hξ)
    rw [← h1] at h3
    by_contra hc
    apply hne
    funext w
    have hw := congrFun h3 w
    rw [Pi.smul_apply, smul_eq_mul] at hw
    have h4 : (ψ (symplO B.V₀ J.W (J.d.incAdj B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ))) (J.d.incX B.V₀ (t.1 ⬝ ξ))) - 1) *
        𝔉 (s.om (1, J.d.levi t) f) w = 0 := by
      rw [sub_mul, ← hw, one_mul, sub_self]
    exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 hc)

  have yZero_mul_diag : ∀ {D : D7} (S : HSp D) {ρ : ℕ} (z : Fin S.rank → D.host.E) (t : Matrix (Fin ρ) (Fin ρ) (AE D))
      (ht : ∀ i j, i ≠ j → t i j = 0) (i : Fin ρ) (hi : i.1 + 1 = ρ),
      yZero S ρ z ⬝ t = t i i • yZero S ρ z := by
    intro D S ρ z t ht i hi
    classical
    have hell : ∀ j : Fin ρ, ell D ρ j = if j = i then 1 else 0 := fun j => by
      by_cases hj : j = i
      · subst hj; simp [ell, hi]
      · have hj' : ¬ (j.1 + 1 = ρ) := fun h => hj (Fin.ext (by omega))
        simp [ell, hj', hj]
    ext k l
    have hy : ∀ j, yZero S ρ z k j = if j = i then -ratV z k else 0 := fun j => by
      simp only [yZero, zEll, Matrix.neg_apply, Matrix.vecMulVec_apply, hell]
      split_ifs <;> simp
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, hy l]
    simp only [hy, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    by_cases hl : l = i
    · subst hl
      rw [ite_eq_left rfl, mul_comm]
    · rw [ite_eq_right hl, ht i l (Ne.symm hl), mul_zero, mul_zero]

  have symplO_incAdj_eq : ∀ {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (z : Mx D S.rank ρ) (w : WO S T),
      symplO S T (d.incAdj S z) w = -Algebra.trace (AF D.host.F) (AE D) (z ⬝ (d.pX ⬝ w)).trace := by
    intro D T T₀ ρ d S z w
    rw [symplO_incAdj_proj, GlobalTheory.SplitScalar.symplO_skew, HypDec.symplO_incX_incAdj]

  have chi_add : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
      (y : Mx D S.rank ρ) (t : Matrix (Fin ρ) (Fin ρ) (AE D)) (ξ₁ ξ₂ : Mx D ρ S.rank),
      ψ (symplO S T (d.incAdj S y) (d.incX S (t ⬝ (ξ₁ + ξ₂)))) =
        ψ (symplO S T (d.incAdj S y) (d.incX S (t ⬝ ξ₁))) * ψ (symplO S T (d.incAdj S y) (d.incX S (t ⬝ ξ₂))) := by
    intro D ψ T T₀ ρ d S y t ξ₁ ξ₂
    rw [Matrix.mul_add, map_add (f := _), symplO_add_right', AddChar.map_add_eq_mul]

  obtain ⟨hθ, h2, hh⟩ := hf
  have hstd : IsStdChar D ψ (-1) := s.weil.std
  obtain ⟨eV, heV_int, heV_act, heV_cA, hhalf⟩ := exists_idemAt D v
  have heV_id : eV ∈ idAt D (· = v) := heV_int.1
  have hcA : ∀ c ∈ idAt D (· = v), cA D c ∈ idAt D (· = v) := fun c hc => by
    rw [← heV_act c hc, map_mul, heV_cA]; exact Ideal.mul_mem_left _ _ heV_id
  have hMx : ∀ c ∈ idAt D (· = v), MxAt (· = v) (J.d.incAdj B.V₀ (c • yZero B.V₀ ρ (vecB B.o B.ζ))) :=
    fun c hc k l => by
      rw [incAdj_smul, Matrix.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_right _ _ (hcA c hc)

  have hcong := (GlobalTheory.IwaPlace.mem_congGrp_iff J.W (idAt D (· = v)) _).1 htG
  have hM : MxAt (· = v) (mt J.W (J.d.levi t) - 1) := fun k l => by rw [Matrix.sub_apply]; exact hcong k l
  have htM : t.1 - 1 = J.d.pX ⬝ (mt J.W (J.d.levi t) - 1) ⬝ J.d.jX := by
    rw [Matrix.mul_sub, Matrix.sub_mul, J.d.pX_levi t, Matrix.mul_one, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one]
  have ha : t.1 i i - 1 ∈ idAt D (· = v) := by
    have := mxAt_mul_right (mxAt_mul_left J.d.pX hM) J.d.jX i i
    rwa [← htM, Matrix.sub_apply, Matrix.one_apply_eq] at this
  have hρ : 0 < ρ := by omega
  rw [← hG.last hρ _ ha]
  refine (GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hstd B.V₀ J.W LV₀ LW hG.sdV₀ hG.sdW (· = v) _ (hMx _ ha)).2 fun u' hu' => ?_
  obtain ⟨ξ, hξdef⟩ : ∃ ξ, ξ = J.d.pX ⬝ u' := ⟨_, rfl⟩
  have hξ : MxAt (· = v) ξ := hξdef ▸ mxAt_mul_left _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu')
  have hu : B.d.ext0 J.W (J.d.incX B.V₀ ξ) ∈ latO B.V J.W (LV : Set _) (LW : Set _) (· = v) :=
    hξdef ▸ wittExtZero_inclusionX_mem_homLatticeCompletion B.d J.d hG.sdV hG.sdW hG.sdV₀ hG.monoV hG.monoW hu'
  have hξe : eV • ξ = ξ := smul_eq_self (fun a ha => (mul_comm eV a).trans (heV_act a ha)) hξ

  have hχ : ψ (symplO B.V₀ J.W (J.d.incAdj B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ))) (J.d.incX B.V₀ (t.1 ⬝ ξ))) = 1 := by
    rcases hG.tame.2 with h2v | ⟨e, ε, he, hε, hes⟩
    · obtain ⟨c, hcc, hcl⟩ := hhalf h2v
      have hcu := hcl _ _ _ _ _ hu
      rw [← wittExtZero_inclusionX_smul] at hcu
      have hfix := h2 _ hcu
      rw [← map_nsmul (B.d.ext0 J.W), ← map_nsmul (J.d.incX B.V₀)] at hfix
      have h2c : 2 • (c • ξ) = ξ := by
        rw [two_nsmul, add_smul_mx, hcc, hξe]
      rw [h2c] at hfix
      exact fix_char s h𝔉 hθ t hne ξ hξ hfix
    · have hact := (GlobalTheory.FinPl.placeIdem_acts D v ε hε).1
      have hce := GlobalTheory.SplitScalar.isSplitIdem_conj he
      have hfixE : ∀ e' : AE D, IsSplitIdem D e' →
          heisO ψ B.V J.W (B.d.ext0 J.W (J.d.incX B.V₀ (e' • ξ))) f = f := by
        intro e' he'
        have hmem := GlobalTheory.LatticeStable.smul_mem_latO D B.V J.W _ _ (· = v) e'
          (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he'.1])) _ hu
        rw [← wittExtZero_inclusionX_smul] at hmem
        refine hh e' he' _ hmem ?_
        rw [wittExtZero_inclusionX_smul]
        exact smul_isHalf' he'.1 _
      have hMe : ∀ e' : AE D, MxAt (· = v) (e' • ξ) := fun e' => mxAt_smul e' hξ
      have h1 := fix_char s h𝔉 hθ t hne _ (hMe e) (hfixE e he)
      have h2' := fix_char s h𝔉 hθ t hne _ (hMe (cA D e)) (hfixE _ hce)
      have hsum : e • ξ + cA D e • ξ = ξ := by
        rw [add_smul_mx, hes]
        exact smul_eq_self (fun a ha => (hact a).1 ha) hξ
      have hk := chi_add ψ J.d B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ)) t.1 (e • ξ) (cA D e • ξ)
      rw [hsum, h1, h2', mul_one] at hk
      exact hk
  have hε' := (GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hstd B.V₀ J.W LV₀ LW hG.sdV₀ hG.sdW (· = v) _ (hMx _ heV_id)).1
    ((hG.last hρ eV heV_id).2 heV_int) u' hu'
  rw [symplO_incAdj_eq, ← hξdef, Matrix.smul_mul, ← Matrix.mul_smul, hξe] at hε'
  have hχ' := hχ
  rw [GlobalTheory.SplitScalar.symplO_skew, HypDec.symplO_incX_incAdj, ← Matrix.mul_assoc,
    yZero_mul_diag _ _ t.1 ht i hi, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at hχ'
  have hT : ψ (Algebra.trace (AF D.host.F) (AE D) (yZero B.V₀ ρ (vecB B.o B.ζ) ⬝ ξ).trace) = 1 := by
    rw [AddChar.map_neg_eq_inv] at hε'
    exact inv_eq_one.1 hε'
  rw [symplO_incAdj_eq, ← hξdef, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, sub_mul, one_mul, map_sub, neg_sub,
    sub_eq_add_neg, AddChar.map_add_eq_mul, hT, hχ', one_mul]
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

theorem snocCols_uni_iff : ∀ (R : Type) [CommRing R] (n σ : ℕ) (M : Matrix (Fin n) (Fin σ) R) (w : Fin n → R) (Y : Matrix (Fin n) (Fin n) R), (∃ U ∈ GlobalTheory.UniIndexPrime.uniSub (σ + 1) R, Y * Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) = Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) * (U : Matrix (Fin (σ + 1)) (Fin (σ + 1)) R)) ↔ ∃ u ∈ GlobalTheory.UniIndexPrime.uniSub σ R, ∃ v : Fin σ → R, Y * M = M * (u : Matrix (Fin σ) (Fin σ) R) ∧ Y *ᵥ w = w + M *ᵥ v := GlobalTheory.T.snocColumns_moved_by_upperUnitriangular_iff

theorem fix_lineVec_emb : ∀ (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ k : GA D S, mt S k *ᵥ ratV (o.iB *ᵥ ζ) = ratV (o.iB *ᵥ ζ) → ∃ h : GA D A, k = o.emb (h, 1) := GlobalTheory.T.exists_unitaryEmbedding_preimage_of_fixes_anisotropicLine

theorem fourierBesselBasePoint_leftInverse_rational : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), (∃ P ∈ ratMx D (σ + 1) B.V.rank, P ⬝ x0 B = 1) ∧ x0 B ∈ ratMx D B.V.rank (σ + 1) := GlobalTheory.T.x0_mem_ratMx_and_exists_rat_leftInverse

variable {D : D7} {σ : ℕ}

theorem ratV_mulVec_rat {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (v : Fin n → D.host.E) :
    ratV (M *ᵥ v) = rat M *ᵥ ratV v := by
  funext i; simp only [ratV, rat, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

def actUni (B : BesLev D σ) : Subgroup (GA D B.V) where
  carrier := {g | ∃ u ∈ UX D (σ + 1), mt B.V g ⬝ x0 B = x0 B ⬝ u.1}
  one_mem' := ⟨1, one_mem _, by rw [mt_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]⟩
  mul_mem' := by
    rintro a b ⟨u, hu, ha⟩ ⟨u', hu', hb⟩
    refine ⟨u * u', mul_mem hu hu', ?_⟩
    rw [mt_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Units.val_mul, Matrix.mul_assoc]
  inv_mem' := by
    rintro a ⟨u, hu, ha⟩
    refine ⟨u⁻¹, inv_mem hu, ?_⟩
    have h1 : mt B.V a⁻¹ ⬝ (x0 B ⬝ u.1) ⬝ (u⁻¹).1 = x0 B ⬝ (u⁻¹).1 := by
      rw [← ha, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
    rw [← h1, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem mem_actUni_iff (B : BesLev D σ) (g : GA D B.V) : g ∈ actUni B ↔ ∃ u ∈ UX D σ, ∃ v : Fin σ → AE D,
    mt B.V g ⬝ B.d.jX = B.d.jX ⬝ u.1 ∧
      mt B.V g *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) = B.d.j0 *ᵥ ratV (vecB B.o B.ζ) + B.d.jX *ᵥ v :=
  snocCols_uni_iff (AE D) B.V.rank σ B.d.jX _ (mt B.V g)

theorem flagN_le_actUni (B : BesLev D σ) : flagN B.d ≤ actUni B := by
  intro n hn
  obtain ⟨u, hu, b, c, rfl⟩ := ((flag_jacobi_structure D B.V B.V₀ σ B.d).1 n).1 hn
  rw [mem_actUni_iff]
  have hm : mt B.V (B.d.levi u * (B.d.nB b * B.d.nC c)) ⬝ B.d.j0 = B.d.j0 + B.d.jX ⬝ (u.1 ⬝ b) := by
    rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, B.d.nC_j0, B.d.nB_j0, Matrix.mul_add, B.d.wittDecomp_levi_inclAnisotropic,
      ← Matrix.mul_assoc, B.d.levi_jX, Matrix.mul_assoc]
  refine ⟨u, hu, (u.1 ⬝ b) *ᵥ ratV (vecB B.o B.ζ), ?_, ?_⟩
  · rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, B.d.nC_jX, B.d.nB_jX, B.d.levi_jX]
  · rw [Matrix.mulVec_mulVec, hm, Matrix.add_mulVec, Matrix.mulVec_mulVec]

theorem embA_mem_actUni (B : BesLev D σ) (h : GA D B.A) : embA B.d B.o h ∈ actUni B := by
  rw [mem_actUni_iff]
  refine ⟨1, one_mem _, 0, ?_, ?_⟩
  · rw [embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]
  · rw [Matrix.mulVec_zero, add_zero, Matrix.mulVec_mulVec, embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec,
      vecB, ratV_mulVec_rat]
    change B.d.j0 *ᵥ (mt B.V₀ (B.o.emb (h, 1)) *ᵥ (B.o.jB *ᵥ ratV B.ζ)) = B.d.j0 *ᵥ (B.o.jB *ᵥ ratV B.ζ)
    congr 1
    rw [Matrix.mulVec_mulVec, B.o.emb_jB, mt_one, Matrix.mul_one]

theorem besGrp_le_actUni (B : BesLev D σ) : besGrp B.d B.o ≤ actUni B :=
  sup_le (flagN_le_actUni B) (by rintro _ ⟨h, rfl⟩; exact embA_mem_actUni B h)

theorem mem_besGrp_of_actUni (B : BesLev D σ) (g : GA D B.V) (hg : g ∈ actUni B) : g ∈ besGrp B.d B.o := by
  obtain ⟨u, hu, v, hX, h0⟩ := (mem_actUni_iff B g).1 hg
  have hst : B.d.levi u⁻¹ * g ∈ stabX B.d := by
    show mt B.V (B.d.levi u⁻¹ * g) ⬝ B.d.jX = B.d.jX
    rw [mt_mul, Matrix.mul_assoc, hX, ← Matrix.mul_assoc, B.d.levi_jX, Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.mul_one]
  obtain ⟨n, hn, k, hk⟩ := ((flag_jacobi_structure D B.V B.V₀ σ B.d).2.2.1 _).1 hst
  obtain ⟨b, c, rfl⟩ := ((flag_jacobi_structure D B.V B.V₀ σ B.d).2.1 n).1 hn
  have hp : B.d.p0 ⬝ mt B.V (B.d.levi u⁻¹ * g) ⬝ B.d.j0 = mt B.V₀ k := by
    rw [hk, mt_mul, mt_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, B.d.wittDecomp_projAnisotropic_unipotentMixed, Matrix.sub_mul, B.d.wittDecomp_projAnisotropic_unipotentSkew,
      Matrix.mul_assoc _ B.d.pY, B.d.pY_nC, Matrix.sub_mul, B.d.wittDecomp_projAnisotropic_anisotropicEmbedding, Matrix.mul_assoc _ B.d.pY, B.d.wittDecomp_projY_anisotropicEmbedding,
      Matrix.sub_mul, Matrix.mul_assoc, B.d.p0_j0, Matrix.mul_one, Matrix.mul_assoc _ B.d.pY, B.d.pY_j0,
      Matrix.mul_zero, sub_zero]
  have hz : mt B.V₀ k *ᵥ ratV (B.o.iB *ᵥ B.ζ) = ratV (B.o.iB *ᵥ B.ζ) := by
    have e1 : B.d.p0 ⬝ mt B.V (B.d.levi u⁻¹ * g) = B.d.p0 ⬝ mt B.V g := by
      rw [mt_mul, ← Matrix.mul_assoc, B.d.wittDecomp_projAnisotropic_levi]
    rw [← hp, e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change B.d.p0 *ᵥ (mt B.V g *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ))) = _
    rw [h0, Matrix.mulVec_add, Matrix.mulVec_mulVec, B.d.p0_j0, Matrix.one_mulVec, Matrix.mulVec_mulVec, B.d.p0_jX,
      Matrix.zero_mulVec, add_zero]
    rfl
  obtain ⟨h, rfl⟩ := fix_lineVec_emb D B.V₀ B.A B.L B.o B.ζ B.line k hz
  have hg' : g = (B.d.levi u * (B.d.nB b * B.d.nC c)) * embA B.d B.o h := by
    rw [embA_apply, mul_assoc, ← hk, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [hg']
  exact mul_mem (Subgroup.mem_sup_left (((flag_jacobi_structure D B.V B.V₀ σ B.d).1 _).2 ⟨u, hu, b, c, rfl⟩))
    (Subgroup.mem_sup_right ⟨h, rfl⟩)

theorem besselGroup_action_fourierBesselBasePoint : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), (∀ g : GA D B.V, g ∈ besGrp B.d B.o ↔ ∃ u ∈ UX D (σ + 1), mt B.V g ⬝ x0 B = x0 B ⬝ u.1) ∧ (∀ a a' : Mx D (σ + 1) (σ + 1), x0 B ⬝ a = x0 B ⬝ a' → a = a') ∧ ∀ g ∈ GQ B.V, ∀ u : UX D (σ + 1), mt B.V g ⬝ x0 B = x0 B ⬝ u.1.1 → u ∈ UXQ D (σ + 1) := by
  intro D σ B
  obtain ⟨⟨P, hP, hPx⟩, hx⟩ := fourierBesselBasePoint_leftInverse_rational D σ B
  refine ⟨fun g => ⟨fun hg => besGrp_le_actUni B hg, fun hg => mem_besGrp_of_actUni B g hg⟩, ?_, ?_⟩
  · intro a a' h
    rw [← Matrix.one_mul a, ← Matrix.one_mul a', ← hPx, Matrix.mul_assoc, Matrix.mul_assoc, h]
  · intro g hg u hgu
    have hinv : mt B.V g⁻¹ ⬝ x0 B = x0 B ⬝ (u.1⁻¹).1 := by
      have h1 : mt B.V g⁻¹ ⬝ (x0 B ⬝ u.1.1) ⬝ (u.1⁻¹).1 = x0 B ⬝ (u.1⁻¹).1 := by
        rw [← hgu, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
      rw [← h1, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    refine ⟨?_, ?_⟩
    · have e : u.1.1 = P ⬝ mt B.V g ⬝ x0 B := by
        rw [Matrix.mul_assoc, hgu, ← Matrix.mul_assoc, hPx, Matrix.one_mul]
      rw [e]; exact ratMx_mul (ratMx_mul hP ((mem_GQ_iff _ _).1 hg)) hx
    · have e : (u.1⁻¹).1 = P ⬝ mt B.V g⁻¹ ⬝ x0 B := by
        rw [Matrix.mul_assoc, hinv, ← Matrix.mul_assoc, hPx, Matrix.one_mul]
      rw [e]; exact ratMx_mul (ratMx_mul hP ((mem_GQ_iff _ _).1 (inv_mem hg))) hx

end GlobalTheory.Unf.FB

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.Core.Rk.UpInjWProof

theorem upInjW_of_aForm : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, GlobalTheory.Hk3.IsSF R SF → GlobalTheory.LiftRows.AForm R SF → GlobalTheory.LiftRows.UpInjW R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS hIrr SF hSF hA
  obtain ⟨a, ha, hAF⟩ := hA
  intro i t x hx h0
  obtain ⟨h, -, -, -, hspan, -⟩ := GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R F hC hS hIrr SF hSF i

  have hpart : ∀ c, GlobalTheory.Hk3.Wcc R SF i c ≤ LinearMap.range (R.thG i t) := by
    intro c y hy
    by_cases hc : GlobalTheory.Hk3.Wcc R SF i c = ⊥
    · rw [hc] at hy
      rw [(Submodule.mem_bot ℂ).1 hy]
      exact Submodule.zero_mem _
    · obtain ⟨z, hz, hS'⟩ := hAF i t c hc
      obtain ⟨B, -, -, hzpos, -⟩ := hz
      have hne : ((a i * z : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (mul_pos (ha i) hzpos).ne'
      refine ⟨((a i * z : ℝ) : ℂ)⁻¹ • LinearMap.adjoint (R.thG i t) y, ?_⟩
      rw [map_smul, hS' y hy, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hxr : x ∈ LinearMap.range (R.thG i t) := by
    have : x ∈ LinearMap.range (GlobalTheory.Hk3.eH R i) := ⟨x, hx⟩
    rw [← hspan] at this
    exact (iSup_le hpart) this
  obtain ⟨v, rfl⟩ := hxr
  have h1 : ⟪R.thG i t v, R.thG i t v⟫_ℂ = 0 := by
    rw [← LinearMap.adjoint_inner_right, h0, inner_zero_right]
  exact inner_self_eq_zero.1 h1

end GlobalTheory.Core.Rk.UpInjWProof
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixModel.OrthDec

theorem isThetaFunO_slice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L)
    (f : WO S T → ℂ) (y : WO L T), IsThetaFunO ψ S T f →
      IsThetaFunO ψ A T (fun w => f ((o.resS T).symm (w, y))) :=
  fun _ _ _ _ _ _ o _ y hf => GlobalTheory.BoxSlice.isThetaFunO_slice_left o hf y

end GlobalTheory.MixModel.OrthDec
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.JacUnimod

theorem jacGrp_rightInv : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (μ : Measure (jacGrp d)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  intro D V V₀ ρ d μ hμ
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨j1, j2, j3, j4, j5, -, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V₀
  have hNc : IsClosed (flagN d : Set (GA D V)) := GlobalTheory.Mem.TrueRecord.isClosed_NFlag V (isIsoSub_e d)
  obtain ⟨hlc, hsc, hbor, hcount⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (isIsoSub_e d)
  obtain ⟨ν, 𝓝, hνH, h𝓝, h𝓝1⟩ := GlobalTheory.Per.UnitN.exists_isUnitN D V ρ d.e (isIsoSub_e d)
  have hnorm := GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D V V₀ ρ d
  have hp := GlobalTheory.JacProj.exists_continuous_proj D V V₀ ρ d
  have hc := GlobalTheory.FlagModulus.map_conj_smallerUnitary_flagUnipotent_haar D V V₀ ρ d ν hνH
  let μ₀ : Measure (GA D V₀) := Measure.haar
  have hμ₀ : μ₀.IsHaarMeasure := inferInstance
  haveI := hνH
  haveI : μ₀.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V₀ μ₀ hμ₀
  haveI : ν.IsMulRightInvariant := GlobalTheory.SemiHaar.rightInv_of_fd _ ν h𝓝 (by rw [h𝓝1]; exact ENNReal.one_ne_top)
  have a := GlobalTheory.MixPer.semiMeas_isMulLeftInvariant (flagN d) d.emb0 hNc d.continuous_embed hnorm hp μ₀ ν hμ₀ hνH hc
  obtain ⟨b, c⟩ := GlobalTheory.MixPer.semiMeas_finite_on_compacts_and_open_pos (flagN d) d.emb0 hNc d.continuous_embed hnorm hp
    μ₀ ν hμ₀ hνH hc
  have hH : (semiMeas (flagN d) d.emb0 μ₀ ν).IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := b, toIsMulLeftInvariant := a, toIsOpenPosMeasure := c }
  have hR := GlobalTheory.SemiHaar.semiMeas_rightInv (flagN d) d.emb0 hNc d.continuous_embed hnorm μ₀ ν
  obtain ⟨e, -⟩ := GlobalTheory.SemiHaar.exists_homeo (flagN d) d.emb0 hnorm d.continuous_embed hp
  haveI : LocallyCompactSpace (jacGrp d) := e.symm.isClosedEmbedding.locallyCompactSpace
  let κ : Measure (jacGrp d) := semiMeas (flagN d) d.emb0 μ₀ ν
  haveI hκH : κ.IsHaarMeasure := hH
  haveI hκR : κ.IsMulRightInvariant := hR
  have hk := Measure.isMulLeftInvariant_eq_smul μ κ
  rw [hk]
  infer_instance

end GlobalTheory.JacUnimod

end
end
