module

import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle010
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle003
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle003
public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.DualLattices.Bundle002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle014
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle011
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle019
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GaGram
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XBundleOps
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle028
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import ReciprocityTheory.DualLattices.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff

@[expose] public section

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.PullPreserve

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)

section Closure

variable {O Ω V : Type} [CommRing O] [Field Ω] [Algebra O Ω] [AddCommGroup V] [Module Ω V]

theorem const_smul_mem (R : Subalgebra O Ω) (A : AddSubgroup V) (c : O) {v : V}
    (hv : v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ A, v = a • e}) :
    algebraMap O Ω c • v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ A, v = a • e} := by
  induction hv using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, e, he, rfl⟩ := hw
    exact AddSubgroup.subset_closure
      ⟨algebraMap O Ω c * a, mul_mem (R.algebraMap_mem c) ha, e, he, by rw [mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add w₁ w₂ _ _ h₁ h₂ => rw [smul_add]; exact add_mem h₁ h₂
  | neg w _ h => rw [smul_neg]; exact neg_mem h

theorem exists_const_smul_mem [IsDomain O] (R : Subalgebra O Ω) (A B : AddSubgroup V)
    (h : ∀ v ∈ A, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ B) {v : V}
    (hv : v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ A, v = a • e}) :
    ∃ c : O, c ≠ 0 ∧
      algebraMap O Ω c • v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ B, v = a • e} := by
  induction hv using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, e, he, rfl⟩ := hw
    obtain ⟨c, hc, hce⟩ := h e he
    exact ⟨c, hc, AddSubgroup.subset_closure ⟨a, ha, _, hce, smul_comm _ _ _⟩⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  | add w₁ w₂ _ _ h₁ h₂ =>
    obtain ⟨c₁, hc₁, m₁⟩ := h₁
    obtain ⟨c₂, hc₂, m₂⟩ := h₂
    refine ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, ?_⟩
    have e : algebraMap O Ω (c₁ * c₂) • (w₁ + w₂) =
        algebraMap O Ω c₂ • (algebraMap O Ω c₁ • w₁) +
          algebraMap O Ω c₁ • (algebraMap O Ω c₂ • w₂) := by
      rw [map_mul, smul_add, smul_smul, smul_smul, mul_comm]
    rw [e]
    exact add_mem (const_smul_mem R B c₂ m₁) (const_smul_mem R B c₁ m₂)
  | neg w _ h =>
    obtain ⟨c, hc, m⟩ := h
    exact ⟨c, hc, by rw [smul_neg]; exact neg_mem m⟩

theorem mem_span_scaled (R : Subalgebra O Ω) (A B : AddSubgroup V) (c : Ω)
    (h : ∀ v, v ∈ B ↔ ∃ e ∈ A, v = c • e) (v : V) :
    v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ B, v = a • e} ↔
      ∃ e ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ A, v = a • e}, v = c • e :=
  _root_.UpperTheory.Reformulated.B.Ydb6.main R A B c h v

end Closure

theorem pull_preserve : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V) (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB E'B : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsPull O x z E' E'B → (LatLE O x E E' → LatLE O (joinCoord x z) EB E'B) ∧ (SameGeneric O x E E' → SameGeneric O (joinCoord x z) EB E'B) ∧ (∀ c : Ω, IsScaled x c E.lat E'.lat → IsScaled (joinCoord x z) c EB.lat E'B.lat) := by
  apply PositivityTheory.Xgn.t_pull_preserve <;> assumption

end GlobalTheory.CompanionTheory.Ar.Num.PullPreserve
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.different_twisted_generator_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : Nat.Primes), ∃ δ : E, δ ≠ 0 ∧ ∀ j : E →+* ℂ_[ℓ], Real.log ‖j δ‖ = logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (H.rt : E)‖ ∧ Real.log ‖j (IsCMField.complexConj E δ)‖ = Real.log ‖j δ‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.RelDiff.exists_local_generator | exact GlobalTheory.CompanionTheory.Ar.Fl.RelDiff.exists_local_generator | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.RelDiff.exists_local_generator <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.lattice_good_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → (∀ τ, LocFree R n (D.af R p (χ τ)) ∧ LocFree R n (D.hh R p (χ τ)) ∧ D.af R p (χ τ) ≤ stdLat R _ ∧ ∀ i, LocFree R 1 (D.xId (χ τ) i)) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → (D.bc RC).Good₁ RC p (fun τ a => algebraMap Ω C (χ τ a)) ∧ ∀ τ, (D.bc RC).af RC p (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.af R p (χ τ)) ∧ (D.bc RC).hh RC p (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.hh R p (χ τ)) ∧ ∀ i, (D.bc RC).xId (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (algebraMap Ω C '' D.xId (χ τ) i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange.main | exact GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange.main <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.CompanionTheory.Relay.torsion_points_homomorphism_compatible : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ (T' : TorsRep G' p) (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'] (pt' : N' → (sp (R₀ := R) R ⟶ G')), IsTorsPts G' p pt' → ∀ j : G ⟶ G', IsMonHom j → ∀ K : AddSubgroup N, (∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ G), z ≫ j = 1 ↔ ∃ φ : (T.A ⧸ vanIdeal T pt K) →ₐ[R] S, spMap φ ≫ (spMap (Ideal.Quotient.mkₐ R (vanIdeal T pt K)) ≫ T.y) = z) → ∀ jN : N →+ N', (∀ x, pt' (jN x) = pt x ≫ j) → jN.ker = K ∧ ∀ g ∈ torsFun C T pt, (∀ k ∈ jN.ker, g k = 0) → g ∈ (augIdeal (torsFun C T' pt')).map (LinearMap.funLeft R C (jN : N → N')) * torsFun C T pt := by
  intro p _ C _ _ _ v R _ _ hv _ G _ _ G' _ _ T N _ _ _ pt hpt T' N' _ _ _ pt' hpt' j hj K hK jN hjN
  haveI := hj
  classical
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  have hpow : ∀ x, (pt x) ^ p = 1 := fun x => (hpt.range _).2 ⟨x, rfl⟩
  have hpow' : ∀ x, (pt' x) ^ p = 1 := fun x => (hpt'.range _).2 ⟨x, rfl⟩
  choose φ hφ hφu using fun x => T.univ R (pt x) (hpow x)
  choose φ' hφ' hφu' using fun x => T'.univ R (pt' x) (hpow' x)
  have h0' : pt' 0 = 1 := by
    have h := hpt'.add 0 0
    rw [add_zero] at h
    simpa using h.symm
  have hyp : (T.y ≫ j) ^ p = 1 := by
    rw [← MonObj.pow_comp, T.y_p, MonObj.one_comp]
  obtain ⟨ψ, hψ, -⟩ := T'.univ T.A (T.y ≫ j) hyp
  have hcomp : ∀ x, (φ x).comp ψ = φ' (jN x) := by
    intro x
    apply hφu'
    rw [← Chart.spMap_comp ψ (φ x), Category.assoc, hψ, ← Category.assoc, hφ x, hjN]
  have hker : ∀ x, jN x = 0 ↔ pt x ≫ j = 1 := by
    intro x
    rw [← hjN, ← h0']
    exact hpt'.inj.eq_iff.symm
  have hfac : ∀ x, pt x ≫ j = 1 ↔ ∀ a ∈ vanIdeal T pt (K : Set N), φ x a = 0 := by
    intro x
    rw [hK R (pt x)]
    constructor
    · rintro ⟨χ, hχ⟩ a ha
      have e : χ.comp (Ideal.Quotient.mkₐ R (vanIdeal T pt (K : Set N))) = φ x := by
        apply hφu
        rw [← Chart.spMap_comp, Category.assoc]
        exact hχ
      rw [← e, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
    · intro h
      refine ⟨Ideal.Quotient.liftₐ _ (φ x) h, ?_⟩
      rw [← Category.assoc, Chart.spMap_comp, Ideal.Quotient.liftₐ_comp]
      exact hφ x
  have hK1 : jN.ker = K := by
    ext x
    rw [AddMonoidHom.mem_ker, hker, hfac]
    constructor
    · intro h
      by_contra hx
      have hne : ∀ k ∈ K, ∃ c : T.A, φ k c ≠ φ x c := by
        intro k hk
        by_contra hall
        push_neg at hall
        have e1 : φ k = φ x := AlgHom.ext hall
        have e2 : pt k = pt x := by rw [← hφ k, ← hφ x, e1]
        exact hx (hpt.inj e2 ▸ hk)
      choose! c hc using hne
      let a : T.A := ∏ k ∈ Finset.univ.filter (· ∈ K), (c k - algebraMap R T.A (φ k (c k)))
      have ha : a ∈ vanIdeal T pt (K : Set N) := by
        rw [PositivityTheory.HtPt.Rf.mem_vanIdeal T hφ]
        intro k hk
        simp only [a, map_prod]
        apply Finset.prod_eq_zero (i := k)
        · simpa using hk
        · simp
      have h1 := h a ha
      apply_fun algebraMap R C at h1
      simp only [a, map_prod, map_sub, AlgHom.commutes, map_zero] at h1
      rw [Finset.prod_eq_zero_iff] at h1
      obtain ⟨k, hk, hk0⟩ := h1
      rw [sub_eq_zero] at hk0
      exact hc k (by simpa using hk) (hinj (by simpa using hk0)).symm
    · intro hx a ha
      exact (PositivityTheory.HtPt.Rf.mem_vanIdeal T hφ _ a).1 ha x hx
  refine ⟨hK1, ?_⟩
  intro g hg hgK
  rw [PositivityTheory.HtPt.Rf.mem_torsFun T hφ] at hg
  obtain ⟨a, rfl⟩ := hg
  have haI : a ∈ vanIdeal T pt (K : Set N) := by
    rw [PositivityTheory.HtPt.Rf.mem_vanIdeal T hφ]
    intro k hk
    have h3 := hgK k (by rw [hK1]; exact hk)
    exact hinj (by rw [map_zero]; exact h3)
  obtain ⟨J, hJ⟩ : ∃ J : Ideal T.A, J = Ideal.map ψ (RingHom.ker (φ' 0)) := ⟨_, rfl⟩
  have hIJ : vanIdeal T pt (K : Set N) ≤ J := by
    have hzp : (spMap (Ideal.Quotient.mkₐ R J) ≫ T.y) ^ p = 1 := by
      rw [← MonObj.comp_pow, T.y_p, MonObj.comp_one]
    have hqψ : (Ideal.Quotient.mkₐ R J).comp ψ = (Algebra.ofId R (T.A ⧸ J)).comp (φ' 0) := by
      apply AlgHom.ext
      intro b
      have hb : b - algebraMap R T'.A (φ' 0 b) ∈ RingHom.ker (φ' 0) := by
        simp [RingHom.mem_ker]
      rw [AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Algebra.ofId_apply,
        ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq, ← AlgHom.commutes ψ, ← map_sub, hJ]
      exact Ideal.mem_map_of_mem _ hb
    have hz1 : (spMap (Ideal.Quotient.mkₐ R J) ≫ T.y) ≫ j = 1 := by
      calc (spMap (Ideal.Quotient.mkₐ R J) ≫ T.y) ≫ j
          = spMap (Ideal.Quotient.mkₐ R J) ≫ spMap ψ ≫ T'.y := by rw [Category.assoc, hψ]
        _ = spMap ((Ideal.Quotient.mkₐ R J).comp ψ) ≫ T'.y := by
          rw [← Category.assoc, Chart.spMap_comp]
        _ = spMap ((Algebra.ofId R (T.A ⧸ J)).comp (φ' 0)) ≫ T'.y := by rw [hqψ]
        _ = spMap (Algebra.ofId R (T.A ⧸ J)) ≫ pt' 0 := by
          rw [← Chart.spMap_comp, Category.assoc, hφ' 0]
        _ = 1 := by rw [h0', MonObj.comp_one]
    obtain ⟨χ, hχ⟩ := (hK (T.A ⧸ J) (spMap (Ideal.Quotient.mkₐ R J) ≫ T.y)).1 hz1
    obtain ⟨w, -, hu⟩ := T.univ (T.A ⧸ J) (spMap (Ideal.Quotient.mkₐ R J) ≫ T.y) hzp
    have e : χ.comp (Ideal.Quotient.mkₐ R (vanIdeal T pt (K : Set N))) = Ideal.Quotient.mkₐ R J := by
      rw [hu _ rfl]
      apply hu
      rw [← Chart.spMap_comp, Category.assoc]
      exact hχ
    intro b hb
    have h2 := AlgHom.congr_fun e b
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h2
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2.symm
  have ha : a ∈ J := hIJ haI
  rw [hJ] at ha
  change a ∈ Submodule.span T.A (⇑ψ '' (RingHom.ker (φ' 0) : Set T'.A)) at ha
  clear hgK haI hIJ hJ
  suffices H : ∀ c : T.A, (fun x => algebraMap R C (φ x (c * a))) ∈
      (augIdeal (torsFun C T' pt')).map (LinearMap.funLeft R C (jN : N → N')) * torsFun C T pt by
    have H1 := H 1
    rwa [_root_.one_mul] at H1
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    intro c
    have e : (fun y => algebraMap R C (φ y (c * ψ b))) =
        (fun y => algebraMap R C (φ y (ψ b))) * (fun y => algebraMap R C (φ y c)) := by
      funext y
      simp [map_mul, mul_comm]
    rw [e]
    apply Submodule.mul_mem_mul
    · rw [Submodule.mem_map]
      refine ⟨fun y => algebraMap R C (φ' y b), ?_, ?_⟩
      · rw [augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply]
        refine ⟨(PositivityTheory.HtPt.Rf.mem_torsFun T' hφ' _).2 ⟨b, rfl⟩, ?_⟩
        rw [SetLike.mem_coe, RingHom.mem_ker] at hb
        simp only [hb, map_zero]
      · funext y
        rw [LinearMap.funLeft_apply, ← hcomp y, AlgHom.comp_apply]
    · exact (PositivityTheory.HtPt.Rf.mem_torsFun T hφ _).2 ⟨c, rfl⟩
  | zero =>
    intro c
    simp only [mul_zero, map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    intro c
    have h4 := Submodule.add_mem _ (hx c) (hy c)
    convert h4 using 1
    funext z
    simp [mul_add]
  | smul r x _ hx =>
    intro c
    convert hx (c * r) using 1
    funext z
    rw [smul_eq_mul, _root_.mul_assoc]
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.CompanionTheory.Relay.torsion_points_hopf_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → (∃ AA : HopfOrder (C := C) R N, AA.carrier = torsFun C T pt) ∧ (∀ a : T.A, (∀ φ : T.A →ₐ[R] R, φ a = 0) → a = 0) ∧ (∀ x, ∃! φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt x) ∧ (∀ φ : T.A →ₐ[R] R, ∃ x, spMap φ ≫ T.y = pt x) ∧ ∀ x : N, p • x = 0 := by
  first | exact @PositivityTheory.HtPt.Rf.tors_hopf | exact PositivityTheory.HtPt.Rf.tors_hopf
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily

theorem main : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V], (∀ Γ : (∀ k, ι k) → AddSubgroup V, IsLatFamily O x Γ → (∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (Γ s)) → ∃ E : ChartBundle O (mseg x) N V, ∀ s, mseg x s ≠ 0 → E.lat s = Γ s) ∧ ∀ E : ChartBundle O (mseg x) N V, IsLatFamily O x E.lat ∧ ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (E.lat s) :=
  @PositivityTheory.Xgn.t_bundle_of_family

end GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily
end

section

open GlobalTheory.CompanionTheory.Ar.HT NumberField TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem htChart_of_projective_module : ∀ (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (p R N : ℕ) (W Ω : Type) [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Projective A W] [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (j : W →ₗ[A] Ω), IsBaseChange K j → ∀ (ρ : 𝓞 E →+* Module.End A W) (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)) (h : (Fin N → 𝓞 E) →+ W), (∀ x, e x x = 0) → (∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv c a • y)) → (∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ R), ∃ x, e x = φ) → (∀ x, e x = 0 → ∃ x', x = (p ^ R) • x') → (∀ (a : 𝓞 E) x, ∃ y, h (a • x) = ρ a (h x) + (p ^ R) • y) → ∃ D : HTChart A K c p R N Ω, D.om = LinearMap.range j ∧ D.e = e ∧ (∀ x, D.h x = j (h x)) ∧ ∀ a w, D.ρΩ a (j w) = j (ρ a w) :=
  @PositivityTheory.HtPt.Htat.chart_build

end GlobalTheory.CompanionTheory.Ar.HT
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem tower_pdiv_exists : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L), ∃ (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate), X.Realises G e τ ∧ G.height = Module.finrank ℤ La ∧ ∃ j : ℤ_[p] ⊗[ℤ] La ≃ₗ[ℤ_[p]] G.Tate, ∀ a, j (1 ⊗ₜ a) = τ a :=
  @PositivityTheory.HtPt.Twpdiv.tower_pdiv

end GlobalTheory.CompanionTheory.Ar.HT
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi
open Coalgebra Bialgebra PositivityTheory.HtPt.Twpdiv in

theorem _root_.GlobalTheory.T.divisible_group_tower_compatibility :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
      (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C]
      (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O)
      (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La]
      (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L)
      (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate)
      (hre : X.Realises G e τ),
      (∀ (φ : La →+ La) (dφ : L →ₗ[O] L), X.Acts φ dφ → ∃ f : G ⟶ G,
        (∀ a, tateMap G G O f (τ a) = τ (φ a)) ∧ ∀ n (g : G.A n) (a : La),
          (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a))) ∧
      ∀ (H : PDivGroup p O) (f f' : G ⟶ H),
        (∀ a, tateMap G H O f (τ a) = tateMap G H O f' (τ a)) → f = f' := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO La _ _ _ L _ _ X G e τ hre
  let ev (n : ℕ) (t : LevGrp La p n) : G.A n →ₐ[O] O := (evalAt (X.A n) t).comp (e n).toAlgHom
  have ev_apply (n : ℕ) (t : LevGrp La p n) (g : G.A n) : ev n t g = (e n g).1 t := rfl
  have ev_sep (n : ℕ) : PositivityTheory.HtPt.Twpdiv.Sep (ev n) :=
    fun _ _ h => (e n).injective (Subtype.ext (funext h))
  have ev_lev (n : ℕ) (a : La) : ev n (lev p n a) = (τ a).pt n :=
    AlgHom.ext fun g => (hre.pt a n g).symm
  have tate_pt {H : PDivGroup p O} (f : G ⟶ H) (a : La) (n : ℕ) (g : H.A n) :
      (tateMap G H O f (τ a)).pt n g = (τ a).pt n (f.app n g) := rfl
  constructor
  · intro φ dφ h
    let levMap (n : ℕ) : LevGrp La p n →* LevGrp La p n :=
      AddMonoidHom.toMultiplicative (Submodule.mapQ _ _ φ.toIntLinearMap (by
        rintro _ ⟨b, rfl⟩
        exact ⟨φ b, (map_nsmul φ _ b).symm⟩)).toAddMonoidHom
    have levMap_lev (n : ℕ) (a : La) : levMap n (lev p n a) = lev p n (φ a) := rfl
    have liftable (n : ℕ) (g : G.A n) : ∃ u : G.A n, ∀ t, ev n t u = ev n (levMap n t) g := by
      let pulled (t : LevGrp La p n) : O := (e n g).1 (levMap n t)
      have hpulled : pulled ∈ X.A n :=
        (h n (e n g).1 pulled fun a => congrArg (e n g).1 (levMap_lev n a)).1 (e n g).2
      let u : X.A n := ⟨pulled, hpulled⟩
      refine ⟨(e n).symm u, fun t => ?_⟩
      rw [ev_apply, AlgEquiv.apply_symm_apply, ev_apply]
    let pull (n : ℕ) : G.A n →ₐ[O] G.A n :=
      Ord.liftTo (ev n) (ev_sep n) (fun t => ev n (levMap n t)) (liftable n)
    have ev_pull (n : ℕ) (t : LevGrp La p n) : (ev n t).comp (pull n) = ev n (levMap n t) :=
      Ord.ev_liftTo _ _ _ _ t
    have pull_apply (n : ℕ) (t : LevGrp La p n) (g : G.A n) :
        ev n t (pull n g) = ev n (levMap n t) g := DFunLike.congr_fun (ev_pull n t) g
    have pull_lev (n : ℕ) (a : La) (g : G.A n) :
        ev n (lev p n a) (pull n g) = ev n (lev p n (φ a)) g := by
      rw [pull_apply, levMap_lev]
    have ev_one (n : ℕ) (g : G.A n) : ev n 1 g = counit (R := O) g := by
      rw [← lev_zero p n, ev_lev, map_zero]
      rfl
    have ev_mul (n : ℕ) (s t : LevGrp La p n) (g : G.A n) :
        pair (ev n s) (ev n t) (comul (R := O) g) = ev n (s * t) g := by
      obtain ⟨a, rfl⟩ := lev_surjective p n s
      obtain ⟨b, rfl⟩ := lev_surjective p n t
      rw [← lev_add, ev_lev, ev_lev, ev_lev, map_add]
      exact (AlgHom.convMul_apply ((τ a).conv n) ((τ b).conv n) g).symm
    let app (n : ℕ) : G.A n →ₐc[O] G.A n :=
      BialgHom.ofAlgHom (pull n)
        (AlgHom.ext fun g => by
          change counit (R := O) (pull n g) = counit (R := O) g
          rw [← ev_one, ← ev_one, pull_apply, map_one])
        (AlgHom.ext fun g => (ev_sep n).pair (ev_sep n) _ _ fun z => by
          change pair (ev n z.1) (ev n z.2) (Algebra.TensorProduct.map _ _ (comul (R := O) g)) =
            pair (ev n z.1) (ev n z.2) (comul (R := O) (pull n g))
          rw [pair_map, ev_pull, ev_pull, ev_mul, ev_mul, pull_apply, map_mul])
    let f : G ⟶ G :=
      { app := app
        comm n := BialgHom.ext fun g => ev_sep n _ _ fun t => by
          obtain ⟨a, rfl⟩ := lev_surjective p n t
          calc
            ev n (lev p n a) (G.res n (pull (n + 1) g)) =
                ev (n + 1) (lev p (n + 1) (p • a)) (pull (n + 1) g) := hre.res n _ a
            _ = ev (n + 1) (lev p (n + 1) (φ (p • a))) g := pull_lev (n + 1) (p • a) g
            _ = ev (n + 1) (lev p (n + 1) (p • φ a)) g := by rw [map_nsmul]
            _ = ev n (lev p n (φ a)) (G.res n g) := (hre.res n g (φ a)).symm
            _ = ev n (lev p n a) (pull n (G.res n g)) := (pull_lev n a (G.res n g)).symm }
    refine ⟨f, fun a => TateOver.ext (funext fun n => AlgHom.ext fun g => ?_), fun n g a => pull_lev n a g⟩
    rw [tate_pt, ← ev_lev, ← ev_lev]
    exact pull_lev n a g
  · intro H f f' hf
    refine GlobalTheory.PDivGroup.Hom.ext (funext fun n => BialgHom.ext fun g => ev_sep n _ _ fun t => ?_)
    obtain ⟨a, rfl⟩ := lev_surjective p n t
    rw [ev_lev, ← tate_pt, ← tate_pt, hf]
end

section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem gram_integral_unit_mod : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (σ : E →+* K) (d : A), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → GeneratesDiff σ d → ∃ G H Z Z' : Matrix (Fin N) (Fin N) A, (∀ i j, algebraMap A K (G i j) = D.gram σ d i j) ∧ G * H = 1 + ((p : A) ^ R) • Z ∧ H * G = 1 + ((p : A) ^ R) • Z' :=
  @PositivityTheory.HtPt.Ga.gram_unit

end GlobalTheory.CompanionTheory.Ar.HT
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.BundleOps

theorem main : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), (∀ (N N₁ : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (F : ChartBundle O (mseg x) N₁ V₁), ∃ P : ChartBundle O (mseg x) (N + N₁) (V × V₁), ∀ s, mseg x s ≠ 0 → P.lat s = (E.lat s).prod (F.lat s)) ∧ (∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V) (c : Ω), c ≠ 0 → ∃ E' : ChartBundle O (mseg x) N V, IsScaled x c E.lat E'.lat) ∧ (∀ (u : Ω) (a : K → ℤ), u ≠ 0 → ∃ A : ChartBundle O (mseg x) 1 Ω, IsLine O x u a A.lat) ∧ (∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (t : Module.Basis (Fin N) Ω V), ∃ T : ChartBundle O (mseg x) N V, ∀ s, mseg x s ≠ 0 → ∀ v, v ∈ T.lat s ↔ ∀ i, t.repr v i ∈ chartRing O (mseg x) s) ∧ (∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω), Function.Bijective β.flip → ∃ F : ChartBundle O (mseg x) N V₁, IsDualLat O x β E.lat F.lat) :=
  @PositivityTheory.Xgn.t_bundle_ops

end GlobalTheory.CompanionTheory.Ar.BundleOps
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.formal_linear_term_composition : ∀ (R : Type) [CommRing R] (d : ℕ) (φ ψ : Pt R 1 d), (∀ i, constantCoeff (φ i) = 0) → (∀ i, constantCoeff (ψ i) = 0) → lin (comp1 φ ψ) 1 = lin φ 1 * lin ψ 1 ∧ lin (pt R (n := 1) d 0) 1 = 1 ∧ ∀ p : ℕ, 1 ≤ p → lin (comp1 φ (ptPow R d p 0)) p = lin φ 1 ∧ lin (comp1 φ (comp1 ψ (ptPow R d p 0))) p = lin φ 1 * lin ψ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.lin_comp_chain | exact GlobalTheory.CompanionTheory.Ar.Conj.lin_comp_chain | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.lin_comp_chain <;> assumption)
end
