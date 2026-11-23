module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle203
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle014
public import Formalism.LocalToGlobal.HermitianForms.Bundle005
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle204
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle206
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle209
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle168
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle205
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle149

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

theorem _root_.GlobalTheory.T.exists_algebraicModularForm_mul_archInvariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n) (f : algForms W) (e : UA E n → ℂ), IsAutFormU e → (∀ g, ∀ x ∈ infU E n, e (g * x) = e g) → ∃ f' : algForms W, ∀ v g, f'.1 v g = e g * f.1 v g := by
  first | (exact @GlobalTheory.AlgMul.exists_mul_algForms) | (exact GlobalTheory.AlgMul.exists_mul_algForms) | (intros; apply GlobalTheory.AlgMul.exists_mul_algForms  <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

theorem _root_.GlobalTheory.T.cuspidal_traceMatrixUnits_acts_by_sum_infinitesimalCharacter : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : GlobalTheory.CuspRep.CuspSub E a) (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar τ m → ∀ φ ∈ π.V, (∑ i : Fin a, GlobalTheory.CuspRep.Eop τ i i) φ = m.sum • φ := by
  first | exact @GlobalTheory.trace_Eop_of_hasInfChar | exact GlobalTheory.trace_Eop_of_hasInfChar | (intros; apply GlobalTheory.trace_Eop_of_hasInfChar <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

theorem _root_.GlobalTheory.T.splitCentreDerivative_eq_sum_diagonalMatrixUnits : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), GlobalTheory.ResW.zc E a = ∑ τ : E →+* ℂ, ∑ i : Fin a, GlobalTheory.CuspRep.Eop τ i i := by
  first | exact @GlobalTheory.ResW.zc_eq_sum_Eop | exact GlobalTheory.ResW.zc_eq_sum_Eop | (intros; apply GlobalTheory.ResW.zc_eq_sum_Eop <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.jumpWindowBlockExponentCondition_of_jumpWindow : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (h₁ : ℕ), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → D.R.t ≤ h₁ → GlobalTheory.BlockWindow.JumpWindow D i r π h₁ → GlobalTheory.BlockWindow.JointTB D HW F i r π h₁ h₁ (GlobalTheory.HubLoc.cBnum (D.nd.l i) h₁ D.R.t (4 * D.R.n * D.R.nV)) := by
  first | exact @GlobalTheory.BlockWindow.jointTB_of_jumpWindow | exact GlobalTheory.BlockWindow.jointTB_of_jumpWindow | (intros; apply GlobalTheory.BlockWindow.jointTB_of_jumpWindow <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

theorem _root_.GlobalTheory.T.pair_kernel_maps_step_weight_values : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m → UnfIs O i (nuT D u i) → ∀ (c : C.cls i) (c' : C.cls (i + 1)) f, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) f → IsVal (O.frm (i + 1)) (lamTG M (i + 1)) (RingHom.id ℂ) (C.Kmap i c c' f) := by
  first | exact @GlobalTheory.KerJ.Kmap_isVal | exact GlobalTheory.KerJ.Kmap_isVal | (intros; apply GlobalTheory.KerJ.Kmap_isVal <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

theorem _root_.GlobalTheory.T.integralJets_normalisedTheta_translates_away_disc : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ D.host.d ha hd lam hlam h Λ θ p ι → p ≠ D.host.d → (p = 3 → D.host.d % 3 = 2) → ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (M : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < M → ¬ p ∣ M → (∀ k, (M : ℂ) • t k ∈ Λ) → ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a₀ b₀ D.host.d ha hd lam hlam) Λ (v j)) → ∀ (ν : Type) [Fintype ν] (A : J → ν → ℂ_[p]), (∀ j x, ‖A j x‖ ≤ 1) → JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A)) := by
  first | exact @GlobalTheory.ThLoc.jetsIntegral_away_disc | exact GlobalTheory.ThLoc.jetsIntegral_away_disc | (intros; apply GlobalTheory.ThLoc.jetsIntegral_away_disc <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

theorem _root_.GlobalTheory.T.normalisedThetaCMCurveTheorems_of_algebraicTranslates : Formalism.L2.KerInert.AlgTAll → GlobalTheory.ThLoc.Inputs := by
  first | exact @GlobalTheory.ThLoc.inputs_of_algT | exact GlobalTheory.ThLoc.inputs_of_algT | (intros; apply GlobalTheory.ThLoc.inputs_of_algT <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

theorem _root_.GlobalTheory.T.pair_kernel_term_target_stabiliser_law : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m → UnfIs O i (nuT D u i) → ∀ (c : C.cls i) (c' : C.cls (i + 1)), Differentiable ℂ (O.Th i c c') → ∀ g, TermLaw O i c c' g → ∀ f, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) f → LawAt O (i + 1) g (C.Kmap i c c' f) := by
  first | exact @GlobalTheory.KerJ.lawAt_Kmap | exact GlobalTheory.KerJ.lawAt_Kmap | (intros; apply GlobalTheory.KerJ.lawAt_Kmap <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.goodForms_baseLevel_iff_goodProjection : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ i (x : (R.HW i (sg0 D A)).H), (R.HW i _).e x ∈ R.Wat i (sg0 D A) (R.levL F false (sg0 D A)) ↔ eH R i x = x ∧ ∀ p : F.P0, R.gW i (sg0 D A) p x = sg0 D A ((F.ψ0⁻¹ p : D.what₂.LLˣ) : D.what₂.LL) • x := by
  first | exact @GlobalTheory.Hk3.goodForms_baseLevel | exact GlobalTheory.Hk3.goodForms_baseLevel | (intros; apply GlobalTheory.Hk3.goodForms_baseLevel <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.doubleCosetOperator_eq_labelOperator_localReps : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank), IsBaseFrame V β Λ N → ∀ P : Pl D.host.E, ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → ∀ (d : List ℤ) (x : Bridge.Gf V) (B : Finset (Bridge.Gf V)), d.Pairwise (fun a b => b ≤ a) → _root_.GlobalTheory.Hk3.IsLabElt V P d x → (∀ a ∈ B, _root_.GlobalTheory.Hk3.IsLocElt V P a) → Bridge.IsDC (levEnv V β L).J x B → IsLab V P d ∧ ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (Φ : Bridge.Gf V → W), (∀ h (k : (levEnv V β L).J), _root_.GlobalTheory.Hk3.IsLocElt V P k → Φ (h * k) = Φ h) → Bridge.dcOp B Φ = hkF V P (Finsupp.single d 1) Φ := by
  first | exact @GlobalTheory.HkDict.dcOp_eq_label | exact GlobalTheory.HkDict.dcOp_eq_label | (intros; apply GlobalTheory.HkDict.dcOp_eq_label <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LabChar

theorem conjPl_eq_cP {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) : _root_.Formalism.DivisionValues.conjPl P = GlobalTheory.IdemSupport.cP P := by
  apply HeightOneSpectrum.ext
  show P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) = P.asIdeal.comap (GlobalTheory.IdemSupport.cO D).toRingHom
  have h : Formalism.DivisionValues.cO D.host.E = GlobalTheory.IdemSupport.cO D := rfl
  rw [h]
  have inv : ∀ y, GlobalTheory.IdemSupport.cO D (GlobalTheory.IdemSupport.cO D y) = y := fun y => by
    apply RingOfIntegers.ext
    simp [GlobalTheory.IdemSupport.cO]
  ext x
  rw [Ideal.mem_map_of_equiv, Ideal.mem_comap]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show GlobalTheory.IdemSupport.cO D (GlobalTheory.IdemSupport.cO D y) ∈ P.asIdeal
    rwa [inv]
  · intro hx
    exact ⟨_, hx, inv x⟩

theorem eq_of_fixed {D : D7} (V : HSp D) {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D}
    (h : IsPrimeIdem P e f) (hc : _root_.Formalism.DivisionValues.conjPl P = P) : f = e := by
  rcases id h with ⟨hs, rfl⟩ | ⟨rfl, -⟩
  · exfalso
    have H := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
    have hcc : Formalism.IndefR.Lev.IsConjPl P P := by
      rw [GlobalTheory.IdemSupport.isConjPl_iff, ← conjPl_eq_cP, hc]
    have hs' := H.2.2.2 P P e hs hcc
    have h' : IsPrimeIdem P (cA D e) (cA D e + cA D (cA D e)) := Or.inl ⟨hs', rfl⟩
    have hee := ((H.2.2.1 P e _ h).2.2.2.1 _ _ h').1
    obtain ⟨⟨h1, h2, -⟩, ht⟩ := hs
    have e0 : e = 0 := by
      rw [hee, h1] at h2
      exact h2
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    have := (ht x hx0).1 hx
    apply this
    rw [e0, zero_mul, map_zero]
    exact zero_mem _
  · rfl

theorem fixed_of_tie {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (h : IsPrimeIdem P e e) : _root_.Formalism.DivisionValues.conjPl P = P := by
  rcases h with ⟨hs, he⟩ | ⟨-, ⟨v, ε, -, rfl⟩, ht⟩
  · exfalso
    obtain ⟨⟨h1, h2, -⟩, ht⟩ := hs
    have hc : cA D e = 0 := by
      have := he
      nth_rewrite 1 [← add_zero e] at this
      exact (add_left_cancel this).symm
    have e0 : e = 0 := by
      have := congrArg (cA D) hc
      rwa [cA_cA, map_zero] at this
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    apply (ht x hx0).1 hx
    rw [e0, zero_mul, map_zero]
    exact zero_mem _
  · have ht' := GlobalTheory.IdemSupport.Comparison₂.conj ht
    rw [GlobalTheory.IdemSupport.cA_algebraMap] at ht'
    rw [conjPl_eq_cP]
    apply HeightOneSpectrum.ext
    ext x
    by_cases hx : x = 0
    · subst hx; simp only [zero_mem]
    · rw [ht' x hx, ht x hx]

theorem lab_char (hU : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (d d' : List ℤ) (g : GA D V), IsPrimeIdem P e f → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.Pairwise (fun a b => b ≤ a) → d'.Pairwise (fun a b => b ≤ a) → DivAt V e (ϖ : D.host.E) d g → DivAt V e (ϖ : D.host.E) d' g → d = d') (hS : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (d : List ℤ), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.length = V.rank → ∃ g : GA D V, SuppF V (e + cA D e) g ∧ DivAt V e (ϖ : D.host.E) d g) (hI : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (x : 𝓞 D.host.F) (ϖ : 𝓞 D.host.E) (d : List ℤ), IsPrimeIdem P e e → (ϖ : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.length = V.rank → dualLab d = d → ∃ g : GA D V, SuppF V e g ∧ DivAt V e (ϖ : D.host.E) d g) : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ d : List ℤ, IsLab V P d ↔ d.length = V.rank ∧ d.Pairwise (fun a b => b ≤ a) ∧ (_root_.Formalism.DivisionValues.conjPl P = P → dualLab d = d) := by
  intro D V P d
  have H := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  constructor
  · rintro ⟨R, e, f, ϖ, α, -, h, h1, h2, hd, -, -, hα, hD, -, -⟩
    refine ⟨hD.1, hd, fun hc => ?_⟩
    obtain rfl := eq_of_fixed V h hc
    have he : f * f = f := (H.2.2.1 P f f h).1
    obtain ⟨⟨a, b, ha, -, hb, -, hinv⟩, -⟩ :=
      GlobalTheory.InertDoubleCoset.inert_double_cosets V P f h (GlobalTheory.SphLabelOps.exists_real_unif D P) α hα
    have hϖ0 := GlobalTheory.SphLabelOps.unif_ne_zero h2
    have hx := GlobalTheory.DivDual.divAt_inv_and_mul V f (ϖ : D.host.E) d α he hϖ0 hD
    have h3 := hx.2 a ha b hb
    rw [← hinv] at h3
    exact hU V P f f ϖ (dualLab d) d α⁻¹ h h1 h2 (GlobalTheory.SphLabelOps.dualLab_pairwise hd) hd hx.1 h3
  · rintro ⟨hl, hd, hs⟩
    obtain ⟨e, f, h⟩ := H.2.1 P
    obtain ⟨x, y, hy, h1, h2⟩ := GlobalTheory.SphLabelOps.exists_real_unif D P
    by_cases hc : _root_.Formalism.DivisionValues.conjPl P = P
    · obtain rfl := eq_of_fixed V h hc
      obtain ⟨g, hg, hD⟩ := hI V P f x y d h hy h1 h2 hl (hs hc)
      exact GlobalTheory.SphLabelOps.isLab_of_divAt h h1 h2 hd hg hD
    · rcases id h with ⟨hi, rfl⟩ | ⟨rfl, -⟩
      · obtain ⟨g, hg, hD⟩ := hS V P e y d hi h1 h2 hl
        exact GlobalTheory.SphLabelOps.isLab_of_divAt h h1 h2 hd hg hD
      · exact absurd (fixed_of_tie h) hc

theorem labels_char : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ d : List ℤ, IsLab V P d ↔ d.length = V.rank ∧ d.Pairwise (fun a b => b ≤ a) ∧ (_root_.Formalism.DivisionValues.conjPl P = P → dualLab d = d) :=
  lab_char GlobalTheory.T.elementaryDivisorsAtPrime_unique GlobalTheory.T.exists_unitary_elementaryDivisors_splitPrime GlobalTheory.T.exists_unitary_elementaryDivisors_inertPrime

end GlobalTheory.LabChar
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.ConjMatch

variable {D : D7}

theorem conj_eq_cP (P : Pl D.host.E) : Formalism.DivisionValues.conjPl P = GlobalTheory.IdemSupport.cP P :=
  (GlobalTheory.IdemSupport.isConjPl_iff P _).1 (GlobalTheory.SplitHeckeAdj.isConjPl_conj P)

theorem conj_conj (P : Pl D.host.E) : Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl P) = P := by
  rw [conj_eq_cP, conj_eq_cP]
  apply HeightOneSpectrum.ext
  ext x
  rw [GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.cO_cO]

theorem isPrimeIdem_conj {P : Pl D.host.E} {e f : AE D} (h : IsPrimeIdem P e f) :
    IsPrimeIdem (Formalism.DivisionValues.conjPl P) (cA D e) f := by
  rcases h with ⟨h, rfl⟩ | ⟨rfl, ⟨v, ε, hε, rfl⟩, ht⟩
  · have h1 : Formalism.L2.NTheta.IsIdemAt (cA D e) (Formalism.DivisionValues.conjPl P) := by
      rw [conj_eq_cP]
      obtain ⟨⟨h1, h2, v, ε, hε, h3⟩, ht⟩ := h
      exact ⟨⟨by rw [← RingHom.map_mul, h1], by rw [Formalism.L2.Theta.cA_cA, mul_comm, h2], v, ε, hε,
        by rw [Formalism.L2.Theta.cA_cA, add_comm, h3]⟩, GlobalTheory.IdemSupport.Comparison₂.conj ht⟩
    exact Or.inl ⟨h1, by rw [Formalism.L2.Theta.cA_cA, add_comm]⟩
  · have hc := GlobalTheory.IdemSupport.cA_algebraMap (D := D) ε
    have ht' := GlobalTheory.IdemSupport.Comparison₂.conj (P := P) ht
    rw [← conj_eq_cP] at ht'
    rw [hc] at ht' ⊢
    exact Or.inr ⟨rfl, ⟨v, ε, hε, rfl⟩, ht'⟩

theorem isVacAt_conj (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (P : Pl D.host.E) (f : WO S T → ℂ)
    (h : IsVacAt ψ S T P f) : IsVacAt ψ S T (Formalism.DivisionValues.conjPl P) f := by
  refine ⟨h.1, fun e f' hP u hu hh => h.2 (cA D e) f' ?_ u hu ?_⟩
  · have := isPrimeIdem_conj hP
    rwa [conj_conj] at this
  · rw [Formalism.L2.Theta.cA_cA]
    exact hh.symm

theorem one_mem_hyp (V : HSp D) (P : Pl D.host.E) : (1 : GA D V) ∈ hyp V P := by
  obtain ⟨e, f, h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem (GlobalTheory.IdemSupport.exists_comp D).choose_spec P
  refine ⟨⟨one_mem _, fun y => ?_, fun v hv => absurd hv (Finset.notMem_empty v)⟩, e, f, h,
    (GlobalTheory.IdemSupport.suppGroup V f).one_mem⟩
  rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one, Matrix.one_mulVec]

theorem match_conj : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → (∀ f, IsVacAt ψ S T (_root_.Formalism.DivisionValues.conjPl P) f ↔ IsVacAt ψ S T P f) ∧ (VacFix ψ om P → VacFix ψ om (_root_.Formalism.DivisionValues.conjPl P) ∧ ∀ cS cT, Match ψ om (_root_.Formalism.DivisionValues.conjPl P) cS cT ↔ Match ψ om P (dualC cS) (dualC cT)) := by
  intro D ψ S T χS χT om P _
  have hv : ∀ f, IsVacAt ψ S T (_root_.Formalism.DivisionValues.conjPl P) f ↔ IsVacAt ψ S T P f := fun f =>
    ⟨fun h => by have := isVacAt_conj ψ S T _ f h; rwa [conj_conj] at this, isVacAt_conj ψ S T P f⟩
  refine ⟨hv, fun hF => ?_⟩
  have hS := GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel S P
  have hT := GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel T P
  refine ⟨fun f hf k hk k' hk' => hF f ((hv f).1 hf) k (hS.1 ▸ hk) k' (hT.1 ▸ hk'), fun cS cT => ?_⟩
  have eS : ∀ f, IsVacAt ψ S T P f → ∀ c, opOf (om.comp (MonoidHom.inl _ _)) (_root_.Formalism.DivisionValues.conjPl P) c f =
      opOf (om.comp (MonoidHom.inl _ _)) P (dualC c) f := fun f hf c =>
    hS.2.2 c _ (om.comp (MonoidHom.inl _ _)) f fun k hk => hF f hf k hk 1 (one_mem_hyp T P)
  have eT : ∀ f, IsVacAt ψ S T P f → ∀ c, opOf (om.comp (MonoidHom.inr _ _)) (_root_.Formalism.DivisionValues.conjPl P) c f =
      opOf (om.comp (MonoidHom.inr _ _)) P (dualC c) f := fun f hf c =>
    hT.2.2 c _ (om.comp (MonoidHom.inr _ _)) f fun k hk => hF f hf 1 (one_mem_hyp S P) k hk
  constructor
  · intro h f hf
    rw [← eS f hf, ← eT f hf]
    exact h f ((hv f).2 hf)
  · intro h f hf
    have hf' := (hv f).1 hf
    rw [eS f hf', eT f hf']
    exact h f hf'

end GlobalTheory.Hk3.ConjMatch

end
end
