module

public import Formalism.LocalRingCardinality.DataForced
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceDualExpansionOrbitLength
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle002
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle085
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle106
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle111
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle006
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Formalism.ConjugateSelfDual.Bundle001
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle149
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle015
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle003
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFrobCong
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGBasic
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle022
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle016
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle004
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedStatus
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.traceDual_expansion_orbitLength : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p), TrDual (nP D p) σ om oms → ∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 → ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0 := by
  first | exact @GlobalTheory.KerStd.HypCoord.trDual_expand | exact GlobalTheory.KerStd.HypCoord.trDual_expand | (intros; apply GlobalTheory.KerStd.HypCoord.trDual_expand <;> assumption)
end

section

open Formalism.BasicNotions Formalism.L2 Formalism.L2.NG Formalism.AUTREP Formalism.IndefR.principalLevelFrame

namespace GlobalTheory

theorem finTyp_invariant_form_of_isotIn : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (B : A → A → ℂ), (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z) → (∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x)) → (∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) → (∀ h, ∀ x ∈ C, ρ h x ∈ C) → (∀ h, ∀ x ∈ C, ∀ y ∈ C, B (ρ h x) (ρ h y) = B x y) → ∀ π : FinTyp D.host.E n, isotIn (D := D) ρ C π ≠ ⊥ → ∃ B' : π.S → π.S → ℂ, (∀ x y z (c : ℂ), B' x (y + c • z) = B' x y + c * B' x z) ∧ (∀ x y, B' x y = starRingEnd ℂ (B' y x)) ∧ (∀ x, x ≠ 0 → 0 < (B' x x).re) ∧ ∀ h (x y x' y' : π.S), (x' : GAf D.host.E n → ℂ) = rt D.host.E n h x → (y' : GAf D.host.E n → ℂ) = rt D.host.E n h y → B' x' y' = B' x y := by
  intro D n A _ _ ρ C B hlin hherm hpos _hstab hinv π hne

  obtain ⟨Φ, ⟨hΦe, hΦC⟩, hΦne⟩ : ∃ Φ : π.S →ₗ[ℂ] A, (IsEqvA ρ π Φ ∧ LinearMap.range Φ ≤ C) ∧ LinearMap.range Φ ≠ ⊥ := by
    by_contra hcon
    push_neg at hcon
    apply hne
    unfold isotIn
    refine iSup_eq_bot.2 fun Φ => iSup_eq_bot.2 fun hΦ => hcon Φ hΦ
  have hmemC : ∀ x : π.S, Φ x ∈ C := fun x => hΦC (LinearMap.mem_range_self Φ x)

  let S' : Submodule ℂ (GAf D.host.E n → ℂ) := (LinearMap.ker Φ).map π.S.subtype
  have hS'le : S' ≤ π.S := by
    rintro f ⟨k, _, rfl⟩
    exact k.2
  have hS'st : ∀ h, ∀ f ∈ S', rt D.host.E n h f ∈ S' := by
    rintro h f ⟨k, hk, rfl⟩
    refine ⟨⟨rt D.host.E n h k, π.stable h k k.2⟩, ?_, rfl⟩
    have hk' : Φ k = 0 := hk
    show Φ _ = 0
    rw [hΦe h k, hk', map_zero]
  have hinj : ∀ x : π.S, Φ x = 0 → x = 0 := by
    intro x hx
    rcases π.irr S' hS'le hS'st with h0 | hall
    · have : (x : GAf D.host.E n → ℂ) ∈ S' := ⟨x, hx, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact Subtype.ext this
    · exfalso
      apply hΦne
      rw [eq_bot_iff]
      rintro a ⟨y, rfl⟩
      have : (y : GAf D.host.E n → ℂ) ∈ S' := by rw [hall]; exact y.2
      obtain ⟨k, hk, hky⟩ := this
      have : k = y := Subtype.ext hky
      subst this
      have hk' : Φ k = 0 := hk
      exact (Submodule.mem_bot ℂ).2 hk'
  refine ⟨fun x y => B (Φ x) (Φ y), ?_, ?_, ?_, ?_⟩
  · intro x y z c
    simp only [map_add (f := _), map_smul]
    exact hlin _ (hmemC x) _ (hmemC y) _ (hmemC z) c
  · intro x y
    exact hherm _ (hmemC x) _ (hmemC y)
  · intro x hx
    exact hpos _ (hmemC x) (fun h0 => hx (hinj x h0))
  · intro h x y x' y' hx hy
    have ex : x' = ⟨rt D.host.E n h x, π.stable h x x.2⟩ := Subtype.ext hx
    have ey : y' = ⟨rt D.host.E n h y, π.stable h y y.2⟩ := Subtype.ext hy
    simp only
    rw [ex, ey, hΦe h x, hΦe h y]
    exact hinv h _ (hmemC x) _ (hmemC y)

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeckeRational

open Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Bridge Formalism.L2.Theta
open scoped TensorProduct

theorem repr_mem_of_basis_rational {K V ι κ : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [Fintype κ]
    (F : Subfield K) (b : Module.Basis ι K V) (b' : Module.Basis κ K V) (h : ∀ i j, b'.repr (b i) j ∈ F)
    (v : V) (hv : ∀ j, b'.repr v j ∈ F) (i : ι) : b.repr v i ∈ F := by
  obtain ⟨φ, h1, h2⟩ := FormsDescent.exists_retraction F
  have e2 : FormsDescent.coordMap F b' φ v = v := by
    apply b'.repr.injective
    ext j
    rw [FormsDescent.repr_coordMap, h2 _ (hv j)]
  have key : v = ∑ a, φ (b.repr v a) • b a := by
    rw [← FormsDescent.coordMap_sum F b' φ _ _ h, b.sum_repr, e2]
  have : b.repr v i = φ (b.repr v i) := by
    conv_lhs => rw [key]
    rw [b.repr_sum_self]
  rw [this]
  exact h1 _

theorem repr_map_mem {K V κ : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype κ]
    (F : Subfield K) (b : Module.Basis κ K V) (g : V →ₗ[K] V) (hg : ∀ i j, b.repr (g (b j)) i ∈ F)
    (v : V) (hv : ∀ j, b.repr v j ∈ F) (i : κ) : b.repr (g v) i ∈ F := by
  have h1 : g v = ∑ j, b.repr v j • g (b j) := by
    conv_lhs => rw [← b.sum_repr v]

    simp only [map_sum, map_smul]
  rw [h1]

  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact F.sum_mem fun j _ => F.mul_mem (hv j) (hg i j)

theorem levFn_isOfFinOrder {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : Formalism.L2.DIV.LevDat E ℂ n) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    IsOfFinOrder (levFn β L x) := by
  have hfin : ∀ PP : Pl E, Finite (kP PP) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  have hone : IsOfFinOrder (1 : ℂˣ) := IsOfFinOrder.one
  unfold levFn
  refine IsOfFinOrder.mul (IsOfFinOrder.mul ?_ ?_) ?_
  · unfold ext1
    split_ifs
    · exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
    · exact hone
  · refine Finset.prod_induction _ IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) hone fun PP _ => ?_
    refine Finset.prod_induction _ IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) hone fun c _ => ?_
    exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
  · refine Finset.prod_induction _ IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) hone fun PP _ => ?_
    exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)

variable {D : D7}

theorem levEnv_chi_pow (V : TH.HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J) : ∃ n : ℕ, 0 < n ∧ (levEnv V β L).χ k ^ n = 1 :=
  isOfFinOrder_iff_pow_eq_one.1 (levFn_isOfFinOrder β (Lev.flag1L L) _)

theorem embE_mem_cmMax (x : D.host.E) : D.embE x ∈ cmMax D.what₂.LL := by
  intro σ
  rw [← D.embE_conj]
  exact D.host.conjE_apply (σ.comp D.embE) x

theorem labLL_mem_cmMax (τ : D.what₂.Tau) (x : D.host.E) : labLL D τ x ∈ cmMax D.what₂.LL := embE_mem_cmMax _

theorem action_rational (V : TH.HSp D) (C : CoefDat D V) {S : CSD D.what₂.LL} {J : Subgroup (Gf V)} {χ : J →* ℂˣ}
    (P : ClassPres (ratF V) S D.what₂.embLL C.ρ J χ) {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair nab del}
    {rho : GL (Fin V.rank) D.host.E →* Module.End D.what₂.LL (VV D.what₂.LL lam)}
    (hP : CoefTie V C P lam c0 pair nab del) (hM : CoefMapTie V C c0 rho)
    (hrho : ∀ g i j, (bVV D.what₂.LL lam).repr (rho g (bVV D.what₂.LL lam j)) i ∈ cmMax D.what₂.LL) (γ : GQ V) (j : S.ιV) :
    ∃ c : S.ιV → D.what₂.LL, (∀ i, c i ∈ cmMax D.what₂.LL) ∧
      C.ρ γ (P.coef (S.bV j)) = ∑ i, D.what₂.embLL (c i) • P.coef (S.bV i) := by
  obtain ⟨e, hr, he, -⟩ := hP
  obtain ⟨γE, hγ⟩ : ∃ γE, IsRatMat V γ γE := by
    obtain ⟨g, hg⟩ := γ.2
    exact ⟨g, hg.2.symm⟩
  refine ⟨fun i => (S.bV.map e).repr (rho γE (e (S.bV j))) i, fun i => ?_, ?_⟩
  · exact repr_mem_of_basis_rational _ (S.bV.map e) (bVV D.what₂.LL lam) hr _
      (repr_map_mem _ _ _ (hrho γE) _ (hr j)) i
  · rw [he, ← hM.1 γ γE hγ]
    conv_lhs => rw [← (S.bV.map e).sum_repr (rho γE (e (S.bV j)))]

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [he, LinearMap.map_smulₛₗ, Module.Basis.map_apply]

theorem dcOp_matrix_mem_cmMax (V : TH.HSp D) (C : CoefDat D V) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {S : CSD D.what₂.LL}
    (P : ClassPres (ratF V) S D.what₂.embLL C.ρ (levEnv V β L).J (levEnv V β L).χ) {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair nab del}
    {rho : GL (Fin V.rank) D.host.E →* Module.End D.what₂.LL (VV D.what₂.LL lam)}
    (hP : CoefTie V C P lam c0 pair nab del) (hM : CoefMapTie V C c0 rho)
    (hrho : ∀ g i j, (bVV D.what₂.LL lam).repr (rho g (bVV D.what₂.LL lam j)) i ∈ cmMax D.what₂.LL)
    (B : Finset (Gf V)) (T : Module.End D.what₂.LL S.Forms)
    (hT : ∀ f : S.Forms, P.ext ((T f : S.Forms) : S.Cl → S.V) = dcOp B (P.ext (f : S.Cl → S.V))) :
    S.HasRatBasis ∧ ∀ a b, LinearMap.toMatrix S.basis S.basis T a b ∈ cmMax D.what₂.LL :=
  GlobalTheory.classPres_dcOp_rat (ratF V) S D.what₂.embLL C.ρ _ _ P B T D.starLL_cx (levEnv_chi_pow V β L)
    (action_rational V C P hP hM hrho) hT

theorem toMatrix_one_mem {K M ι : Type} [Field K] [AddCommGroup M] [Module K M] [Fintype ι] [DecidableEq ι] (F : Subfield K)
    (b : Module.Basis ι K M) (i j : ι) : LinearMap.toMatrix b b (1 : Module.End K M) i j ∈ F := by
  rw [LinearMap.toMatrix_one, Matrix.one_apply]
  split_ifs
  · exact F.one_mem
  · exact F.zero_mem

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem rows_dcOp_mem_cmMax (R : RealDat D A Ks) (h : R.fam_tie) (t : T) (B : Finset (Gf D.sp.X'))
    (U : Module.End D.what₂.LL (A.MtildeCSD t).Forms)
    (hU : ∀ f : (A.MtildeCSD t).Forms, (R.B.R t).pres.ext (U f).1 = dcOp B ((R.B.R t).pres.ext f.1)) (a b) :
    LinearMap.toMatrix (A.MtildeCSD t).basis (A.MtildeCSD t).basis U a b ∈ cmMax D.what₂.LL := by
  obtain ⟨gramR, c0R, c0L, hT⟩ := h
  exact (dcOp_matrix_mem_cmMax D.sp.X' R.cX.coef R.βX (R.datXt t) (R.B.R t).pres (hT.coefR t) hT.mapR
    (fun g i j => (coefAction_repr_mem_subfield (labLL D) _ _ labLL_mem_cmMax g i j).1) B U hU).2 a b

theorem lifts_dcOp_mem_cmMax (R : RealDat D A Ks) (h : R.fam_tie) (j : Fin D.R.m) (t : T) (B : Finset (Gf (Vc D j)))
    (U : Module.End D.what₂.LL (A.MtCSD j t).Forms)
    (hU : ∀ f : (A.MtCSD j t).Forms, (R.B.L j t).pres.ext (U f).1 = dcOp B ((R.B.L j t).pres.ext f.1)) (a b) :
    LinearMap.toMatrix (A.MtCSD j t).basis (A.MtCSD j t).basis U a b ∈ cmMax D.what₂.LL := by
  obtain ⟨gramR, c0R, c0L, hT⟩ := h
  exact (dcOp_matrix_mem_cmMax (Vc D j) (R.cV j).coef (R.βV j) (R.datVt j t) (R.B.L j t).pres (hT.coefL j t) (hT.mapL j)
    (fun g i k => (coefAction_repr_mem_subfield (labLL D) _ _ labLL_mem_cmMax g i k).2) B U hU).2 a b

end GlobalTheory.HeckeRational

end
end

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField ReciprocityTheory.ChartRestriction.L1

namespace GlobalTheory.ArtinClassCM

theorem inertia_fixes (hW : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], ∃ art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E), IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) ∧ (∀ (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → art g = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v → IsArithFrobenius A v φ → art φ = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) (hC : ChebOmSt)
    {d : ℕ} {L : PeriodPair} (hsf : Squarefree d) (hd : d % 4 = 3) (hL : HasCMBy d L)
    (x : Om d) (hx : (x : ℂ) = jInv L) (B : ValuationSubring (Om d)) (σ : Om d ≃ₐ[KQ d] Om d) (hσ : InertiaEl B σ) :
    σ x = x := by
  obtain ⟨art, hop, hin, hfrob⟩ := hW (KQ d) (Om d)
  have hxi : IsIntegral ℤ x := by
    obtain ⟨y, hy, hyi⟩ := exists_Om d (cm1 d L hsf hd hL)
    have : y = x := Subtype.ext (hy.trans hx.symm)
    rwa [this] at hyi
  obtain ⟨P, hP, hPx⟩ := hxi
  have hxs : x ∈ fixJRoots (Ω := Om d) P := by
    rw [mem_fixJRoots hP]
    rwa [show algebraMap ℤ (Om d) = Int.castRingHom (Om d) from RingHom.ext_int _ _] at hPx
  obtain ⟨n, hn0, hn⟩ := sepInt (fixJRoots (Ω := Om d) P) (fun r hr => isIntegral_of_mem_fixJRoots hP hr)
  set S : Set (HeightOneSpectrum (𝓞 (KQ d))) := {v | (n : 𝓞 (KQ d)) ∈ v.asIdeal} with hS
  have hSfin : S.Finite := finite_places (KQ d) hn0

  have key : ∀ (A : ValuationSubring (Om d)) (v : HeightOneSpectrum (𝓞 (KQ d))), LiesAbove A v → v ∉ S →
      ∀ r ∈ fixJRoots (Ω := Om d) P, ∀ r' ∈ fixJRoots (Ω := Om d) P, r - r' ∈ A.nonunits → r = r' := by
    intro A v hA hv r hr r' hr' h
    by_contra hne
    have h1 := hn r hr r' hr' hne A h
    apply hv
    rw [hS, Set.mem_ofPred_eq, ← hA]
    simpa using h1
  set H : Subgroup (Om d ≃ₐ[KQ d] Om d) := art.ker ⊓ fixJStab (KQ d) (Om d) P with hH
  have := fixJStab_normal (E := KQ d) (Ω := Om d) hP
  have hHn : H.Normal := inferInstance
  have hHo : IsOpen (H : Set (Om d ≃ₐ[KQ d] Om d)) := by
    rw [hH, Subgroup.coe_inf]
    exact hop.inter fixJStab_isOpen
  obtain ⟨A, v, φ, hA, hv, hp, hφ, hσφ⟩ := hC (KQ d) (Om d) S hSfin H hHn hHo (by
    intro A v hA hv g hg
    refine ⟨hin A g hg, fun r hr => ?_⟩
    exact key A v hA hv _ (map_mem_fixJRoots hP g hr) _ hr
      (hg.2 r (mem_of_isIntegral A (isIntegral_of_mem_fixJRoots hP hr)))) σ
  have hσ1 : art σ = 1 := hin B σ hσ
  have hφ1 : art φ = 1 := by
    have : σ⁻¹ * φ ∈ art.ker := hσφ.1
    rw [MonoidHom.mem_ker, map_mul, map_inv, hσ1, inv_one, one_mul] at this
    exact this
  have hcl := hfrob v A φ hA hφ
  rw [hφ1] at hcl
  have h1 := frobCong hsf hd hL x hx A v hA hp hcl.symm
  have h2 := hφ.2 x (mem_of_isIntegral A (isIntegral_of_mem_fixJRoots hP hxs))
  have h3 : φ x - x ∈ A.nonunits := by
    have := fixJ_nonunits_add A h2 h1
    simpa using this
  have h4 : φ x = x := key A v hA hv _ (map_mem_fixJRoots hP φ hxs) _ hxs h3
  have h5 := hσφ.2 x hxs
  rw [AlgEquiv.mul_apply, h4] at h5
  calc σ x = σ (σ⁻¹ x) := by rw [h5]
    _ = x := by rw [← AlgEquiv.mul_apply, mul_inv_cancel]; rfl

theorem good_model (hW : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], ∃ art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E), IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) ∧ (∀ (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → art g = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v → IsArithFrobenius A v φ → art φ = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) (hC : ChebOmSt) : CM2 := by
  refine goodReduction_of_integral_unramified jInt ?_
  intro d L hsf hd hL l _ hl hld ι
  obtain ⟨x, hx, -⟩ := exists_Om d (cm1 d L hsf hd hL)
  rw [← hx]
  exact inertKur (by omega) hld ι x fun σ hσ => inertia_fixes hW hC hsf hd hL x hx _ σ hσ

end GlobalTheory.ArtinClassCM
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.NormValGen

theorem valuation_eq_pow_of_norm_eq {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) (y : (v.adicCompletion K)ˣ) (x : (w.adicCompletion L)ˣ)
    (h : ‖(y : v.adicCompletion K)‖ = ‖(x : w.adicCompletion L)‖) (f : ℕ) (hf : normV w = normV v ^ f) :
    Valued.v (y : v.adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have hf' : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f := by
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hf
  have hy : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
  have hx : Valued.v (x : w.adicCompletion L) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [FinitePlace.norm_def, FinitePlace.norm_def] at h
  rw [WithZeroMulInt.toNNReal_neg_apply _ hy, WithZeroMulInt.toNNReal_neg_apply _ hx, NNReal.coe_inj, hf',
    Nat.cast_pow, ← zpow_natCast, ← zpow_mul] at h
  have h1 := HeightOneSpectrum.one_lt_absNorm_nnreal v
  have h2 := zpow_right_injective₀ (zero_lt_one.trans h1) h1.ne' h
  rw [← WithZero.coe_unzero hy, ← WithZero.coe_unzero hx, ← WithZero.coe_pow]
  refine congrArg _ (Multiplicative.toAdd.injective ?_)
  rw [toAdd_pow, nsmul_eq_mul, WithZero.toAdd_unzero_eq_log,
    WithZero.toAdd_unzero_eq_log, h2]

theorem loc_eq_of_comp_norm {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (ψ : HChar K) (ψ' : HChar M) (hψ : ∀ x : Ideles M, ψ'.1 x = ψ.1 (GroundTheory.Global.ideleNorm K M x))
    (w : HeightOneSpectrum (𝓞 M)) (f : ℕ) (hf : normV w = normV (w.under (𝓞 K)) ^ f)
    (x : (w.adicCompletion M)ˣ) : ∃ y : ((w.under (𝓞 K)).adicCompletion K)ˣ,
      ψ'.loc w x = ψ.loc (w.under (𝓞 K)) y ∧
      Valued.v (y : (w.under (𝓞 K)).adicCompletion K) = Valued.v (x : w.adicCompletion M) ^ f := by
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w x
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  exact ⟨_, (hψ _).trans (congrArg ψ.1 h), valuation_eq_pow_of_norm_eq _ w _ x hm' f hf⟩

theorem unrAt_val_of_comp_norm : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (ψ : HChar K) (ψ' : HChar M), (∀ x : Ideles M, ψ'.1 x = ψ.1 (GroundTheory.Global.ideleNorm K M x)) → ∀ (w : HeightOneSpectrum (𝓞 M)) (f : ℕ), normV w = normV (w.under (𝓞 K)) ^ f → ψ.UnrAt (w.under (𝓞 K)) → ψ'.UnrAt w ∧ ψ'.val w = ψ.val (w.under (𝓞 K)) ^ f := by
  intro K M _ _ _ _ _ ψ ψ' hψ w f hf hu
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, hv⟩ := loc_eq_of_comp_norm ψ ψ' hψ w f hf x
    rw [hy]
    apply hu
    unfold IsUnitAt at *
    rw [hv, hx, one_pow]
  · obtain ⟨y, hy, hv⟩ := loc_eq_of_comp_norm ψ ψ' hψ w f hf (atFin w (unif w))
    have h1 := unif_spec w
    have h2 := unif_spec (w.under (𝓞 K))
    have hunit : IsUnitAt (w.under (𝓞 K)) (y * ((atFin _ (unif (w.under (𝓞 K)))) ^ f)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, hv, h1, h2]
      exact mul_inv_cancel₀ (pow_ne_zero _ WithZero.exp_ne_zero)
    have h3 := hu _ hunit
    rw [map_mul, map_inv, mul_inv_eq_one, map_pow] at h3
    exact hy.trans h3

end GlobalTheory.NormValGen

end
end
