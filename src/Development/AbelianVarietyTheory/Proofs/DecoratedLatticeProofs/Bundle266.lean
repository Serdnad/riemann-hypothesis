module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle239
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle252
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle253
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle259
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle242
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsKeepStandardLattice
public import Formalism.LocalToGlobal.Columns.RecLevelLoc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle241
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle243
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle006

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.seesaw_fubini_two_lifts_moderate_growth_kernels : ∀ (D : D7) (A B : HSp D) (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure → ∀ K₁ K₂ : GA D A → GA D B → ℂ, (∀ K ∈ ({K₁, K₂} : Set (GA D A → GA D B → ℂ)), Continuous (Function.uncurry K) ∧ (∀ γ ∈ GQ A, ∀ g h, K (γ * g) h = K g h) ∧ (∀ g, MemL2Quotient (GQ B) mH (K g)) ∧ (GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (K g) (K g)) ∧ ∀ h, GlobalTheory.Grow.ModGrowth A fun g => K g h) → ∀ u₁ u₂ : GA D A → ℂ, GlobalTheory.Grow.RapidDec A u₁ → GlobalTheory.Grow.RapidDec A u₂ → let θ₁ : GA D B → ℂ := fun h => ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ A) (fun g => K₁ g h * u₁ g) q ∂autMeasure A m; let θ₂ : GA D B → ℂ := fun h => ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ A) (fun g => K₂ g h * u₂ g) q ∂autMeasure A m; (∀ h, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) fun g => K₁ g h * u₁ g) (autMeasure A m)) ∧ (∀ h, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) fun g => K₂ g h * u₂ g) (autMeasure A m)) ∧ MemL2Quotient (GQ B) mH θ₁ ∧ MemL2Quotient (GQ B) mH θ₂ ∧ petersson B mH θ₁ θ₂ = ∫ q : AutQ A × AutQ A, petersson B mH (K₁ q.1.out) (K₂ q.2.out) * u₁ q.1.out * conj (u₂ q.2.out) ∂(autMeasure A m).prod (autMeasure A m) := by
  first | exact @GlobalTheory.Core.Rk.Seesaw.seesaw_fubini | exact GlobalTheory.Core.Rk.Seesaw.seesaw_fubini | (intros; apply GlobalTheory.Core.Rk.Seesaw.seesaw_fubini <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix

noncomputable section

namespace GlobalTheory.Core.Rk.Dich

theorem offOpen : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ¬ (∃ δ ∈ GQ V, γ * (io V (δ, 1))⁻¹ ∈ siegel V) → ∃ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C ∧ (∀ n ∈ NI V C, ∃ p : siegel V, γ * io V (n, 1) = p * γ ∧ aP V p = 1) ∧ ∀ δ ∈ GQ V, γ * io V (δ, 1) * γ⁻¹ ∈ siegel V → ∀ n ∈ NI V C, δ * n * δ⁻¹ ∈ NI V C := by
  intro D V γ hγ hopen
  obtain ⟨g, hg, -, hγi⟩ := exists_rat (dblSp V) hγ
  have hgi : g⁻¹ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (dblSp V).gram := inv_mem hg
  set γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E := (g⁻¹).1 with hγidef
  have hU : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γi * dblGram finSumFinEquiv V.gram * γi =
      dblGram finSumFinEquiv V.gram := by
    have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γi * (dblSp V).gram * γi = (dblSp V).gram := hgi
    rwa [gram_hdbl] at h
  set Qd := diagSnd γi with hQd
  set P := leviMat finSumFinEquiv γi with hP
  have hinj : ∀ x, P *ᵥ x = 0 → Qd *ᵥ x = 0 → x = 0 := by
    intro x h1 h2
    have h3 : γi *ᵥ pairVec finSumFinEquiv x x = 0 := by
      rw [mulVec_pairVec_diag, ← hP, ← hQd, h1, h2]
      funext j; simp [pairVec, Sum.elim_zero_zero]
    have h4 : (g.1 * γi) *ᵥ pairVec finSumFinEquiv x x = 0 := by rw [← mulVec_mulVec, h3, mulVec_zero]
    rw [hγidef, Units.mul_inv, one_mulVec] at h4
    funext i
    have := congrFun h4 (finSumFinEquiv (.inl i))
    rwa [pairVec_inl] at this
  by_cases hk : ∀ x, Qd *ᵥ x = 0 → x = 0
  · exact absurd (GlobalTheory.T.doubled_lagrangian_transverse_in_open_orbit D V γ hγ γi hγi hk) hopen
  push Not at hk
  obtain ⟨x0, hx0, hx0ne⟩ := hk
  let W := LinearMap.ker Qd.mulVecLin
  let b := Module.finBasis D.host.E W
  let K : Matrix (Fin V.rank) (Fin (Module.finrank D.host.E W)) D.host.E :=
    Matrix.of fun i j => (b j : Fin V.rank → D.host.E) i
  have hKv : ∀ y, K *ᵥ y = ((∑ j, y j • b j : W) : Fin V.rank → D.host.E) := by
    intro y; funext i
    simp [K, Matrix.mulVec, dotProduct, Submodule.coe_sum, Finset.sum_apply, mul_comm]
  have hbQ : ∀ j, Qd *ᵥ (b j : Fin V.rank → D.host.E) = 0 := fun j => (b j).2
  have hQK : Qd * K = 0 := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (hbQ j) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, K, Matrix.of_apply, Matrix.zero_apply]
    exact this
  have hspan : ∀ x, Qd *ᵥ x = 0 → ∃ y, x = K *ᵥ y := by
    intro x hx
    refine ⟨b.repr ⟨x, hx⟩, ?_⟩
    rw [hKv, b.sum_repr]
  have hiso : IsIsoFrame V (P * K) := by
    refine ⟨?_, ?_, ?_⟩
    · exact Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x0, hx0⟩, fun h => hx0ne (congrArg Subtype.val h)⟩
    · refine (Matrix.mulVec_injective_iff (M := P * K)).1 ?_
      intro c c' hc
      rw [← sub_eq_zero] at hc ⊢
      rw [← mulVec_sub, ← mulVec_mulVec] at hc
      have h1 : K *ᵥ (c - c') = 0 := hinj _ hc (by rw [mulVec_mulVec, hQK, zero_mulVec])
      rw [hKv] at h1
      have h2 : (∑ j, (c - c') j • b j : W) = 0 := Subtype.ext h1
      funext j
      exact Fintype.linearIndependent_iff.1 b.linearIndependent _ h2 j
    · have hI := isotropic_diag hU
      rw [← hP, ← hQd] at hI
      rw [Formalism.UG.cT_mul]
      calc Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) K * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) P *
            V.gram * (P * K)
          = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) K *
            (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) P * V.gram * P) * K := by
            simp only [Matrix.mul_assoc]
        _ = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (Qd * K) * V.gram * (Qd * K) := by
            rw [hI, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hQK]; simp [Formalism.UG.cT]
  refine ⟨_, P * K, hiso, GlobalTheory.T.conj_doubling_isotropic_unipotent_mem_siegel D V γ hγ γi hγi _ K hQK hiso, ?_⟩
  intro δ hδ hs n hn
  obtain ⟨d, -, hδm, -⟩ := exists_rat V hδ
  obtain ⟨G, hG, hGe⟩ := GlobalTheory.T.rational_isometry_keeps_isotropic_frame_of_siegel D V γ hγ γi hγi _ K hQK hspan hiso δ hδ d.1 hδm hs
  exact GlobalTheory.T.rational_isometry_normalises_isotropic_unipotent_radical D V _ (P * K) δ hδ d.1 hδm G hG hGe n hn

end GlobalTheory.Core.Rk.Dich

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.chartCharacter_trivial_on_standardPairStabilizer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ b, ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), g • Q j i = Q j i → ∀ h : (β j i).gl g ∈ A.U j b, A.chi j b ⟨_, h⟩ = 1 := by
  first | exact @GlobalTheory.AdForm.chi_std_trivial | exact GlobalTheory.AdForm.chi_std_trivial | (intros; apply GlobalTheory.AdForm.chi_std_trivial <;> assumption)
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.SBMove


open _root_.Formalism.L2.Col in
theorem isFrame_one_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (n : ℕ) : Formalism.L2.DIV.IsFrame (F := F) 1 (Formalism.L2.Col.stdLat E n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro x
    simp only [inv_one, Units.val_one, Matrix.one_mulVec, IsEmpty.forall_iff, iff_true]
    rw [Subsingleton.elim x 0]; exact zero_mem _
  · haveI : NeZero n := ⟨hn.ne'⟩
    have e : Formalism.L2.Col.stdLat E n = baseLb E n ∅ := by
      ext x
      rw [rll_mem_baseLb]
      constructor
      · intro h
        have h' : ∀ j, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x j := fun j =>
          (Submodule.mem_one).1 ((Submodule.mem_pi).1 h j (Set.mem_univ _))
        choose r hr using h'
        exact ⟨r, hr, fun P hP => absurd hP (Finset.notMem_empty _)⟩
      · rintro ⟨r, hr, -⟩
        exact (Submodule.mem_pi).2 fun j _ => (Submodule.mem_one).2 ⟨r j, hr j⟩
    intro x
    rw [e, rll_mem_hat_base, inv_one, Units.val_one, Matrix.one_mulVec]
    constructor
    · rintro ⟨y, hy, -⟩ i
      exact hy i ▸ (y i).2
    · exact fun h => ⟨fun i => ⟨x i, h i⟩, fun _ => rfl, fun P hP => absurd hP (Finset.notMem_empty _)⟩

theorem mulVec_mem_sub {A : Type} [CommRing A] {n : ℕ} (R : Subring A) (M : Matrix (Fin n) (Fin n) A)
    (hM : ∀ a b, M a b ∈ R) (v : Fin n → A) (hv : ∀ i, v i ∈ R) (i : Fin n) : (M *ᵥ v) i ∈ R := by
  simp only [Matrix.mulVec, dotProduct]
  exact R.sum_mem fun j _ => R.mul_mem (hM i j) (hv j)

theorem isFrame_of_int {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {L : Submodule (𝓞 E) (Fin n → E)} (hL : Formalism.L2.DIV.IsFrame (F := F) 1 L)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (h1 : ∀ a b, (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) a b ∈ Formalism.L2.Herm.intAf F E)
    (h2 : ∀ a b, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) a b ∈
      Formalism.L2.Herm.intAf F E) : Formalism.L2.DIV.IsFrame β L := by
  intro x
  rw [hL x, inv_one, Units.val_one, Matrix.one_mulVec]
  constructor
  · intro hx i; exact mulVec_mem_sub _ _ h2 x hx i
  · intro hx i
    have e : x = (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
        (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e]; exact mulVec_mem_sub _ _ h1 _ hx i

theorem int_of_moves {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V)
    (h : Moves V hn g (Formalism.L2.Col.stdLat D.host.E n)) (a b : Fin V.rank) :
    toEAf D (Formalism.L2.Theta.mt V g⁻¹ a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have hmem : (Pi.single (Fin.cast hn b) 1 : Fin n → D.host.E) ∈ Formalism.L2.Col.stdLat D.host.E n := by
    refine (Submodule.mem_pi).2 fun j _ => ?_
    by_cases hj : j = Fin.cast hn b
    · subst hj; simp only [Pi.single_eq_same]; exact Submodule.one_le.1 le_rfl
    · rw [Pi.single_eq_of_ne hj]; exact zero_mem _
  have h' := (h _).1 hmem (Fin.cast hn a)
  have e : (fun j => eToEAf D ((Pi.single (Fin.cast hn b) 1 : Fin n → D.host.E) j)) =
      Pi.single (Fin.cast hn b) 1 := by
    funext j
    by_cases hj : j = Fin.cast hn b
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  rw [e, Matrix.mulVec_single_one] at h'
  simpa [finM, Matrix.reindex_apply] using h'

end GlobalTheory.SBMove

namespace GlobalTheory.SBMove

theorem mt_mul_inv_eq {D : D7} (V : HSp D) (g : GA D V) :
    Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  simp only [Formalism.L2.Theta.mt]
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem actO_actO_inv {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  simp only [actO, inv_inv]
  simp only [← Matrix.mul_assoc]
  rw [mt_mul_inv_eq, Matrix.one_mul, Matrix.mul_assoc, mt_mul_inv_eq, Matrix.mul_one]

theorem actO_add' {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  simp only [actO, Matrix.mul_add, Matrix.add_mul]

theorem actO_zero' {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) :
    actO S T g h 0 = 0 := by
  simp only [actO, Matrix.mul_zero, Matrix.zero_mul]

theorem actO_nsmul {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (y : WO S T) (k : ℕ) :
    actO S T g h (k • y) = k • actO S T g h y := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, actO_zero']
  | succ k ih => rw [succ_nsmul, succ_nsmul, actO_add', ih]

theorem actO_add_nsmul {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) (k : ℕ) :
    actO S T g h (x + k • y) = actO S T g h x + k • actO S T g h y := by
  rw [actO_add', actO_nsmul]

theorem actO_isHalf {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (e : AE D) {x : WO S T} (hx : IsHalf e x) :
    IsHalf e (actO S T g h x) := by
  have hx' : x = e • x := by
    ext a b; exact (hx a b).symm
  have key : actO S T g h x = e • actO S T g h x := by
    conv_lhs => rw [hx']
    simp only [actO, Matrix.mul_smul, Matrix.smul_mul]
  intro i j
  have := congrFun (congrFun key i) j
  rw [Matrix.smul_apply, smul_eq_mul] at this
  exact this.symm

theorem coe_stdLat {D : D7} (n : ℕ) :
    ((Formalism.L2.Col.stdLat D.host.E n : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = intVec D n := by
  ext x
  simp only [SetLike.mem_coe, intVec, Set.mem_setOf_eq]
  rw [Formalism.L2.Col.stdLat, Submodule.mem_pi]
  refine forall_congr' fun k => ?_
  simp only [Set.mem_univ, true_implies, Submodule.mem_one]
  constructor
  · rintro ⟨y, hy⟩; rw [← hy]; exact y.isIntegral_coe
  · intro hk; exact ⟨⟨x k, hk⟩, rfl⟩

theorem actO_mem_stdHom {D : D7} (S T : HSp D) {n m : ℕ} (hn : S.rank = n) (hm : T.rank = m) (g : GA D S) (h : GA D T)
    (hg : Moves S hn g (Formalism.L2.Col.stdLat D.host.E n)) (hg' : Moves S hn g⁻¹ (Formalism.L2.Col.stdLat D.host.E n))
    (hh : Moves T hm h (Formalism.L2.Col.stdLat D.host.E m)) (hh' : Moves T hm h⁻¹ (Formalism.L2.Col.stdLat D.host.E m))
    {x : WO S T} (hx : x ∈ stdHom S T) : actO S T g h x ∈ stdHom S T := by
  have e : stdHom S T = latO S T ((Formalism.L2.Col.stdLat D.host.E S.rank : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) : Set (Fin S.rank → D.host.E))
      ((Formalism.L2.Col.stdLat D.host.E T.rank : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : Set (Fin T.rank → D.host.E)) fun _ => True := by
    rw [coe_stdLat, coe_stdLat]
  rw [e] at hx ⊢
  have fr : ∀ (V : HSp D) {k : ℕ} (hk : V.rank = k) (b : GA D V), Moves V hk b (Formalism.L2.Col.stdLat D.host.E k) →
      Moves V hk b⁻¹ (Formalism.L2.Col.stdLat D.host.E k) →
      Formalism.L2.DIV.IsFrame (Matrix.GeneralLinearGroup.map (toEAf D) (matHom V b)) (Formalism.L2.Col.stdLat D.host.E V.rank) := by
    intro V k hk b hb hb'
    refine isFrame_of_int (isFrame_one_std _) _ (fun a c => ?_) (fun a c => ?_)
    · have := int_of_moves V hk b⁻¹ hb' a c
      rw [inv_inv] at this
      exact this
    · rw [← map_inv, ← map_inv]
      exact int_of_moves V hk b hb a c
  exact GlobalTheory.AdelicLatMove.actO_mem_latO S T g h _ _ _ _ 1 (Matrix.GeneralLinearGroup.map (toEAf D) (matHom S g)) 1
    (Matrix.GeneralLinearGroup.map (toEAf D) (matHom T h)) (isFrame_one_std _) (fr S hn g hg hg') (isFrame_one_std _)
    (fr T hm h hh hh') (by rw [Units.val_one, Matrix.mul_one]; rfl) (by rw [Units.val_one, Matrix.mul_one]; rfl) x hx

end GlobalTheory.SBMove


open GlobalTheory.SBMove in
theorem GlobalTheory.SBMove.isSBHalf_actO_lev : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ), IsSBHalf A.e (stdHom _ _) (fun z => Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z)) := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ Φ hΦ κ κ'
  have hi0 : i ≤ B.R.m := Nat.le_of_succ_le hi
  have hU : ∀ j (hj : j ≤ B.R.m) (β : Ch j) g, g ∈ A.U j β →
      Moves _ (rankN (I.rec7 l Z) j hj) g (Formalism.L2.Col.stdLat B.fields.E _) :=
    fun j hj β g hg => GlobalTheory.AdForm.levels_keep_stdLat I hI hP l Z u a Ch A hA j hj β g hg
  have hG : ∀ x ∈ stdHom _ _, actO _ _ κ.1⁻¹ κ'.1⁻¹ x ∈ stdHom _ _ := fun x hx =>
    actO_mem_stdHom _ _ _ _ _ _ (hU i hi0 α _ (inv_mem κ.2)) (hU i hi0 α _ (by rw [inv_inv]; exact κ.2))
      (hU (i + 1) hi γ _ (inv_mem κ'.2)) (hU (i + 1) hi γ _ (by rw [inv_inv]; exact κ'.2)) hx
  have hH : ∀ x ∈ stdHom _ _, actO _ _ κ.1 κ'.1 x ∈ stdHom _ _ := fun x hx =>
    actO_mem_stdHom _ _ _ _ _ _ (hU i hi0 α _ κ.2) (hU i hi0 α _ (inv_mem κ.2))
      (hU (i + 1) hi γ _ κ'.2) (hU (i + 1) hi γ _ (inv_mem κ'.2)) hx
  obtain ⟨hsupp, k, hk, hinv, hden⟩ := hΦ
  refine ⟨fun t ht => ?_, k, hk, fun v hv hve t => ?_, fun t ht => ?_⟩
  · rw [← actO_actO_inv κ.1 κ'.1 t]
    exact actO_isHalf _ _ _ (hsupp _ ht)
  · show Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ (t + k • v)) = Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ t)
    rw [actO_add_nsmul]
    exact hinv _ (hG v hv) (actO_isHalf _ _ _ hve) _
  · have h1 := hden _ ht
    rw [← actO_nsmul] at h1
    rw [← actO_actO_inv κ.1 κ'.1 (k • t)]
    exact hH _ h1
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.chartLevel_exists_adelicLevel_trivialReal_lift : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) (z : (A.K i hi β).lev.U), ∃ w : A.U i β, z.1.1 = finM _ (rankN (I.rec7 l Z) i hi) w.1 := by
  first | exact @GlobalTheory.AdForm.LevLift.exists_mem_U_finM | exact GlobalTheory.AdForm.LevLift.exists_mem_U_finM | (intros; apply GlobalTheory.AdForm.LevLift.exists_mem_U_finM <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.trueChainKernel_eq_classSum_jets : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) (hab : B.R.N i ≤ B.R.N (i + 1)) (φ : ColT I l u a i) (Fc : (I.chain l u a).cls i → PY (I.rec7 l Z).what₂.Tau (B.R.N i)), (∀ c y, φ c y = evalAt y.1 (Fc c) * ∏ τ, (y.1 τ).det ^ (-(I.chain l u a).sSharp i τ)) → ∀ c' y', (I.chain l u a).K i φ c' y' = ∑ᶠ c, ((Nat.card ((I.chain l u a).stab i c) : ℕ) : ℂ)⁻¹ * A.abelian₂ i c c' (subY hab y'.1 (Fc c)) * ∏ τ, (y'.1 τ).det ^ (-(I.chain l u a).sDiv i τ) := by
  first | exact @GlobalTheory.AdForm.KerVal.kernel_classSum | exact GlobalTheory.AdForm.KerVal.kernel_classSum | (intros; apply GlobalTheory.AdForm.KerVal.kernel_classSum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.centralEigen_realDatum_finite_sum_fockProducts : ∀ (D : D7), CenFock D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → ∀ (χ : GA D A → ℂ) (χ' : GA D S → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k.om (a, 1) (fun u => C u v) = χ a • fun u => C u v) → (∀ b ∈ GinfC S, b ∈ Subgroup.center (GA D S) → ∀ u, k'.om (b, 1) (C u) = χ' b • C u) → ∃ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank), ∀ u v, C u v = ∑ i, pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i) u * pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i) v := by
  first | exact @GlobalTheory.SeeSaw.FinRank.biVac_sum_fock | exact GlobalTheory.SeeSaw.FinRank.biVac_sum_fock | (intros; apply GlobalTheory.SeeSaw.FinRank.biVac_sum_fock <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.doubleLift_fockSum_eq_sum_iteratedLifts : ∀ (D : D7), BiAct D → CenFock D → LiftSum D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → ∀ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank) (C : WO A S → WO S A' → ℂ), (∀ u v, C u v = ∑ i, pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i) u * pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i) v) → ∀ φ, IsContAut A φ → biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) = ∑ i, k'.lift ψ θ y z (P' i) (k.lift ψ θ x y (P i) φ) := by
  first | exact @GlobalTheory.SeeSaw.biLift_biComb_fockSum | exact GlobalTheory.SeeSaw.biLift_biComb_fockSum | (intros; apply GlobalTheory.SeeSaw.biLift_biComb_fockSum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.exists_charExponent_infinity_kernel_shift : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), ∃ e : (I.rec7 l Z).what₂.Tau → ℤ, (∀ τ, HasInfExp (I.rec7 l Z) (A.chr (i + 1)) τ (e τ)) ∧ ∀ τ, (I.chain l u a).sSharp i τ = -e τ - ((I.rec7 l Z).sp.X (i + 1)).rank / 2 ∧ -(I.chain l u a).sDiv i τ = e τ + ((I.rec7 l Z).sp.X i).rank / 2 ∧ 0 ≤ shiftOf (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u i) τ + (I.chain l u a).sSharp i τ := by
  first | exact @GlobalTheory.AdForm.TwDat.chr_exp_shifts | exact GlobalTheory.AdForm.TwDat.chr_exp_shifts | (intros; apply GlobalTheory.AdForm.TwDat.chr_exp_shifts <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.chartLevel_column_sub_one_mem_baseLattice : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ j (hj : j ≤ B.R.m) b, ∀ κ ∈ A.U j b, ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → ∀ s : Fin ((I.rec7 l Z).R.N j), (fun r => Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (GlobalTheory.AdForm.finM _ (rankN (I.rec7 l Z) j hj) κ r s) - (1 : Matrix (Fin ((I.rec7 l Z).R.N j)) (Fin ((I.rec7 l Z).R.N j)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) r s) ∈ Formalism.UG.latS (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (intV (I.rec7 l Z).host.E v) (A.K j hj b).lev.Lb := by
  first | exact @GlobalTheory.AdForm.level_col_sub_one_mem | exact GlobalTheory.AdForm.level_col_sub_one_mem | (intros; apply GlobalTheory.AdForm.level_col_sub_one_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

theorem _root_.GlobalTheory.T.baseChartDecoration_levelPrimeFunctional_eq_conj_mul : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ i, i ≤ B.R.m → ∀ (β : Ch i) (P : (B.primes X).vT u)
    (x : Formalism.L2.Col.Sp B.fields.E (B.R.N i)), x ∈ Formalism.L2.Col.stdLat B.fields.E (B.R.N i) → ∀ r : Fin (B.R.N i), r.1 + 1 = B.R.N i →
    ∀ c : 𝓞 B.fields.E, algebraMap (𝓞 B.fields.E) B.fields.E c = x r →
      (A.p0 i β).1.1.deco.1.f P x = Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u) * c) := by
  first | exact @GlobalTheory.PhiOneVal.base_deco_fn | exact GlobalTheory.PhiOneVal.base_deco_fn | (intros; apply GlobalTheory.PhiOneVal.base_deco_fn <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.chartLevels_keep_standardLattice : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) β, ∀ k ∈ A.U i β, Moves _ (rankN (I.rec7 l Z) i hi) k (Formalism.L2.Col.stdLat B.fields.E _) := by
  first | exact @GlobalTheory.AdForm.levels_keep_stdLat | exact GlobalTheory.AdForm.levels_keep_stdLat | (intros; apply GlobalTheory.AdForm.levels_keep_stdLat <;> assumption)
end
