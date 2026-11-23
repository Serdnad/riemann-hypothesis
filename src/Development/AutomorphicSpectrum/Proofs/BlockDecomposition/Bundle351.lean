module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle348
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle328
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle326
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle329
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle173
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle191
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle340
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle145
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle297
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle330
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle098
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle111
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle312
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle331
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle333
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle125
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle316
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenCoreMain

theorem le_of_not_le_sup {V : Type} [AddCommGroup V] [Module ℂ V] (T A B : Submodule ℂ V)
    (hT : Module.rank ℂ (V ⧸ T) ≤ 1) (hA : ¬ A ≤ B ⊔ T) : B ≤ T := by
  intro b hb
  by_contra hbT
  obtain ⟨a, haA, haBT⟩ := SetLike.not_le_iff_exists.mp hA
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.mp hT
  obtain ⟨r, hr⟩ := hv₀ (Submodule.Quotient.mk b)
  obtain ⟨s, hs⟩ := hv₀ (Submodule.Quotient.mk a)
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hbT
    rw [zero_smul] at hr
    exact (Submodule.Quotient.mk_eq_zero T).mp hr.symm
  have hmk : Submodule.Quotient.mk (p := T) (a - (s * r⁻¹) • b) = 0 := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, ← hr, ← hs, smul_smul,
      mul_assoc, inv_mul_cancel₀ hr0, mul_one, sub_self]
  have ht : a - (s * r⁻¹) • b ∈ T := (Submodule.Quotient.mk_eq_zero T).mp hmk
  apply haBT
  have : a = (s * r⁻¹) • b + (a - (s * r⁻¹) • b) := by abel
  rw [this]
  exact Submodule.add_mem_sup (B.smul_mem _ hb) ht

theorem nonempty_equiv_of_generic {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (T : Submodule ℂ V) (hT : Module.rank ℂ (V ⧸ T) ≤ 1)
    (hsup : ∀ X Y : Subrepresentation ρ,
      (X ⊔ Y).toSubmodule ⊓ T ≤ X.toSubmodule ⊓ T ⊔ Y.toSubmodule ⊓ T)
    (A B C D : Subrepresentation ρ) (hBA : B ≤ A) (hDC : D ≤ C)
    (hAB : (subQuot A B).IsIrreducible) (hCD : (subQuot C D).IsIrreducible)
    (hA : ¬ A.toSubmodule ≤ B.toSubmodule ⊔ T) (hC : ¬ C.toSubmodule ≤ D.toSubmodule ⊔ T) :
    Nonempty ((subQuot A B).Equiv (subQuot C D)) := by
  have hBT : B.toSubmodule ≤ T := le_of_not_le_sup T _ _ hT hA
  have hDT : D.toSubmodule ≤ T := le_of_not_le_sup T _ _ hT hC
  have hAT : ¬ A.toSubmodule ≤ T := fun h => hA (h.trans le_sup_right)
  have hCT : ¬ C.toSubmodule ≤ T := fun h => hC (h.trans le_sup_right)
  have hET : ¬ (A ⊓ C).toSubmodule ≤ T := GlobalTheory.T.inf_not_in_codim_one_submodule ρ T hT A C (hsup A C) hAT hCT
  have hEA : A ⊓ C ≤ A := inf_le_left
  have hEC : A ⊓ C ≤ C := inf_le_right
  have hEB : ¬ A ⊓ C ≤ B := fun h => hET (le_trans h hBT)
  have hED : ¬ A ⊓ C ≤ D := fun h => hET (le_trans h hDT)
  have hfillB := GlobalTheory.T.sup_eq_of_irreducible_subquotient ρ A B (A ⊓ C) hBA hAB hEA hEB
  have hfillD := GlobalTheory.T.sup_eq_of_irreducible_subquotient ρ C D (A ⊓ C) hDC hCD hEC hED
  obtain ⟨e₁⟩ := GlobalTheory.T.subquotient_equiv_of_sup_eq ρ A B (A ⊓ C) hEA hfillB
  obtain ⟨e₂⟩ := GlobalTheory.T.subquotient_equiv_of_sup_eq ρ C D (A ⊓ C) hEC hfillD
  have hiB : (subQuot (A ⊓ C) B).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e₁.symm hAB
  have hiD : (subQuot (A ⊓ C) D).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e₂.symm hCD
  have hnot : ¬ A ⊓ C ≤ (A ⊓ C) ⊓ B ⊔ (A ⊓ C) ⊓ D := by
    intro h
    apply hET
    have h3 : ((A ⊓ C) ⊓ B ⊔ (A ⊓ C) ⊓ D).toSubmodule ≤ T := by
      rw [Subrepresentation.toSubmodule_sup, Subrepresentation.toSubmodule_inf,
        Subrepresentation.toSubmodule_inf]
      exact sup_le (inf_le_right.trans hBT) (inf_le_right.trans hDT)
    exact (fun v hv => h3 (h hv) : (A ⊓ C).toSubmodule ≤ T)
  obtain ⟨e₃⟩ := GlobalTheory.T.irreducible_subquotients_equiv_of_not_le ρ (A ⊓ C) B D hiB hiD hnot
  exact ⟨(e₁.symm.trans e₃).trans e₂⟩

end GlobalTheory.CompanionTheory.GenCoreMain
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

theorem _root_.GlobalTheory.T.equiv_of_multiplicity_one_unique_factor : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (T : Representation ℂ G W) (J : Representation ℂ G V), T.IsIrreducible → HasFiniteLength J → jhMult T J = 1 → (∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X), ρ.IsIrreducible → IsSubquotient ρ J → Nonempty (ρ.Equiv T)) → Nonempty (J.Equiv T) := by
  first | exact @GlobalTheory.CompanionTheory.FineStep.nonempty_equiv_of_jhMult_eq_one | exact GlobalTheory.CompanionTheory.FineStep.nonempty_equiv_of_jhMult_eq_one | (intros; apply GlobalTheory.CompanionTheory.FineStep.nonempty_equiv_of_jhMult_eq_one <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.standard_blocks_reindex_strictMono : ∀ {r r' N : ℕ} (d : Fin r → ℕ) (hd : ∑ a, d a = N) (o : Fin r' → Fin r), StrictMono o → (∀ j, d j ≠ 0 → j ∈ Set.range o) → ∀ (hd' : ∑ a, d (o a) = N) (a : Fin r') (t : Fin (d (o a))), stdBlocks (fun a => d (o a)) hd' ⟨a, t⟩ = stdBlocks d hd ⟨o a, t⟩ := by
  first | exact @GlobalTheory.CompanionTheory.StdCompat.stdBlocks_drop_empty | exact GlobalTheory.CompanionTheory.StdCompat.stdBlocks_drop_empty | (intros; apply GlobalTheory.CompanionTheory.StdCompat.stdBlocks_drop_empty <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.tensor_product_drop_zero_factors : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' : ℕ} (y : Fin r → IrrGL (k := k)) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → Nonempty ((piTensor fun j => (y j).rep).Equiv ((piTensor fun a => (y (o a)).rep).comp (GlobalTheory.CompanionTheory.FineProd.dropHom (k := k) (fun j => (y j).1) o) : Representation ℂ (Levi k fun j => Fin (y j).1) _)) := by
  first | exact @GlobalTheory.CompanionTheory.FineProd.TensorLine.piTensor_drop_equiv | exact GlobalTheory.CompanionTheory.FineProd.TensorLine.piTensor_drop_equiv | (intros; apply GlobalTheory.CompanionTheory.FineProd.TensorLine.piTensor_drop_equiv <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi
open MeasureTheory

theorem _root_.GlobalTheory.T.restriction_ball_indicator_span : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) (X E : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup E] [Module ℂ E] (r : X →ₗ[ℂ] (Fin (N + 1) → k) → E), (∀ f, ∃ s : kˣ, ∀ (v a : Fin (N + 1) → k), Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s → r f (v + a) = r f v) → (∀ f, ∃ S : kˣ, ∀ v : Fin (N + 1) → k, r f v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) S) → ∀ (tr : (Fin (N + 1) → k) → X → X), (∀ a f v, r (tr a f) v = r f (v + a)) → ∀ (lev : GL (Fin (N + 1)) k → X → X) (A : GL (Fin (N + 1)) k → E →ₗ[ℂ] E), (∀ m f v, r (lev m f) v = A m (r f (((m⁻¹ : GL (Fin (N + 1)) k) : Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec v))) → ∃ T : X →ₗ[ℂ] E, (∀ a f, T (tr a f) = ((ψ (a (Fin.last N)) : Circle) : ℂ) • T f) ∧ (∀ m : GL (Fin (N + 1)) k, m ∈ Mir k N → ∀ f, T (lev m f) = ((nabs k (Matrix.GeneralLinearGroup.det m) : ℝ) : ℂ) • A m (T f)) ∧ (∀ s : kˣ, (∀ a : Fin (N + 1) → k, Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s → ψ (a (Fin.last N)) = 1) → ∃ c : ℂ, c ≠ 0 ∧ ∀ (b : X) (e : E), (∀ v, r b v = @ite _ (Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) s) (Classical.propDecidable _) e 0) → T b = c • e) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaInt.exists_twisted_integral | exact GlobalTheory.CompanionTheory.ThetaInt.exists_twisted_integral | (intros; apply GlobalTheory.CompanionTheory.ThetaInt.exists_twisted_integral <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeLocal

theorem loc_coef : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (t : Fin d → Γ(X, W)) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s t E ε → ∀ (σ : ∀ T, E.D ⟶ T) (m : ℕ) (r : ℤ), r = m → m + 1 ≤ s →
    (∀ c : HQ (KS q s {W}) r (r + 1) m, ∃ y : Idx m d → Γ(X, W),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (ε (y I)) u) c) ∧
    ∀ y : Idx m d → Γ(X, W),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (ε (y I)) u) 0 → y = 0 := by
  intro K _ _ X q W d t s E ε hL σ m r hr hs
  obtain ⟨hc, h1, -⟩ := hL
  obtain ⟨PQ, hPQ⟩ := GlobalTheory.T.polynomial_transfer (dividedPowersBot K) q (Ideal.Quotient.mk ⊥) 1 s {W}
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {W})
  have key := GlobalTheory.T.local_graded_vanishing PQ hF E σ hc r (fun r' hr' => (hPQ r' (by omega)).1) m
  obtain ⟨ha, hb⟩ := key.2 0 (by simpa using hr)
  refine ⟨fun c => ?_, fun y hy => ?_⟩
  · obtain ⟨x, -, hx⟩ := ha c
    refine ⟨fun I => ε.symm (x I), ?_⟩
    simpa only [RingEquiv.apply_symm_apply] using hx
  · have h0 : ∀ I, ε (y I) ∈ (sFil (KS q s {W}) ((0 : ℕ) : ℤ)).S E.D := fun I => by
      have e : (sFil (KS q s {W}) ((0 : ℕ) : ℤ)).S E.D = ⊤ := E.D.obj.pdPow_zero
      rw [e]
      trivial
    have := hb (fun I => ε (y I)) h0 hy
    funext I
    have h2 := h1 _ (this I)
    simpa using h2

end GlobalTheory.CompanionTheory.ConeLocal
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.smooth_integral_linear_change : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] {Z : Type} [AddCommGroup Z] [Module ℂ Z] (w : GL (Fin t) k) (φ : (Fin t → k) → Z), IsLocallyConstant φ → HasCompactSupport φ → smInt μ (fun v => φ (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v)) = ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • smInt μ φ := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.SmIntHaar.smInt_comp_inv_mulVec | exact GlobalTheory.CompanionTheory.Rodier.SmIntHaar.smInt_comp_inv_mulVec | (intros; apply GlobalTheory.CompanionTheory.Rodier.SmIntHaar.smInt_comp_inv_mulVec <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.Dich

open GlobalTheory.CompanionTheory.BZPhiPhi GlobalTheory.CompanionTheory.BZPhiPG.Cells

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem blockIndex_false_eq (m j : ℕ) (a : Fin m) :
    eGP m j ⟨false, a⟩ = Fin.castSucc (⟨a.1, by have := a.2; omega⟩ : Fin (m + j)) :=
  Fin.ext (blockIndex_false_val m j a)

theorem blockIndex_true_castSucc (m j : ℕ) (b : Fin (j + 1)) :
    eGP m (j + 1) ⟨true, Fin.castSucc b⟩ =
      Fin.castSucc (⟨m + b.1, by have := b.2; omega⟩ : Fin (m + (j + 1))) :=
  Fin.ext (blockIndex_true_val m (j + 1) _)

theorem mem_mirabolicParabolic_of (m j : ℕ) (x : Mir k (m + (j + 1)))
    (h : ∀ r c : Fin (m + j + 1), ¬ r.val < m → c.val < m →
      ((x : GL (Fin (m + (j + 1) + 1)) k) : Matrix _ _ k) (Fin.castSucc r) (Fin.castSucc c) = 0) :
    x ∈ MirabolicParabolic k m (j + 1) := by
  rw [mem_mirabolicParabolic_iff]
  intro b a
  rw [blockIndex_false_eq]
  induction b using Fin.lastCases with
  | last =>
    rw [blockIndex_true_last, (mem_Mir_iff k _).1 x.2]
    exact Pi.single_eq_of_ne (Fin.castSucc_ne_last _) _
  | cast b =>
    rw [blockIndex_true_castSucc]
    exact h _ _ (by simp) (by simp)

theorem unip_mem_HGP (m j : ℕ) (x : Mir k (m + (j + 1))) (v : Fin (m + (j + 1)) → k)
    (hx : (x : GL (Fin (m + (j + 1) + 1)) k) = unip k (m + (j + 1)) (Multiplicative.ofAdd v)) :
    x ∈ MirabolicParabolic k m (j + 1) := by
  refine mem_mirabolicParabolic_of m j x fun r c hr hc => ?_
  rw [hx]
  refine unip_castSucc_castSucc _ v _ _ ?_
  rintro rfl
  exact hr hc

theorem unip_entry (n : ℕ) (v : Fin n → k) (i c : Fin (n + 1))
    (h : c = Fin.last n → ∀ r : Fin n, i = Fin.castSucc r → v r = 0) :
    (unip k n (Multiplicative.ofAdd v)).val i c = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i c := by
  show (1 + colMat k n v) i c = _
  rw [Matrix.add_apply]
  by_cases hc : c = Fin.last n
  · induction i using Fin.lastCases with
    | last => simp [colMat, hc]
    | cast r => simp [colMat, hc, h hc r rfl]
  · simp [colMat, hc]

theorem gpProj_unip (m j : ℕ) (y : MirabolicParabolic k m (j + 1)) (v : Fin (m + (j + 1)) → k)
    (hv : ∀ r : Fin (m + (j + 1)), ¬ r.val < m → v r = 0)
    (hy : ((y : Mir k (m + (j + 1))) : GL (Fin (m + (j + 1) + 1)) k) =
      unip k (m + (j + 1)) (Multiplicative.ofAdd v)) :
    gpProj k m (j + 1) y = 1 := by
  have hone : ∀ (x : Bool) (a b : Two (Fin m) (Fin (j + 1 + 1)) x),
      (1 : Matrix _ _ k) (eGP m (j + 1) ⟨x, a⟩) (eGP m (j + 1) ⟨x, b⟩) =
        (1 : Matrix (Two (Fin m) (Fin (j + 1 + 1)) x) _ k) a b := by
    intro x a b
    by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne]
      intro e
      exact hab (by simpa using (eGP m (j + 1)).injective e)
  refine Prod.ext ?_ (Subtype.ext ?_)
  · apply Units.ext
    ext a b
    show ((y : Mir k (m + (j + 1))) : GL (Fin (m + (j + 1) + 1)) k).val (eGP m (j + 1) ⟨false, a⟩)
      (eGP m (j + 1) ⟨false, b⟩) = _
    rw [hy, unip_entry, hone]
    · rfl
    · intro e
      exact absurd e (blockIndex_false_ne_last m (j + 1) b)
  · apply Units.ext
    ext a b
    show ((y : Mir k (m + (j + 1))) : GL (Fin (m + (j + 1) + 1)) k).val (eGP m (j + 1) ⟨true, a⟩)
      (eGP m (j + 1) ⟨true, b⟩) = _
    rw [hy, unip_entry, hone]
    · rfl
    · intro _ r e
      refine hv r ?_
      have := congrArg Fin.val e
      rw [blockIndex_true_val] at this
      simp at this
      omega

end

section

variable {k : Type} [Field k]

theorem conj_unip (n : ℕ) (g : Mir k (n + 1)) (w : Fin (n + 1) → k) :
    ((g⁻¹ * unipM k n (Multiplicative.ofAdd w) * g : Mir k (n + 1)) : GL (Fin (n + 2)) k) =
      unip k (n + 1) (Multiplicative.ofAdd
        (((mirabolicProjection k (n + 1) g⁻¹ : GL (Fin (n + 1)) k) : Matrix _ _ k).mulVec w)) := by
  obtain ⟨v, A, hp, hA⟩ : ∃ v A, (g : GL (Fin (n + 2)) k) = unip k (n + 1) v * glEmb k (n + 1) A ∧
      A = mirabolicProjection k (n + 1) g := ⟨_, _, eq_unip_glEmb g, rfl⟩
  rw [map_inv (mirabolicProjection k (n + 1)) g, ← hA]
  have e := glEmb_mul_unip' k (n + 1) A⁻¹ (Multiplicative.ofAdd w)
  have c : (unip k (n + 1) v)⁻¹ * unip k (n + 1) (Multiplicative.ofAdd w) * unip k (n + 1) v =
      unip k (n + 1) (Multiplicative.ofAdd w) := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [mul_comm _ (Multiplicative.ofAdd w), mul_assoc]
    simp
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv, unipM_val, hp]
  simp only [toAdd_ofAdd] at e
  calc (unip k (n + 1) v * glEmb k (n + 1) A)⁻¹ * unip k (n + 1) (Multiplicative.ofAdd w) *
        (unip k (n + 1) v * glEmb k (n + 1) A)
      = (glEmb k (n + 1) A)⁻¹ * ((unip k (n + 1) v)⁻¹ * unip k (n + 1) (Multiplicative.ofAdd w) *
          unip k (n + 1) v) * glEmb k (n + 1) A := by group
    _ = glEmb k (n + 1) A⁻¹ * unip k (n + 1) (Multiplicative.ofAdd w) * glEmb k (n + 1) A := by
        rw [c, map_inv]
    _ = _ := by
        rw [e, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

end

theorem dichotomy : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), ψ ≠ 1 → ∀ (m j : ℕ) (g : Mir k (m + (j + 1))),
    (∃ h ∈ MirabolicParabolic k m (j + 1), ∃ x : Mir k (m + j), g = h * embedding₂ k (m + j) x) ∨
    ∃ u : MirUin k (m + (j + 1)), ∃ hx : g * (u : Mir k (m + (j + 1))) * g⁻¹ ∈ MirabolicParabolic k m (j + 1),
      gpProj k m (j + 1) ⟨_, hx⟩ = 1 ∧ mirChar k ψ (m + j) u ≠ 1 := by
  intro k _ _ _ _ ψ hψ m j g
  by_cases hl : ∃ l : Fin (m + j + 1), l.val < m ∧ rowQ k (m + j) g⁻¹ l ≠ 0
  · obtain ⟨l, hlm, hrl⟩ := hl
    obtain ⟨t, ht⟩ := (AddChar.ne_one_iff).1 hψ
    let w : Fin (m + j + 1) → k := Pi.single l (t / rowQ k (m + j) g⁻¹ l)
    let X : Mir k (m + j + 1) := unipM k (m + j) (Multiplicative.ofAdd w)
    have hu := conj_unip (m + j) g w
    have hmem : g⁻¹ * X * g ∈ MirUin k (m + j + 1) := ⟨_, hu.symm⟩
    have hgx : g * (g⁻¹ * X * g) * g⁻¹ = X := by group
    have hX : X ∈ MirabolicParabolic k m (j + 1) := unip_mem_HGP m j X w rfl
    have hw : ∀ r : Fin (m + (j + 1)), ¬ r.val < m → w r = 0 := by
      intro r hr
      refine Pi.single_eq_of_ne ?_ _
      rintro rfl
      exact hr hlm
    refine Or.inr ⟨⟨g⁻¹ * X * g, hmem⟩, hgx.symm ▸ hX, ?_, ?_⟩
    · refine gpProj_unip m j _ w hw ?_
      show ((g * (g⁻¹ * X * g) * g⁻¹ : Mir k (m + j + 1)) : GL (Fin (m + j + 2)) k) = _
      rw [hgx]
      rfl
    · rw [mirChar_eq k ψ (m + j) _ _ hu]
      have e : (((mirabolicProjection k (m + j + 1) g⁻¹ : GL (Fin (m + j + 1)) k) : Matrix _ _ k).mulVec w)
          (Fin.last (m + j)) = t := by
        show rowQ k (m + j) g⁻¹ ⬝ᵥ w = t
        simp only [w, dotProduct_single]
        field_simp
      simp only [toAdd_ofAdd, e]
      intro h
      apply ht
      have := congrArg Units.val h
      exact Circle.ext (by simpa using this)
  · have hr0 : ∀ l : Fin (m + j + 1), l.val < m → rowQ k (m + j) g⁻¹ l = 0 := by
      intro l hlm
      by_contra h
      exact hl ⟨l, hlm, h⟩
    obtain ⟨c, hc⟩ := row_ne_zero (mirabolicProjection k (m + j + 1) g⁻¹) (Fin.last (m + j))
    have hc' : rowQ k (m + j) g⁻¹ c ≠ 0 := hc
    have hcs : ¬ c.val < m := fun h => hc' (hr0 c h)
    have hlast : ¬ (Fin.last (m + j)).val < m := by simp
    obtain ⟨B, hBj, hB⟩ := exists_row (fun x : Fin (m + j + 1) => x.val < m) (rowQ k (m + j) g⁻¹) c
      (Fin.last (m + j)) hc' (by simp only [hcs, hlast]) (fun _ x hx => hr0 x hx)
    let d : Mir k (m + j + 1) := levi k (m + j + 1) B
    have hd : d ∈ MirabolicParabolic k m (j + 1) := by
      refine mem_mirabolicParabolic_of m j d fun r c hr hc => ?_
      exact (glEmb_castSucc_castSucc _ B _ _).trans (hB _ _ hr hc)
    have hrow : rowQ k (m + j) g⁻¹ = rowQ k (m + j) d := by
      funext c
      exact (congrFun hBj c).symm.trans (glEmb_castSucc_castSucc _ B _ _).symm
    have hQ := mul_inv_mem_Q_of_rowQ_eq (m + j) g⁻¹ d hrow
    have hQ' : d * g ∈ Q k (m + j) := by
      have := (Q k (m + j)).inv_mem hQ
      simpa using this
    obtain ⟨v, hp⟩ : ∃ v, ((d * g : Mir k (m + j + 1)) : GL (Fin (m + j + 2)) k) =
        unip k (m + j + 1) (Multiplicative.ofAdd v) * glEmb k (m + j + 1) (mirabolicProjection k (m + j + 1) (d * g)) :=
      ⟨_, eq_unip_glEmb (d * g)⟩
    let uM : Mir k (m + j + 1) := unipM k (m + j) (Multiplicative.ofAdd v)
    have huM : uM ∈ MirabolicParabolic k m (j + 1) := unip_mem_HGP m j uM v rfl
    refine Or.inl ⟨d⁻¹ * uM, (MirabolicParabolic k m (j + 1)).mul_mem ((MirabolicParabolic k m (j + 1)).inv_mem hd) huM,
      qProj k (m + j) ⟨d * g, hQ'⟩, ?_⟩
    have e : d * g = uM * embedding₂ k (m + j) (qProj k (m + j) ⟨d * g, hQ'⟩) := Subtype.ext hp
    rw [mul_assoc, ← e]
    group

end GlobalTheory.CompanionTheory.LeibPhi.Dich
end
end

section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair


theorem _root_.GlobalTheory.T.mirabolic_coefficient_translation : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), TwInv T T' B s → (∀ (y x : Fin (n + 1) → k) (v : V) (v' : V'), coef T B (T (uM (n + 1) y) v) v' x = coef T B v v' (x + y)) ∧ (∀ (y x : Fin (n + 1) → k) (v : V) (v' : V'), coef T B v (T' (uM (n + 1) y) v') x = coef T B v v' (x - y)) ∧ (∀ (g : GL (Fin (n + 1)) k) (x : Fin (n + 1) → k) (v : V) (v' : V'), coef T B (T (levi k (n + 1) g) v) (T' (levi k (n + 1) g) v') x = ((detChar (Fin (n + 1)) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) * coef T B v v' (((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x)) := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.coef_rules | exact GlobalTheory.CompanionTheory.MirPair.coef_rules | (intros; apply GlobalTheory.CompanionTheory.MirPair.coef_rules <;> assumption)
end

section

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem twist_integral_eq_JJ_shear : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → IsSmooth T → TwInv T T' B s → ∀ (b : Fin (n + 1) → k) (M : Set (Fin (n + 1) → k)) (v : V) (v' : V'), valuation k (b (Fin.last n)) < 1 → T (levi k (n + 1) (shearGL n b)) v = v → (∀ x, ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ M ↔ x ∈ M) → ∫ x in M, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (wt ψ n x * coef T B v v' x) ∂(piHaar ν (n + 1)) = JJ ν ψ T B M v (T' (levi k (n + 1) (shearGL n b)) v') := by
  intro k _ _ _ _ _ _ ν _ ψ n V V' _ _ _ _ T T' B s _ _ hB b M v v' hb hfix hM
  obtain ⟨hg, hdet⟩ := GlobalTheory.CompanionTheory.MirPair.shearGL_mulVec_and_nabs_det b hb
  obtain ⟨-, -, hlevi⟩ := GlobalTheory.CompanionTheory.MirPair.coef_rules T T' B s hB
  have hcoef : ∀ x, GlobalTheory.CompanionTheory.MirPair.coef T B v
      (T' (GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b)) v') x =
      GlobalTheory.CompanionTheory.MirPair.coef T B v v'
        ((((GlobalTheory.CompanionTheory.MirPair.shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) := by
    intro x
    have h := hlevi (GlobalTheory.CompanionTheory.MirPair.shearGL n b) x v v'
    rw [hfix] at h
    rw [h, GlobalTheory.SmGL.detChar_apply, GlobalTheory.SmGL.val_absPow, hdet]
    simp
  have hgg : ∀ x : Fin (n + 1) → k,
      ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ
        ((((GlobalTheory.CompanionTheory.MirPair.shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hset : {y : Fin (n + 1) → k | ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y ∈ M} = M := Set.ext fun y => hM y
  have key := GlobalTheory.CompanionTheory.MirPair.setIntegral_inv_mulVec ν (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b) M
    (fun y => GlobalTheory.CompanionTheory.MirPair.wt ψ n
      (((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y) *
      GlobalTheory.CompanionTheory.MirPair.coef T B v v' y)
  rw [hdet, hset] at key
  simp only [hgg, Complex.ofReal_one, NNReal.coe_one, one_mul] at key
  rw [GlobalTheory.CompanionTheory.MirPair.JJ]
  simp_rw [hcoef]
  rw [key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hlast : (x + (b ⬝ᵥ x) • GlobalTheory.BZMir.eLast k n) (Fin.last n) = x (Fin.last n) + b ⬝ᵥ x := by
    simp [GlobalTheory.BZMir.eLast]
  simp only [GlobalTheory.CompanionTheory.MirPair.wt]
  rw [hg x, hlast, show -(x (Fin.last n) + b ⬝ᵥ x) = -(b ⬝ᵥ x) + -x (Fin.last n) by ring,
    AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

end GlobalTheory.CompanionTheory.MirPair

end
end
