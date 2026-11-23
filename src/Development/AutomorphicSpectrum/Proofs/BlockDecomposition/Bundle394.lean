module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle316
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle383
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenEvaluationEquivariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle372
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle354
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle351
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle380
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle369
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle379
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle122
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle370
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle349
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnitaryRootEmbedding
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle387
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibQ

section Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def mulVecHomeo {t : ℕ} (w : GL (Fin t) k) : (Fin t → k) ≃ₜ (Fin t → k) where
  toFun v := (w : Matrix (Fin t) (Fin t) k).mulVec v
  invFun v := ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v
  left_inv v := by
    show ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec ((w : Matrix (Fin t) (Fin t) k).mulVec v) = v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  right_inv v := by
    show (w : Matrix (Fin t) (Fin t) k).mulVec (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v) = v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem smInt_transform {t : ℕ} [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)]
    (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure]
    {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (Φ Ψ : (Fin t → k) → X) (B : X →ₗ[ℂ] Y) (A : Y →ₗ[ℂ] Y) (w : GL (Fin t) k)
    (lΦ : IsLocallyConstant Φ) (cΦ : HasCompactSupport Φ)
    (lΨ : IsLocallyConstant Ψ) (cΨ : HasCompactSupport Ψ)
    (h : ∀ v, B (Φ v) = A (B (Ψ (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v)))) :
    B (smInt μ Φ) = ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • A (B (smInt μ Ψ)) := by
  have lG : IsLocallyConstant (B ∘ Ψ) := lΨ.comp B
  have cG : HasCompactSupport (B ∘ Ψ) := cΨ.comp_left (map_zero B)
  have lGL : IsLocallyConstant ((B ∘ Ψ) ∘ (mulVecHomeo w⁻¹)) := lG.comp_continuous (mulVecHomeo w⁻¹).continuous
  have cGL : HasCompactSupport ((B ∘ Ψ) ∘ (mulVecHomeo w⁻¹)) := cG.comp_homeomorph (mulVecHomeo w⁻¹)
  calc B (smInt μ Φ) = smInt μ (B ∘ Φ) := (SmIntEl.smInt_linear μ B lΦ cΦ).symm
    _ = smInt μ (A ∘ ((B ∘ Ψ) ∘ (mulVecHomeo w⁻¹))) := congrArg (smInt μ) (funext h)
    _ = A (smInt μ ((B ∘ Ψ) ∘ (mulVecHomeo w⁻¹))) := SmIntEl.smInt_linear μ A lGL cGL
    _ = A (((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • smInt μ (B ∘ Ψ)) :=
        congrArg A (GlobalTheory.T.smooth_integral_linear_change k t μ w (B ∘ Ψ) lG cG)
    _ = ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • A (smInt μ (B ∘ Ψ)) := map_smul A _ _
    _ = ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • A (B (smInt μ Ψ)) :=
        congrArg (fun z => ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • A z) (SmIntEl.smInt_linear μ B lΨ cΨ)

end Abstract

section Group

variable (k : Type) [Field k]

theorem point_eq (i t : ℕ) (q g : GL (Fin (i + t)) k) (y : Fin (i + t) → k) (x : Fin i → k) (u : Fin t → k)
    (hx : ((q⁻¹ : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y = topV k i t x + midV k i t u) :
    uM k (i + t) y * levi k (i + t) (q * g) =
      levi k (i + t) q * uM k (i + t) (topV k i t x) * (uM k (i + t) (midV k i t u) * levi k (i + t) g) := by
  have h := levi_mul_uM k (i + t) q⁻¹ y
  rw [hx, uM_add, map_inv] at h
  have h2 : uM k (i + t) y =
      levi k (i + t) q * (uM k (i + t) (topV k i t x) * uM k (i + t) (midV k i t u) * (levi k (i + t) q)⁻¹) :=
    inv_mul_eq_iff_eq_mul.mp h
  calc uM k (i + t) y * levi k (i + t) (q * g)
      = levi k (i + t) q * (uM k (i + t) (topV k i t x) * uM k (i + t) (midV k i t u) * (levi k (i + t) q)⁻¹) *
          (levi k (i + t) q * levi k (i + t) g) := by rw [map_mul, ← h2]
    _ = _ := by group

end Group

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem clT_extTensor (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (a : GL (Fin i) k) (x : Fin i → k) (w : GL (Fin t) k) (z : V ⊗[ℂ] W) :
    clT τ W (extTensor τ σ (levi k i a * uM k i x, w) z) =
      extTensor (psiMinus k τ) σ (a, w) (clT τ W z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v u =>
    have e : (twKer τ (MirUin k i) 1).mkQ (τ (uM k i x) v) = (twKer τ (MirUin k i) 1).mkQ v := by
      refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨uM k i x, uM_mem k i x⟩, v, ?_⟩)
      simp
    have e2 : (twKer τ (MirUin k i) 1).mkQ (τ (levi k i a * uM k i x) v) =
        psiMinus k τ a ((twKer τ (MirUin k i) 1).mkQ v) := by
      rw [← e, map_mul]
      rfl
    simp only [clT, extTensor_tmul, LinearMap.rTensor_tmul]
    rw [e2]

theorem fibV_mul (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (q : Qp k i t) (g : GL (Fin (i + t)) k) (v u : Fin t → k) (x : Fin i → k)
    (hx : (((q : GL (Fin (i + t)) k)⁻¹ : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec (midV k i t v) =
      topV k i t x + midV k i t u) :
    fibV f ((q : GL (Fin (i + t)) k) * g) v =
      extTensor τ σ (levi k i (qBlocks k i t q).1 * uM k i x, (qBlocks k i t q).2) (fibV f g u) := by
  obtain ⟨m1, p1⟩ := GlobalTheory.T.levi_block_mem_parabolic k i t q
  obtain ⟨m2, p2⟩ := GlobalTheory.T.unipotent_top_mem_parabolic k i t x
  have key := f.1.1.2 ((⟨_, m1⟩ : HPG k i t) * ⟨_, m2⟩) (uM k (i + t) (midV k i t u) * levi k (i + t) g)
  have e : pgProj k i t ((⟨_, m1⟩ : HPG k i t) * ⟨_, m2⟩) =
      (levi k i (qBlocks k i t q).1 * uM k i x, (qBlocks k i t q).2) := by
    rw [map_mul, p1, p2]
    simp
  calc fibV f ((q : GL (Fin (i + t)) k) * g) v
      = f.1.1.1 (levi k (i + t) (q : GL (Fin (i + t)) k) * uM k (i + t) (topV k i t x) *
          (uM k (i + t) (midV k i t u) * levi k (i + t) g)) :=
        congrArg f.1.1.1 (point_eq k i t _ g _ x u hx)
    _ = extTensor τ σ (pgProj k i t ((⟨_, m1⟩ : HPG k i t) * ⟨_, m2⟩)) (fibV f g u) := key
    _ = _ := congrArg (fun y => extTensor τ σ y (fibV f g u)) e

end Rep

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure], ∀ (f : cIndSpace (HPG k i t) (hRep τ σ)) (q : Qp k i t) (g : GL (Fin (i + t)) k), fibInt μ f ((q : GL (Fin (i + t)) k) * g) = qRep τ σ q (fibInt μ f g) := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ _ _ μ _ f q g
  have h1 := GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ f ((q : GL (Fin (i + t)) k) * g)
  have h2 := GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ f g
  have hpt : ∀ v, clT τ W (fibV f ((q : GL (Fin (i + t)) k) * g) v) =
      extTensor (psiMinus k τ) σ ((qBlocks k i t q).1, (qBlocks k i t q).2)
        (clT τ W (fibV f g ((((qBlocks k i t q).2⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v))) := by
    intro v
    obtain ⟨x, hx⟩ := GlobalTheory.T.mulVec_mid_block_decomp k i t q⁻¹ v
    have hb : (qBlocks k i t q⁻¹).2 = (qBlocks k i t q).2⁻¹ := by
      rw [map_inv, Prod.snd_inv]
    rw [hb] at hx
    have e := fibV_mul τ σ f q g v _ x hx
    exact (congrArg (clT τ W) e).trans (clT_extTensor τ σ _ x _ _)
  exact smInt_transform μ _ _ (clT τ W)
    (extTensor (psiMinus k τ) σ ((qBlocks k i t q).1, (qBlocks k i t q).2)) (qBlocks k i t q).2
    h1.1 h1.2 h2.1 h2.2 hpt

end GlobalTheory.CompanionTheory.BZPsiPG.FibQ

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.open_evaluation_equivariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (u : MirUin k ((i + 1) + t + 1)) (f : XS τ σ),
  eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (u : Mir k ((i + 1) + t + 1)) f) =
      ((mirChar k ψ ((i + 1) + t) u : ℂˣ) : ℂ) • eO ψ f := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.TwO.eO_cInd | exact GlobalTheory.CompanionTheory.BZPhiPG.TwO.eO_cInd | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.TwO.eO_cInd <;> assumption)
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

theorem mem_twKer_of_sum {G X ι : Type} [Group G] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
    (N : Subgroup G) (T : Finset ι) (hT : T.Nonempty) (g : ι → N) (x : X) (hs : ∑ t ∈ T, ρ (g t : G) x = 0) :
    x ∈ twKer ρ N 1 := by
  have hc : (T.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hT.card_pos.ne'
  have hmem : ∀ t ∈ T, x - ρ (g t : G) x ∈ twKer ρ N 1 := by
    intro t _
    have hg : ρ (g t : G) x - (((1 : N →* ℂˣ) (g t) : ℂˣ) : ℂ) • x ∈ twKer ρ N 1 :=
      Submodule.subset_span ⟨g t, x, rfl⟩
    have := (twKer ρ N 1).neg_mem hg
    simpa using this
  have hs' : (T.card : ℂ) • x = ∑ t ∈ T, (x - ρ (g t : G) x) := by
    rw [Finset.sum_sub_distrib, hs, sub_zero, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have h1 : (T.card : ℂ) • x ∈ twKer ρ N 1 := by
    rw [hs']
    exact Submodule.sum_mem _ hmem
  exact ((twKer ρ N 1).smul_mem_iff hc).1 h1

theorem exists_reps {L : Type} [Group L] (K : Subgroup L) (hK : K.FiniteIndex) :
    ∃ T : Finset L, T.Nonempty ∧ ∀ x : L, ∃! t, t ∈ T ∧ t⁻¹ * x ∈ K := by
  classical
  haveI : Fintype (L ⧸ K) := Fintype.ofFinite _
  refine ⟨(Finset.univ : Finset (L ⧸ K)).image Quotient.out, ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk 1))⟩, ?_⟩
  intro x
  refine ⟨(QuotientGroup.mk x : L ⧸ K).out, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
  · exact QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
  · rintro t ⟨ht, hx⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ht
    have : q = (QuotientGroup.mk x : L ⧸ K) := by
      rw [← QuotientGroup.out_eq' q]
      exact QuotientGroup.eq.2 hx
    rw [this]

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_mulH {n : ℕ} (κ : GL (Fin n) k) : Continuous (mulH κ) := by
  have : Continuous fun y : Fin n → k => (κ : Matrix (Fin n) (Fin n) k).mulVec y :=
    Continuous.matrix_mulVec continuous_const continuous_id
  exact continuous_ofAdd.comp (this.comp continuous_toAdd)

theorem continuous_uMh (n : ℕ) : Continuous (uMh k n) :=
  (GlobalTheory.T.continuous_levi_unipotent_proj k n).2.1.comp continuous_toAdd

theorem exists_sum_eq_zero_abs (n : ℕ) {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) Y) (hρ : IsSmooth ρ)
    (ρ' : Representation ℂ (Multiplicative (Fin n → k)) X) (hρ' : IsSmooth ρ')
    (S : Set (GL (Fin n) k)) (hS : ∀ κ ∈ S, κ ∈ GlobalTheory.SplitWeil.KO k (Fin n))
    (F : GL (Fin n) k → X →ₗ[ℂ] Y)
    (hF : ∀ κ ∈ S, ∀ y x, F κ (ρ' y x) = ρ (mulH κ y) (F κ x))
    (hinj : ∀ x, (∀ κ ∈ S, F κ x = 0) → x = 0)
    (x : X) (hx : ∀ κ ∈ S, F κ x ∈ twKer ρ ⊤ 1) (hfin : ((fun κ => F κ x) '' S).Finite) :
    ∃ T : Finset (Multiplicative (Fin n → k)), T.Nonempty ∧ ∑ y ∈ T, ρ' y x = 0 := by
  classical
  obtain ⟨c, hc, hS'⟩ := GlobalTheory.T.finite_jacquet_kernel_common_lattice k n ρ _ hfin (by
    rintro _ ⟨κ, hκ, rfl⟩
    exact hx κ hκ)
  have hcomp : IsCompact (Lc n c : Set (Multiplicative (Fin n → k))) := isCompact_Lc n hc
  have hθ : IsOpen (((1 : Lc n c →* ℂˣ).ker : Subgroup (Lc n c)) : Set (Lc n c)) := by
    have : (((1 : Lc n c →* ℂˣ).ker : Subgroup (Lc n c)) : Set (Lc n c)) = Set.univ := by
      ext l
      simp [MonoidHom.mem_ker]
    rw [this]
    exact isOpen_univ
  set K := GlobalTheory.CompanionTheory.TwistedAverage.stabKer ρ' (Lc n c) 1 x with hK
  have hKo : IsOpen (K : Set (Lc n c)) := GlobalTheory.CompanionTheory.TwistedAverage.isOpen_stabKer hρ' _ _ hθ x
  have hKf : K.FiniteIndex := GlobalTheory.CompanionTheory.TwistedAverage.finiteIndex_stabKer hρ' hcomp _ hθ x
  obtain ⟨T, hTn, hT⟩ := exists_reps K hKf
  refine ⟨T.image Subtype.val, hTn.image _, ?_⟩
  rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
  refine hinj _ fun κ hκ => ?_

  rw [map_sum]
  have hsmooth : IsSmooth (MonoidHom.comp ρ (mulH κ)) := fun v =>
    (hρ v).preimage (continuous_mulH κ)
  have key := GlobalTheory.T.sum_over_compact_cosets_jacquet_kernel (MonoidHom.comp ρ (mulH κ)) hsmooth (Lc n c) hcomp (F κ x)
    (GlobalTheory.T.jacquet_kernel_lattice_conj_compact k n ρ c κ (hS κ hκ) _ (hS' _ ⟨κ, hκ, rfl⟩)) K T hKo
    (fun l hl => by
      have h1 : ρ' (l : Multiplicative (Fin n → k)) x = x := hl.1
      have h2 := hF κ hκ (l : Multiplicative (Fin n → k)) x
      rw [h1] at h2
      exact h2.symm) hT
  refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) key
  exact hF κ hκ _ x

theorem mem_twKer_fibAct (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z)
    [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure]
    (φ : fibM (Fin t → k) Z) (h : smInt μ φ.1 ∈ twKer ρ₀ ⊤ 1) : φ ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
  classical
  obtain ⟨c, hc, hinv⟩ := GlobalTheory.T.exists_lattice_periodicity k t φ.1 φ.2.1 φ.2.2
  obtain ⟨A, hA⟩ := GlobalTheory.T.locally_constant_coset_indicator_sum k t φ.1 c hc φ.2.2 hinv
  have hφ : φ.1 = fun v => ∑ a ∈ A, (cosetSet t c a).indicator (fun _ => φ.1 a) v := funext hA
  have hsum : φ = ∑ a ∈ A, cosetFn t hc a (φ.1 a) := by
    apply Subtype.ext
    funext v
    rw [hA v, Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hI := GlobalTheory.T.integral_coset_indicator_sum k t μ c hc A φ.1
  rw [← hφ] at hI
  rw [hI] at h
  have hz : ∑ a ∈ A, φ.1 a ∈ twKer ρ₀ ⊤ 1 := ((twKer ρ₀ ⊤ 1).smul_mem_iff (GlobalTheory.T.haar_measure_coset_ne_zero k t μ c hc)).1 h
  have h0 : cosetFn t hc 0 (∑ a ∈ A, φ.1 a) = ∑ a ∈ A, cosetFn t hc 0 (φ.1 a) := by
    apply Subtype.ext
    funext v
    rw [Submodule.coe_sum, Finset.sum_apply]
    have e : ∀ z : Z, (cosetFn t hc 0 z).1 v = (cosetSet t c 0).indicator (fun _ => z) v := fun _ => rfl
    simp only [e]
    by_cases hv : v ∈ cosetSet t c 0
    · simp only [Set.indicator_of_mem hv]
    · simp only [Set.indicator_of_notMem hv, Finset.sum_const_zero]
  have hd : φ - cosetFn t hc 0 (∑ a ∈ A, φ.1 a) ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
    have e : φ - cosetFn t hc 0 (∑ a ∈ A, φ.1 a) = ∑ a ∈ A, (cosetFn t hc a (φ.1 a) - cosetFn t hc 0 (φ.1 a)) := by
      rw [h0, Finset.sum_sub_distrib, ← hsum]
    rw [e]
    exact Submodule.sum_mem _ fun a _ => GlobalTheory.T.coset_function_translate_jacquet_kernel k i t ρ₀ c hc a _
  have := (twKer (fibAct t ρ₀) ⊤ 1).add_mem hd (GlobalTheory.T.coset_function_jacquet_kernel k i t ρ₀ c hc _ hz)
  simpa using this

end

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def fibLin (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (hτ : IsSmooth τ) (hσ : IsSmooth σ)
    (κ : GL (Fin (i + t)) k) : cIndSpace (HPG k i t) (hRep τ σ) →ₗ[ℂ] fibM (Fin t → k) (V ⊗[ℂ] W) :=
  LinearMap.codRestrict (fibM (Fin t → k) (V ⊗[ℂ] W))
    (LinearMap.pi fun v => evL (τ := τ) (σ := σ) (uM k (i + t) (midV k i t v) * levi k (i + t) κ))
    (fun x => GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ x κ)

end

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer


theorem GlobalTheory.CompanionTheory.BZPsiPG.FibKer.mem_twKer_of_fibInt_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure], ∀ f : cIndSpace (HPG k i t) (hRep τ σ), (∀ g, fibInt μ f g = 0) → f ∈ twKer (prodPG τ σ) (MirUin k (i + t)) 1 := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ _ _ μ _ f hf
  classical
  have hsm₀ : IsSmooth (topRep τ W) := GlobalTheory.T.smooth_top_representation k i τ hτ
  have hsm : IsSmooth (fibAct t (topRep τ W)) := GlobalTheory.T.smooth_fibre_action k i t (topRep τ W) hsm₀
  have hsmP : IsSmooth (MonoidHom.comp (prodPG τ σ) (uMh k (i + t))) := fun v =>
    (GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd _ _ v).preimage (continuous_uMh (i + t))
  have hker : ∀ κ, fibLin τ σ hτ hσ κ f ∈ twKer (fibAct t (topRep τ W)) ⊤ 1 := fun κ =>
    mem_twKer_fibAct i t (topRep τ W) μ (fibLin τ σ hτ hσ κ f) (GlobalTheory.T.closure_kernel_mem_jacquet_kernel k i τ _ (hf κ))
  have hfin : ((fun κ => fibLin τ σ hτ hσ κ f) '' (GlobalTheory.SplitWeil.KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k))).Finite := by
    refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
    rw [Set.image_image]
    exact GlobalTheory.T.finite_fibre_functions_compact k i t τ σ f
  have hF : ∀ κ ∈ (GlobalTheory.SplitWeil.KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k)), ∀ y x,
      fibLin τ σ hτ hσ κ (MonoidHom.comp (prodPG τ σ) (uMh k (i + t)) y x) =
        fibAct t (topRep τ W) (mulH κ y) (fibLin τ σ hτ hσ κ x) := by
    intro κ _ y x
    apply Subtype.ext
    funext v
    exact GlobalTheory.T.fibre_function_unipotent_action k i t τ σ x y.toAdd κ v
  have hinj : ∀ x, (∀ κ ∈ (GlobalTheory.SplitWeil.KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k)), fibLin τ σ hτ hσ κ x = 0) → x = 0 := by
    intro x hx
    exact GlobalTheory.T.induced_vanishing_on_compact k i t τ σ x fun κ hκ => congrArg Subtype.val (hx κ hκ)
  obtain ⟨T, hTn, hT⟩ := exists_sum_eq_zero_abs (i + t) (fibAct t (topRep τ W)) hsm
    (MonoidHom.comp (prodPG τ σ) (uMh k (i + t))) hsmP _ (fun _ h => h) (fibLin τ σ hτ hσ) hF hinj f
    (fun κ _ => hker κ) hfin
  exact mem_twKer_of_sum (prodPG τ σ) (MirUin k (i + t)) T hTn
    (fun y => ⟨uM k (i + t) y.toAdd, uM_mem k (i + t) y.toAdd⟩) f hT

end
end

section

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

namespace GlobalTheory.CompanionTheory.SwapRoot

section Cont

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem continuous_of_v_eq (σ : L →+* L) (hv : ∀ x, Valued.v (σ x) = Valued.v x) : Continuous σ := by
  refine continuous_of_continuousAt_zero σ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero L _).tendsto_iff (Valued.hasBasis_nhds_zero L _)]
  refine fun γ _ => ⟨γ, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq] at hx ⊢
  rwa [show Valued.v.restrict (σ x) = Valued.v.restrict x from (Valuation.restrict_inj _).2 (hv x)]

theorem continuous_nU_val : Continuous fun x : L => ((nU x : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [nU] <;> first | exact continuous_id | exact continuous_const

theorem continuous_nU_inv_val :
    Continuous fun x : L => (((nU x)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [nU, Units.inv_mk] <;>
    first | exact continuous_id | exact continuous_const | exact continuous_neg

theorem continuous_partner_nU (σ : L →+* L) (hc : Continuous σ) :
    Continuous fun x : L => partner σ (nU x) := by
  unfold partner cT
  exact (continuous_const.matrix_mul
    (continuous_nU_inv_val.matrix_map hc).matrix_transpose).matrix_mul continuous_const

theorem continuous_uR_val (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ) (a : ℕ)
    (h : 2 * (a + 2) ≤ n) :
    Continuous fun x : L => (((uR σ hσ a h x : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
  simp only [uR, rootHom_val, blockM]
  exact (continuous_const.add (((continuous_const.matrix_mul
    (continuous_nU_val.sub continuous_const))).matrix_mul continuous_const)).add
    ((continuous_const.matrix_mul
    ((continuous_partner_nU σ hc).sub continuous_const)).matrix_mul continuous_const)

theorem uR_neg (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) :
    (uR σ hσ a h x)⁻¹ = uR σ hσ a h (-x) := by
  have h0 : uR σ hσ a h (0 : L) = 1 := by
    have e : nU (0 : L) = 1 := by
      ext p r; fin_cases p <;> fin_cases r <;> simp [nU]
    simp only [uR, e, map_one]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← uR_add, add_neg_cancel, h0]

theorem continuous_uR : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n),
    Continuous (uR σ hU.1 a h : L → GU σ n) := by
  intro L _ _ ϖ σ q n hU a h
  have hc : Continuous σ := continuous_of_v_eq σ hU.2.1
  refine Continuous.subtype_mk (f := fun x => ((uR σ hU.1 a h x : GU σ n) : GL (Fin n) L)) ?_ _
  refine Units.continuous_iff.2 ⟨continuous_uR_val σ hU.1 hc a h, ?_⟩
  have e : ∀ x : L, ((((uR σ hU.1 a h x : GU σ n) : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      (((uR σ hU.1 a h (-x) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := fun x => by
    rw [← uR_neg, Subgroup.coe_inv]
  simp only [e]
  exact (continuous_uR_val σ hU.1 hc a h).comp continuous_neg

end Cont

end GlobalTheory.CompanionTheory.SwapRoot

end
end

section

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

namespace GlobalTheory.CompanionTheory.SwapRoot.Unip

variable {L : Type} [Field L] {n : ℕ}

theorem sR_uR_mul_unip : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (v : GU σ n), IsUnipU v →
    ∃ y : L, ∀ x : L, ∃ b : GU σ n, IsUnipU b ∧
      sR σ hσ a h * uR σ hσ a h x * v = b * (sR σ hσ a h * uR σ hσ a h (x + y)) :=
  _root_.UpperTheory.Reformulated.B.AntidiagonalWeylElement.sR_uR_mul_unip

end GlobalTheory.CompanionTheory.SwapRoot.Unip

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

theorem _root_.GlobalTheory.T.exponent_lt_of_precedes_of_isLSeg : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ Δ' : Segment k) (y y' : IrrGL (k := k)) (s s' : ℝ), IsLSeg Δ y.rep → IsLSeg Δ' y'.rep → (∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y t c → ‖c‖ = nabs k t ^ ((y.1 : ℝ) * s)) → (∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y' t c → ‖c‖ = nabs k t ^ ((y'.1 : ℝ) * s')) → Δ.Precedes Δ' → s < s' := by
  first | exact @GlobalTheory.CompanionTheory.SegExp.exponent_lt_of_precedes | exact GlobalTheory.CompanionTheory.SegExp.exponent_lt_of_precedes | (intros; apply GlobalTheory.CompanionTheory.SegExp.exponent_lt_of_precedes <;> assumption)
end
