module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle035
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjInvariantCharacterTransport
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle118
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle117
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleHomFixedVectors
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle029
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle120
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle101
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

noncomputable section

open Matrix ValuativeRel GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.BZMirExhaust

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ballSub (s : kˣ) : AddSubgroup k where
  carrier := cball s
  zero_mem' := by simp [cball]
  add_mem' {a b} ha hb := by
    have ha' : valuation k a ≤ valuation k (s : k) := ha
    have hb' : valuation k b ≤ valuation k (s : k) := hb
    exact (Valuation.map_add _ a b).trans (max_le ha' hb')
  neg_mem' {a} ha := by
    have ha' : valuation k a ≤ valuation k (s : k) := ha
    show valuation k (-a) ≤ valuation k (s : k)
    rwa [Valuation.map_neg]

theorem exists_ball_of_finset (T : Finset k) : ∃ s : kˣ, ∀ x ∈ T, x ∈ cball s := by
  classical
  refine Finset.induction_on T ?_ ?_
  · exact ⟨1, by simp⟩
  · intro a T _ ih
    obtain ⟨s, hs⟩ := ih
    by_cases h : valuation k a ≤ valuation k (s : k)
    · refine ⟨s, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact h
      · exact hs x hx
    · have ha0 : a ≠ 0 := by
        rintro rfl
        exact h (by simp)
      refine ⟨Units.mk0 a ha0, fun x hx => ?_⟩
      show valuation k x ≤ valuation k a
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact le_rfl
      · have hx' : valuation k x ≤ valuation k (s : k) := hs x hx
        exact le_trans hx' (le_of_lt (not_le.1 h))

def unipMir (n : ℕ) : Multiplicative (Fin n → k) →* Mir k n :=
  (unip k n).codRestrict (Mir k n) (fun v => MirU_le_Mir k n ⟨v, rfl⟩)

theorem continuous_colMat (n : ℕ) : Continuous (colMat k n) := by
  refine continuous_matrix fun i j => ?_
  unfold GlobalTheory.BZMir.colMat
  by_cases hj : j = Fin.last n
  · simp only [if_pos hj]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · simp only [Fin.lastCases_castSucc]
      exact continuous_apply i
    · simp only [Fin.lastCases_last]
      exact continuous_const
  · simp only [if_neg hj]
    exact continuous_const

theorem continuous_unipMir (n : ℕ) :
    Continuous (fun v : Fin n → k => unipMir (k := k) n (Multiplicative.ofAdd v)) := by
  have hval : Continuous fun v : Fin n → k =>
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + GlobalTheory.BZMir.colMat k n v :=
    continuous_const.add (GlobalTheory.CompanionTheory.BZMirExhaust.continuous_colMat n)
  have hinv : Continuous fun v : Fin n → k =>
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) - GlobalTheory.BZMir.colMat k n v :=
    continuous_const.sub (GlobalTheory.CompanionTheory.BZMirExhaust.continuous_colMat n)
  have hGL : Continuous fun v : Fin n → k =>
      GlobalTheory.BZMir.unip k n (Multiplicative.ofAdd v) :=
    Units.continuous_iff.2 ⟨hval, hinv⟩
  exact hGL.subtype_mk _

def ballGroup (n : ℕ) (s : kˣ) : Subgroup (Mir k n) :=
  (AddSubgroup.toSubgroup (AddSubgroup.pi Set.univ fun _ : Fin n => ballSub s)).map (unipMir n)

theorem ballGroup_le (n : ℕ) (s : kˣ) : ballGroup (k := k) n s ≤ MirUin k n := by
  rintro _ ⟨v, -, rfl⟩
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU]
  exact ⟨v, rfl⟩

theorem coe_ballGroup (n : ℕ) (s : kˣ) : (ballGroup (k := k) n s : Set (Mir k n)) =
    (fun v : Fin n → k => unipMir (k := k) n (Multiplicative.ofAdd v)) '' Set.univ.pi fun _ => cball s := by
  rw [GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup, Subgroup.coe_map]
  ext g
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Multiplicative.toAdd v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Multiplicative.ofAdd v, hv, rfl⟩

theorem isCompact_ballGroup (n : ℕ) (s : kˣ) : IsCompact (ballGroup (k := k) n s : Set (Mir k n)) := by
  rw [GlobalTheory.CompanionTheory.BZMirExhaust.coe_ballGroup]
  exact (isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_cball s).image
    (GlobalTheory.CompanionTheory.BZMirExhaust.continuous_unipMir n)

theorem exhaust (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GlobalTheory.BZMir.Fun.Exhaust k := by
  classical
  intro n S hS
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.BZMirExhaust.exists_ball_of_finset
    ((S ×ˢ (Finset.univ : Finset (Fin n))).image fun p =>
      ((p.1 : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc p.2) (Fin.last n))
  refine ⟨GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup n s, GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup_le n s, ?_,
    GlobalTheory.CompanionTheory.BZMirExhaust.isCompact_ballGroup n s⟩
  intro g hg
  have hgU := hS hg
  rw [SetLike.mem_coe, GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range] at hgU
  obtain ⟨v, hv⟩ := hgU
  rw [Finset.mem_coe] at hg
  rw [SetLike.mem_coe, GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup, Subgroup.mem_map]
  refine ⟨v, ?_, Subtype.ext hv⟩
  show ∀ i ∈ Set.univ, Multiplicative.toAdd v i ∈ GlobalTheory.CompanionTheory.BZMirExhaust.ballSub s
  intro i _
  have hvi := GlobalTheory.BZMir.unip_apply_castSucc_last k n v i
  rw [hv] at hvi
  show Multiplicative.toAdd v i ∈ GlobalTheory.SplitWeil.cball s
  rw [← hvi]
  exact hs _ (Finset.mem_image.2 ⟨(g, i), Finset.mem_product.2 ⟨hg, Finset.mem_univ i⟩, rfl⟩)

end GlobalTheory.CompanionTheory.BZMirExhaust

end
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirSmooth

section General

variable {G M V : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V]

theorem isSmooth_twAct [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M]
    (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n)
    (hc : Continuous s) (hρ : IsSmooth ρ) : IsSmooth (twAct ρ N θ s hs) :=
  _root_.UpperTheory.Reformulated.B.Gwa2.isSmooth_twAct ρ N θ s hs hc hρ

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_glEmbHom (n : ℕ) : Continuous (glEmbHom k n) := by
  refine continuous_matrix fun i j => ?_
  show Continuous fun A : Matrix (Fin n) (Fin n) k => glEmbMat k n A i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simpa [glEmbMat] using continuous_const
    | cast j => simpa [glEmbMat] using continuous_const
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa [glEmbMat] using continuous_const
    | cast j =>
      simpa [glEmbMat] using (continuous_id.matrix_elem i j)

theorem continuous_glEmb (n : ℕ) : Continuous (glEmb k n) :=
  Continuous.units_map _ (continuous_glEmbHom n)

theorem continuous_levi (n : ℕ) : Continuous (levi k n) :=
  (continuous_glEmb n).subtype_mk _

theorem smPhiMinus (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    SmPhiMinus k := by
  intro ψ n V _ _ τ hτ
  exact isSmooth_twAct τ (MirUin k (n + 1)) (mirChar k ψ n) ((levi k (n + 1)).comp (Mir k n).subtype) (levi_stab ψ n)
    ((continuous_levi (n + 1)).comp continuous_subtype_val) hτ

end GlobalTheory.CompanionTheory.BZMirSmooth

end
end

section

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirFun

open Matrix

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_glEmbHom (n : ℕ) : Continuous (glEmbHom k n) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun A : Matrix (Fin n) (Fin n) k => glEmbMat k n A i j
  induction i using Fin.lastCases with
  | last => induction j using Fin.lastCases <;> simpa [glEmbMat] using continuous_const
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa [glEmbMat] using continuous_const
    | cast j =>
      simp only [glEmbMat, Fin.lastCases_castSucc]
      exact (continuous_apply j).comp (continuous_apply i)

theorem continuous_levi (n : ℕ) : Continuous (levi k n) := by
  have h : Continuous (glEmb k n) := Continuous.units_map _ (continuous_glEmbHom k n)
  exact h.subtype_mk _

theorem smPsiMinus : SmPsiMinus k :=
  by apply _root_.UpperTheory.Reformulated.B.DYhc8.main <;> assumption

end GlobalTheory.CompanionTheory.BZMirFun
end

section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeSub

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_iterate_eq_zero_of_subquot {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (hE : IsHk K e) (π : Representation ℂ (GL ι F) V)
    (ρ : Representation ℂ (GL ι F) U) (hρ : IsSmooth ρ) (hfl : HasFiniteLength ρ)
    (hkill : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL ι F) W), IsSmooth τ →
      τ.IsIrreducible → IsSubquotient τ ρ → IsEmpty (τ.Equiv π) → ∀ w ∈ fixed τ K, hk τ K e w = 0)
    (hns : ¬ IsSubquotient π ρ) (S : Subrepresentation ρ) :
    ∃ r : ℕ, ∀ u ∈ S.toSubmodule, u ∈ fixed ρ K → (hk ρ K e)^[r] u = 0 := by
  obtain ⟨hGT, hLT⟩ := (hasFiniteLength_iff_wellFounded ρ).1 hfl
  induction S using WellFoundedLT.induction with
  | ind S ih =>
    by_cases hS : S = ⊥
    · subst hS
      exact ⟨0, fun u hu _ => hu⟩
    obtain ⟨T, hT, hmax⟩ := (wellFounded_gt (α := Subrepresentation ρ)).has_min {T | T < S}
      ⟨⊥, bot_lt_iff_ne_bot.2 hS⟩
    have hcov : T ⋖ S := ⟨hT, fun c h1 h2 => hmax c h2 h1⟩
    let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    have hsq : IsSubquotient (subQuot S T) ρ := ⟨S, p, Submodule.mkQ_surjective _⟩
    have hne : IsEmpty ((subQuot S T).Equiv π) := ⟨fun φ => hns
      ((IsSubquotient.trans (IsSubquotient.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective) hsq))⟩
    obtain ⟨r, hr⟩ := ih T hT
    refine ⟨r + 1, fun u huS hufix => ?_⟩
    have hfixS : (Submodule.mkQ _ (⟨u, huS⟩ : S.toSubmodule) :
        S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) ∈ fixed (subQuot S T) K := by
      intro h
      have h1 : ρ (h : GL ι F) u = u := by simpa using hufix h
      have h2 : S.toRepresentation (h : GL ι F) ⟨u, huS⟩ = ⟨u, huS⟩ := Subtype.ext h1
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      exact congrArg (Submodule.mkQ _) h2
    have h0 := hkill _ (subQuot S T) (hsq.isSmooth hρ) (isIrreducible_subQuot hcov) hsq hne _ hfixS
    have h1 : (hk S.toRepresentation K e ⟨u, huS⟩ : S.toSubmodule).1 = hk ρ K e u :=
      hk_map S.toRepresentation ρ S.toSubmodule.subtype (fun _ _ => rfl) hE ⟨u, huS⟩
    have h2 := hk_map S.toRepresentation (subQuot S T) (Submodule.mkQ _) (fun _ _ => rfl) hE ⟨u, huS⟩
    rw [h0] at h2
    have h3 : hk ρ K e u ∈ T.toSubmodule := by
      rw [← h1]
      exact (Submodule.Quotient.mk_eq_zero (T.toSubmodule.comap S.toSubmodule.subtype)).1 h2
    rw [Function.iterate_succ_apply]
    exact hr _ h3 (GlobalTheory.CompanionTheory.HeckeFix.hk_mem_fixed F ι K e hE U ρ u hufix).1

end GlobalTheory.CompanionTheory.HeckeSub
end

section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeAlg

theorem hk_alg : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], HkAlg F ι := by
  intro F _ _ _ _ ι _ _
  unfold HkAlg
  intro K e₁ e₂ h₁ h₂
  obtain ⟨hstar₁, hadj⟩ := GlobalTheory.CompanionTheory.HeckeAdj.hk_adjoint F ι K e₁ h₁
  refine ⟨GlobalTheory.CompanionTheory.HeckeMul.isHk_hconv h₁ h₂, hstar₁, ?_⟩
  intro V _ _ ρ v hv
  exact ⟨(GlobalTheory.CompanionTheory.HeckeFix.hk_mem_fixed F ι K e₁ h₁ V ρ v hv).1,
    GlobalTheory.CompanionTheory.HeckeMul.hk_hconv h₁ h₂ ρ hv,
    fun B hB w hw => hadj V ρ B hB v hv w hw⟩

end GlobalTheory.CompanionTheory.HeckeAlg
end

section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

theorem _root_.GlobalTheory.T.irreducible_hom_fixed_vectors : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι] (K : Subgroup (GL ι F)), IsOpen (K : Set (GL ι F)) → IsCompact (K : Set (GL ι F)) → ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL ι F) V) (τ : Representation ℂ (GL ι F) W), GlobalTheory.PRep.IsSmooth π → π.IsIrreducible → GlobalTheory.PRep.IsSmooth τ → τ.IsIrreducible → (∃ v ∈ fixed π K, v ≠ 0) → ∀ T : V →ₗ[ℂ] W, (∀ v ∈ fixed π K, T v ∈ fixed τ K) → (∀ w ∈ fixed τ K, ∃ v ∈ fixed π K, T v = w) → (∀ v ∈ fixed π K, T v = 0 → v = 0) → (∀ e, IsHk K e → ∀ v ∈ fixed π K, T (hk π K e v) = hk τ K e (T v)) → Nonempty (π.Equiv τ) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeInj.hecke_determines | exact GlobalTheory.CompanionTheory.HeckeInj.hecke_determines | (intros; apply GlobalTheory.CompanionTheory.HeckeInj.hecke_determines <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

theorem _root_.GlobalTheory.T.multipliable_local_factors : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), (∀ v, v ∉ S → ∀ s : Fv F v, Valued.v s = 1 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) → ∀ β : F, β ≠ 0 → Multipliable fun v => g v (algebraMap F (Fv F v) β) := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.multipliable_localFactors | exact GlobalTheory.CompanionTheory.Mass.MeanV.multipliable_localFactors | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.multipliable_localFactors <;> assumption)
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SW.CharacterTrivial

theorem eq_one_of_isFundamentalDomain :
    ∀ (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
      [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁]
      (Γ₁ : Subgroup G₁) [Countable Γ₁] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (𝓕₁ : Set G₁),
      IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → ∀ δ : G₁ →* ℝ≥0, Measurable δ →
        (∀ γ ∈ Γ₁, δ γ = 1) → ∀ u, δ u = 1 := by
  intro G₁ _ _ _ _ _ _ _ _ Γ₁ _ μ₁ _ 𝓕₁ h𝓕₁ hfin δ hδ hγ
  obtain ⟨h0, hR, -⟩ :=
    GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain G₁ Γ₁ μ₁ 𝓕₁ h𝓕₁ hfin
  have hinv : ∀ u, δ u * δ u⁻¹ = 1 := fun u => by rw [← map_mul, mul_inv_cancel, map_one]
  have hpos : ∀ u, 0 < (δ u : ℝ) := by
    intro u
    have h : δ u ≠ 0 := left_ne_zero_of_mul_eq_one (hinv u)
    exact_mod_cast pos_iff_ne_zero.2 h
  have hδr : Measurable (fun u => (δ u : ℝ)) := measurable_coe_nnreal_real.comp hδ
  have hind : ∀ (A B : Set G₁) (x y : G₁), (x ∈ A ↔ y ∈ B) →
      A.indicator (1 : G₁ → ℝ≥0∞) x = B.indicator (1 : G₁ → ℝ≥0∞) y := by
    intro A B x y h
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (h.1 hx)]; rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun hy => hx (h.2 hy))]
  have hbig : ∀ u₀, 1 < δ u₀ → False := by
    intro u₀ ht
    obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = δ u₀ := ⟨_, rfl⟩
    have ht1 : 1 < t := by rw [htdef]; exact_mod_cast ht
    have ht0 : 0 < t := by linarith
    let C : ℤ → Set G₁ := fun n => (fun u => (δ u : ℝ)) ⁻¹' Set.Ico (t ^ n) (t ^ (n + 1))
    have hCm : ∀ n, MeasurableSet (C n) := fun n => hδr measurableSet_Ico
    have hmem : ∀ n u, u * u₀ ∈ C (n + 1) ↔ u ∈ C n := by
      intro n u
      have e : (δ (u * u₀) : ℝ) = δ u * t := by rw [map_mul, htdef]; push_cast; rfl
      simp only [C, Set.mem_preimage, Set.mem_Ico, e]
      rw [zpow_add_one₀ ht0.ne' n, zpow_add_one₀ ht0.ne' (n + 1),
        mul_le_mul_iff_of_pos_right ht0, mul_lt_mul_iff_of_pos_right ht0, zpow_add_one₀ ht0.ne' n]
    have hshift : ∀ n, (μ₁.restrict 𝓕₁) (C n) = (μ₁.restrict 𝓕₁) (C (n + 1)) := by
      intro n
      have hinvar : ∀ γ ∈ Γ₁, ∀ u, (C (n + 1)).indicator (1 : G₁ → ℝ≥0∞) (γ * u) =
          (C (n + 1)).indicator (1 : G₁ → ℝ≥0∞) u := by
        intro γ hg u
        have e : γ * u ∈ C (n + 1) ↔ u ∈ C (n + 1) := by
          simp only [C, Set.mem_preimage, map_mul, hγ γ hg, one_mul]
        exact hind _ _ _ _ e
      have e := GlobalTheory.CompanionTheory.SW.Averaging.setLIntegral_mul_right_eq μ₁ Γ₁ 𝓕₁ h𝓕₁
        ((C (n + 1)).indicator 1) hinvar u₀
      have e' : (fun u => (C (n + 1)).indicator (1 : G₁ → ℝ≥0∞) (u * u₀)) =
          (C n).indicator 1 := by
        funext u
        exact hind _ _ _ _ (hmem n u)
      rw [e', lintegral_indicator_one (hCm n), lintegral_indicator_one (hCm (n + 1))] at e
      exact e
    have hconst : ∀ n, (μ₁.restrict 𝓕₁) (C n) = (μ₁.restrict 𝓕₁) (C 0) := by
      intro n
      induction n using Int.induction_on with
      | zero => rfl
      | succ i ih => rw [← hshift]; exact ih
      | pred i ih =>
        rw [← ih, hshift (-(i : ℤ) - 1)]
        congr 2
        ring
    have hU : ⋃ n, C n = Set.univ := by
      refine Set.eq_univ_of_forall fun u => Set.mem_iUnion.2 ?_
      obtain ⟨n, hn⟩ := exists_mem_Ico_zpow (hpos u) ht1
      exact ⟨n, hn⟩
    have hdisj : Pairwise (Function.onFun Disjoint C) := by
      intro m n hmn
      refine Set.disjoint_left.2 fun u h₁ h₂ => hmn ?_
      have a : t ^ n < t ^ (m + 1) := lt_of_le_of_lt h₂.1 h₁.2
      have b : t ^ m < t ^ (n + 1) := lt_of_le_of_lt h₁.1 h₂.2
      have a' := (zpow_lt_zpow_iff_right₀ ht1).1 a
      have b' := (zpow_lt_zpow_iff_right₀ ht1).1 b
      omega
    have hsum : μ₁ 𝓕₁ = ∑' _ : ℤ, (μ₁.restrict 𝓕₁) (C 0) := by
      rw [← Measure.restrict_apply_univ 𝓕₁, ← hU, measure_iUnion hdisj hCm]
      exact tsum_congr hconst
    by_cases hz : (μ₁.restrict 𝓕₁) (C 0) = 0
    · rw [hz, tsum_zero] at hsum
      exact h0 hsum
    · rw [ENNReal.tsum_const_eq_top_of_ne_zero hz] at hsum
      exact hfin.ne hsum
  intro u
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine hbig u⁻¹ ?_
    by_contra hle
    have h1 : δ u * δ u⁻¹ < 1 * 1 :=
      mul_lt_mul'' hlt (lt_of_le_of_ne (not_lt.1 hle) ?_) zero_le zero_le
    · rw [hinv u, one_mul] at h1
      exact lt_irrefl _ h1
    · intro e
      have := hinv u
      rw [e, mul_one] at this
      exact hne this
  · exact hbig u hgt

end GlobalTheory.CompanionTheory.SW.CharacterTrivial
end

section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

theorem _root_.GlobalTheory.T.compact_open_subgroups_basis : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k), IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧ (K : Set (GL (Fin n) k)) ⊆ U := by
  first | exact @GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset | exact GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset | (intros; apply GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open MvPolynomial

theorem _root_.GlobalTheory.T.fraction_field_transcendence_basis_ext : ∀ (K : Type) [Field K] [CharZero K] (d : ℕ) (A : Type) [CommRing A] [IsDomain A] [Algebra K A] (t : Fin d → A), Function.Injective (MvPolynomial.aeval t : MvPolynomial (Fin d) K →ₐ[K] A) → (∀ a : A, ∃ f g : MvPolynomial (Fin d) K, IsUnit (MvPolynomial.aeval t g) ∧ a * MvPolynomial.aeval t g = MvPolynomial.aeval t f) → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [Module.Finite A B], Function.Injective (algebraMap A B) → ∀ (F L : Type) [Field F] [Field L] [Algebra A F] [IsFractionRing A F] [Algebra B L] [IsFractionRing B L] [Algebra F L] [Algebra A L] [IsScalarTower A F L] [IsScalarTower A B L] [Algebra K L] [IsScalarTower K B L] (D : Fin d → Derivation K L L), (∀ k j, D k (algebraMap A L (t j)) = if k = j then 1 else 0) → ∀ (m : ℕ) (κ : Fin m ↪ Fin d) (c : B) (b : Fin m → B), ∃ a : A, algebraMap A F a = Algebra.trace F L (algebraMap B L c * (Matrix.of fun k l => D (κ k) (algebraMap B L (b l))).det) := by
  first | exact @GlobalTheory.CompanionTheory.TraceJac.trace_minor_mem | exact GlobalTheory.CompanionTheory.TraceJac.trace_minor_mem | (intros; apply GlobalTheory.CompanionTheory.TraceJac.trace_minor_mem <;> assumption)
end
