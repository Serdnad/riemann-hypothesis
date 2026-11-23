module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle309
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetKernelSpanTwistedCharacter
public import Mathlib.RepresentationTheory.Intertwining
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle308
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle311
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle312
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
public import GroundTheory.GlobalFields.ComplexMultiplication.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle313
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.MirClosed

theorem isClosed_mirabolic :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ),
      IsClosed (Mir k n : Set (GL (Fin (n + 1)) k)) := by
  apply GlobalTheory.CompanionTheory.BZMirOnto.isClosed_Mir <;> assumption

end GlobalTheory.CompanionTheory.BZRes.MirClosed
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.quotient_map_induced_surjective_intertwiner : ∀ {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H : Subgroup G) (H' : Subgroup G') (ι : G' →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H' W')
    (q : W →ₗ[ℂ] W'), Continuous ι → IsSmooth σ → Function.Surjective q →
    (∀ x, x ∈ H' ↔ ι x ∈ H) →
    (∀ (h : H') (hh : ι h ∈ H) (w : W), q (σ ⟨ι h, hh⟩ w) = σ' h (q w)) →
    (∀ K' ∈ 𝓝 (1 : G'), ∃ K ∈ 𝓝 (1 : G), ∀ x : G', ∀ h ∈ H, ∀ κ ∈ K, ι x = h * κ →
      ∃ h' ∈ H', ∃ κ' ∈ K', x = h' * κ') →
    (∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) →
    ∀ F : cIndSpace H' σ', ∃ f : cIndSpace H σ, ∀ x, F.1.1.1 x = q (f.1.1.1 (ι x)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_restrict_eq | exact GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_restrict_eq | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_restrict_eq <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.quotient_map_intertwines_restriction : ∀ {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H : Subgroup G) (H' : Subgroup G') (ι : G' →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H' W')
    (q : W →ₗ[ℂ] W'), Continuous ι → (∀ x, x ∈ H' ↔ ι x ∈ H) →
    (∀ (h : H') (hh : ι h ∈ H) (w : W), q (σ ⟨ι h, hh⟩ w) = σ' h (q w)) →
    IsClosed {g : G | ∃ h ∈ H, ∃ x : G', g = h * ι x} →
    (∀ K' ∈ 𝓝 (1 : G'), ∃ K ∈ 𝓝 (1 : G), ∀ x : G', ∀ h ∈ H, ∀ κ ∈ K, ι x = h * κ →
      ∃ h' ∈ H', ∃ κ' ∈ K', x = h' * κ') →
    (∃ K' ∈ 𝓝 (1 : G'), IsCompact K') →
    ∀ f : cIndSpace H σ, ∃ F : cIndSpace H' σ', ∀ x, F.1.1.1 x = q (f.1.1.1 (ι x)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_restrict | exact GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_restrict | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_restrict <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.jacquet_kernel_span_twisted_character : ∀ {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H U : Subgroup G) (hUH : U ≤ H) (_ : U.Normal) (θ : U →* ℂˣ) (ι : G' →* G)
    (_ : ∀ (m : G') (n : U), ∃ h : ι m * (n : G) * (ι m)⁻¹ ∈ U, θ ⟨_, h⟩ = θ n)
    (σ : Representation ℂ H W) (q : W →ₗ[ℂ] W'), IsSmooth σ →
    (∀ w, q w = 0 ↔ w ∈ Submodule.span ℂ {y | ∃ (u : U) (v : W), y = σ ⟨u, hUH u.2⟩ v - (θ u : ℂ) • v}) →
    (∀ g : G, (∃ h ∈ H, ∃ x : G', g = h * ι x) ∨
      ∃ u : U, ∃ hx : g * (u : G) * g⁻¹ ∈ H, (∀ w, σ ⟨_, hx⟩ w = w) ∧ θ u ≠ 1) →
    (∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) →
    ∀ f : cIndSpace H σ, (∀ x, q (f.1.1.1 (ι x)) = 0) → f ∈ twKer (cInd H σ) U θ := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.Kernel.mem_twKer_of_restrict_zero | exact GlobalTheory.CompanionTheory.LeibPhi.Kernel.mem_twKer_of_restrict_zero | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.Kernel.mem_twKer_of_restrict_zero <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.compactInduction_congr_equiv : ∀ {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (H : Subgroup G) (σ : Representation ℂ H W) (σ' : Representation ℂ H W'),
    σ.Equiv σ' → Nonempty ((cInd H σ).Equiv (cInd H σ')) := by
  first | exact @GlobalTheory.CompanionTheory.CIndCongr.nonempty_equiv_cInd | exact GlobalTheory.CompanionTheory.CIndCongr.nonempty_equiv_cInd | (intros; apply GlobalTheory.CompanionTheory.CIndCongr.nonempty_equiv_cInd <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.Segments

theorem exists_coatom_ge_of_hasFiniteLength {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {P : Representation ℂ G V} (hfl : HasFiniteLength P) (S : Subrepresentation P) (hS : S ≠ ⊤) :
    ∃ C : Subrepresentation P, IsCoatom C ∧ S ≤ C := by
  obtain ⟨hN, -⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hfl
  have : IsCoatomic (Submodule (MonoidAlgebra ℂ G) P.asModule) := inferInstance
  have hc : IsCoatomic (Subrepresentation P) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := P)).isCoatomic_iff.2 this
  obtain h | ⟨C, hC, hle⟩ := hc.eq_top_or_exists_le_coatom S
  · exact absurd h hS
  · exact ⟨C, hC, hle⟩

theorem cosocle_quotient_of_quotient : ∀ {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (P : Representation ℂ G V)
    (Q : Representation ℂ G X) (hc : IsCosocle σ P) (hfl : HasFiniteLength P) (f : P.IntertwiningMap Q)
    (hf : Function.Surjective f) (hQ : Nontrivial X), ∃ g : Q.IntertwiningMap σ, Function.Surjective g := by
  intro G V W X _ _ _ _ _ _ _ σ P Q hc hfl f hf hQ
  obtain ⟨-, f0, hf0, hco⟩ := hc
  have hne : Representation.IntertwiningMap.ker P Q f ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    obtain ⟨v, rfl⟩ := hf x
    have hv : v ∈ (⊤ : Subrepresentation P) := trivial
    rw [← h] at hv
    exact hx hv
  obtain ⟨C, hC, hle⟩ := exists_coatom_ge_of_hasFiniteLength hfl _ hne
  have hk : ∀ v : V, f v = 0 → f0 v = 0 := by
    intro v hv
    have h1 : v ∈ Representation.IntertwiningMap.ker P Q f := hv
    have h2 : v ∈ C := hle h1
    rw [hco C hC] at h2
    exact h2
  let e := LinearMap.quotKerEquivOfSurjective f.toLinearMap hf
  let gl : X →ₗ[ℂ] W :=
    (LinearMap.ker f.toLinearMap).liftQ f0.toLinearMap (fun v hv => hk v hv) ∘ₗ e.symm.toLinearMap
  have hgl : ∀ v : V, gl (f v) = f0 v := by
    intro v
    have h1 : e.symm (f v) = Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [gl, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, Submodule.liftQ_apply]
    rfl
  refine ⟨⟨gl, fun h => ?_⟩, ?_⟩
  · refine LinearMap.ext fun x => ?_
    obtain ⟨v, rfl⟩ := hf x
    have h2 : Q h (f v) = f (P h v) := by
      have := congrArg (fun m => m v) (f.isIntertwining' h)
      exact this.symm
    have h3 : f0 (P h v) = σ h (f0 v) := congrArg (fun m => m v) (f0.isIntertwining' h)
    simp only [LinearMap.comp_apply]
    rw [h2, hgl, hgl, h3]
  · intro w
    obtain ⟨v, rfl⟩ := hf0 w
    exact ⟨f v, hgl v⟩

end GlobalTheory.CompanionTheory.Segments
end

section

open GlobalTheory.PRep GlobalTheory.SmGL

theorem _root_.GlobalTheory.T.subquotient_equiv_of_irreducible_image : ∀ (G : Type) [Group G] (V Y W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (R : Representation ℂ G Y) (σ : Representation ℂ G W), ρ.IsIrreducible → σ.IsIrreducible →
    (⨆ f : ρ.IntertwiningMap R, LinearMap.range f.toLinearMap = ⊤) → IsSubquotient σ R → Nonempty (σ.Equiv ρ) := by
  first | exact @GlobalTheory.CompanionTheory.IsoSub.equiv_of_isSubquotient | exact GlobalTheory.CompanionTheory.IsoSub.equiv_of_isSubquotient | (intros; apply GlobalTheory.CompanionTheory.IsoSub.equiv_of_isSubquotient <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.compactInduction_twist_equiv : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) (χ : G →* ℂˣ), IsOpen (χ.ker : Set G) →
    Nonempty ((twist (cInd H σ) χ).Equiv (cInd H (twist σ (χ.comp H.subtype)))) := by
  first | exact @GlobalTheory.CompanionTheory.TwCInd.nonempty_twist_cInd_equiv | exact GlobalTheory.CompanionTheory.TwCInd.nonempty_twist_cInd_equiv | (intros; apply GlobalTheory.CompanionTheory.TwCInd.nonempty_twist_cInd_equiv <;> assumption)
end

section

open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.ConjPointDict

theorem mapPoint_eq_pointMapRing : ∀ [DecidableEq ℂ] (X : WeierstrassCurve ℂ) (σ : ℂ →+* ℂ)
    (P : X.toAffine.Point), GlobalTheory.ConjPoint.mapPoint X σ P = GroundTheory.Global.pointMapRing σ X P := by
  intro _ X σ P
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨h', e⟩ := GroundTheory.Global.pointMapRing_some σ X h
    rw [e]
    rfl

end GlobalTheory.CompanionTheory.ConjPointDict
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg Matrix

namespace GlobalTheory.CompanionTheory.SegNu

theorem exists_ne_zero_of_irr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hi : π.IsIrreducible) : ∃ v : V, v ≠ 0 := by
  by_contra h
  push_neg at h
  haveI := hi
  refine (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤) (Subrepresentation.toSubmodule_injective ?_)
  show (⊥ : Submodule ℂ V) = ⊤
  ext v
  simp [h v]

theorem eq_smul_of_eigenvector {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hi : π.IsIrreducible) {z : G} (hz : ∀ g, z * g = g * z) {c : ℂ} {w : V}
    (hw : w ≠ 0) (hc : π z w = c • w) (v : V) : π z v = c • v := by
  haveI := hi
  let E : Subrepresentation π :=
    { toSubmodule := LinearMap.ker (π z - c • (1 : Module.End ℂ V))
      apply_mem_toSubmodule := fun g v hv => by
        have hv' : π z v = c • v := by
          simpa [sub_eq_zero] using hv
        have h1 : π z (π g v) = π g (π z v) := by
          rw [← Module.End.mul_apply, ← map_mul, hz, map_mul, Module.End.mul_apply]
        simp [sub_eq_zero, h1, hv'] }
  have hE : E ≠ ⊥ := fun h => hw (by
    have h1 : w ∈ E.toSubmodule := by
      show w ∈ LinearMap.ker (π z - c • (1 : Module.End ℂ V))
      simp [sub_eq_zero, hc]
    rw [h] at h1
    exact (Submodule.mem_bot ℂ).1 h1)
  have hT : E = ⊤ := (eq_bot_or_eq_top E).resolve_left hE
  have h2 : v ∈ E.toSubmodule := by
    rw [hT]
    exact Submodule.mem_top
  have h3 : v ∈ LinearMap.ker (π z - c • (1 : Module.End ℂ V)) := h2
  simpa [sub_eq_zero] using h3

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_scalar {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) k) V}
    (ha : IsAdmissible π) (hi : π.IsIrreducible) {z : GL (Fin n) k} (hz : ∀ g, z * g = g * z) :
    ∃ ω : ℂ, ∀ v, π z v = ω • v := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_irr hi
  let S : Subgroup (GL (Fin n) k) :=
    { carrier := {g | π g v = v}
      mul_mem' := fun {a b} ha hb => by
        have ha' : π a v = v := ha
        have hb' : π b v = v := hb
        show π (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      one_mem' := by
        show π 1 v = v
        simp
      inv_mem' := fun {a} ha => by
        have ha' : π a v = v := ha
        show π a⁻¹ v = v
        conv_lhs => rw [← ha']
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hSo : IsOpen (S : Set (GL (Fin n) k)) := ha.1 v
  let K : Subgroup (GL (Fin n) k) := S ⊓ KO k (Fin n)
  have hKo : IsOpen (K : Set (GL (Fin n) k)) := hSo.inter SplitFlip.isOpen_KO
  have hKc : IsCompact (K : Set (GL (Fin n) k)) :=
    SplitFlip.isCompact_KO.of_isClosed_subset (K.isClosed_of_isOpen hKo) Set.inter_subset_right
  haveI : FiniteDimensional ℂ (fixed π K) := ha.2 K hKo hKc
  have hvK : v ∈ fixed π K := fun h => by
    have h' : π (h : GL (Fin n) k) v = v := h.2.1
    simpa using h'
  haveI : Nontrivial (fixed π K) := ⟨⟨⟨v, hvK⟩, 0, fun e => hv (congrArg Subtype.val e)⟩⟩
  have hst : ∀ u ∈ fixed π K, π z u ∈ fixed π K := fun u hu h => by
    have hu' := hu h
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at hu' ⊢
    rw [← Module.End.mul_apply, ← map_mul, ← hz, map_mul, Module.End.mul_apply, hu']
  let T : Module.End ℂ (fixed π K) := (π z).restrict hst
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have h1 : π z (w : V) = c • (w : V) := congrArg Subtype.val hw.apply_eq_smul
  have h2 : (w : V) ≠ 0 := fun e => hw.2 (Subtype.ext e)
  exact ⟨c, eq_smul_of_eigenvector hi hz h2 h1⟩

theorem eq_zero_of_nu_eq (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) (hd : 0 < x.1) {s : ℝ}
    (hs : x.nu (s : ℂ) = x) : s = 0 := by
  have h1 := IrrGL.tw_of x.rep x.2.rep.smooth x.2.rep.irr (absPow k (s : ℂ)) (isSmoothChar_absPow _)
  rw [IrrGL.of_rep] at h1
  obtain ⟨φ⟩ := IrrGL.of_eq_of.1 (h1.symm.trans (hs.trans (IrrGL.of_rep x).symm))
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  let z : GL (Fin x.1) k := GeneralLinearGroup.scalar (Fin x.1) ϖ
  have hz : ∀ g, z * g = g * z := fun g => by
    ext i j
    simp [z, GeneralLinearGroup.scalar, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  have hdet : GeneralLinearGroup.det z = ϖ ^ x.1 := by
    ext
    simp [z, GeneralLinearGroup.scalar]
  obtain ⟨ω, hω⟩ := exists_scalar (hA k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr) x.2.rep.irr hz
  obtain ⟨v, hv⟩ := exists_ne_zero_of_irr x.2.rep.irr
  have hω0 : ω ≠ 0 := fun e => hv (by
    have h2 : x.rep z⁻¹ (x.rep z v) = v := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [hω, e, zero_smul, map_zero] at h2
    exact h2.symm)
  have h3 := LinearMap.congr_fun (φ.isIntertwining' z) v
  have hLv : φ.toLinearEquiv v ≠ 0 := fun e => hv (φ.toLinearEquiv.map_eq_zero_iff.1 e)
  have h4 : φ.toLinearEquiv (((absPow k (s : ℂ) (ϖ ^ x.1) : ℂˣ) : ℂ) • x.rep z v) = x.rep z (φ.toLinearEquiv v) := by
    have h5 : φ.toLinearEquiv ((twist x.rep (detChar _ (absPow k (s : ℂ)))) z v) = x.rep z (φ.toLinearEquiv v) := h3
    rwa [twist_apply, detChar_apply, hdet] at h5
  rw [hω, hω, map_smul, map_smul, smul_smul] at h4
  have h6 : ((absPow k (s : ℂ) (ϖ ^ x.1) : ℂˣ) : ℂ) * ω = ω := smul_left_injective ℂ hLv h4
  have h7 : ((absPow k (s : ℂ) (ϖ ^ x.1) : ℂˣ) : ℂ) = 1 := mul_right_cancel₀ hω0 (h6.trans (one_mul ω).symm)
  have h8 : ((absPow k (s : ℂ) ϖ : ℂˣ) : ℂ) ^ x.1 = 1 := by
    rw [← h7, map_pow, Units.val_pow_eq_pow_val]
  rw [val_absPow_ofReal] at h8
  have h9 : (nabs k ϖ ^ s) ^ x.1 = 1 := by exact_mod_cast h8
  have hpos : 0 < nabs k ϖ := nabs_pos' k ϖ
  have h10 : nabs k ϖ ^ s = 1 := (pow_eq_one_iff_of_nonneg (Real.rpow_nonneg hpos.le s) hd.ne').1 h9
  have hne : nabs k ϖ ≠ 1 := fun e => ValuativeRel.uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)
  have h11 := congrArg Real.log h10
  rw [Real.log_rpow hpos, Real.log_one] at h11
  exact (mul_eq_zero.1 h11).resolve_right (Real.log_ne_zero_of_pos_of_ne_one hpos hne)

theorem nu_natCast_inj : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) (hx : x.IsCusp) (a b : ℕ)
    (h : x.nu (a : ℂ) = x.nu (b : ℂ)), a = b := by
  intro k _ _ _ _ hA x hx a b h
  have h1 : x.nu (((a : ℝ) - (b : ℝ) : ℝ) : ℂ) = x := by
    have h2 := congrArg (fun y => IrrGL.nu y (-(b : ℂ))) h
    simp only [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at h2
    rw [← h2]
    congr 1
    push_cast
    ring
  have h3 := eq_zero_of_nu_eq hA x hx.1 h1
  exact_mod_cast sub_eq_zero.1 h3

end GlobalTheory.CompanionTheory.SegNu
end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegTerm

theorem term_injective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) : Function.Injective Δ.term :=
  Segment.term_injective Δ

end GlobalTheory.CompanionTheory.SegTerm
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

theorem exists_entry_nhds {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] (m : ℕ)
    {t : Set (Matrix (Fin m) (Fin m) k)} (ht : t ∈ 𝓝 (1 : Matrix (Fin m) (Fin m) k)) :
    ∃ U ∈ 𝓝 (0 : k), ∀ A : Matrix (Fin m) (Fin m) k,
      (∀ a b, A a b - (1 : Matrix (Fin m) (Fin m) k) a b ∈ U) → A ∈ t := by
  have hc : Continuous fun B : Matrix (Fin m) (Fin m) k => 1 + B := continuous_const.add continuous_id
  have hs : (fun B : Matrix (Fin m) (Fin m) k => 1 + B) ⁻¹' t ∈ 𝓝 (0 : Matrix (Fin m) (Fin m) k) := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa using ht
  have e : 𝓝 (0 : Fin m → Fin m → k) = Filter.pi fun a => 𝓝 ((0 : Fin m → Fin m → k) a) := nhds_pi
  have hs' : ((fun B : Matrix (Fin m) (Fin m) k => 1 + B) ⁻¹' t : Set (Fin m → Fin m → k)) ∈
      Filter.pi fun a => 𝓝 ((0 : Fin m → Fin m → k) a) := by
    rw [← e]
    exact hs
  obtain ⟨I, -, t₁, ht₁, hsub⟩ := Filter.mem_pi.1 hs'
  have h2 : ∀ a, ∃ t₂ : Fin m → Set k, (∀ b, t₂ b ∈ 𝓝 (0 : k)) ∧ Set.univ.pi t₂ ⊆ t₁ a := by
    intro a
    have e' : 𝓝 (0 : Fin m → k) = Filter.pi fun b => 𝓝 ((0 : Fin m → k) b) := nhds_pi
    have h : t₁ a ∈ Filter.pi fun b => 𝓝 ((0 : Fin m → k) b) := by
      rw [← e']
      exact ht₁ a
    obtain ⟨J, -, t₂, ht₂, hJ⟩ := Filter.mem_pi.1 h
    exact ⟨t₂, ht₂, fun x hx => hJ fun b _ => hx b (Set.mem_univ b)⟩
  choose t₂ ht₂ hsub₂ using h2
  refine ⟨⋂ a, ⋂ b, t₂ a b, Filter.iInter_mem.2 fun a => Filter.iInter_mem.2 fun b => ht₂ a b,
    fun A hA => ?_⟩
  have hmem : A - 1 ∈ (fun B : Matrix (Fin m) (Fin m) k => 1 + B) ⁻¹' t :=
    hsub fun a _ => hsub₂ a fun b _ => Set.mem_iInter.1 (Set.mem_iInter.1 (hA a b) a) b
  simpa using hmem

theorem congM_subset_nhds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (O : Set (Mir k n)) (hO : O ∈ 𝓝 (1 : Mir k n)) :
    ∃ s₀ : kˣ, ∀ (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1),
      ValuativeRel.valuation k (s : k) ≤ ValuativeRel.valuation k (s₀ : k) →
        (GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n : Set (Mir k n)) ⊆ O := by
  obtain ⟨u, hu, huO⟩ :=
    (mem_nhds_subtype ((GlobalTheory.BZMir.Mir k n : Set (GL (Fin (n + 1)) k))) 1 O).1 hO
  have hu1 : u ∈ 𝓝 (1 : GL (Fin (n + 1)) k) := by simpa using hu
  rw [Units.isEmbedding_embedProduct.toIsInducing.nhds_eq_comap, Filter.mem_comap] at hu1
  obtain ⟨w, hw, hwu⟩ := hu1
  rw [Units.embedProduct_apply, nhds_prod_eq, Filter.mem_prod_iff] at hw
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := hw
  have ht₁' : t₁ ∈ 𝓝 (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by simpa using ht₁
  have ht₂' : MulOpposite.op ⁻¹' t₂ ∈ 𝓝 (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    have h := MulOpposite.continuous_op.continuousAt.preimage_mem_nhds ht₂
    simpa using h
  obtain ⟨U₁, hU₁, h₁⟩ := GlobalTheory.CompanionTheory.BZPhiPG.Onto.exists_entry_nhds (n + 1) ht₁'
  obtain ⟨U₂, hU₂, h₂⟩ := GlobalTheory.CompanionTheory.BZPhiPG.Onto.exists_entry_nhds (n + 1) ht₂'
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.SplitWeil.exists_cball_subset (Filter.inter_mem hU₁ hU₂)
  refine ⟨s₀, fun s hs hss₀ g hg => ?_⟩
  have hball : ∀ x : k, x ∈ GlobalTheory.SplitWeil.cball s → x ∈ GlobalTheory.SplitWeil.cball s₀ := by
    intro x hx
    simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq] at hx ⊢
    exact le_trans hx hss₀
  refine huO (hwu (hsub (Set.mem_prod.2 ⟨?_, ?_⟩)))
  · have hg' : GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
      hg.1
    show ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∈ t₁
    exact h₁ _ fun a b => (hs₀ (hball _ (hg' a b))).1
  · have hg' : GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s
        (((g : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
      hg.2
    show MulOpposite.op (((g : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∈ t₂
    exact h₂ _ fun a b => (hs₀ (hball _ (hg' a b))).2

end GlobalTheory.CompanionTheory.BZPhiPG.Onto
end
