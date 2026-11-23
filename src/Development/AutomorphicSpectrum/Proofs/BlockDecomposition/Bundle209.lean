module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import GroundTheory.AutomorphicForms.SmoothRep
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InductionReindexEquiv
public import GroundTheory.AutomorphicForms.InductionParabolic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleDeterminantTwist
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle200
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle194
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle201
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.MoyPrasadJacquetIsoTrivial
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
import Std.Tactic.BVDecide.Normalize.Prop
public import GroundTheory.AutomorphicForms.FiniteBruhat
public import GroundTheory.AutomorphicForms.GeometricLemmaJacquetCell
public import GroundTheory.AutomorphicForms.GeometricLemmaNormal
import GroundTheory.AutomorphicForms.Bundle002
import GroundTheory.AutomorphicForms.Iwasawa
import Mathlib.GroupTheory.DoubleCoset
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.SmoothBridge

theorem isSmooth_comp {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (ψ : H →* G) (hψ : Continuous ψ) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (hρ : GlobalTheory.PRep.IsSmooth ρ) : GroundTheory.Automorphic.IsSmooth (ρ.comp ψ) := by
  intro v
  have h := (hρ v).preimage hψ
  exact h

end GlobalTheory.CompanionTheory.SmoothBridge
end

section

noncomputable section

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

namespace GlobalTheory.CompanionTheory.JacquetCentral

theorem exists_fixed_mk_eq_of_commute : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V), IsAdmissible π → ∀ (I N : Subgroup G), IsOpen (I : Set G) → IsCompact (I : Set G) →
    ∀ {M : Type} [Group M] (s : M →* G) (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G)) (M₀ : Subgroup M),
    (∀ d ∈ M₀, s d ∈ I) → ∀ (C : Set G), (∀ g ∈ I, ∃ d ∈ M₀, ∃ x ∈ N, ∃ c ∈ C, g = s d * x * c) →
    (∀ U ∈ 𝓝 (1 : G), ∃ t : M, (∀ d ∈ M₀, t * d = d * t) ∧ ∀ c ∈ C, (s t)⁻¹ * c * s t ∈ U) →
    ∀ y : Jacquet π N, y ∈ fixed (jacquet π N s hs) M₀ → ∃ v ∈ fixed π I, (twKer π N 1).mkQ v = y := by
  intro G V _ _ _ _ _ π hπ I N hIo hIc M _ s hs M₀ hsI C hfac hcon y hy
  obtain ⟨hsm, hfd⟩ := hπ
  have hj : ∀ (m : M) (z : V),
      jacquet π N s hs m ((twKer π N 1).mkQ z) = (twKer π N 1).mkQ (π (s m) z) :=
    fun m z => rfl
  have hfixI : ∀ v ∈ fixed π I, ∀ g ∈ I, π g v = v := by
    intro v hv g hg
    have h := hv ⟨g, hg⟩
    simpa using h
  have hy' : ∀ d ∈ M₀, jacquet π N s hs d y = y := by
    intro d hd
    have h := hy ⟨d, hd⟩
    simpa using h
  have hmul : ∀ (a b : G) (z : V), π a (π b z) = π (a * b) z := fun a b z =>
    (LinearMap.congr_fun (map_mul π a b) z).symm
  have hconj : ∀ (g h : G) (z : V), π g (π h z) = π h (π (h⁻¹ * g * h) z) := by
    intro g h z
    rw [hmul, hmul, show h * (h⁻¹ * g * h) = g * h by simp [mul_assoc]]
  have hN : ∀ x ∈ N, ∀ z : V, (twKer π N 1).mkQ (π x z) = (twKer π N 1).mkQ z := by
    intro x hx z
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact Submodule.subset_span ⟨⟨x, hx⟩, z, by simp⟩
  have hstep : ∀ u : V, (∀ c ∈ C, π c u = u) →
      (∀ d ∈ M₀, (twKer π N 1).mkQ (π (s d) u) = (twKer π N 1).mkQ u) →
      ∃ v ∈ fixed π I, (twKer π N 1).mkQ v = (twKer π N 1).mkQ u := by
    intro u hu hd
    refine GlobalTheory.SmGL.IwahoriOnto.exists_fixed_map_eq hsm hIc (twKer π N 1).mkQ u ?_
    intro g hg
    obtain ⟨d, hdM, x, hx, c, hc, rfl⟩ := hfac g hg
    rw [← hmul, ← hmul, hu c hc, ← hj, hN x hx u, hj]
    exact hd d hdM
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (twKer π N 1) y
  have hU : {g : G | π g w = w} ∩ (I : Set G) ∈ 𝓝 (1 : G) :=
    Filter.inter_mem ((hsm w).mem_nhds (by simp)) (hIo.mem_nhds I.one_mem)
  obtain ⟨t, htc, htC⟩ := hcon _ hU
  have hcomm : ∀ d ∈ M₀, ∀ z : V, π (s d) (π (s t) z) = π (s t) (π (s d) z) := by
    intro d hd z
    rw [hmul, hmul, ← map_mul, ← map_mul, htc d hd]
  have hC : ∀ z : V, (∀ c ∈ C, π ((s t)⁻¹ * c * s t) z = z) →
      ∀ c ∈ C, π c (π (s t) z) = π (s t) z := by
    intro z hz c hc
    rw [hconj c (s t) z, hz c hc]
  set W : Submodule ℂ (V ⧸ twKer π N 1) := (fixed π I).map (twKer π N 1).mkQ with hW
  haveI : FiniteDimensional ℂ (fixed π I) := hfd I hIo hIc
  have hWfd : FiniteDimensional ℂ W := by
    rw [hW]
    infer_instance
  have hstepW : ∀ u : V, (∀ c ∈ C, π c u = u) →
      (∀ d ∈ M₀, (twKer π N 1).mkQ (π (s d) u) = (twKer π N 1).mkQ u) →
      (twKer π N 1).mkQ u ∈ W := by
    intro u hu hd
    obtain ⟨v, hv, he⟩ := hstep u hu hd
    exact Submodule.mem_map.2 ⟨v, hv, he⟩
  have hAW : ∀ z ∈ W, jacquet π N s hs t z ∈ W := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hz
    rw [hj]
    apply hstepW
    · exact hC v (fun c hc => hfixI v hv _ (htC c hc).2)
    · intro d hd
      rw [hcomm d hd, hfixI v hv (s d) (hsI d hd)]
  have hAy : jacquet π N s hs t ((twKer π N 1).mkQ w) ∈ W := by
    rw [hj]
    apply hstepW
    · exact hC w (fun c hc => (htC c hc).1)
    · intro d hd
      rw [hcomm d hd, ← hj t (π (s d) w), ← hj t w, ← hj d w, hy' d hd]
  have hinv : ∀ z : Jacquet π N, jacquet π N s hs t⁻¹ (jacquet π N s hs t z) = z := by
    intro z
    have h1 := LinearMap.congr_fun (map_mul (jacquet π N s hs) t⁻¹ t) z
    rw [inv_mul_cancel, map_one] at h1
    exact h1.symm
  let A : W →ₗ[ℂ] W := LinearMap.restrict (jacquet π N s hs t) hAW
  have hAinj : Function.Injective A := by
    intro a b hab
    have h : jacquet π N s hs t (a : V ⧸ twKer π N 1) = jacquet π N s hs t (b : V ⧸ twKer π N 1) :=
      congrArg Subtype.val hab
    apply Subtype.ext
    rw [← hinv (a : V ⧸ twKer π N 1), h, hinv]
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.1 hAinj) ⟨_, hAy⟩
  have hz' : jacquet π N s hs t (z : V ⧸ twKer π N 1) = jacquet π N s hs t ((twKer π N 1).mkQ w) :=
    congrArg Subtype.val hz
  have hzw : (z : V ⧸ twKer π N 1) = (twKer π N 1).mkQ w := by
    rw [← hinv (z : V ⧸ twKer π N 1), hz', hinv]
  have hwW : (twKer π N 1).mkQ w ∈ W := by
    rw [← hzw]
    exact z.2
  obtain ⟨v, hv, hvz⟩ := Submodule.mem_map.1 hwW
  exact ⟨v, hv, hvz⟩

end GlobalTheory.CompanionTheory.JacquetCentral
end
end

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.induction_reindex_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' n : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] [Fintype n] [DecidableEq n] {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ n) (e' : (Σ j, m' j) ≃ n) {N : ℕ} (ι : n ≃ Fin N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W), Nonempty ((jac e' (parInd e ρ)).Equiv (jac (e'.trans ι) (parInd (e.trans ι) ρ))) := by
  first | exact @GlobalTheory.CompanionTheory.ParIndReindex.jac_parInd_reindex | exact GlobalTheory.CompanionTheory.ParIndReindex.jac_parInd_reindex | (intros; apply GlobalTheory.CompanionTheory.ParIndReindex.jac_parInd_reindex <;> assumption)
end

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.jac_equiv_jacquetRep_comp_levi_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] {N : ℕ} (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ), (∀ x y, γ x < γ y ↔ blk e' x < blk e' y) → ∀ (φ' : Levi k m' ≃* levi k N γ), (∀ g, ((φ' g : levi k N γ) : GL (Fin N) k) = leviEmb k e' g) → ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), Nonempty ((jac e' π).Equiv ((jacquetRep k N γ π).comp φ'.toMonoidHom)) := by
  first | exact @GlobalTheory.CompanionTheory.JacBridge.jac_equiv_jacquetRep | exact GlobalTheory.CompanionTheory.JacBridge.jac_equiv_jacquetRep | (intros; apply GlobalTheory.CompanionTheory.JacBridge.jac_equiv_jacquetRep <;> assumption)
end

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.FiltTransfer

theorem subQuot_of_filtration : ∀ {G H : Type} [Group G] [Group H] (ψ : H →* G) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (ρ : Representation ℂ H V) (ρ' : Representation ℂ G V'), ρ.Equiv (ρ'.comp ψ) → ∀ (K : ℕ) (X : Fin K → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (τ : ∀ j, Representation ℂ G (X j)) (Vf : ℕ → Submodule ℂ V'), Vf 0 = ⊥ → Vf K = ⊤ → Monotone Vf → ∀ (hV : ∀ i (g : G), Vf i ≤ (Vf i).comap (ρ' g)), (∀ j : Fin K, ∃ Ψ : Representation.IntertwiningMap (ρ'.subrepresentation (Vf (j + 1)) (hV (j + 1))) (τ j), Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ (x : V') ∈ Vf j) → ∃ S : Fin (K + 1) → Subrepresentation ρ, Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last K) = ⊤ ∧ ∀ t : Fin K, Nonempty ((GlobalTheory.SmGL.subQuot (S t.succ) (S t.castSucc)).Equiv ((τ t).comp ψ)) := by
  intro G H _ _ ψ V V' _ _ _ _ ρ ρ' e K X _ _ τ Vf h0 hK hm hV hΨ
  have he : ∀ (h : H) (v : V), e (ρ h v) = ρ' (ψ h) (e v) := fun h v =>
    e.toIntertwiningMap.isIntertwining _ _ h v
  let S : ℕ → Subrepresentation ρ := fun i =>
    ⟨(Vf i).comap e.toLinearMap, fun h v hv => by
      have hv' : e v ∈ Vf i := hv
      show e (ρ h v) ∈ Vf i
      rw [he]
      exact hV i (ψ h) hv'⟩
  have memS : ∀ (i : ℕ) (v : V), v ∈ (S i).toSubmodule ↔ e v ∈ Vf i := fun _ _ => Iff.rfl
  refine ⟨fun t => S t, ?_, ?_, ?_, ?_⟩
  · intro a b hab v hv
    exact hm (Fin.le_def.1 hab) hv
  · apply Subrepresentation.toSubmodule_injective
    ext v
    show e v ∈ Vf 0 ↔ v = 0
    rw [h0]
    simp
  · apply Subrepresentation.toSubmodule_injective
    ext v
    show e v ∈ Vf K ↔ True
    rw [hK]
    simp
  · intro t
    obtain ⟨Ψ, hs, hk⟩ := hΨ t
    let f : (S (t + 1)).toSubmodule →ₗ[ℂ] X t :=
      Ψ.toLinearMap ∘ₗ
        (e.toLinearMap.restrict (p := (S (t + 1)).toSubmodule) (q := Vf (t + 1)) fun _ hv => hv)
    have hf : ∀ x, f x = Ψ ⟨e x, x.2⟩ := fun _ => rfl
    have hsurj : Function.Surjective f := by
      intro y
      obtain ⟨w, rfl⟩ := hs y
      refine ⟨⟨e.symm w, ?_⟩, ?_⟩
      · show e (e.symm w) ∈ Vf (t + 1)
        simp
      · rw [hf]
        congr 1
        apply Subtype.ext
        simp
    have hker : (S t).toSubmodule.comap (S (t + 1)).toSubmodule.subtype = LinearMap.ker f := by
      ext x
      rw [LinearMap.mem_ker, hf, hk]
      rfl
    let E := (Submodule.quotEquivOfEq _ _ hker).trans (f.quotKerEquivOfSurjective hsurj)
    refine ⟨Representation.Equiv.mk E ?_⟩
    intro g
    have hE : ∀ x, E (Submodule.Quotient.mk x) = f x := fun x => rfl
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hstep : f ⟨ρ g x, (S (t + 1)).apply_mem_toSubmodule g x.2⟩ =
        τ t (ψ g) (f x) := by
      rw [hf, hf, ← Ψ.isIntertwining _ _ (ψ g)]
      congr 1
      exact Subtype.ext (he g x)
    exact hstep

end GlobalTheory.CompanionTheory.FiltTransfer
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.MoyPrasad

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.IwahoriInj GlobalTheory.DepthZeroJac ValuativeRel Matrix _root_.Topology

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isEmbedding_val_GL (n : ℕ) :
    IsEmbedding (Units.val : GL (Fin n) k → Matrix (Fin n) (Fin n) k) := by
  refine Units.isEmbedding_val_mk' (f := fun A => A⁻¹) (fun A hA => ?_) fun u => by simp
  have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
  exact (continuousAt_matrix_inv _
    (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hd)).continuousWithinAt

theorem exists_entry_nhds {n : ℕ} {V : Set (Matrix (Fin n) (Fin n) k)}
    (hV : V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) k)) :
    ∃ W ∈ 𝓝 (0 : k), ∀ A : Matrix (Fin n) (Fin n) k, (∀ i j, (A - 1) i j ∈ W) → A ∈ V := by
  have hS : (fun A : Matrix (Fin n) (Fin n) k => A + 1) ⁻¹' V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) k) :=
    (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds (by simpa using hV)
  have e : 𝓝 (0 : Matrix (Fin n) (Fin n) k) =
      Filter.pi fun _ : Fin n => Filter.pi fun _ : Fin n => 𝓝 (0 : k) := by
    show 𝓝 (0 : Fin n → Fin n → k) = _
    rw [nhds_pi]
    congr 1
    funext i
    rw [nhds_pi]
    rfl
  rw [e] at hS
  obtain ⟨I, t, ht, hsub⟩ := Filter.mem_pi'.1 hS
  have ht' : ∀ i, ∃ (I' : Finset (Fin n)) (t' : Fin n → Set k), (∀ j, t' j ∈ 𝓝 (0 : k)) ∧
      (I' : Set (Fin n)).pi t' ⊆ t i := fun i => Filter.mem_pi'.1 (ht i)
  choose I' t' h1 h2 using ht'
  refine ⟨⋂ i, ⋂ j, t' i j, Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => h1 i j,
    fun A hA => ?_⟩
  have h3 : A - 1 ∈ (fun A : Matrix (Fin n) (Fin n) k => A + 1) ⁻¹' V :=
    hsub fun i _ => h2 i fun j _ => by
      have := hA i j
      simp only [Set.mem_iInter] at this
      exact this i j
  simpa using h3

variable {s : ℕ} {d : Fin s → ℕ}

def blockScalar {c : k} (hc : c ≠ 0) (C : Fin s → ℕ) : Levi k (fun a => Fin (d a)) := fun a =>
  ⟨(c ^ C a) • (1 : Matrix (Fin (d a)) (Fin (d a)) k), (c ^ C a)⁻¹ • (1 : Matrix (Fin (d a)) (Fin (d a)) k),
    by rw [smul_mul_smul_comm, mul_inv_cancel₀ (pow_ne_zero _ hc), one_smul, one_mul],
    by rw [smul_mul_smul_comm, inv_mul_cancel₀ (pow_ne_zero _ hc), one_smul, one_mul]⟩

theorem blockScalar_central {c : k} (hc : c ≠ 0) (C : Fin s → ℕ) (m : Levi k (fun a => Fin (d a))) :
    blockScalar hc C * m = m * blockScalar hc C := by
  funext a
  refine Units.ext ?_
  show ((c ^ C a) • (1 : Matrix (Fin (d a)) (Fin (d a)) k)) * (m a).val =
    (m a).val * ((c ^ C a) • (1 : Matrix (Fin (d a)) (Fin (d a)) k))
  simp

theorem leviEmb_blockScalar {n : ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {c : k} (hc : c ≠ 0)
    (C : Fin s → ℕ) : leviEmb k e (blockScalar hc C) = dia e hc C := by
  refine Units.ext ?_
  rw [dia_val]
  ext i j
  obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
  by_cases h : a = b
  · subst h
    rw [leviEmb_apply_same]
    show ((c ^ C a) • (1 : Matrix (Fin (d a)) (Fin (d a)) k)) i' j' = _
    by_cases h2 : i' = j'
    · subst h2
      simp
    · rw [Matrix.smul_apply, one_apply_ne h2, smul_zero, diagonal_apply_ne]
      simpa using h2
  · rw [leviEmb_apply_ne k e _ h, diagonal_apply_ne]
    exact fun h' => h (congrArg Sigma.fst (e.injective h'))

theorem valuation_conj_le {c x : k} (hc : c ≠ 0) (hv : valuation k c ≤ 1) (hx : valuation k x ≤ 1)
    {A B N : ℕ} (h : A + N ≤ B) : valuation k ((c ^ A)⁻¹ * x * c ^ B) ≤ valuation k c ^ N := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  have e1 : (c ^ A)⁻¹ * x * c ^ (A + N + r) = c ^ N * (x * c ^ r) := by
    rw [pow_add, pow_add]
    field_simp
  rw [e1, map_mul, map_mul, map_pow, map_pow]
  exact mul_le_of_le_one_right' (mul_le_one' hx (pow_le_one' hv r))

theorem expo_gap {s : ℕ} (N : ℕ) {a b : Fin s} (h : b < a) : expo s N a + N ≤ expo s N b := by
  have h1 : (b : ℕ) < a := h
  have h2 : (a : ℕ) < s := a.2
  simp only [expo]
  calc (N + 1) * (s - 1 - (a : ℕ)) + N ≤ (N + 1) * (s - 1 - (a : ℕ)) + (N + 1) := by omega
    _ = (N + 1) * (s - 1 - (a : ℕ) + 1) := by ring
    _ ≤ (N + 1) * (s - 1 - (b : ℕ)) := Nat.mul_le_mul_left _ (by omega)

end GlobalTheory.CompanionTheory.MoyPrasad
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

theorem _root_.GlobalTheory.T.galois_character_artin_compat : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω) (χ : HChar E) (n : (E →+* ℂ) → ℤ)
    (μ : G E Ω →* (Qbar l)ˣ), IsLAdicOf art ι χ n μ → ∀ (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ)
    (σ : G E Ω), art (localIdele E w x) = toAb E Ω σ →
    ((μ σ : (Qbar l)ˣ) : Qbar l) = ι.symm (((χ.1 (localIdele E w x) : ℂˣ) : ℂ)) * locPow ι n w (x : w.adicCompletion E) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeLocal.isLAdicOf_localIdele | exact GlobalTheory.CompanionTheory.HeckeLocal.isLAdicOf_localIdele | (intros; apply GlobalTheory.CompanionTheory.HeckeLocal.isLAdicOf_localIdele <;> assumption)
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

theorem _root_.GlobalTheory.T.galois_open_subgroup_local_units : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (U : Subgroup (w.adicCompletion E)ˣ), IsOpen (U : Set (w.adicCompletion E)ˣ) → (∀ x ∈ U, IsUnitAt w x) →
    ∃ V : Subgroup (G E Ω), IsOpen (V : Set (G E Ω)) ∧
      ∀ σ ∈ V, σ ∈ Ine (F := E) A → ∃ x ∈ U, art (localIdele E w x) = toAb E Ω σ := by
  first | exact @GlobalTheory.CompanionTheory.InertOpen.exists_openSubgroup_ine_art_units | exact GlobalTheory.CompanionTheory.InertOpen.exists_openSubgroup_ine_art_units | (intros; apply GlobalTheory.CompanionTheory.InertOpen.exists_openSubgroup_ine_art_units <;> assumption)
end
end

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.SizeCells

theorem exists_perm_cell_sizes : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (b : SizeMatrix m m'), ∃ w : Equiv.Perm (Fin N), ∀ i j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = b.1 i j := by
  intro α _ _ N m _ _ β' _ _ m' _ _ e e' b
  obtain ⟨f⟩ := b.nonempty_rows
  obtain ⟨g⟩ := b.nonempty_cols
  let A : (Σ i, Σ j, Fin (b.1 i j)) ≃ Fin N := (Equiv.sigmaCongrRight f).trans e
  let B : (Σ j, Σ i, Fin (b.1 i j)) ≃ Fin N := (Equiv.sigmaCongrRight g).trans e'
  let S : (Σ i, Σ j, Fin (b.1 i j)) ≃ (Σ j, Σ i, Fin (b.1 i j)) :=
    { toFun := fun p => ⟨p.2.1, p.1, p.2.2⟩
      invFun := fun p => ⟨p.2.1, p.1, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let w : Equiv.Perm (Fin N) := (B.symm.trans S.symm).trans A
  have hA : ∀ p, blk e (A p) = p.1 := by
    intro p
    simp [A, blk]
  have hB : ∀ p, blk e' (B p) = p.1 := by
    intro p
    simp [B, blk]
  have hw : ∀ p, w.symm (A p) = B (S p) := by
    intro p
    simp [w]
  refine ⟨w, fun i j => ?_⟩
  have himg : (Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j) =
      Finset.univ.image (fun t : Fin (b.1 i j) => A ⟨i, j, t⟩) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨⟨i', j', t⟩, rfl⟩ := A.surjective x
      rw [hA] at h1
      rw [hw, hB] at h2
      dsimp only [S, Equiv.coe_fn_mk] at h1 h2
      subst h1
      subst h2
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      refine ⟨hA _, ?_⟩
      rw [hw, hB]
      rfl
  rw [himg, Finset.card_image_of_injective _ (fun s t h => by simpa using A.injective h)]
  simp

end GlobalTheory.CompanionTheory.SizeCells
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gram_fibre_measure_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (g : GL (Fin M) (R ⊗[F] E)) (l : R), IsUnit l → cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = (algebraMap R (R ⊗[F] E) l) • JR R J → ∀ a c : ℝ≥0, μ.map (actTup R g) = a • μ → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ l) = c • ν → ∀ S, (m S).map (actTup R g) = (a / c) • m (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ l S) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibSim.fib_similitude | exact GlobalTheory.CompanionTheory.SW.FibSim.fib_similitude | (intros; apply GlobalTheory.CompanionTheory.SW.FibSim.fib_similitude <;> assumption)
end

end

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.exists_perm_block_matrix : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (b : SizeMatrix m m'), ∃ w : Equiv.Perm (Fin N), ∀ i j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = b.1 i j := by
  first | exact @GlobalTheory.CompanionTheory.SizeCells.exists_perm_cell_sizes | exact GlobalTheory.CompanionTheory.SizeCells.exists_perm_cell_sizes | (intros; apply GlobalTheory.CompanionTheory.SizeCells.exists_perm_cell_sizes <;> assumption)

end
end
