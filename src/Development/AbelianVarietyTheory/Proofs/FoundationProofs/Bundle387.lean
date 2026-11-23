module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle386
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle379
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle335
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle444
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntertwinerOfInvariantPairingAdmissible
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanLogPeriodConjugatesEqChowlaSelberg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.HeckeProj

theorem heckeProj_newform : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (k : ℕ) (g : UpperTheory.V.Af.Newform k) (N l : ℕ) [Fact l.Prime], l ≠ 2 → g.M ∣ N → 5 ≤ N → Nat.Coprime N l → Odd k → 3 ≤ k → ∀ α : ℂ, α ^ 2 - g.a l * α + g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) = 0 → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 2) → ∀ lamC : Letter → ℂ, (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → lamC (Letter.T q) = g.a q) → lamC Letter.U = α → (∀ d : ℕ, Nat.Coprime d N → lamC (Letter.D d) = g.χ (d : ZMod g.M)) → ∀ {E : Type} [NormedField E] [IsAlgClosed E] [Algebra ℤ_[l] E], (∀ z : ℤ_[l], ‖algebraMap ℤ_[l] E z‖ = ‖z‖) → ∀ (ι : E ≃+* ℂ), let w := k - 2; let lam : Letter → E := fun T => ι.symm (lamC T); ∀ (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) E) (S0 : Finset ℕ), (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ q : ℕ, q.Prime → q ∉ S0 → ∀ s, FrobAt q s → Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E) = lam (Letter.T q) ∧ Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E) = (q : E) ^ (w + 1) * lam (Letter.D q)) → (∀ V : Submodule E (Fin 2 → E), (∀ s v, v ∈ V → (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v ∈ V) → V = ⊥ ∨ V = ⊤) → ∃ (m : ℕ) (π : Fin m → (E ⊗[ℤ_[l]] X.Fn l) →ₗ[E] (Fin 2 → E)) (σ : Fin m → (Fin 2 → E) →ₗ[E] (E ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra E Letter), P ∈ admissibleLettersSubalgebra E N l ∧ FreeAlgebra.lift E lam P = 1 ∧ (∀ x ∈ X.VB N l w E, (∀ T : Letter, admitted N l T → X.opV N l E T x = lam T • x) → ∑ i, σ i (π i x) = x) ∧ (∀ i v, σ i v ∈ X.VB N l w E) ∧ (∀ i s, ∀ x ∈ X.VB N l w E, π i (X.galV l E s x) = (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ π i x) ∧ (∀ i s v, X.galV l E s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v)) ∧ (∀ i (T : Letter) v, admitted N l T → X.opV N l E T (σ i v) = lam T • σ i v) ∧ (∀ i (T : Letter), admitted N l T → ∀ x ∈ X.VB N l w E, π i (X.opV N l E T x) = lam T • π i x) ∧ (∀ i j v, π i (σ j v) = if i = j then v else 0) ∧ ∀ x ∈ X.VB N l w E, FreeAlgebra.lift E (X.opV N l E) P x = ∑ i, σ i (π i x) := by
  intro Ω _ _ _ ε X hε han k g N l _ hl2 hgN hN5 hNl hk hk3 α hα hα1 hα2 lamC hT hU hD E _ _ _ hnorm ι
    w lam ρ S0 htr hdet hfrob hirr
  have hlp : l.Prime := Fact.out
  have hlN : ¬ l ∣ N := (Nat.Prime.coprime_iff_not_dvd hlp).1 hNl.symm
  have hpot : SSPotB N l (k - 2) lamC :=
    GlobalTheory.T.semisimple_potentials_at_newform_eigensystem k g N l hgN hN5 hlp hlN hk hk3 α hα hα1 hα2 lamC hT hU hD
  have hw : Odd w := by
    obtain ⟨j, rfl⟩ := hk
    refine ⟨j - 1, ?_⟩
    show 2 * j + 1 - 2 = 2 * (j - 1) + 1
    omega
  have hpot' : SSPotB N l w (fun T => ι (lam T)) := by
    have : (fun T => ι (lam T)) = lamC := by
      funext T; simp [lam]
    rw [this]; exact hpot
  have hbb : X.SSBB N l w E lam :=
    GlobalTheory.T.semisimple_tensor_of_semisimple_potentials ε X hε han N l w hl2 hN5 hNl hw ι lam hpot'
  exact GlobalTheory.T.galois_representation_of_eigensystem ε X hε han N l w hl2 hN5 hNl hw hnorm lam hbb ρ S0 htr hdet hfrob hirr

end GlobalTheory.KZ.HeckeProj
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.AutMult

theorem isUnitEquiv_iff_nonempty_equiv_of_isCopyFinDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → IsCopyFinDS σ M π ⊤ → ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (π' : GA D V →* (H' →L[ℂ] H')), IsIrrUnitary π' → ∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (σ' : Representation ℂ (GfC V) W'), σ'.IsIrreducible → IsAdmissible σ' → IsCopyFinDS σ' M π' ⊤ → (IsUnitEquiv π π' ↔ Nonempty (σ.Equiv σ')) := by
  classical
  intro D V S M H _ _ π hπ W _ _ σ hσ hσa hc H' _ _ π' hπ' W' _ _ σ' hσ' hσa' hc'
  have := hπ.complete
  have := hπ'.complete
  obtain ⟨T, hT, hTi, hTd⟩ := hc
  obtain ⟨T', hT', hTi', hTd'⟩ := hc'
  have hTf : T ∈ homFinDS σ M π ⊤ := hT
  have hTf' : T' ∈ homFinDS σ' M π' ⊤ := hT'
  have hTm := mem_homTensorPi.1 hT
  have hTm' := mem_homTensorPi.1 hT'
  have hδ : ∀ τ, IsIrrUnitary (dsRep M τ) := isIrrUnitary_dsRep M
  haveI : σ.IsIrreducible := hσ
  haveI : σ'.IsIrreducible := hσ'
  haveI : Nontrivial W := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GfC V)) σ.asModule
  haveI : Nontrivial W' := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GfC V)) σ'.asModule
  constructor
  · rintro ⟨A, hA⟩
    have hAs : ∀ g x, A.symm (π' g x) = π g (A.symm x) := fun g x => by
      apply A.injective
      rw [hA, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
    let Ac : H' →L[ℂ] H := A.symm.toLinearIsometry.toContinuousLinearMap
    let T'' : W' →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H :=
      (ContinuousLinearMap.compContinuousMultilinearMapL ℂ M.H H' H Ac).toLinearMap ∘ₗ T'
    have hT''v : ∀ w y, T'' w y = A.symm (T' w y) := fun _ _ => rfl
    have hT'' : ∀ w, T'' w ∈ homDS M π ⊤ := fun w => ⟨fun _ => trivial, fun τ g y => by
      rw [hT''v, hT''v, hTm'.2.2, hAs]⟩
    let B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun v w => bePi (T v) (T w))
      (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
      (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
    let C : W →ₗ[ℂ] W' →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun v w => bePi (T v) (T'' w))
      (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
      (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
    have hBpos : ∀ x, x ≠ 0 → 0 < (B x x).re := fun x hx =>
      bePi_self_pos hδ hπ.unitary (hT.1 x) ((map_ne_zero_iff T hTi).2 hx)
    have hB : ∀ g x y, B (σ g x) (σ g y) = B x y := fun g x y => by
      change ⟪T (σ g y) _, T (σ g x) _⟫_ℂ = ⟪T y _, T x _⟫_ℂ
      rw [hTm.2.1, hTm.2.1, inner_map_map hπ.unitary]
    have hC : ∀ g x y, C (σ g x) (σ' g y) = C x y := fun g x y => by
      change ⟪T'' (σ' g y) _, T (σ g x) _⟫_ℂ = ⟪T'' y _, T x _⟫_ℂ
      rw [hT''v, hT''v, hTm'.2.1, hAs, hTm.2.1, inner_map_map hπ.unitary]
    obtain ⟨K₀, hKo, hKc⟩ := GlobalTheory.CuspDec.exists_compact_open V
    obtain ⟨φ, hφ, hCB⟩ := GlobalTheory.InvPairing.exists_intertwiner (GfC V) K₀ hKo hKc W W' σ σ' hσa hσa'.1 B C hBpos hB hC
    obtain ⟨w', hw'⟩ := exists_ne (0 : W')
    have h1 : T'' w' ≠ 0 := by
      intro h
      apply hw'
      apply hTi'
      rw [map_zero]
      ext y
      apply A.symm.injective
      rw [← hT''v, h]
      simp
    obtain ⟨y', hy'⟩ : ∃ y', T'' w' y' ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact h1 (ContinuousMultilinearMap.ext hn)
    obtain ⟨w, y, hwy⟩ : ∃ w y, ⟪T'' w' y', T w y⟫_ℂ ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hy'
      have hsub : Submodule.span ℂ {v | ∃ w y, v = T w y} ≤ (ℂ ∙ T'' w' y')ᗮ := Submodule.span_le.2 (by
        rintro _ ⟨w, y, rfl⟩
        exact Submodule.mem_orthogonal_singleton_iff_inner_right.2 (hn w y))
      have hcl := Submodule.topologicalClosure_minimal _ hsub (Submodule.isClosed_orthogonal _)
      rw [hTd] at hcl
      exact inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hcl Submodule.mem_top))
    have hC0 : C w w' ≠ 0 := fun h => hwy (by
      rw [inner_eq_bePi hδ hπ.unitary (hT.1 w) (hT'' w') y y']
      change C w w' * _ = 0
      rw [h, zero_mul])
    have hφ0 : φ w' ≠ 0 := fun h => hC0 (by rw [hCB, h, map_zero])
    let f : Representation.IntertwiningMap σ' σ := ⟨φ, fun g => LinearMap.ext fun y => hφ g y⟩
    rcases Representation.IsIrreducible.bijective_or_eq_zero f with hb | hf0
    · exact ⟨(Representation.IntertwiningMap.ofBijective f hb).symm⟩
    · exact absurd (congrArg (fun F : Representation.IntertwiningMap σ' σ => F w') hf0) hφ0
  · rintro ⟨e⟩
    let T₂ : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H' := T' ∘ₗ e.toLinearMap
    have hT₂ : T₂ ∈ homFinDS σ M π' ⊤ := by
      refine mem_homTensorPi.2 ⟨fun _ _ => trivial, fun g w y => ?_, fun τ g w y => hTm'.2.2 τ g (e w) y⟩
      change T' (e (σ g w)) y = _
      rw [show e (σ g w) = σ' g (e w) from Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g w]
      exact hTm'.2.1 g (e w) y
    obtain ⟨B, hB, hBv⟩ := GlobalTheory.TrExt.exists_homIn_extend D V S M W σ hσ hσa H π hπ.unitary T hTf hTi hTd H' π'
      hπ'.unitary ⊤ isClosed_univ T₂ hT₂
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have h1 : T' (e w) ≠ 0 := fun h => hw (e.injective (hTi' (h.trans (map_zero T').symm) |>.trans (map_zero e).symm))
    obtain ⟨y, hy⟩ : ∃ y, T' (e w) y ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact h1 (ContinuousMultilinearMap.ext hn)
    have hB0 : B ≠ 0 := fun h => hy (by rw [← show B (T w y) = T' (e w) y from hBv w y, h]; rfl)
    have hm : multIn π π' ⊤ ≠ 0 := by
      intro h0
      rw [multIn, Submodule.rank_eq_zero] at h0
      exact hB0 (by simpa [h0] using hB)
    obtain ⟨f, hf⟩ := uEquiv_of_multIn_ne_zero hπ hπ' hm
    exact ⟨f, hf⟩

end GlobalTheory.AutMult
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_irreducibleUnitary_completion_finiteTimesDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → mCuspDS μ σ M ≠ 0 → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π ∧ IsCopyFinDS σ M π ⊤ := by
  first | exact @GlobalTheory.AutMult.exists_isIrrUnitary_isCopyFinDS | exact GlobalTheory.AutMult.exists_isIrrUnitary_isCopyFinDS | (intros; apply GlobalTheory.AutMult.exists_isIrrUnitary_isCopyFinDS <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AutMult

open scoped InnerProductSpace
open GlobalTheory.Cusp


open Classical in
theorem rank_homIn_eq_rank_homFinDS {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : GA D V →* (H →L[ℂ] H)} (hπ : IsUnitaryRep π)
    {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GfC V) W} (hirr : σ.IsIrreducible)
    (hadm : IsAdmissible σ) (hcopy : IsCopyFinDS σ M π ⊤) {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {ρ : GA D V →* (K →L[ℂ] K)} (hρ : IsUnitaryRep ρ) {U : Submodule ℂ K} (hU : IsClosed (U : Set K)) :
    Module.rank ℂ (homIn π ρ U) = Module.rank ℂ (homFinDS σ M ρ U) := by
  obtain ⟨T, hT, hinj, hd⟩ := hcopy
  have hTm := mem_homTensorPi.1 hT
  let f : homIn π ρ U →ₗ[ℂ] (W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H K) :=
    { toFun := fun A => (ContinuousLinearMap.compContinuousMultilinearMapL ℂ M.H H K (A : H →L[ℂ] K)).toLinearMap ∘ₗ T
      map_add' := fun A B => by ext w y; simp
      map_smul' := fun c A => by ext w y; simp }
  have hmem : ∀ A, f A ∈ homFinDS σ M ρ U := fun A => by
    refine mem_homTensorPi.2 ⟨fun w y => ?_, fun g w y => ?_, fun i g w y => ?_⟩
    · exact A.2.1 _
    · change (A : H →L[ℂ] K) (T (σ g w) y) = _
      exact (congrArg (A : H →L[ℂ] K) (hTm.2.1 g w y)).trans (A.2.2 _ _)
    · change (A : H →L[ℂ] K) (T w _) = _
      exact (congrArg (A : H →L[ℂ] K) (hTm.2.2 i g w y)).trans (A.2.2 _ _)
  let F : homIn π ρ U →ₗ[ℂ] homFinDS σ M ρ U := f.codRestrict _ hmem
  have hdense : Dense ((Submodule.span ℂ {v | ∃ w y, v = T w y} : Submodule ℂ H) : Set H) :=
    (Submodule.dense_iff_topologicalClosure_eq_top).2 hd
  have hbij : Function.Bijective F := by
    constructor
    · intro A B hAB
      have e : ∀ w y, (A : H →L[ℂ] K) (T w y) = (B : H →L[ℂ] K) (T w y) := fun w y =>
        congrArg (fun Φ : homFinDS σ M ρ U => ((Φ : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H K) w) y) hAB
      refine Subtype.ext (ContinuousLinearMap.ext_on hdense ?_)
      rintro _ ⟨w, y, rfl⟩
      exact e w y
    · intro Φ
      obtain ⟨A, hA, hAe⟩ := GlobalTheory.TrExt.exists_homIn_extend D V S M W σ hirr hadm H π hπ T hT hinj hd K ρ hρ U hU Φ.1 Φ.2
      exact ⟨⟨A, hA⟩, Subtype.ext (LinearMap.ext fun w => ContinuousMultilinearMap.ext fun y => hAe w y)⟩
  exact (LinearEquiv.ofBijective F hbij).rank_eq


open Classical in
theorem mCusp_eq_mCuspDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → IsCopyFinDS σ M π ⊤ → mCusp V μ π = mCuspDS μ σ M := by
  intro D V S M μ _ _ H _ _ π hπ W _ _ σ hirr hadm hcopy
  haveI : CompleteSpace H := hπ.complete
  exact rank_homIn_eq_rank_homFinDS hπ.unitary hirr hadm hcopy (isUnitaryRep_RG V μ) (isSubrep_L2cusp V μ).1

end GlobalTheory.AutMult
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.mean_log_period_conjugates_eq_chowlaSelberg : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M → (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)) / Real.pi)) / (Module.finrank ℚ M : ℝ) = Real.eulerMascheroniConstant + Real.log (2 * Real.pi / Real.sqrt D.host.d) - logDerivativeAtOne D := by
  first | exact @GlobalTheory.PeriodMean.mean_log_period | exact GlobalTheory.PeriodMean.mean_log_period | (intros; apply GlobalTheory.PeriodMean.mean_log_period <;> assumption)
end

end

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitaryEquiv_iff_finitePart_equiv_discreteSeries : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → IsCopyFinDS σ M π ⊤ → ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (π' : GA D V →* (H' →L[ℂ] H')), IsIrrUnitary π' → ∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (σ' : Representation ℂ (GfC V) W'), σ'.IsIrreducible → IsAdmissible σ' → IsCopyFinDS σ' M π' ⊤ → (IsUnitEquiv π π' ↔ Nonempty (σ.Equiv σ')) := by
  first | exact @GlobalTheory.AutMult.isUnitEquiv_iff_nonempty_equiv_of_isCopyFinDS | exact GlobalTheory.AutMult.isUnitEquiv_iff_nonempty_equiv_of_isCopyFinDS | (intros; apply GlobalTheory.AutMult.isUnitEquiv_iff_nonempty_equiv_of_isCopyFinDS <;> assumption)

end
end

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.cuspMultiplicity_completion_eq_discreteSeriesModel : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → IsCopyFinDS σ M π ⊤ → mCusp V μ π = mCuspDS μ σ M := by
  first | exact @GlobalTheory.AutMult.mCusp_eq_mCuspDS | exact GlobalTheory.AutMult.mCusp_eq_mCuspDS | (intros; apply GlobalTheory.AutMult.mCusp_eq_mCuspDS <;> assumption)

end
end
