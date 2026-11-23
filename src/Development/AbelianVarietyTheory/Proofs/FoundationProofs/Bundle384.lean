module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle009
public import Formalism.SatakeDualWeyl.StatementG
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceNonsplitPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CayleyHamiltonHeckeEigenvectorEveryGaloisElement
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonvanishingTransferCharacterSumsPowerSeries
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle366
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle233
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle383
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle338
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle331
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)

noncomputable section
namespace GlobalTheory.InertIwasawaGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_trace_one_loc {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) :
    ∃ τ ∈ intLoc F E v, τ + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ τ = 1 := by
  have hu := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨x, hx⟩ := GlobalTheory.LFun.InertChart.exists_conj_sub_unit h hw
  have hσ := GlobalTheory.LFun.InertChart.conj_conj h
  have h0 : σ (x : E) - x ≠ 0 := by
    intro e; rw [e, map_zero] at hx; exact zero_ne_one hx
  set t : E := σ x / (σ x - x) with ht
  have hsum : t + σ t = 1 := by
    rw [ht, map_div₀, map_sub, hσ, ← neg_sub (σ (x : E)) x, div_neg, ← sub_eq_add_neg, ← sub_div, div_self h0]
  refine ⟨(1 : Fv F v) ⊗ₜ[F] t, ?_, ?_⟩
  · rw [GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hu, GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]
    have hval : ∀ a : E, Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a := fun a =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    change Valued.v (algebraMap E (w.adicCompletion E) t) ≤ 1
    rw [hval, ht, map_div₀, hx, div_one]
    exact w.valuation_le_one (RingOfIntegers.mapRingHom (σ : E →+* E) x)
  · change (1 : Fv F v) ⊗ₜ[F] t + 1 ⊗ₜ[F] σ t = 1
    rw [← TensorProduct.tmul_add, hsum]; rfl


open GlobalTheory.LFun GlobalTheory.InertIwasawa in
theorem hasIwasawa_of_inertAt {σ : E →ₐ[F] E} (hC : IsCMExt F E σ) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hQ : Q = dblGram finSumFinEquiv J) {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsFullLattice E L]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (hL : IsSelfDualAt σ J L v) : HasIwasawa σ Q (KFin σ Q L v) := fun g => by
  have h := (InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨τ, hτO, hτ⟩ := exists_trace_one_loc hC hw
  obtain ⟨a, ha⟩ := Frames.exists_isLatticeFrame (F := F) L
  have eQ : JR (F := F) (Fv F v) Q = dblGram finSumFinEquiv (JR (Fv F v) J) := hQ ▸ JR_dblGram _ J
  obtain ⟨k, h1, h2, h3⟩ := exists_stab finSumFinEquiv (intLoc F E v)
    (hasFrames_of_equiv _ (w.adicCompletionIntegers E) (InertChart.complEquiv hw h) (InertChart.mem_intLoc_iff hw h))
    (σ := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) (fun _ => sigR_mem_intLoc σ) (sigR_invol (InertChart.conj_conj hC))
    hτO hτ
    (J := JR (Fv F v) J) (by ext i j; exact congrArg (fun x => (1 : Fv F v) ⊗ₜ[F] x) (hJ.1 i j))
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_JR hJ.2)) (Λ := latLoc F L v)
    (fun y => Submodule.ext_iff.1 hL y) (ha v) (g := matHom _ σ Q g) (eQ ▸ g.2)
  let κ : GLoc σ Q v := ⟨k, (eQ ▸ h1 : k ∈ Formalism.UG.UJ _ (JR (Fv F v) Q))⟩
  have hκ : κ ∈ KFin σ Q L v := by
    change k ∈ Formalism.UG.stabGL _
    rwa [latLoc_sumLat]
  exact ⟨⟨g * κ, h3⟩, κ⁻¹, inv_mem hκ, (mul_inv_cancel_right g κ).symm⟩

theorem ioH_mem_siegel_mul_KFin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)),
    IsSelfDualAt σ J L v → ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ g : GLoc σ J v,
      ∃ p : siegelH (Fv F v) σ (dblGram finSumFinEquiv J), ∃ k ∈ KFin σ (dblGram finSumFinEquiv J) L v,
        ioH (Fv F v) σ rfl (g, 1) = (p : GLoc σ (dblGram finSumFinEquiv J) v) * k := by
  intro F E _ _ _ _ _ σ h n J hJ L _ v hL P hP g
  exact hasIwasawa_of_inertAt h hJ rfl (w := P) hP hL _

end GlobalTheory.InertIwasawaGen
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

noncomputable section

namespace GlobalTheory.KA

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def untwist (W : R2 Ω l) (θ : G ℚ Ω →* (Qbar l)ˣ) : R2 Ω l where
  toFun s := Units.map (algebraMap (Qbar l) (Matrix (Fin 2) (Fin 2) (Qbar l))).toMonoidHom (θ s)⁻¹ * W s
  map_one' := by simp
  map_mul' s t := by
    apply Units.ext
    simp only [map_mul, mul_inv, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      ← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul, Algebra.algebraMap_eq_smul_one, one_mul, mul_comm]

theorem mat_untwist (W : R2 Ω l) (θ : G ℚ Ω →* (Qbar l)ˣ) (s : G ℚ Ω) :
    mat (untwist W θ) s = (((θ s)⁻¹ : (Qbar l)ˣ) : Qbar l) • mat W s := by
  show algebraMap (Qbar l) (Matrix (Fin 2) (Fin 2) (Qbar l)) (((θ s)⁻¹ : (Qbar l)ˣ) : Qbar l) * mat W s = _
  rw [← Algebra.smul_def]

theorem continuous_untwist {W : R2 Ω l} {θ : G ℚ Ω →* (Qbar l)ˣ} (hW : Continuous W) (hθ : Continuous θ) :
    Continuous (untwist W θ) := by
  have h1 : Continuous fun s => mat (untwist W θ) s := by
    simp only [mat_untwist]
    exact (Units.continuous_coe_inv.comp hθ).smul (Units.continuous_val.comp hW)
  refine Units.continuous_iff.2 ⟨h1, ?_⟩
  have h2 : (fun s => (((untwist W θ s)⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l))) =
      fun s => (θ s : Qbar l) • (((W s)⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
    funext s
    rw [← map_inv, ← map_inv]
    have := mat_untwist W θ s⁻¹
    rw [map_inv θ, inv_inv] at this
    exact this
  rw [h2]
  exact (Units.continuous_val.comp hθ).smul (Units.continuous_coe_inv.comp hW)

theorem unr_of_twisted_limit : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l)) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l), Continuous W → Continuous θ → (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) → (∀ s i j, ρ s i j ∈ c.O) → (∀ r x i, Continuous fun s => Y r s x i) → (∀ r s x i, Y r s x i ∈ c.O) → (∀ r, ShCoc ρ (cycMod ℚ Ω l r)⁻¹ (Y r)) → (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) → (∀ r x, η r x ∈ c.O) → (∀ r s x, ‖η r (x * cycMod ℚ Ω l r s) - η r x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → y ∈ Z1 (Loc.colRep W) → (∀ r s i, ‖y s i - spec (η r) (Y r) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → Unr W y := by
  intro l _ Ω _ _ _ W c θ ρ Y η y hW hθ _ hWρ hρ hYc hYi hSh hpush hη _ hy hlim q hq
  have hρ' : mat (untwist W θ) = ρ := by
    funext s
    rw [mat_untwist, hWρ, smul_smul, Units.inv_mul, one_smul]
  obtain ⟨B, hB, v, hv⟩ := GlobalTheory.T.shifted_cocycle_limit_integral l Ω (untwist W θ) c Y η y (continuous_untwist hW hθ)
    (by rw [hρ']; exact hρ) hYc hYi (by rw [hρ']; exact hSh) hpush hη hlim q hq
  refine ⟨B, hB, ?_⟩
  by_cases h : ∀ s ∈ Ine (F := ℚ) B, θ s = 1
  · refine ⟨v, fun s hs => ?_⟩
    rw [hv s hs, mat_untwist, h s hs]
    simp
  · push Not at h
    obtain ⟨s, hs, hne⟩ := h
    refine ⟨0, fun t ht => ?_⟩
    have hc : y (s * t) = y s + mat W s *ᵥ y t := by
      rw [hy.2 s t]
      rfl
    have hm : mat (untwist W θ) (s * t) = mat (untwist W θ) s * mat (untwist W θ) t := by
      simp only [mat, map_mul, Units.val_mul]
    have hc' : y (s * t) = y s + mat (untwist W θ) s *ᵥ y t := by
      rw [hv _ (mul_mem hs ht), hv s hs, hv t ht, hm, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
      abel
    rw [hc, mat_untwist, Matrix.smul_mulVec, add_right_inj] at hc'
    have h0 : mat W s *ᵥ y t = 0 := by
      have h1 : (1 - (((θ s)⁻¹ : (Qbar l)ˣ) : Qbar l)) • (mat W s *ᵥ y t) = 0 := by
        rw [sub_smul, one_smul, ← hc', sub_self]
      refine (smul_eq_zero.1 h1).resolve_left fun h2 => hne ?_
      have h3 : (θ s)⁻¹ = 1 := Units.ext (sub_eq_zero.1 h2).symm
      exact inv_eq_one.1 h3
    have h4 : y t = 0 := by
      have h5 : mat W s⁻¹ *ᵥ (mat W s *ᵥ y t) = y t := by
        rw [Matrix.mulVec_mulVec]
        have : mat W s⁻¹ * mat W s = 1 := by
          simp only [mat]
          rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
        rw [this, Matrix.one_mulVec]
      rw [← h5, h0, Matrix.mulVec_zero]
    rw [h4]
    simp

end GlobalTheory.KA

end
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.cayleyHamilton_heckeEigenvector_every_galois_element : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ {E : Type} [NormedField E] [IsAlgClosed E] [Algebra ℤ_[l] E], (∀ z : ℤ_[l], ‖algebraMap ℤ_[l] E z‖ = ‖z‖) → ∀ (lam : Letter → E) (t d : (Ω ≃ₐ[ℚ] Ω) → E) (S0 : Finset ℕ), (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖t (s * s') - t (s)‖ < δ) → (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖d (s * s') - d (s)‖ < δ) → (∀ q : ℕ, q.Prime → q ∉ S0 → ∀ s, FrobAt q s → t s = lam (Letter.T q) ∧ d s = (q : E) ^ (w + 1) * lam (Letter.D q)) → ∀ x ∈ X.VB N l w E, (∀ T : Letter, admitted N l T → X.opV N l E T x = lam T • x) → ∀ s : Ω ≃ₐ[ℚ] Ω, X.galV l E s (X.galV l E s x) - t s • X.galV l E s x + d s • x = 0 := by
  first | exact @GlobalTheory.cayleyHamilton_galV | exact GlobalTheory.cayleyHamilton_galV | (intros; apply GlobalTheory.cayleyHamilton_galV <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem h1dual_of_vanish_fix : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ)
    (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ z ∈ Z1 (Loc.colRep (dual1 W)),
    (∀ g ∈ N0g W, z g = 0) → z ∈ ReciprocityTheory.Gal.B1 (Loc.colRep (dual1 W)) := by
  intro l _ Ω _ _ _ e S A W hW z hz hN
  obtain ⟨a, haK, hae⟩ := GlobalTheory.T.exists_ker_rep_cyclotomic_ne_one_normalForm l Ω e S A W hW
  have hWa : W a = 1 := haK
  have hdual : ∀ v : Fin 2 → Qbar l, Loc.colRep (dual1 W) a v = eps l a • v := by
    intro v
    show Matrix.toLin' ((dual1 W a : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) v = _
    rw [dual1, UpperTheory.V.Af.tw_val, hWa]
    simp [dt, hWa, eps, Matrix.toLin'_apply]
  have hcomm : ∀ g, z (a * g) = z (g * a) := by
    intro g
    have hn : (g * a)⁻¹ * (a * g) ∈ N0g W := by
      refine ⟨?_, ?_⟩
      · show cycBar ℚ Ω l ((g * a)⁻¹ * (a * g)) = 1
        simp [map_mul, map_inv, mul_comm, mul_left_comm, mul_assoc]
      · show W ((g * a)⁻¹ * (a * g)) = 1
        simp [map_mul, map_inv, hWa]
    have h1 : a * g = (g * a) * ((g * a)⁻¹ * (a * g)) := by group
    rw [h1, hz.2, hN _ hn, map_zero, add_zero]
  have hne : eps l a - 1 ≠ 0 := sub_ne_zero.mpr hae
  rw [mem_coboundaries1]
  refine ⟨(eps l a - 1)⁻¹ • z a, fun g => ?_⟩
  have key := hcomm g
  rw [hz.2, hz.2, hdual] at key

  have : (eps l a - 1) • z g = Loc.colRep (dual1 W) g (z a) - z a := by
    rw [sub_smul, one_smul]; rw [← sub_eq_zero] at key ⊢; rw [← key]; abel
  rw [map_smul, ← smul_sub, ← this, smul_smul, inv_mul_cancel₀ hne, one_smul]

end GlobalTheory.Ord2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

theorem _root_.GlobalTheory.T.nonvanishing_transfer_characterSums_powerSeries : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Gs L : PowerSeries (Qbar l)) (a a' κ : Qbar l) (v v' : ℕ → Qbar l) (c₀ m₀ c₁ n₀ : ℕ) (φ : DirichletCharacter (Qbar l) l) (e : ℕ), l ≠ 2 → 1 ≤ e → 2 ≤ m₀ → (∀ n, Gs.coeff n ∈ c.O) → (∀ n, L.coeff n ∈ c.O) → ‖a‖ = 1 → ‖a'‖ = 1 → κ ≠ 0 → (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) → (∀ m, ‖v' m‖ = 1 ∧ Cg m (v' (m + 1)) (v' m)) → 2 ≤ c₀ → ¬ l ∣ c₀ → (∀ m, m₀ ≤ m → ∃ z : Qbar l, IsPrimitiveRoot z (l ^ m) ∧ ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive → Cg (m - c₁) ((1 - (c₀ : Qbar l) * ψ⁻¹ (c₀ : ZMod (l ^ m))) * (v' m * κ * a' ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval L (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))) (v m * a ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval Gs (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))) → (∃ r₁ : ℕ, ∀ r, r₁ ≤ r → 1 ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) → ¬ Cg (n₀ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass L r ξ x) 0) → ∃ n₁ r₁ : ℕ, ∀ r, r₁ ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) → ¬ Cg (n₁ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass Gs r ξ x) 0 := by
  first | (exact @GlobalTheory.KZ.Cmp.nonvanishing_transfer) | (exact GlobalTheory.KZ.Cmp.nonvanishing_transfer) | (intros; apply GlobalTheory.KZ.Cmp.nonvanishing_transfer  <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.constantTermAlongFlag_eq_zero_of_cuspidal : ∀ (D : D7) (V : HSp D) (φ : GA D V → ℂ), φ ∈ cuspCont V → ∀ 𝔉 : IsoFlag V, 𝔉.Proper → constTerm 𝔉 φ = 0 := by
  first | exact @GlobalTheory.Cusp.constTerm_eq_zero_of_mem_cuspCont | exact GlobalTheory.Cusp.constTerm_eq_zero_of_mem_cuspCont | (intros; apply GlobalTheory.Cusp.constTerm_eq_zero_of_mem_cuspCont <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchFree.coord

theorem coord_conj_le : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), 0 < Q → ∀ (B : ℝ), 1 ≤ B → (∀ τ, (P.n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ h T, P.coord h T ∈ Qbar ∧ ‖cj Qbar ρ (P.coord h T)‖ ^ 2 ≤ (Nat.card (Cls D P.a (intG D P.a)) : ℝ) ^ 2 * (Q : ℝ) ^ (P.a * P.d) * (((P.a.factorial : ℝ) ^ (∑ τ, P.n τ)) ^ 2 * (3 * (2 * ((fF D * P.a * P.d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * P.a * P.d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * P.a * P.d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (P.a * ∑ τ, P.n τ))) := by
  intro D cc δ t0 Q hc ht0 P hQ B hB hn ρ t0' ht0' h T
  generalize hM : (((P.a.factorial : ℝ) ^ (∑ τ, P.n τ)) ^ 2 * (3 * (2 * ((fF D * P.a * P.d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * P.a * P.d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * P.a * P.d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (P.a * ∑ τ, P.n τ))) = M
  have hev : Even (P.a * P.d) := P.d_even.mul_left _
  obtain ⟨Lt, hL, hL1, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D P.a
  obtain ⟨Lt', hL', hL1', -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D P.d
  have hs : SD D (stdL D P.a) := hL1 ▸ (hL 1).2
  have hs' : SD D (stdL D P.d) := hL1' ▸ (hL' 1).2
  have hjet : ∀ L L', SD D L → SD D L' → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G →
      ∀ y, LaQ D (tor0 D cc δ) L L' y →
      GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G) ∈ Qbar ∧
        ‖cj Qbar ρ (GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G))‖ ^ 2 ≤ M := by
    intro L L' h1 h2 G hG y hy
    rw [← hM]
    exact GlobalTheory.T.conjugate_jet_bound_vacuum_torsion_translate D cc δ t0 hc ht0 P.a P.d L L' h1 h2 hev G hG y hy P.n B hB hn ρ t0' ht0' T
  have hM0 : 0 ≤ M :=
    (sq_nonneg _).trans (hjet _ _ hs hs' P.e0 P.vac.2.2.2.1 0 ⟨1, one_pos, by simp⟩).2
  have hterm : ∀ x, P.term x h T ∈ Qbar ∧ ‖cj Qbar ρ (P.term x h T)‖ ^ 2 ≤ (Q : ℝ) ^ (P.a * P.d) * M := by
    intro x
    obtain ⟨c, k, r, y, hy⟩ := GlobalTheory.T.testVector_adelicPair_translates_movedLatticeVacuum D cc δ t0 Q hc ht0 P x h (Lt x) (Lt' h) (hL x).1 (hL' h).1
    obtain ⟨⟨hcQ, hc1⟩, hy, -, hr, hF, -⟩ := hy hQ
    have hG := GlobalTheory.T.vacuum_image_intertwiner_selfDual_pair D cc δ t0 hc ht0 P.a P.d _ _ (Lt x) (Lt' h) hs hs' (hL x).2 (hL' h).2 P.e0
      P.vac.2.2.2.1
    have hGd := GlobalTheory.NormSum.CoordConj.differentiable_Iop (T := tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d)
      (La D (tor0 D cc δ) (Lt x) (Lt' h)) P.vac.1.1
    change ThetaVectorUpToUnits D (tor0 D cc δ) t0 (Lt x) (Lt' h) (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d)
      (La D (tor0 D cc δ) (Lt x) (Lt' h)) P.e0) at hG
    generalize Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d)
      (La D (tor0 D cc δ) (Lt x) (Lt' h)) P.e0 = G at hG hGd hF
    have e : P.W.Om x h P.F = ∑ i, (((⟨c, hcQ⟩ * r i : Qbar) : ℂ)) • U D (tor0 D cc δ) (y i) G := by
      rw [hF]
      funext z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, MulMemClass.coe_mul, mul_assoc]
    unfold Pair.term
    rw [e, GlobalTheory.NormSum.CoordConj.applyAt0_comb _ _ _ fun i => GlobalTheory.NormSum.CoordConj.differentiable_U _ hGd]
    refine GlobalTheory.NormSum.CoordConj.comb_bound ρ _ _ _ _ hM0 ?_ fun i => hjet _ _ (hL x).2 (hL' h).2 G hG _ ⟨Q, hQ, hy i⟩
    have h1 : ‖ρ ⟨c, hcQ⟩‖ = 1 := hc1 (ρ : Qbar →+* ℂ)
    simp only [map_mul, norm_mul, h1, one_mul]
    exact hr (ρ : Qbar →+* ℂ)
  haveI := (GlobalTheory.T.unitaryDoubleCosetClasses_finite_card_le D P.a).1
  haveI := Fintype.ofFinite (Cls D P.a (intG D P.a))
  have e : P.coord h T = ∑ x : Cls D P.a (intG D P.a),
      ((((gam D (intG D P.a) x.out : Qbar))⁻¹ : Qbar) : ℂ) * P.term x.out h T := by
    unfold Pair.coord
    rw [finsum_eq_sum_of_fintype]
    simp
  rw [e, mul_assoc]
  refine GlobalTheory.NormSum.CoordConj.comb_bound ρ _ _ _ _ (by positivity) ?_ fun x => hterm _
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  rw [Nat.card_eq_fintype_card, Fintype.card, Finset.card_eq_sum_ones]
  push_cast
  refine Finset.sum_le_sum fun x _ => ?_
  rw [map_inv₀, map_natCast, norm_inv, Complex.norm_natCast]
  exact Nat.cast_inv_le_one _

end GlobalTheory.ArchFree.coord
end
