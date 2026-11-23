module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle255
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle236
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle185
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle027
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle186
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle045
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction

namespace GlobalTheory.BKDimNoInv

section Bridge

open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

theorem rep_apply {m : ℕ} (r : ↥Gw →* GL (Fin m) O) (g : ↥(GK Bw.Kw)) (x : Fin m → ↥Bw.LL.1) :
    Bw.rep r g x = (((r (Bw.e.symm g) : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map Bw.toLL).mulVec x :=
  rfl

theorem toLL_injective : Function.Injective Bw.toLL :=
  Subtype.val_injective.comp Bw.eO.injective

theorem toLL_continuous : Continuous Bw.toLL :=
  continuous_subtype_val.comp Bw.eO_cont

theorem rep_continuous {m : ℕ} (r : ↥Gw →* GL (Fin m) O)
    (hr : Continuous fun g => ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O))
    (x : Fin m → ↥Bw.LL.1) : Continuous fun g => Bw.rep r g x := by
  haveI : IsTopologicalRing ↥Bw.LL.1 := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1.2.2.2.1
  simp only [rep_apply]
  exact ((hr.comp Bw.e_symm_cont).matrix_map (toLL_continuous Bw)).matrix_mulVec continuous_const

theorem localGaloisRep_invariants_from_fractionRing [IsDomain O] {m : ℕ} (r : ↥Gw →* GL (Fin m) O)
    (h : ∀ x : Fin m → FractionRing O, (∀ g : ↥Gw,
      (((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map (algebraMap O (FractionRing O))).mulVec x = x) →
        x = 0) : H0V (Bw.rep r) = ⊥ := by
  obtain ⟨_, -, hfr⟩ := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1.1
  let φ : FractionRing O →+* ↥Bw.LL.1 := IsFractionRing.lift (g := Bw.toLL) (toLL_injective Bw)
  have hφ : ∀ a, φ (algebraMap O _ a) = Bw.toLL a := fun a => IsFractionRing.lift_algebraMap _ a
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨n, d, -, rfl⟩ := IsFractionRing.div_surjective (A := ↥(OL Bw.LL)) y
    refine ⟨algebraMap O _ (Bw.eO.symm n) / algebraMap O _ (Bw.eO.symm d), ?_⟩
    rw [map_div₀, hφ, hφ]
    simp [LocBridge.toLL]
  rw [eq_bot_iff]
  intro x hx
  choose x₀ hx₀ using fun a => hsurj (x a)
  have h0 : x₀ = 0 := by
    refine h x₀ fun g => ?_
    have h1 : Bw.rep r (Bw.e g) x = x := by
      have := (Submodule.mem_iInf _).1 hx (Bw.e g)
      rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    rw [rep_apply, MulEquiv.symm_apply_apply] at h1
    funext a
    apply φ.injective
    rw [hx₀, ← congrFun h1 a]

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hφ, hx₀]
  rw [Submodule.mem_bot]
  funext a
  rw [← hx₀, h0]
  exact map_zero φ

noncomputable def grepOf {m : ℕ} (r : ↥Gw →* GL (Fin m) O)
    (hr : Continuous fun g => ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O)) :
    GRep ↥(GK Bw.Kw) ℚ_[l] ↥Bw.LL.1 ↥(OL Bw.LL) :=
  haveI : IsTopologicalRing ↥Bw.LL.1 := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1.2.2.2.1
  { V := Fin m → ↥Bw.LL.1
    acg := inferInstance
    modLL := inferInstance
    modQp := inferInstance
    towQp := inferInstance
    modO := inferInstance
    towO := inferInstance
    fd := inferInstance
    top := inferInstance
    mtop := inferInstance
    cadd := inferInstance
    csmul := inferInstance
    ρ := Bw.rep r
    cont := rep_continuous Bw r hr }


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem finrank_h1f_no_invariants [IsDomain O] (P : LocPrime l) {m : ℕ} (r : ↥Gw →* GL (Fin m) O)
    (hr : Continuous fun g => ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O))
    (hBK : Formalism.MainNotions.LocalSituation.bkADim (P.PD Bw.Kw)) (hdR : Bw.IsdRW P r)
    (h : ∀ x : Fin m → FractionRing O, (∀ g : ↥Gw,
      (((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map (algebraMap O (FractionRing O))).mulVec x = x) →
        x = 0) :
    (Module.finrank ↥Bw.LL.1 (FiniteCohomology (P.PD Bw.Kw) (Bw.rep r)) : ℤ) =
      (Module.finrank ↥Bw.LL.1 ↥(DdR (P.PD Bw.Kw) (Bw.rep r)) : ℤ) -
        Module.finrank ↥Bw.LL.1 ↥(DdR (P.PD Bw.Kw) (Bw.rep r) ⊓
          FilV (P.PD Bw.Kw) (LL := ↥Bw.LL.1) (V := Fin m → ↥Bw.LL.1) 0) := by
  have hG := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1
  let A := grepOf Bw r hr
  have hA : IsDR (P.PD Bw.Kw) A.ρ := by
    change Module.finrank ↥Bw.LL.1 ↥(DdR (P.PD Bw.Kw) (Bw.rep r)) =
      Module.finrank ℚ_[l] ↥Bw.Kw.1 * Module.finrank ↥Bw.LL.1 (Fin m → ↥Bw.LL.1)
    rw [Module.finrank_fin_fun]
    exact hdR
  have key := hBK _ _ hG A hA
  have h0 : Module.finrank ↥Bw.LL.1 ↥(H0V A.ρ) = 0 := by
    have : H0V A.ρ = ⊥ := localGaloisRep_invariants_from_fractionRing Bw r h
    rw [this, finrank_bot]
  rw [h0, Nat.cast_zero, zero_add] at key
  exact key

end Bridge

end GlobalTheory.BKDimNoInv
end

section

open scoped Matrix

namespace GlobalTheory.AugSpan

theorem exists_mem_span_sub_one_eq_id_on :
    ∀ {K : Type} [Field K] [IsAlgClosed K] {Γ : Type} [Group Γ] {m : ℕ}
      (S : Γ →* Matrix (Fin m) (Fin m) K) (P : Submodule K (Fin m → K)),
      (∀ g, ∀ v ∈ P, S g *ᵥ v ∈ P) →
      (∀ Q : Submodule K (Fin m → K), Q ≤ P → (∀ g, ∀ v ∈ Q, S g *ᵥ v ∈ Q) → Q = ⊥ ∨ Q = P) →
      (∃ g, ∃ v ∈ P, S g *ᵥ v ≠ v) →
      ∃ T ∈ Submodule.span K (Set.range fun g => S g - 1), ∀ v ∈ P, T *ᵥ v = v := by
  intro K _ _ Γ _ m S P hst hirrP hnt
  classical
  set J := Submodule.span K (Set.range fun g => S g - 1) with hJ
  obtain ⟨g₀, v₀, hv₀, hne⟩ := hnt
  have hP : P ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hv₀
    apply hne
    rw [hv₀, Matrix.mulVec_zero]
  have hinv : ∀ g, ∀ v ∈ P, (Matrix.toLin' (S g)) v ∈ P :=
    fun g v hv => by rw [Matrix.toLin'_apply]; exact hst g v hv
  let r : Representation K Γ P :=
    { toFun := fun g => (Matrix.toLin' (S g)).restrict (hinv g)
      map_one' := by
        ext v i
        simp [LinearMap.restrict_apply]
      map_mul' := fun g g' => by
        ext v i
        simp [LinearMap.restrict_apply, Matrix.mulVec_mulVec] }
  have hr : ∀ g (v : P), ((r g v : P) : Fin m → K) = S g *ᵥ (v : Fin m → K) :=
    fun g v => by simp [r, LinearMap.restrict_apply]
  have hirr : r.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation r) := by
      refine ⟨⊥, ⊤, fun hbt => hP ?_⟩
      have h2 := congrArg Subrepresentation.toSubmodule hbt
      change (⊥ : Submodule K P) = ⊤ at h2
      rw [eq_bot_iff]
      intro v hv
      have : (⟨v, hv⟩ : P) ∈ (⊥ : Submodule K P) := by rw [h2]; trivial
      rw [Submodule.mem_bot] at this
      simpa using congrArg Subtype.val this
    refine ⟨fun W => ?_⟩
    have hle : W.toSubmodule.map P.subtype ≤ P := by
      rintro _ ⟨v, _, rfl⟩; exact v.2
    have hinvW : ∀ g, ∀ v ∈ W.toSubmodule.map P.subtype, S g *ᵥ v ∈ W.toSubmodule.map P.subtype := by
      rintro g _ ⟨v, hv, rfl⟩
      refine ⟨r g v, W.apply_mem_toSubmodule g hv, ?_⟩
      simp [hr]
    rcases hirrP _ hle hinvW with h1 | h1
    · left
      refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun v hv => ?_)
      have : (v : Fin m → K) ∈ W.toSubmodule.map P.subtype := ⟨v, hv, rfl⟩
      rw [h1, Submodule.mem_bot] at this
      show v ∈ (⊥ : Submodule K P)
      rw [Submodule.mem_bot]; exact Subtype.ext this
    · right
      refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun v _ => ?_)
      have : (v : Fin m → K) ∈ W.toSubmodule.map P.subtype := by rw [h1]; exact v.2
      obtain ⟨w, hw, hwv⟩ := this
      rwa [show w = v from Subtype.ext hwv] at hw
  have hs := GlobalTheory.BurnsideField.span_range_eq_top_of_isAlgClosed r hirr
  have hJl : ∀ g, ∀ T ∈ J, S g * T ∈ J := by
    intro g T hT
    induction hT using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      have : S g * (S h - 1) = (S (g * h) - 1) - (S g - 1) := by
        rw [map_mul, mul_sub, mul_one]; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ c hx
  have hJr : ∀ g, ∀ T ∈ J, T * S g ∈ J := by
    intro g T hT
    induction hT using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      have : (S h - 1) * S g = (S (h * g) - 1) - (S g - 1) := by
        rw [map_mul, sub_mul, one_mul]; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ c hx
  let J' : Submodule K (Module.End K P) :=
    { carrier := {f | ∃ T ∈ J, ∀ w : P, T *ᵥ (w : Fin m → K) = f w}
      add_mem' := by
        rintro f f' ⟨T, hT, hTf⟩ ⟨T', hT', hTf'⟩
        exact ⟨T + T', J.add_mem hT hT', fun w => by
          rw [Matrix.add_mulVec, hTf, hTf']; simp⟩
      zero_mem' := ⟨0, J.zero_mem, fun w => by simp⟩
      smul_mem' := by
        rintro c f ⟨T, hT, hTf⟩
        exact ⟨c • T, J.smul_mem c hT, fun w => by
          rw [Matrix.smul_mulVec, hTf]; simp⟩ }
  have hmem : ∀ f, f ∈ J' ↔ ∃ T ∈ J, ∀ w : P, T *ᵥ (w : Fin m → K) = f w := fun f => Iff.rfl
  have hl : ∀ a : Module.End K P, ∀ f ∈ J', a * f ∈ J' := by
    intro a f hf
    have ha : a ∈ Submodule.span K (Set.range r) := by rw [hs]; trivial
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨T, hT, hTf⟩ := (hmem f).1 hf
      refine (hmem _).2 ⟨S g * T, hJl g T hT, fun w => ?_⟩
      rw [← Matrix.mulVec_mulVec, hTf, Module.End.mul_apply, hr]
    | zero => rw [zero_mul]; exact J'.zero_mem
    | add x y _ _ hx hy => rw [add_mul]; exact J'.add_mem hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact J'.smul_mem c hx
  have hrt : ∀ a : Module.End K P, ∀ f ∈ J', f * a ∈ J' := by
    intro a f hf
    have ha : a ∈ Submodule.span K (Set.range r) := by rw [hs]; trivial
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨T, hT, hTf⟩ := (hmem f).1 hf
      refine (hmem _).2 ⟨T * S g, hJr g T hT, fun w => ?_⟩
      rw [← Matrix.mulVec_mulVec, ← hr, hTf, Module.End.mul_apply]
    | zero => rw [mul_zero]; exact J'.zero_mem
    | add x y _ _ hx hy => rw [mul_add]; exact J'.add_mem hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact J'.smul_mem c hx
  set f₀ : Module.End K P := r g₀ - 1 with hf₀def
  have hf₀ : f₀ ∈ J' := (hmem _).2 ⟨S g₀ - 1, Submodule.subset_span ⟨g₀, rfl⟩, fun w => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hf₀def, LinearMap.sub_apply, Submodule.coe_sub, hr]; rfl⟩
  set w₀ : P := ⟨v₀, hv₀⟩ with hw₀
  have hfw : f₀ w₀ ≠ 0 := by
    intro h
    apply hne
    have h' := congrArg Subtype.val h
    rw [hf₀def, LinearMap.sub_apply, Submodule.coe_sub, hr, Submodule.coe_zero, sub_eq_zero] at h'
    exact h'
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual K P, ψ (f₀ w₀) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hfw ((Module.forall_dual_apply_eq_zero_iff K _).1 hc)
  let b := Module.finBasis K P
  have hid : (1 : Module.End K P) ∈ J' := by
    have heq : (1 : Module.End K P) = ∑ i, ((ψ (f₀ w₀))⁻¹ • ψ.smulRight (b i)) * f₀ *
        ((b.coord i).smulRight w₀) := by
      ext1 w
      rw [LinearMap.sum_apply, Module.End.one_apply]
      conv_lhs => rw [← b.sum_repr w]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, map_smul,
        smul_eq_mul, smul_smul, Module.Basis.coord_apply]
      congr 1
      field_simp
    rw [heq]
    exact J'.sum_mem fun i _ => hrt _ _ (hl _ _ hf₀)
  obtain ⟨T, hT, hTid⟩ := (hmem _).1 hid
  exact ⟨T, hT, fun v hv => hTid ⟨v, hv⟩⟩

end GlobalTheory.AugSpan
end

section

open GlobalTheory.NeedB Polynomial

noncomputable section

open IntermediateField

namespace GlobalTheory.Hilbert90CupCoboundary

theorem isLocallyConstant_eval {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (τ : Ω) : IsLocallyConstant (fun g : Ω ≃ₐ[K] Ω => g τ) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  haveI : FiniteDimensional K K⟮τ⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral τ)
  have hopen : IsOpen ((K⟮τ⟯).fixingSubgroup : Set (Ω ≃ₐ[K] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  refine ⟨(fun g' => g⁻¹ * g') ⁻¹' ((K⟮τ⟯).fixingSubgroup : Set (Ω ≃ₐ[K] Ω)),
    hopen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact Subgroup.one_mem _
  · intro g' hg'
    have hfτ : (g⁻¹ * g') τ = τ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg' τ
        (IntermediateField.mem_adjoin_simple_self K τ)
    have e : g' = g * (g⁻¹ * g') := by group
    show g' τ = g τ
    rw [e, AlgEquiv.mul_apply, hfτ]

theorem zmod_cocycle_eq_coboundary_of_unit_twisted_cocycle : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  ∀ (c : (Ω ≃ₐ[K] Ω) → (Ω ≃ₐ[K] Ω) → ZMod N) (v : (Ω ≃ₐ[K] Ω) → Ωˣ), IsLocallyConstant v →
  (∀ g h, (v g : Ω) * g (v h) = ζ ^ (c g h).val * v (g * h)) →
  ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧ ∀ g h, c g h = η h - η (g * h) + η g := by
  intro K Ω _ _ _ _ _ N ζ hN0 hζ hfix c v hv hcoc
  classical
  haveI : NeZero N := ⟨by omega⟩
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let u : (Ω ≃ₐ[K] Ω) → Ωˣ := fun g => v g ^ N
  have hu_lc : IsLocallyConstant u := hv.comp (fun x : Ωˣ => x ^ N)
  have hu_coc : ∀ g h, ((u (g * h) : Ωˣ) : Ω) = u g * g (u h) := by
    intro g h
    simp only [u, Units.val_pow_eq_pow_val, map_pow]
    rw [← mul_pow, hcoc g h, mul_pow, ← pow_mul, mul_comm (c g h).val N, pow_mul, hζ.pow_eq_one,
      one_pow, one_mul]
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_unit_eq_div_of_locallyConstant_cocycle K Ω u hu_lc hu_coc
  obtain ⟨τ, hτ⟩ := IsAlgClosed.exists_pow_nat_eq (t : Ω) hN0
  have ht0 : (t : Ω) ≠ 0 := t.ne_zero
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN0.ne'] at hτ
    exact ht0 hτ.symm
  have hgτ0 : ∀ g : Ω ≃ₐ[K] Ω, g τ ≠ 0 := fun g => (map_ne_zero g).2 hτ0
  let w : (Ω ≃ₐ[K] Ω) → Ω := fun g => (v g : Ω) * τ / g τ
  have hw_lc : IsLocallyConstant w :=
    (hv.comp (fun x : Ωˣ => (x : Ω))).comp₂ (isLocallyConstant_eval (K := K) τ) (fun a b => a * τ / b)
  have hw_pow : ∀ g, w g ^ N = 1 := by
    intro g
    have h1 : (v g : Ω) ^ N = g t / t := by rw [← Units.val_pow_eq_pow_val]; exact ht g
    have h2 : (g τ) ^ N = g t := by rw [← map_pow, hτ]
    have h3 : g (t : Ω) ≠ 0 := (map_ne_zero g).2 ht0
    simp only [w]
    rw [div_pow, mul_pow, h1, h2, hτ]
    field_simp
  have hw_coc : ∀ g h, w g * g (w h) = ζ ^ (c g h).val * w (g * h) := by
    intro g h
    have hghτ : g (h τ) ≠ 0 := (map_ne_zero g).2 (hgτ0 h)
    have hg := hgτ0 g
    have e1 : w g * g (w h) = ((v g : Ω) * g (v h)) * τ / g (h τ) := by
      simp only [w, map_div₀, map_mul]
      field_simp
    rw [e1, hcoc g h]
    simp only [w, AlgEquiv.mul_apply]
    ring
  let E : Ω → ZMod N := fun x => if hx : ∃ i : ZMod N, ζ ^ i.val = x then hx.choose else 0
  let η : (Ω ≃ₐ[K] Ω) → ZMod N := fun g => E (w g)
  have hη : ∀ g, ζ ^ (η g).val = w g := by
    intro g
    obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one (hw_pow g)
    have hex : ∃ j : ZMod N, ζ ^ j.val = w g := ⟨(i : ZMod N), by rw [ZMod.val_cast_of_lt hi, hi']⟩
    simp only [η, E, dif_pos hex]
    exact hex.choose_spec
  refine ⟨η, hw_lc.comp E, ?_⟩
  intro g h
  have key : ζ ^ (η g + η h).val = ζ ^ (c g h + η (g * h)).val := by
    rw [KumLemma.pow_val_add hζ, KumLemma.pow_val_add hζ, hη g, hη h, hη (g * h)]
    have : g (w h) = w h := by rw [← hη h, map_pow, hfix]
    rw [← hw_coc, this]
  have hinj : η g + η h = c g h + η (g * h) :=
    ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) key)
  linear_combination -hinj

end GlobalTheory.Hilbert90CupCoboundary
end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem rankin_dirichlet_identity : ∀ (e : ℕ) (χ ψ θ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ m n, ψ (m * n) = ψ m * ψ n) → (∀ m n, θ (m * n) = θ m * θ n) → (∀ n, ‖χ n‖ ≤ 1 ∧ ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) → (∀ m n : ℕ, 0 < m → 0 < n → g m * g n = ∑ δ ∈ (Nat.gcd m n).divisors, χ δ * (δ : ℂ) ^ (2 * e) * g (m * n / δ ^ 2)) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → ∀ b : ℕ → ℂ, (∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ (e - 1) * θ p.2) → LSeriesSummable (fun n => g n * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ) ∧ LSeries (fun n => χ n * ψ n * θ n) ((e + 1 : ℕ) + 2 * s) * LSeries (fun n => g n * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ) = LSeries (fun n => ψ n * g n) ((e + 1 : ℝ) + s : ℝ) * LSeries (fun n => θ n * g n) ((2 * (e : ℝ) + s : ℝ) : ℂ) := by
  intro e χ ψ θ g s he hs hψ hθ hn hg hsum b hb
  have hGB := GlobalTheory.T.lSeriesSummable_mul_divisorSum' e ψ θ g b s he hs (fun n => ⟨(hn n).2.1, (hn n).2.2⟩) hsum hb
  have hU := GlobalTheory.T.lSeriesSummable_twist_pow_of_summable_sq_div e ψ g s he hs (fun n => (hn n).2.1) hsum
  have hV := GlobalTheory.T.lSeriesSummable_bounded_mul_of_summable_sq_div e θ g s he hs (fun n => (hn n).2.2) hsum
  have hz := GlobalTheory.T.lSeries_squares_eq_shift e χ ψ θ s he hs hn
  refine ⟨hGB, ?_⟩
  rw [← hz.2, ← LSeries_convolution' hz.1 hGB, ← GlobalTheory.T.lSeries_twist_natPow_eq_shift e ψ g s he, ← LSeries_convolution' hU hV]
  exact LSeries_congr (fun {n} hn0 => (GlobalTheory.T.convolution_twist_eq_convolution_squares e χ ψ θ g b hψ hθ hg hb n hn0).symm) _

end GlobalTheory.EisM
end
