module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle225
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle044
public import Formalism.SatakeDualWeyl.StatementW
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle085
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle084
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.LocalRingCardinality.Params
import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting

@[expose] public section

section

open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

namespace GlobalTheory.SerSys

theorem continuous_glMap {g : ℕ} [Fact g.Prime] {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    (e : ℚ_[g] ≃+* F) (he : Continuous e) (n : ℕ) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) e.toRingHom) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map he
  · have : (fun x : GL (Fin n) ℚ_[g] => ((Matrix.GeneralLinearGroup.map (n := Fin n) e.toRingHom x)⁻¹ : GL (Fin n) F).val) =
        fun x => (x⁻¹).val.map e := by
      funext x; rw [← map_inv]; rfl
    rw [this]
    exact Units.continuous_coe_inv.matrix_map he

theorem irrSm_pullback (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F) (he : Continuous e) (n : ℕ)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) F)) :
    IrrSm (Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) : QRep g n) := by
  set φ := Matrix.GeneralLinearGroup.map (n := Fin n) e.toRingHom with hφ
  have hsurj : Function.Surjective φ := fun y =>
    ⟨Matrix.GeneralLinearGroup.map (n := Fin n) e.symm.toRingHom y, by
      ext i j; simp [hφ]⟩
  refine ⟨⟨GlobalTheory.SmGL.nontrivial_of_irreducible σ.irr, fun W hW => ?_⟩, fun v => ?_⟩
  · have hW' : ∀ y, ∀ v ∈ W, σ.ρ y v ∈ W := fun y v hv => by
      obtain ⟨x, rfl⟩ := hsurj y
      exact hW x v hv
    haveI : IsSimpleOrder (Subrepresentation σ.ρ) := σ.irr
    let S : Subrepresentation σ.ρ := ⟨W, fun y v hv => hW' y v hv⟩
    rcases eq_bot_or_eq_top S with h | h
    · left; exact congrArg Subrepresentation.toSubmodule h
    · right; exact congrArg Subrepresentation.toSubmodule h
  · exact (σ.smooth v).preimage (continuous_glMap e he n)

end GlobalTheory.SerSys
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Ker GlobalTheory.RatEqui

namespace GlobalTheory.DetStab

theorem isIntegral_det_of_stable {R E : Type} [CommRing R] [IsNoetherianRing R] [Field E] [Algebra R E] {n : ℕ}
    (L : Submodule R (Fin n → E)) (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (γ : Matrix (Fin n) (Fin n) E) (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral R γ.det := by
  classical
  let N : Submodule R E := Submodule.span R {x | ∃ w : Fin n → L, x = (Matrix.of fun i => (w i : Fin n → E)).det}
  let M : Submodule R E := ⨆ j : Fin n, L.map (LinearMap.proj j : (Fin n → E) →ₗ[R] E)
  have hM : M.FG := Submodule.fg_iSup _ fun j => hfg.map (LinearMap.proj j : (Fin n → E) →ₗ[R] E)
  have hprod : ∀ (s : Finset (Fin n)) (f : Fin n → E), (∀ i, f i ∈ M) → ∏ i ∈ s, f i ∈ M ^ s.card := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.card_empty, pow_zero]
      exact Submodule.one_le.1 le_rfl
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
      exact Submodule.mul_mem_mul (hf a) ih
  have hle : N ≤ M ^ (Finset.univ : Finset (Fin n)).card := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, rfl⟩
    rw [SetLike.mem_coe, Matrix.det_apply]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [Units.smul_def]
    refine Submodule.smul_of_tower_mem _ _ (hprod _ _ fun i => ?_)
    exact Submodule.mem_iSup_of_mem i ⟨_, (w (σ i)).2, rfl⟩
  have hN : N.FG := (hM.pow _).of_le hle
  have hne : N ≠ ⊥ := by
    intro h
    have h0 : (Matrix.detRowAlternating (n := Fin n) (R := E)).toMultilinearMap = 0 := by
      refine MultilinearMap.ext_of_span_eq_top (g := fun _ (x : L) => (x : Fin n → E)) (fun _ => ?_) fun w => ?_
      · rw [← hsp]; congr 1; exact Subtype.range_coe
      · have : (Matrix.of fun i => (w i : Fin n → E)).det ∈ N := Submodule.subset_span ⟨w, rfl⟩
        rw [h] at this
        exact this
    have h1 := congrArg (fun f => f (1 : Matrix (Fin n) (Fin n) E)) h0
    have h2 : (1 : Matrix (Fin n) (Fin n) E).det = 0 := h1
    simp at h2
  refine isIntegral_of_smul_mem_submodule N hne hN _ fun x hx => ?_
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine Submodule.subset_span ⟨fun i => ⟨γ.mulVec (w i), hγ _ (w i).2⟩, ?_⟩
    rw [smul_eq_mul, mul_comm, ← Matrix.det_transpose γ, ← Matrix.det_mul]
    congr 1
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact N.add_mem hx hy
  | smul r x _ hx => rw [smul_comm]; exact N.smul_mem r hx

theorem prod_emb_det_eq_one (D : D7) (χ : IdE D → ℂ) (hχ : IsChi D χ) (n : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (hL : SD D L) (γ : Matrix (Fin n) (Fin n) D.host.E)
    (hu : γ * adj D γ = 1) (hs : ∀ v, v ∈ L ↔ γ.mulVec v ∈ L) : ∏ τ, embT D τ γ.det = 1 := by
  letI := D.host.cmStar
  obtain ⟨hfg, hsp, -⟩ := hL
  have hstar : ∀ x : D.host.E, star x = D.host.conj x := by
    intro x
    haveI := D.host.isCMField_hostE
    apply D.host.φ₀.injective
    rw [Formalism.HC.HostAx.conjE_apply]
    exact IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x
  have hd : γ.det * (adj D γ).det = 1 := by rw [← Matrix.det_mul, hu, Matrix.det_one]
  have hadj : (adj D γ).det = D.host.conj γ.det := by
    unfold adj
    rw [Matrix.det_transpose]
    exact (RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) γ).symm
  have hz : γ.det ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, hstar, ← hadj]
    exact ⟨by rw [mul_comm, hd], hd⟩
  have i1 := isIntegral_det_of_stable L hfg hsp γ fun v hv => (hs v).1 hv
  have i2 := isIntegral_det_of_stable L hfg hsp (adj D γ) fun v hv => (hs _).2 (by
    rw [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]; exact hv)
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝓞 D.host.E)).1 i1
  obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝓞 D.host.E)).1 i2
  have hspan : Submodule.span (𝓞 D.host.E) {γ.det} = Submodule.span (𝓞 D.host.E) {(1 : D.host.E)} := by
    apply le_antisymm
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨a, by rw [Algebra.smul_def, ha, mul_one]⟩
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨b, by rw [Algebra.smul_def, hb, mul_comm, hd]⟩
  have e1 := hχ.2 ⟨γ.det, hz⟩
  have e2 := hχ.2 1
  have e3 : ∏ τ, (embT D τ γ.det)⁻¹ = 1 := by
    have e1' : χ (Submodule.span (𝓞 D.host.E) {γ.det}) = ∏ τ, (embT D τ γ.det)⁻¹ := e1
    have e2' : χ (Submodule.span (𝓞 D.host.E) {(1 : D.host.E)}) = ∏ τ, (embT D τ 1)⁻¹ := e2
    rw [← e1', hspan, e2']
    simp
  rwa [Finset.prod_inv_distrib, inv_eq_one] at e3

end GlobalTheory.DetStab
end

section

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

theorem _root_.GlobalTheory.T.cofactorTwistRelation_dualWeight_involutive : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∃ ε : ℤˣ, ∀ f ∈ dualWeyl R (m + 1) (m + 1) ν, ∀ g : MP R (m + 1), CofRel R m ν f g → CofRel R m (nuDual ν) g ((ε : ℤ) • f) := by
  first | exact @GlobalTheory.ValCmp.Invol.cofRel_invol | exact GlobalTheory.ValCmp.Invol.cofRel_invol | (intros; apply GlobalTheory.ValCmp.Invol.cofRel_invol <;> assumption)
end

section

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

theorem _root_.GlobalTheory.T.cofactorTwistRelation_rowAct_equivariant : ∀ (K : Type) [Field K] (m : ℕ) (ν : Fin (m + 1) → ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) K), IsUnit h.det → ∀ f ∈ dualWeyl K (m + 1) (m + 1) ν, ∀ g : MP K (m + 1), CofRel K m ν f g → CofRel K m ν (rowAct K h⁻¹ f) (h.det ^ (-(ν 0 : ℤ)) • rowAct K h.transpose g) := by
  first | exact @GlobalTheory.ValCmp.Eqv.cofRel_rowAct | exact GlobalTheory.ValCmp.Eqv.cofRel_rowAct | (intros; apply GlobalTheory.ValCmp.Eqv.cofRel_rowAct <;> assumption)
end

section

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

theorem _root_.GlobalTheory.T.cofactorTwistRelation_rowDiv_swap : ∀ (R : Type) [CommRing R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (a b : Fin (m + 1)) (k : ℕ) (f g : MP R (m + 1)), a ≠ b → CofRel R m ν f g → CofRel R m ν (rowDiv R a b k f) (((-1 : ℤ) ^ k) • rowDiv R b a k g) := by
  first | exact @GlobalTheory.ValCmp.cofRel_rowDiv | exact GlobalTheory.ValCmp.cofRel_rowDiv | (intros; apply GlobalTheory.ValCmp.cofRel_rowDiv <;> assumption)
end

section

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem initMinor_mem_dualWeyl_ind (R : Type) [CommRing R] {r n s : ℕ} (hs : s ≤ n) (I : Fin s → Fin r) :
    initMinor R I hs ∈ dualWeyl R r n (fun t => if t.val < s then 1 else 0) := by
  have h := bidetMem R r n 1 (fun _ => s) (fun _ => hs) (fun _ => I)
  have e1 : bideterminant R (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) = initMinor R I hs := by
    simp [bideterminant]
  have e2 : (shapeDeg (fun _ : Fin 1 => s) : Fin n → ℕ) = fun t => if t.val < s then 1 else 0 := by
    funext t
    by_cases ht : t.val < s <;> simp [shapeDeg, ht]
  rwa [e1, e2] at h

private lemma one_mem_dualWeyl_zero (R : Type) [CommRing R] (r n : ℕ) :
    (1 : MvPolynomial (Fin r × Fin n) R) ∈ dualWeyl R r n 0 := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule]
  exact ⟨isWeightedHomogeneous_one R _, fun l j _ => by rw [map_one, map_one]⟩

private lemma mul_mem_dualWeyl_add (R : Type) [CommRing R] {r n : ℕ} {ν₁ ν₂ : Fin n → ℕ}
    {f g : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ dualWeyl R r n ν₁) (hg : g ∈ dualWeyl R r n ν₂) :
    f * g ∈ dualWeyl R r n (ν₁ + ν₂) := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf hg ⊢
  refine ⟨hf.1.mul hg.1, fun l j hlj => ?_⟩
  rw [map_mul, map_mul, hf.2 l j hlj, hg.2 l j hlj]

theorem prod_mem_dualWeyl_sum (R : Type) [CommRing R] {r n : ℕ} {ι : Type} (S : Finset ι) (w : ι → Fin n → ℕ)
    (g : ι → MvPolynomial (Fin r × Fin n) R) (hg : ∀ k, g k ∈ dualWeyl R r n (w k)) :
    ∏ k ∈ S, g k ∈ dualWeyl R r n (∑ k ∈ S, w k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using one_mem_dualWeyl_zero R r n
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mul_mem_dualWeyl_add R (hg a) ih

theorem exists_cofAct_initMinor (R : Type) [CommRing R] [IsDomain R] {n s : ℕ} (hs : s ≤ n) (I : Fin s → Fin n) :
    ∃ g ∈ dualWeyl R n n (fun t => if 0 < s ∧ t.val < n - s then 1 else 0),
      (genM R n).det ^ (s - 1) * g = cofAct R n (initMinor R I hs) := by
  classical
  rcases Nat.eq_zero_or_pos s with rfl | h1
  · refine ⟨1, ?_, ?_⟩
    · convert one_mem_dualWeyl_zero R n n using 2
      funext t
      simp
    · simp [initMinor]
  by_cases hI : Function.Injective I
  · obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), ∀ a, σ (Fin.castLE hs a) = I a := by
      let e : {x // x ∈ Set.range (Fin.castLE hs)} ≃ {x // x ∈ Set.range I} :=
        (Equiv.ofInjective _ (Fin.castLE_injective hs)).symm.trans (Equiv.ofInjective I hI)
      refine ⟨e.extendSubtype, fun a => ?_⟩
      rw [Equiv.extendSubtype_apply_of_mem e _ ⟨a, rfl⟩]
      simp only [e, Equiv.trans_apply]
      rw [Equiv.ofInjective_symm_apply]
      rfl
    obtain ⟨ε, hε⟩ := cofAct_initMinor R n s hs h1 σ
    have hIσ : (fun a : Fin s => σ (Fin.castLE hs a)) = I := funext hσ
    rw [hIσ] at hε
    refine ⟨(ε : ℤ) • initMinor R (fun a : Fin (n - s) => σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a)))
      (Nat.sub_le n s), ?_, ?_⟩
    · have hm := initMinor_mem_dualWeyl_ind R (Nat.sub_le n s)
        (fun a : Fin (n - s) => σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a)))
      have hw : (fun t : Fin n => if 0 < s ∧ t.val < n - s then 1 else 0) =
          fun t : Fin n => if t.val < n - s then 1 else 0 := by
        funext t
        simp [h1]
      rw [hw]
      exact zsmul_mem hm _
    · rw [hε, mul_smul_comm]
  · refine ⟨0, zero_mem _, ?_⟩
    simp only [Function.Injective, not_forall, exists_prop] at hI
    obtain ⟨a, b, hab, hne⟩ := hI
    have h0 : initMinor R I hs = 0 := by
      unfold initMinor
      exact Matrix.det_zero_of_row_eq hne (by funext q; simp [hab])
    rw [h0, map_zero, mul_zero]

theorem nuDual_shapeDeg {m K : ℕ} (sz : Fin K → ℕ) :
    nuDual (shapeDeg sz : Fin (m + 1) → ℕ) =
      ∑ k, fun t : Fin (m + 1) => if 0 < sz k ∧ t.val < m + 1 - sz k then 1 else 0 := by
  funext t
  have key : ∀ k, ((if t.rev.val < sz k then 1 else 0) +
      (if 0 < sz k ∧ t.val < m + 1 - sz k then 1 else 0) : ℕ) =
        if (0 : Fin (m + 1)).val < sz k then 1 else 0 := by
    intro k
    have := t.isLt
    rw [Fin.val_rev]
    split_ifs <;> (try simp only [Fin.val_zero] at *) <;> omega
  have hsum : ∑ k, (if t.rev.val < sz k then 1 else 0) +
      ∑ k, (if 0 < sz k ∧ t.val < m + 1 - sz k then 1 else 0) =
        ∑ k, (if (0 : Fin (m + 1)).val < sz k then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => key k
  simp only [nuDual, shapeDeg, Finset.sum_apply, Finset.card_filter]
  omega

private lemma card_filter_fin_val_lt_eq_of_le {N a : ℕ} (h : a ≤ N) :
    (Finset.univ.filter fun i : Fin N => i.val < a).card = a := by
  have e : (Finset.univ.filter fun i : Fin N => i.val < a) = Finset.univ.map (Fin.castLEEmb h) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    constructor
    · intro hi
      exact ⟨⟨i.val, hi⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.isLt
  rw [e, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem sum_shapeDeg_sub {m K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ m + 1) :
    ∑ i, (shapeDeg sz : Fin (m + 1) → ℕ) i - (shapeDeg sz : Fin (m + 1) → ℕ) 0 = ∑ k, (sz k - 1) := by
  have h1 : ∑ i, (shapeDeg sz : Fin (m + 1) → ℕ) i = ∑ k, sz k := by
    simp only [shapeDeg, Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.card_filter]
    exact card_filter_fin_val_lt_eq_of_le (hsz k)
  have h0 : (shapeDeg sz : Fin (m + 1) → ℕ) 0 = ∑ k, (if (0 : Fin (m + 1)).val < sz k then 1 else 0) := by
    simp only [shapeDeg, Finset.card_filter]
  have h2 : ∑ k, (sz k - 1) + ∑ k, (if (0 : Fin (m + 1)).val < sz k then 1 else 0) = ∑ k, sz k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      split_ifs <;> (try simp only [Fin.val_zero] at *) <;> omega
  rw [h1, h0]
  omega

theorem exists_cofRel_dualWeyl : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∀ f ∈ dualWeyl R (m + 1) (m + 1) ν, ∃ g ∈ dualWeyl R (m + 1) (m + 1) (nuDual ν), CofRel R m ν f g := by
  intro R _ _ m ν _ _ f hf
  obtain ⟨b, ⟨_, hspan, _⟩, hb⟩ := sSBasis R (m + 1) (m + 1) ν
  rw [← hspan] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨K, sz, hsz, I, hsh, -, hbi⟩ := (hb i).2.2
    rw [hbi]
    choose g hg hgeq using fun k => exists_cofAct_initMinor R (hsz k) (I k)
    refine ⟨∏ k, g k, ?_, ?_⟩
    · have hm := prod_mem_dualWeyl_sum R Finset.univ _ g hg
      rwa [← nuDual_shapeDeg sz, hsh] at hm
    · show (genM R (m + 1)).det ^ (∑ i, ν i - ν 0) * ∏ k, g k = cofAct R (m + 1) (bideterminant R sz hsz I)
      rw [← hsh, sum_shapeDeg_sub sz hsz, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, bideterminant,
        map_prod]
      exact Finset.prod_congr rfl fun k _ => hgeq k
  | zero => exact ⟨0, zero_mem _, by simp [CofRel]⟩
  | add x y _ _ hx hy =>
    obtain ⟨g₁, h₁, e₁⟩ := hx
    obtain ⟨g₂, h₂, e₂⟩ := hy
    refine ⟨g₁ + g₂, add_mem h₁ h₂, ?_⟩
    unfold CofRel at e₁ e₂ ⊢
    rw [mul_add, e₁, e₂, map_add (f := _)]
  | smul a x _ hx =>
    obtain ⟨g, h, e⟩ := hx
    refine ⟨a • g, Submodule.smul_mem _ a h, ?_⟩
    unfold CofRel at e ⊢
    rw [mul_smul_comm, e, map_smul]

end GlobalTheory.ValCmp
end

section

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem sum_mul_sub_succ : ∀ (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν →
    ∑ s : Fin m, s.val * (ν s.castSucc - ν s.succ) + m * ν (Fin.last m) + ν 0 = ∑ i, ν i := by
  intro m
  induction m with
  | zero => intro ν _; simp
  | succ m ih =>
    intro ν hν
    have h := ih (fun i => ν i.castSucc) (fun a b hab => hν (by simpa using hab))
    rw [Fin.sum_univ_castSucc (f := ν), ← h, Fin.sum_univ_castSucc]
    have hle : ν (Fin.last (m + 1)) ≤ ν (Fin.last m).castSucc := hν (Fin.le_last _)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    simp only [Fin.val_castSucc, Fin.val_last, Fin.succ_last, Fin.castSucc_zero, Fin.succ_castSucc, hd,
      Nat.add_sub_cancel_left]
    ring

noncomputable def revInitMinor (R : Type) [CommRing R] (n k : ℕ) : MP R n :=
  if h : k ≤ n then initMinor R (fun a : Fin k => Fin.rev (Fin.castLE h a)) h else 1

def antiDiagGL (R : Type) [CommRing R] (n : ℕ) : GL (Fin n) R where
  val := Matrix.of fun a b => if b = a.rev then 1 else 0
  inv := Matrix.of fun a b => if b = a.rev then 1 else 0
  val_inv := by
    ext a b
    rw [Matrix.mul_apply, Finset.sum_eq_single a.rev (fun j _ hj => by simp [hj]) (by simp)]
    simp [Matrix.one_apply, eq_comm]
  inv_val := by
    ext a b
    rw [Matrix.mul_apply, Finset.sum_eq_single a.rev (fun j _ hj => by simp [hj]) (by simp)]
    simp [Matrix.one_apply, eq_comm]

theorem dwAct_antiDiag_X (R : Type) [CommRing R] (n : ℕ) (a s : Fin n) :
    Formalism.UG.dwAct R n n (antiDiagGL R n) (X (a, s)) = X (a.rev, s) := by
  have : (((antiDiagGL R n)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      Matrix.of fun a b => if b = a.rev then 1 else 0 := rfl
  rw [Formalism.UG.dwAct, this, rowAct, aeval_X, Finset.sum_eq_single a.rev (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem dwAct_antiDiag_lpMinor (R : Type) [CommRing R] (n k : ℕ) (h h' : k ≤ n) :
    Formalism.UG.dwAct R n n (antiDiagGL R n) (lpMinor R k h h') = revInitMinor R n k := by
  rw [revInitMinor, dite_eq_left h, lpMinor, initMinor, AlgHom.map_det]
  congr 1
  ext a b : 2
  simp [dwAct_antiDiag_X]

theorem cofAct_lpMinor (R : Type) [CommRing R] [IsDomain R] (n k : ℕ) (h h' : k + 1 ≤ n) : ∃ ε : ℤˣ,
    cofAct R n (lpMinor R (k + 1) h h') = (ε : ℤ) • ((genM R n).det ^ k * revInitMinor R n (n - (k + 1))) := by
  obtain ⟨ε, hε⟩ := cofAct_initMinor R n (k + 1) h (by omega) 1
  refine ⟨ε, ?_⟩
  rw [revInitMinor, dite_eq_left (Nat.sub_le _ _)]
  exact hε

theorem exists_cofRel_hw : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∃ g ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν), CofRel R m ν (hw R le_rfl ν) g := by
  intro R _ _ m ν hν h0
  have hmem : hw R le_rfl (nuDual ν) ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν) :=
    Submodule.subset_span ⟨[], rfl⟩
  have hJ := Formalism.UG.Final.WeylGLStable R (m + 1) (m + 1) le_rfl (nuDual ν) (antiDiagGL R (m + 1)) _ hmem
  have hnext : ∀ (μ : Fin (m + 1) → ℕ) (s : Fin m), nuNext μ s.castSucc = μ s.succ := by
    intro μ s
    have : s.castSucc.val + 1 < m + 1 := by simp
    rw [nuNext, dite_eq_left this]
    rfl
  have e1 : Formalism.UG.dwAct R (m + 1) (m + 1) (antiDiagGL R (m + 1)) (hw R le_rfl (nuDual ν)) =
      ∏ s : Fin m, revInitMinor R (m + 1) (m + 1 - (s.val + 1)) ^ (ν s.castSucc - ν s.succ) := by
    rw [hw, map_prod, Fin.prod_univ_castSucc]
    simp only [map_pow, dwAct_antiDiag_lpMinor, hnext]
    have : nuDual ν (Fin.last m) = 0 := by simp [nuDual]
    rw [this, Nat.zero_sub, pow_zero, mul_one, ← Equiv.prod_comp Fin.revPerm]
    refine Finset.prod_congr rfl fun s _ => ?_
    have h1 : ν s.castSucc ≤ ν 0 := hν (Fin.zero_le _)
    have h2 : ν s.succ ≤ ν s.castSucc := hν (Fin.castSucc_lt_succ).le
    have hs := s.isLt
    congr 1
    · congr 1
      simp [Fin.val_rev]
      omega
    · simp only [nuDual, Fin.revPerm_apply, Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev]
      omega
  choose ε hε using fun s : Fin m =>
    cofAct_lpMinor R (m + 1) s.val (by have := s.isLt; omega) (by have := s.isLt; omega)
  refine ⟨(∏ s : Fin m, (ε s : ℤ) ^ (ν s.castSucc - ν s.succ)) • _, Submodule.smul_of_tower_mem _ _ hJ, ?_⟩
  have hsum : ∑ i, ν i - ν 0 = ∑ s : Fin m, s.val * (ν s.castSucc - ν s.succ) := by
    have := sum_mul_sub_succ m ν hν
    rw [h0] at this
    omega
  rw [CofRel, e1, hsum, hw, map_prod, Fin.prod_univ_castSucc, h0, Nat.zero_sub, pow_zero, map_one, mul_one]
  simp only [map_pow, hnext, Fin.val_castSucc, hε, zsmul_eq_mul, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum]
  push_cast
  ring

end GlobalTheory.ValCmp
end

section

open NumberField Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.isAlgebraicHeckeCharOfWeight_of_integer_expo : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ : HChar E) (n : (E →+* ℂ) → ℤ), (∀ τ, expo χ τ = n τ) → IsAlgPos χ n := by
  first | exact @GlobalTheory.CuspRep.AlgExpo.isAlgPos_of_expo | exact GlobalTheory.CuspRep.AlgExpo.isAlgPos_of_expo | (intros; apply GlobalTheory.CuspRep.AlgExpo.isAlgPos_of_expo <;> assumption)
end
