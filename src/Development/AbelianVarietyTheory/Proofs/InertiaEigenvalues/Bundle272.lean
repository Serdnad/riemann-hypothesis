module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle051
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle146
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle237
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle246
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle114
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle147
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle249
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitaryGroupTorusCutoff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussAtUniformiser
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle222
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle248
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle247
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Valuation.Integral
public import Mathlib.RingTheory.WittVector.Complete
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

noncomputable section

namespace GlobalTheory.UnipCoords

variable (R : Type) [CommRing R] (n : ℕ)

def strictUpper (x : {p : Fin n × Fin n // p.1 < p.2} → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if h : i < j then x ⟨(i, j), h⟩ else 0

theorem det_one_add_strictUpper (x : {p : Fin n × Fin n // p.1 < p.2} → R) :
    (1 + strictUpper R n x).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [strictUpper]
  · intro i j hij
    have h1 : ¬ i < j := not_lt.2 (le_of_lt hij)
    have h2 : i ≠ j := ne_of_gt hij
    simp [strictUpper, h1, h2, Matrix.one_apply_ne h2]

def unitOf (x : {p : Fin n × Fin n // p.1 < p.2} → R) : GL (Fin n) R where
  val := 1 + strictUpper R n x
  inv := (1 + strictUpper R n x).adjugate
  val_inv := by rw [Matrix.mul_adjugate, det_one_add_strictUpper, one_smul]
  inv_val := by rw [Matrix.adjugate_mul, det_one_add_strictUpper, one_smul]

theorem unitOf_mem (x : {p : Fin n × Fin n // p.1 < p.2} → R) :
    unitOf R n x ∈ GlobalTheory.SmGL.unipB R (Fin n) := by
  refine (GlobalTheory.SmGL.mem_unipB R).2 ⟨fun i j hji => ?_, fun i => ?_⟩
  · have h1 : ¬ i < j := not_lt.2 (le_of_lt hji)
    have h2 : i ≠ j := ne_of_gt hji
    simp [unitOf, strictUpper, h1, Matrix.one_apply_ne h2]
  · simp [unitOf, strictUpper]

end GlobalTheory.UnipCoords

open GlobalTheory.UnipCoords in
theorem GlobalTheory.UnipCoords.unipCoordsHomeomorph : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (n : ℕ),
    ∃ e : (GlobalTheory.SmGL.unipB R (Fin n)) ≃ₜ ({p : Fin n × Fin n // p.1 < p.2} → R),
      ∀ u : GlobalTheory.SmGL.unipB R (Fin n), e u = fun p => ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2 := by
  intro R _ _ _ n
  have hX : Continuous (fun x : {p : Fin n × Fin n // p.1 < p.2} → R => strictUpper R n x) := by
    refine continuous_matrix fun i j => ?_
    by_cases h : i < j
    · simp only [strictUpper, Matrix.of_apply, h, dite_true]; exact continuous_apply _
    · simp only [strictUpper, Matrix.of_apply, h, dite_false]; exact continuous_const
  let e : (GlobalTheory.SmGL.unipB R (Fin n)) ≃ ({p : Fin n × Fin n // p.1 < p.2} → R) :=
    { toFun := fun u p => ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2
      invFun := fun x => ⟨unitOf R n x, unitOf_mem R n x⟩
      left_inv := by
        rintro ⟨u, hu⟩
        obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 hu
        apply Subtype.ext; apply Units.ext; ext i j
        change (1 + strictUpper R n _) i j = _
        rcases lt_trichotomy i j with h | h | h
        · simp [strictUpper, h, Matrix.one_apply_ne (ne_of_lt h)]
        · subst h; simp [strictUpper, h2]
        · have h' : ¬ i < j := not_lt.2 (le_of_lt h)
          simp [strictUpper, h', Matrix.one_apply_ne (ne_of_gt h), h1 i j h]
      right_inv := by
        intro x; funext p
        change (1 + strictUpper R n x) p.1.1 p.1.2 = x p
        simp [strictUpper, p.2, Matrix.one_apply_ne (ne_of_lt p.2)] }
  refine ⟨{ toEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }, fun u => rfl⟩
  · refine continuous_pi fun p => ?_
    have hv : Continuous (fun u : GlobalTheory.SmGL.unipB R (Fin n) => ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) :=
      (Units.continuous_val (M := Matrix (Fin n) (Fin n) R)).comp continuous_subtype_val
    exact (continuous_apply_apply p.1.1 p.1.2).comp hv
  · refine Continuous.subtype_mk ?_ _
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact continuous_const.add hX
    · exact (continuous_const.add hX).matrix_adjugate
end
end

section

open Formalism.MainNotions.N GlobalTheory.TraceSemisimple

namespace GlobalTheory.SemisimpleTraceForm

theorem idem_eq_zero_of_trace {k : Type} [Field k] [CharZero k] {n : ℕ}
    (e : Matrix (Fin n) (Fin n) k) (he : e * e = e) (ht : e.trace = 0) : e = 0 := by
  have hf : IsIdempotentElem (Matrix.toLin' e) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he]
  have hp : LinearMap.IsProj (LinearMap.range (Matrix.toLin' e)) (Matrix.toLin' e) :=
    ⟨fun v => ⟨v, rfl⟩, by
      rintro _ ⟨v, rfl⟩
      exact congrArg (fun f : Module.End k (Fin n → k) => f v) hf⟩
  have h1 := hp.trace
  rw [Matrix.trace_toLin'_eq, ht] at h1
  have h2 : Module.finrank k (LinearMap.range (Matrix.toLin' e)) = 0 := by
    exact_mod_cast h1.symm
  rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h2
  exact (LinearEquiv.map_eq_zero_iff _).1 h2

theorem semisimple_span {Γ k : Type} [Group Γ] [Field k] {n : ℕ}
    (ρ : Γ →* GL (Fin n) k) (h : IsSSRep ρ) : IsSemisimpleRing (spanAlg ρ) := by
  let φ : spanAlg ρ →+* Module.End k (Fin n → k) :=
    ((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp (spanAlg ρ).val).toRingHom
  letI : Module (spanAlg ρ) (Fin n → k) := Module.compHom _ φ
  have hs : ∀ (a : spanAlg ρ) (v : Fin n → k),
      a • v = (a : Matrix (Fin n) (Fin n) k).mulVec v := fun _ _ => rfl
  have hinv : ∀ W, IsInv ρ W → ∀ a : spanAlg ρ, ∀ v ∈ W, a • v ∈ W := by
    rintro W hW ⟨a, ha⟩ v hv
    rw [hs]
    show a.mulVec v ∈ W
    rw [mem_spanAlg] at ha
    induction ha using Submodule.span_induction with
    | mem y hy => obtain ⟨g, rfl⟩ := hy; exact hW g v hv
    | zero => rw [Matrix.zero_mulVec]; exact W.zero_mem
    | add y z _ _ hy hz => rw [Matrix.add_mulVec]; exact W.add_mem hy hz
    | smul c y _ hy => rw [Matrix.smul_mulVec]; exact W.smul_mem c hy
  have hV : IsSemisimpleModule (spanAlg ρ) (Fin n → k) := by
    rw [isSemisimpleModule_iff]
    refine ⟨fun U => ?_⟩
    let W : Submodule k (Fin n → k) :=
      { toAddSubmonoid := U.toAddSubmonoid
        smul_mem' := fun c v hv => by
          have h1 : (c • (1 : Matrix (Fin n) (Fin n) k)).mulVec v ∈ U :=
            U.smul_mem (c • (1 : spanAlg ρ)) hv
          rw [Matrix.smul_mulVec, Matrix.one_mulVec] at h1
          exact h1 }
    have hW : IsInv ρ W := fun g v hv =>
      U.smul_mem ⟨(ρ g : GL (Fin n) k), Submodule.subset_span ⟨g, rfl⟩⟩ hv
    obtain ⟨W', hW', hc⟩ := h W hW
    let U' : Submodule (spanAlg ρ) (Fin n → k) :=
      { toAddSubmonoid := W'.toAddSubmonoid
        smul_mem' := fun a v hv => hinv W' hW' a v hv }
    refine ⟨U', ?_, ?_⟩
    · rw [Submodule.disjoint_def]
      exact fun v hv hv' => Submodule.disjoint_def.1 hc.disjoint v hv hv'
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have hv : v ∈ W ⊔ W' := by rw [hc.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
      exact Submodule.add_mem_sup hy hz
  let ψ : spanAlg ρ →ₗ[spanAlg ρ] (Fin n → Fin n → k) :=
    LinearMap.pi fun j => LinearMap.toSpanSingleton _ _ (Pi.single j 1)
  have hψ : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    ext i j
    have h1 : (a : Matrix (Fin n) (Fin n) k).mulVec ((Pi.single j 1 : Fin n → k)) i = 0 :=
      congrFun (congrFun ha j) i
    simpa using h1
  have hP : IsSemisimpleModule (spanAlg ρ) (Fin n → Fin n → k) :=
    instIsSemisimpleModuleForallOfFinite fun _ => Fin n → k
  exact IsSemisimpleModule.of_injective ψ hψ

theorem trace_form_nondegenerate :
    ∀ {Γ k : Type} [Group Γ] [Field k] [CharZero k] {n : ℕ} (ρ : Γ →* GL (Fin n) k),
      IsSSRep ρ → ∀ x ∈ spanAlg ρ,
        (∀ g : Γ, Matrix.trace (x * ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) = 0) →
        x = 0 := by
  intro Γ k _ _ _ n ρ h x hx ht
  have := semisimple_span ρ h
  have hA : ∀ a ∈ spanAlg ρ, (x * a).trace = 0 := by
    intro a ha
    rw [mem_spanAlg] at ha
    induction ha using Submodule.span_induction with
    | mem y hy => obtain ⟨g, rfl⟩ := hy; exact ht g
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, Matrix.trace_add, hy, hz, add_zero]
    | smul c y _ hy => rw [Matrix.mul_smul, Matrix.trace_smul, hy, smul_zero]
  let y : spanAlg ρ := ⟨x, hx⟩
  obtain ⟨C, hC⟩ := exists_isCompl (Submodule.span (spanAlg ρ) {y})
  have h1 : (1 : spanAlg ρ) ∈ Submodule.span (spanAlg ρ) {y} ⊔ C := by
    rw [hC.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.1 h1
  have key : ∀ z ∈ Submodule.span (spanAlg ρ) {y}, z * e = z := by
    intro z hz
    have h2 : z * f = z - z * e := by
      rw [eq_sub_iff_add_eq', ← mul_add, hef, mul_one]
    have h3 : z * f = 0 :=
      Submodule.disjoint_def.1 hC.disjoint _
        (h2 ▸ Submodule.sub_mem _ hz (Submodule.smul_mem _ z he)) (C.smul_mem z hf)
    rw [h3] at h2
    exact (sub_eq_zero.1 h2.symm).symm
  have he0 : (e : Matrix (Fin n) (Fin n) k) = 0 := by
    refine idem_eq_zero_of_trace _ (congrArg Subtype.val (key e he)) ?_
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 he
    show ((a : Matrix (Fin n) (Fin n) k) * x).trace = 0
    rw [Matrix.trace_mul_comm]
    exact hA a a.2
  have h4 : x * (e : Matrix (Fin n) (Fin n) k) = x :=
    congrArg Subtype.val (key y (Submodule.mem_span_singleton_self y))
  rw [← h4, he0, mul_zero]

end GlobalTheory.SemisimpleTraceForm
end

section

noncomputable section

open Polynomial

namespace GlobalTheory.Per.LangUnit

open GlobalTheory.Cyc.FontW

theorem onto_of_cpl' {l : ℕ} {M : Type} [AddCommGroup M] (hM : Cpl l M) (f : M →+ M)
    (h : ∀ y, ∃ x z, f x - y = l • z) : Function.Surjective f := by
  intro y
  have hstep : ∀ (r : ℕ) (x : M), f x - y ∈ Dv l r M →
      ∃ x', f x' - y ∈ Dv l (r + 1) M ∧ x' - x ∈ Dv l r M := by
    intro r x hx
    obtain ⟨u, hu⟩ := mem_Dv.1 hx
    obtain ⟨a, z, haz⟩ := h (-u)
    refine ⟨x + l ^ r • a, mem_Dv.2 ⟨z, ?_⟩, mem_Dv.2 ⟨a, by abel⟩⟩
    rw [pow_succ, mul_smul, ← haz, map_add (f := _), map_nsmul, add_sub_right_comm, ← hu, sub_neg_eq_add,
      smul_add, add_comm]
  choose nx hnx using hstep
  let g : (r : ℕ) → {x // f x - y ∈ Dv l r M} := fun r =>
    Nat.rec ⟨0, mem_Dv.2 ⟨_, by rw [pow_zero, one_smul]⟩⟩
      (fun r b => ⟨nx r b.1 b.2, (hnx r b.1 b.2).1⟩) r
  obtain ⟨L, hL⟩ := hM.2 (fun r => (g r).1) fun r => (hnx r (g r).1 (g r).2).2
  refine ⟨L, sub_eq_zero.1 (hM.1 _ fun r => ?_)⟩
  have e : f L - y = f (L - (g r).1) + (f (g r).1 - y) := by rw [map_sub]; abel
  rw [e]
  exact add_mem (Dv_map f (hL r)) (g r).2

variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [CommRing k] [CharP k p] [PerfectRing k p]

theorem eq_smul_of_coeff_zero {A : WittVector p k} (hA : A.coeff 0 = 0) : ∃ Z, A = p • Z := by
  have h0 : A ∈ Ideal.span {(p : WittVector p k)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, WittVector.constantCoeff_apply]
    exact hA
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 h0
  exact ⟨u, by rw [← hu, nsmul_eq_mul, mul_comm]⟩

theorem coeff_zero_frob_sub (ω X : WittVector p k) :
    (WittVector.frobenius X - ω * X).coeff 0 = X.coeff 0 ^ p - ω.coeff 0 * X.coeff 0 := by
  simp only [← WittVector.constantCoeff_apply, map_sub, map_mul]
  rw [WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP]
  simp only [WittVector.constantCoeff_apply]

theorem lang_unit
    (hroot : ∀ f : k[X], f.Monic → 0 < f.natDegree → ∃ x, f.IsRoot x)
    (ω : WittVector p k) (hω : IsUnit ω) :
    ∃ η : WittVector p k, IsUnit η ∧ WittVector.frobenius η = ω * η := by
  have hp1 : 1 < p := hp.out.one_lt
  haveI : Nontrivial k := CharP.nontrivial_of_char_ne_one hp.out.ne_one
  set ω₀ := ω.coeff 0 with hω₀
  have hu0 : IsUnit ω₀ := by
    rw [hω₀, ← WittVector.constantCoeff_apply]; exact hω.map _
  let f : WittVector p k →+ WittVector p k :=
    (WittVector.frobenius : WittVector p k →+* WittVector p k).toAddMonoidHom -
      AddMonoidHom.mulLeft ω
  have hf : ∀ X, f X = WittVector.frobenius X - ω * X := fun X => rfl

  have hmod : ∀ Y, ∃ X Z, f X - Y = p • Z := by
    intro Y
    obtain ⟨x, hx⟩ := hroot (X ^ p - (C ω₀ * X + C (Y.coeff 0)))
      (monic_X_pow_sub (by
        refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
        · exact (degree_C_mul_X_le _).trans_lt (by exact_mod_cast hp1)
        · exact (degree_C_le).trans_lt (by exact_mod_cast (by omega : 0 < p))))
      (by
        have hlow : (C ω₀ * X + C (Y.coeff 0)).natDegree < p := by
          refine (natDegree_add_le _ _).trans_lt (max_lt ?_ ?_)
          · exact ((natDegree_C_mul_le _ _).trans natDegree_X_le).trans_lt hp1
          · rw [natDegree_C]; omega
        rw [natDegree_sub_eq_left_of_natDegree_lt (by rwa [natDegree_X_pow]), natDegree_X_pow]
        omega)
    refine ⟨WittVector.teichmuller p x, eq_smul_of_coeff_zero ?_⟩
    have hx' : x ^ p - (ω₀ * x + Y.coeff 0) = 0 := by simpa using hx
    rw [← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, hf, coeff_zero_frob_sub, WittVector.teichmuller_coeff_zero,
      ← hω₀]
    rw [← hx']; ring

  obtain ⟨t₀, ht₀⟩ := hroot (X ^ (p - 1) - C ω₀) (monic_X_pow_sub_C _ (by omega))
    (by rw [natDegree_X_pow_sub_C _]; omega)
  have ht₀' : t₀ ^ (p - 1) = ω₀ := by simpa [sub_eq_zero] using ht₀
  have hut : IsUnit t₀ := (isUnit_pow_iff (by omega : p - 1 ≠ 0)).1 (ht₀' ▸ hu0)
  have htp : t₀ ^ p = ω₀ * t₀ := by
    rw [← ht₀', ← pow_succ, Nat.sub_add_cancel hp.out.one_le]
  set t := WittVector.teichmuller p t₀ with ht
  obtain ⟨Y, hY⟩ := eq_smul_of_coeff_zero (A := f t) (by
    rw [hf, coeff_zero_frob_sub, ht, WittVector.teichmuller_coeff_zero, ← hω₀, htp, sub_self])
  obtain ⟨Z, rfl⟩ := onto_of_cpl' (cpl_witt p k) f hmod Y
  refine ⟨t - p • Z, ?_, ?_⟩
  · have hj : -(p • Z) ∈ (⊥ : Ideal (WittVector p k)).jacobson :=
      IsAdicComplete.le_jacobson_bot (Ideal.span {(p : WittVector p k)})
        (neg_mem (Ideal.mem_span_singleton'.2 ⟨Z, by rw [nsmul_eq_mul, mul_comm]⟩))
    obtain ⟨u, hu⟩ : IsUnit t := hut.map (WittVector.teichmuller p)
    have h1 := Ideal.mem_jacobson_bot.1 hj (↑u⁻¹)
    have e : t - p • Z = (-(p • Z) * ↑u⁻¹ + 1) * u := by
      rw [add_mul, mul_assoc, Units.inv_mul, mul_one, one_mul, hu]; abel
    rw [e]
    exact h1.mul u.isUnit
  · rw [← sub_eq_zero, ← hf, map_sub, map_nsmul, hY, sub_self]

end GlobalTheory.Per.LangUnit

namespace GlobalTheory.Per

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc



theorem OCb_exists_root (l : ℕ) [Fact l.Prime] (f : (OCb l)[X]) (hf : f.Monic)
    (hd : 0 < f.natDegree) : ∃ x, f.IsRoot x := by
  haveI : IsAlgClosed (Cb l) := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1
  haveI : ValuationRing (OCb l) := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).2
  haveI : IsIntegrallyClosed (OCb l) :=
    (ValuationRing.integers (OCb l) (Cb l)).isIntegrallyClosed
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (f.map (algebraMap (OCb l) (Cb l))) (by
    rw [degree_map_eq_of_injective (IsFractionRing.injective (OCb l) (Cb l)),
      degree_eq_natDegree hf.ne_zero]
    exact_mod_cast hd.ne')
  have hint : IsIntegral (OCb l) z := ⟨f, hf, by rwa [IsRoot, eval_map_algebraMap] at hz⟩
  obtain ⟨x, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨x, IsFractionRing.injective (OCb l) (Cb l) ?_⟩
  rw [IsRoot, eval_map_algebraMap, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at hz
  rw [hz, map_zero]

theorem frobenius_eq_mul_solvable :
    ∀ (l : ℕ) [Fact l.Prime] (ω : (Ainf l)ˣ), ∃ η : (Ainf l)ˣ, WittVector.frobenius (η : Ainf l) = ω * η := by
  intro l _ ω
  obtain ⟨η, ⟨u, rfl⟩, h⟩ := GlobalTheory.Per.LangUnit.lang_unit (p := l) (k := OCb l)
    (OCb_exists_root l) (ω : Ainf l) ω.isUnit
  exact ⟨u, h⟩

end GlobalTheory.Per
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LinDesc

theorem gl_lc_td (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] [IsUltrametricDist F] (r : ℕ) :
    LocallyCompactSpace (GL (Fin r) F) ∧ TotallyDisconnectedSpace (GL (Fin r) F) := by
  refine ⟨?_, ?_⟩
  · haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) F) :=
      inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → F))
    exact (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin r) (Fin r) F)).locallyCompactSpace
  · haveI : TotallyDisconnectedSpace (Matrix (Fin r) (Fin r) F) :=
      inferInstanceAs (TotallyDisconnectedSpace (Fin r → Fin r → F))
    exact ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

theorem exists_cutoff_torus : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ f' : Gl r F → ℂ, IsTest f' → ∃ α : GL (Fin r) F → ℝ, IsLocallyConstant α ∧ HasCompactSupport α ∧ (∀ g, 0 ≤ α g) ∧ ∀ g : GL (Fin r) F, (∃ v w : Fin r → F, f' ((g : Matrix (Fin r) (Fin r) F) * companion p * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F), v, w, lam) ≠ 0) → ∀ s₀ : A.Kˣ, ∫ s, α (g * LinDesc.tm A hG s₀ * LinDesc.tm A hG s) ∂(LinDesc.unitsMeas A μK) = 1 := by
  intro F E _ _ _ _ _ A r τ p hG lam μK hμ f' hf'
  haveI := (Unram.lcF (F := F) (E := E))
  haveI := (Unram.ultraF (F := F) (E := E))
  obtain ⟨hlc, htd⟩ := gl_lc_td F r
  obtain ⟨hB, hH, -⟩ := GlobalTheory.T.etaleUnitsHaarMeasureDivAbs_isHaarMeasure F E A μK hμ
  have hZ : IsCompact (Prod.fst '' tsupport f') := hf'.2.isCompact.image continuous_fst
  obtain ⟨C, hC, hCg⟩ := (GlobalTheory.T.conjugates_separable_matrix_compact_mod_centralizer F E r).1 (companion p) (GlobalTheory.T.charpoly_companionMatrix_etaleGenerator_separable F E A r τ p hG) _ hZ
  obtain ⟨α, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_locallyConstant_cutoff_closedEmbedding (GL (Fin r) F) A.Kˣ (LinDesc.tm A hG)
    (GlobalTheory.T.isClosedEmbedding_leftMulMatrixPowerBasisUnitsHom F E A r τ p hG) (LinDesc.unitsMeas A μK) C hC
  refine ⟨α, h1, h2, h3, ?_⟩
  rintro g ⟨v, w, hne⟩ s₀
  have hmem : (g : Matrix (Fin r) (Fin r) F) * companion p * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) ∈
      Prod.fst '' tsupport f' := ⟨(_, v, w, lam), subset_tsupport _ (Function.mem_support.2 hne), rfl⟩
  obtain ⟨c, hc, t, ht, rfl⟩ := hCg g hmem
  obtain ⟨t₁, rfl⟩ := GlobalTheory.T.exists_unit_leftMulMatrix_of_commute_companion F E A r τ p hG t ht
  have := h4 c hc (t₁ * s₀)
  simpa [map_mul, mul_assoc] using this

end GlobalTheory.JR.LinDesc
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.fubini_cutoff_integral_generalLinear_torus : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (M : Meas r F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (α : GL (Fin r) F → ℝ) (Φ : GL (Fin r) F → ℂ), IsTest Φ → IsLocallyConstant α → HasCompactSupport α → (∀ g, 0 ≤ α g) → ∀ c : GL (Fin r) F, (∀ g, Φ g ≠ 0 → ∫ s, α (g * c * LinDesc.tm A hG s) ∂(LinDesc.unitsMeas A μK) = 1) → ∫ s, (letI := M.mG; ∫ g, Φ g * (α (g * c * LinDesc.tm A hG s) : ℂ) ∂M.μG) ∂(LinDesc.unitsMeas A μK) = (letI := M.mG; ∫ g, Φ g ∂M.μG) := by
  first | exact @GlobalTheory.JR.LinDesc.fubini_cutoff | exact GlobalTheory.JR.LinDesc.fubini_cutoff | (intros; apply GlobalTheory.JR.LinDesc.fubini_cutoff <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.fourier_descendedFunction_eq_partialFourier : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (M : Meas r F E) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ μ : Measure A.L, SelfDual μ (A.kerL ψ x) → ∀ (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → HasCompactSupport α → ∀ f : Hn r F E → ℂ, IsTest f → fourB μ (A.kerL ψ x) (A.descFn M Ax j lam α f) = A.descFn M Ax j lam α (fourU M ψ f) := by
  first | exact @GlobalTheory.JR.fourB_descFn | exact GlobalTheory.JR.fourB_descFn | (intros; apply GlobalTheory.JR.fourB_descFn <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_unitary_group_torus_cutoff : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F), A.IsGen τ p → ∀ (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) (hx : A.IsIsom x j) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) → ∀ (ν : Measure (unitary A.L)), ν.IsHaarMeasure → ∀ Z : Set (Matrix (Fin r) (Fin r) E), IsCompact Z → ∃ α : Matrix.unitaryGroup (Fin r) E → ℝ, IsLocallyConstant α ∧ HasCompactSupport α ∧ (∀ g, 0 ≤ α g) ∧ ∀ g : Matrix.unitaryGroup (Fin r) E, g.1 * Ax.1 * star g.1 ∈ Z → ∫ t, α (g * (A.uHom hx t)⁻¹) ∂ν = 1 := by
  first | exact @GlobalTheory.JR.TorusCutOff.exists_unitary_cutoff | exact GlobalTheory.JR.TorusCutOff.exists_unitary_cutoff | (intros; apply GlobalTheory.JR.TorusCutOff.exists_unitary_cutoff <;> assumption)
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_nonNorm_uniformizer_isStableGauss : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ G₁ : ℂ, IsStableGauss A ψ x μ 1 G₁ → ∃ ϖ : A.Kˣ, (¬ ∃ y, A.NL y = ϖ) ∧ IsStableGauss A ψ x μ ϖ (-(G₁ * ((A.absK ϖ : ℂ))⁻¹)) := by
  first | exact @GlobalTheory.JR.WeilQuad.NonNorm.gauss_at_uniformiser | exact GlobalTheory.JR.WeilQuad.NonNorm.gauss_at_uniformiser | (intros; apply GlobalTheory.JR.WeilQuad.NonNorm.gauss_at_uniformiser <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.isotypicProjector_mem_breuilKisinLattice : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι) (Δ : Descent P) (c : ZMod e) (v : Vec K a ι), v ∈ P.L → GlobalTheory.CokerL.isoProj Δ c v ∈ P.L := by
  first | exact @GlobalTheory.CokerL.isoProj_mem_L | exact GlobalTheory.CokerL.isoProj_mem_L | (intros; apply GlobalTheory.CokerL.isoProj_mem_L <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.sum_isotypicProjectors_eq_id : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι) (Δ : Descent P) (v : Vec K a ι), ∑ c : ZMod e, GlobalTheory.CokerL.isoProj Δ c v = v := by
  first | exact @GlobalTheory.CokerL.sum_isoProj | exact GlobalTheory.CokerL.sum_isoProj | (intros; apply GlobalTheory.CokerL.sum_isoProj <;> assumption)
end
