module

public import Formalism.LocalToGlobal.HermitianForms.Bundle009
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle004
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle003
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ExtendOneMulVecSingleLast
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle002
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle001
import Formalism.LocalToGlobal.HermitianForms.Bundle004
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

section Gen

theorem exists_proj {E : Type} [Field E] {N n : ℕ} (hN : n + 1 = N) (A : Matrix (Fin N) (Fin n) E) (z : Fin N → E)
    (hA : Function.Injective A.mulVec) (hz : ∀ x, A *ᵥ x ≠ z) :
    ∃ P : Matrix (Fin n) (Fin N) E, P * A = 1 ∧ P *ᵥ z = 0 := by
  subst hN
  have hB := isUnit_det_cols rfl A z hA hz
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) E :=
    Matrix.of (fun a (b : Fin (n + 1)) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a) with hBdef
  have h := nonsing_inv_mul B hB
  refine ⟨Matrix.of fun a j => B⁻¹ (Fin.castSucc a) j, ?_, ?_⟩
  · ext a b
    have e := congrFun (congrFun h (Fin.castSucc a)) (Fin.castSucc b)
    have hcol (j : Fin (n + 1)) : B j (Fin.castSucc b) = A j b := by
      simp [hBdef]
    simp only [Matrix.mul_apply, hcol, Matrix.one_apply, Fin.castSucc_inj] at e
    simpa [Matrix.mul_apply, Matrix.one_apply] using e
  · funext a
    have e := congrFun (congrFun h (Fin.castSucc a)) (Fin.last n)
    simp only [Matrix.mul_apply, hBdef, of_apply, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true, one_apply] at e
    simpa [mulVec, dotProduct, (Fin.castSucc_lt_last a).ne] using e

theorem cT_ext_unitary {A : Type} [CommRing A] (τ : A →+* A) {N n : ℕ} (I : Matrix (Fin N) (Fin n) A)
    (J : Matrix (Fin N) (Fin N) A) (G : Matrix (Fin N) (Fin N) A) (k : Matrix (Fin n) (Fin n) A)
    (hG : cT τ G * J * G = J) (hE : G * I = I * k) :
    cT τ k * (cT τ I * J * I) * k = cT τ I * J * I := by
  calc cT τ k * (cT τ I * J * I) * k = cT τ (I * k) * J * (I * k) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = cT τ (G * I) * J * (G * I) := by rw [hE]
    _ = cT τ I * (cT τ G * J * G) * I := by rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = cT τ I * J * I := by rw [hG]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem latS_mulVec (R : Type) [CommRing R] [Algebra F R] (S : Subring (E ⊗[F] R)) {n N : ℕ}
    (M : Matrix (Fin N) (Fin n) E) (Λ' : Submodule (𝓞 E) (Fin n → E)) (Λ : Submodule (𝓞 E) (Fin N → E))
    (hM : ∀ x ∈ Λ', M *ᵥ x ∈ Λ) :
    ∀ x ∈ latS (F := F) R S Λ', (M.map (inclE (F := F) R)) *ᵥ x ∈ latS (F := F) R S Λ := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x0, hx0, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨M *ᵥ x0, hM x0 hx0, ?_⟩
    funext i

    simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    have e : (M.map (inclE (F := F) R)) *ᵥ (a • x) = a • ((M.map (inclE (F := F) R)) *ᵥ x) := by
      rw [Subring.smul_def, Subring.smul_def, mulVec_smul]
    rw [e]; exact Submodule.smul_mem _ a hx

end Gen

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem exists_projP (Tf : FormsTiedSym D u Ch chOf) :
    ∃ P : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m)) D.host.E, P * iXm D = 1 ∧ P *ᵥ Tf.til.z0 = 0 := by
  obtain ⟨P, h1, h2⟩ := exists_proj (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) (iXm D) (fun i => Tf.til.z0 i / ((D.mem u).A.T : D.host.E))
    (iXm_mulVec_injective D) (quotient_not_in_range_symmetric Tf)
  refine ⟨P, h1, ?_⟩
  have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  have e : Tf.til.z0 = ((D.mem u).A.T : D.host.E) • (fun i => Tf.til.z0 i / ((D.mem u).A.T : D.host.E)) := by
    funext i; simp only [Pi.smul_apply, smul_eq_mul]; field_simp
  rw [e, mulVec_smul, h2, smul_zero]

theorem lat_in_out (Tf : FormsTiedSym D u Ch chOf) (P : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m)) D.host.E)
    (hP1 : P * iXm D = 1) (hPz : P *ᵥ Tf.til.z0 = 0) :
    (∀ x ∈ Tf.clsP.lev.Lb, iXm D *ᵥ x ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb) ∧
    (∀ y ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb, P *ᵥ y ∈ Tf.clsP.lev.Lb) := by
  have hL : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb =
      Tf.clsP.lev.Lb.map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {Tf.til.z0} := Tf.tilLat
  have hiX : ∀ x, iXm D *ᵥ x = iXc D x := fun x => by simp only [iXm, LinearMap.toMatrix'_mulVec]
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · rw [hL, hiX]
    exact Submodule.mem_sup_left (Submodule.mem_map_of_mem hx)
  · rw [hL] at hy
    obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy1
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy2
    have e1 : P *ᵥ ((iXc D).restrictScalars (𝓞 D.host.E) x) = x := by
      show P *ᵥ (iXc D x) = x
      rw [← hiX, mulVec_mulVec, hP1, one_mulVec]
    have e2 : P *ᵥ (a • Tf.til.z0) = 0 := by
      rw [← algebraMap_smul D.host.E a Tf.til.z0, mulVec_smul, hPz, smul_zero]
    rw [mulVec_add, e1, e2, add_zero]
    exact hx

theorem isExt_prV {z0 : Fin (D.R.N D.R.m) → D.host.E} (v : HeightOneSpectrum (𝓞 D.host.F))
    {k : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {G : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    (h : IsExt D z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) k G) :
    IsExt D z0 (inclE (F := D.host.F) (v.adicCompletion D.host.F)) (k.map (prV (E := D.host.E) v)) (G.map (prV (E := D.host.E) v)) := by
  obtain ⟨h1, h2⟩ := h
  have hc : (prV (E := D.host.E) v).comp (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) =
      inclE (F := D.host.F) (v.adicCompletion D.host.F) := RingHom.ext fun e => rfl
  refine ⟨?_, ?_⟩
  · have := congrArg (fun M => M.map (prV (E := D.host.E) v)) h1
    simp only [Matrix.map_mul, Matrix.map_map] at this
    rw [← RingHom.coe_comp, hc] at this
    exact this
  · funext i
    have := congrArg (fun w => prV (E := D.host.E) v (w i)) h2
    simp only at this
    exact (RingHom.map_mulVec _ _ _ _).symm.trans this



theorem lev_lat (Tf : FormsTiedSym D u Ch chOf)
    (k : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) k G.1)
    (hG : G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U) (v : HeightOneSpectrum (𝓞 D.host.F))
    (x : Fin (D.R.N D.R.m - 1) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :
    x ∈ latS (F := D.host.F) (v.adicCompletion D.host.F)
      (tensInt (F := D.host.F) (v.adicCompletion D.host.F) (intOE D.host.E) (v.adicCompletionIntegers D.host.F).toSubring) Tf.clsP.lev.Lb ↔
    (k.map (prV (E := D.host.E) v)) *ᵥ x ∈ latS (F := D.host.F) (v.adicCompletion D.host.F)
      (tensInt (F := D.host.F) (v.adicCompletion D.host.F) (intOE D.host.E) (v.adicCompletionIntegers D.host.F).toSubring) Tf.clsP.lev.Lb := by
  set S := tensInt (F := D.host.F) (v.adicCompletion D.host.F) (intOE D.host.E) (v.adicCompletionIntegers D.host.F).toSubring
  set Km := (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev
  have hGv : bc (prV (E := D.host.E) v) G ∈ levelVL (sigD D) (gramN D D.R.m le_rfl) v Km.Lb :=
    Km.Uloc_lev v (((Km.U_eq G).1 hG).2 v)
  have hst := (Subgroup.mem_inf.mp hGv).2
  have hGm : ((bc (prV (E := D.host.E) v) G : GL _ _) : Matrix _ _ _) = G.1.map (prV (E := D.host.E) v) := rfl
  obtain ⟨hEv, -⟩ := isExt_prV v hE
  obtain ⟨P, hP1, hPz⟩ := exists_projP Tf
  obtain ⟨hin, hout⟩ := lat_in_out Tf P hP1 hPz
  have hI := latS_mulVec (F := D.host.F) (v.adicCompletion D.host.F) S (iXm D) _ _ hin
  have hO := latS_mulVec (F := D.host.F) (v.adicCompletion D.host.F) S P _ _ hout
  have hPI : (P.map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) * ((iXm D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) = 1 := by
    rw [← Matrix.map_mul, hP1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hback : ∀ y, y = (P.map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) *ᵥ
      (((iXm D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) *ᵥ y) := fun y => by
    rw [mulVec_mulVec, hPI, one_mulVec]
  have hcomm : ∀ y, G.1.map (prV (E := D.host.E) v) *ᵥ (((iXm D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) *ᵥ y) =
      ((iXm D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) *ᵥ ((k.map (prV (E := D.host.E) v)) *ᵥ y) := fun y => by
    rw [mulVec_mulVec, hEv, ← mulVec_mulVec]
  have hs : ∀ y, y ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) S Km.Lb ↔
      G.1.map (prV (E := D.host.E) v) *ᵥ y ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) S Km.Lb := fun y => by
    rw [← hGm]; exact hst y
  constructor
  · intro hx
    have h1 := (hs _).1 (hI x hx)
    rw [hcomm] at h1
    rw [hback ((k.map (prV (E := D.host.E) v)) *ᵥ x)]
    exact hO _ h1
  · intro hx
    have h1 := hI _ hx
    rw [← hcomm] at h1
    rw [hback x]
    exact hO _ ((hs _).2 h1)

theorem lev_unit (Tf : FormsTiedSym D u Ch chOf)
    (k : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) k G.1)
    (hG : G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U) :
    cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) k *
      (gramP D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * k =
      (gramP D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  set Km := (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev
  have hU : G ∈ UPts (sigD D) (gramN D D.R.m le_rfl) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := ((Km.U_eq G).1 hG).1
  have hc : (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).comp (sigD D : D.host.E →+* D.host.E) =
      (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).comp (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    ext e
    simp [sigR, inclE, Algebra.TensorProduct.includeLeftRingHom_apply]
  have hJ : (gramP D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) =
      cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((iXm D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) *
        (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) *
        (iXm D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    rw [Formalism.UG.P.cT_map _ _ _ hc, ← Matrix.map_mul, ← Matrix.map_mul, gramP_eq]
    rfl
  rw [hJ]
  exact cT_ext_unitary _ _ _ _ _ hU hE.1

theorem lev_isUnit (Tf : FormsTiedSym D u Ch chOf)
    (k : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) k G.1) :
    IsUnit k.det := by
  obtain ⟨P, hP1, -⟩ := exists_projP Tf
  obtain ⟨Gi, hGi⟩ : ∃ Gi : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      Gi * G.1 = 1 := ⟨(G⁻¹ : GL _ _).1, by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]⟩
  have hQ : HMul.hMul (HMul.hMul Gi ((iXm D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))) k = (iXm D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    rw [Matrix.mul_assoc, ← hE.1, ← Matrix.mul_assoc, hGi, Matrix.one_mul]
  have hl : HMul.hMul (HMul.hMul (P.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) (HMul.hMul Gi ((iXm D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))))) k = 1 := by
    rw [Matrix.mul_assoc, hQ, ← Matrix.map_mul, hP1, Matrix.map_one _ (map_zero _) (map_one _)]
  exact Matrix.isUnit_det_of_left_inverse hl

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix

structure CrdFacts (D : D7) : Prop where
  conj : ∀ (φ : D.host.E →+* ℂ) (x : D.host.E), φ ((sigD D : D.host.E →+* D.host.E) x) = (starRingEnd ℂ) (φ x)
  defN : ∀ (φ : D.host.E →+* ℂ) (x : Fin (D.R.N D.R.m) → D.host.E), ∃ r : ℝ, 0 ≤ r ∧
    φ (hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) x x) = r ∧ (r = 0 → x = 0)
  iso : ∀ x x', hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (iXc D x) (iXc D x') =
    hform (sigD D : D.host.E →+* D.host.E) (gramP D) x x'
  orth : ∀ x, hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (iXc D x) (zc D) = 0 ∧
    hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (zc D) (iXc D x) = 0
  span : ∀ y, ∃ (x : Fin (D.R.N D.R.m - 1) → D.host.E) (s : D.host.E), y = iXc D x + s • zc D

section Unit

variable {E : Type} [Field E] {n : ℕ}

theorem hform_eq_dot (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hform σ J x y = dotProduct (fun i => σ (x i)) (J *ᵥ y) := by
  simp only [hform, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem hform_UJ (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) E) (hg : cT σ g * J * g = J)
    (x y : Fin n → E) : hform σ J (g *ᵥ x) (g *ᵥ y) = hform σ J x y := by
  have h1 : (fun i => σ ((g *ᵥ x) i)) = (g.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i; simp [mulVec, dotProduct, map_sum]
  have key : ∀ (A : Matrix (Fin n) (Fin n) E) (v w : Fin n → E), (A *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (Aᵀ *ᵥ w) := by
    intro A v w; rw [dotProduct_mulVec, vecMul_transpose]
  rw [hform_eq_dot, hform_eq_dot, h1, key, mulVec_mulVec, mulVec_mulVec]
  congr 2

end Unit

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem ga_herm (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (x y : Fin (D.R.N D.R.m) → D.host.E) :
    hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) ((Tf.til.ga c).1.1 *ᵥ x) ((Tf.til.ga c).1.1 *ᵥ y) =
      hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) x y :=
  hform_UJ _ _ _ (Tf.til.ga c).2 x y

section Glue

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem mulLat_mulLat {E : Type} [Field E] [NumberField E] {n : ℕ} (A B : Matrix (Fin n) (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) : mulLat A (mulLat B L) = mulLat (A * B) L := by
  unfold mulLat
  rw [← Submodule.map_comp]
  congr 1
  ext x i
  simp

theorem fv_pr_congr (Tf : FormsTiedSym D u Ch chOf) (v : (D.mem u).A.vT) (a b : (D.mem u).C.cls D.R.m) (hab : a = b)
    (x : Fin (D.R.N D.R.m) → D.host.E) (hxa : x ∈ Ld D u D.R.m le_rfl a) (hxb : x ∈ Ld D u D.R.m le_rfl b) :
    (D.fm u).fv D.R.m v a ((Tf.lv D.R.m le_rfl).pr v a ⟨x, hxa⟩) =
      (D.fm u).fv D.R.m v b ((Tf.lv D.R.m le_rfl).pr v b ⟨x, hxb⟩) := by
  subst hab; rfl

theorem T_mem_Pv (Tf : FormsTiedSym D u Ch chOf) (v : (D.mem u).A.vT) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ Tf.atT.Pv v := by
  let pb : 𝓞 D.host.E := ⟨D.host.conj (Tf.atT.piU : D.host.E), (Tf.atT.piU.2).map (D.host.conj : D.host.E →+* D.host.E).toIntAlgHom⟩
  have hT : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) = Tf.atT.piU * pb := by
    apply RingOfIntegers.ext
    have e1 : ((Tf.atT.piU * pb : 𝓞 D.host.E) : D.host.E) = (Tf.atT.piU : D.host.E) * (pb : D.host.E) := rfl
    have e2 : ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) : D.host.E) = (((D.mem u).A.T : ℕ) : D.host.E) := by simp
    rw [e1, e2, ← Tf.atT.piU_norm]; rfl
  rw [hT]
  show Tf.atT.res v (Tf.atT.piU * pb) = 0
  rw [map_mul, Tf.atT.res_pi, zero_mul]

theorem til_eq_fix (Tf : FormsTiedSym D u Ch chOf) (hC : CrdFacts D)
    (hSD : ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hdeg : Module.finrank ℚ D.host.E < (D.mem u).A.T - 1) (v : (D.mem u).A.vT)
    (c c' : (D.fm u).clsP) (h : (D.fm u).til c = (D.fm u).til c') :
    ((Tf.til.ga c').1.1 * ((Tf.til.ga c)⁻¹).1.1) *ᵥ Tf.til.z0 = Tf.til.z0 := by
  have hTp : ((D.mem u).A.T : ℕ).Prime := (D.mem u).A.T_prime
  set σ : D.host.E →+* D.host.E := (sigD D : D.host.E →+* D.host.E) with hσdef
  set J := gramN D D.R.m le_rfl with hJ
  set z0 := Tf.til.z0 with hz0
  set g1 := (Tf.til.ga c).1.1 with hg1
  set g2 := (Tf.til.ga c').1.1 with hg2
  set gi := ((Tf.til.ga c)⁻¹).1.1 with hgi
  have hgi1 : gi * g1 = 1 := by simp [hgi, hg1]
  have hg1i : g1 * gi = 1 := by simp [hgi, hg1]
  obtain ⟨a, ha⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  rw [← hz0] at ha
  have hzz : hform σ J z0 z0 = (((D.mem u).A.T : ℕ) : D.host.E) := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
  have ha0 : a ≠ 0 := by
    intro h0
    have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hTp.ne_zero
    rw [ha, h0, zero_smul] at hzz
    apply hT0; rw [← hzz]; simp [hform]
  have horth : ∀ x, hform σ J (iXc D x) z0 = 0 ∧ hform σ J z0 (iXc D x) = 0 := fun x => by
    rw [ha, hform_smul_right, hform_smul_left, (hC.orth x).1, (hC.orth x).2]; simp
  have hspan : ∀ y, ∃ (x : Fin (D.R.N D.R.m - 1) → D.host.E) (s : D.host.E), y = iXc D x + s • z0 := fun y => by
    obtain ⟨x, s, hy⟩ := hC.span y
    exact ⟨x, s / a, by rw [hy, ha, smul_smul, div_mul_cancel₀ s ha0]⟩
  have hUgi : cT σ gi * J * gi = J := ((Tf.til.ga c)⁻¹).2
  have hγ : ∀ x y, hform σ J ((g2 * gi) *ᵥ x) ((g2 * gi) *ᵥ y) = hform σ J x y := fun x y => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, ga_herm Tf c', hform_UJ σ J gi hUgi]
  have hlat : mulLat (g2 * gi) ((Tf.clsP.lat c).map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0}) =
      (Tf.clsP.lat c').map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0} := by
    rw [← Tf.til.til_lat c, ← Tf.til.til_lat c', mulLat_mulLat, Matrix.mul_assoc, hgi1, Matrix.mul_one, h]
  have hres : ∀ y : Fin (D.R.N D.R.m) → D.host.E,
      (∀ w ∈ (Tf.clsP.lat c).map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0},
        hform σ J w y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) →
      ∀ r r' : 𝓞 D.host.E, (r : D.host.E) = hform σ J z0 y → (r' : D.host.E) = hform σ J z0 ((g2 * gi) *ᵥ y) →
        r - r' ∈ Tf.atT.Pv v := by
    intro y hy r r' hr hr'
    have hxy : g1 *ᵥ (gi *ᵥ y) = y := by rw [mulVec_mulVec, hg1i, one_mulVec]
    have hxa : gi *ᵥ y ∈ Ld D u D.R.m le_rfl ((D.fm u).til c) := by
      apply Submodule.subset_span
      intro l hl
      have hl' : g1 *ᵥ l ∈ (Tf.clsP.lat c).map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0} := by
        rw [← Tf.til.til_lat c]; exact Submodule.mem_map.2 ⟨l, hl, rfl⟩
      have := hy _ hl'
      rw [← hxy, ga_herm Tf c] at this
      exact this
    have hxb : gi *ᵥ y ∈ Ld D u D.R.m le_rfl ((D.fm u).til c') := h ▸ hxa
    have e1 := Tf.til.til_fv v c ⟨gi *ᵥ y, hxa⟩ r (by rw [hr]; show _ = hform σ J z0 (g1 *ᵥ (gi *ᵥ y)); rw [hxy])
    have e2 := Tf.til.til_fv v c' ⟨gi *ᵥ y, hxb⟩ r' (by rw [hr', ← mulVec_mulVec])
    rw [fv_pr_congr Tf v _ _ h _ hxa hxb, e2] at e1
    show Tf.atT.res v (r - r') = 0
    rw [map_sub, e1, sub_self]
  exact fix_orthogonal_vector σ hC.conj J (gramP D) hC.defN (iXc D) z0 hC.iso horth hspan _ hTp hdeg hzz
    (Tf.clsP.lat c) (Tf.clsP.lat c')
    ⟨fun y hy => by
      have : y ∈ dualSet σ (gramP D) (Tf.clsP.lat c') := fun x hx => hy x hx
      rw [hSD c'] at this; exact this,
     fun x hx y hy => by
      have : y ∈ dualSet σ (gramP D) (Tf.clsP.lat c') := by rw [hSD c']; exact hy
      exact this x hx⟩
    (g2 * gi) hγ hlat (Tf.atT.Pv v) inferInstance (T_mem_Pv Tf v) hres

theorem til_eq_ext (Tf : FormsTiedSym D u Ch chOf) (hC : CrdFacts D)
    (hSD : ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hdeg : Module.finrank ℚ D.host.E < (D.mem u).A.T - 1) (v : (D.mem u).A.vT)
    (c c' : (D.fm u).clsP) (h : (D.fm u).til c = (D.fm u).til c') :
    ∃ δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E,
      IsExt D Tf.til.z0 (RingHom.id D.host.E) δ ((Tf.til.ga c').1.1 * ((Tf.til.ga c)⁻¹).1.1) ∧
      ∀ x y, hform (sigD D : D.host.E →+* D.host.E) (gramP D) (δ *ᵥ x) (δ *ᵥ y) =
        hform (sigD D : D.host.E →+* D.host.E) (gramP D) x y := by
  have hTp : ((D.mem u).A.T : ℕ).Prime := (D.mem u).A.T_prime
  have hfix := til_eq_fix Tf hC hSD hdeg v c c' h
  set σ : D.host.E →+* D.host.E := (sigD D : D.host.E →+* D.host.E) with hσdef
  set J := gramN D D.R.m le_rfl with hJ
  set z0 := Tf.til.z0 with hz0
  set γ := (Tf.til.ga c').1.1 * ((Tf.til.ga c)⁻¹).1.1 with hγdef
  obtain ⟨a, ha⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  rw [← hz0] at ha
  have hzz : hform σ J z0 z0 = (((D.mem u).A.T : ℕ) : D.host.E) := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hTp.ne_zero
  have ha0 : a ≠ 0 := by
    intro h0
    have hzz' := hzz
    rw [ha, h0, zero_smul] at hzz'
    apply hT0; rw [← hzz']; simp [hform]
  have horth : ∀ x, hform σ J (iXc D x) z0 = 0 ∧ hform σ J z0 (iXc D x) = 0 := fun x => by
    rw [ha, hform_smul_right, hform_smul_left, (hC.orth x).1, (hC.orth x).2]; simp
  have hspan : ∀ y, ∃ (x : Fin (D.R.N D.R.m - 1) → D.host.E) (s : D.host.E), y = iXc D x + s • z0 := fun y => by
    obtain ⟨x, s, hy⟩ := hC.span y
    exact ⟨x, s / a, by rw [hy, ha, smul_smul, div_mul_cancel₀ s ha0]⟩
  have hUgi : cT σ ((Tf.til.ga c)⁻¹).1.1 * J * ((Tf.til.ga c)⁻¹).1.1 = J := ((Tf.til.ga c)⁻¹).2
  have hγ : ∀ x y, hform σ J (γ *ᵥ x) (γ *ᵥ y) = hform σ J x y := fun x y => by
    rw [hγdef, ← mulVec_mulVec, ← mulVec_mulVec, ga_herm Tf c', hform_UJ σ J _ hUgi]
  obtain ⟨δ, hδ, hδi⟩ := fix_restrict σ J (gramP D) (iXc D) (iXc_injective D) z0 hC.iso horth hspan
    (by rw [hzz]; exact hT0) γ hγ hfix
  refine ⟨δ, ⟨?_, ?_⟩, hδi⟩
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Matrix.toLin'_apply, ← mulVec_mulVec]
    show γ *ᵥ ((iXm D).map (RingHom.id D.host.E) *ᵥ x) = (iXm D).map (RingHom.id D.host.E) *ᵥ (δ *ᵥ x)
    have hm : (iXm D).map (RingHom.id D.host.E) = iXm D := by ext i j; rfl
    rw [hm, iXm, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hδ]
  · have : (fun a => (RingHom.id D.host.E) (z0 a)) = z0 := rfl
    rw [this]; exact hfix

theorem til_ext (Tf : FormsTiedSym D u Ch chOf) {R : Type} [CommRing R] (φ : D.host.E →+* R)
    (g' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) R) :
    ∃ g : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) R, IsExt D Tf.til.z0 φ g' g ∧ (IsUnit g'.det → IsUnit g.det) := by
  obtain ⟨G, h1, h2, h3⟩ := ext_general φ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) (iXm D)
    (fun a => Tf.til.z0 a / ((D.mem u).A.T : D.host.E)) (by exact bZ_isUnitS Tf) g'
  refine ⟨G, ⟨h1, ?_⟩, h3⟩
  have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  have hz : (fun a => φ (Tf.til.z0 a)) = φ ((D.mem u).A.T : D.host.E) • (fun a => φ (Tf.til.z0 a / ((D.mem u).A.T : D.host.E))) := by
    funext a
    rw [Pi.smul_apply, smul_eq_mul, ← map_mul, mul_div_cancel₀ _ hT]
  rw [hz, mulVec_smul, h2]

end Glue

end Formalism.L2.GlobalTheoryTheory.Br
end
end
