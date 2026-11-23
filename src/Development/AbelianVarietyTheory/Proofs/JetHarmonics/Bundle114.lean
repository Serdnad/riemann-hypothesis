module

public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.HermitianCurvature.CompositeFormulaLevelZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseIndexConstantInjective
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle087
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle038
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle092
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle021
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.RealPlaceAnalysis.Bundle005
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle064
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle041
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
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
import Formalism.HermitianCurvature.StatementFr
import Formalism.HermitianCurvature.Bundle001
import Formalism.HermitianCurvature.StatementWd

@[expose] public section

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.DualFrame

theorem exists_linearIndependent_extend {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (v : Fin n → V)
    (hv : LinearIndependent ℂ v) (m : ℕ) (hm : n + m ≤ Module.finrank ℂ V) :
    ∃ w : Fin (n + m) → V, LinearIndependent ℂ w ∧ ∀ j, w (Fin.castAdd m j) = v j := by
  induction m with
  | zero => exact ⟨v, hv, fun j => rfl⟩
  | succ m ih =>
    obtain ⟨w, hw, hwv⟩ := ih (by omega)
    have hx : ∃ x, x ∉ Submodule.span ℂ (Set.range w) := by
      by_contra h
      have htop : Submodule.span ℂ (Set.range w) = ⊤ :=
        eq_top_iff.mpr (fun x _ => by_contra (fun hx => h ⟨x, hx⟩))
      have h1 := finrank_range_le_card (R := ℂ) (b := w)
      rw [Set.finrank, htop, finrank_top, Fintype.card_fin] at h1
      omega
    obtain ⟨x, hx⟩ := hx
    refine ⟨Fin.snoc (α := fun _ => V) w x, linearIndependent_finSnoc.mpr ⟨hw, hx⟩, fun j => ?_⟩
    have hj : (Fin.castAdd (m + 1) j : Fin (n + (m + 1))) = Fin.castSucc (Fin.castAdd m j) := Fin.ext rfl
    rw [hj, Fin.snoc_castSucc, hwv]

theorem linearIndependent_fvec (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z') (h0 : z' ≠ 0) :
    LinearIndependent ℂ (fvec k r z') := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hs : ∀ d, ∑ i : Fin r, g (Fin.castSucc i) * bvec (eI k r i) d + g (Fin.last r) * z' d = 0 := by
    intro d
    have := congrFun hg d
    rw [Fin.sum_univ_castSucc] at this
    simpa [fvec] using this
  have hlast : g (Fin.last r) = 0 := by
    obtain ⟨d, hd⟩ := Function.ne_iff.mp h0
    have hd' : r ≤ d.val := by
      by_contra hlt
      exact hd (hz d (Or.inl (by omega)))
    have := hs d
    have hb : ∀ i : Fin r, bvec (eI k r i) d = 0 := by
      intro i
      have hne : d ≠ eI k r i := by
        intro h
        have := congrArg Fin.val h
        simp [eI] at this
        omega
      simp [bvec, hne]
    simp only [hb, mul_zero, Finset.sum_const_zero, zero_add] at this
    exact (mul_eq_zero.mp this).resolve_right hd
  intro i
  refine Fin.lastCases hlast (fun a => ?_) i
  have := hs (eI k r a)
  rw [hlast, zero_mul, add_zero] at this
  rw [Finset.sum_eq_single a] at this
  · simpa [bvec] using this
  · intro b _ hb
    have hne : eI k r a ≠ eI k r b := by
      intro h
      apply hb
      have := congrArg Fin.val h
      simp [eI] at this
      exact Fin.ext this.symm
    simp [bvec, hne]
  · simp

theorem exists_dual_matrix (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (e : Fin (r + 1 + (r + k)) ≃ Fin (2 * r + k + 1)) (hz : inWb k r z') (hT : 0 < Tz k r z') :
    ∃ Q : Matrix (Fin (r + 1 + (r + k))) (Fin (r + 1 + (r + k))) ℂ, Q.det ≠ 0 ∧
      (∀ (i j : Fin (r + 1)), ∑ d, Q (Fin.castAdd (r + k) i) d * fvec k r z' j (e d) = if i = j then 1 else 0) ∧
      ∀ (i : Fin (r + k)) (j : Fin (r + 1)), ∑ d, Q (Fin.natAdd (r + 1) i) d * fvec k r z' j (e d) = 0 := by
  have hz0 : z' ≠ 0 := by
    rintro rfl
    simp [Tz, herm] at hT
  have hli := linearIndependent_fvec k r z' hz hz0
  set u : Fin (r + 1) → Fin (r + 1 + (r + k)) → ℂ := fun j d => fvec k r z' j (e d) with hu
  have hul : LinearIndependent ℂ u :=
    hli.map' (LinearEquiv.funCongrLeft ℂ ℂ e).toLinearMap (LinearEquiv.ker _)
  obtain ⟨w, hw, hwu⟩ := exists_linearIndependent_extend u hul (r + k)
    (by rw [Module.finrank_fin_fun])
  set A : Matrix (Fin (r + 1 + (r + k))) (Fin (r + 1 + (r + k))) ℂ := Matrix.of w with hA
  have hAu : IsUnit A := Matrix.linearIndependent_rows_iff_isUnit.mp hw
  have hdet : IsUnit A.transpose.det := by
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det A).mp hAu
  have hQ : (A.transpose)⁻¹ * A.transpose = 1 := Matrix.nonsing_inv_mul _ hdet
  have hcol : ∀ (i : Fin (r + 1 + (r + k))) (j : Fin (r + 1)),
      ∑ d, (A.transpose)⁻¹ i d * fvec k r z' j (e d) = if i = Fin.castAdd (r + k) j then 1 else 0 := by
    intro i j
    have := congrFun (congrFun hQ i) (Fin.castAdd (r + k) j)
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    simp [hA, hwu, hu]
  refine ⟨(A.transpose)⁻¹, ?_, fun i j => ?_, fun i j => ?_⟩
  · intro h
    have := congrArg Matrix.det hQ
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  · rw [hcol]
    simp [Fin.castAdd_inj]
  · rw [hcol]
    have : Fin.natAdd (r + 1) i ≠ Fin.castAdd (r + k) j := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [this]

end GlobalTheory.HatNF.DualFrame
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

theorem doubleCoset_of_zeta_eq :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (c : Fin P.r → ℂ) (g g' : Q.Mx P.k P.r), (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' → (c, g') ∈ Q.DomR P.k P.r Bs.z Bs.z' → P5.zeta P.k P.r Bs.z Bs.z' g = P5.zeta P.k P.r Bs.z Bs.z' g' → ∃ h ∈ UWset P.k P.r Bs.z, ∃ h' ∈ UWset P.k P.r Bs.z', g' = h * g * h' := by
  intro Wp Wq _ _ _ _ _ _ P Bs c g g' hg hg' hζ
  obtain ⟨a, ha, b, hb, e⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp Bs.k_pos Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos Bs.sec
    hg.2.1 hg.2.2
  obtain ⟨a', ha', b', hb', e'⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp Bs.k_pos Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos Bs.sec
    hg'.2.1 hg'.2.2
  unfold P5.zeta at hζ
  dsimp only at e e'
  rw [← hζ] at e'
  generalize NF.muZ P.k P.r Bs.μsec (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) g) = m at e e'
  refine ⟨a' * a⁻¹, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul ha' (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv ha), b⁻¹ * b',
    Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hb) hb', ?_⟩
  have h1 := Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul ha
  have h2 := Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hb
  rw [e', e]
  calc a' * m * b' = a' * (a⁻¹ * a) * m * (b * b⁻¹) * b' := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one]
    _ = a' * a⁻¹ * (a * m * b) * (b⁻¹ * b') := by simp only [Matrix.mul_assoc]

end GlobalTheory.HatNF
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

noncomputable section
namespace GlobalTheory
namespace CapelliModel

open Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.PBG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem mem_lev {g : B.Mat k r} : g ∈ Q.Glev k r 0 ∩ Set.univ ↔ g ∈ B.GV k r :=
  ⟨fun h => h.1.1, fun h => ⟨⟨h, fun a ha => absurd ha (by simp)⟩, trivial⟩⟩

theorem smooth_iff {f : B.Mat k r → F} :
    Q.SmoothLev k r 0 Set.univ f ↔ B.CkOn ⊤ (B.GV k r) f := by
  constructor
  · intro h g₀ hg₀
    obtain ⟨U, f', hU, hg, hf, he⟩ := h g₀ (mem_lev.2 hg₀)
    exact ⟨U, f', hU, hg, hf, fun g hgU hgG => he g hgU (mem_lev.2 hgG).1⟩
  · intro h g₀ hg₀
    obtain ⟨U, f', hU, hg, hf, he⟩ := h g₀ (mem_lev.1 hg₀)
    exact ⟨U, f', hU, hg, hf, fun g hgU hgG => he g hgU hgG.1⟩

theorem dLR_zero (u v : List (B.Mat k r)) : B.dLR u v (0 : B.Mat k r → F) = 0 := by
  have h1 : B.Rw v (0 : B.Mat k r → F) = 0 := by
    unfold B.Rw
    induction v with
    | nil => rfl
    | cons X v ih =>
      rw [List.foldr_cons, ih]
      funext g
      simp [RdV]
  unfold B.dLR
  rw [h1]
  induction u with
  | nil => rfl
  | cons X u ih =>
    rw [List.foldr_cons, ih]
    funext g
    simp [B.LdV]

theorem inCC_zero (A : ℝ) (m : ℕ) : B.InCC A m (0 : B.Mat k r → F) := by
  refine ⟨0, fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩, ?_⟩
  intro u v _ _ _ g _
  simp [dLR_zero]

abbrev Sm (k r : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] := VS k r 0 Set.univ F

abbrev Eu (k r : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] (a b : Fin (2 * r + k + 1)) :
    Module.End ℂ (Sm k r F) := E0 isOpen_univ a b

theorem sm_ext (v v' : Sm k r F) (h : ∀ g ∈ B.GV k r, (v : B.Mat k r → F) g = (v' : B.Mat k r → F) g) :
    v = v' := by
  refine Subtype.ext (funext fun g => ?_)
  by_cases hg : g ∈ Q.Glev k r 0 ∩ Set.univ
  · exact h g (mem_lev.1 hg)
  · rw [v.2.2 g hg, v'.2.2 g hg]

theorem ev_Eu (a b : Fin (2 * r + k + 1)) (v : Sm k r F) (g : B.Mat k r) (hg : g ∈ B.GV k r) :
    (Eu k r F a b v : B.Mat k r → F) g = Q.EH k r a b (v : B.Mat k r → F) g := by
  have := ev_E (i := 0) isOpen_univ (c0 a) (c0 b) v (mem_lev.2 hg)
  rwa [position_level_zero_coord, position_level_zero_coord] at this

theorem qminorOp_cast {n t t' : ℕ} (h : t = t')
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → F) → (Matrix (Fin n) (Fin n) ℂ → F))
    (a : Fin t' → Fin n) (a' : Fin t → Fin n) (ha : ∀ j, a' j = a (Fin.cast h j)) (u : ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → F) : qminorOp Eop a' a' u f = qminorOp Eop a a u f := by
  subst h
  have : a' = a := funext ha
  rw [this]

theorem CV_eq (Y : ℂ) (f : B.Mat k r → F) :
    Q.CV k r Y f = qminorOp (Q.EH k r) id id (Y + (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2) f := by
  have hm : Q.mdim k r 0 = 2 * r + k + 1 := by simp [Q.mdim]
  unfold Q.CV Q.capL Q.uC
  rw [qminorOp_cast hm _ id _ (fun j => by ext; simp [Q.posL]), hm]

theorem ev_qdet (Y : ℂ) (v : Sm k r F) (g : B.Mat k r) (hg : g ∈ B.GV k r) :
    (qdet (Eu k r F) (Y + (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2) v : B.Mat k r → F) g =
      Q.CV k r Y (v : B.Mat k r → F) g := by
  rw [CV_eq]
  exact quantum_minor_level_eq_hat isOpen_univ id id _ v g (mem_lev.2 hg)

def eig (k r : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] (χ : ℂ → ℂ) (A : ℝ) :
    Submodule ℂ (Sm k r F) where
  carrier := {v | (∀ m : ℕ, B.InCC A m (v : B.Mat k r → F)) ∧ ∀ u : ℂ, qdet (Eu k r F) u v = χ u • v}
  zero_mem' := ⟨fun m => inCC_zero A m, fun u => by simp⟩
  add_mem' := by
    rintro v w ⟨hv, hv'⟩ ⟨hw, hw'⟩
    refine ⟨fun m => ?_, fun u => by rw [map_add (f := _), hv', hw', smul_add]⟩
    obtain ⟨c, hc⟩ := hv m
    obtain ⟨c', hc'⟩ := hw m
    exact ⟨_, (Formalism.FourierDecayAlt.P.matrix_coefficient_linear k r F A m _ _ c c' 1 hc hc').1⟩
  smul_mem' := by
    rintro a v ⟨hv, hv'⟩
    refine ⟨fun m => ?_, fun u => by rw [map_smul, hv', smul_comm]⟩
    obtain ⟨c, hc⟩ := hv m
    exact ⟨_, (Formalism.FourierDecayAlt.P.matrix_coefficient_linear k r F A m _ _ c c a hc hc).2⟩


open Classical in
def mulOp (k r : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] (c : B.Mat k r → ℂ) :
    Module.End ℂ (Sm k r F) :=
  if h : B.CkOn ⊤ (B.GV k r) c then Mh isOpen_univ c (smooth_iff.2 h) else 0

theorem glRel_of_intertwine {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ W) (ι : W →ₗ[ℂ] V)
    (hι : Function.Injective ι) (h : ∀ a b w, ι (E' a b w) = E a b (ι w)) (hE : GlRel E) : GlRel E' := by
  intro a b c d
  refine LinearMap.ext fun w => hι ?_
  have := LinearMap.congr_fun (hE a b c d) (ι w)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, h] at this ⊢
  rw [this]
  congr 1 <;> split_ifs <;> simp [h]

end CapelliModel


open CapelliModel Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.PBG in
theorem capelli_module_model : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (A : ℝ), ∃ (V W : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : AddCommGroup W) (_ : Module ℂ W) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ V) (E' : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ W) (ι : W →ₗ[ℂ] V) (ev : V →ₗ[ℂ] (B.Mat k r → (Wq →L[ℂ] Wp))) (mul : (B.Mat k r → ℂ) → Module.End ℂ V), GlRel E ∧ GlRel E' ∧ (∀ a b w, ι (E' a b w) = E a b (ι w)) ∧ (∀ (u : ℂ) (w : W), qdet E' u w = (∏ s, (u + ((lam s : ℂ) - (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2))) • w) ∧ (∀ v, B.CkOn ⊤ (B.GV k r) (ev v)) ∧ (∀ v v', (∀ g ∈ B.GV k r, ev v g = ev v' g) → v = v') ∧ (∀ w, ∀ m : ℕ, B.InCC A m (ev (ι w))) ∧ (∀ f : B.Mat k r → (Wq →L[ℂ] Wp), (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A) m (f)) → (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → ∃ w, ∀ g ∈ B.GV k r, ev (ι w) g = f g) ∧ (∀ a b v, ∀ g ∈ B.GV k r, ev (E a b v) g = Q.EH k r a b (ev v) g) ∧ (∀ (Y : ℂ) v, ∀ g ∈ B.GV k r, ev (qdet E (Y + (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2) v) g = Q.CV k r Y (ev v) g) ∧ (∀ c : B.Mat k r → ℂ, B.CkOn ⊤ (B.GV k r) c → (∀ v, ∀ g ∈ B.GV k r, ev (mul c v) g = c g • ev v g) ∧ ∀ a b v, ∀ g ∈ B.GV k r, ev (E a b (mul c v)) g = c g • ev (E a b v) g + Q.EH k r a b c g • ev v g) := by
  intro k r Wp Wq _ _ _ _ _ _ lam A
  let χ : ℂ → ℂ := fun u => ∏ s, (u + ((lam s : ℂ) - (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2))
  have hgl : GlRel (Eu k r (Wq →L[ℂ] Wp)) := level_zero_derivation_relation isOpen_univ
  have hst : ∀ a b, ∀ v ∈ eig k r (Wq →L[ℂ] Wp) χ A, Eu k r (Wq →L[ℂ] Wp) a b v ∈ eig k r (Wq →L[ℂ] Wp) χ A := by
    rintro a b v ⟨hv, hv'⟩
    refine ⟨fun m => ?_, fun u => ?_⟩
    · exact (GlobalTheory.ckOn_inCC_congr_on_group k r _ A _ _ (fun g hg => (ev_Eu a b v g hg).symm)).2 m
        ((GlobalTheory.T.operatorEab_preserves_smooth_classCC k r Wp Wq A a b _ ⟨smooth_iff.1 v.2.1, hv⟩).2 m)
    · have := LinearMap.congr_fun (qDetCentral _ _ _ hgl u a b) v
      rw [Module.End.mul_apply, Module.End.mul_apply, hv', map_smul] at this
      exact this
  have hint : ∀ a b (w : eig k r (Wq →L[ℂ] Wp) χ A),
      (eig k r (Wq →L[ℂ] Wp) χ A).subtype ((Eu k r (Wq →L[ℂ] Wp) a b).restrict (hst a b) w) =
        Eu k r (Wq →L[ℂ] Wp) a b ((eig k r (Wq →L[ℂ] Wp) χ A).subtype w) := fun _ _ _ => rfl
  refine ⟨Sm k r (Wq →L[ℂ] Wp), eig k r (Wq →L[ℂ] Wp) χ A, inferInstance, inferInstance, inferInstance,
    inferInstance, Eu k r (Wq →L[ℂ] Wp), fun a b => (Eu k r (Wq →L[ℂ] Wp) a b).restrict (hst a b),
    (eig k r (Wq →L[ℂ] Wp) χ A).subtype, (Sm k r (Wq →L[ℂ] Wp)).subtype, mulOp k r _, hgl,
    glRel_of_intertwine _ _ _ (Submodule.subtype_injective _) hint hgl, hint, ?_,
    fun v => smooth_iff.1 v.2.1, sm_ext, fun w => w.2.1, ?_, ev_Eu, ev_qdet, ?_⟩
  · intro u w
    apply Submodule.subtype_injective
    unfold qdet
    rw [qminor_intertwine _ _ _ _ _ _ _ hint, map_smul]
    exact w.2.2 u
  · rintro f ⟨hf, hfc⟩ hY
    have hcut : ∀ g ∈ B.GV k r, f g = (vK isOpen_univ f (smooth_iff.2 hf) : B.Mat k r → (Wq →L[ℂ] Wp)) g :=
      fun g hg => (cut_of_mem f (mem_lev.2 hg)).symm
    refine ⟨⟨vK isOpen_univ f (smooth_iff.2 hf), fun m => (GlobalTheory.ckOn_inCC_congr_on_group k r _ A _ _ hcut).2 m (hfc m),
      fun u => ?_⟩, fun g hg => (hcut g hg).symm⟩
    refine sm_ext _ _ fun g hg => ?_
    have h1 := ev_qdet (u - (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2) (vK isOpen_univ f (smooth_iff.2 hf)) g hg
    rw [sub_add_cancel] at h1
    have h2 := GlobalTheory.capelli_eigen_real_to_complex k r Wp Wq lam f hf hY (u - (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2) g hg
    rw [CV_eq] at h1 h2
    rw [h1, ← qminorOp_loc isOpen_univ id id _ f _ (fun x hx => hcut x (mem_lev.1 hx)) g (mem_lev.2 hg), h2,
      Submodule.coe_smul, Pi.smul_apply, ← hcut g hg]
    congr 1
    exact Finset.prod_congr rfl fun s _ => by ring
  · intro c hc
    simp only [mulOp, dif_pos hc]
    refine ⟨fun v g hg => ev_M isOpen_univ (smooth_iff.2 hc) v (mem_lev.2 hg), fun a b v g hg => ?_⟩
    have := ev_EM (i := 0) isOpen_univ (c0 a) (c0 b) (smooth_iff.2 hc) v (mem_lev.2 hg)
    rw [position_level_zero_coord, position_level_zero_coord, ← ev_Eu a b v g hg] at this
    exact this

end GlobalTheory
end
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open scoped ComplexConjugate

namespace GlobalTheory.HatNF.MinorPoly

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem qminor_words (k r m : ℕ) (a b : Fin m → Fin (2 * r + k + 1)) (u : ℂ) :
    ∃ L : List (ℂ × List (B.Mat k r)),
    (∀ cw ∈ L, (∀ X ∈ cw.2, B.inLie k r X) ∧ cw.2.length ≤ m) ∧
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
      B.CkOn ⊤ UU f → ∀ g ∈ UU, g ∈ B.GV k r →
        qminorOp (EabH (Hpk k r)) a b u f g = (L.map fun cw => cw.1 • B.Rw cw.2 f g).sum := by
  let ts : Equiv.Perm (Fin m) → List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) :=
    fun σ => List.ofFn fun j : Fin m => (u - ((j : ℕ) : ℂ), a (σ j), b j)
  refine ⟨(Finset.univ : Finset (Equiv.Perm (Fin m))).toList.flatMap
      (fun σ => (Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (ts σ)).map
        fun cw => (((Equiv.Perm.sign σ : ℤ) : ℂ) * cw.1, cw.2)), ?_, ?_⟩
  · intro cw hcw
    simp only [List.mem_flatMap, List.mem_map] at hcw
    obtain ⟨σ, _, cw', hm', rfl⟩ := hcw
    have := Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_words (k := k) (r := r) (ts σ) cw' hm'
    refine ⟨fun X hX => (this.1 X hX).1, this.2.trans ?_⟩
    simp [ts]
  · intro E _ _ UU f hf g hgU hg
    have hloc : ∀ σ, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ((ts σ).length : ℕ∞) f g := fun σ =>
      Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.loc_mono le_top (hf g hgU)
    have e1 : qminorOp (EabH (Hpk k r)) a b u f g =
        ∑ σ, (((Equiv.Perm.sign σ : ℤ) : ℂ)) • Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT (ts σ) f g := by
      simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      congr 1
      simp only [Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT, ts, List.map_ofFn]
      rfl
    rw [e1, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_eq (ts σ) f g hg (hloc σ), List.map_map,
      ← Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.sum_map_mul_smul]
    rfl

section terms

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def scalarTerm (P : B.Mat k r → ℂ) (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) : B.DTerm k r Wp Wq where
  coef := fun g => P g • ContinuousLinearMap.id ℂ _
  coefAdj := fun g => star (P g) • ContinuousLinearMap.id ℂ _
  word := w
  word_lie := hw
  adj_id := by
    intro x A B'
    simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
    rw [Formalism.FourierDecayAlt.P5.HerB.hs_smul_left, Formalism.FourierDecayAlt.P5.HerB.hs_smul_right]
    simp

theorem isPolyDeg_mul_const {N κ : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg κ P) (c : ℂ) :
    U.IsPolyDeg κ fun g => P g * c := by
  obtain ⟨q, hq, he⟩ := h
  refine ⟨q * MvPolynomial.C c, ?_, fun g => by simp [he g]⟩
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simpa using hq

theorem exists_polyOp_words (m κ : ℕ) (P : B.Mat k r → ℂ) (hP : U.IsPolyDeg κ P)
    (L : List (ℂ × List (B.Mat k r))) (hL : ∀ cw ∈ L, (∀ X ∈ cw.2, B.inLie k r X) ∧ cw.2.length ≤ m) :
    ∃ Θ : B.DiffOp k r Wp Wq, Formalism.FourierDecayAlt.P.CutMP.PolyOp m κ Θ ∧ ∀ F g,
      B.opApply Θ F g = P g • (L.map fun cw => cw.1 • B.Rw cw.2 F g).sum := by
  induction L with
  | nil => exact ⟨[], fun T hT => by simp at hT, fun F g => by simp [B.opApply]⟩
  | cons cw L ih =>
    obtain ⟨Θ, hΘ, he⟩ := ih fun cw' h => hL cw' (List.mem_cons_of_mem _ h)
    have h0 := hL cw List.mem_cons_self
    refine ⟨scalarTerm (fun g => P g * cw.1) cw.2 h0.1 :: Θ, ?_, fun F g => ?_⟩
    · intro T hT
      rcases List.mem_cons.1 hT with rfl | hT
      · exact ⟨h0.2, fun g => P g * cw.1, isPolyDeg_mul_const hP _, fun _ => rfl, fun _ => rfl⟩
      · exact hΘ T hT
    · have h1 := he F g
      simp only [B.opApply, List.map_cons, List.sum_cons] at h1 ⊢
      rw [h1, smul_add, smul_smul]
      rfl

end terms

theorem minor_polyOp : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r m κ : ℕ) (ι : Type) [Fintype ι] (a b : ι → Fin m → Fin (2 * r + k + 1)) (u : ℂ) (co : ι → B.Mat k r → ℂ), (∀ i, U.IsPolyDeg κ (co i)) → ∃ Θ : B.DiffOp k r Wp Wq, Formalism.FourierDecayAlt.P.CutMP.PolyOp m κ Θ ∧ ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), ∀ g ∈ B.GV k r, ∀ V : Set (B.Mat k r), IsOpen V → g ∈ V → B.CkOn ⊤ (B.GV k r ∩ V) F → B.opApply Θ F g = ∑ i, co i g • qminorOp (EabH (Hpk k r)) (a i) (b i) u F g := by
  intro Wp Wq _ _ _ _ _ _ k r m κ ι _ a b u co hco
  choose L hL hE using fun i => qminor_words k r m (a i) (b i) u
  choose Θ hΘ hA using fun i => exists_polyOp_words (Wp := Wp) (Wq := Wq) m κ (co i) (hco i) (L i) (hL i)
  refine ⟨(Finset.univ : Finset ι).toList.flatMap Θ, ?_, ?_⟩
  · intro T hT
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.1 hT
    exact hΘ i T hi
  · intro F g hg V _ hgV hF
    unfold B.opApply
    rw [Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hE i _ _ F hF g ⟨hg, hgV⟩ hg, ← hA i F g]
    rfl

end

end GlobalTheory.HatNF.MinorPoly
end
