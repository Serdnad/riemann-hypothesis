module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1628
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1514
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1580
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualWeylModuleInvRationalPointEqConjCharAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1625
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1626
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.ArchBound

theorem entries_bound : ∀ {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ), P.IsHermitian →
    (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) →
    ∃ K : ℝ, ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 < s → Yᴴ * P * Y = (s : ℂ) • P →
      ∀ i j, ‖Y i j‖ ^ 2 ≤ K * s :=
  GlobalTheory.T.hermitian_similitude_entry_sq_bound

theorem majorant : ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian), H.det ≠ 0 → sigPosH hH = 1 →
    ∀ z : Fin n → ℂ, 0 < (star z ⬝ᵥ H *ᵥ z).re →
    ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧
      ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (c : ℂ), 0 < s → Yᴴ * H * Y = (s : ℂ) • H →
        Y *ᵥ z = c • z → Yᴴ * P * Y = (s : ℂ) • P :=
  GlobalTheory.T.exists_posDef_majorant_of_positiveIndex_one

variable {p : ℕ} [Fact p.Prime]

theorem sh_inv_mul (G : HTGroup p) (β : G.Cˣ) (y : grp G β) :
    sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      algebraMap ℚ G.C (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) * ((β⁻¹ : G.Cˣ) : G.C) := by
  set u : G.Cˣ := (y : G.Cˣ × ℚˣ).1
  set s : ℚ := (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)
  have h : (u : G.C) * β * sh G u = algebraMap ℚ G.C s * β := y.2.1
  have h1 : sh G u = algebraMap ℚ G.C s * (((β⁻¹ : G.Cˣ) : G.C) * ((u⁻¹ : G.Cˣ) : G.C) * β) := by
    calc sh G u = (((β⁻¹ : G.Cˣ) : G.C) * ((u⁻¹ : G.Cˣ) : G.C)) * ((u : G.C) * β * sh G u) := by
          simp only [mul_assoc, Units.inv_mul_cancel_left]
      _ = _ := by
          rw [h]; simp only [← Algebra.smul_def, mul_smul_comm, mul_assoc]
  rw [h1]
  simp only [← Algebra.smul_def, smul_mul_assoc, mul_assoc, Units.mul_inv_cancel_left]
  rw [Units.inv_mul, mul_one]

theorem psi_algebraMap (G : HTGroup p) (w : InfinitePlace G.F) (q : ℚ) :
    G.psi w (algebraMap ℚ G.C q) = ((q : ℝ) : ℂ) • (1 : Matrix (Fin G.n) (Fin G.n) ℂ) := by
  have := ((G.psi w).toRatAlgHom).commutes q
  simp only [RingHom.toRatAlgHom_apply] at this
  rw [this, Algebra.algebraMap_eq_smul_one]
  ext i j
  simp [Matrix.smul_apply, Rat.smul_def]

theorem herm_sim (G : HTGroup p) (β : G.Cˣ) (y : grp G β) (w : InfinitePlace G.F) :
    (G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * herm G w β * G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) : ℂ) • herm G w β := by
  have h := congrArg (G.psi w) (sh_inv_mul G β y)
  rw [map_mul, map_mul, map_mul, psi_algebraMap] at h
  have hs : G.psi w (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) =
      (G.gram w)⁻¹ * (G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * G.gram w := G.psi_star w _
  rw [hs] at h
  have hg : IsUnit (G.gram w).det := isUnit_iff_ne_zero.2 (G.gram_det w)
  unfold herm
  calc _ = G.gram w * ((G.gram w)⁻¹ * (G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * G.gram w *
        G.psi w ((β⁻¹ : G.Cˣ) : G.C) * G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) := by
        simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]
    _ = _ := by rw [h, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]

theorem herm_congr (G : HTGroup p) (β : G.Cˣ) (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1)
    (v : InfinitePlace G.F) :
    ∃ Z : GL (Fin G.n) ℂ, herm G v β =
      (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) := by
  obtain ⟨z, hz⟩ := hR
  refine ⟨Units.map (G.psiR v).toMonoidHom z, ?_⟩
  set Zm : Matrix (Fin G.n) (Fin G.n) ℂ := G.psiR v (z : ℝ ⊗[ℚ] G.C) with hZm
  change G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C) = Zmᴴ * G.gram v * Zm
  have hb : G.psiR v (inC G ℝ (β : G.C)) = G.psi v (β : G.C) := by
    change G.psiR v ((1 : ℝ) ⊗ₜ (β : G.C)) = _
    rw [psiR_tmul, one_smul]
  have h1 := congrArg (G.psiR v) hz
  rw [map_mul, map_mul, psiR_starT, hb] at h1
  simp only [Units.val_one, map_one] at h1
  rw [← hZm] at h1
  have hg : IsUnit (G.gram v).det := isUnit_iff_ne_zero.2 (G.gram_det v)
  set M := G.psi v ((β⁻¹ : G.Cˣ) : G.C)
  have hMb : M * G.psi v (β : G.C) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have h2 : G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm) = 1 := by
    have := mul_eq_one_comm.1 (by simpa [Matrix.mul_assoc] using h1 :
      Zm * (G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v)) = 1)
    simpa [Matrix.mul_assoc] using this
  have h3 : M = (G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm := by
    calc M = M * (G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm)) := by rw [h2, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hMb, Matrix.one_mul]
  rw [h3]
  simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]

end GlobalTheory.ArchBound

namespace GlobalTheory.ArchBound

variable {p : ℕ} [Fact p.Prime]

theorem sigPosH_eq_zero_of_ne (G : HTGroup p) (ha : G.a = 1) (v : InfinitePlace G.F)
    (hv : sigPosH (G.gram_herm v) = 1) (w : InfinitePlace G.F) (hw : w ≠ v) : sigPosH (G.gram_herm w) = 0 := by
  rcases G.sig w with ⟨h1, -⟩ | ⟨h0, -⟩
  · exfalso
    have hc : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} = 1 := ha
    obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.1 hc
    have e1 := hx ⟨v, hv⟩
    have e2 := hx ⟨w, h1⟩
    exact hw (by rw [← e2] at e1; exact (congrArg Subtype.val e1).symm)
  · exact h0

theorem exists_majorant (G : HTGroup p) (ha : G.a = 1) (v : InfinitePlace G.F)
    (hv : sigPosH (G.gram_herm v) = 1) (β : G.Cˣ) (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1)
    (z : Fin G.n → ℂ) (hz : 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re) (w : InfinitePlace G.F) :
    ∃ P : Matrix (Fin G.n) (Fin G.n) ℂ, P.IsHermitian ∧
      (∀ x : Fin G.n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧
      ∀ y : grp G β, FixL G v β y z →
        (G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * P * G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
          (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) : ℂ) • P := by
  obtain ⟨Z, hZ⟩ := herm_congr G β hR w
  have hH : (herm G w β).IsHermitian := by
    rw [hZ]; unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      (G.gram_herm w).eq, Matrix.mul_assoc]
  have hdet : (herm G w β).det ≠ 0 := by
    rw [hZ, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    have hz0 : (Z : Matrix (Fin G.n) (Fin G.n) ℂ).det ≠ 0 := (Matrix.isUnits_det_units Z).ne_zero
    exact mul_ne_zero (mul_ne_zero (by simpa using hz0) (G.gram_det w)) hz0
  have hsig : sigPosH hH = sigPosH (G.gram_herm w) :=
    GlobalTheory.SigCong.sigPosH_congr (G.gram w) (G.gram_herm w) (G.gram_det w) Z _ hH hZ
  by_cases hw : w = v
  · subst hw
    obtain ⟨P, hPh, hPp, hPs⟩ := majorant (herm G w β) hH hdet (hsig.trans hv) z hz
    refine ⟨P, hPh, hPp, fun y hy => ?_⟩
    obtain ⟨c, hc⟩ := hy
    exact hPs _ _ c (by exact_mod_cast y.2.2) (herm_sim G β y w) hc
  · have h0 := sigPosH_eq_zero_of_ne G ha v hv w hw
    refine ⟨-herm G w β, hH.neg, fun x hx => ?_, fun y _ => ?_⟩
    · have := GlobalTheory.herm_negDef_of_sigPosH_eq_zero (herm G w β) hH hdet (hsig.trans h0) x hx
      rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]
      linarith
    · rw [Matrix.mul_neg, Matrix.neg_mul, herm_sim G β y w, smul_neg]

end GlobalTheory.ArchBound


open GlobalTheory.ArchBound in
theorem GlobalTheory.LKCx.entries_sq_le_of_fixL : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (β : G.Cˣ), sh G β = β →
    (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ (z : Fin G.n → ℂ), 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re →
    ∃ K : ℝ, ∀ y : grp G β, FixL G v β y z → ∀ (w : InfinitePlace G.F) (i j : Fin G.n),
      ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i j‖ ^ 2 ≤ K * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by
  intro p _ G ha v hv β _ hR z hz
  choose P hPh hPp hPs using exists_majorant G ha v hv β hR z hz
  choose K hK using fun w => entries_bound (P w) (hPh w) (hPp w)
  refine ⟨∑ w, |K w|, fun y hy w i j => ?_⟩
  have hs : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by exact_mod_cast y.2.2
  refine (hK w _ _ hs (hPs w y hy) i j).trans ?_
  refine mul_le_mul_of_nonneg_right ((le_abs_self _).trans ?_) hs.le
  exact Finset.single_le_sum (f := fun w => |K w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.HintInv

theorem rStab_comp_equiv {H : Type} [Group H] (φ : H ≃* H) (u : H → ℂ) :
    rStab (u ∘ φ) = (rStab u).comap (φ : H →* H) := by
  ext k
  simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
  show (∀ x, u (φ (x * k)) = u (φ x)) ↔ ∀ x, u (x * φ k) = u x
  constructor
  · intro h x
    have := h (φ.symm x)
    simpa using this
  · intro h x
    rw [map_mul]; exact h _

theorem hint_comp_equiv {H : Type} [Group H] (K : Subgroup H) (φ : H ≃* H) (hK : K.map (φ : H →* H) = K)
    (u : H → ℂ) : hint K (u ∘ φ) = hint K u := by
  set S := rStab u ⊓ K with hS
  have hS' : rStab (u ∘ φ) ⊓ K = S.comap (φ : H →* H) := by
    rw [rStab_comp_equiv, hS, Subgroup.comap_inf]
    congr 1
    have h1 : (K.map (φ : H →* H)).comap (φ : H →* H) = K :=
      Subgroup.comap_map_eq_self_of_injective φ.injective K
    rw [hK] at h1
    exact h1.symm
  unfold hint
  rw [hS', Subgroup.relIndex_comap, hK]
  congr 1
  let e : H ⧸ S.comap (φ : H →* H) ≃ H ⧸ S :=
    Quotient.congr φ.toEquiv (fun a b => by
      simp only [QuotientGroup.leftRel_apply, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_inv]
      rfl)
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S (φ q.out)
  have he : e q = ((φ q.out : H) : H ⧸ S) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [he, hs]
  exact ((Subgroup.mem_inf.1 s.2).1 _).symm

section Integral

variable {L : Type} [Field L] {a b : ℕ}

theorem entries_of_mem_GLint {O : Subring L} {A : GL (Fin a) L} (hA : A ∈ GLint (Fin a) O) (i j : Fin a) :
    A.val i j ∈ O ∧ (A⁻¹).val i j ∈ O := by
  obtain ⟨y, rfl⟩ := hA
  rw [← map_inv]
  exact ⟨(y.val i j).2, ((y⁻¹).val i j).2⟩

theorem mul_mul_mem {O : Subring L} {P : Matrix (Fin a) (Fin a) L} {X : Matrix (Fin a) (Fin b) L}
    {Q : Matrix (Fin b) (Fin b) L} (hP : ∀ i j, P i j ∈ O) (hX : ∀ i j, X i j ∈ O) (hQ : ∀ i j, Q i j ∈ O)
    (i : Fin a) (j : Fin b) : (P * X * Q) i j ∈ O := by
  rw [Matrix.mul_apply]
  refine Subring.sum_mem _ fun l _ => Subring.mul_mem _ ?_ (hQ l j)
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hP i k) (hX k l)

def lrEquiv (A : GL (Fin a) L) (B : GL (Fin b) L) : Matrix (Fin a) (Fin b) L ≃+ Matrix (Fin a) (Fin b) L where
  toFun X := A.val * X * B.val
  invFun X := (A⁻¹).val * X * (B⁻¹).val
  left_inv X := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A.val X, ← Matrix.mul_assoc (A⁻¹).val, ← Matrix.mul_assoc (A⁻¹).val]
    rw [Units.inv_mul, Matrix.one_mul, Units.mul_inv, Matrix.mul_one]
  right_inv X := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (A⁻¹).val X, ← Matrix.mul_assoc A.val, ← Matrix.mul_assoc A.val]
    rw [Units.mul_inv, Matrix.one_mul, Units.inv_mul, Matrix.mul_one]
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]

end Integral

theorem map_intMat {E : Type} [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (A : GLw a w) (B : GLw b w)
    (hA : A ∈ GlobalTheory.LFun.KGL w (n := a)) (hB : B ∈ GlobalTheory.LFun.KGL w (n := b)) :
    (intMat a b w).map ((lrEquiv A B).toMultiplicative : _ →* _) = intMat a b w := by
  have hint' : ∀ X : Matrix (Fin a) (Fin b) (w.adicCompletion E),
      (∀ i j, Valued.v (X i j) ≤ 1) ↔ ∀ i j, X i j ∈ Ov E w := fun X =>
    forall_congr' fun i => forall_congr' fun j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm
  have hA1 := fun i j => (entries_of_mem_GLint hA i j).1
  have hA2 := fun i j => (entries_of_mem_GLint hA i j).2
  have hB1 := fun i j => (entries_of_mem_GLint hB i j).1
  have hB2 := fun i j => (entries_of_mem_GLint hB i j).2
  have key : ∀ (P : GLw a w) (Q : GLw b w), (∀ i j, P.val i j ∈ Ov E w) → (∀ i j, Q.val i j ∈ Ov E w) →
      (intMat a b w).map ((lrEquiv P Q).toMultiplicative : _ →* _) ≤ intMat a b w := by
    intro P Q hP hQ
    rw [intMat, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨X, hX, rfl⟩
    refine Subgroup.subset_closure ?_
    show ∀ i j, Valued.v ((P.val * Multiplicative.toAdd X * Q.val) i j) ≤ 1
    rw [hint']
    exact mul_mul_mem hP ((hint' _).1 hX) hQ
  refine le_antisymm (key A B hA1 hB1) ?_
  have h2 := key A⁻¹ B⁻¹ hA2 hB2
  intro X hX
  refine ⟨(lrEquiv A⁻¹ B⁻¹).toMultiplicative X, h2 ⟨X, hX, rfl⟩, ?_⟩
  show Multiplicative.ofAdd (A.val * ((A⁻¹).val * Multiplicative.toAdd X * (B⁻¹).val) * B.val) = X
  rw [show A.val * ((A⁻¹).val * Multiplicative.toAdd X * (B⁻¹).val) * B.val = Multiplicative.toAdd X from
    (lrEquiv A B).right_inv _]
  rfl

theorem hint_intMat_mul_mul :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (u : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) → ℂ) (A : GLw a w) (B : GLw b w),
    A ∈ GlobalTheory.LFun.KGL w (n := a) → B ∈ GlobalTheory.LFun.KGL w (n := b) →
    hint (intMat a b w) (fun X => u (Multiplicative.ofAdd (A.val * Multiplicative.toAdd X * B.val))) =
      hint (intMat a b w) u := by
  intro E _ _ _ a b w u A B hA hB
  exact hint_comp_equiv (intMat a b w) (lrEquiv A B).toMultiplicative (map_intMat a b w A B hA hB) u

end GlobalTheory.BCT.HintInv
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.RegVan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_GLint_of_entries {L : Type} [Field L] {k : ℕ} (O : Subring L) (g : GL (Fin k) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin k) O := by
  have hi : Function.Injective fun A : Matrix (Fin k) (Fin k) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem eventually_toSub_mem (x : finU (E := E) (n := n)) :
    ∀ᶠ w in cofinite, toSub (UL n w) (cLoc w (x : UA E n)) ∈ KL n w := by
  have h : ∀ y : FiniteAdeleRing (𝓞 E) E, ∀ᶠ w in cofinite, pLoc E w y ∈ Formalism.UG.Ov E w := fun y => y.2
  have h1 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (pFin E (((x : UA E n) : GA E n).val i j)) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  have h2 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (pFin E ((((x : UA E n) : GA E n))⁻¹.val i j)) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  filter_upwards [h1, h2] with w a b
  have hK : cLoc w (x : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n) := by
    refine mem_GLint_of_entries _ _ (fun i j => a i j) (fun i j => ?_)
    rw [← map_inv]
    exact b i j
  unfold toSub
  split_ifs with hU
  · exact Subgroup.mem_subgroupOf.2 hK
  · exact one_mem _

theorem cLoc_finPt_val (w : Pl E) (γ : UE E n) :
    (cLoc w ((finPt γ : finU (E := E) (n := n)) : UA E n)).val = γ.1.val.map (algebraMap E (w.adicCompletion E)) := by
  rw [FinPtLoc.finPt_eq]
  refine Matrix.ext fun i j => ?_
  change pLoc E w (pFin E ((finGL E n (ratF E n γ.1)).val i j)) = algebraMap E _ (γ.1.val i j)
  rw [FinPtLoc.snd_entry]
  rfl

theorem separable_of_monic_natDegree_le_one {K : Type} [Field K] {p : K[X]} (hm : p.Monic) (hd : p.natDegree ≤ 1) :
    p.Separable := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd with h | h
  · rw [Polynomial.eq_one_of_monic_natDegree_zero hm h]; exact separable_one
  · rw [Polynomial.Monic.eq_X_add_C hm h]; exact separable_X_add_C _

end GlobalTheory.BCT.RegVan

theorem GlobalTheory.BCT.regvan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E))
    (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), IsTest (KL n) K' f → ∀ w ∈ S,
    (∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → ∀ (x : finU (E := E) (n := n)) (γ : UE E n),
    globFn S f (x⁻¹ * finPt γ * x) ≠ 0 → γ.1.val.charpoly.Separable := by
  intro E _ _ _ n S K' f hT w hw hsep x γ hne
  set y : finU (E := E) (n := n) := x⁻¹ * finPt γ * x with hy
  set g : Pl E → ℂ := fun u => f u (toSub (UL n u) (cLoc u (y : UA E n))) with hg
  have hev : ∀ᶠ u in cofinite, g u = 1 := by
    filter_upwards [RegVan.eventually_toSub_mem y, hT.2] with u a b
    simp only [hg, b]
    rw [Set.indicator_of_mem a]
    rfl
  have hfin : (Function.mulSupport g).Finite := hev
  have hgw : g w ≠ 0 := by
    intro h0
    apply hne
    unfold globFn
    rw [finprod_mem_def]
    refine finprod_eq_zero (S.mulIndicator g) w (by rw [Set.mulIndicator_of_mem hw]; exact h0) ?_
    exact hfin.subset (by rw [Set.mulSupport_mulIndicator]; exact Set.inter_subset_right)
  have hs := hsep _ hgw
  by_cases hmem : cLoc w (y : UA E n) ∈ UL n w
  · rw [show toSub (UL n w) (cLoc w (y : UA E n)) = ⟨_, hmem⟩ from dif_pos hmem] at hs
    change (cLoc w (y : UA E n)).val.charpoly.Separable at hs
    have hyv : (cLoc w (y : UA E n)).val = (cLoc w (x : UA E n))⁻¹.val *
        (cLoc w ((finPt γ : finU (E := E) (n := n)) : UA E n)).val * (cLoc w (x : UA E n)).val := by
      rw [hy]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, Units.val_mul]
    rw [hyv, Matrix.coe_units_inv, Matrix.charpoly_units_conj', RegVan.cLoc_finPt_val, Matrix.charpoly_map] at hs
    exact (separable_map _).1 hs
  · rw [show toSub (UL n w) (cLoc w (y : UA E n)) = 1 from dif_neg hmem] at hs
    change (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)).charpoly.Separable at hs
    rw [Matrix.charpoly_one, Fintype.card_fin, ← C_1] at hs
    have hn : n ≤ 1 := by
      rcases hs.of_pow' with h | ⟨_, h⟩ | h
      · exact absurd h (not_isUnit_X_sub_C _)
      · omega
      · omega
    exact RegVan.separable_of_monic_natDegree_le_one (Matrix.charpoly_monic _)
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hn)
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.eventually_integralConjugate_mem_centralizer_mul_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ γ : UE E n, γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, ∀ g : UL n w, g⁻¹ * locPt w γ * g ∈ KL n w → ∃ t ∈ twCent (MonoidHom.id (UL n w)) (locPt w γ), t⁻¹ * g ∈ KL n w := by
  first | exact @GlobalTheory.BCT.GoodConj.main | exact GlobalTheory.BCT.GoodConj.main | (intros; apply GlobalTheory.BCT.GoodConj.main <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_open_compact_integralMatrixAddSubgroup : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ), ∃ Λ : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (Λ : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ IsCompact (Λ : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ intMat a b w = AddSubgroup.toSubgroup Λ := by
  first | exact @GlobalTheory.IntMatOpen.intMat_open_compact | exact GlobalTheory.IntMatOpen.intMat_open_compact | (intros; apply GlobalTheory.IntMatOpen.intMat_open_compact <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.traceOnInvariantSubmodule_iSup_eq_sum : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : Type) [Fintype ι] (M : ι → Submodule ℂ V) (L : V →ₗ[ℂ] V), iSupIndep M → (∀ i, FiniteDimensional ℂ (M i)) → (∀ i, ∀ v ∈ M i, L v ∈ M i) → trOn (⨆ i, M i) L = ∑ i, trOn (M i) L := by
  first | exact @GlobalTheory.BCT.trOn_iSup_eq_sum | exact GlobalTheory.BCT.trOn_iSup_eq_sum | (intros; apply GlobalTheory.BCT.trOn_iSup_eq_sum <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.trace_dualWeylModule_inv_rationalPoint_eq_conj_charAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : DomWeight n) (γ : UE E n) (v : InfinitePlace E), LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam (GeneralLinearGroup.map v.embedding (γ⁻¹).1)) = starRingEnd ℂ (chAt lam (γ.1.val.charpoly.map v.embedding)) := by
  first | exact @GlobalTheory.ContraChar.trace_sqRep_inv_eq_conj_chAt | exact GlobalTheory.ContraChar.trace_sqRep_inv_eq_conj_chAt | (intros; apply GlobalTheory.ContraChar.trace_sqRep_inv_eq_conj_chAt <;> assumption)
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem _root_.GlobalTheory.T.skewHermitian_cartanInvolutionSystems_conjugate_archimedean : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n r s : ℕ) (X Y : Spc F E n), B.IsGood σ → X.IsSkew σ B r s → (reS X Y).IsSkew σ B r s →
    ∃ g ∈ UAt σ X (evI F), ∀ w, (mat g).map (piInf (B.emb w)) * X.θ w = Y.θ w * (mat g).map (piInf (B.emb w)) := by
  first | exact @GlobalTheory.CartanConjSkew.conj_skew | exact GlobalTheory.CartanConjSkew.conj_skew | (intros; apply GlobalTheory.CartanConjSkew.conj_skew <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc : GlobalTheory.EtC.C1 := by
  first | (exact @GlobalTheory.EtC.gaugeSplitting_holds) | (exact GlobalTheory.EtC.gaugeSplitting_holds) | (intros; apply GlobalTheory.EtC.gaugeSplitting_holds  <;> assumption)
end
