module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanPairNegativeSymplecticPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047

@[expose] public section

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

noncomputable section

namespace GlobalTheory.RealLift.DConst

theorem Jm_diag' (p q : ℕ) :
    Jm p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp

theorem Jm_mul_self' (p q : ℕ) : Jm p q * Jm p q = 1 := by
  rw [Jm_diag', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  cases a <;> simp

theorem card_eq_of_isFrame {β : Type} [Fintype β] [DecidableEq β] {r s : ℕ} {M : Matrix β β ℂ}
    {C : Matrix β (Ix r s) ℂ} (h : IsFrame M C) : Fintype.card β = r + s := by
  obtain ⟨h1, C', h2⟩ := h
  apply le_antisymm
  · have := Matrix.rank_mul_le_left C C'
    rw [h2, Matrix.rank_one] at this
    have h3 := Matrix.rank_le_card_width C
    simp only [Fintype.card_sum, Fintype.card_fin] at h3
    simpa using this.trans h3
  · have e : (Jm r s * Cᵀ * M) * C.map star = 1 := by
      rw [Matrix.mul_assoc (Jm r s * Cᵀ), Matrix.mul_assoc, ← Matrix.mul_assoc Cᵀ, h1, Jm_mul_self']
    have := Matrix.rank_mul_le_right (Jm r s * Cᵀ * M) (C.map star)
    rw [e, Matrix.rank_one] at this
    have h3 := Matrix.rank_le_card_height (C.map star)
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    exact this.trans h3

theorem atPl_tprod {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V] (w : ι)
    (L : Module.End ℂ V) (f : ι → V) :
    atPl (V := fun _ => V) w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem cd_eq_half_exp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φd : Tens F P Q (R + S) (S + R) →ₗ[ℂ] SInf F (κ ⊕ κ))
    (omd : UG (cA σ) (dbl JB) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)) (χ : Chr F E) (m : InfinitePlace F → ℤ)
    (cd : InfinitePlace F → ℂ),
    IsCMExt F E σ → IsStd ψ → Framed τ JA JB a b A C →
    IsUWeilSplit (cA σ) (adeleClass F) ψ (-1) JA (dbl JB) dd χ (diagCols β) omd → HasExp τ χ m →
    ActsBy τ (fun w => dblM (C w)) omd Φd (fockAct2 P Q (R + S) (S + R)) cd →
    (∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ z : Matrix α β (AE F E), ∀ φ ∈ (adeleClass F).sp (κ ⊕ κ),
      l (dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ) φ) = l φ) ∧
      ∃ g ∈ SB (κ ⊕ κ → Af F), ∀ f : SInf F (κ ⊕ κ),
        l (pureA F f g) = ∫ x : κ → mixedEmbedding.mixedSpace F, f (Sum.elim x x)) →
    (∫ x : κ → mixedEmbedding.mixedSpace F, Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x)) ≠ 0 →
    0 < R + S → ∀ w, cd w = m w / 2 := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB dd a b A C Φd omd χ m cd hCM hψ hFr hWS hχ hAct hl hne hpos w₀
  obtain ⟨l, hladm, hlinv, g, hg, hlint⟩ := hl
  obtain ⟨z, γ, hγ, hgen, hγz, hzat, hzpi⟩ :=
    GlobalTheory.T.exists_central_circle_oneParameter_unitary_realPlace F E σ (β ⊕ β) (R + S) (S + R) τ (dbl JB) (fun w => dblM (C w)) w₀ hCM
  have hcard : Fintype.card β = R + S := card_eq_of_isFrame (hFr.2.2 w₀)
  have hzz : ∀ t, (z t : AE F E) * cA σ (z t : AE F E) = 1 := by
    intro t
    have h0 := GlobalTheory.AdeleInfInj.eq_zero_of_piInf_eq_zero F E σ hCM τ
      ((z t : AE F E) * cA σ (z t : AE F E) - 1) ?_ ?_
    · exact sub_eq_zero.mp h0
    · intro u hu
      have h1 := hzat t u hu
      have e : (z t : AE F E) * cA σ (z t : AE F E) - 1 =
          ((z t : AE F E) - 1) * cA σ (z t : AE F E) + cA σ ((z t : AE F E) - 1) := by
        rw [map_sub, map_one]; ring
      rw [e, smul_add, ← smul_mul_assoc, h1, zero_mul, ← map_smul, h1, map_zero, add_zero]
    · intro w
      rw [map_sub, map_mul, GlobalTheory.WrongSignPair.piInf_cA hCM, hzpi, map_one]
      split_ifs
      · rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; simp
      · simp
  have hχz : ∀ t : ℝ, (χ (z t) : ℂ) = Complex.exp (((m w₀ : ℂ) * Complex.I) * t) := by
    intro t
    rw [hχ (z t) (hzat t), Finset.prod_eq_single w₀]
    · rw [hzpi, if_pos rfl, Complex.norm_exp_ofReal_mul_I, Complex.ofReal_one, div_one, ← Complex.exp_int_mul]
      congr 1; ring
    · intro w _ hw
      rw [hzpi, if_neg hw]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  let tt : ℝ → GL β (AE F E) := fun t =>
    Units.map (Matrix.scalar β : AE F E →+* Matrix β β (AE F E)).toMonoidHom (z t)
  have htt : ∀ t, ((tt t : GL β (AE F E)) : Matrix β β (AE F E)) = (z t : AE F E) • 1 := by
    intro t; simp [tt, Matrix.smul_one_eq_diagonal]
  have hdet : ∀ t, Matrix.GeneralLinearGroup.det (tt t) = z t ^ Fintype.card β := by
    intro t; ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, htt, Matrix.det_smul, Matrix.det_one, mul_one,
      Units.val_pow_eq_pow_val]
  set φ : (κ ⊕ κ → AF F) → ℂ := pureA F (Φd (PiTensorProduct.tprod ℂ fun _ => 1)) g with hφdef
  have hφ : φ ∈ (adeleClass F).sp (κ ⊕ κ) := Submodule.subset_span ⟨_, g, hg, rfl⟩
  set L := ∫ x : κ → mixedEmbedding.mixedSpace F, Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x) with hL
  have hlφ : l φ = L := hlint _
  set c₀ : ℂ := ((m w₀ : ℂ) * ((R + S : ℕ) : ℂ)) * Complex.I with hc₀
  have hval : ∀ t : ℝ, l (omd (γ (Multiplicative.ofAdd t)) φ) = L * Complex.exp (c₀ * t) := by
    intro t
    have hp : (((γ (Multiplicative.ofAdd t) : UG (cA σ) (dbl JB)) : GL (β ⊕ β) (AE F E)) :
        Matrix (β ⊕ β) (β ⊕ β) (AE F E)) * (diagCols β : Matrix (β ⊕ β) β (AE F E)) =
        (diagCols β : Matrix (β ⊕ β) β (AE F E)) * ((tt t : GL β (AE F E)) : Matrix β β (AE F E)) := by
      erw [hγz t]
      rw [htt, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
    have hmod : Units.map (Algebra.norm (AF F) : AE F E →* AF F) (z t ^ Fintype.card β) = 1 := by
      ext; simp [GlobalTheory.T.norm_extensionAdeles_eq_one_of_mul_conj_eq_one F E σ hCM _ (hzz t)]
    rw [hWS.2.2 l hladm hlinv _ (tt t) hp φ hφ, hdet, hmod, map_one, map_pow, hlφ]
    simp only [NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, mul_one]
    rw [show ((χ (z t) ^ Fintype.card β : Circle) : ℂ) = (χ (z t) : ℂ) ^ Fintype.card β from by simp, hχz, ← Complex.exp_nat_mul, hcard, mul_comm]
    congr 1; rw [hc₀]; push_cast; ring_nf
  have hder1 : HasDerivAt (fun t : ℝ => l (omd (γ (Multiplicative.ofAdd t)) φ)) (L * c₀) 0 := by
    have h1 : HasDerivAt (fun y : ℂ => L * Complex.exp (c₀ * y)) (L * (Complex.exp (c₀ * ((0 : ℝ) : ℂ)) * (c₀ * 1)))
        ((0 : ℝ) : ℂ) := (((hasDerivAt_id ((0 : ℝ) : ℂ)).const_mul c₀).cexp).const_mul L
    have h2 := h1.comp_ofReal
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, mul_one] at h2
    exact h2.congr_of_eventuallyEq (Filter.Eventually.of_forall hval)
  have hd := hAct γ hγ _ hgen (PiTensorProduct.tprod ℂ fun _ => 1) g hg l hladm
  have huniq := hd.unique hder1
  have hsum : ∑ c : Ix (R + S) (S + R), Complex.I * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) c = 0 := by
    simp [Fintype.sum_sum_type]; ring
  have hT : sumPl (fun w => fockAct2 P Q (R + S) (S + R)
        ((fun w => if w = w₀ then Complex.I • (1 : Mat (R + S) (S + R)) else 0) w) +
        (cd w * ((fun w => if w = w₀ then Complex.I • (1 : Mat (R + S) (S + R)) else 0) w).trace) • 1)
        (PiTensorProduct.tprod ℂ fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q (R + S) (S + R))) =
      (cd w₀ * (Complex.I * (((R + S : ℕ) : ℂ) + ((S + R : ℕ) : ℂ)))) •
        PiTensorProduct.tprod ℂ fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q (R + S) (S + R)) := by
    unfold sumPl
    rw [LinearMap.sum_apply, Finset.sum_eq_single w₀]
    · rw [atPl_tprod]
      simp only [↓reduceIte]
      have hf : (fockAct2 P Q (R + S) (S + R) (Complex.I • (1 : Mat (R + S) (S + R))) +
          (cd w₀ * (Complex.I • (1 : Mat (R + S) (S + R))).trace) • 1) (1 : Formalism.BasicNotions.TH.Pol P Q (R + S) (S + R)) =
          (cd w₀ * (Complex.I * (((R + S : ℕ) : ℂ) + ((S + R : ℕ) : ℂ)))) • (1 : Formalism.BasicNotions.TH.Pol P Q (R + S) (S + R)) := by
        rw [LinearMap.add_apply, Matrix.smul_one_eq_diagonal, GlobalTheory.VacuumWeight.fockAct2_diagonal_one, hsum, mul_zero,
          zero_smul, zero_add, ← Matrix.smul_one_eq_diagonal, Matrix.trace_smul, Matrix.trace_one]
        simp [Fintype.card_sum, Fintype.card_fin]
      rw [hf, MultilinearMap.map_update_smul, Function.update_eq_self]
      rfl
    · intro w _ hw
      rw [atPl_tprod]
      simp only [if_neg hw, map_zero, Matrix.trace_zero, mul_zero, zero_smul, add_zero, LinearMap.zero_apply]
      exact (PiTensorProduct.tprod ℂ).map_update_zero _ _
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hT, map_smul, hlint] at huniq
  simp only [SchwartzMap.smul_apply, smul_eq_mul] at huniq
  rw [MeasureTheory.integral_const_mul, ← hL] at huniq
  have hRS : ((R + S : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hfin : (cd w₀ - (m w₀ : ℂ) / 2) * (2 * Complex.I * ((R + S : ℕ) : ℂ) * L) = 0 := by
    rw [hc₀] at huniq
    push_cast at huniq hRS ⊢
    linear_combination huniq
  have hne' : 2 * Complex.I * ((R + S : ℕ) : ℂ) * L ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hRS) hne
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfin).resolve_right hne')

end GlobalTheory.RealLift.DConst
end
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.SympFrames

def sgn {p q : ℕ} : Ix p q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

theorem jm_eq_diagonal (p q : ℕ) : Jm p q = Matrix.diagonal (sgn (p := p) (q := q)) := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks, Matrix.diagonal, Matrix.one_apply, sgn] <;> split_ifs <;> simp

theorem lineSign_eq {p q r s : ℕ} (x : Ix p q) (y : Ix r s) : lineSign x y = sgn x * sgn y := by
  rcases x with x | x <;> rcases y with y | y <;> simp [lineSign, sgn]

theorem trace_jm {p q r s : ℕ} (c c' : Matrix (Ix p q) (Ix r s) ℂ) :
    (cᵀ * Jm p q * c'.map star * (Jm r s)ᵀ).trace = ∑ x, ∑ y, lineSign x y * c x y * star (c' x y) := by
  rw [jm_eq_diagonal, jm_eq_diagonal, Matrix.diagonal_transpose, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_diagonal, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul, lineSign_eq, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem quad_eq_trace {α β : Type} [Fintype α] [Fintype β]
    (U U' : Matrix α β ℂ) (X : Matrix α α ℂ) (Y : Matrix β β ℂ) :
    ∑ i, ∑ j, ∑ k, ∑ l, U i j * X i k * Y j l * star (U' k l) = (Uᵀ * X * U'.map star * Yᵀ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem frame_trace {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {P Q R S : ℕ}
    (X : Matrix α α ℂ) (Y : Matrix β β ℂ) (a b : ℂ) (A : Matrix α (Ix P Q) ℂ) (C : Matrix β (Ix R S) ℂ)
    (hA : Aᵀ * (a • X) * A.map star = Jm P Q) (hC : Cᵀ * (b • Y) * C.map star = Jm R S)
    (c c' : Matrix (Ix P Q) (Ix R S) ℂ) :
    a * b * ((A * c * Cᵀ)ᵀ * X * (A * c' * Cᵀ).map star * Yᵀ).trace =
      ∑ x, ∑ y, lineSign x y * c x y * star (c' x y) := by
  rw [← trace_jm, ← hA, ← hC]
  have hm : (A * c' * Cᵀ).map star = A.map star * c'.map star * (C.map star)ᵀ := by
    rw [show (star : ℂ → ℂ) = starRingEnd ℂ from rfl, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  rw [hm, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm C]
  simp only [Matrix.mul_assoc]
  ring

theorem symp_frames : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {P Q R S : ℕ} (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → Framed τ JA JB a b A C →
    ∀ (u u' : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c c' : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ), At (evI F) u → At (evI F) u' →
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → (∀ w, u'.map (piInf (τ w)) = A w * c' w * (C w)ᵀ) →
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := by
  intro F E _ _ _ _ _ σ α β _ _ _ _ P Q R S τ JA JB a b A C hCM hF u u' c c' _ _ hu hu'
  have key : ∀ w, a * b * piInf (τ w) (hTens (cA σ) JA JB u u') =
      ∑ x, ∑ y, lineSign x y * c w x y * star (c' w x y) := by
    intro w
    have e : piInf (τ w) (hTens (cA σ) JA JB u u') = ∑ i, ∑ j, ∑ k, ∑ l, u.map (piInf (τ w)) i j *
        JA.map (piInf (τ w)) i k * JB.map (piInf (τ w)) j l * star (u'.map (piInf (τ w)) k l) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hTens, map_sum, map_mul, GlobalTheory.WrongSignPair.piInf_cA hCM, Matrix.map_apply]
    rw [e, hu w, hu' w, quad_eq_trace]
    exact frame_trace _ _ a b (A w) (C w) (hF.2.1 w).1 (hF.2.2 w).1 (c w) (c' w)
  rw [symp, GlobalTheory.WrongSignPair.trace_evI_trace hCM τ, Complex.im_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h2 := key w
  rw [hF.1] at h2
  rw [← h2, map_mul, map_neg, map_one]
  simp only [Complex.neg_re, Complex.mul_im, Complex.I_re, Complex.I_im, neg_one_mul, zero_mul, one_mul, zero_add]
  ring

end GlobalTheory.SympFrames
end
end

section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section

namespace GlobalTheory.ThetaOfSmF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_theta_infPartF {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmbF τ θ) :
    Continuous fun z : AEF F E => θ (infPartF F E z) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := isModuleTopology_AE F E
  let b := Module.finBasis F E
  let bb := Algebra.TensorProduct.basis (AF F) b
  have hz : ∀ z : AEF F E, θ (infPartF F E z) = ∑ i, θ (fstA F (bb.repr z i) ⊗ₜ[F] (1 : E)) * τ (b i) := by
    intro z
    conv_lhs => rw [← bb.sum_repr z]

    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    show θ (fstA F (bb.repr z i) ⊗ₜ[F] b i) = _
    rw [← hθ.1 (b i), ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hc : ∀ i, Continuous fun z : AEF F E => bb.repr z i := fun i =>
    IsModuleTopology.continuous_of_linearMap (bb.coord i)
  refine (continuous_finsetSum _ fun i _ => ?_).congr fun z => (hz z).symm
  exact (hθ.2.comp (continuous_fst.comp (hc i))).mul continuous_const

end GlobalTheory.ThetaOfSmF


open GlobalTheory.ThetaOfSmF in
theorem GlobalTheory.ThetaOfSmF.theta_of_smF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (hψ : IsCharAF F B.ψ) (f : BBF σ JS JT ξ₀ B.ψ), Sm (rhoVF σ JS JT ξ₀ B.ψ hψ ι) f →
        (∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
          ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u f.1 = f.1) →
        IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ θ hθ ι hι hψ f hF hl
  refine ⟨f.2, hl, f.1.continuous, fun k L hL hL0 w => ?_⟩
  obtain ⟨lam, hlc, hlam⟩ := GlobalTheory.HeisLineDiffF.exists_log (GlobalTheory.T.standardTraceAddChar_isStandardChar_of_admissibleCMBase F E σ B hB)

  let P : (Fin k → ℝ) →+ (IxF F nS nT → ℂ) :=
    { toFun := fun t => piWF θ (L t)
      map_zero' := by
        funext p
        simp only [piWF, map_zero, Matrix.zero_apply, Pi.zero_apply]
      map_add' := fun s t => by
        funext p
        simp only [piWF, map_add (f := _), Matrix.add_apply, Pi.add_apply] }
  have hP : Continuous P := continuous_pi fun p =>
    (continuous_theta_infPartF (hθ p.2)).comp ((continuous_apply p.1.2).comp ((continuous_apply p.1.1).comp hL))
  have hLP : ∀ t, L t = iotaVF ι (P t) := by
    intro t
    ext i j
    refine sub_eq_zero.1 (hι.ext _ ?_ fun w' => ?_)
    · have h0 : finPartF F E (L t i j) = 0 := congrFun (congrFun (hL0 t) i) j
      rw [map_sub, h0]
      simp only [iotaVF, Matrix.of_apply, hι.fin, sub_zero]
    · rw [map_sub, map_sub]
      simp only [iotaVF, Matrix.of_apply, hι.comp]
      show θ w' (infPartF F E (L t i j)) - θ w' (infPartF F E (L t i j)) = 0
      exact sub_self _

  let φ : (Fin k → ℝ) →+ ℂ :=
    { toFun := fun t => -lam (symplOHF σ JS JT ξ₀ w (L t))
      map_zero' := by rw [map_zero L, GlobalTheory.HeisLineDiffF.symplOHF_zero_right, map_zero, neg_zero]
      map_add' := fun s t => by rw [map_add L, GlobalTheory.HeisLineDiffF.symplOHF_add_right, map_add (f := _), neg_add] }
  have hφ : Continuous φ := (hlc.comp (GlobalTheory.HeisLineDiffF.continuous_symplOHF σ JS JT ξ₀ w hL)).neg
  have e : (fun t => f.1 (w + L t)) =
      fun t => Complex.exp (φ.toRealLinearMap hφ t) * ev _ _ w (rhoVF σ JS JT ξ₀ B.ψ hψ ι (P.toRealLinearMap hP t) f) := by
    funext t
    have h1 : (rhoVF σ JS JT ξ₀ B.ψ hψ ι (P t) f).1 w = heisOF σ JS JT ξ₀ B.ψ (L t) f.1 w := by
      show (rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι (P t)) f).1 w = _
      rw [coe_rhoBF, ← hLP t]
    have h2 : B.ψ (-(symplOHF σ JS JT ξ₀ w (L t))) = Complex.exp (φ t) := by
      rw [hlam _ (by rw [map_neg, GlobalTheory.HeisLineDiffF.sndA_symplOHF σ JS JT ξ₀ w _ (hL0 t), neg_zero]), map_neg]
      rfl
    show f.1 (w + L t) = Complex.exp (φ t) * ev _ _ w (rhoVF σ JS JT ξ₀ B.ψ hψ ι (P t) f)
    rw [ev_apply, h1, ← h2, heisOF, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one,
      one_mul]
  rw [e]
  exact (φ.toRealLinearMap hφ).contDiff.cexp.mul
    (((ev _ _ w).restrictScalars ℝ).contDiff.comp (hF.comp (P.toRealLinearMap hP).contDiff))

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VolIndex

open GlobalTheory.Mass GlobalTheory.Mass.Levels

theorem latLev_le_range {D : D7} (V : HSp D) : latLev V ≤ (Lev.finE V).range := by
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj D.sp.cm.sig V.gram
  rintro _ ⟨_, ⟨b, -, rfl⟩, rfl⟩
  obtain ⟨g, rfl⟩ := hπ.surjective b
  refine ⟨g, ?_⟩
  change Lev.finE V g =
    ((swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (π g) : UA D.sp.cm V.gram) : GL (Fin V.rank) (Lev.EAf D))
  rw [coe_swapPts, hπ g]
  rfl

theorem vol_eq_index_mul_mass : ∀ (D : D7) (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), V.SigOK → V.IsPosDef → K ≤ GlobalTheory.Mass.Levels.latLev V → K.relIndex (GlobalTheory.Mass.Levels.latLev V) ≠ 0 → IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) → IsMeasDef V K ν 𝓕 → (ν 𝓕).toReal = (K.relIndex (GlobalTheory.Mass.Levels.latLev V) : ℝ) * GlobalTheory.Mass.unitaryMass D.sp.cm.sig V.gram (GlobalTheory.Mass.Levels.latStab V) := by
  intro D V K ν 𝓕 hW hs hK hi ho hν
  have hd : Formalism.UG.IsTotDef D.sp.cm.sig V.gram := GlobalTheory.DefiniteQuotient.isTotDef_of_posDef V fun τ => by
    have := hW (Formalism.BasicNotions.TH.tauE D τ)
    rw [hs] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj D.sp.cm.sig V.gram
  obtain ⟨hc, hL⟩ := latStab_compact_open V
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := hν.1.1
  have h1 : ν (K.comap (Lev.finE V)) = 1 := measure_comap_finE hν.1
  have hidx : (K.comap (Lev.finE V)).relIndex ((latLev V).comap (Lev.finE V)) = K.relIndex (latLev V) := by
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self (latLev_le_range V)]
  have : ((K.comap (Lev.finE V)).subgroupOf ((latLev V).comap (Lev.finE V))).FiniteIndex := ⟨hidx.trans_ne hi⟩
  have h2 := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure (K.comap (Lev.finE V)) ((latLev V).comap (Lev.finE V))
    (Subgroup.comap_mono hK) ho.measurableSet ν
  rw [hidx, h1, mul_one] at h2
  have hn0 : ((K.relIndex (latLev V) : ℕ) : ENNReal) ≠ 0 := Nat.cast_ne_zero.2 hi
  have hnt : ((K.relIndex (latLev V) : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcm := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  have h3 := hπ.measure_toReal hcm.1 (hcm.2 V) hd hc hL (((K.relIndex (latLev V) : ℕ) : ENNReal)⁻¹ • ν)
    (by
      rw [← toLev_latLev, comap_toLev V _ hπ, Measure.smul_apply, ← h2, smul_eq_mul]
      exact ENNReal.inv_mul_cancel hn0 hnt)
    (hν.2.mono (Measure.smul_absolutelyContinuous))
  rw [← h3, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    mul_inv_cancel_left₀ (Nat.cast_ne_zero.2 hi)]

end GlobalTheory.VolIndex
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.poincare_volume_integrableOn_compact_punctured_polydisc : ∀ {n : ℕ} (S : Finset (Fin n)) (K : Set (V n)), IsCompact K → (∀ v ∈ K, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → IntegrableOn (fun v => ∏ a, (poinWt S v a)⁻¹ ^ 2) K := by
  first | exact @GlobalTheory.GoodTop.integrableOn_poinVol | exact GlobalTheory.GoodTop.integrableOn_poinVol | (intros; apply GlobalTheory.GoodTop.integrableOn_poinVol <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.topDegreeDensityComplexForm_aeval_dzWedgeDzbar : ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ), dens ((aeval sym P : Ev n) : Alt n) = topCoeff P / (Complex.I / 2) ^ n := by
  first | exact @GlobalTheory.ChernCalc.DensTop.dens_aeval_sym | exact GlobalTheory.ChernCalc.DensTop.dens_aeval_sym | (intros; apply GlobalTheory.ChernCalc.DensTop.dens_aeval_sym <;> assumption)
end
