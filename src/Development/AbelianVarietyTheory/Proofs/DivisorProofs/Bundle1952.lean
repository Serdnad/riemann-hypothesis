module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle050
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylFour.LocInv

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

local instance borelFvLoc (v : Pl (F := F)) : BorelSpace (Fv F v) := ⟨rfl⟩

open GlobalTheory.SplitWeil

theorem norm_addChar_eq_one {v : Pl (F := F)} (χ : AddChar (Fv F v) ℂ) (hχ : Continuous χ) (x : Fv F v) :
    ‖χ x‖ = 1 := by
  have hb : ∀ y : Fv F v, ‖χ y‖ ≤ 1 := by
    intro y
    obtain ⟨s, hs⟩ : ∃ s : (Fv F v)ˣ, y ∈ cball s := by
      by_cases hy : y = 0
      · exact ⟨1, by simp [hy, cball]⟩
      · exact ⟨Units.mk0 y hy, by simp [cball]⟩
    obtain ⟨M, hM⟩ := (isCompact_cball s).exists_bound_of_continuousOn hχ.continuousOn
    have hn : ∀ n : ℕ, ‖χ y‖ ^ n ≤ M := by
      intro n
      have hmem : n • y ∈ cball s := by
        induction n with
        | zero => simp [cball]
        | succ n ih => rw [succ_nsmul]; exact add_mem_cball ih hs
      rw [← norm_pow, ← AddChar.map_nsmul_eq_pow]
      exact hM _ hmem
    by_contra h
    push_neg at h
    obtain ⟨n, hn'⟩ := pow_unbounded_of_one_lt M h
    exact absurd (hn n) (not_le.mpr hn')
  have h1 := hb x
  have h2 := hb (-x)
  have h3 : χ x * χ (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h4 : ‖χ x‖ * ‖χ (-x)‖ = 1 := by rw [← norm_mul, h3, norm_one]
  refine le_antisymm h1 ?_
  nlinarith [norm_nonneg (χ x), norm_nonneg (χ (-x))]

def toCirc {v : Pl (F := F)} (χ : AddChar (Fv F v) ℂ) (h : ∀ x, ‖χ x‖ = 1) : AddChar (Fv F v) Circle where
  toFun x := ⟨χ x, by simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using h x⟩
  map_zero_eq_one' := by
    apply Circle.ext
    simp
  map_add_eq_mul' a b := by
    apply Circle.ext
    exact χ.map_add_eq_mul a b

theorem coe_toCirc {v : Pl (F := F)} (χ : AddChar (Fv F v) ℂ) (h : ∀ x, ‖χ x‖ = 1) (x : Fv F v) :
    ((toCirc χ h x : Circle) : ℂ) = χ x := rfl

theorem continuous_psiAt' (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl (F := F)) :
    Continuous (GlobalTheory.LatVac.psiAt ψ v) := by
  have hj : Continuous (GlobalTheory.LatVac.liftV (F := F) v) := by
    change Continuous fun a => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a)
    exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)
  exact hψ.comp hj

theorem measV_selfDual (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (v : Pl (F := F)) (hne : ∃ x, psiLoc ψ v x ≠ 1) :
    ∃ (h : ∀ x, ‖GlobalTheory.LatVac.psiAt ψ v x‖ = 1) (c : (Fv F v)ˣ),
      HasConductor (toCirc _ h) c ∧ IsSelfDual (toCirc _ h) (measV ψ v) := by
  have hc := continuous_psiAt' ψ hψ.1 v
  have hn : ∀ x, ‖GlobalTheory.LatVac.psiAt ψ v x‖ = 1 := norm_addChar_eq_one _ hc
  have hcc : Continuous (toCirc _ hn) := Continuous.subtype_mk hc _
  have hne1 : toCirc _ hn ≠ 1 := by
    obtain ⟨x, hx⟩ := hne
    intro h1
    apply hx
    have := congrArg (fun χ : AddChar (Fv F v) Circle => ((χ x : Circle) : ℂ)) h1
    simpa [coe_toCirc, GlobalTheory.LatVac.psiAt_apply] using this
  obtain ⟨c, hcond⟩ := exists_hasConductor_of_continuous _ hcc hne1
  obtain ⟨ν, hν⟩ := exists_isSelfDual_of_hasConductor hcond
  have hex : ∃ ν, IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) ν := ⟨ν, hν.1, fun f hf => hν.2 f hf⟩
  refine ⟨hn, c, hcond, ?_⟩
  have hm : measV ψ v = hex.choose := by
    unfold measV
    rw [dite_eq_left hex]
  rw [hm]
  exact ⟨hex.choose_spec.1, fun f hf => hex.choose_spec.2 f hf⟩

end GlobalTheory.WeylFour.LocInv

namespace GlobalTheory.WeylFour.LocInv

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem fourV_fourV : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl (F := F),
    (∃ x, psiLoc ψ v x ≠ 1) →
    ∀ (κ : Type) [Fintype κ], ∀ φ ∈ SB (κ → Fv F v), fourV ψ v (fourV ψ v φ) = fun x => φ (-x) := by
  intro F _ _ ψ hψ v hne κ _ φ hφ
  classical
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨hn, c, hcond, hself⟩ := measV_selfDual ψ hψ v hne
  haveI := hself.1
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv F v)
  haveI := GlobalTheory.SplitWeil.t2Space (Fv F v)
  funext z
  have hinner : ∀ y, fourV ψ v φ y * GlobalTheory.LatVac.psiAt ψ v (y ⬝ᵥ z) =
      ∫ x, φ (x - z) * ((toCirc _ hn (x ⬝ᵥ y) : Circle) : ℂ) ∂(Measure.pi fun _ : κ => measV ψ v) := by
    intro y
    unfold fourV
    rw [← integral_mul_const]
    have h1 : ∀ x : κ → Fv F v, φ x * GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ y) * GlobalTheory.LatVac.psiAt ψ v (y ⬝ᵥ z) =
        φ x * GlobalTheory.LatVac.psiAt ψ v ((x + z) ⬝ᵥ y) := by
      intro x
      rw [add_dotProduct, AddChar.map_add_eq_mul, dotProduct_comm z y, mul_assoc]
    simp only [h1]
    rw [← integral_sub_right_eq_self (μ := Measure.pi fun _ : κ => measV ψ v)
      (fun x => φ x * GlobalTheory.LatVac.psiAt ψ v ((x + z) ⬝ᵥ y)) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [sub_add_cancel, coe_toCirc]
  have hg : (fun x : κ → Fv F v => φ (x - z)) ∈ GlobalTheory.SplitWeil.SB (κ → Fv F v) :=
    ⟨hφ.1.comp_continuous (continuous_id.sub continuous_const),
      hφ.2.comp_homeomorph (Homeomorph.subRight z)⟩
  have h2 := (GlobalTheory.SplitWeil.FourierPi.fourier_pi_of_conductor hcond hself hg).2
  show ∫ y, fourV ψ v φ y * GlobalTheory.LatVac.psiAt ψ v (y ⬝ᵥ z) ∂(Measure.pi fun _ : κ => measV ψ v) = φ (-z)
  simp only [hinner]
  rw [h2, zero_sub]

end GlobalTheory.WeylFour.LocInv
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChangeGen

open Matrix GlobalTheory.SympChange

variable {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]

def upM (T : Matrix κ κ K) : Matrix (κ ⊕ κ) (κ ⊕ κ) K := fromBlocks 1 T 0 1

theorem weylM_mem : (weylM : Matrix (κ ⊕ κ) (κ ⊕ κ) K) ∈ Submonoid.closure (gens (F := K) (κ := κ)) :=
  Submonoid.subset_closure (Or.inr rfl)

theorem leviM_mem (A : Matrix κ κ K) (h : IsUnit A.det) :
    leviM A ∈ Submonoid.closure (gens (F := K) (κ := κ)) :=
  Submonoid.subset_closure (Or.inl (Or.inl ⟨A, h, rfl⟩))

theorem unipM_mem (S : Matrix κ κ K) (h : Sᵀ = S) :
    unipM S ∈ Submonoid.closure (gens (F := K) (κ := κ)) :=
  Submonoid.subset_closure (Or.inl (Or.inr ⟨S, h, rfl⟩))

theorem upM_eq (T : Matrix κ κ K) :
    upM T = weylM * unipM (-T) * (weylM * weylM * weylM) := by
  simp [upM, weylM, unipM, fromBlocks_multiply]

theorem upM_mem (T : Matrix κ κ K) (h : Tᵀ = T) :
    upM T ∈ Submonoid.closure (gens (F := K) (κ := κ)) := by
  rw [upM_eq]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ weylM_mem (unipM_mem _ (by rw [transpose_neg, h])))
    (Submonoid.mul_mem _ (Submonoid.mul_mem _ weylM_mem weylM_mem) weylM_mem)

theorem isSymp_mul {G H : Matrix (κ ⊕ κ) (κ ⊕ κ) K} (hG : IsSymp G) (hH : IsSymp H) :
    IsSymp (G * H) := by
  unfold IsSymp at *
  calc (G * H)ᵀ * weylM * (G * H) = Hᵀ * (Gᵀ * weylM * G) * H := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = weylM := by rw [hG, hH]

theorem isSymp_upM (T : Matrix κ κ K) (h : Tᵀ = T) : IsSymp (upM T) := by
  simp [IsSymp, upM, weylM, fromBlocks_transpose, fromBlocks_multiply, h]

theorem weyl_sq : (weylM : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * weylM = -1 := by
  simp [weylM, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

theorem exists_sym_isUnit (a c : Matrix κ κ K) (hs : aᵀ * c = cᵀ * a)
    (hinj : ∀ x, a *ᵥ x = 0 → c *ᵥ x = 0 → x = 0) :
    ∃ T : Matrix κ κ K, Tᵀ = T ∧ IsUnit (a + T * c).det := by
  classical
  let P : Finset κ → Prop := fun s => ∀ y, (∀ i ∉ s, (a *ᵥ y) i = 0) → a *ᵥ y = 0
  have hP0 : P ∅ := fun y hy => funext fun i => hy i (Finset.notMem_empty i)
  obtain ⟨s, hs_mem, hmax⟩ := Finset.exists_max_image (Finset.univ.filter P) Finset.card
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, hP0⟩⟩
  have hsP : P s := (Finset.mem_filter.1 hs_mem).2
  have key : ∀ z : κ → K, (∀ i ∈ s, z i = 0) → (∀ y, z ⬝ᵥ (a *ᵥ y) = 0) → z = 0 := by
    intro z hzs hzo
    funext j
    by_cases hj : j ∈ s
    · exact hzs j hj
    · have hnot : ¬ P (insert j s) := by
        intro hP'
        have := hmax (insert j s) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hP'⟩)
        rw [Finset.card_insert_of_notMem hj] at this
        omega
      simp only [P, not_forall] at hnot
      obtain ⟨y, hy, hne⟩ := hnot
      have hvj : (a *ᵥ y) j ≠ 0 := by
        intro h0
        apply hne
        apply hsP y
        intro i hi
        by_cases hij : i = j
        · rw [hij]; exact h0
        · exact hy i (by simp [hij, hi])
      have hsum : z ⬝ᵥ (a *ᵥ y) = z j * (a *ᵥ y) j := by
        unfold dotProduct
        apply Finset.sum_eq_single j
        · intro i _ hij
          by_cases his : i ∈ s
          · rw [hzs i his, zero_mul]
          · rw [hy i (by simp [hij, his]), mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      have h0 := hzo y
      rw [hsum] at h0
      exact (mul_eq_zero.1 h0).resolve_right hvj
  set T : Matrix κ κ K := diagonal fun i => if i ∈ s then 1 else 0 with hTdef
  have hTe : ∀ w : κ → K, ∀ i, (T *ᵥ w) i = (if i ∈ s then 1 else 0) * w i := fun w i => by
    simp [hTdef, mulVec_diagonal]
  have hx : ∀ x, (a + T * c) *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [add_mulVec, ← mulVec_mulVec] at hx
    have hx2 : ∀ i, (a *ᵥ x) i + (if i ∈ s then 1 else 0) * (c *ᵥ x) i = 0 := fun i => by
      rw [← hTe]; exact congrFun hx i
    have hax : a *ᵥ x = 0 := hsP x (fun i hi => by
      have := hx2 i
      rwa [if_neg hi, zero_mul, add_zero] at this)
    have hcs : ∀ i ∈ s, (c *ᵥ x) i = 0 := fun i hi => by
      have := hx2 i
      rwa [if_pos hi, one_mul, hax, Pi.zero_apply, zero_add] at this
    have horth : ∀ y, (c *ᵥ x) ⬝ᵥ (a *ᵥ y) = 0 := fun y => by
      calc (c *ᵥ x) ⬝ᵥ (a *ᵥ y) = x ⬝ᵥ ((cᵀ * a) *ᵥ y) := by
            rw [← mulVec_mulVec, dotProduct_mulVec x cᵀ, vecMul_transpose]
        _ = x ⬝ᵥ ((aᵀ * c) *ᵥ y) := by rw [hs]
        _ = (a *ᵥ x) ⬝ᵥ (c *ᵥ y) := by
            rw [← mulVec_mulVec, dotProduct_mulVec x aᵀ, vecMul_transpose]
        _ = 0 := by rw [hax, zero_dotProduct]
    exact hinj x hax (key _ hcs horth)
  refine ⟨T, by simp [hTdef], isUnit_iff_ne_zero.2 fun hdet => ?_⟩
  obtain ⟨v, hv, hmv⟩ := exists_mulVec_eq_zero_iff.2 hdet
  exact hv (hx v hmv)

theorem symp_blocks {a b c d : Matrix κ κ K} (h : IsSymp (fromBlocks a b c d)) :
    aᵀ * c = cᵀ * a ∧ aᵀ * d = 1 + cᵀ * b ∧ bᵀ * d = dᵀ * b := by
  simp only [IsSymp, weylM, fromBlocks_transpose, fromBlocks_multiply] at h
  obtain ⟨h11, h12, -, h22⟩ := fromBlocks_inj.1 h
  simp at h11 h12 h22
  refine ⟨(neg_add_eq_zero.1 h11).symm, ?_, (neg_add_eq_zero.1 h22).symm⟩
  rw [← h12]; abel

theorem mem_of_isUnit {a b c d : Matrix κ κ K} (h : IsSymp (fromBlocks a b c d)) (ha : IsUnit a.det) :
    fromBlocks a b c d ∈ Submonoid.closure (gens (F := K) (κ := κ)) := by
  obtain ⟨e1, e2, e3⟩ := symp_blocks h
  have haa : a * a⁻¹ = 1 := mul_nonsing_inv a ha
  have hai : a⁻¹ * a = 1 := nonsing_inv_mul a ha
  have hT1 : a⁻¹ᵀ * aᵀ = 1 := by rw [← transpose_mul, haa, transpose_one]
  have hT2 : aᵀ * a⁻¹ᵀ = 1 := by rw [← transpose_mul, hai, transpose_one]
  set Y := c * a⁻¹ with hYdef
  have hY : Yᵀ = Y := by
    rw [hYdef, transpose_mul]
    calc a⁻¹ᵀ * cᵀ = a⁻¹ᵀ * cᵀ * (a * a⁻¹) := by rw [haa, Matrix.mul_one]
      _ = a⁻¹ᵀ * (cᵀ * a) * a⁻¹ := by simp only [Matrix.mul_assoc]
      _ = a⁻¹ᵀ * (aᵀ * c) * a⁻¹ := by rw [e1]
      _ = (a⁻¹ᵀ * aᵀ) * c * a⁻¹ := by simp only [Matrix.mul_assoc]
      _ = c * a⁻¹ := by rw [hT1, Matrix.one_mul]
  have hd : d = a⁻¹ᵀ + Y * b := by
    calc d = (a⁻¹ᵀ * aᵀ) * d := by rw [hT1, Matrix.one_mul]
      _ = a⁻¹ᵀ * (aᵀ * d) := by rw [Matrix.mul_assoc]
      _ = a⁻¹ᵀ + (a⁻¹ᵀ * cᵀ) * b := by rw [e2, Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc]
      _ = a⁻¹ᵀ + Y * b := by rw [← transpose_mul, ← hYdef, hY]
  set X := a⁻¹ * b with hXdef
  have hX : Xᵀ = X := by
    have e3' := e3
    rw [hd, Matrix.mul_add, transpose_add, Matrix.add_mul, transpose_mul, hY, transpose_transpose] at e3'
    simp only [← Matrix.mul_assoc] at e3'
    rw [hXdef, transpose_mul]
    exact add_right_cancel e3'
  have hG : fromBlocks a b c d = unipM Y * leviM a * upM X := by
    simp only [unipM, leviM, upM, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]
    congr 1
    · rw [hXdef, ← Matrix.mul_assoc, haa, Matrix.one_mul]
    · rw [hYdef, Matrix.mul_assoc, hai, Matrix.mul_one]
    · rw [hd, hXdef, hYdef, add_comm]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc a a⁻¹ b, haa, Matrix.one_mul]
  rw [hG]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (unipM_mem _ hY) (leviM_mem _ ha)) (upM_mem _ hX)

theorem mem_closure_gens : ∀ (K : Type) [Field K] [CharZero K] (κ : Type) [Fintype κ] [DecidableEq κ]
    (G : Matrix (κ ⊕ κ) (κ ⊕ κ) K),
    GlobalTheory.SympChange.IsSymp G → G ∈ Submonoid.closure (GlobalTheory.SympChange.gens (F := K) (κ := κ)) := by
  intro K _ _ κ _ _ G hG
  rw [← fromBlocks_toBlocks G] at hG ⊢
  set a := G.toBlocks₁₁
  set b := G.toBlocks₁₂
  set c := G.toBlocks₂₁
  set d := G.toBlocks₂₂
  obtain ⟨e1, -, -⟩ := symp_blocks hG

  have hL : (-(weylM * (fromBlocks a b c d)ᵀ * weylM)) * fromBlocks a b c d = 1 := by
    have h := hG
    unfold IsSymp at h
    have e : weylM * (fromBlocks a b c d)ᵀ * weylM * fromBlocks a b c d
        = weylM * ((fromBlocks a b c d)ᵀ * weylM * fromBlocks a b c d) := by simp only [Matrix.mul_assoc]
    rw [Matrix.neg_mul, e, h, weyl_sq, neg_neg]
  have hinj : ∀ x, a *ᵥ x = 0 → c *ᵥ x = 0 → x = 0 := by
    intro x hax hcx
    have hv : fromBlocks a b c d *ᵥ Sum.elim x 0 = 0 := by
      rw [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, hax, hcx, mulVec_zero, mulVec_zero]
      simp
    have h0 : Sum.elim x (0 : κ → K) = 0 := by
      rw [← Matrix.one_mulVec (Sum.elim x 0), ← hL, ← mulVec_mulVec, hv, mulVec_zero]
    funext i
    exact congrFun h0 (Sum.inl i)
  obtain ⟨T, hT, hu⟩ := exists_sym_isUnit a c e1 hinj
  have hH : upM T * fromBlocks a b c d = fromBlocks (a + T * c) (b + T * d) c d := by
    simp [upM, fromBlocks_multiply]
  have hHs : IsSymp (fromBlocks (a + T * c) (b + T * d) c d) := hH ▸ isSymp_mul (isSymp_upM T hT) hG
  have hinv : upM (-T) * upM T = (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) := by
    simp [upM, fromBlocks_multiply]
  have : fromBlocks a b c d = upM (-T) * fromBlocks (a + T * c) (b + T * d) c d := by
    rw [← hH, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  rw [this]
  exact Submonoid.mul_mem _ (upM_mem _ (by rw [transpose_neg, hT])) (mem_of_isUnit hHs hu)

end GlobalTheory.SympChangeGen
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChangeBij

open GlobalTheory.SympChange

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem spAct_one' {R : Type} [CommRing R] [Algebra F R] (w : (κ → R) × (κ → R)) :
    spAct (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) w = w := by
  have h1 : (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  simp only [spAct, h1, Matrix.one_mulVec]
  rfl

theorem spAct_mul' {R : Type} [CommRing R] [Algebra F R] (G G' : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (w : (κ → R) × (κ → R)) :
    spAct (G * G') w = spAct G (spAct G' w) := by
  have h : Sum.elim (spAct G' w).1 (spAct G' w).2 = G'.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2 := by
    funext i; cases i <;> rfl
  conv_rhs => rw [spAct, h]
  simp only [spAct, Matrix.map_mul (f := algebraMap F R), Matrix.mulVec_mulVec]

variable [NumberField F]

def HasOpB (ψ : AddChar (AF F) ℂ) (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop :=
  ∃ (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    Function.Surjective ei ∧ (∀ Φ ∈ schA F κ, e Φ ∈ schA F κ) ∧
    (∀ w, ∀ Φ ∈ schA F κ, e (schr ψ w Φ) = schr ψ (spAct G w) (e Φ)) ∧
    (∀ v, (SB _).map (ev v) = SB _) ∧ (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = 0 → φ = 0) ∧
    (∀ v w, ∀ φ ∈ SB (κ → Fv F v),
      ev v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) = schr (GlobalTheory.LatVac.psiAt ψ v) (spAct G w) (ev v φ)) ∧
    (∀ᶠ v in cofinite, ev v (indO v) = indO v) ∧
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = indO v) →
      e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)) ∧
    Set.BijOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ))

theorem hasOpB_one (ψ : AddChar (AF F) ℂ) : HasOpB (κ := κ) ψ 1 := by
  refine ⟨LinearMap.id, ContinuousLinearMap.id ℂ _, fun _ => LinearMap.id, Function.surjective_id, fun Φ h => h,
    fun w Φ _ => by simp [spAct_one'], fun v => Submodule.map_id _, fun v φ _ h => h, fun v w φ _ => by simp [spAct_one'],
    Filter.Eventually.of_forall fun v => rfl, fun f φ _ _ => rfl, ?_⟩
  simpa using Set.bijOn_id (schA F κ : Set ((κ → AF F) → ℂ))

theorem hasOpB_mul {ψ : AddChar (AF F) ℂ} {G G' : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hG : HasOpB ψ G) (hG' : HasOpB ψ G') :
    HasOpB ψ (G * G') := by
  obtain ⟨e, ei, ev, hs, hm, hh, hSB, hi, hl, hind, hp, hb⟩ := hG
  obtain ⟨e', ei', ev', hs', hm', hh', hSB', hi', hl', hind', hp', hb'⟩ := hG'
  have hmem : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev' v φ ∈ SB (κ → Fv F v) := fun v φ hφ => by
    rw [← hSB' v]; exact Submodule.mem_map_of_mem hφ
  refine ⟨e ∘ₗ e', ei.comp ei', fun v => ev v ∘ₗ ev' v, hs.comp hs', fun Φ h => hm _ (hm' _ h), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w Φ hΦ
    simp only [LinearMap.comp_apply]
    rw [hh' w Φ hΦ, hh _ _ (hm' _ hΦ), spAct_mul']
  · intro v
    rw [Submodule.map_comp, hSB', hSB]
  · intro v φ hφ h0
    exact hi' v φ hφ (hi v _ (hmem v φ hφ) h0)
  · intro v w φ hφ
    simp only [LinearMap.comp_apply]
    rw [hl' v w φ hφ, hl v _ _ (hmem v φ hφ), spAct_mul']
  · filter_upwards [hind, hind'] with v h1 h2
    simp only [LinearMap.comp_apply, h2, h1]
  · intro f φ hφ hφv
    simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [hp' f φ hφ hφv, hp _ _ (fun v => hmem v _ (hφ v))]
    filter_upwards [hφv, hind'] with v h1 h2
    rw [h1, h2]
  · rw [LinearMap.coe_comp]
    exact hb.comp hb'

theorem hasOpB_of_mem_closure {ψ : AddChar (AF F) ℂ} (hgen : ∀ G ∈ gens (F := F) (κ := κ), HasOpB ψ G) :
    ∀ G ∈ Submonoid.closure (gens (F := F) (κ := κ)), HasOpB ψ G := fun G hG =>
  Submonoid.closure_induction (fun x hx => hgen x hx) (hasOpB_one ψ) (fun _ _ _ _ hx hy => hasOpB_mul hx hy) hG

theorem bijOn_of_inv (e e' : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) (hm : ∀ Φ ∈ schA F κ, e Φ ∈ schA F κ)
    (hm' : ∀ Φ ∈ schA F κ, e' Φ ∈ schA F κ) (h1 : ∀ Φ ∈ schA F κ, e' (e Φ) = Φ) (h2 : ∀ Φ ∈ schA F κ, e (e' Φ) = Φ) :
    Set.BijOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) :=
  Set.InvOn.bijOn (f' := e') ⟨fun Φ h => h1 Φ h, fun Φ h => h2 Φ h⟩ (fun Φ h => hm Φ h) (fun Φ h => hm' Φ h)

end GlobalTheory.SympChangeBij
end
end

section

noncomputable section

open Formalism.BasicNotions

namespace GlobalTheory.GoodIdemTie

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.factPrime

theorem idemTie_of_tameTie (hG : GlobalTheory.Published.GreenCuspidal) (D : D7) (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ)
    (hT : GlobalTheory.DimPartsCompare.TameTie D om) : GlobalTheory.DimPartsCompare.IdemTie D om :=
  hT.idemTie hG.green

end GlobalTheory.GoodIdemTie

end
end
