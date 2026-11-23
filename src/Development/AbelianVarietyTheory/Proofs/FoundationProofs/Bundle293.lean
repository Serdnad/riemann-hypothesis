module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle102
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle140
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle173
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle172
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle283
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
namespace GlobalTheory.CoshPowMeas
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
open Filter Topology

variable {p q : ℕ}

theorem continuous_cartanB : Continuous (cartanB : UpqT p q → Matrix (Fin p) (Fin q) ℂ) := by
  have h : Continuous fun g : UpqT p q => GlobalTheory.PolarLogCont.halfLog (UpqT.mat g) :=
    GlobalTheory.PolarLogCont.continuousOn_halfLog.comp_continuous GlobalTheory.UpqTopology.continuous_mat
      fun g => Units.isUnit (show Formalism.UG.Upq p q from g).1
  have hc : Continuous fun M : Mat p q => M.toBlocks₁₂ := by
    refine continuous_matrix fun i j => ?_
    exact continuous_id.matrix_elem (Sum.inl i) (Sum.inr j)
  exact hc.comp h

def sPad (B : Matrix (Fin p) (Fin q) ℂ) (j : Fin q) : ℝ := if (j : ℕ) < p then singVal B j else 0

theorem exists_gram (B : Matrix (Fin p) (Fin q) ℂ) : ∃ V : Matrix (Fin q) (Fin q) ℂ, Vᴴ * V = 1 ∧
    Bᴴ * B = V * Matrix.diagonal (fun j => ((sPad B j : ℝ) : ℂ) ^ 2) * Vᴴ := by
  obtain ⟨U, hU, V, hV, hB⟩ := GlobalTheory.RectSVD.exists_svd_singularValues p q B
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have h2 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  refine ⟨V, h2, ?_⟩
  set D : Matrix (Fin p) (Fin q) ℂ := Matrix.of fun (i : Fin p) (j : Fin q) =>
        if (i : ℕ) = (j : ℕ) then (((Matrix.toEuclideanLin B).singularValues i : ℝ) : ℂ) else 0 with hD
  have hDD : Dᴴ * D = Matrix.diagonal (fun j => ((sPad B j : ℝ) : ℂ) ^ 2) := by
    ext j j'
    rw [Matrix.mul_apply]
    by_cases hj : (j : ℕ) < p
    · rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin p)]
      · by_cases hjj : j = j'
        · subst hjj
          simp [hD, sPad, hj, singVal, sq]
        · have : (j : ℕ) ≠ j' := fun h => hjj (Fin.ext h)
          simp [hD, hjj, this]
      · intro i _ hi
        have : (i : ℕ) ≠ j := fun h => hi (Fin.ext h)
        simp [hD, this]
      · simp
    · rw [Finset.sum_eq_zero]
      · by_cases hjj : j = j'
        · subst hjj
          simp [sPad, hj]
        · simp [hjj]
      · intro i _
        have : (i : ℕ) ≠ j := fun h => hj (h ▸ i.isLt)
        simp [hD, this]
  rw [← hDD]
  conv_lhs => rw [hB]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, h1, Matrix.one_mul]

theorem conj_pow {n : Type} [Fintype n] [DecidableEq n] (V A : Matrix n n ℂ) (h : Vᴴ * V = 1) (k : ℕ) :
    (V * A * Vᴴ) ^ k = V * A ^ k * Vᴴ := by
  induction k with
  | zero => simp [mul_eq_one_comm.1 h]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V, h, Matrix.one_mul]

def coshSum (n : ℕ) (B : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ :=
  ∑ k ∈ Finset.range n, (((2 * k).factorial : ℕ) : ℂ)⁻¹ • (Bᴴ * B) ^ k

theorem continuous_coshSum (n : ℕ) : Continuous (coshSum n : Matrix (Fin p) (Fin q) ℂ → _) := by
  unfold coshSum
  refine continuous_finsetSum _ fun k _ => ?_
  have h : Continuous fun B : Matrix (Fin p) (Fin q) ℂ => Bᴴ * B :=
    continuous_id.matrix_conjTranspose.matrix_mul continuous_id
  exact (h.pow k).const_smul ((((2 * k).factorial : ℕ) : ℂ)⁻¹)

theorem det_coshSum (n : ℕ) (B : Matrix (Fin p) (Fin q) ℂ) : (coshSum n B).det.re =
    ∏ j : Fin q, ∑ k ∈ Finset.range n, sPad B j ^ (2 * k) / ((2 * k).factorial : ℕ) := by
  obtain ⟨V, hV, h⟩ := exists_gram B
  have e : coshSum n B = V * Matrix.diagonal (fun j => ((∑ k ∈ Finset.range n,
      sPad B j ^ (2 * k) / ((2 * k).factorial : ℕ) : ℝ) : ℂ)) * Vᴴ := by
    have e1 : Matrix.diagonal (fun j => ((∑ k ∈ Finset.range n,
      sPad B j ^ (2 * k) / ((2 * k).factorial : ℕ) : ℝ) : ℂ)) = ∑ k ∈ Finset.range n,
        (((2 * k).factorial : ℕ) : ℂ)⁻¹ • (Matrix.diagonal (fun j => ((sPad B j : ℝ) : ℂ) ^ 2)) ^ k := by
      ext i j
      simp only [Matrix.diagonal_pow, Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply]
      split_ifs
      · push_cast
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [pow_mul, div_eq_inv_mul]
      · simp
    rw [e1, coshSum, h, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conj_pow _ _ hV, Matrix.mul_smul, Matrix.smul_mul]
  rw [e, Matrix.det_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.det_diagonal,
    ← Complex.ofReal_prod, Complex.ofReal_re]

theorem prod_cosh_sPad (B : Matrix (Fin p) (Fin q) ℂ) :
    ∏ j : Fin q, Real.cosh (sPad B j) = ∏ i ∈ Finset.range (min p q), Real.cosh (singVal B i) := by
  unfold sPad
  rw [Fin.prod_univ_eq_prod_range (fun j => Real.cosh (if j < p then singVal B j else 0)) q]
  symm
  refine Finset.prod_subset_one_on_sdiff (Finset.range_subset_range.2 (min_le_right p q)) ?_ ?_
  · intro x hx
    have : ¬ x < p := by
      simp only [Finset.mem_sdiff, Finset.mem_range] at hx; omega
    simp [this]
  · intro x hx
    have : x < p := by
      simp only [Finset.mem_range] at hx; omega
    simp [this]

theorem tendsto_det_coshSum (B : Matrix (Fin p) (Fin q) ℂ) :
    Tendsto (fun n => (coshSum n B).det.re) atTop
      (𝓝 (∏ i ∈ Finset.range (min p q), Real.cosh (singVal B i))) := by
  simp only [det_coshSum, ← prod_cosh_sPad]
  exact tendsto_finsetProd _ fun j _ => (Real.hasSum_cosh (sPad B j)).tendsto_sum_nat

theorem measurable_coshPow : ∀ (p q : ℕ) (c : ℝ), Measurable (coshPow c : UpqT p q → ℝ) := by
  intro p q c
  have : BorelSpace (UpqT p q) := (GlobalTheory.UpqTopology.upq_lcsc p q).2.2.2.2.1
  have h : Measurable fun g : UpqT p q =>
      ∏ i ∈ Finset.range (min p q), Real.cosh (singVal (cartanB g) i) := by
    refine measurable_of_tendsto_metrizable
      (f := fun n (g : UpqT p q) => (coshSum n (cartanB g)).det.re) (fun n => ?_)
      (tendsto_pi_nhds.2 fun g => tendsto_det_coshSum _)
    exact (Complex.continuous_re.comp
      (((continuous_coshSum n).comp continuous_cartanB).matrix_det)).measurable
  have e : (coshPow c : UpqT p q → ℝ) = fun g =>
      (∏ i ∈ Finset.range (min p q), Real.cosh (singVal (cartanB g) i)) ^ (-c) := by
    funext g
    exact Real.finsetProd_rpow _ _ (fun i _ => (Real.cosh_pos _).le) _
  rw [e]
  exact h.pow_const _

end GlobalTheory.CoshPowMeas
end
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem gamma_mem_of_dvd {M N : ℕ} (hMN : M ∣ N) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma N) :
    δ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  have key : ∀ k : ℤ, ((k : ZMod N) = 1 → (k : ZMod M) = 1) ∧ ((k : ZMod N) = 0 → (k : ZMod M) = 0) := by
    intro k
    constructor
    · intro h
      have := congrArg (ZMod.castHom hMN (ZMod M)) h
      rwa [map_intCast, map_one] at this
    · intro h
      have := congrArg (ZMod.castHom hMN (ZMod M)) h
      rwa [map_intCast, map_zero] at this
  exact ⟨(key _).1 h1, (key _).2 h2, (key _).2 h3, (key _).1 h4⟩

theorem isKummerPotentialIncrement_linear_laws : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], (∀ (x x' : X.Khat l) (h h' : ℂ → ℤ_[l]), R1 X l x h → R1 X l x' h' → R1 X l (x + x') (h + h')) ∧ R1 X l 0 0 ∧ (∀ (c : ℤ_[l]) (x : X.Khat l) (h : ℂ → ℤ_[l]), R1 X l x h → R1 X l (c • x) (c • h)) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (x : X.Khat l) (h : ℂ → ℤ_[l]), 0 < m.det → R1 X l x h → R1 X l (X.kmap l (X.sl (toGQ m)).toRingEquiv x) (fun z => h (mob (toGQ m) z))) := by
  intro Ω _ _ ε X l _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x x' h h' hx hx' n
    obtain ⟨χ, hK, M, hM, hI⟩ := hx n
    obtain ⟨χ', hK', M', hM', hI'⟩ := hx' n
    refine ⟨χ + χ', ((GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).1 x x' χ χ' hK hK'), M * M', Nat.mul_pos hM hM', ?_⟩
    intro δ hδ z hz
    have e1 := hI δ (gamma_mem_of_dvd (dvd_mul_right M M') hδ) z hz
    have e2 := hI' δ (gamma_mem_of_dvd (dvd_mul_left M' M) hδ) z hz
    have : (h + h') (mob (ofSL δ) z) - (h + h') z = (h (mob (ofSL δ) z) - h z) + (h' (mob (ofSL δ) z) - h' z) := by
      simp only [Pi.add_apply]; ring
    rw [this, map_add (f := _), e1, e2, Pi.add_apply]
  · intro n
    refine ⟨0, (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).2.1, 1, Nat.one_pos, ?_⟩
    intro δ _ z _
    simp
  · intro c x h hx n
    obtain ⟨χ, hK, M, hM, hI⟩ := hx n
    refine ⟨fun δ => PadicInt.toZModPow n c * χ δ, GlobalTheory.T.isKummerCharacterAtLevel_padicInt_smul Ω ε X l n c x χ hK, M, hM, ?_⟩
    intro δ hδ z hz
    have : (c • h) (mob (ofSL δ) z) - (c • h) z = c * (h (mob (ofSL δ) z) - h z) := by
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [this, map_mul, hI δ hδ z hz]
  · intro m x h hm hx n
    obtain ⟨χ, hK, M, hM, hI⟩ := hx n
    refine ⟨fun δ => χ (cj m δ), GlobalTheory.T.isKummerCharacterAtLevel_integral_matrix_conj Ω ε X l n m x χ hm hK, M * m.det.natAbs,
      Nat.mul_pos hM (Int.natAbs_pos.mpr hm.ne'), ?_⟩
    intro δ hδ z hz
    obtain ⟨hc1, hc2⟩ := GlobalTheory.T.integralConjugateSL2Int_laws.1 m M hm δ hδ
    have hmz : mob (toGQ m) z ∈ Hs := GlobalTheory.T.glTwoPosRatMobius_basic_laws.1 (toGQ m) z hz
    have hcomm := GlobalTheory.T.integralConjugateSL2Int_laws.2.2 m δ (cj m δ) hm hc1 z hz
    show PadicInt.toZModPow n (h (mob (toGQ m) (mob (ofSL δ) z)) - h (mob (toGQ m) z)) = χ (cj m δ)
    rw [hcomm]
    exact hI (cj m δ) hc2 (mob (toGQ m) z) hmz

end GlobalTheory.KZ.H3
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.invariant_inner_forms_proportional_weight_line : ∀ (p q : ℕ) (M : GKMod p q) (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (j : M.V →ₗ[ℂ] H₁) (E₁ E₂ : M.V →ₗ[ℂ] H₂), (∀ Z x y, inner ℂ (j (M.act Z x)) (j y) = inner ℂ (j x) (j (M.act (adjZ Z) y))) → (∀ Z x y, inner ℂ (E₁ (M.act Z x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (M.act (adjZ Z) y))) → ∀ (μ : Ix p q → ℚ) (v : M.V), v ∈ wtSub M.act μ → (∀ x ∈ wtSub M.act μ, ∃ c : ℂ, x = c • v) → genSub M.act {v} = ⊤ → ‖j v‖ = 1 → ∀ x y, inner ℂ (E₁ x) (E₂ y) = inner ℂ (E₁ v) (E₂ v) * inner ℂ (j x) (j y) := by
  first | exact @GlobalTheory.FockForm.inner_eq_mul | exact GlobalTheory.FockForm.inner_eq_mul | (intros; apply GlobalTheory.FockForm.inner_eq_mul <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_sub_mem_intLoc (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) :
    ∃ x : E, y - (1 : Fv F v) ⊗ₜ[F] x ∈ intLoc F E v := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add y z hy hz =>
    obtain ⟨x, hx⟩ := hy
    obtain ⟨x', hx'⟩ := hz
    refine ⟨x + x', ?_⟩
    rw [TensorProduct.tmul_add, add_sub_add_comm]
    exact add_mem hx hx'
  | tmul a e =>
    obtain ⟨m, hm, he⟩ := exists_integral_multiples ℤ ℚ ({e} : Finset E)
    have he' : IsIntegral ℤ (m • e) := he e (Finset.mem_singleton_self e)
    have hmF : (m : F) ≠ 0 := by exact_mod_cast hm
    have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
    have hcont : Continuous fun z : Fv F v => (m : F)⁻¹ • a - z := continuous_sub_left _
    obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) F v).exists_mem_open
      (hO.preimage hcont) ⟨(m : F)⁻¹ • a, by simp⟩
    refine ⟨k • (m • e), ?_⟩
    have hk' : (m : F)⁻¹ • a - algebraMap F (Fv F v) k ∈ v.adicCompletionIntegers F := hk
    have h := tmul_mem_intLoc (E := E) hk' ⟨m • e, he'⟩
    convert h using 1
    change _ = ((m : F)⁻¹ • a - algebraMap F (Fv F v) k) ⊗ₜ[F] (m • e)
    rw [TensorProduct.sub_tmul, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      ← Int.cast_smul_eq_zsmul F m e, inv_smul_smul₀ hmF]

theorem isIntegral_of_absBar_le_one (v : HeightOneSpectrum (𝓞 F)) (x : E)
    (hx : ∀ τ : E →ₐ[F] FvBar F v, absBar F v (τ x) ≤ 1) :
    ∃ p : Polynomial (v.valuationSubringAtPrime F), p.Monic ∧
      p.eval₂ ((algebraMap F E).comp (v.valuationSubringAtPrime F).subtype) x = 0 := by
  classical
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hmon := minpoly.monic hint
  have h1 : (minpoly F x).map (algebraMap F (FvBar F v)) ∈ Polynomial.lifts (valBar F v).integer.subtype := by
    refine Polynomial.Splits.mem_lift_of_roots_mem_range (IsAlgClosed.splits _) (hmon.map _) _ fun a ha => ?_
    have ha' : a ∈ (minpoly F x).rootSet (FvBar F v) := by
      rw [Polynomial.rootSet_def]; simpa [Polynomial.aroots_def] using ha
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at ha'
    obtain ⟨τ, rfl⟩ := ha'
    exact ⟨⟨τ x, hx τ⟩, rfl⟩
  have h2 : minpoly F x ∈ Polynomial.lifts (v.valuationSubringAtPrime F).subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts] at h1 ⊢
    intro n
    obtain ⟨c, hc⟩ := h1 n
    have h3 : absBar F v (algebraMap F (FvBar F v) ((minpoly F x).coeff n)) ≤ 1 := by
      rw [← Polynomial.coeff_map, ← hc]; exact c.2
    rw [IsScalarTower.algebraMap_apply F (Fv F v) (FvBar F v), absBar_algebraMap] at h3
    have h4 : Valued.v (algebraMap F (Fv F v) ((minpoly F x).coeff n)) ≤ 1 :=
      Valued.toNormedField.norm_le_one_iff.1 (by exact_mod_cast h3)
    refine ⟨⟨(minpoly F x).coeff n, ?_⟩, rfl⟩
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm.trans_le h4
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic h2 hmon
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval₂_map, hq]
  exact minpoly.aeval F x

theorem one_tmul_mem_intLoc (v : HeightOneSpectrum (𝓞 F)) (x : E)
    (hx : absFin F v ((1 : Fv F v) ⊗ₜ[F] x) ≤ 1) : (1 : Fv F v) ⊗ₜ[F] x ∈ intLoc F E v := by
  let : Algebra (v.valuationSubringAtPrime F) E :=
    ((algebraMap F E).comp (v.valuationSubringAtPrime F).subtype).toAlgebra
  have : IsScalarTower (𝓞 F) (v.valuationSubringAtPrime F) E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : IsIntegral (v.valuationSubringAtPrime F) x :=
    isIntegral_of_absBar_le_one v x fun τ => by simpa using (absFin_le_iff F v).1 hx τ
  obtain ⟨⟨s, hs⟩, h2⟩ := IsIntegral.exists_multiple_integral_of_isLocalization v.asIdeal.primeCompl x h1
  have h3 : IsIntegral ℤ ((s : F) • x) := isIntegral_trans _ h2
  have hv : v.valuation F (s : F) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hs
  have hs0 : (s : F) ≠ 0 := fun e => by simp [e] at hv
  have h4 : algebraMap F (Fv F v) (s : F)⁻¹ ∈ v.adicCompletionIntegers F :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (s : F)⁻¹).trans_le (by rw [map_inv₀, hv, inv_one])
  have h := tmul_mem_intLoc (E := E) h4 ⟨_, h3⟩
  convert h using 1
  change _ = (algebraMap F (Fv F v) (s : F)⁻¹) ⊗ₜ[F] ((s : F) • x)
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, inv_smul_smul₀ hs0]

theorem mem_intLoc_iff_absFin_le_one {v : HeightOneSpectrum (𝓞 F)} {y : Fv F v ⊗[F] E} :
    y ∈ intLoc F E v ↔ absFin F v y ≤ 1 := by
  refine ⟨absFin_le_one_of_mem_intLoc, fun hy => ?_⟩
  obtain ⟨x, hx⟩ := exists_sub_mem_intLoc v y
  have h1 : absFin F v ((1 : Fv F v) ⊗ₜ[F] x) ≤ 1 := by
    have := absFin_add_le F v y (-(y - (1 : Fv F v) ⊗ₜ[F] x))
    rw [absFin_neg, ← sub_eq_add_neg, sub_sub_cancel] at this
    exact this.trans (max_le hy (absFin_le_one_of_mem_intLoc hx))
  simpa using add_mem hx (one_tmul_mem_intLoc v x h1)

theorem algebraMap_basis_repr {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) (i : ι) :
    algebraMap (Fv F v) (FvBar F v) ((Algebra.TensorProduct.basis (Fv F v) b.traceDual).repr y i) =
      ∑ τ : E →ₐ[F] FvBar F v, finEmb F v τ y * τ (b i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => simp only [map_add (f := _), Finsupp.add_apply, hy, hz, add_mul, Finset.sum_add_distrib]
  | tmul a e =>
    rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul,
      ← IsScalarTower.algebraMap_apply, Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply,
      trace_eq_sum_embeddings, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [finEmb_tmul, map_mul]; ring

theorem absFin_eq_zero_iff {v : HeightOneSpectrum (𝓞 F)} {y : Fv F v ⊗[F] E} : absFin F v y = 0 ↔ y = 0 := by
  refine ⟨fun hy => ?_, fun h => by rw [h, absFin_zero]⟩
  have h0 : ∀ τ : E →ₐ[F] FvBar F v, finEmb F v τ y = 0 := fun τ =>
    (absBar_eq_zero F v).1 (le_antisymm ((absFin_le_iff F v).1 hy.le τ) zero_le)
  let b := Module.finBasis F E
  refine (Algebra.TensorProduct.basis (Fv F v) b.traceDual).ext_elem fun i => ?_
  refine (algebraMap (Fv F v) (FvBar F v)).injective ?_
  rw [algebraMap_basis_repr]
  simp [h0]

end GlobalTheory.AdelicU

end
end

section

namespace GlobalTheory.AdelicU

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))

omit [NumberField E] in
theorem mem_levelOpen_iff_projFin {g : GAd σ J} :
    g ∈ levelOpen σ J L ↔ projFin σ J g ∈ levelOffFin σ J L ∅ := by
  simp [mem_levelOpen, mem_levelOffFin]

omit [NumberField E] in
theorem mem_stabLoc_iff_embLocFin {v : HeightOneSpectrum (𝓞 F)} {g : GLoc σ J v} :
    g ∈ stabLoc σ J L v ↔ embLocFin σ J v g ∈ levelOffFin σ J L ∅ := by
  rw [mem_levelOffFin]
  refine ⟨fun h => ⟨by simp, fun u _ => ?_⟩, fun h => by simpa using h.2 v (by simp)⟩
  by_cases e : u = v
  · subst e; simpa using h
  · rw [projFinLoc_embLocFin_ne σ J e]; exact one_mem _

omit [NumberField E] in
theorem image_ofFin_levelOffFin (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ofFin σ J '' (levelOffFin σ J L S : Set (GFin σ J)) = (levelOff σ J L S : Set (GAd σ J)) := by
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hg
    have h : g ∈ (ofFin σ J).range := by rw [range_ofFin]; exact (mem_levelOff.1 hg).1
    obtain ⟨y, rfl⟩ := h
    exact ⟨y, hg, rfl⟩

variable [Submodule.IsFullLattice E L]

theorem isOpen_isCompact_levelOffFin_empty :
    IsOpen (levelOffFin σ J L ∅ : Set (GFin σ J)) ∧ IsCompact (levelOffFin σ J L ∅ : Set (GFin σ J)) := by
  have hfg : L.FG := Submodule.IsLattice.fg (A := E) L
  obtain ⟨K, hK, ho, hc⟩ := GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab F E σ n J L hfg
    Submodule.IsFullLattice.span_eq_top
  have e : levelOffFin σ J L ∅ = K := by
    ext g
    have h := mem_levelOpen_iff_latHat σ J hfg (ofFin σ J g)
    have h2 : Formalism.MainNotions.StandardLattice.finMat σ J (ofFin σ J g) = (HA.mat (Af F) σ J g).1 :=
      congrArg (fun x => (HA.mat (Af F) σ J x).1) (projFin_ofFin σ J g)
    rw [mem_levelOpen_iff_projFin, projFin_ofFin, h2] at h
    exact h.trans (hK g).symm
  rw [e]
  exact ⟨ho, hc⟩

theorem isOpen_levelOffFin_empty : IsOpen (levelOffFin σ J L ∅ : Set (GFin σ J)) :=
  (isOpen_isCompact_levelOffFin_empty σ J L).1

theorem isOpen_levelOpen : IsOpen (levelOpen σ J L : Set (GAd σ J)) := by
  have : (levelOpen σ J L : Set (GAd σ J)) = projFin σ J ⁻¹' (levelOffFin σ J L ∅ : Set (GFin σ J)) :=
    Set.ext fun _ => mem_levelOpen_iff_projFin σ J L
  rw [this]
  exact (isOpen_levelOffFin_empty σ J L).preimage (continuous_projFin σ J)

theorem isOpen_stabLoc (v : HeightOneSpectrum (𝓞 F)) : IsOpen (stabLoc σ J L v : Set (GLoc σ J v)) := by
  have : (stabLoc σ J L v : Set (GLoc σ J v)) = embLocFin σ J v ⁻¹' (levelOffFin σ J L ∅ : Set (GFin σ J)) :=
    Set.ext fun _ => mem_stabLoc_iff_embLocFin σ J L
  rw [this]
  exact (isOpen_levelOffFin_empty σ J L).preimage (continuous_embLocFin σ J v)

theorem isCompact_stabLoc (v : HeightOneSpectrum (𝓞 F)) : IsCompact (stabLoc σ J L v : Set (GLoc σ J v)) := by
  have : (stabLoc σ J L v : Set (GLoc σ J v)) = embLocFin σ J v ⁻¹' (levelOffFin σ J L ∅ : Set (GFin σ J)) :=
    Set.ext fun _ => mem_stabLoc_iff_embLocFin σ J L
  rw [this]
  exact (Function.LeftInverse.isClosedEmbedding (projFinLoc_embLocFin_self σ J v) (continuous_projFinLoc σ J v)
    (continuous_embLocFin σ J v)).isCompact_preimage (isOpen_isCompact_levelOffFin_empty σ J L).2

theorem isCompact_levelOffFin (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsCompact (levelOffFin σ J L S : Set (GFin σ J)) := by
  have : (levelOffFin σ J L S : Set (GFin σ J)) =
      (levelOffFin σ J L ∅ : Set (GFin σ J)) ∩ ofFin σ J ⁻¹' (awayPts σ J S : Set (GAd σ J)) := by
    ext g
    change ofFin σ J g ∈ levelOff σ J L S ↔ ofFin σ J g ∈ levelOff σ J L ∅ ∧ ofFin σ J g ∈ awayPts σ J S
    simp only [levelOff_eq, finAwayPts, Subgroup.mem_inf, awayPts_empty, Subgroup.mem_top]
    tauto
  rw [this]
  exact (isOpen_isCompact_levelOffFin_empty σ J L).2.inter_right
    ((isClosed_awayPts σ J S).preimage (continuous_ofFin σ J))

theorem isCompact_levelOff (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsCompact (levelOff σ J L S : Set (GAd σ J)) := by
  rw [← image_ofFin_levelOffFin]
  exact (isCompact_levelOffFin σ J L S).image (continuous_ofFin σ J)

theorem isCompact_levelFin : IsCompact (levelFin σ J L : Set (GAd σ J)) := isCompact_levelOff σ J L ∅

end GlobalTheory.AdelicU
end
