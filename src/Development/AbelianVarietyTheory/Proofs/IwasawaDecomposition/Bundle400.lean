module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle256
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle277
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle395
public import Formalism.LocalToGlobal.Columns.Bundle021
public import Formalism.LocalToGlobal.Columns.ChainTwOk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicLiftTypePrimeReductions
public import Formalism.LocalRingCardinality.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle018
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle340
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle341

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.HD.TupPin

theorem isTwist_types (B : Base) (f : Fr B.toPre) (T : TwDat B) :
    ∀ ξ ∈ T.set f, Chr.IsTwist B.host (Set.range B.host.g) ξ := by
  have a1 : Chr.IsTwist B.host (Set.range B.host.g) f.del := Chr.isTwist_of_isDelta B.host.pde_prime
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ B.host.pde_prime B.pde_cond.1).1
    (fun ⟨i, h⟩ => (B.host.pde_ne_g i).1 h.symm) f.isDel
  have a2 : Chr.IsTwist B.host (Set.range B.host.g) f.del' := Chr.isTwist_of_isDelta B.host.pde'_prime
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ B.host.pde'_prime B.pde_cond.2).1
    (fun ⟨i, h⟩ => (B.host.pde_ne_g i).2 h.symm) f.isDel'
  rintro ξ ((rfl | rfl | rfl) | ⟨w, rfl⟩)
  · exact Chr.isTwist_one _ _
  · exact a1
  · exact a2
  · have h := T.psi_tw w
    have a3 : Chr.IsTwist B.host (Set.range B.host.g) (T.psi w) := ⟨h.1, h.2.1, h.2.2.1, fun v hv =>
      ⟨(h.2.2.2 v hv).1, (h.2.2.2 v hv).2.1, (h.2.2.2 v hv).2.2.1,
        fun ⟨i, hi⟩ => (h.2.2.2 v hv).2.2.2 (Or.inr (Or.inl ⟨i, hi.symm⟩))⟩⟩
    unfold TwDat.xiTw
    split_ifs
    exacts [a2.mul_twist a3, a1.mul_twist a3]

theorem xiTw_unr (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : B.places.Pl) (v : HeightOneSpectrum (𝓞 B.host.E))
    (hv : OverP B.host (B.places.resChar w) v) : (T.xiTw f w).UnrAt v := by
  have hψ : (T.psi w).UnrAt v := fun x _ => (T.psi_is w).atl v hv x
  unfold TwDat.xiTw
  split_ifs with h
  · refine (f.isDel'.unr v fun hn => B.host.pde_ne ?_).mul hψ
    rw [h] at hv
    exact Examples₂.PlacesToy.prime_mem_unique v B.host.pde_prime B.host.pde'_prime hv hn
  · exact (f.isDel.unr v fun hn => h
      (Examples₂.PlacesToy.prime_mem_unique v (B.places.resChar_prime w) B.host.pde_prime hv hn)).mul hψ

end GlobalTheory.Mem.HD.TupPin
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.HD

theorem exists_hilbert_le_O (hR : RayField) (B : Base) (δ : FieldDat B.toPre) (hδ : δ.ray ≤ B.KsC) :
    ∃ M : IntermediateField ℚ ℂ, IsRayFieldIn B.host.φ₀ ⊤ M ∧
      ∀ z ∈ M, IsIntegral ℤ z → ∃ y : B.O, B.embLL (B.OtoLL y) = z := by
  obtain ⟨M, hM⟩ := exists_isRayFieldIn B.host.φ₀ hR (𝔮 := ⊤) top_ne_bot
  refine ⟨M, hM, fun z hz hI => ?_⟩
  have hle : M ≤ δ.ray := RayMono.le_of_isRayFieldIn_of_dvd _ _ _ _ _ _ (natIdeal_ne_bot (modulus_ne_zero B.toPre))
    (Ideal.dvd_iff_le.2 le_top) hM δ.isRay
  obtain ⟨x, hx, rfl⟩ := B.mem_KsC.1 (hδ (hle hz))
  have hx' : IsIntegral ℤ x :=
    (isIntegral_algHom_iff B.embLL.toIntAlgHom B.embLL.injective).1 hI
  obtain ⟨y, hy⟩ := B.O_full x hx hx'
  exact ⟨y, by rw [hy]⟩

theorem twistConductor_not_over_levelPrimes (B : Base) (T : TwDat B) (w : B.places.Pl) {v : HeightOneSpectrum (𝓞 B.host.E)} (hv : v ∈ T.Q w)
    (u : B.Word) (hp : (B.T u).Prime) : ¬ OverP B.host (B.T u) v := by
  intro ho
  obtain ⟨-, h1, -, h2⟩ := (T.psi_tw w).2.2.2 v fun h => ((T.psi_is w).ram v).1 h hv
  have := Examples₂.PlacesToy.prime_mem_unique v h1 hp (Ideal.absNorm_mem _) ho
  exact h2 (this ▸ .inr (.inr (.inr (.inr (.inl ⟨u, rfl⟩)))))

end GlobalTheory.Mem.HD
end

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FreeOnDomain

theorem exists_conj_first_col {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∃ P B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, P.det ≠ 0 ∧ (∀ a : Fin n, B a.succ 0 = 0) ∧ A * P = P * B := by
  first
  | exact @_root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero
  | exact _root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero
  | (apply _root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero <;> assumption)
  | (intros; apply _root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero ..)

theorem exists_conj_triangular (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ P T : Matrix (Fin n) (Fin n) ℂ, P.det ≠ 0 ∧ (∀ a c, c < a → T a c = 0) ∧ A * P = P * T := by
  induction n with
  | zero => exact ⟨1, 1, by simp, fun a => a.elim0, Subsingleton.elim _ _⟩
  | succ n ih =>
    obtain ⟨P, B, hP, hB, e⟩ := exists_conj_first_col A
    obtain ⟨Q, T, hQ, hT, e'⟩ := ih (B.submatrix Fin.succ Fin.succ)
    let D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
      of (Fin.cons (Fin.cons 1 fun _ => 0) fun a => Fin.cons 0 (Q a))
    let T' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
      of (Fin.cons ((B * D) 0) fun a => Fin.cons 0 (T a))
    have hD : D.det = Q.det := by
      rw [det_succ_row_zero, Fin.sum_univ_succ]
      simp only [D, of_apply, Fin.cons_zero, Fin.cons_succ, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
        Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
      rfl
    have hBD : B * D = D * T' := by
      ext a c
      refine Fin.cases ?_ (fun a => ?_) a
      · rw [Matrix.mul_apply (M := D), Fin.sum_univ_succ]
        simp [D, T']
      · refine Fin.cases ?_ (fun c => ?_) c
        · simp [D, T', Matrix.mul_apply, Fin.sum_univ_succ, hB]
        · have := congrFun (congrFun e' a) c
          simpa [D, T', Matrix.mul_apply, Fin.sum_univ_succ] using this
    refine ⟨P * D, T', ?_, fun a c h => ?_, ?_⟩
    · rw [det_mul, hD]; exact mul_ne_zero hP hQ
    · revert h
      refine Fin.cases ?_ (fun a => ?_) a
      · intro h; exact absurd h (by simp)
      · refine Fin.cases ?_ (fun c => ?_) c
        · intro _; simp [T']
        · intro h; simpa [T'] using hT a c (Fin.succ_lt_succ_iff.1 h)
    · rw [← Matrix.mul_assoc, e, Matrix.mul_assoc, hBD, Matrix.mul_assoc]

theorem toBlocks₁₂_eq_zero {p q : ℕ} {F F' : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hF : IsUnit F.det)
    (h2 : IsUnit F.toBlocks₂₂.det) (h2' : IsUnit F'.toBlocks₂₂.det) (h : moeb F' 0 = moeb F 0) :
    (F⁻¹ * F').toBlocks₁₂ = 0 := by
  rw [moeb_zero, moeb_zero] at h
  have h1 : F'.toBlocks₁₂ = F.toBlocks₁₂ * (F.toBlocks₂₂⁻¹ * F'.toBlocks₂₂) := by
    rw [← Matrix.mul_assoc, ← h, nonsing_inv_mul_cancel_right _ _ h2']
  have e : F' * fromBlocks 0 0 0 1 =
      F * fromBlocks (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (F.toBlocks₂₂⁻¹ * F'.toBlocks₂₂) := by
    conv_lhs => rw [← fromBlocks_toBlocks F']
    conv_rhs => enter [1]; rw [← fromBlocks_toBlocks F]
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, ← h1, mul_nonsing_inv_cancel_left _ _ h2]
  have e2 : (F⁻¹ * F') * fromBlocks 0 0 0 1 =
      fromBlocks (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (F.toBlocks₂₂⁻¹ * F'.toBlocks₂₂) := by
    rw [Matrix.mul_assoc, e, nonsing_inv_mul_cancel_left _ _ hF]
  rw [← fromBlocks_toBlocks (F⁻¹ * F'), fromBlocks_multiply] at e2
  simpa using congrArg toBlocks₁₂ e2

theorem exists_conj_block {r j : ℕ} (hj : j ≤ r) (M : Matrix (Fin r) (Fin r) ℂ)
    (hM : (reindex (idx hj) (idx hj) M).toBlocks₁₂ = 0) :
    ∃ b t : Matrix (Fin r) (Fin r) ℂ, b.det ≠ 0 ∧ (∀ a c : Fin r, (c : ℕ) < r - j → ¬ (a : ℕ) < r - j → b a c = 0) ∧
      (∀ a c, c < a → t a c = 0) ∧ M * b = b * t := by
  set G := reindex (idx hj) (idx hj) M with hG
  obtain ⟨P, T, hP, hT, e⟩ := exists_conj_triangular _ G.toBlocks₁₁
  obtain ⟨Q, S, hQ, hS, e'⟩ := exists_conj_triangular _ G.toBlocks₂₂
  have hm : G * fromBlocks P 0 0 Q = fromBlocks P 0 0 Q * fromBlocks T 0 (Q⁻¹ * (G.toBlocks₂₁ * P)) S := by
    conv_lhs => rw [← fromBlocks_toBlocks G, hM]
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e, e', mul_nonsing_inv_cancel_left _ _ hQ.isUnit]
  refine ⟨(fromBlocks P 0 0 Q).submatrix (idx hj) (idx hj),
    (fromBlocks T 0 (Q⁻¹ * (G.toBlocks₂₁ * P)) S).submatrix (idx hj) (idx hj), ?_, fun a c hc ha => ?_,
    fun a c h => ?_, ?_⟩
  · rw [det_submatrix_equiv_self, det_fromBlocks_zero₁₂]; exact mul_ne_zero hP hQ
  · obtain ⟨a, rfl⟩ := (idx hj).symm.surjective a
    obtain ⟨c, rfl⟩ := (idx hj).symm.surjective c
    rcases a with a | a <;> rcases c with c | c
    · rw [idx_symm_inl] at hc; omega
    · simp
    · simp
    · rw [idx_symm_inr] at ha; exact absurd a.2 ha
  · obtain ⟨a, rfl⟩ := (idx hj).symm.surjective a
    obtain ⟨c, rfl⟩ := (idx hj).symm.surjective c
    rw [Fin.lt_def] at h
    rcases a with a | a <;> rcases c with c | c
    · rw [idx_symm_inl, idx_symm_inl] at h
      simpa using hT a c (by rw [Fin.lt_def]; omega)
    · simp
    · rw [idx_symm_inl, idx_symm_inr] at h
      have := a.2; omega
    · rw [idx_symm_inr, idx_symm_inr] at h
      simpa using hS a c h
  · have : M = G.submatrix (idx hj) (idx hj) := by simp [hG]
    rw [submatrix_mul_equiv, ← hm, ← submatrix_mul_equiv _ _ _ (idx hj), ← this]

theorem eq_one_of_domPt_lact_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, domPt X hj κ (lact γ x) = domPt X hj κ x → γ = 1 := by
  intro E _ _ _ r j X hj Tau _ κ hp γ hγ x hx h
  obtain ⟨x, ho, b₀, hb₀, rfl⟩ := ortho_holds r X x hx
  rw [KU.lact_rmul', domPt_rmul X hj κ hb₀, domPt_rmul X hj κ hb₀] at h
  have hx := IC.orth_mem_dom X ho
  have hx' := IC.orth_mem_dom X (KU.isOrth_lact X hγ ho)
  have key : ∀ τ : X.Ψ, ∃ b t : Matrix (Fin r) (Fin r) ℂ, b.det ≠ 0 ∧
      (∀ a c : Fin r, (c : ℕ) < r - j → ¬ (a : ℕ) < r - j → b a c = 0) ∧
      (∀ a c, c < a → t a c = 0) ∧ (mat x τ)⁻¹ * mat (lact γ x) τ * b = b * t := by
    intro τ
    refine exists_conj_block hj _ ?_
    obtain ⟨s, rfl⟩ := κ.surjective τ
    have u0 : IsUnit (mat (x0F X) (κ s)).det := (det_x0F X _).isUnit
    have hF : IsUnit (frameCo X hj x (κ s)).det := by
      rw [frameCo, det_reindex_self, det_mul]
      exact (isUnit_nonsing_inv_det _ u0).mul (hx _).1.isUnit
    have := toBlocks₁₂_eq_zero hF (frameCo_isUnit₂₂ X hj hp hx _) (frameCo_isUnit₂₂ X hj hp hx' _) (congrFun h s)
    rw [frameCo, frameCo, inv_reindex, Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ u0] at this
    simp only [reindex_apply, submatrix_mul_equiv] at this ⊢
    rwa [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ u0] at this
  choose b t hb hb0 ht e using key
  have e' : ∀ τ, mat (lact γ x) τ * b τ = mat x τ * b τ * t τ := fun τ => by
    rw [Matrix.mul_assoc, ← e, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ (hx τ).1.isUnit]
  refine X.Γ_free γ hγ (rmul x fun τ => b τ)
    (GlobalTheory.PointOfFrames.rmul_mem_dom X hx _ hb (by rw [hp]; exact hb0)) (fun τ => t τ) (fun τ => ⟨?_, ht τ⟩) ?_
  · intro h0
    have h1 := congrArg det (e' τ)
    have h0' : (t τ).det = 0 := h0
    rw [det_mul, det_mul, h0', mul_zero] at h1
    exact mul_ne_zero (hx' τ).1 (hb τ) h1
  · exact (KU.lact_rmul' X γ x _).trans (funext e')

end GlobalTheory.FreeOnDomain
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch

theorem pi_conj {X : Fields} {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (Λ Λ' : LevFam X.E X.K n SG) (x : ∀ w : SG, GL (Fin n) (𝓞 X.E ⧸ w.1.asIdeal))
    (hH : ∀ w hbar, hbar ∈ (Λ w).H ↔ x w * hbar * (x w)⁻¹ ∈ (Λ' w).H)
    (hL : ∀ w (hbar : ↥(Λ w).H) (hbar' : ↥(Λ' w).H), hbar'.1 = x w * hbar.1 * (x w)⁻¹ →
      (Λ w).lam hbar = (Λ' w).lam hbar') :
    (∀ g : GLG (E := X.E) (n := n) (SG := SG), g ∈ Λ.grp ↔ (fun w => x w * g w * (x w)⁻¹) ∈ Λ'.grp) ∧
    ∀ (g : ↥Λ.grp) (g0 : ↥Λ'.grp), (∀ w, g0.1 w = x w * g.1 w * (x w)⁻¹) → Λ.chr g = Λ'.chr g0 := by
  refine ⟨fun g => ?_, fun g g0 hg => ?_⟩
  · simp only [LevFam.grp, Subgroup.mem_pi, Set.mem_univ, true_implies]
    exact forall_congr' fun w => hH w (g w)
  · rw [LevFam.chr_apply, LevFam.chr_apply]
    exact Finset.prod_congr rfl fun w _ => hL w _ _ (hg w)

section Gen

variable {Xf : Fields} {Pr : Primes Xf} {R : Ranks} {Ch : Chars Xf Pr R.m}
  {sel : HeightOneSpectrum (𝓞 Xf.F) → HeightOneSpectrum (𝓞 Xf.E)} {S : Set ℕ} {mu : Tup Xf.F Xf.E Xf.K S}
  {cst : LocCst Xf (rowSG Pr sel mu)} {L : ChIdx Xf Pr R (QE sel (mu : Chr Xf.F Xf.E Xf.K))} {G : ChGlob Xf R.m} {m2 : ℕ}

theorem cosetOne (hX : Xf.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hsel : IsSel Xf sel) (hs : cst.sharp = true)
    (hok : L.Ok Ch sel mu cst G m2) : ∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
      SameDC (Pr := Pr) true j P.1 1 (L.h j b P) := by
  have hB := clL_base hok hX hPr hCh hs
  intro j
  induction j with
  | zero =>
    intro _ b P _
    rw [hok.zero_h]
    exact ⟨1, one_mem _, 1, one_mem _, by simp⟩
  | succ i ih =>
    intro hj b P hP
    by_cases hi : i < m2
    · obtain ⟨al, hal⟩ := hok.nonvan i hi b P
      have h1 := ih (by omega) al P hP
      have hs1 := hok.stabG i al P hP
      have hs2 := hok.stabG (i + 1) b P hP
      have h2 := (GlobalTheory.T.unfoldedDatum_ne_zero_iff_doubleCoset Ch sel mu cst L G m2 hX hPr hCh hsel hs hok i hi P hP _ _ hs1 hs2 (by rw [hs]; exact h1)).1 hal
      have h3 := twSurjG G.σ₀ hB hi P hP _ hs2 h2
      rwa [hs] at h3
    · obtain rfl : i = m2 := by omega
      rw [hok.last_h]
      exact ⟨1, one_mem _, 1, one_mem _, by simp⟩

theorem idx_nonempty (hX : Xf.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hsel : IsSel Xf sel) (hs : cst.sharp = true)
    (hok : L.Ok Ch sel mu cst G m2) (hQ : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs) :
    ∀ j, j ≤ m2 + 1 → Nonempty (L.β j) := by
  have hB := clL_base hok hX hPr hCh hs
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨b, -⟩ := hok.zero_uniq
    exact ⟨b⟩
  | succ i ih =>
    intro hj
    by_cases hi : i < m2
    · obtain ⟨al⟩ := ih (by omega)
      obtain ⟨b, -⟩ := hok.surj i hi (fun _ => 1) (fun _ _ => one_mem _) (fun P hP => absurd (hQ P) hP)
        (fun P => ⟨al, (GlobalTheory.T.unfoldedDatum_ne_zero_iff_doubleCoset Ch sel mu cst L G m2 hX hPr hCh hsel hs hok i hi P (hQ P) _ _ (hok.stabG i al P (hQ P))
          (one_mem _) (by rw [hs]; exact cosetOne hX hPr hCh hsel hs hok i (by omega) al P (hQ P))).2
          (twNonVanG G.σ₀ hB hi P (hQ P))⟩)
      exact ⟨b⟩
    · obtain rfl : i = m2 := by omega
      obtain ⟨b, -⟩ := hok.last_uniq
      exact ⟨b⟩

end Gen

end GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch


open Classical in
theorem idx_match : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (a : I.ι) (i : ℕ), 1 ≤ i → i < B.R.m →
    ∀ b : Idx I.sel (I.tup a) (I.idx a) i, ∃ (b0 : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) i)
      (x : ∀ w : (B.primes X).vGs, GL (Fin (B.R.N i)) (𝓞 B.fields.E ⧸ w.1.asIdeal)),
      (i + 1 = B.R.m → ∀ w, x w = 1) ∧
      (∀ g : GLG (E := B.fields.E) (n := B.R.N i) (SG := (B.primes X).vGs), g ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).grp ↔
        (fun w => x w * g w * (x w)⁻¹) ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).grp) ∧
      ∀ (g : ↥(levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).grp) (g0 : ↥(levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).grp),
        (∀ w, g0.1 w = x w * g.1 w * (x w)⁻¹) →
        (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).chr g = (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).chr g0 := by
  intro B X I h l a i hi1 hi b
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hoka := h.idx_ok a
  have hok0 := h.idx_ok I.mu0
  generalize B.R.m - 2 = m2 at hoka hok0
  have hm := hoka.hm
  have hQ0 : ∀ P : rowSG (B.primes X) I.sel (I.tup I.mu0), P.1 ∈ (B.primes X).vGs := fun P =>
    (Finset.mem_union.1 P.2).resolve_right (by
      have e : QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty I
      rw [e]
      exact Finset.notMem_empty _)
  rcases b with ⟨_ | β, hb⟩
  · exact absurd (hb.2 hi) (by simp)
  have key : ∃ β0 : (I.idx I.mu0).β i, ∀ w : (B.primes X).vGs, ∃ (r κ : AutY B.fields B.R i),
      r ∈ Loc.R1 B.fields.E (B.R.N i) (cOf B.R i) ∧ κ ∈ Jat (Pr := B.primes X) true i w.1 ∧
      (I.idx a).h i β ⟨w.1, Finset.mem_union_left _ w.2⟩ = r * (I.idx I.mu0).h i β0 ⟨w.1, Finset.mem_union_left _ w.2⟩ * κ ∧
      (i + 1 = B.R.m → r = 1) := by
    by_cases hlast : i = m2 + 1
    · subst hlast
      obtain ⟨β0, -⟩ := hok0.last_uniq
      refine ⟨β0, fun w => ⟨1, 1, one_mem _, one_mem _, ?_, fun _ => rfl⟩⟩
      rw [hoka.last_h, hok0.last_h]
      simp
    · obtain ⟨β0⟩ := idx_nonempty hX l.pr h.ch_ok h.sel_ok (h.sharp I.mu0) hok0 hQ0 i (by omega)
      refine ⟨β0, fun w => ?_⟩
      obtain ⟨r1, hr1, κ1, hκ1, e1⟩ :=
        cosetOne hX l.pr h.ch_ok h.sel_ok (h.sharp a) hoka i (by omega) β ⟨w.1, Finset.mem_union_left _ w.2⟩ w.2
      obtain ⟨r0, hr0, κ0, hκ0, e0⟩ :=
        cosetOne hX l.pr h.ch_ok h.sel_ok (h.sharp I.mu0) hok0 i (by omega) β0 ⟨w.1, Finset.mem_union_left _ w.2⟩ w.2
      refine ⟨r1 * r0⁻¹, κ0⁻¹ * κ1, mul_mem hr1 (inv_mem hr0), mul_mem (inv_mem hκ0) hκ1, ?_, fun e => absurd e (by omega)⟩
      rw [e1, e0]
      group
  obtain ⟨β0, hw⟩ := key
  choose r κ hr hκ he hr1 using hw
  have gc := fun w => GlobalTheory.T.doubleCoset_reps_conjugate_level_groups I.Ch I.sel (I.tup a) (I.tup I.mu0) (I.cst a) (I.cst I.mu0) (I.idx a) (I.idx I.mu0) I.glob m2
    hX l.pr h.ch_ok (h.sharp a) (h.sharp I.mu0) hoka hok0 i (by omega) β β0 w (r w) (κ w) (hr w) (hκ w) (he w)
  choose x hx1 hxH hxL using gc
  refine ⟨⟨some β0, by simp [hi]⟩, x, fun e w => hx1 w (hr1 w e), ?_⟩
  exact pi_conj ((I.idx a).levG i β) ((I.idx I.mu0).levG i β0) x hxH hxL

end GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_unitaryAdelic_lift_typePrime_reductions : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (n : ℕ)
    (x : ∀ w : (B.primes X).vGs, GL (Fin n) (𝓞 B.fields.E ⧸ w.1.asIdeal)), ∃ t : GA B n,
      (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf t p ∧ p.deco.1.N = stdLat B.fields.E n) ∧
      (∀ v : HeightOneSpectrum (𝓞 B.host.F), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) →
        bc (prV (E := B.host.E) v) t = 1) ∧
      ∀ (w : (B.primes X).vGs) (r j : Fin n), HasRes w.1 (adAt B.host.F w.1 ((t : Matrix (Fin n) (Fin n) _) r j)) ((x w).1 r j) := by
  first | exact @GlobalTheory.Mem.Col2.TC.ChTw.Match.exists_unitary_lift | exact GlobalTheory.Mem.Col2.TC.ChTw.Match.exists_unitary_lift | (intros; apply GlobalTheory.Mem.Col2.TC.ChTw.Match.exists_unitary_lift <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitianChart_complex_rational_integral_forms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → ValuationCompatibleChart (D := (I.rec7 l Z)) (I.fm l u a) eY (fun _ => True) chOf (lat := fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) K := by
  first | exact @GlobalTheory.Mem.Col2.TC.val_tied | exact GlobalTheory.Mem.Col2.TC.val_tied | (intros; apply GlobalTheory.Mem.Col2.TC.val_tied <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.DualOffLevel

theorem mem_divs_of {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A}
    (h : P ∈ divs a) : a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · exact (hf.mem_toFinset.1 h)
  · simp at h

theorem isLocBasis_dual_iff_N : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (u : B.Word) (a : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u a w → ∀ (i : ℕ) (hi : i ≤ B.R.m) (c : (I.stp u a i).Cl) (Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (dualSet (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c))) Bm ↔ Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (((I.stp u a i).rep c).1.1.deco.1.N : Set (Sp B.fields.E (B.R.N i))) Bm := by
  intro B X I hOk hPins l Z Y u a w hw i hi c Bm
  classical
  have hpP : ((I.rec7 l Z).what₂.places.resChar w).Prime := (I.rec7 l Z).what₂.places.resChar_prime w
  have hTP : (B.T u).Prime := l.pr.T_prime u
  have hpT : ¬ (I.rec7 l Z).what₂.places.resChar w ∣ B.T u := fun h => hw.1 ((Nat.prime_dvd_prime_iff_eq hpP hTP).1 h)
  obtain ⟨hG, -, hc⟩ := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 i hi
  have hL := (hc u a).1 c
  have hS : dualSet (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)
      (latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) =
      (((I.stp u a i).rep c).1.1.deco.1.Lsh : Set (Sp B.fields.E (B.R.N i))) := by
    rw [hG, hL]
    exact GlobalTheory.Mem.Col2.ValTie.dualSet_std (E := B.fields.E) _ (fun _ => rfl) _
  rw [hS]
  set d := ((I.stp u a i).rep c).1.1.deco with hd
  have hTP' : ∀ P : (B.primes X).vT u, (((B.T u : ℕ) : 𝓞 B.fields.E)) ∈ (P : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal := by
    intro P
    have hpi := mem_divs_of P.2
    rw [← l.pr.piT_norm u]
    exact Ideal.mul_mem_right _ _ hpi
  have hLN : ∀ x ∈ d.1.Lsh, ((B.T u : ℕ) : B.fields.E) • x ∈ d.1.N := by
    intro x hx
    have := d.2.smul_Lsh_mem_N (a := ((B.T u : ℕ) : 𝓞 B.fields.E)) (fun P => by rw [map_natCast]; exact hTP' P) hx
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul B.fields.E] at this
  unfold Formalism.L2.Forms.IsLocBasis
  refine forall_congr' fun x => iff_congr ⟨?_, ?_⟩ Iff.rfl
  · rintro ⟨s, hs, hx⟩
    refine ⟨B.T u * s, fun h => (hpP.dvd_mul.1 h).elim hpT hs, ?_⟩
    have h3 := hLN _ hx
    have e : ((B.T u * s : ℕ) : (I.rec7 l Z).host.E) • x = ((B.T u : ℕ) : (I.rec7 l Z).host.E) • ((s : (I.rec7 l Z).host.E) • x) := by
      rw [smul_smul, ← Nat.cast_mul]
    exact e ▸ h3
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, d.2.N_le_Lsh hx⟩

end GlobalTheory.DualOffLevel
end
