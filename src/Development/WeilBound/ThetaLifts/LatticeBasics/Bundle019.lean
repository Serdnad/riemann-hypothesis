module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LocGram
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.HasIwasawaArch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.WeilBound.ThetaLifts.LatticeBasics.ThetaBox
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.Bundle001
public import Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinC
public import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle008
import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactIntV
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Spectrum
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
public import Development.WeilBound.ThetaLifts.LatticeBasics.SliceSeminorm

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ThK.Dbl.Hgt

open scoped Matrix TensorProduct
open NumberField GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl

theorem unitary_iff_commute {ι : Type} [Fintype ι] [DecidableEq ι] {Q Θ : Matrix ι ι ℂ} {s : ℂ} (hs : s ≠ 0) (hQ : IsUnit Q)
    (B g : GL ι ℂ) (hB : B.1ᴴ * (s • (Q * Θ)) * B.1 = 1) (hg : g.1ᴴ * Q * g.1 = Q) :
    (B⁻¹ * g * B).1ᴴ * (B⁻¹ * g * B).1 = 1 ↔ Commute g.1 Θ := by
  have u : ∀ x : GL ι ℂ, IsUnit x.1ᴴ := fun x => (Matrix.isUnit_conjTranspose _).2 x.isUnit
  have h1 : (B⁻¹).1ᴴ * (B⁻¹).1 = s • (Q * Θ) := by
    refine (u B).mul_left_cancel (B.isUnit.mul_right_cancel ?_)
    rw [hB, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_assoc, Units.inv_mul]; simp
  have h2 : (B⁻¹ * g * B).1ᴴ * (B⁻¹ * g * B).1 = B.1ᴴ * (s • (g.1ᴴ * Q * (Θ * g.1))) * B.1 := by
    simp only [Units.val_mul, Matrix.conjTranspose_mul]
    calc _ = B.1ᴴ * (g.1ᴴ * ((B⁻¹).1ᴴ * (B⁻¹).1) * g.1) * B.1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
  rw [h2, ← hB, B.isUnit.mul_left_inj, (u B).mul_right_inj, (smul_right_injective _ hs).eq_iff]
  conv_lhs => rhs; rw [← hg, Matrix.mul_assoc]
  rw [((u g).mul hQ).mul_right_inj]
  exact eq_comm

theorem exists_cartan_frame {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ = M) (hd : IsUnit M) (h : IsCartan M θ) {r : ℝ}
    (hr : r ≠ 0) : ∃ (b : GL (Fin n) ℂ) (ε : Fin n → Bool) (s : ℂ), s ≠ 0 ∧
      b.1ᴴ * ((r : ℂ) • Mᵀ) * b.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧
      b.1ᴴ * (s • (((r : ℂ) • Mᵀ) * θ)) * b.1 = 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hM' : Mᵀᴴ = Mᵀ := congrArg Matrix.transpose hM
  have h4 : θᴴ * Mᵀ = Mᵀ * θ := by
    have e : θᴴ * Mᵀ * θ = Mᵀ := by
      conv_rhs => rw [← h2]
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]; rfl
    calc _ = θᴴ * Mᵀ * (θ * θ) := by rw [h1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e]
  set N : Matrix (Fin n) (Fin n) ℂ := ((|r| : ℝ) : ℂ) • (Mᵀ * θ) with hN
  have hr' : ((|r| : ℝ) : ℂ) ≠ 0 := by simpa using hr
  have hNh : N.IsHermitian := by
    change Nᴴ = N
    rw [hN, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hM', h4]; simp
  obtain ⟨ε, b, hb⟩ := Frames.exists_congr_diagonal_sign hNh (by
    rw [hN, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ hr') (mul_ne_zero ((Matrix.isUnit_iff_isUnit_det _).1 hd).ne_zero
      (Matrix.isUnit_det_of_left_inverse h1).ne_zero))
  have hb1 : b.1ᴴ * N * b.1 = 1 := by
    rw [hb, ← Matrix.diagonal_one]
    congr 1
    funext i
    have hx : (fun j => b.1 j i) ≠ 0 := fun e => by
      have := congrFun (congrFun b.inv_mul i) i
      simp [Matrix.mul_apply, show ∀ j, b.1 j i = 0 from congrFun e] at this
    have e : (b.1ᴴ * N * b.1) i i = ((|r| : ℝ) : ℂ) * ((θ *ᵥ fun j => b.1 j i) ⬝ᵥ M *ᵥ star fun j => b.1 j i) := by
      rw [hN, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, dotProduct_comm, ← Matrix.vecMul_transpose,
        ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rfl
    have := mul_pos (abs_pos.2 hr) (h3 _ hx)
    rw [← Complex.re_ofReal_mul, ← e, hb, Matrix.diagonal_apply_eq] at this
    split_ifs at this ⊢
    · rfl
    · norm_num at this
  set s : ℂ := ((|r| : ℝ) : ℂ) / r with hs
  have hrc : (r : ℂ) ≠ 0 := by simpa using hr
  have hss : s * s = 1 := by
    rw [hs, div_mul_div_comm, ← Complex.ofReal_mul, abs_mul_abs_self, Complex.ofReal_mul, div_self (mul_ne_zero hrc hrc)]
  have hsN : s • (((r : ℂ) • Mᵀ) * θ) = N := by rw [Matrix.smul_mul, smul_smul, hs, div_mul_cancel₀ _ hrc]
  set S := b.1ᴴ * ((r : ℂ) • Mᵀ) * b.1 with hS
  have hSh : S.IsHermitian := by
    change Sᴴ = S
    simp [hS, Matrix.conjTranspose_smul, hM', Matrix.mul_assoc]
  have hS1 : S = s • ((b⁻¹).1 * θ * b.1) := by
    have : (r : ℂ) • Mᵀ = s • (N * θ) := by
      rw [← hsN, Matrix.smul_mul, smul_smul, hss, one_smul, Matrix.mul_assoc, h1, Matrix.mul_one]
    have e : b.1ᴴ * N = (b⁻¹).1 := by
      rw [← Matrix.one_mul (b⁻¹).1, ← hb1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [hS, this, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, e]
  have hS2 : S * S = 1 := by
    rw [hS1, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hss, one_smul]
    calc _ = (b⁻¹).1 * θ * (b.1 * (b⁻¹).1) * θ * b.1 := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Units.mul_inv, Matrix.mul_one, Matrix.mul_assoc _ θ θ, h1, Matrix.mul_one, Units.inv_mul]
  have hD := hSh.conjStarAlgAut_star_eigenvectorUnitary
  have hD2 := congrArg (Unitary.conjStarAlgAut ℂ _ (star hSh.eigenvectorUnitary)) hS2
  rw [map_mul, hD, map_one, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] at hD2
  rw [Unitary.conjStarAlgAut_star_apply] at hD
  set U := hSh.eigenvectorUnitary
  refine ⟨b * Unitary.toUnits U, fun i => decide (hSh.eigenvalues i = 1), s, left_ne_zero_of_mul_eq_one hss, ?_, ?_⟩
  · refine Eq.trans ?_ (hD.trans ?_)
    · simp only [hS, Units.val_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]; rfl
    · congr 1
      funext i
      have : (hSh.eigenvalues i : ℂ) * hSh.eigenvalues i = 1 := congrFun (Matrix.diagonal_injective hD2) i
      rcases mul_self_eq_one_iff.1 this with e | e
      · rw [if_pos (by simpa using e)]; exact e
      · rw [if_neg (by simp only [decide_eq_true_eq]; intro e'; rw [e'] at e; norm_num at e)]; exact e
  · rw [hsN, Units.val_mul, Matrix.conjTranspose_mul]
    calc _ = (Unitary.toUnits U).1ᴴ * (b.1ᴴ * N * b.1) * (Unitary.toUnits U).1 := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hb1, Matrix.mul_one]; exact U.2.1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem exists_arch (hc : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) {J : Matrix (Fin n) (Fin n) E}
    {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ = M) (hd : IsUnit M) (h : IsCartan M θ) {r : ℝ} (hr : r ≠ 0)
    (hJ : J.map τ.1 = (r : ℂ) • Mᵀ) : ∃ b : GL (Fin n) (w.Completion ⊗[F] E),
      HasIwasawa σ (dblGram finSumFinEquiv J) (KArch σ _ w b) ∧ ∀ g : GArch σ (dblGram finSumFinEquiv J) w,
        g ∈ KArch σ _ w b ↔ Commute ((matHom _ σ _ g).1.map (infEmb τ)) (blkMat finSumFinEquiv θ (-θ)) := by
  obtain ⟨b, ε, s, hs, h1, h2⟩ := exists_cartan_frame hM hd h hr
  let e := RingEquiv.ofBijective _ (infEmb_bijective hc τ)
  have e1 : bc (infEmb τ) (bc e.symm.toRingHom b) = b := Units.ext (Matrix.ext fun i j => e.apply_symm_apply _)
  have e2 : ∀ {m : ℕ} (X : Matrix (Fin m) (Fin m) E), (JR w.Completion X).map (infEmb τ) = X.map τ.1 := fun X => by
    ext r s; simp [JR, inclR]
  have inj : ∀ {m : ℕ} {X Y : Matrix (Fin m) (Fin m) (w.Completion ⊗[F] E)}, X = Y ↔ X.map (infEmb τ) = Y.map (infEmb τ) :=
    (Matrix.map_injective e.injective).eq_iff.symm
  refine ⟨bc e.symm.toRingHom b, hasIwasawa_arch hc rfl w _ ε (inj.2 ?_), fun g => ?_⟩
  · rw [locGram, Matrix.map_mul, Matrix.map_mul, Frames.map_cT_sigR hc, e2, hJ, Matrix.diagonal_map (map_zero _)]
    refine (show _ = _ from ?_).trans (h1.trans ?_)
    · conv_rhs => rw [← e1]
      rfl
    · congr 1; funext i; split_ifs <;> simp
  · have hQ : (dblGram finSumFinEquiv J).map τ.1 = blkMat finSumFinEquiv ((r : ℂ) • Mᵀ) (-((r : ℂ) • Mᵀ)) := by
      rw [dblGram, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _), hJ]
    have hu : IsUnit ((r : ℂ) • Mᵀ).det := by
      rw [Matrix.det_smul, Matrix.det_transpose]
      exact (mul_ne_zero (pow_ne_zero _ (by simpa using hr)) ((Matrix.isUnit_iff_isUnit_det _).1 hd).ne_zero).isUnit
    refine Iff.trans ?_ (unitary_iff_commute (Q := (dblGram finSumFinEquiv J).map τ.1) hs ?_ (blkGL finSumFinEquiv (b, b))
      (bc (infEmb τ) (matHom _ σ _ g)) ?_ ?_)
    · rw [mem_stabArch]
      change _ * 1 * _ = 1 ↔ _
      rw [inj, Matrix.mul_one, Matrix.map_mul, Frames.map_cT_sigR hc, Matrix.map_one _ (map_zero _) (map_one _)]
      conv_rhs => rw [← e1, ← bc_blkGL, ← map_inv, ← map_mul, ← map_mul]
      rfl
    · rw [hQ, Matrix.isUnit_iff_isUnit_det, det_blkMat, Matrix.det_neg]
      exact hu.mul ((isUnit_one.neg.pow _).mul hu)
    · rw [hQ, blkMat_mul, neg_mul_neg, val_blkGL, show (blkMat finSumFinEquiv b.1 b.1)ᴴ = blkMat finSumFinEquiv b.1ᴴ b.1ᴴ from
        cT_blkMat _ (starRingEnd ℂ) _ _, Matrix.mul_smul, Matrix.smul_mul, blkMat_mul, blkMat_mul]
      rw [Matrix.mul_smul, Matrix.smul_mul] at h2
      rw [← blkMat_one finSumFinEquiv, ← h2]
      let A : Matrix (Fin n) (Fin n) ℂ := b.1ᴴ * (((r : ℂ) • Mᵀ) * θ) * b.1
      exact (congrArg (fun X => Matrix.submatrix X finSumFinEquiv.symm finSumFinEquiv.symm) (Matrix.fromBlocks_smul s A 0 0 A)).trans
        (by simp only [smul_zero]; rfl)
    · have := inj.1 (show cT _ (matHom _ σ _ g).1 * JR _ _ * (matHom _ σ _ g).1 = JR _ _ from g.2)
      rwa [Matrix.map_mul, Matrix.map_mul, Frames.map_cT_sigR hc, e2] at this

end GlobalTheory.ThK.Dbl.Hgt

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl.Bad

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open PositivityTheory.ThKG.Loc (idem)
open PositivityTheory.ThKG.Loc.Cone

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing in
theorem sq_ne (ν : @Measure (κ → AF F) (borel _)) (hν : @Measure.IsAddHaarMeasure _ _ _ (borel _) ν) {Φ : (κ → AF F) → ℂ}
    (h : Φ ∈ schA F κ) (h0 : Φ ≠ 0) : ∫ u, Φ u * star (Φ u) ∂ν ≠ 0 := fun z => by
  obtain ⟨c, -, hc⟩ := lD_haar ν hν
  have e := hc Φ h Φ h
  have i := (sl_int (box_mem h h) 0).norm
  have ct := GroundTheory.Automorphic.GJMatrix.continuous_of_mem_schwartzBruhatPi h
  have : ∀ u, boxFun Φ (star Φ) (Sum.elim u u) = ((‖Φ u‖ ^ 2 : ℝ) : ℂ) := fun u => by simp [boxFun, Complex.mul_conj']
  rw [z, mul_zero, lD_int (box_mem h h)] at e
  simp only [sl, add_zero, this, Complex.norm_real, norm_pow, norm_norm] at e i
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero, integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) i,
    Continuous.ae_eq_iff_eq _ (show Continuous fun x => ‖Φ x‖ ^ 2 from ct.norm.pow 2) continuous_zero] at e
  exact h0 (funext fun u => by simpa using congrFun e u)

theorem norm_eig {G : Type} [Group G] {om : G →* Module.End ℂ ((κ → AF F) → ℂ)} (hu : IsUnitaryOn (adeleClass F) om)
    (hp : ∀ g, ∀ φ ∈ schA F κ, om g φ ∈ schA F κ) {g : G} {Φ} (h : Φ ∈ schA F κ) (h0 : Φ ≠ 0) {c : ℂ} (hc : om g Φ = c • Φ) :
    ‖c‖ = 1 := by
  letI : MeasurableSpace (κ → AF F) := borel _
  have : BorelSpace (κ → AF F) := ⟨rfl⟩
  obtain ⟨a, a0, ha⟩ := lD_haar (F := F) (κ := κ) Measure.addHaar inferInstance
  have e := lD_unit hu hp g h h
  rw [hc, star_smul, GlobalTheory.SchwartzBox.boxFun_smul_left, GlobalTheory.SchwartzBox.boxFun_smul_right, smul_smul, map_smul, smul_eq_mul,
    mul_eq_right₀ (ha Φ h Φ h ▸ mul_ne_zero (Complex.ofReal_ne_zero.2 a0.ne') (sq_ne _ inferInstance h h0)), Complex.star_def,
    Complex.mul_conj'] at e
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 (by exact_mod_cast e)

theorem schr_unit {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (ν : @Measure (κ → AF F) (borel _))
    (hν : @Measure.IsAddHaarMeasure _ _ _ (borel _) ν) (w) (A C : (κ → AF F) → ℂ) :
    ∫ u, schr ψ w A u * star (schr ψ w C u) ∂ν = ∫ u, A u * star (C u) ∂ν := by
  letI : MeasurableSpace (κ → AF F) := borel _
  have : BorelSpace (κ → AF F) := ⟨rfl⟩
  rw [← integral_add_right_eq_self (fun u => A u * star (C u)) w.1]
  refine integral_congr_ae (.of_forall fun u => ?_)
  simp only [schr, star_mul']
  rw [mul_mul_mul_comm, Complex.star_def, Complex.mul_conj', GlobalTheory.StdCharFromIsStd.norm_psi hψ]
  simp

open scoped Classical in
theorem ev_adm (x : κ → AF F) : (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := fun g _ =>
  ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => mul_comm _ _⟩

variable {f : SInf F κ} {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hS : ∀ v, φ v ∈ SB _)
  (hs : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
include hS hs

theorem rest_ex (v : Pl F) : ∃ r, Rest (evFin F v) (φ v) r ∧ tens (evFin F v) (φ v) r = pure f φ := by
  classical
  obtain ⟨r, h1, h2⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hs
  have e := h2 (φ v)
  rw [Function.update_eq_self] at e
  exact ⟨r, ⟨h1, e ▸ GlobalTheory.TensUniq.pure_mem_schA f φ hS hs⟩, e⟩

theorem eig {v : Pl F} {S} {c : ℂ} (h : Acts (evFin F v) S (φ v) (c • φ v)) : S (pure f φ) = c • pure f φ := by
  obtain ⟨r, h1, h2⟩ := rest_ex (f := f) hS hs v
  rw [← h2, h r h1]
  exact funext fun x => mul_assoc _ _ _

theorem fix_real {S} (h : Acts (evI F) S f f) : S (pure f φ) = pure f φ := by
  refine h (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) ⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA f φ hS hs⟩
  refine finprod_congr fun v => congrArg _ (funext fun i => ?_)
  have := congrArg (evFin F v) (congrFun (hz (idem F v) (evI_idem v)) i)
  rw [Pi.smul_apply, smul_eq_mul, map_mul, evFin_idem_self, one_mul, Pi.zero_apply, map_zero] at this
  rw [Pi.add_apply, map_add (f := _), this, add_zero]

theorem fix_box {v : Pl F} {S} (h : Acts (evFin F v) S (boxFun (φ v) (star (φ v))) (boxFun (φ v) (star (φ v)))) :
    S (boxFun (pure f φ) (star (pure f φ))) = boxFun (pure f φ) (star (pure f φ)) := by
  obtain ⟨r, h1, h2⟩ := rest_ex (f := f) hS hs v
  have e : tens (evFin F v) (boxFun (φ v) (star (φ v))) (boxFun r (star r)) = boxFun (pure f φ) (star (pure f φ)) := by
    rw [← h2]
    funext x
    simp only [tens, boxFun, Pi.star_apply, star_mul', Function.comp_def]
    ring
  have m := GlobalTheory.TensUniq.pure_mem_schA f φ hS hs
  rw [← e]
  refine h _ ⟨fun x z hz => ?_, e ▸ box_mem m m⟩
  exact congrArg₂ (fun a b => a * star b) (h1.1 (x ∘ Sum.inl) (z ∘ Sum.inl) fun u hu => congrArg (· ∘ Sum.inl) (hz u hu))
    (h1.1 (x ∘ Sum.inr) (z ∘ Sum.inr) fun u hu => congrArg (· ∘ Sum.inr) (hz u hu))

end GlobalTheory.ThK.Dbl.Bad

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl.Box

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dense

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {κ β : Type} [Fintype κ] [Fintype β] {m n : ℕ}

variable {A : Spc F E m} {Y : Spc F E n} {B : Base F E}

theorem isSec_of {dd} {χ : Chr F E} {om S l} (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ ⊕ κ) B.ψ dd χ om S l)
    {K : Subgroup (G2 σ Y)} {Φ} (hΦ : Φ ∈ kfin om K) : IsSec K χ (((m : ℂ) - n) / 2) fun x => l (om x Φ) := by
  obtain ⟨N, _, h0, h1, h2⟩ := hΦ
  obtain ⟨c1, c2⟩ := sec_cont_law h (h0 h1)
  refine ⟨c1, c2, Submodule.finiteDimensional_of_le (S₂ := N.map (LinearMap.pi fun x => l ∘ₗ om x)) (Submodule.span_le.2 ?_)⟩
  rintro _ ⟨k, rfl⟩
  exact ⟨_, h2 k.1 k.2 Φ h1, funext fun x => by simp [map_mul]⟩

theorem polData_kfin {a d : ℕ} {X : Spc F E a} {W : Spc F E d} {M : Model σ X W} (hM : M.IsGood B.ψ)
    {N : Submodule ℂ (((Fin a × Fin d) ⊕ (Fin a × Fin d) → AF F) → ℂ)}
    (h : ∀ g₁ ∈ SB _, ∀ g₂ ∈ SB _, ∀ f₁ ∈ M.Pol B.ψ B.emb, ∀ f₂ ∈ M.Pol B.ψ B.emb,
      boxFun (pureA F f₁ g₁) (star (pureA F f₂ g₂)) ∈ N) {Φ₁ Φ₂} (h1 : Φ₁ ∈ PolData B M) (h2 : Φ₂ ∈ PolData B M) :
    boxFun Φ₁ (star Φ₂) ∈ N := by
  induction h1 using Submodule.span_induction with
  | mem Φ₁ m1 =>
    obtain ⟨f, hf, φ, a1, a2, rfl⟩ := m1
    induction h2 using Submodule.span_induction with
    | mem Φ₂ m2 =>
      obtain ⟨f', hf', φ', b1, b2, rfl⟩ := m2
      exact h _ (pf_mem ⟨a1, (a2.and hM.std).mono fun v hv => hv.1.trans hv.2⟩) _
        (pf_mem ⟨b1, (b2.and hM.std).mono fun v hv => hv.1.trans hv.2⟩) f hf f' hf'
    | zero => convert N.zero_mem; funext z; simp [boxFun]
    | add _ _ _ _ i j => convert N.add_mem i j; funext z; simp [boxFun, mul_add]
    | smul c _ _ i => convert N.smul_mem (star c) i; funext z; simp [boxFun, mul_left_comm]
  | zero => convert N.zero_mem; funext z; simp [boxFun]
  | add _ _ _ _ i j => convert N.add_mem i j; funext z; simp [boxFun, add_mul]
  | smul c _ _ i => convert N.smul_mem c i; funext z; simp [boxFun, mul_assoc]

theorem _root_.GlobalTheory.ThK.Dbl.boxSec_of (hL : FinLevel) (hC : Stab2Cpt) : BoxSec := by
  intro F E _ _ _ _ _ σ B m n A Y M r s r' s' hB _ _ _ _ hY hM χ _ _ dd om S l hd h K a hK _ Φ₁ h1 Φ₂ h2
  refine isSec_of h (polData_kfin hM (fun g₁ s1 g₂ s2 f₁ p1 f₂ p2 => box_kfin hL hB hK (hC F E σ B n Y r' s' hB (.inr hY) K hK)
    h.weil.2.1.toIsSplitting hd (fun N n1 n2 => (sInf_le (a := N) ⟨fun f ⟨ε, hε⟩ => n1 ε f fun u u' hu hu' e => ?_,
      fun u hu f hf f₁ e => ?_⟩ : M.Pol B.ψ B.emb ≤ N)) s1 s2 p1 p2) h1 h2)
  · exact hε u u' hu hu' e _ _ (actsD_dop M hB.std hu f) (actsD_dop M hB.std hu' f)
  · rw [actsD_unique' M hB.std hu e]; exact n2 u hu f hf

theorem _root_.GlobalTheory.ThK.Dbl.boxSecX_of (hL : FinLevel) (hC : Stab2Cpt) : BoxSecX := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB _ _ hX _ _ hM χ _ _ dd om S l ⟨d', ht, hd⟩ h K a hK _ Φ₁ h1 Φ₂ h2
  have tr : ∀ {p q : ℕ} {u : Matrix (Fin p) (Fin q) (AE F E)}, At (evI F) u → At (evI F) uᵀ := fun hu c hc => by
    rw [← Matrix.transpose_smul, hu c hc, Matrix.transpose_zero]
  refine isSec_of h (polData_kfin hM (fun g₁ s1 g₂ s2 f₁ p1 f₂ p2 => box_kfin hL hB hK (hC F E σ B n X r s hB (.inl hX) K hK)
    h.weil.2.1.toIsSplitting hd (fun N n1 n2 => (sInf_le (a := N) ⟨fun f ⟨ε, hε⟩ => n1 ε f fun u u' hu hu' e => ?_,
      fun u hu f hf f₁ e => ?_⟩ : M.Pol B.ψ B.emb ≤ N)) s1 s2 p1 p2) h1 h2)
  · rw [← u.transpose_transpose, ← u'.transpose_transpose, ht, ht]
    refine hε uᵀ u'ᵀ (tr hu) (tr hu') (fun w => ?_) _ _ (actsD_dop M hB.std (tr hu) f) (actsD_dop M hB.std (tr hu') f)
    rw [Matrix.transpose_map, Matrix.transpose_map, e w, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  · rw [actsD_unique' M hB.std hu e]
    have := n2 uᵀ (tr hu) f hf
    rwa [ht] at this

end GlobalTheory.ThK.Dbl.Box

end
end
