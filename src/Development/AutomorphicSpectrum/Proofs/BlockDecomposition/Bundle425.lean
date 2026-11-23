module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriUnipotentDatum
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle412
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.PosDef
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

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegMoveProof

theorem log_step {a b c : ℝ} {k n : ℕ} (hkn : k ≤ n) (ha : 0 < a) (hb : 0 < b) (h : a ≤ c ^ k * b) :
    Real.log a ≤ n * Real.posLog c + Real.log b := by
  have hp : 0 < c ^ k * b := lt_of_lt_of_le ha h
  have hck : c ^ k ≠ 0 := fun h0 => by simp [h0] at hp
  have h1 : Real.log a ≤ Real.log (c ^ k * b) := Real.log_le_log ha h
  rw [Real.log_mul hck hb.ne', Real.log_pow] at h1
  have h2 : Real.log c ≤ Real.posLog c := le_max_right 0 (Real.log c)
  have h3 : (0 : ℝ) ≤ Real.posLog c := Real.posLog_nonneg
  have h4 : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have h5 : (k : ℝ) * Real.log c ≤ n * Real.posLog c :=
    (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg k)).trans (mul_le_mul_of_nonneg_right h4 h3)
  linarith

theorem finsum_bound {α : Type} {f g s : α → ℝ} {c : ℝ} (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) (hs : (Function.support s).Finite) (h : ∀ a, f a ≤ c * s a + g a) :
    ∑ᶠ a, f a ≤ c * ∑ᶠ a, s a + ∑ᶠ a, g a := by
  classical
  let T : Finset α := hf.toFinset ∪ hg.toFinset ∪ hs.toFinset
  rw [finsum_eq_sum_of_support_subset f (s := T) (fun a ha => by simp [T, Set.mem_toFinset] at ha ⊢; tauto),
    finsum_eq_sum_of_support_subset g (s := T) (fun a ha => by simp [T, Set.mem_toFinset] at ha ⊢; tauto),
    finsum_eq_sum_of_support_subset s (s := T) (fun a ha => by simp [T, Set.mem_toFinset] at ha ⊢; tauto),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun a _ => h a

theorem sz_sq_le {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : sz g ^ 2 ≤ ⨆ p : Fin n × Fin n, ‖g p.1 p.2‖ ^ 2 := by
  rcases isEmpty_or_nonempty (Fin n × Fin n) with he | hne
  · simp [sz, Real.iSup_of_isEmpty]
  · obtain ⟨p, hp⟩ := exists_eq_ciSup_of_finite (f := fun p : Fin n × Fin n => ‖g p.1 p.2‖)
    rw [sz, ← hp]
    exact le_ciSup (f := fun p : Fin n × Fin n => ‖g p.1 p.2‖ ^ 2) (Set.finite_range _).bddAbove p

theorem nI_nonneg {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ ℂ) : 0 ≤ nI A := by
  open ComplexOrder in
  have h : 0 ≤ (Aᴴ * A).det := (Matrix.posSemidef_conjTranspose_mul_self A).det_nonneg
  exact (Complex.le_def.1 h).1

theorem nF_nonneg {K ι κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K) : 0 ≤ nF A :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem exists_left_inv {K : Type} [Field K] {n k : ℕ} (M : Matrix (Fin n) (Fin k) K)
    (h : LinearIndependent K Mᵀ) : ∃ N : Matrix (Fin k) (Fin n) K, N * M = 1 := by
  have hinj : Function.Injective M.mulVecLin := Matrix.mulVec_injective_iff.2 h
  obtain ⟨f, hf⟩ := LinearMap.exists_leftInverse_of_injective M.mulVecLin (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  have h1 : LinearMap.toMatrix' (f ∘ₗ M.mulVecLin) = 1 := by rw [hf]; exact LinearMap.toMatrix'_id
  rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at h1

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n k : ℕ}

theorem ultra (w : HeightOneSpectrum (𝓞 E)) : IsUltrametricDist (w.adicCompletion E) :=
  inferInstanceAs (@IsUltrametricDist (w.adicCompletion E)
    (Valued.toNormedField (w.adicCompletion E) (WithZero (Multiplicative ℤ))).toDist)

theorem inf_step (hI : MulI) (hkn : k ≤ n) (h : Matrix (Fin n) (Fin n) (Ad E)) (A : Matrix (Fin n) (Fin k) (Ad E))
    (v : InfinitePlace E) (h0 : nI ((h * A).map (cV v)) ≠ 0) (h1 : nI (A.map (cV v)) ≠ 0) :
    Real.log (nI ((h * A).map (cV v))) ≤
      n * (Real.posLog ((n : ℝ) * n) + Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (h p.1 p.2)‖ ^ 2)) +
        Real.log (nI (A.map (cV v))) := by
  have hm : (h * A).map (cV v) = h.map (cV v) * A.map (cV v) := Matrix.map_mul
  have hle := (hI (Fin n) (Fin n) (Fin k) (A.map (cV v))).1 (h.map (cV v))
  simp only [Fintype.card_fin] at hle
  rw [← hm] at hle
  have hs := log_step hkn (lt_of_le_of_ne (nI_nonneg _) h0.symm) (lt_of_le_of_ne (nI_nonneg _) h1.symm) hle
  refine hs.trans ?_
  have h2 : Real.posLog ((n : ℝ) * n * sz (h.map (cV v)) ^ 2) ≤
      Real.posLog ((n : ℝ) * n) + Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (h p.1 p.2)‖ ^ 2) :=
    Real.posLog_mul.trans (add_le_add le_rfl (Real.posLog_le_posLog (by nlinarith [sq_nonneg (sz (h.map (cV v)))]) (sz_sq_le _)))
  have := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) n)
  linarith

theorem fin_step (hF : MulF) (hkn : k ≤ n) (h : Matrix (Fin n) (Fin n) (Ad E)) (A : Matrix (Fin n) (Fin k) (Ad E))
    (w : HeightOneSpectrum (𝓞 E)) (h0 : nF ((h * A).map (cW w)) ≠ 0) (h1 : nF (A.map (cW w)) ≠ 0) :
    Real.log (nF ((h * A).map (cW w))) ≤
      n * Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (h p.1 p.2)‖) + Real.log (nF (A.map (cW w))) := by
  haveI := ultra w
  have hm : (h * A).map (cW w) = h.map (cW w) * A.map (cW w) := Matrix.map_mul
  have hle := (hF (w.adicCompletion E) (Fin n) (Fin n) (Fin k) (A.map (cW w))).1 (h.map (cW w))
  simp only [Fintype.card_fin] at hle
  rw [← hm] at hle
  exact log_step hkn (lt_of_le_of_ne (nF_nonneg _) h0.symm) (lt_of_le_of_ne (nF_nonneg _) h1.symm) hle

theorem logSizeM_nonneg (A : Matrix (Fin n) (Fin n) (Ad E)) : 0 ≤ logSizeM A :=
  add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg) (finsum_nonneg fun _ => Real.posLog_nonneg)

theorem frame_move (x : GA E n) (g : GL (Fin n) E) (M : Matrix (Fin n) (Fin k) E) :
    (x⁻¹ * ratGL E n g * x : GA E n).val * ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))) =
      (x⁻¹ : GA E n).val * (g.val * M).map (algebraMap E (Ad E)) := by
  have h1 : (ratGL E n g).val = g.val.map (algebraMap E (Ad E)) := rfl
  rw [Matrix.map_mul, ← h1, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem core (hF : MulF) (hI : MulI) (hSz : SzFin) (hFS : FinSupp) (hkn : k ≤ n) (h : GA E n)
    (A : Matrix (Fin n) (Fin k) (Ad E)) (Y : Matrix (Fin k) (Fin n) (Ad E)) (hY : Y * A = 1) :
    ∑ v, Real.log (nI ((h.val * A).map (cV v))) + ∑ᶠ w, Real.log (nF ((h.val * A).map (cW w))) ≤
      (∑ v, Real.log (nI (A.map (cV v))) + ∑ᶠ w, Real.log (nF (A.map (cW w)))) +
        n * ((Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n)) + n * logSizeM h.val := by
  have hY' : (Y * (h⁻¹ : GA E n).val) * (h.val * A) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (h⁻¹ : GA E n).val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, hY]
  obtain ⟨a1, a2, a3⟩ := hFS E (Fin n) (Fin k) A Y hY
  obtain ⟨b1, b2, b3⟩ := hFS E (Fin n) (Fin k) (h.val * A) _ hY'
  have hinf := Finset.sum_le_sum (s := Finset.univ) fun v (_ : v ∈ Finset.univ) =>
    inf_step (E := E) hI hkn h.val A v (b1 v) (a1 v)
  have hfin := finsum_bound (c := (n : ℝ))
    (f := fun w => Real.log (nF ((h.val * A).map (cW w))))
    (g := fun w => Real.log (nF (A.map (cW w))))
    (s := fun w => Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (h.val p.1 p.2)‖))
    (b3.subset fun w hw hne => hw ((congrArg Real.log hne).trans Real.log_one))
    (a3.subset fun w hw hne => hw ((congrArg Real.log hne).trans Real.log_one))
    ((hSz E (Fin n) (Fin n) h.val).subset fun w hw => by
      by_contra hc
      apply hw
      exact max_eq_left (Real.log_nonpos (Real.iSup_nonneg fun _ => norm_nonneg _) (not_lt.1 hc)))
    fun w => fin_step hF hkn h.val A w (b2 w) (a2 w)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hinf
  have hS : logSizeM h.val = ∑ v, Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (h.val p.1 p.2)‖ ^ 2) +
      ∑ᶠ w, Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (h.val p.1 p.2)‖) := rfl
  rw [hS]
  nlinarith [hinf, hfin]

theorem lin_basisMat (W : Submodule E (Fin n → E)) : LinearIndependent E (basisMat W)ᵀ ∧
    Submodule.span E (Set.range (basisMat W)ᵀ) = W := by
  have hM : (basisMat W)ᵀ = W.subtype ∘ (Module.finBasis E W) := by
    funext j i
    rfl
  rw [hM]
  refine ⟨(Module.finBasis E W).linearIndependent.map' W.subtype W.ker_subtype, ?_⟩
  rw [Set.range_comp, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem linearIndependent_image_span (g : GL (Fin n) E) (f : Fin k → Fin n → E) (hf : LinearIndependent E f) :
    LinearIndependent E (Matrix.toLin' g.val ∘ f) ∧
      Submodule.span E (Set.range (Matrix.toLin' g.val ∘ f)) = img g (Submodule.span E (Set.range f)) := by
  have inj : Function.Injective (Matrix.toLin' g.val) := fun a b hab => by
    have h1 := congrArg (fun y => (g⁻¹ : GL (Fin n) E).val *ᵥ y) hab
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul] using h1
  refine ⟨hf.map' _ (LinearMap.ker_eq_bot.2 inj), ?_⟩
  rw [Set.range_comp, ← Submodule.map_span]
  rfl

theorem lin_moved (g : GL (Fin n) E) (M : Matrix (Fin n) (Fin k) E) (hM : LinearIndependent E Mᵀ) :
    LinearIndependent E (g.val * M)ᵀ ∧
      Submodule.span E (Set.range (g.val * M)ᵀ) = img g (Submodule.span E (Set.range Mᵀ)) := by
  have hG : (Matrix.toLin' g.val ∘ (Mᵀ : Fin k → Fin n → E)) = ((g.val * M)ᵀ : Fin k → Fin n → E) := by
    funext j i
    change (Matrix.toLin' g.val (fun i' => M i' j)) i = (g.val * M) i j
    rw [Matrix.toLin'_apply]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have h1 := linearIndependent_image_span g Mᵀ hM
  rw [hG] at h1
  exact h1

theorem degMove_of : MulF → MulI → SzFin → FinSupp → DegBasisG → DegMove := by
  intro hF hI hSz hFS hB E _ _ _ n
  refine ⟨n * (1 + (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n)), fun x g W => ?_⟩
  obtain ⟨hLI, hspan⟩ := lin_basisMat W
  obtain ⟨hLI', hspan'⟩ := lin_moved g (basisMat W) hLI
  rw [hspan] at hspan'
  have hkn : Module.finrank E W ≤ n := by simpa using Submodule.finrank_le W
  obtain ⟨N, hN⟩ := exists_left_inv (basisMat W) hLI
  have e1 : deg x (img g W) = degG x (g.val * basisMat W) := by rw [hB E n _ x _ hLI', hspan']
  have e2 : deg x W = degG x (basisMat W) := rfl
  have hY : (N.map (algebraMap E (Ad E)) * x.val) * ((x⁻¹ : GA E n).val * (basisMat W).map (algebraMap E (Ad E))) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
      ← Matrix.map_mul, hN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc := core hF hI hSz hFS hkn (x⁻¹ * ratGL E n g * x) _ _ hY
  rw [frame_move] at hc
  rw [e1, e2]
  simp only [degG]
  have hS := logSizeM_nonneg (x⁻¹ * ratGL E n g * x : GA E n).val
  have hS' := logSizeM_nonneg ((x⁻¹ * ratGL E n g * x)⁻¹ : GA E n).val
  have hL : (0 : ℝ) ≤ (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n) :=
    mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg
  have hsz : logSize (x⁻¹ * ratGL E n g * x) = logSizeM (x⁻¹ * ratGL E n g * x : GA E n).val +
    logSizeM ((x⁻¹ * ratGL E n g * x)⁻¹ : GA E n).val := rfl
  rw [hsz]
  generalize logSizeM (x⁻¹ * ratGL E n g * x : GA E n).val = S at *
  generalize logSizeM ((x⁻¹ * ratGL E n g * x)⁻¹ : GA E n).val = S' at *
  generalize (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n) = b at *
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpos : 0 ≤ (n : ℝ) * (1 + S' + b * S + b * S') := by positivity
  nlinarith [hc, hpos]

end GlobalTheory.CompanionTheory.DegMoveProof

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegBasisGen

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem ultra (w : HeightOneSpectrum (𝓞 E)) : IsUltrametricDist (w.adicCompletion E) :=
  inferInstanceAs (@IsUltrametricDist (w.adicCompletion E)
    (Valued.toNormedField (w.adicCompletion E) (WithZero (Multiplicative ℤ))).toDist)

theorem exists_left_inv {K ι κ : Type} [Field K] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (P : Matrix ι κ K) (hP : LinearIndependent K Pᵀ) : ∃ Y : Matrix κ ι K, Y * P = 1 := by
  have inj : LinearMap.ker P.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have h0 := hv
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_eq_sum] at h0
    simp only [op_smul_eq_smul] at h0
    funext i
    exact Fintype.linearIndependent_iff.1 hP v h0 i
  obtain ⟨f, hf⟩ := P.mulVecLin.exists_leftInverse_of_injective inj
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  have h := congrArg LinearMap.toMatrix' hf
  rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin',
    LinearMap.toMatrix'_id] at h

theorem degG_reindex (hF : WedgeF) (hI : WedgeI) {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ']
    [DecidableEq κ'] (e : κ' ≃ κ) (x : GA E n) (M : Matrix (Fin n) κ E) :
    degG x (M.submatrix id e) = degG x M := by
  have hfr : (x⁻¹ : GA E n).val * (M.submatrix id e).map (algebraMap E (Ad E)) =
      ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))).submatrix id e := by
    ext i j
    simp [Matrix.mul_apply]
  obtain ⟨A, hA⟩ : ∃ A, A = (x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)) := ⟨_, rfl⟩
  have hv : ∀ v, nI ((A.submatrix id e).map (cV v)) = nI (A.map (cV v)) := fun v => by
    rw [← Matrix.submatrix_map]
    exact (hI (Fin n)).reindex κ κ' e (A.map (cV v))
  have hw : ∀ w, nF ((A.submatrix id e).map (cW w)) = nF (A.map (cW w)) := fun w => by
    haveI := ultra w
    rw [← Matrix.submatrix_map]
    exact (hF (w.adicCompletion E) (Fin n)).reindex κ κ' e (A.map (cW w))
  simp only [degG, hfr, ← hA, hv, hw]

theorem degG_mul (mF : MulF) (mI : MulI) (lg : LogAbsBasic) (fs : FinSupp) {κ : Type} [Fintype κ] [DecidableEq κ]
    (x : GA E n) (P : Matrix (Fin n) κ E) (hP : LinearIndependent E Pᵀ) (s : Matrix κ κ E) (hs : s.det ≠ 0) :
    degG x (P * s) = degG x P := by
  obtain ⟨A, hA⟩ : ∃ A, A = (x⁻¹ : GA E n).val * P.map (algebraMap E (Ad E)) := ⟨_, rfl⟩
  have hfr : (x⁻¹ : GA E n).val * (P * s).map (algebraMap E (Ad E)) = A * s.map (algebraMap E (Ad E)) := by
    rw [hA, Matrix.map_mul, Matrix.mul_assoc]
  obtain ⟨Y₀, hY₀⟩ := exists_left_inv P hP
  have hYA : (Y₀.map (algebraMap E (Ad E)) * x.val) * A = 1 := by
    rw [hA, Matrix.mul_assoc, ← Matrix.mul_assoc x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, ← Matrix.map_mul, hY₀, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨h1, h2, h3⟩ := (lg E).1, (lg E).2.1, (lg E).2.2
  obtain ⟨f1, f2, f3⟩ := fs E (Fin n) κ A _ hYA
  have hu : IsUnit (algebraMap E (Ad E) s.det) := (IsUnit.mk0 _ hs).map _
  have hdet : ∀ {R : Type} [CommRing R] (f : Ad E →+* R),
      ((s.map (algebraMap E (Ad E))).map f).det = f (algebraMap E (Ad E) s.det) := fun f => by
    rw [RingHom.map_det, RingHom.map_det]
    rfl
  have hv : ∀ v, Real.log (nI ((A * s.map (algebraMap E (Ad E))).map (cV v))) =
      Real.log (nI (A.map (cV v))) + Real.log (‖cV v (algebraMap E (Ad E) s.det)‖ ^ 2) := fun v => by
    have hne : ‖cV v (algebraMap E (Ad E) s.det)‖ ^ 2 ≠ 0 :=
      pow_ne_zero _ (norm_ne_zero_iff.2 (hu.map (cV v)).ne_zero)
    rw [Matrix.map_mul, (mI (Fin n) (Fin n) κ _).2.1, hdet, Real.log_mul (f1 v) hne]
  have hw : ∀ w, Real.log (nF ((A * s.map (algebraMap E (Ad E))).map (cW w))) =
      Real.log (nF (A.map (cW w))) + Real.log ‖cW w (algebraMap E (Ad E) s.det)‖ := fun w => by
    haveI := ultra w
    have hne : ‖cW w (algebraMap E (Ad E) s.det)‖ ≠ 0 := norm_ne_zero_iff.2 (hu.map (cW w)).ne_zero
    rw [Matrix.map_mul, (mF _ (Fin n) (Fin n) κ _).2.1, hdet, Real.log_mul (f2 w) hne]
  have hsupp : (Function.support fun w => Real.log (nF (A.map (cW w)))).Finite :=
    f3.subset fun w hw' h => hw' (by simp [h])
  have hprod := h3 s.det hs
  simp only [degG, hfr, ← hA, hv, hw]
  rw [Finset.sum_add_distrib, finsum_add_distrib hsupp (h1 _ hu)]
  unfold logAbs at hprod
  linarith

theorem degBasisG_of : WedgeF → WedgeI → MulF → MulI → LogAbsBasic → FinSupp → DegBasisG := by
  intro hF hI mF mI lg fs E _ _ _ n κ _ _ x M hM
  obtain ⟨W, hW⟩ : ∃ W, W = Submodule.span E (Set.range Mᵀ) := ⟨_, rfl⟩
  rw [← hW]
  have hcard : Module.finrank E W = Fintype.card κ := by
    rw [hW]
    exact finrank_span_eq_card hM
  have hsub : ∀ k, (fun i => M i k) ∈ W := fun k => by
    rw [hW]
    exact Submodule.subset_span ⟨k, rfl⟩
  let e : Fin (Module.finrank E W) ≃ κ := (Fintype.equivFinOfCardEq hcard.symm).symm
  have hcol : ∀ j, (fun i => M i (e j)) ∈ W := fun j => hsub (e j)
  let b := Module.finBasis E W
  let s : Matrix (Fin (Module.finrank E W)) (Fin (Module.finrank E W)) E :=
    Matrix.of fun i j => b.repr ⟨fun i' => M i' (e j), hcol j⟩ i
  have hfac : M.submatrix id e = basisMat W * s := by
    ext i j
    have h := congrArg (fun y : W => (y : Fin n → E) i) (b.sum_repr ⟨fun i' => M i' (e j), hcol j⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h
    simp only [Matrix.mul_apply, basisMat, Matrix.of_apply, Matrix.submatrix_apply, id, s]
    rw [← h]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hlin : LinearIndependent E (M.submatrix id e)ᵀ := hM.comp e e.injective
  have hs : s.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have h1 : M.submatrix id e *ᵥ v = 0 := by
      rw [hfac, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    rw [Matrix.mulVec_eq_sum] at h1
    simp only [op_smul_eq_smul] at h1
    exact hv0 (funext fun i => Fintype.linearIndependent_iff.1 hlin v h1 i)
  have hP : LinearIndependent E (basisMat W)ᵀ :=
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  calc degG x M = degG x (M.submatrix id e) := (degG_reindex hF hI e x M).symm
    _ = degG x (basisMat W * s) := by rw [hfac]
    _ = degG x (basisMat W) := degG_mul mF mI lg fs x _ hP s hs
    _ = deg x W := rfl

end GlobalTheory.CompanionTheory.DegBasisGen

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegAdelicProof

theorem exists_leftInv {K : Type} [Field K] {n k : ℕ} (M : Matrix (Fin n) (Fin k) K)
    (h : LinearIndependent K Mᵀ) : ∃ L : Matrix (Fin k) (Fin n) K, L * M = 1 := by
  have hinj : Function.Injective M.mulVec := Matrix.mulVec_injective_iff.2 h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective M.mulVecLin (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h1 : LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' M) = 1 := by
    rw [Matrix.toLin'_apply', hg, LinearMap.toMatrix'_id]
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at h1

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n k : ℕ}

theorem frame_mul (x t : GA E n) (s : GA E k) (M : Matrix (Fin n) (Fin k) E)
    (h : t.val * M.map (algebraMap E (Ad E)) = M.map (algebraMap E (Ad E)) * s.val) :
    frame (t * x) M = frame x M * (s⁻¹ : GA E k).val := by
  have h' : (t⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)) =
      M.map (algebraMap E (Ad E)) * (s⁻¹ : GA E k).val := by
    calc (t⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))
        = (t⁻¹ : GA E n).val * (M.map (algebraMap E (Ad E)) * (s.val * (s⁻¹ : GA E k).val)) := by
          rw [Units.mul_inv, Matrix.mul_one]
      _ = (t⁻¹ : GA E n).val * (t.val * M.map (algebraMap E (Ad E))) * (s⁻¹ : GA E k).val := by
          rw [h, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = M.map (algebraMap E (Ad E)) * (s⁻¹ : GA E k).val := by
          rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  unfold frame
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, h', Matrix.mul_assoc]

theorem lognInf_mul (hI : MulI) (v : InfinitePlace E) (A : Matrix (Fin n) (Fin k) (Ad E))
    (S : Matrix (Fin k) (Fin k) (Ad E)) (hA : nI (A.map (cV v)) ≠ 0) (hS : IsUnit S.det) :
    lognInf v (A * S) = lognInf v A + Real.log (‖cV v S.det‖ ^ 2) := by
  have hd : (S.map (cV v)).det = cV v S.det := (RingHom.map_det (cV v) S).symm
  have h0 : cV v S.det ≠ 0 := (hS.map (cV v)).ne_zero
  change Real.log (nI ((A * S).map (cV v))) = Real.log (nI (A.map (cV v))) + _
  rw [Matrix.map_mul, (hI (Fin n) (Fin n) (Fin k) _).2.1, hd,
    Real.log_mul hA (pow_ne_zero 2 (norm_ne_zero_iff.2 h0))]

theorem lognFin_mul (hF : MulF) (w : HeightOneSpectrum (𝓞 E)) (A : Matrix (Fin n) (Fin k) (Ad E))
    (S : Matrix (Fin k) (Fin k) (Ad E)) (hA : nF (A.map (cW w)) ≠ 0) (hS : IsUnit S.det) :
    lognFin w (A * S) = lognFin w A + Real.log ‖cW w S.det‖ := by
  have hd : (S.map (cW w)).det = cW w S.det := (RingHom.map_det (cW w) S).symm
  have h0 : cW w S.det ≠ 0 := (hS.map (cW w)).ne_zero
  change Real.log (nF ((A * S).map (cW w))) = Real.log (nF (A.map (cW w))) + _
  rw [Matrix.map_mul, (hF _ (Fin n) (Fin n) (Fin k) _).2.1, hd,
    Real.log_mul hA (norm_ne_zero_iff.2 h0)]

theorem logAbs_inv (hL : LogAbsBasic) (u u' : Ad E) (hu : IsUnit u) (hu' : IsUnit u') (h : u * u' = 1) :
    logAbs u = -logAbs u' := by
  have h1 := (hL E).2.1 u u' hu hu'
  have h2 := (hL E).2.2 1 one_ne_zero
  rw [map_one] at h2
  rw [h, h2] at h1
  linarith

theorem frame_leftInv (x : GA E n) (M : Matrix (Fin n) (Fin k) E) (L : Matrix (Fin k) (Fin n) E)
    (hLM : L * M = 1) :
    (L.map (algebraMap E (Ad E)) * x.val) * frame x M = 1 := by
  unfold frame
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc x.val, Units.mul_inv, Matrix.one_mul,
    ← Matrix.map_mul, hLM, Matrix.map_one _ (map_zero _) (map_one _)]

theorem degAdelic_of (hF : MulF) (hI : MulI) (hL : LogAbsBasic) (hS : FinSupp) : DegAdelic := by
  intro E _ _ _ n k x t s M hM h
  obtain ⟨L, hLM⟩ := exists_leftInv M hM
  obtain ⟨h1, h2, h3⟩ := hS E (Fin n) (Fin k) (frame x M) _ (frame_leftInv x M L hLM)
  have hδ : IsUnit (s⁻¹ : GA E k).val.det := Matrix.isUnits_det_units _
  have hs : IsUnit s.val.det := Matrix.isUnits_det_units _
  have hmul : (s⁻¹ : GA E k).val.det * s.val.det = 1 := by
    rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
  have hinv := logAbs_inv hL _ _ hδ hs hmul
  have hfin₁ : (Function.support fun w => lognFin w (frame x M)).Finite := by
    refine h3.subset fun w hw hw1 => hw ?_
    change Real.log (nF ((frame x M).map (cW w))) = 0
    rw [show nF ((frame x M).map (cW w)) = 1 from hw1, Real.log_one]
  have hfin₂ := (hL E).1 _ hδ
  rw [degM, degM, frame_mul x t s M h]
  have e₁ : ∀ v, lognInf v (frame x M * (s⁻¹ : GA E k).val) =
      lognInf v (frame x M) + Real.log (‖cV v (s⁻¹ : GA E k).val.det‖ ^ 2) :=
    fun v => lognInf_mul hI v _ _ (h1 v) hδ
  have e₂ : ∀ w, lognFin w (frame x M * (s⁻¹ : GA E k).val) =
      lognFin w (frame x M) + Real.log ‖cW w (s⁻¹ : GA E k).val.det‖ :=
    fun w => lognFin_mul hF w _ _ (h2 w) hδ
  simp_rw [e₁, e₂]
  rw [Finset.sum_add_distrib, finsum_add_distrib hfin₁ hfin₂]
  unfold logAbs at hinv ⊢
  linarith

end GlobalTheory.CompanionTheory.DegAdelicProof

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG PositivityTheory.SphericalProduct

theorem _root_.GlobalTheory.T.iwahori_unipotent_datum : PositivityTheory.SphericalProduct.IwahoriU := by
  first | exact @GlobalTheory.CompanionTheory.IwUnit.iwahoriU | exact GlobalTheory.CompanionTheory.IwUnit.iwahoriU | (intros; apply GlobalTheory.CompanionTheory.IwUnit.iwahoriU <;> assumption)
end

section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

theorem _root_.GlobalTheory.T.casselman_first_property : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], PositivityTheory.SphericalProduct.A1 G := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.hecke_dominant_mul_abstract | exact GlobalTheory.CompanionTheory.Casselman.hecke_dominant_mul_abstract | (intros; apply GlobalTheory.CompanionTheory.Casselman.hecke_dominant_mul_abstract <;> assumption)
end
