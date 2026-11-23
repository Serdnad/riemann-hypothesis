module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TotallySplit
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle398
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle412
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle409
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegreeSubmod

theorem exists_leftInv {K ι κ : Type} [Field K] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι κ K) (h : LinearIndependent K Mᵀ) : ∃ Y : Matrix κ ι K, Y * M = 1 := by
  have hinj : Function.Injective M.mulVecLin := by
    have : Function.Injective M.mulVec := Matrix.mulVec_injective_iff.2 h
    exact this
  obtain ⟨g, hg⟩ := M.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h2 : LinearMap.toMatrix' (g ∘ₗ M.mulVecLin) = LinearMap.toMatrix' g * M := by
    rw [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  rw [← h2, hg]
  simp

theorem map_fromCols {R S ι κ κ' : Type} (f : R → S) (P : Matrix ι κ R) (Q : Matrix ι κ' R) :
    (fromCols P Q).map f = fromCols (P.map f) (Q.map f) := by
  ext i (j | j) <;> rfl

theorem log_ineq {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (N : Fam K ι) (hN : IsWedge N) (hS : WedgeSub)
    {κ₀ κ₁ κ₂ : Type} [Fintype κ₀] [DecidableEq κ₀] [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂]
    (B : Matrix ι κ₀ K) (A : Matrix ι κ₁ K) (C : Matrix ι κ₂ K)
    (h0 : N (κ₀ ⊕ (κ₁ ⊕ κ₂)) (fromCols B (fromCols A C)) ≠ 0) (h1 : N κ₀ B ≠ 0)
    (h2 : N (κ₀ ⊕ κ₁) (fromCols B A) ≠ 0) (h3 : N (κ₀ ⊕ κ₂) (fromCols B C) ≠ 0) :
    Real.log (N (κ₀ ⊕ (κ₁ ⊕ κ₂)) (fromCols B (fromCols A C))) + Real.log (N κ₀ B) ≤
      Real.log (N (κ₀ ⊕ κ₁) (fromCols B A)) + Real.log (N (κ₀ ⊕ κ₂) (fromCols B C)) := by
  have p0 := lt_of_le_of_ne (hN.nonneg _ (fromCols B (fromCols A C))) h0.symm
  have p1 := lt_of_le_of_ne (hN.nonneg _ B) h1.symm
  rw [← Real.log_mul h0 h1, ← Real.log_mul h2 h3]
  exact Real.log_le_log (mul_pos p0 p1) (hS K ι N hN _ _ _ B A C)

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem frame_leftInv {κ : Type} [Fintype κ] [DecidableEq κ] (x : GA E n) (M : Matrix (Fin n) κ E)
    (h : LinearIndependent E Mᵀ) :
    ∃ Y : Matrix κ (Fin n) (Ad E), Y * ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))) = 1 := by
  obtain ⟨Y, hY⟩ := exists_leftInv M h
  refine ⟨Y.map (algebraMap E (Ad E)) * x.val, ?_⟩
  have hx : x.val * (x⁻¹ : GA E n).val = 1 := Units.mul_inv x
  have hm : Y.map (algebraMap E (Ad E)) * M.map (algebraMap E (Ad E)) = 1 := by
    rw [← Matrix.map_mul, hY, Matrix.map_one _ (map_zero _) (map_one _)]
  calc Y.map (algebraMap E (Ad E)) * x.val * ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)))
      = Y.map (algebraMap E (Ad E)) * (x.val * (x⁻¹ : GA E n).val) * M.map (algebraMap E (Ad E)) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hx, Matrix.mul_one, hm]

theorem frame_fromCols {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : GA E n) (P : Matrix (Fin n) κ E)
    (Q : Matrix (Fin n) κ' E) :
    (x⁻¹ : GA E n).val * (fromCols P Q).map (algebraMap E (Ad E)) =
      fromCols ((x⁻¹ : GA E n).val * P.map (algebraMap E (Ad E))) ((x⁻¹ : GA E n).val * Q.map (algebraMap E (Ad E))) := by
  rw [map_fromCols, Matrix.mul_fromCols]

theorem sum_ineq (hF : WedgeF) (hI : WedgeI) (hS : WedgeSub) (hFS : FinSupp)
    {κ₀ κ₁ κ₂ : Type} [Fintype κ₀] [DecidableEq κ₀] [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂]
    (P : Matrix (Fin n) κ₀ (Ad E)) (Q : Matrix (Fin n) κ₁ (Ad E)) (R : Matrix (Fin n) κ₂ (Ad E))
    {Y₀ : Matrix (κ₀ ⊕ (κ₁ ⊕ κ₂)) (Fin n) (Ad E)} (h₀ : Y₀ * fromCols P (fromCols Q R) = 1)
    {Y₁ : Matrix κ₀ (Fin n) (Ad E)} (h₁ : Y₁ * P = 1)
    {Y₂ : Matrix (κ₀ ⊕ κ₁) (Fin n) (Ad E)} (h₂ : Y₂ * fromCols P Q = 1)
    {Y₃ : Matrix (κ₀ ⊕ κ₂) (Fin n) (Ad E)} (h₃ : Y₃ * fromCols P R = 1) :
    (∑ v, Real.log (nI ((fromCols P (fromCols Q R)).map (cV v))) +
        ∑ᶠ w, Real.log (nF ((fromCols P (fromCols Q R)).map (cW w)))) +
      (∑ v, Real.log (nI (P.map (cV v))) + ∑ᶠ w, Real.log (nF (P.map (cW w)))) ≤
    (∑ v, Real.log (nI ((fromCols P Q).map (cV v))) + ∑ᶠ w, Real.log (nF ((fromCols P Q).map (cW w)))) +
      (∑ v, Real.log (nI ((fromCols P R).map (cV v))) + ∑ᶠ w, Real.log (nF ((fromCols P R).map (cW w)))) := by
  obtain ⟨i₀, f₀, s₀⟩ := hFS E _ _ _ Y₀ h₀
  obtain ⟨i₁, f₁, s₁⟩ := hFS E _ _ _ Y₁ h₁
  obtain ⟨i₂, f₂, s₂⟩ := hFS E _ _ _ Y₂ h₂
  obtain ⟨i₃, f₃, s₃⟩ := hFS E _ _ _ Y₃ h₃
  have fin : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (T : Matrix (Fin n) κ (Ad E)),
      {w | nF (T.map (cW w)) ≠ 1}.Finite →
      (Function.support fun w => Real.log (nF (T.map (cW w)))).Finite := by
    intro κ _ _ T hT
    refine hT.subset fun w hw h1 => hw ?_
    simp only [Function.mem_support] at hw
    exact absurd (by rw [h1, Real.log_one]) hw
  have inf : ∑ v, Real.log (nI ((fromCols P (fromCols Q R)).map (cV v))) + ∑ v, Real.log (nI (P.map (cV v))) ≤
      ∑ v, Real.log (nI ((fromCols P Q).map (cV v))) + ∑ v, Real.log (nI ((fromCols P R).map (cV v))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun v _ => ?_
    have a₀ := i₀ v
    have a₂ := i₂ v
    have a₃ := i₃ v
    rw [map_fromCols] at a₂ a₃
    rw [map_fromCols, map_fromCols] at a₀
    rw [map_fromCols, map_fromCols, map_fromCols, map_fromCols]
    exact log_ineq (fun _ _ _ A => nI A) (hI _) hS _ _ _ a₀ (i₁ v) a₂ a₃
  have finp : ∑ᶠ w, Real.log (nF ((fromCols P (fromCols Q R)).map (cW w))) + ∑ᶠ w, Real.log (nF (P.map (cW w))) ≤
      ∑ᶠ w, Real.log (nF ((fromCols P Q).map (cW w))) + ∑ᶠ w, Real.log (nF ((fromCols P R).map (cW w))) := by
    rw [← finsum_add_distrib (fin _ s₀) (fin _ s₁), ← finsum_add_distrib (fin _ s₂) (fin _ s₃)]
    refine finsum_le_finsum' ((fin _ s₀).union (fin _ s₁) |>.subset (Function.support_add _ _))
      ((fin _ s₂).union (fin _ s₃) |>.subset (Function.support_add _ _)) fun w => ?_
    have a₀ := f₀ w
    have a₂ := f₂ w
    have a₃ := f₃ w
    rw [map_fromCols] at a₂ a₃
    rw [map_fromCols, map_fromCols] at a₀
    simp only [Pi.add_apply]
    rw [map_fromCols, map_fromCols, map_fromCols, map_fromCols]
    exact log_ineq (fun _ _ _ A => nF A) (hF _ _) hS _ _ _ a₀ (f₁ w) a₂ a₃
  linarith

theorem degG_ineq (hF : WedgeF) (hI : WedgeI) (hS : WedgeSub) (hFS : FinSupp) (x : GA E n)
    {κ₀ κ₁ κ₂ : Type} [Fintype κ₀] [DecidableEq κ₀] [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂]
    (B : Matrix (Fin n) κ₀ E) (A : Matrix (Fin n) κ₁ E) (C : Matrix (Fin n) κ₂ E)
    (l₀ : LinearIndependent E (fromCols B (fromCols A C))ᵀ) (l₁ : LinearIndependent E Bᵀ)
    (l₂ : LinearIndependent E (fromCols B A)ᵀ) (l₃ : LinearIndependent E (fromCols B C)ᵀ) :
    degG x (fromCols B A) + degG x (fromCols B C) ≤ degG x B + degG x (fromCols B (fromCols A C)) := by
  obtain ⟨Y₀, h₀⟩ := frame_leftInv x _ l₀
  obtain ⟨Y₁, h₁⟩ := frame_leftInv x _ l₁
  obtain ⟨Y₂, h₂⟩ := frame_leftInv x _ l₂
  obtain ⟨Y₃, h₃⟩ := frame_leftInv x _ l₃
  rw [frame_fromCols, frame_fromCols] at h₀
  rw [frame_fromCols] at h₂ h₃
  have key := sum_ineq hF hI hS hFS _ _ _ h₀ h₁ h₂ h₃
  simp only [degG, frame_fromCols]
  linarith

theorem degSubmod_of (hF : WedgeF) (hI : WedgeI) (hS : WedgeSub) (hFS : FinSupp) (hB : DegBasisG) (hT : TwoBases) :
    DegSubmod := by
  intro E _ _ _ n x W W'
  obtain ⟨a, b, c, B, A, C, l₀, e₁, e₂, e₃, e₄⟩ := hT E n W W'
  have l₂ : LinearIndependent E (fromCols B A)ᵀ := by
    have : (fromCols B A)ᵀ = (fromCols B (fromCols A C))ᵀ ∘ Sum.map id Sum.inl := by
      funext j; rcases j with j | j <;> rfl
    rw [this]
    exact l₀.comp _ (Sum.map_injective.2 ⟨Function.injective_id, Sum.inl_injective⟩)
  have l₃ : LinearIndependent E (fromCols B C)ᵀ := by
    have : (fromCols B C)ᵀ = (fromCols B (fromCols A C))ᵀ ∘ Sum.map id Sum.inr := by
      funext j; rcases j with j | j <;> rfl
    rw [this]
    exact l₀.comp _ (Sum.map_injective.2 ⟨Function.injective_id, Sum.inr_injective⟩)
  have l₁ : LinearIndependent E Bᵀ := by
    have : Bᵀ = (fromCols B (fromCols A C))ᵀ ∘ Sum.inl := by
      funext j; rfl
    rw [this]
    exact l₀.comp _ Sum.inl_injective
  have d₀ := hB E n _ x _ l₀
  have d₁ := hB E n _ x _ l₁
  have d₂ := hB E n _ x _ l₂
  have d₃ := hB E n _ x _ l₃
  rw [e₄] at d₀
  rw [e₁] at d₁
  rw [e₂] at d₂
  rw [e₃] at d₃
  rw [← d₀, ← d₁, ← d₂, ← d₃]
  exact degG_ineq hF hI hS hFS x B A C l₀ l₁ l₂ l₃

end GlobalTheory.CompanionTheory.DegreeSubmod

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.Degree

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem basisMat_transpose_eq (W : Submodule E (Fin n → E)) :
    ((basisMat W)ᵀ : Fin (Module.finrank E W) → Fin n → E) =
      W.subtype ∘ (Module.finBasis E W) := by
  funext j i
  rfl

theorem basisMat_linearIndependent (W : Submodule E (Fin n → E)) :
    LinearIndependent E (basisMat W)ᵀ := by
  rw [basisMat_transpose_eq]
  exact (Module.finBasis E W).linearIndependent.map' W.subtype W.ker_subtype

theorem span_basisMat (W : Submodule E (Fin n → E)) :
    Submodule.span E (Set.range (basisMat W)ᵀ) = W := by
  rw [basisMat_transpose_eq, Set.range_comp, ← Submodule.map_span, (Module.finBasis E W).span_eq,
    Submodule.map_top, Submodule.range_subtype]

theorem mul_transpose_apply {κ : Type} [Fintype κ] (g : GL (Fin n) E) (M : Matrix (Fin n) κ E) (j : κ) :
    (g.val * M)ᵀ j = Matrix.toLin' g.val (Mᵀ j) := by
  funext i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem ker_toLin'_eq_bot (g : GL (Fin n) E) : LinearMap.ker (Matrix.toLin' g.val) = ⊥ := by
  refine LinearMap.ker_eq_bot.2 fun a b hab => ?_
  have h := congrArg (Matrix.toLin' (g⁻¹ : GL (Fin n) E).val) hab
  simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using h

theorem frame_rat {κ : Type} [Fintype κ] (x : GA E n) (g : GL (Fin n) E) (M : Matrix (Fin n) κ E) :
    ((ratGL E n g * x)⁻¹ : GA E n).val * (g.val * M).map (algebraMap E (Ad E)) =
      (x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)) := by
  have hr : (g.val * M).map (algebraMap E (Ad E)) =
      (ratGL E n g).val * M.map (algebraMap E (Ad E)) := by
    rw [Matrix.map_mul]
    rfl
  rw [hr, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (ratGL E n g)⁻¹.val,
    Units.inv_mul, Matrix.one_mul]

theorem degG_rat {κ : Type} [Fintype κ] [DecidableEq κ] (x : GA E n) (g : GL (Fin n) E)
    (M : Matrix (Fin n) κ E) : degG (ratGL E n g * x) (g.val * M) = degG x M := by
  simp only [degG, frame_rat]

theorem degRat_of_degBasisG : DegBasisG → DegRat := by
  intro h E _ _ _ n x g W
  have hli : LinearIndependent E (g.val * basisMat W)ᵀ := by
    have e : (fun j => (g.val * basisMat W)ᵀ j) = Matrix.toLin' g.val ∘ fun j => (basisMat W)ᵀ j :=
      funext (mul_transpose_apply g (basisMat W))
    have l : LinearIndependent E (fun j => (g.val * basisMat W)ᵀ j) :=
      e ▸ (basisMat_linearIndependent W).map' _ (ker_toLin'_eq_bot g)
    exact l
  have hspan : Submodule.span E (Set.range (g.val * basisMat W)ᵀ) = img g W := by
    have e : Set.range (g.val * basisMat W)ᵀ = Matrix.toLin' g.val '' Set.range (basisMat W)ᵀ :=
      Set.ext fun y => ⟨fun ⟨j, hj⟩ => ⟨(basisMat W)ᵀ j, ⟨j, rfl⟩,
          (mul_transpose_apply g (basisMat W) j).symm.trans hj⟩,
        fun ⟨_, ⟨j, hj⟩, hy⟩ => ⟨j, (mul_transpose_apply g (basisMat W) j).trans (hj ▸ hy)⟩⟩
    rw [e, ← Submodule.map_span, span_basisMat]
    rfl
  have key := h E n (Fin (Module.finrank E W)) (ratGL E n g * x) (g.val * basisMat W) hli
  rw [hspan] at key
  rw [← key, degG_rat]
  rfl

end GlobalTheory.CompanionTheory.Degree

end
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem isOpen_iwU {σ : L →+* L} {n : ℕ} (hσv : ∀ x, Valued.v (σ x) = Valued.v x) :
    IsOpen (IwU σ n : Set (GU σ n)) := by
  have hc : ∀ i j : Fin n, Continuous fun g : GU σ n =>
      ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j := fun i j =>
    (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j
  have hle : IsOpen {x : L | Valued.v x ≤ 1} := by
    convert Valued.isOpen_integer (Γ₀ := WithZero (Multiplicative ℤ)) L using 1
    ext x
    exact (Valuation.mem_integer_iff (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) x).symm
  have hlt : IsOpen {x : L | Valued.v x < 1} := by
    convert Valued.isOpen_ball L 1 using 2 with x
    simp only [Valuation.restrict_lt_one_iff]
  have hset : (IwU σ n : Set (GU σ n)) =
      ⋂ i : Fin n, ⋂ j : Fin n,
        ({g : GU σ n | Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1} ∩
         {g : GU σ n | j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1}) := by
    ext g
    simp only [SetLike.mem_coe, mem_iwU_iff hσv g, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩ i j
      exact ⟨h1 i j, h2 i j⟩
    · intro h
      exact ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  refine (hle.preimage (hc i j)).inter ?_
  by_cases hij : j < i
  · have e : {g : GU σ n | j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1} =
        (fun g : GU σ n => ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ⁻¹'
          {x : L | Valued.v x < 1} := by
      ext g
      simp [hij]
    rw [e]
    exact hlt.preimage (hc i j)
  · have e : {g : GU σ n | j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1} =
        Set.univ := by
      ext g
      simp [hij]
    rw [e]
    exact isOpen_univ

theorem isOpen_map_conj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Subgroup G} (hH : IsOpen (H : Set G)) (t : G) :
    IsOpen ((H.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  have e : ⇑(MulAut.conj t).toMonoidHom = fun x => t * x * t⁻¹ := by
    funext x
    simp [MulAut.conj_apply]
  rw [e]
  have h1 : IsOpenMap fun x : G => t * x * t⁻¹ :=
    (isOpenMap_mul_right t⁻¹).comp (isOpenMap_mul_left t)
  exact h1 _ hH

theorem finite_index_iwU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q →
      Finite (KU σ n ⧸ (IwU σ n).subgroupOf (KU σ n)) ∧
      ∀ t : GU σ n, Finite (IwU σ n ⧸
        (IwU σ n ⊓ (IwU σ n).map (MulAut.conj t).toMonoidHom).subgroupOf (IwU σ n)) := by
  intro L _ _ _ ϖ σ q n h
  obtain ⟨-, hKc, hle, -⟩ := GlobalTheory.CompanionTheory.KUFactsU.kuFacts L ϖ σ q n h
  have hIo : IsOpen (IwU σ n : Set (GU σ n)) := isOpen_iwU h.2.1
  haveI : CompactSpace (KU σ n) := isCompact_iff_compactSpace.mp hKc
  refine ⟨Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen _ _ hIo), fun t => ?_⟩
  have hIc : IsCompact (IwU σ n : Set (GU σ n)) :=
    hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hIo) fun x hx => hle hx
  haveI : CompactSpace (IwU σ n) := isCompact_iff_compactSpace.mp hIc
  have hOpen : IsOpen ((IwU σ n ⊓ (IwU σ n).map (MulAut.conj t).toMonoidHom : Subgroup (GU σ n)) :
      Set (GU σ n)) := by
    rw [Subgroup.coe_inf]
    exact hIo.inter (isOpen_map_conj hIo t)
  exact Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen _ _ hOpen)

end GlobalTheory.CompanionTheory.SatPow

end
end

section

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.FrobRec

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def coeffMap (ρ : Representation ℂ G V) (lam : Module.Dual ℂ V) : V →ₗ[ℂ] (G → ℂ) where
  toFun v g := lam (ρ g v)
  map_add' v w := by
    funext g
    simp
  map_smul' c v := by
    funext g
    simp

theorem coeffMap_apply (ρ : Representation ℂ G V) (lam : Module.Dual ℂ V) (v : V) (g : G) :
    coeffMap ρ lam v g = lam (ρ g v) := rfl

theorem coeffMap_equivariant (ρ : Representation ℂ G V) (lam : Module.Dual ℂ V) (g : G) (v : V) :
    coeffMap ρ lam (ρ g v) = rightReg ℂ G ℂ g (coeffMap ρ lam v) := by
  funext x
  change lam (ρ x (ρ g v)) = lam (ρ (x * g) v)
  rw [map_mul, Module.End.mul_apply]

theorem coeffMap_injective {ρ : Representation ℂ G V} (hρ : ρ.IsIrreducible) {lam : Module.Dual ℂ V}
    (hlam : lam ≠ 0) : Function.Injective (coeffMap ρ lam) := by
  let S : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker (coeffMap ρ lam)
      apply_mem_toSubmodule := by
        intro g v hv
        rw [LinearMap.mem_ker] at hv ⊢
        rw [coeffMap_equivariant, hv, map_zero] }
  rcases hρ.eq_bot_or_eq_top S with h | h
  · have h1 : LinearMap.ker (coeffMap ρ lam) = ⊥ := congrArg Subrepresentation.toSubmodule h
    exact LinearMap.ker_eq_bot.1 h1
  · exfalso
    have h1 : LinearMap.ker (coeffMap ρ lam) = ⊤ := congrArg Subrepresentation.toSubmodule h
    refine hlam (LinearMap.ext fun v => ?_)
    have h2 : v ∈ LinearMap.ker (coeffMap ρ lam) := h1 ▸ Submodule.mem_top
    have h3 := congrFun (LinearMap.mem_ker.1 h2) 1
    simpa [coeffMap_apply] using h3

end Abstract

section U

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem chiDeltaU_mul_uni {m : ℕ} (q : ℕ) (α : Fin m → ℂ) {t u : GU σ n}
    (ht : IsDiagM (t : GL (Fin n) L)) (hu : IsUniM (u : GL (Fin n) L)) :
    chiDeltaU q α (t * u) = chiDeltaU q α t := by
  have h : ∀ i : Fin n, (((t * u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
    intro i
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single i]
    · rw [hu.2 i, mul_one]
    · intro j _ hj
      rw [ht i j (Ne.symm hj), zero_mul]
    · simp
  unfold chiDeltaU
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [h]
  · rfl

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem form_uni {ρ : Representation ℂ (GU σ n) V} {lam : Module.Dual ℂ V}
    (hJ : ∀ x ∈ jacU ρ, lam x = 0) {u : GU σ n} (hu : IsUniM (u : GL (Fin n) L)) (w : V) :
    lam (ρ u w) = lam w := by
  have h : ρ u w - w ∈ jacU ρ := Submodule.subset_span ⟨u, hu, w, rfl⟩
  have h0 := hJ _ h
  rwa [map_sub, sub_eq_zero] at h0

theorem coeffMap_mem (hsplit : BorelSplitU) (hσ : ∀ x, σ (σ x) = x) {q : ℕ} {β : Fin (n / 2) → ℂˣ}
    {ρ : Representation ℂ (GU σ n) V} {lam : Module.Dual ℂ V} (hJ : ∀ x ∈ jacU ρ, lam x = 0)
    (hT : ∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ∀ v,
      lam (ρ t v) = chiDeltaU q (fun i => (β i : ℂ)) t * lam v) (v : V) :
    coeffMap ρ lam v ∈ psSpaceU σ q β := by
  intro b g hb
  obtain ⟨t, u, ht, hu, rfl⟩ := hsplit L σ n hσ b hb
  rw [chiDeltaU_mul_uni q _ ht hu, coeffMap_apply, coeffMap_apply, map_mul, map_mul,
    Module.End.mul_apply, Module.End.mul_apply, hT t ht, form_uni hJ hu]

end U

theorem frobU_of_split (hsplit : BorelSplitU) : FrobU := by
  intro L _ _ _ ϖ σ q n V _ _ ρ α hU _ hIrr hSat β lam hJ hlam hT
  have hmem := coeffMap_mem hsplit hU.1 hJ hT
  have hinj := coeffMap_injective hIrr hlam
  have heq := coeffMap_equivariant ρ lam
  refine ⟨?_, (coeffMap ρ lam).codRestrict (psSpaceU σ q β) hmem, ?_, fun g v => ?_⟩
  · obtain ⟨v₀, hv₀⟩ := hSat.exists_vec
    have h0 : coeffMap ρ lam v₀ ≠ 0 := fun h => hv₀.1 (hinj (h.trans (map_zero _).symm))
    have hα : IsSatVecU ϖ q (rightReg ℂ _ ℂ) (coeffMap ρ lam v₀) α := hv₀.map hU _ heq h0
    have hsph : IsSphericalU q (fun i => (β i : ℂ)) (coeffMap ρ lam v₀) := by
      intro b g k hb hk
      have h1 : coeffMap ρ lam v₀ (b * g * k) = coeffMap ρ lam v₀ (b * g) := by
        rw [coeffMap_apply, coeffMap_apply, map_mul (ρ) (b * g) k, Module.End.mul_apply,
          GlobalTheory.LGrp.mem_fixed.1 hv₀.2.1 k hk]
      rw [h1]
      exact hmem v₀ b g hb
    exact hα.unique hU (isSatVecU_of_isSphericalU hU hsph h0)
  · intro a b hab
    exact hinj (congrArg Subtype.val hab)
  · exact Subtype.ext (heq g v)

theorem frobU : FrobU := frobU_of_split GlobalTheory.T.unitary_borel_splitting

end GlobalTheory.CompanionTheory.FrobRec

end
end
