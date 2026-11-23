module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift

namespace GlobalTheory.KStableSums

def pureL {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    SInf F κ →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' a f := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem exists_sum_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W)
    (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) {Ψ : (Fin n × Fin d → AF F) → ℂ}
    (hΨ : Ψ ∈ GlobalTheory.SquareAgree.algD M ψ emb) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb) ∧ (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) ∧
      Ψ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) := by
  obtain ⟨m, a, g, hg⟩ := Submodule.mem_span_set'.1 hΨ
  choose f φ hf hSB hev he using fun i => (g i).2
  refine ⟨m, fun i => a i • f i, φ, fun i => (M.Pol ψ emb).smul_mem _ (hf i), fun i => ⟨hSB i, hev i⟩, ?_⟩
  rw [← hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [he i]
  exact ((pureL (φ i)).map_smul (a i) (f i)).symm

def piEnd {V : Type} [AddCommGroup V] [Module ℂ V] (m : ℕ) (L : Module.End ℂ V) : Module.End ℂ (Fin m → V) :=
  LinearMap.pi fun i => L ∘ₗ LinearMap.proj i

theorem piEnd_apply {V : Type} [AddCommGroup V] [Module ℂ V] (m : ℕ) (L : Module.End ℂ V) (y : Fin m → V)
    (i : Fin m) : piEnd m L y i = L (y i) := rfl

theorem piEnd_pow_apply {V : Type} [AddCommGroup V] [Module ℂ V] (m : ℕ) (L : Module.End ℂ V) (k : ℕ)
    (y : Fin m → V) (i : Fin m) : (piEnd m L ^ k) y i = (L ^ k) (y i) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, piEnd_apply, ih, pow_succ', Module.End.mul_apply]

theorem isExp_piEnd {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (h : IsExp L U) (m : ℕ) :
    IsExp (piEnd m L) (piEnd m U) := by
  intro y l
  have hl : ∀ z : Fin m → V, l z = ∑ i, (l ∘ₗ LinearMap.single ℂ (fun _ : Fin m => V) i) (z i) := by
    intro z
    conv_lhs => rw [← Finset.univ_sum_single z]

    simp [map_sum]
  have key : (fun k : ℕ => ((k.factorial : ℂ))⁻¹ * l ((piEnd m L ^ k) y)) =
      fun k => ∑ i, ((k.factorial : ℂ))⁻¹ * (l ∘ₗ LinearMap.single ℂ (fun _ : Fin m => V) i) ((L ^ k) (y i)) := by
    funext k
    rw [hl, Finset.mul_sum]
    simp only [piEnd_pow_apply]
  rw [key, hl]
  exact hasSum_sum fun i _ => h (y i) _

theorem exp_conj_rect {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
    (C : Matrix β ι ℂ) (A' : Matrix ι β ℂ) (hCA : C * A' = 1) (hAC : A' * C = 1) (Y : Matrix ι ι ℂ) :
    NormedSpace.exp (C * Y * A') = C * NormedSpace.exp Y * A' := by
  let f : Matrix ι ι ℂ →+* Matrix β β ℂ :=
    { toFun := fun X => C * X * A'
      map_one' := by simp [hCA]
      map_mul' := fun X Z => by
        calc C * (X * Z) * A' = C * X * (A' * C) * Z * A' := by rw [hAC, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc]
      map_zero' := by simp
      map_add' := fun X Z => by simp [Matrix.mul_add, Matrix.add_mul] }
  have hf : Continuous f := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  open scoped Norms.Operator in
  exact (NormedSpace.map_exp f hf Y).symm

theorem atPl_zero {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (w : ι) : atPl (V := V) w 0 = 0 := by
  unfold atPl
  exact (PiTensorProduct.mapMultilinear ℂ V V).map_update_zero (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w

theorem sumPl_single {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V] {κ : Type}
    [Fintype κ] (act : Matrix κ κ ℂ →ₗ[ℂ] Module.End ℂ V) (c : ι → ℂ) (w : ι) (Y : Matrix κ κ ℂ) :
    sumPl (V := fun _ : ι => V) (fun w' => act ((Pi.single w Y : ι → Matrix κ κ ℂ) w') +
        (c w' * ((Pi.single w Y : ι → Matrix κ κ ℂ) w').trace) • 1) =
      atPl (V := fun _ : ι => V) w (act Y + (c w * Y.trace) • 1) := by
  unfold sumPl
  rw [Finset.sum_eq_single w]
  · simp
  · intro w' _ hw'
    simp only [Pi.single_eq_of_ne hw', map_zero, Matrix.trace_zero, mul_zero, zero_smul, add_zero]
    exact atPl_zero w'
  · intro h; exact absurd (Finset.mem_univ w) h

theorem exists_line_upq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {β : Type} [Fintype β] [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (J : Matrix β β (AE F E)) (b : ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (θ : InfinitePlace F → Matrix β β ℂ)
    (hCM : IsCMExt F E σ) (hfr : ∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) (hθ : ∀ w, θ w * C w = C w * Jm R S)
    (k : UG (cA σ) J) (hk : At (evI F) ((k.1 : Matrix β β (AE F E)) - 1))
    (hkθ : ∀ w, Commute ((k.1 : Matrix β β (AE F E)).map (piInf (τ w))) (θ w)) :
    ∃ γ ∈ RLines (σ := σ) J, ∃ Y : InfinitePlace F → Matrix (Ix R S) (Ix R S) ℂ, IsGen τ C γ Y ∧ (∀ w, Y w ∈ upq R S) ∧
      (∀ w, IsKC (Y w)) ∧ γ (Multiplicative.ofAdd 1) = k := by
  open GlobalTheory.RealLift.KLineProof in
  have hu : (k.1 : Matrix β β (AE F E))ᵀ * J * (k.1 : Matrix β β (AE F E)).map (cA σ) = J := k.2
  have hloc : ∀ w, ∃ Y : Matrix (Ix R S) (Ix R S) ℂ, Y ∈ upq R S ∧ IsKC Y ∧
      C w * NormedSpace.exp Y = (k.1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w := by
    intro w
    obtain ⟨A', hCA, hAC⟩ := GlobalTheory.RealLift.KLineProof.frame_inv (hfr w)
    refine GlobalTheory.RealLift.KLineProof.exists_gen_at (C w) A' hCA hAC (J.map (piInf (τ w))) b (hfr w).1 _ (θ w) ?_
      (hθ w) (hkθ w)
    have := congrArg (fun X => X.map (piInf (τ w))) hu
    simp only [Matrix.map_mul, GlobalTheory.RealLift.KLineProof.map_cA_map hCM, Matrix.transpose_map] at this
    exact this
  choose Y hY using hloc
  obtain ⟨γ, hγ, hgen⟩ := GlobalTheory.T.unitaryLieElements_generate_oneParamLines F E σ β R S τ J b C hCM hfr Y (fun w => (hY w).1)
  refine ⟨γ, hγ, Y, hgen, fun w => (hY w).1, fun w => (hY w).2.1, ?_⟩
  have hw : ∀ w, ((γ (Multiplicative.ofAdd 1)).1 : Matrix β β (AE F E)).map (piInf (τ w)) =
      (k.1 : Matrix β β (AE F E)).map (piInf (τ w)) := by
    intro w
    obtain ⟨A', hCA, -⟩ := GlobalTheory.RealLift.KLineProof.frame_inv (hfr w)
    have h1 := hgen 1 w
    rw [one_smul, (hY w).2.2] at h1
    calc _ = ((γ (Multiplicative.ofAdd 1)).1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w * A' := by
          rw [Matrix.mul_assoc, hCA, Matrix.mul_one]
      _ = _ := by rw [h1, Matrix.mul_assoc, hCA, Matrix.mul_one]
  have hA1 := hγ.2 (Multiplicative.ofAdd 1)
  have hmat : ((γ (Multiplicative.ofAdd 1)).1 : Matrix β β (AE F E)) = k.1 := by
    ext i j
    rw [← sub_eq_zero]
    refine GlobalTheory.RealLift.KLineProof.eq_zero_of_piInf hCM τ _ ?_ ?_
    · intro u hu0
      have e1 := congrFun (congrFun (hA1 u hu0) i) j
      have e2 := congrFun (congrFun (hk u hu0) i) j
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, smul_sub] at e1 e2 ⊢
      rw [← sub_sub_sub_cancel_right _ _ (u • (1 : Matrix β β (AE F E)) i j), e1, e2, sub_zero]
    · intro w
      have := congrFun (congrFun (hw w) i) j
      simp only [Matrix.map_apply] at this
      rw [map_sub, this, sub_self]
  exact Subtype.ext (Units.ext hmat)


end GlobalTheory.KStableSums
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree

theorem hTens_eq_trace {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type} [Fintype α]
    [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    GlobalTheory.WeilM.hTens c JA JB x y = (xᵀ * JA * y.map c * JBᵀ).trace := by
  simp only [GlobalTheory.WeilM.hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc ∑ i, ∑ k, ∑ l, x i j * JA i k * JB j l * c (y k l)
      = ∑ i, ∑ l, ∑ k, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ k, x i j * JA i k * JB j l * c (y k l) := Finset.sum_comm
    _ = ∑ l, ∑ k, ∑ i, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun i _ => ?_
        ring

theorem hTens_transpose_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] (e : α ≃ γ) (K : Matrix α α A) {G H : Matrix β β A} (x : A)
    (hGH : H * G = 1) (hG : G.map c = Gᵀ) (u u' : Matrix β γ A) :
    GlobalTheory.WeilM.hTens c Kᵀ (x • H) (uᵀ.submatrix e id * G) (u'ᵀ.submatrix e id * G) =
      -GlobalTheory.WeilM.hTens c (-G) (x • reindex e e Kᵀ) u u' := by
  have hHG : Gᵀ * Hᵀ = 1 := by rw [← Matrix.transpose_mul, hGH, Matrix.transpose_one]
  have hmap : (u'ᵀ.submatrix e id * G).map c = (u'ᵀ.submatrix e id).map c * Gᵀ := by
    rw [← hG]
    exact Matrix.map_mul (f := (c : A →+* A))
  have hM : ((u'ᵀ.submatrix e id).map c)ᵀ * K * uᵀ.submatrix e id = u'.map c * reindex e e K * uᵀ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, id,
      Matrix.reindex_apply]
    refine Fintype.sum_equiv e _ _ fun a => ?_
    congr 1
    exact Fintype.sum_equiv e _ _ fun b => by simp
  rw [hTens_eq_trace, hTens_eq_trace, hmap, Matrix.transpose_mul, Matrix.transpose_smul]
  calc (Gᵀ * (uᵀ.submatrix e id)ᵀ * Kᵀ * ((u'ᵀ.submatrix e id).map c * Gᵀ) * (x • Hᵀ)).trace
      = x * (Gᵀ * (uᵀ.submatrix e id)ᵀ * Kᵀ * (u'ᵀ.submatrix e id).map c * (Gᵀ * Hᵀ)).trace := by
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
        simp only [Matrix.mul_assoc]
    _ = x * (Gᵀ * (uᵀ.submatrix e id)ᵀ * Kᵀ * (u'ᵀ.submatrix e id).map c).trace := by
        rw [hHG, Matrix.mul_one]
    _ = x * (((u'ᵀ.submatrix e id).map c)ᵀ * K * uᵀ.submatrix e id * G).trace := by
        congr 1
        rw [← Matrix.trace_transpose]
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = x * (u'.map c * reindex e e K * uᵀ * G).trace := by rw [hM]
    _ = x * (uᵀ * G * u'.map c * reindex e e K).trace := by
        rw [Matrix.mul_assoc (u'.map c * reindex e e K), Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
    _ = -((uᵀ * -G * u'.map c * (x • reindex e e Kᵀ)ᵀ).trace) := by
        rw [Matrix.transpose_smul, Matrix.transpose_reindex, Matrix.transpose_transpose, Matrix.mul_neg,
          Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_smul, Matrix.trace_neg, Matrix.trace_smul, neg_neg,
          smul_eq_mul]

theorem exists_darboux_transpose_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
    {α β γ κ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype κ] [DecidableEq β] (e : α ≃ γ) (K : Matrix α α A)
    {G H : Matrix β β A} (x : A) (hGH : H * G = 1) (hG : G.map c = Gᵀ) {JV JB : Matrix β β A} {JW : Matrix γ γ A}
    {JA : Matrix α α A} (hV : JV = -G) (hW : JW = x • reindex e e Kᵀ) (hA : JA = Kᵀ) (hB : JB = x • H)
    (M : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c (-1) JV JW) κ) (T : Matrix β γ A ≃+ Matrix α β A)
    (hT : ∀ u, T u = uᵀ.submatrix e id * G) :
    ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c 1 JA JB) κ, ∀ u, co.e (T u) = M.e u := by
  subst hV hW hA hB
  have hsmul : ∀ (r : R) (u : Matrix β γ A), T (r • u) = r • T u := by
    intro r u
    rw [hT, hT, Matrix.transpose_smul]
    exact Matrix.smul_mul r (uᵀ.submatrix e id) G
  have h1 : ∀ v, (T.toLinearEquiv hsmul).symm (T v) = v := fun v => (T.toLinearEquiv hsmul).symm_apply_apply v
  refine ⟨{ e := (T.toLinearEquiv hsmul).symm.trans M.e, form := ?_ }, ?_⟩
  · intro w w'
    obtain ⟨u, rfl⟩ := T.surjective w
    obtain ⟨u', rfl⟩ := T.surjective w'
    simp only [LinearEquiv.trans_apply]
    rw [h1, h1, ← M.form]
    simp only [GlobalTheory.WeilM.symp]
    rw [hT, hT, hTens_transpose_mul c e K x hGH hG, one_mul, neg_one_mul]
  · intro u
    simp only [LinearEquiv.trans_apply]
    rw [h1]

theorem map_transpose_inv_mul {E A : Type} [CommRing E] [CommRing A] (f : E →+* A) {α β γ : Type} [Fintype β]
    [DecidableEq β] (e : α ≃ γ) (x : Matrix α β E) {G : Matrix β β E} (hG : IsUnit G.det) :
    (((x * G⁻¹)ᵀ.submatrix id e.symm).map f)ᵀ.submatrix e id * G.map f = x.map f := by
  have h1 : (((x * G⁻¹)ᵀ.submatrix id e.symm).map f)ᵀ.submatrix e id = (x * G⁻¹).map f := by
    ext a b
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq, Equiv.symm_apply_apply]
  rw [h1, ← Matrix.map_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul G hG, Matrix.mul_one]

private theorem symp_smul_eq_symp_one_smul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type}
    [Fintype α] [Fintype β] (ξ : A) (JA : Matrix α α A) (JB : Matrix β β A) (w w' : Matrix α β A) :
    GlobalTheory.WeilM.symp c ξ JA JB w w' = GlobalTheory.WeilM.symp c 1 JA (ξ • JB) w w' := by
  simp only [GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens, one_mul, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring



theorem exists_darboux_transport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∃ (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB)) (Fin S.rank × Fin d)),
        ξ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹) ∧
        (∀ x : Matrix (Fin X.rank) (Fin S.rank) D.host.E, ∃ y z : Fin S.rank × Fin d → D.host.F,
          co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F x) =
            (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) ∧
        ∀ (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (f : WO S X → ℂ),
          IsDatum M ψ cS Φ f ↔
            Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d) ∧ GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ = f := by
  intro D ψ θ _ ε S X A B d e Bs _ _ Vs Ws r s r' s' hJ hJW hV _ _ M hM cS hcS
  have hsgn : (sgn ε S).gram = (if ε then -1 else 1 : D.host.E) • S.gram := by
    cases ε <;> ext i j <;> simp [Formalism.BasicNotions.HSpace.gram]
  have hdet : IsUnit (sgn ε S).gram.det := isUnit_iff_ne_zero.mpr (Formalism.L2.Theta.gram_det_ne _)
  have hG0 : (sgn ε S).gram = -Vs.J := by
    rw [hsgn, hJ]
    cases ε <;> simp
  have hmapc : ∀ {m n : Type} (J : Matrix m n D.host.E),
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F J).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (J.map D.sp.cm.sig) := by
    intro m n J
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
  have hGJ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J = -GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram := by
    rw [hG0]
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  have hG : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram)ᵀ := by
    rw [hmapc, hG0]
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, hV.herm]
  have hGH : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F ((sgn ε S).gram)⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram = 1 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F) D.host.xi0 •
      reindex e e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram)ᵀ := by
    rw [hJW]
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.reindex_apply, map_mul]
  have hT : ∀ u, cS u = uᵀ.submatrix e id * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram := by
    intro u
    rw [hcS u, hsgn]
  obtain ⟨co0, hco0⟩ := exists_darboux_transpose_mul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F) D.host.xi0)
    hGH hG hGJ hW rfl rfl M.co cS hT
  obtain ⟨co, hco⟩ : ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F) D.host.xi0)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F ((sgn ε S).gram)⁻¹))
      (Fin S.rank × Fin d), (∀ u, co.e (cS u) = M.co.e u) ∧ ∀ w, co.e w = co0.e w := by
    refine ⟨⟨co0.e, fun w w' => ?_⟩, hco0, fun _ => rfl⟩
    rw [← co0.form, symp_smul_eq_symp_one_smul]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.transpose_map]
  refine ⟨Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F) D.host.xi0, ((sgn ε S).gram)⁻¹, co, ?_, ?_, ?_⟩
  · ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, map_mul]
  · intro y
    obtain ⟨a, b, hab⟩ := hM.rat ((y * ((sgn ε S).gram)⁻¹)ᵀ.submatrix id e.symm)
    refine ⟨a, b, ?_⟩
    have hu : cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F ((y * ((sgn ε S).gram)⁻¹)ᵀ.submatrix id e.symm)) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F y := by
      rw [hT]
      exact map_transpose_inv_mul _ e y hdet
    rw [← hu, hco.1]
    exact hab
  · intro Φ f
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, funext fun w => ?_⟩
      obtain ⟨u, rfl⟩ := cS.surjective w
      rw [← h2 u]
      simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, hco.1 u]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun u => ?_⟩
      rw [← h2]
      simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, hco.1 u]

end GlobalTheory.SquareAgree

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.SquareAgree.KapOnto

variable {D : D7}

theorem inv_mem (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (x : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) :
    Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom x.1 ∈
      HR (AF D.host.F) D.sp.cm.sig X.gram := by
  have hx : (x.1.1 : Matrix (Fin d) (Fin d) (AE D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J *
      (x.1.1 : Matrix (Fin d) (Fin d) (AE D)).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := x.2
  show (((x.1.1 : Matrix (Fin d) (Fin d) (AE D)).submatrix e e).map (cA D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram *
    (x.1.1 : Matrix (Fin d) (Fin d) (AE D)).submatrix e e = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram
  generalize (x.1.1 : Matrix (Fin d) (Fin d) (AE D)) = Y at hx ⊢
  rw [hJ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at hx
  have hx' := congrArg (fun y => incA D (D.host.xi0)⁻¹ • y) hx
  simp only [smul_smul, ← map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_smul] at hx'
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (reindex e e X.gramᵀ) = reindex e e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram)ᵀ := rfl
  rw [e1] at hx'
  have hs := congrArg (fun y => y.submatrix e e) hx'
  simp only [reindex_apply] at hs
  rw [← submatrix_mul_equiv _ _ _ e _, ← submatrix_mul_equiv _ _ _ e _] at hs
  simp only [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id, ← transpose_submatrix,
    ← Matrix.submatrix_map] at hs
  have ht := congrArg transpose hs
  rw [transpose_mul, transpose_mul, transpose_transpose, transpose_transpose, ← Matrix.mul_assoc] at ht
  exact ht



theorem kapX_onto : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d)
    (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)),
    ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Wd (GlobalTheory.AdelicU.evFin D.host.F v), ∃ h' ∈ GfC X, kapX X e hJ h' = h := by
  intro D X d e Wd hJ v h hh
  let h' : GA D X := ⟨Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom h.1, inv_mem X e hJ h⟩
  refine ⟨h', ?_, ?_⟩
  · set a : AF D.host.F := 1 - GlobalTheory.EmbChart.atPlace v 1 with ha
    have h0 : GlobalTheory.AdelicU.evFin D.host.F v a = 0 := by
      rw [ha, map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
    have h1 : fstA D.host.F a = 1 := by
      show (1 : Ainf D.host.F) - (0 : Ainf D.host.F) = 1
      exact sub_zero 1
    let f := Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    have hf1 : f (a ⊗ₜ[D.host.F] (1 : D.host.E)) = 1 := by
      simp only [f, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, h1]
      rfl
    have hz : ∀ i j, f ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h - 1) i j) = 0 := by
      intro i j
      have k := congrFun (congrFun (hh a h0) i) j
      rw [Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply] at k
      have k2 := congrArg f k
      rw [map_mul, map_zero, hf1, one_mul] at k2
      exact k2
    rw [GfC, MonoidHom.mem_ker]
    apply Units.ext
    ext i j
    show f (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h (e i) (e j)) = (1 : Matrix (Fin X.rank) (Fin X.rank) _) i j
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h (e i) (e j) =
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h - 1) (e i) (e j) + (1 : Matrix (Fin d) (Fin d) (AE D)) (e i) (e j) := by
      rw [Matrix.sub_apply, sub_add_cancel]
    rw [e2, map_add (f := _), hz, zero_add]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq (α := AF D.host.F ⊗[D.host.F] D.host.E), map_one,
        Matrix.one_apply_eq (α := Ainf D.host.F ⊗[D.host.F] D.host.E)]
    · rw [Matrix.one_apply_ne (α := AF D.host.F ⊗[D.host.F] D.host.E) (e.injective.ne hij), map_zero,
        Matrix.one_apply_ne (α := Ainf D.host.F ⊗[D.host.F] D.host.E) hij]
  · apply Subtype.ext
    apply Units.ext
    ext i j
    show (h.1.1 : Matrix (Fin d) (Fin d) (AE D)) (e (e.symm i)) (e (e.symm j)) = h.1.1 i j
    simp only [Equiv.apply_symm_apply]

end GlobalTheory.SquareAgree.KapOnto
end
end
