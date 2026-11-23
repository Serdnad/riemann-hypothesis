module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1949
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.finite_fourier_transform_surjective_integral : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ ei : SInf F κ →L[ℂ] SInf F κ, Function.Surjective ei ∧ (∀ f y, ei f y = ∫ x, f x * eInf x y ∂(measI F κ)) ∧
      ∀ (f : SInf F κ) y, Continuous (fun x => f x * eInf x y) ∧ Integrable (fun x => f x * eInf x y) (measI F κ) := by
  first | exact @GlobalTheory.WeylFour.exists_fourier_measI | exact GlobalTheory.WeylFour.exists_fourier_measI | (intros; apply GlobalTheory.WeylFour.exists_fourier_measI <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.BlockForms.Norm

section Abstract

variable {A : Type} [CommRing A] {n r d : ℕ} {X Y : Matrix (Fin n) (Fin r) A} {L K : Matrix (Fin r) (Fin n) A}
  (e : Fin d → Fin r) (P Q : Matrix (Fin d) (Fin d) A)

theorem row_span {Z : Matrix (Fin r) (Fin n) A} {I : Set (Fin r)} {a : Fin r} (hz : ∀ i ∈ I, (Z * X) a i = 0)
    {y : Fin n → A} (hy : y ∈ Submodule.span A ((fun i => Xᵀ i) '' I)) : (Z *ᵥ y) a = 0 := by
  have : Submodule.span A ((fun i => Xᵀ i) '' I) ≤ LinearMap.ker (LinearMap.proj a ∘ₗ Z.mulVecLin) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    exact hz i hi
  exact this hy

theorem blk_mulVec (y : Fin n → A) :
    (1 + X.submatrix id e * P * K.submatrix e id + Y.submatrix id e * Q * L.submatrix e id) *ᵥ y =
      y + X.submatrix id e *ᵥ (P *ᵥ fun a => (K *ᵥ y) (e a)) + Y.submatrix id e *ᵥ (Q *ᵥ fun a => (L *ᵥ y) (e a)) := by
  rw [add_mulVec, add_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  rfl

theorem blk_span (hLX : L * X = 0) (hKX : K * X = 1) {I : Set (Fin r)} (hI : (∀ a, e a ∈ I) ∨ ∀ a, e a ∉ I)
    {y : Fin n → A} (hy : y ∈ Submodule.span A ((fun i => Xᵀ i) '' I)) :
    (1 + X.submatrix id e * P * K.submatrix e id + Y.submatrix id e * Q * L.submatrix e id) *ᵥ y ∈
      Submodule.span A ((fun i => Xᵀ i) '' I) := by
  have h1 : (fun a => (L *ᵥ y) (e a)) = 0 := funext fun a => row_span (fun i _ => by rw [hLX]; rfl) hy
  rw [blk_mulVec, h1, mulVec_zero, mulVec_zero, add_zero]
  refine add_mem hy ?_
  rcases hI with hI | hI
  · rw [mulVec_eq_sum]
    refine sum_mem fun a _ => ?_
    rw [op_smul_eq_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e a, hI a, rfl⟩)
  · have h2 : (fun a => (K *ᵥ y) (e a)) = 0 := funext fun a => row_span (fun i hi => by
      rw [hKX, Matrix.one_apply_ne]; rintro rfl; exact hI a hi) hy
    rw [h2, mulVec_zero, mulVec_zero]
    exact zero_mem _

theorem blk_perp (hLX : L * X = 0) (hLY : L * Y = 1) {I : Set (Fin r)} (hI : (∀ a, e a ∈ I) ∨ ∀ a, e a ∉ I)
    {y : Fin n → A} (hy : ∀ i ∈ I, (L *ᵥ y) i = 0) : ∀ i ∈ I,
    (L *ᵥ ((1 + X.submatrix id e * P * K.submatrix e id + Y.submatrix id e * Q * L.submatrix e id) *ᵥ y)) i = 0 := by
  intro i hi
  have h1 : L * X.submatrix id e = 0 := by
    ext a b
    exact congrFun (congrFun hLX a) (e b)
  rw [blk_mulVec, mulVec_add, mulVec_add, mulVec_mulVec _ L (X.submatrix id e), h1, zero_mulVec, add_zero,
    Pi.add_apply, hy i hi, zero_add]
  rcases hI with hI | hI
  · have h2 : (fun a => (L *ᵥ y) (e a)) = 0 := funext fun a => hy _ (hI a)
    rw [h2, mulVec_zero, mulVec_zero, mulVec_zero]
    rfl
  · rw [mulVec_mulVec _ L]
    change ∑ a, (L * Y.submatrix id e) i a * _ = 0
    refine Finset.sum_eq_zero fun a _ => ?_
    have : (L * Y.submatrix id e) i a = 0 := by
      change (L * Y) i (e a) = 0
      rw [hLY, Matrix.one_apply_ne]
      rintro rfl
      exact hI a hi
    rw [this, zero_mul]

end Abstract

open GlobalTheory.StdPar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}


omit [NumberField E] in
theorem conj_mem_trivOn {A B B' : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)} {m u : GAd σ J}
    (h1 : ∀ y ∈ A, (matHom _ σ J m).1 *ᵥ y ∈ A) (h2 : ∀ y ∈ A, (matHom _ σ J m⁻¹).1 *ᵥ y ∈ A)
    (h3 : ∀ y ∈ B, (matHom _ σ J m⁻¹).1 *ᵥ y ∈ B') (hu : u ∈ trivOn σ J A B') : m * u * m⁻¹ ∈ trivOn σ J A B := by
  have e : ∀ (a : GAd σ J) y, (matHom _ σ J a⁻¹).1 *ᵥ (matHom _ σ J a).1 *ᵥ y = y := fun a y => by
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]
  have e' : ∀ y, (matHom _ σ J m).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y = y := fun y => by
    simpa only [inv_inv] using e m⁻¹ y
  have i1 : ∀ y, y ∈ A ↔ (matHom _ σ J m).1 *ᵥ y ∈ A := fun y => ⟨h1 y, fun h => e m y ▸ h2 _ h⟩
  have i2 : ∀ y, y ∈ A ↔ (matHom _ σ J m⁻¹).1 *ᵥ y ∈ A := fun y => ⟨h2 y, fun h => e' y ▸ h1 _ h⟩
  have v : ∀ y, (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y =
      (matHom _ σ J m).1 *ᵥ (matHom _ σ J u).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y := fun y => by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, mulVec_mulVec, mulVec_mulVec]
  refine ⟨fun y => by rw [v, ← i1, ← hu.1, ← i2], fun y hy => ?_⟩
  have := h1 _ (hu.2 _ (h3 y hy))
  rwa [mulVec_sub, e', ← v] at this


omit [NumberField E] in
theorem mem_trivOn_span {A : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)} {u : GAd σ J} {T : Set (Fin r)} {j : Fin r}
    (hj : j ∈ T) (hu : ∀ i ∈ T, u ∈ trivOn σ J A (colSpan F X {i})) : u ∈ trivOn σ J A (colSpan F X T) := by
  refine ⟨(hu j hj).1, fun y hy => ?_⟩
  have : colSpan F X T ≤ A.comap ((matHom _ σ J u).1.mulVecLin - LinearMap.id) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    exact (hu i hi).2 _ (Submodule.subset_span ⟨i, rfl, rfl⟩)
  exact this hy

theorem blockEmb_normalises : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      (∀ g, ∀ u ∈ GlobalTheory.StdPar.unip σ J Xf S, ι g * u * (ι g)⁻¹ ∈ GlobalTheory.StdPar.unip σ J Xf S) ∧
      ∀ y : GL (Fin d) (GlobalTheory.CuspRep.Cinf E), ι (GlobalTheory.CuspRep.infGL E d y) ∈ infPts σ J := by
  intro F E _ _ _ _ _ _ σ hσ n J hJ r X Y hW S l d h ι ⟨Φ, jj, _, _, _, hΦ, hι⟩ hS _ _
  constructor
  · let e : Fin d → Fin r := fun a => ⟨l + a.val, by omega⟩
    have hm : ∀ {a b c : ℕ} (U : Matrix (Fin a) (Fin b) E) (V : Matrix (Fin b) (Fin c) E),
        adMat F U * adMat F V = adMat F (U * V) := fun U V => (Matrix.map_mul).symm
    have hLX : adMat F (cT (σ : E →+* E) X * J) * adMat F X = 0 := by
      rw [hm, hW.xx]; exact Matrix.map_zero _ (map_zero _)
    have hLY : adMat F (cT (σ : E →+* E) X * J) * adMat F Y = 1 := by
      rw [hm, hW.xy]; exact Matrix.map_one _ (map_zero _) (map_one _)
    have hKX : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
      rw [hm, yx hσ hJ hW]; exact Matrix.map_one _ (map_zero _) (map_one _)
    have sp : ∀ g {I : Set (Fin r)}, ((∀ a, e a ∈ I) ∨ ∀ a, e a ∉ I) → ∀ y ∈ colSpan F X I,
        (matHom _ σ J (ι g)).1 *ᵥ y ∈ colSpan F X I := fun g I hI y hy => by
      rw [hι]
      exact blk_span (Y := adMat F Y) e _ _ hLX hKX hI hy
    have pp : ∀ g {I : Set (Fin r)}, ((∀ a, e a ∈ I) ∨ ∀ a, e a ∉ I) → ∀ y ∈ colPerp σ J X I,
        (matHom _ σ J (ι g)).1 *ᵥ y ∈ colPerp σ J X I := fun g I hI y hy => by
      rw [hι]
      simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
      exact blk_perp (X := adMat F X) (K := adMat F (cT (σ : E →+* E) Y * J)) e _ _ hLX hLY hI hy
    have cp : ∀ p : Fin r → Prop, (∀ a, e a ∈ {i | ∃ k ∈ S, i ≤ k ∧ p k}) ∨ ∀ a, e a ∉ {i | ∃ k ∈ S, i ≤ k ∧ p k} := fun p => by
      by_contra hc
      obtain ⟨h1, h2⟩ := not_or.1 hc
      obtain ⟨b, k, hk, hb, hp⟩ : ∃ b, e b ∈ {i | ∃ k ∈ S, i ≤ k ∧ p k} := by simpa only [not_forall, not_not] using h2
      refine h1 fun a => ⟨k, hk, ?_, hp⟩
      have hb' : l + b.val ≤ k.val := hb
      have : ¬ k.val + 1 < l + d := fun h' => hS k (by omega) h' hk
      change l + a.val ≤ k.val
      omega
    have cp' : (∀ a, e a ∈ {i | ∃ k ∈ S, i ≤ k}) ∨ ∀ a, e a ∉ {i | ∃ k ∈ S, i ≤ k} := by
      simpa only [and_true] using cp fun _ => True
    intro g u hu
    refine ⟨Subgroup.mem_iInf.2 fun j => ?_, conj_mem_trivOn (sp g cp') (map_inv ι g ▸ sp g⁻¹ cp')
      (map_inv ι g ▸ pp g⁻¹ cp') hu.2⟩
    have hu1 := Subgroup.mem_iInf.1 hu.1
    by_cases hj : j ∈ Set.range e
    · refine conj_mem_trivOn (B' := colSpan F X (Set.range e)) (sp g (cp _)) (map_inv ι g ▸ sp g⁻¹ (cp _))
        (fun y hy => map_inv ι g ▸ sp g⁻¹ (I := Set.range e) (Or.inl fun a => Set.mem_range_self a) y
          (Submodule.span_mono (Set.image_mono (Set.singleton_subset_iff.2 hj)) hy)) (mem_trivOn_span hj ?_)
      obtain ⟨b, rfl⟩ := hj
      rintro _ ⟨a, rfl⟩
      have key : ∀ a b : Fin d, ∀ k ∈ S, k < e a → k < e b := fun a b k hk hka => by
        have h1 : k.val < l + a.val := hka
        have h2 : ¬ l ≤ k.val := fun h' => hS k h' (by omega) hk
        change k.val < l + b.val
        omega
      have : {i | ∃ k ∈ S, i ≤ k ∧ k < e b} = {i | ∃ k ∈ S, i ≤ k ∧ k < e a} := Set.ext fun i =>
        ⟨fun ⟨k, hk, h1, h2⟩ => ⟨k, hk, h1, key _ _ k hk h2⟩, fun ⟨k, hk, h1, h2⟩ => ⟨k, hk, h1, key _ _ k hk h2⟩⟩
      rw [this]
      exact hu1 _
    · exact conj_mem_trivOn (sp g (cp _)) (map_inv ι g ▸ sp g⁻¹ (cp _))
        (map_inv ι g ▸ sp g⁻¹ (I := {j}) (Or.inr fun a (ha : e a = j) => hj (Exists.intro a ha))) (hu1 j)
  · have k1 : ∀ z, GlobalTheory.LFun.finTens F E (Φ.symm z) = (GlobalTheory.LFun.finAdEquiv F E).symm (GlobalTheory.CuspRep.pFin E z) := fun z => by
      have := congrArg (GlobalTheory.CuspRep.pFin E) (hΦ (Φ.symm z))
      rw [RingEquiv.apply_symm_apply] at this
      rw [this]
      exact ((GlobalTheory.LFun.finAdEquiv F E).symm_apply_apply _).symm
    have k2 : ∀ y, ((GlobalTheory.CuspRep.infGL E d y).1.map Φ.symm).map (GlobalTheory.LFun.finTens F E) = 1 := fun y => by
      have := congrArg Units.val (GlobalTheory.CuspRep.pFin_infGL (E := E) y)
      have e : ((GlobalTheory.CuspRep.infGL E d y).1.map Φ.symm).map (GlobalTheory.LFun.finTens F E) =
          ((GlobalTheory.CuspRep.infGL E d y).1.map (GlobalTheory.CuspRep.pFin E)).map (GlobalTheory.LFun.finAdEquiv F E).symm :=
        Matrix.ext fun a b => k1 _
      rw [e, show (GlobalTheory.CuspRep.infGL E d y).1.map (GlobalTheory.CuspRep.pFin E) = 1 from this]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have k3 : ∀ x, sigR (Af F) σ (GlobalTheory.LFun.finTens F E x) = GlobalTheory.LFun.finTens F E (sigR (AF F) σ x) := fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul a b => rfl
    intro y
    refine Units.ext ?_
    change (matHom _ σ J (ι (GlobalTheory.CuspRep.infGL E d y))).1.map (GlobalTheory.LFun.finTens F E) = 1
    have o : ∀ {a : ℕ}, (1 : Matrix (Fin a) (Fin a) (AF F ⊗[F] E)).map (GlobalTheory.LFun.finTens F E) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    rw [hι, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
      Matrix.map_mul, Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _), k2,
      ← GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map _ (sigR (Af F) σ) _ k3, ← map_inv, k2, o, o, Formalism.UG.cT_one, sub_self]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]

end GlobalTheory.BlockForms.Norm

end
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.fock_vector_isThetaFunction_definite_pair : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  ∀ T, IsThetaFunO X.ψ X.A X.B (X.fock T) := by
  first | exact @GlobalTheory.NormDict.fock_isThetaFunO | exact GlobalTheory.NormDict.fock_isThetaFunO | (intros; apply GlobalTheory.NormDict.fock_isThetaFunO <;> assumption)
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.substitution_inverse_transpose_maximalMinorProduct : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P)
    (T : Tup D P.a P.d P.n) (G : D.what₂.Tau → Matrix (Fin X.A.rank) (Fin X.A.rank) ℂ),
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ)) (fun τ => (G τ)⁻¹.transpose)
      (MvPolynomial.rename X.var (minorPol D T)) =
      (∏ τ, ((G τ)⁻¹.det) ^ P.n τ) • MvPolynomial.rename X.var (minorPol D T) := by
  first | exact @GlobalTheory.NormDict.substF_invT_minorPol | exact GlobalTheory.NormDict.substF_invT_minorPol | (intros; apply GlobalTheory.NormDict.substF_invT_minorPol <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.partial_L_trivial_rep_twist_eq_prod_hecke_L : ∀ {D : D7} (χ : (AE D)ˣ →* Circle) (Sf : Finset (FinPl D)) (n : ℕ), GlobalTheory.LFun.UnrOff χ (Sf : Set (FinPl D)) → EqRight (fun s => ∏ i ∈ Finset.range n, GlobalTheory.LFun.charL χ⁻¹ (Sf : Set (FinPl D)) (s + (n : ℂ) / 2 - i)) (fun s => GlobalTheory.LFun.LSD D Sf (GlobalTheory.BottomRallis.trivPar n) χ (s + 1 / 2)) := by
  first | exact @GlobalTheory.RallisEuler.trivPar_euler | exact GlobalTheory.RallisEuler.trivPar_euler | (intros; apply GlobalTheory.RallisEuler.trivPar_euler <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DepthUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem gcd_nsmul_mem_of {A S : Type*} [AddCommGroup A] [SetLike S A] [AddSubgroupClass S A] (Λ : S) {x : A}
    {k k' : ℕ} (h : k • x ∈ Λ) (h' : k' • x ∈ Λ) : Nat.gcd k k' • x ∈ Λ := by
  have e : Nat.gcd k k' • x = Nat.gcdA k k' • (k • x) + Nat.gcdB k k' • (k' • x) := by
    rw [← natCast_zsmul, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, Nat.gcd_eq_gcd_ab]
    congr 1; ring
  rw [e]
  exact add_mem (zsmul_mem h _) (zsmul_mem h' _)

theorem add_mul_succ_zsmul {A : Type*} [AddCommGroup A] (k : ℕ) (n : ℤ) (z w : A) :
    z + ((k : ℤ) * (n + 1)) • w = (z + ((k : ℤ) * n) • w) + k • w := by
  rw [mul_add, mul_one, add_smul, natCast_zsmul, add_assoc]

theorem add_mul_pred_zsmul {A : Type*} [AddCommGroup A] (k : ℕ) (n : ℤ) (z w : A) :
    (z + ((k : ℤ) * (n - 1)) • w) + k • w = z + ((k : ℤ) * n) • w := by
  rw [add_assoc, ← natCast_zsmul, ← add_smul]; congr 2; ring

theorem add_gcd_nsmul_eq {A : Type*} [AddCommGroup A] (k k' : ℕ) (z w : A) :
    z + Nat.gcd k k' • w = (z + ((k : ℤ) * Nat.gcdA k k') • w) + ((k' : ℤ) * Nat.gcdB k k') • w := by
  rw [add_assoc, ← add_smul, ← Nat.gcd_eq_gcd_ab, natCast_zsmul]

theorem isHalf_add_zsmul {e : AE D} {m n : ℕ} {a b : Mx D m n} (ha : IsHalf e a) (hb : IsHalf e b) (c : ℤ) :
    IsHalf e (a + c • b) := fun i j => by
  have h1 := ha i j
  have h2 := hb i j
  show e * (a i j + c • b i j) = a i j + c • b i j
  rw [zsmul_eq_mul, mul_add, mul_left_comm, h1, h2]

theorem DepthOK.flatProd_add_zsmul {S : GridChoice W U} {t : T} {Φ : G.Datum} {β : CosFam G t} {e : AE D} {k : ℕ}
    (hK : DepthOK S t Φ β e k) (c : ℤ)
    (x u : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
    (y v : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)))
    (hx : ∀ j, IsHalf e (x j)) (hy : ∀ i, IsHalf e (y i))
    (hu : ∀ j : Fin D.R.m, IsHalf e (u j) ∧ u j ∈ pairLat G (.top t j))
    (hv : ∀ i : Fin D.R.m, IsHalf e (v i) ∧ v i ∈ pairLat G (.chi i D.R.m)) :
    flatProd S t Φ β (x + ((k : ℤ) * c) • u) (y + ((k : ℤ) * c) • v) = flatProd S t Φ β x y := by
  induction c using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [add_mul_succ_zsmul, add_mul_succ_zsmul,
      hK.2 (x + ((k : ℤ) * n) • u) u (y + ((k : ℤ) * n) • v) v (fun j => isHalf_add_zsmul (hx j) (hu j).1 _) (fun i => isHalf_add_zsmul (hy i) (hv i).1 _) hu hv, ih]
  | pred n ih =>
    rw [← hK.2 (x + ((k : ℤ) * (-n - 1)) • u) u (y + ((k : ℤ) * (-n - 1)) • v) v (fun j => isHalf_add_zsmul (hx j) (hu j).1 _) (fun i => isHalf_add_zsmul (hy i) (hv i).1 _) hu hv,
      add_mul_pred_zsmul, add_mul_pred_zsmul, ih]

theorem depthOK_gcd (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (k k' : ℕ)
    (h : DepthOK S t Φ β e k) (h' : DepthOK S t Φ β e k') : DepthOK S t Φ β e (Nat.gcd k k') := by
  refine ⟨fun x y hx hy hF => ⟨fun j => gcd_nsmul_mem_of _ ((h.1 x y hx hy hF).1 j) ((h'.1 x y hx hy hF).1 j),
    fun i => gcd_nsmul_mem_of _ ((h.1 x y hx hy hF).2 i) ((h'.1 x y hx hy hF).2 i)⟩, ?_⟩
  intro x u y v hx hy hu hv
  rw [add_gcd_nsmul_eq k k' x u, add_gcd_nsmul_eq k k' y v,
    h'.flatProd_add_zsmul _ (x + ((k : ℤ) * Nat.gcdA k k') • u) u (y + ((k : ℤ) * Nat.gcdA k k') • v) v (fun j => isHalf_add_zsmul (hx j) (hu j).1 _)
      (fun i => isHalf_add_zsmul (hy i) (hv i).1 _) hu hv,
    h.flatProd_add_zsmul _ x u y v hx hy hu hv]

end GlobalTheory.DepthUnf

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.FrameTransport

def adSwap (D : D7) : StandardLatticesGL3.AE D →+* Lev.EAf D :=
  (Lev.swapAE D).comp (GlobalTheory.BotFormula.toAfE D).toRingHom

def inclEAf (D : D7) : D.host.E →+* Lev.EAf D := Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F)

def frConj {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) : GL (Fin n) (StandardLatticesGL3.AE D) →* GL (Fin n) (Lev.EAf D) :=
  (MulAut.conj (Formalism.UG.bc (inclEAf D) fr)).toMonoidHom.comp (Formalism.UG.bc (adSwap D))

theorem frConj_apply {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (h : GL (Fin n) (StandardLatticesGL3.AE D)) :
    frConj fr h = Formalism.UG.bc (inclEAf D) fr * Formalism.UG.bc (adSwap D) h * (Formalism.UG.bc (inclEAf D) fr)⁻¹ := rfl

end GlobalTheory.FrameTransport

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertCompletionConjugation_properties : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
  B.IsGood σ → ∀ {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w),
  (∀ x, GlobalTheory.InertBigCell.conjW σ hw (GlobalTheory.InertBigCell.conjW σ hw x) = x) ∧
  (∀ x ∈ w.adicCompletionIntegers E, GlobalTheory.InertBigCell.conjW σ hw x ∈ w.adicCompletionIntegers E) ∧
  (2 : w.adicCompletion E)⁻¹ ∈ w.adicCompletionIntegers E ∧
  (∀ e : E, GlobalTheory.InertBigCell.conjW σ hw (algebraMap E (w.adicCompletion E) e) = algebraMap E (w.adicCompletion E) (σ e)) := by
  first | exact @GlobalTheory.InertBigCell.conjW_props | exact GlobalTheory.InertBigCell.conjW_props | (intros; apply GlobalTheory.InertBigCell.conjW_props <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.adelicMatrix_trivial_off_inertPlace_unitary_at_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {v : Pl (F := F)}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι],
  (∀ (J : Matrix ι ι E) (P : Matrix ι ι (w.adicCompletion E)),
    (GlobalTheory.InertBigCell.glueW hw P)ᵀ * incM F J * (GlobalTheory.InertBigCell.glueW hw P).map (cA σ) = incM F J ↔
      Pᵀ * J.map (algebraMap E (w.adicCompletion E)) * P.map (GlobalTheory.InertBigCell.conjW σ hw) = J.map (algebraMap E (w.adicCompletion E))) ∧
  (∀ P : Matrix (ι ⊕ ι) (ι ⊕ ι) (w.adicCompletion E), P * diagCols ι = diagCols ι →
    GlobalTheory.InertBigCell.glueW hw P * (diagCols ι : Matrix (ι ⊕ ι) ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = diagCols ι) ∧
  (∀ P : Matrix (ι ⊕ ι) (ι ⊕ ι) (w.adicCompletion E),
    ⅟(2 : AF F) • ((GlobalTheory.InertBigCell.glueW hw P).toBlocks₁₁ + (GlobalTheory.InertBigCell.glueW hw P).toBlocks₁₂ +
      (GlobalTheory.InertBigCell.glueW hw P).toBlocks₂₁ + (GlobalTheory.InertBigCell.glueW hw P).toBlocks₂₂) =
    GlobalTheory.InertBigCell.glueW hw ((2 : w.adicCompletion E)⁻¹ • (P.toBlocks₁₁ + P.toBlocks₁₂ + P.toBlocks₂₁ + P.toBlocks₂₂))) := by
  first | exact @GlobalTheory.InertBigCell.glueW_read_at_place | exact GlobalTheory.InertBigCell.glueW_read_at_place | (intros; apply GlobalTheory.InertBigCell.glueW_read_at_place <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertBigCell

theorem iotaW_adelic_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {v : Pl (F := F)}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w),
  Function.Injective (GlobalTheory.InertBigCell.iotaW hw) ∧
  (∀ x y, GlobalTheory.InertBigCell.iotaW hw (x * y) = GlobalTheory.InertBigCell.iotaW hw x * GlobalTheory.InertBigCell.iotaW hw y) ∧
  GlobalTheory.InertBigCell.iotaW hw 1 = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) ∧
  (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, GlobalTheory.InertBigCell.iotaW hw x = z) ∧
  (∀ x, GlobalTheory.InertBigCell.iotaW hw (GlobalTheory.InertBigCell.conjW σ hw x) = cA σ (GlobalTheory.InertBigCell.iotaW hw x)) ∧
  (∀ x, GlobalTheory.InertBigCell.iotaW hw (2⁻¹ * x) = ⅟(2 : AF F) • GlobalTheory.InertBigCell.iotaW hw x) ∧
  (∀ e : E, GlobalTheory.InertBigCell.iotaW hw (algebraMap E (w.adicCompletion E) e) =
    algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) * inclR (F := F) (AF F) e) := by
  intro F E _ _ _ _ _ σ v w hw
  refine ⟨iotaW_injective hw, iotaW_mul hw, iotaW_one hw, fun z => ?_, iotaW_conjW σ hw, fun x => ?_,
    iotaW_algebraMap hw⟩
  · rw [GlobalTheory.InertLocField.at_iff v z]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨InertChart.complEquiv hw (under_eq_of_isInertAt hw) y, by
        rw [iotaW_apply, RingEquiv.symm_apply_apply]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, (iotaW_apply hw x).symm⟩
  · have h := invOf_two_smul_add_iotaW hw 0 x
    rw [add_zero, zero_add, zero_add] at h
    exact h.symm

end GlobalTheory.InertBigCell
end
