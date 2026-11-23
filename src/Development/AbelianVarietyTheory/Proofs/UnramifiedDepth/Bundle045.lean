module

public import ReciprocityTheory.DualLattices.Bundle019
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle039
public import Mathlib.Algebra.DirectSum.LinearMap
public import ReciprocityTheory.DualLattices.Bundle014
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle036
public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAdjointIntegralEndOfLadicLimit
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle035
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigAdd

private theorem trace_eq (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (OE : Type) [CommRing OE] [IsDomain OE]
    [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [Fintype (OE →+* C)]
    (V : Type) [AddCommGroup V] [Module C V] [Module.Finite C V] (ρ : OE →+* Module.End C V) (a : OE) :
    LinearMap.trace C V (ρ a) = ∑ τ : OE →+* C,
      (Module.finrank C ↥(⨅ b : OE, Module.End.eigenspace (ρ b) (τ b)) : C) * τ a := by
  classical
  obtain ⟨h1, h2⟩ := (GlobalTheory.order_rep_diagonalisable C OE).2 V ρ
  have hI := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top h1 h2
  have hv : ∀ (τ : OE →+* C) (v : V), v ∈ (⨅ b : OE, Module.End.eigenspace (ρ b) (τ b)) → ρ a v = τ a • v :=
    fun τ v hv => Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hv a)
  have hf : ∀ τ : OE →+* C, Set.MapsTo (ρ a) ↑(⨅ b : OE, Module.End.eigenspace (ρ b) (τ b))
      ↑(⨅ b : OE, Module.End.eigenspace (ρ b) (τ b)) := fun τ v h => by
    have h' : v ∈ (⨅ b : OE, Module.End.eigenspace (ρ b) (τ b)) := h
    have := Submodule.smul_mem _ (τ a) h'
    rw [← hv τ v h'] at this
    exact this
  rw [LinearMap.trace_eq_sum_trace_restrict hI hf]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have : (ρ a).restrict (hf τ) = τ a • LinearMap.id := by
    ext v
    exact hv τ v.1 v.2
  rw [this, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

private theorem trace_mat (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (O : Type) [CommRing O] [Algebra O C]
    (OE : Type) [CommRing OE] [IsDomain OE]
    [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [Fintype (OE →+* C)] (d : ℕ)
    (ρ : OE →+* Matrix (Fin d) (Fin d) O) (a : OE) :
    algebraMap O C (ρ a).trace = ∑ τ : OE →+* C, (eigDim C ρ τ : C) * τ a := by
  have := trace_eq C OE (Fin d → C)
    ((Matrix.toLinAlgEquiv' (R := C) (n := Fin d)).toRingEquiv.toRingHom.comp
      ((algebraMap O C).mapMatrix.comp ρ)) a
  refine Eq.trans ?_ this
  change _ = LinearMap.trace C _ (Matrix.toLin' ((ρ a).map (algebraMap O C)))
  rw [Matrix.trace_toLin'_eq, ← AddMonoidHom.map_trace]

private theorem coeff_eq (C : Type) [Field C] [CharZero C] (OE : Type) [CommRing OE] [Fintype (OE →+* C)]
    (m n : (OE →+* C) → ℕ) (h : ∀ a, ∑ τ : OE →+* C, (m τ : C) * τ a = ∑ τ : OE →+* C, (n τ : C) * τ a)
    (τ : OE →+* C) : m τ = n τ := by
  have li : LinearIndependent C (fun τ : OE →+* C => (τ : OE → C)) :=
    (linearIndependent_monoidHom OE C).comp (fun τ : OE →+* C => (τ : OE →* C))
      RingHom.coe_monoidHom_injective
  have := Fintype.linearIndependent_iffₛ.1 li (fun τ => (m τ : C)) (fun τ => (n τ : C))
    (by funext a; simpa [Finset.sum_apply] using h a) τ
  exact_mod_cast this

private def trHom {O OE : Type} [CommRing O] [CommRing OE] {d : ℕ} (ρ : OE →+* Matrix (Fin d) (Fin d) O) :
    OE →+* Matrix (Fin d) (Fin d) O where
  toFun a := (ρ a)ᵀ
  map_one' := by simp
  map_mul' a b := by rw [mul_comm a b, map_mul, Matrix.transpose_mul]
  map_zero' := by simp
  map_add' a b := by simp

theorem eigDim_add_transpose : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (O : Type) [CommRing O] [Algebra O C] (OE : Type) [CommRing OE] [IsDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (d r g : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O), SplitEx A B → ∀ (ρ : OE →+* Matrix (Fin d) (Fin d) O) (ρA : OE →+* Matrix (Fin r) (Fin r) O) (ρB : OE →+* Matrix (Fin g) (Fin g) O), (∀ a, B * ρ a = ρB a * B) → (∀ a, ρ a * A = A * ρA a) → ∀ τ : OE →+* C, eigDim C ρ τ = eigDim C ρA τ + eigDim C ρB τ ∧ eigDim C (fun a => (ρ a)ᵀ) τ = eigDim C ρ τ := by
  intro C _ _ _ O _ _ OE _ _ _ _ _ d r g A B hS ρ ρA ρB hB hA τ
  haveI : Finite (OE →+* C) := (GlobalTheory.order_rep_diagonalisable C OE).1
  letI : Fintype (OE →+* C) := Fintype.ofFinite _
  obtain ⟨-, A', B', h1, h2, h3⟩ := hS
  constructor
  · refine coeff_eq C OE (fun τ => eigDim C ρ τ) (fun τ => eigDim C ρA τ + eigDim C ρB τ) (fun a => ?_) τ
    have ht : (ρ a).trace = (ρA a).trace + (ρB a).trace := by
      have e1 : (ρ a * (A * A')).trace = (ρA a).trace := by
        rw [← Matrix.mul_assoc, hA, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]
      have e2 : (ρ a * (B' * B)).trace = (ρB a).trace := by
        rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hB, Matrix.mul_assoc, h2,
          Matrix.mul_one]
      rw [← e1, ← e2, ← Matrix.trace_add, ← Matrix.mul_add, h3, Matrix.mul_one]
    simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib]
    rw [← trace_mat, ← trace_mat, ← trace_mat, ht, map_add (f := _)]
  · refine coeff_eq C OE (fun τ => eigDim C (trHom ρ) τ) (fun τ => eigDim C ρ τ) (fun a => ?_) τ
    rw [← trace_mat, ← trace_mat]
    exact congrArg _ (Matrix.trace_transpose _)

end GlobalTheory.EigAdd
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private lemma dualNumberPoint_preimage_top_of_reduction {O : Type} [CommRing O] {d r g m : ℕ} (A : Matrix (Fin d) (Fin r) O)
    (B : Matrix (Fin g) (Fin d) O) (h : SplitEx A B) (s : Fin m → Fin d → O)
    (hT : ∀ i, ∃ k, Aᵀ *ᵥ s k = Pi.single i 1) (f : Fin d → O) :
    ∃ (t : Fin d → O) (l : Fin g → O), t ∈ Submodule.span O (Set.range s) ∧ f = t + Bᵀ *ᵥ l := by
  obtain ⟨-, A', B', -, -, h3⟩ := h
  choose k hk using hT
  set t : Fin d → O := ∑ i, (Aᵀ *ᵥ f) i • s (k i) with ht
  have h0 : Aᵀ *ᵥ (f - t) = 0 := by
    rw [Matrix.mulVec_sub, ht, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hk]
    rw [sub_eq_zero]
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : (A * A' + B' * B)ᵀ *ᵥ (f - t) = f - t := by rw [h3]; simp
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero, zero_add] at h1
  refine ⟨t, B'ᵀ *ᵥ (f - t), ?_, by rw [h1]; abel⟩
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k i, rfl⟩)

private lemma idem_fix {O E : Type} [CommRing O] {g m : ℕ} (ρ : E → Matrix (Fin g) (Fin g) O)
    (ε : Fin m → Matrix (Fin g) (Fin g) O) (sg : Fin m → E → O)
    (horth : ∀ i j, ε i * ε j = if i = j then ε i else 0) (hsum : ∑ i, ε i = 1)
    (heig : ∀ a i, ρ a * ε i = sg i a • ε i) (i : Fin m)
    (hd : ∀ j, i ≠ j → ∃ a, IsUnit (sg i a - sg j a)) (y : Fin g → O)
    (hy : ∀ a, ρ a *ᵥ y = sg i a • y) : ε i *ᵥ y = y := by
  have hl : ∀ a j, ε j * ρ a = sg j a • ε j := by
    intro a j
    have : ρ a = ∑ k, sg k a • ε k := by
      rw [← Matrix.mul_one (ρ a), ← hsum, Matrix.mul_sum]
      simp only [heig]
    rw [this, Matrix.mul_sum]
    simp only [Matrix.mul_smul, horth]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · simp
  have hz : ∀ j, i ≠ j → ε j *ᵥ y = 0 := by
    intro j hj
    obtain ⟨a, ha⟩ := hd j hj
    have h1 : ε j *ᵥ (ρ a *ᵥ y) = sg j a • (ε j *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, hl, Matrix.smul_mulVec]
    rw [hy, Matrix.mulVec_smul] at h1
    have h2 : (sg i a - sg j a) • (ε j *ᵥ y) = 0 := by rw [sub_smul, h1, sub_self]
    exact (ha.smul_eq_zero).1 h2
  have h3 : (∑ j, ε j) *ᵥ y = y := by rw [hsum]; simp
  rw [Matrix.sum_mulVec, Finset.sum_eq_single i] at h3
  · exact h3
  · intro b _ hb
    exact hz b hb.symm
  · simp

theorem cokE_surj_res_quot : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ (U : UnramData p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp H) (i : Fin U.m) (τ : OE →+* O), (∀ x, U.sg i x = tauExt τ x) → ∀ (n : ℕ) (W : Fin n → Fin d → O), EigB ρG τ W → ∃ f : cokE H.Ht U.εT U.εL i (U.cj i) →ₗ[O] ((Fin n → O) ⧸ Submodule.span O (Set.range fun k => Pdiv.ChartF.res W (s k))), Function.Surjective f := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp _ g H d r m A B ρG N s hL U i τ hτ n W hW
  have hsurj := (GlobalTheory.ChF.eigB_res_surjective C v O hv OE d n ρG τ W hW).1
  have hZ : ∀ c : ℤ_[p], H.ρL (c ⊗ₜ[ℤ] (1 : OE)) = algebraMap ℤ_[p] O c • 1 := fun c =>
    (GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique p O).2 g (H.ρL.comp Algebra.TensorProduct.includeLeftRingHom) c
  have hy : ∀ l x, H.ρL x *ᵥ (B *ᵥ W l) = U.sg i x • (B *ᵥ W l) := by
    intro l x
    rw [hτ]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), Matrix.add_mulVec, hx, hy, add_smul]
    | tmul c a =>
      have e : (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = (c ⊗ₜ[ℤ] (1 : OE)) * ((1 : ℤ_[p]) ⊗ₜ[ℤ] a) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      have e2 : tauExt τ (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = algebraMap ℤ_[p] O c * τ a := by
        simp [tauExt, Algebra.ofId_apply]
      rw [e2, e, map_mul, hZ, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mulVec, Matrix.mulVec_mulVec,
        ← hL.eqB, ← Matrix.mulVec_mulVec, hW.1, Matrix.mulVec_smul, mul_smul]
  have hfix : ∀ l, U.εL i *ᵥ (B *ᵥ W l) = B *ᵥ W l := fun l =>
    idem_fix (fun x => H.ρL x) U.εL (fun j x => U.sg j x) U.εL_orth U.εL_sum U.εL_eig i
      (fun j hj => by
        obtain ⟨a, ha⟩ := U.distinct i j hj
        exact ⟨a, hv.isUnit_of_one' ha⟩) _ (hy l)
  have hres : ∀ l : Fin g → O, Pdiv.ChartF.res W (Bᵀ *ᵥ ((U.εL i)ᵀ *ᵥ l)) = Pdiv.ChartF.res W (Bᵀ *ᵥ l) := by
    intro l
    ext k
    change W k ⬝ᵥ (Bᵀ *ᵥ ((U.εL i)ᵀ *ᵥ l)) = W k ⬝ᵥ (Bᵀ *ᵥ l)
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      hfix, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  set S : Submodule O (Fin n → O) := Submodule.span O (Set.range fun k => Pdiv.ChartF.res W (s k)) with hS
  have hSm : ∀ t ∈ Submodule.span O (Set.range s), Pdiv.ChartF.res W t ∈ S := by
    intro t ht
    have := Submodule.mem_map_of_mem (f := Pdiv.ChartF.res W) ht
    rwa [Submodule.map_span, ← Set.range_comp] at this
  let F : LinearMap.range (Matrix.mulVecLin (U.εL i)ᵀ) →ₗ[O] ((Fin n → O) ⧸ S) :=
    S.mkQ ∘ₗ Pdiv.ChartF.res W ∘ₗ Matrix.mulVecLin Bᵀ ∘ₗ Submodule.subtype _
  have hF : ∀ x, F x = S.mkQ (Pdiv.ChartF.res W (Bᵀ *ᵥ x.1)) := fun x => rfl
  refine ⟨Submodule.liftQ _ F ?_, ?_⟩
  · rintro x ⟨ν, -, hx⟩
    rw [LinearMap.mem_ker, hF, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    apply hSm
    have hx' : x.1 = ∑ c, ν c • (fun l => H.Ht l c) := by
      have : H.Ht *ᵥ ν = x.1 := hx
      rw [← this]
      ext l
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [hx', Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    obtain ⟨k, hk⟩ := hL.fromB c
    rw [Matrix.mulVec_smul, ← hk]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · intro z
    obtain ⟨z, rfl⟩ := S.mkQ_surjective z
    obtain ⟨f, rfl⟩ := hsurj z
    obtain ⟨t, l, ht, rfl⟩ := dualNumberPoint_preimage_top_of_reduction A B hL.exact s hL.fromT f
    refine ⟨Submodule.Quotient.mk ⟨(U.εL i)ᵀ *ᵥ l, l, rfl⟩, ?_⟩
    rw [Submodule.liftQ_apply, hF, hres, map_add (f := _), map_add (f := _)]
    have : S.mkQ (Pdiv.ChartF.res W t) = 0 := (Submodule.Quotient.mk_eq_zero S).2 (hSm t ht)
    rw [this, zero_add]

end GlobalTheory.ChF
end

section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem exists_mulEquiv {B B' : Scheme.{0}} {G : Over B} [GrpObj G] {G' : Over B'} [GrpObj G']
    {f : B' ⟶ B} {π : G'.left ⟶ G.left} (h : Geo.Tor.IsGrpPullback G' G f π) {Y : Scheme.{0}}
    (t' : Y ⟶ B') (t : Y ⟶ B) (ht : t = t' ≫ f) :
    ∃ e : (Over.mk t' ⟶ G') ≃* (Over.mk t ⟶ G), ∀ z, (e z).left = z.left ≫ π := by
  subst ht
  let m : (Over.mk t' ⟶ G') → (Over.mk (t' ≫ f) ⟶ G) := fun z =>
    Over.homMk (z.left ≫ π) (by
      have := Over.w z
      simp only [Over.mk_hom] at this
      simp only [Over.mk_hom, Category.assoc, h.1.w]
      rw [← Category.assoc, this])
  have hm : ∀ z, (m z).left = z.left ≫ π := fun _ => rfl
  have hb : Function.Bijective m := by
    refine ⟨fun z w hzw => ?_, fun y => ?_⟩
    · apply Over.OverMorphism.ext
      refine h.1.hom_ext ?_ ?_
      · rw [← hm, ← hm, hzw]
      · rw [Over.w z, Over.w w]
    · refine ⟨Over.homMk (h.1.lift y.left t' (Over.w y)) (h.1.lift_snd _ _ _), ?_⟩
      apply Over.OverMorphism.ext
      exact h.1.lift_fst _ _ _
  refine ⟨MulEquiv.mk (Equiv.ofBijective m hb) (fun z w => ?_), hm⟩
  apply Over.OverMorphism.ext
  exact (h.2 (Over.mk t') z w (m z) (m w) rfl rfl).symm

private abbrev resAlg {R R' : Type} [CommRing R] [CommRing R'] (β : R →+* R') (S : Type) [CommRing S]
    [Algebra R' S] : Algebra R S := ((algebraMap R' S).comp β).toAlgebra

private def resHom {R R' : Type} [CommRing R] [CommRing R'] (β : R →+* R') {S S' : Type} [CommRing S]
    [Algebra R' S] [CommRing S'] [Algebra R' S'] (φ : S →ₐ[R'] S') :
    @AlgHom R S S' _ _ _ (resAlg β S) (resAlg β S') :=
  letI := resAlg β S
  letI := resAlg β S'
  { φ.toRingHom with commutes' := fun r => φ.commutes (β r) }

theorem nilChart_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (β : R →+* R') (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom β)) π → ∀ (d : ℕ) (F : Fin d → PS R 2 d) (X : Fam G d), NilChart G F X → ∃ X' : Fam G' d, NilChart G' (fun i => MvPowerSeries.map β (F i)) X' ∧ ∀ (f : G ⟶ G) (f' : G' ⟶ G') (α : Fin d → PS R 1 d), f'.left ≫ π = π ≫ f.left → Reads X X f α → Reads X' X' f' (fun i => MvPowerSeries.map β (α i)) := by
  intro R R' _ _ β G _ _ G' _ _ π h d F X hX
  have key : ∀ (S : Type) [CommRing S] [Algebra R' S],
      ∃ e : (sp (R₀ := R') S ⟶ G') ≃* (@sp R _ S _ (resAlg β S) ⟶ G), ∀ z, (e z).left = z.left ≫ π :=
    fun S _ _ => exists_mulEquiv h _ _ (by rw [← Spec.map_comp]; rfl)
  choose e he using key
  have hnat : ∀ (S : Type) [CommRing S] [Algebra R' S] (S' : Type) [CommRing S'] [Algebra R' S']
      (φ : S →ₐ[R'] S') (z : sp (R₀ := R') S ⟶ G'), e S' (spMap φ ≫ z) =
        @spMap R _ S S' _ (resAlg β S) _ (resAlg β S') (resHom β φ) ≫ e S z := by
    intro S _ _ S' _ _ φ z
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc]
    rfl
  have hnv : ∀ (S : Type) [CommRing S] [Algebra R' S] (n : ℕ) (a : Fin n → Fin d → S),
      (∀ i j, IsNilpotent (a i j)) → ∀ f : PS R n d,
      nv (@algebraMap R S _ _ (resAlg β S)) f a = nv (algebraMap R' S) (MvPowerSeries.map β f) a :=
    fun S _ _ n a ha f => (nv_calculus R' S (algebraMap R' S) n d a ha).2.2.2.1 R β f
  refine ⟨fun S _ _ a => (e S).symm (@X S _ (resAlg β S) a), ⟨fun S _ _ => ?_, fun S _ _ S' _ _ φ a ha => ?_,
    fun S _ _ a b ha hb hab => ?_, fun S _ _ S' _ _ ρ σ hρ hn z hz => ?_, fun S _ _ a b ha hb => ?_⟩,
    fun f f' α hf hα => ⟨fun j => ?_, fun S _ _ a ha => ?_⟩⟩
  · rw [@hX.zero S _ (resAlg β S), map_one]
  · apply (e S').injective
    rw [hnat, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact @hX.nat S _ (resAlg β S) S' _ (resAlg β S') (resHom β φ) a ha
  · exact @hX.inj S _ (resAlg β S) a b ha hb ((e S).symm.injective hab)
  · obtain ⟨a, ha, hz'⟩ := @hX.surj S _ (resAlg β S) S' _ (resAlg β S') (resHom β ρ) (resHom β σ)
      (by
        letI := resAlg β S
        letI := resAlg β S'
        exact AlgHom.ext fun x => DFunLike.congr_fun hρ x) hn (e S z)
      (by rw [← hnat, hz, map_one])
    exact ⟨a, ha, by rw [← hz', MulEquiv.symm_apply_apply]⟩
  · rw [← map_mul, @hX.law S _ (resAlg β S) a b ha hb]
    refine congrArg (fun c => (e S).symm (@X S _ (resAlg β S) c)) (funext fun k => hnv S 2 _ (fun i j => ?_) _)
    fin_cases i
    · exact ha j
    · exact hb j
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hα.1 j, map_zero]
  · apply (e S).injective
    have h1 : ∀ z : sp (R₀ := R') S ⟶ G', e S (z ≫ f') = e S z ≫ f := fun z => by
      apply Over.OverMorphism.ext
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc, hf]
    rw [h1, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, @hα.2 S _ (resAlg β S) a ha]
    refine congrArg (@X S _ (resAlg β S)) (funext fun k => hnv S 1 _ (fun i j => ?_) _)
    fin_cases i
    exact ha j

end GlobalTheory.ChF
end
end

section

noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.GermDerivativeLinearMaps GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ActionLimit

namespace GlobalTheory.ActionEnd

variable {C : Type} [Field C]

theorem germ_comp1_zero_point_left {dd n : ℕ} (a : Pt C n dd) (ha : GP a) : comp1 (pt C dd (0 : Fin 1)) a = a := by
  funext i
  rw [germComp1_eq_subst]
  exact MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 1 × Fin dd => ha q.2) _

theorem actK_self [CharZero C] {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (B : FB C dd O) (a : O) :
    B.actK C a = B.A.act a := by
  funext i
  show MvPowerSeries.map (RingHom.id C) _ = _
  rw [MvPowerSeries.map_id]; rfl

theorem exists_isEnd_act : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I) (a : O), ∃ M M' : Matrix (Fin dd) (Fin dd) C, (∀ v, M.mulVec v = linAct (Y.B.A.act a) v) ∧ (∀ v, M'.mulVec v = linAct (Y.B.A.act (star a)) v) ∧ IsEnd (Y.raw p) V M M' ∧ un1 (Y.B.hL C Y.h a) = hEnd (Y.raw p) 1 M := by
  intro C _ _ V O _ _ dd Y d _ I _ p a
  have hX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
    fun i => by simp
  have g : ∀ b, GP (Y.B.A.act b) := fun b i => Y.B.A.const b i
  refine ⟨dLin (Y.B.A.act a), dLin (Y.B.A.act (star a)), fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · refine isEnd_of_hom Y p _ _ (g _) (g _) (Y.B.A.hom _) (Y.B.A.hom _) (Y.intAct _) (Y.intAct _) ?_
    have h := Y.gauge.ad a
    rw [actK_self, actK_self] at h
    rw [← h]
    have e : FB.toK C (Y.B.ad a) = Y.B.ad a := by
      show MvPowerSeries.map (RingHom.id C) _ = _
      rw [MvPowerSeries.map_id]; rfl
    rw [e]
    exact Y.intAd a
  · have p0 : GP (pt C (n := 2) dd 0) := gp_pt 0
    have p1 : GP (pt C (n := 2) dd 1) := gp_pt 1
    have q0 : GP (pt C (n := 1) dd 0) := gp_pt 0
    have hs : MvPowerSeries.HasSubst
        (fun q : Fin 1 × Fin dd => (MvPowerSeries.X q.2 : MvPowerSeries (Fin dd) C)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hX q.2
    have e1 := matrixEnd_eq_subst Y p (pt C dd 0) q0 (by
      rw [germ_comp1_zero_point_left _ (gp_addOf _ Y.B.G.const _ _ p0 p1), germ_comp1_zero_point_left _ p0, germ_comp1_zero_point_left _ p1]) _ hX
    rw [germLinearPart_coordinatePoint_zero] at e1
    have e2 := matrixEnd_eq_subst Y p _ (g a) (Y.B.A.hom a) _ hX
    have e3 : comp1 (Y.B.A.act a) (pt C dd (0 : Fin 1)) = Y.B.A.act a := by
      funext i
      rw [germComp1_eq_subst]
      have : (fun q : Fin 1 × Fin dd => pt C dd (0 : Fin 1) q.2) = MvPowerSeries.X := by
        funext ⟨s, x⟩
        obtain rfl : s = 0 := Subsingleton.elim _ _
        rfl
      rw [this, MvPowerSeries.subst_self]; rfl
    have e4 : un1 (Y.B.hL C Y.h a) = MvPowerSeries.subst
        (fun q : Fin 1 × Fin dd => (MvPowerSeries.X q.2 : MvPowerSeries (Fin dd) C)) (Y.B.hL C Y.h a) := by
      rw [← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]; rfl
    rw [e4, FB.hL, actK_self, e3, ev, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 2 × Fin dd => pair_points_zero_constant q0 (g a) q.1 q.2) hs,
      hEnd, hAt]
    show MvPowerSeries.subst _ Y.h = MvPowerSeries.subst _ Y.h
    congr 1
    funext ⟨s, x⟩
    fin_cases s
    · exact (e1 x).symm
    · exact (e2 x).symm

end GlobalTheory.ActionEnd
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hodgeTate_datum_hypotheses_period_tower : ∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p) (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [StarRing OE], HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) (show O from (Ainf.ainfTowerL p O hv ε hε).c) := by
  first | exact @GlobalTheory.ChF.hodgeTateSetting_ainfTower_of_isPrimitiveRoot | exact GlobalTheory.ChF.hodgeTateSetting_ainfTower_of_isPrimitiveRoot | (intros; apply GlobalTheory.ChF.hodgeTateSetting_ainfTower_of_isPrimitiveRoot <;> assumption)
end
