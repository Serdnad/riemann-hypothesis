module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.LagrThetaInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev dC (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin (n + n)) (Fin n) R :=
  ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) R).submatrix finSumFinEquiv.symm id)

theorem dC_mul_inl {R : Type} [CommRing R] {n m : ℕ} (a : Matrix (Fin n) (Fin m) R) (p : Fin n) (j : Fin m) :
    (dC R n * a) (finSumFinEquiv (Sum.inl p)) j = a p j := by
  simp only [dC, Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  simp [diagCols, Matrix.one_apply]

theorem dC_mul_inr {R : Type} [CommRing R] {n m : ℕ} (a : Matrix (Fin n) (Fin m) R) (p : Fin n) (j : Fin m) :
    (dC R n * a) (finSumFinEquiv (Sum.inr p)) j = a p j := by
  simp only [dC, Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  simp [diagCols, Matrix.one_apply]

theorem dC_mul_castAdd {R : Type} [CommRing R] {n m : ℕ} (a : Matrix (Fin n) (Fin m) R) (p : Fin n) (j : Fin m) :
    (dC R n * a) (Fin.castAdd n p) j = a p j := by
  simpa using dC_mul_inl a p j

theorem dC_mul_addNat {R : Type} [CommRing R] {n m : ℕ} (a : Matrix (Fin n) (Fin m) R) (p : Fin n) (j : Fin m) :
    (dC R n * a) (p.addNat n) j = a p j := by
  simpa using dC_mul_inr a p j

theorem dC_mul_eq {R : Type} [CommRing R] {n m : ℕ} (a : Matrix (Fin n) (Fin m) R) :
    dC R n * a = Matrix.of fun i j => a (Sum.elim id id (finSumFinEquiv.symm i)) j := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with p | p
  · rw [dC_mul_inl, Matrix.of_apply, Equiv.symm_apply_apply]; rfl
  · rw [dC_mul_inr, Matrix.of_apply, Equiv.symm_apply_apply]; rfl

theorem dblG_apply {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (i k : Fin n ⊕ Fin n) :
    GlobalTheory.WeilSchrodinger.DblTargetF.dblG J (finSumFinEquiv i) (finSumFinEquiv k) = dbl J i k := by
  simp only [GlobalTheory.WeilSchrodinger.DblTargetF.dblG, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem hTens_dC (σ : E →ₐ[F] E) {nS nT : ℕ} (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E)
    (a b : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) :
    hTens (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB) (dC (AF F ⊗[F] E) nT * a) (dC (AF F ⊗[F] E) nT * b) = 0 := by
  unfold hTens
  have ha : dC (AF F ⊗[F] E) nT * a = Matrix.of fun i j => a (Sum.elim id id (finSumFinEquiv.symm i)) j :=
    dC_mul_eq a
  have hb : dC (AF F ⊗[F] E) nT * b = Matrix.of fun i j => b (Sum.elim id id (finSumFinEquiv.symm i)) j :=
    dC_mul_eq b
  rw [ha, hb]
  simp only [← finSumFinEquiv.sum_comp, Matrix.of_apply, Equiv.symm_apply_apply, incM, Matrix.map_apply,
    Matrix.transpose_apply, dblG_apply]
  simp only [Fintype.sum_sum_type]
  simp [dbl, Finset.sum_add_distrib, Finset.sum_neg_distrib, dC_mul_castAdd, dC_mul_addNat]

end GlobalTheory.LagrThetaInv

namespace GlobalTheory.LagrThetaInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem schr_dC (σ : E →ₐ[F] E) {nS nT : ℕ} (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E)
    (ξ : AF F ⊗[F] E) {κ : Type} [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ)
    (ψ : AddChar (AF F) ℂ) (a b : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) (φ : (κ → AF F) → ℂ) :
    schr ψ (co.e (dC (AF F ⊗[F] E) nT * a)) (schr ψ (co.e (dC (AF F ⊗[F] E) nT * b)) φ) =
      schr ψ (co.e (dC (AF F ⊗[F] E) nT * (a + b))) φ := by
  rw [GlobalTheory.ThetaQuasiRat.schr_schr, ← co.form, symp, hTens_dC, mul_zero, map_zero, mul_zero,
    AddChar.map_zero_eq_one, one_smul, ← map_add, Matrix.mul_add]

theorem dC_map {n : ℕ} : (dC E n).map (incAF F E) = dC (AF F ⊗[F] E) n := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with p | p <;>
    simp only [dC, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, diagCols,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.one_apply] <;> split_ifs <;> simp

theorem dC_mul_rat {nS nT : ℕ} (γ : Matrix (Fin nT) (Fin nS) E) :
    dC (AF F ⊗[F] E) nT * γ.map (incAF F E) = incM F (dC E nT * γ) := by
  rw [← dC_map, ← Matrix.map_mul]
  rfl

end GlobalTheory.LagrThetaInv


open scoped Pointwise in
open GlobalTheory.LagrThetaInv in
theorem GlobalTheory.LagrThetaInv.lagrInt_rho_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (κ : Type) [Fintype κ]
      (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)), ∀ φ ∈ schA F κ,
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (co.rho B.ψ (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) φ)) = GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JT JB ξ κ _ co hco ν 𝓕 _ h𝓕 u φ hφ
  change GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT)
      (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (co.rho B.ψ (dC (AF F ⊗[F] E) nT * u) φ)) =
    GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ)
  set g : WOF F E nS nT → ℂ := fun v => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (dC (AF F ⊗[F] E) nT * v) with hg
  have h1 : ∀ v : WOF F E nS nT, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (co.rho B.ψ (dC (AF F ⊗[F] E) nT * u) φ)
      (dC (AF F ⊗[F] E) nT * v) = g (v + u) := by
    intro v
    simp only [hg, GlobalTheory.WeilSchrodinger.thetaTr, Darboux.rho]
    rw [schr_dC]
  have h2 : ∀ (r : ratLF F E nS nT) (v : WOF F E nS nT), g (r +ᵥ v) = g v := by
    rintro ⟨r, γ, rfl⟩ v
    obtain ⟨y, z, hyz⟩ := hco (dC E nT * γ)
    have hr : ((incAF F E).toAddMonoidHom.mapMatrix γ : WOF F E nS nT) = γ.map (incAF F E) := rfl
    show GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (dC (AF F ⊗[F] E) nT * (_ + v)) = _
    simp only [hg, GlobalTheory.WeilSchrodinger.thetaTr, Darboux.rho]
    rw [← schr_dC, hr, dC_mul_rat, hyz, GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F B.ψ hB.std.2.1 y z]
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousAdd (WOF F E nS nT) := inferInstanceAs (ContinuousAdd (Fin nT → Fin nS → AF F ⊗[F] E))
  haveI : MeasurableAdd (WOF F E nS nT) :=
    ⟨fun c => (continuous_const_add c).measurable, fun c => (continuous_add_const c).measurable⟩
  haveI : MeasurableConstVAdd (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun r => (continuous_const_add (r : WOF F E nS nT)).measurable⟩
  haveI : VAddInvariantMeasure (ratLF F E nS nT) (WOF F E nS nT) ν :=
    ⟨fun r s _ => measure_preimage_add ν (r : WOF F E nS nT) s⟩
  haveI : VAddCommClass (WOF F E nS nT) (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun a r x => add_left_comm a (r : WOF F E nS nT) x⟩
  haveI : Countable (ratLF F E nS nT) := by
    haveI : Countable E := by
      haveI : FiniteDimensional ℚ E := inferInstance
      exact ((Module.finBasis ℚ E).equivFun).injective.countable
    have : Countable (Matrix (Fin nT) (Fin nS) E) := inferInstanceAs (Countable (Fin nT → Fin nS → E))
    exact (Set.countable_range ((incAF F E).toAddMonoidHom.mapMatrix (m := Fin nT) (n := Fin nS))).to_subtype
  unfold GlobalTheory.LagrTheta.lagrInt
  simp_rw [h1]
  rw [← (measurePreserving_add_right ν u).setIntegral_image_emb (measurableEmbedding_addRight u) g 𝓕]
  have hF' : IsAddFundamentalDomain (ratLF F E nS nT) ((· + u) '' 𝓕) ν := by
    have hs : (· + u) '' 𝓕 = ((u : WOF F E nS nT) +ᵥ 𝓕 : Set (WOF F E nS nT)) := by
      rw [← Set.image_vadd]
      congr 1
      funext v
      exact add_comm v u
    rw [hs]
    exact h𝓕.vadd_of_comm (G' := WOF F E nS nT) (u : WOF F E nS nT)
  exact hF'.setIntegral_eq h𝓕 h2
end
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem isCompact_setOf_fst_mem (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) :
    letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C);
    ∀ K : Set (Qv v ⊗[ℚ] G.C)ˣ, IsCompact K →
      IsCompact {d : Gv G v | (d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 ∈ K} := by
  letI tA : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  intro K hK
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _
  haveI : T2Space (Qv v ⊗[ℚ] G.C) := T2Space.of_injective_continuous (basV G v).equivFun.injective
    (IsModuleTopology.continuous_of_linearMap (basV G v).equivFun.toLinearMap)
  have hst1 : ∀ r : Qv v, (starT G.star (Qv v) (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) r)).unop =
      algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) r := by
    intro r
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, starT_tmul, map_one,
      MulOpposite.unop_one]
  let sL : (Qv v ⊗[ℚ] G.C) →ₗ[Qv v] (Qv v ⊗[ℚ] G.C) :=
    { toFun := fun y => (starT G.star (Qv v) y).unop
      map_add' := fun x y => by simp
      map_smul' := fun r y => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul, MulOpposite.unop_mul]
        rw [hst1]
        exact (Algebra.commutes r _).symm }
  have hsc : Continuous sL := IsModuleTopology.continuous_of_linearMap sL
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_eq_one (K := Qv v) (s := ({()} : Set Unit))
    (v := fun _ : Unit => (1 : Qv v ⊗[ℚ] G.C)) (by
      rw [linearIndepOn_singleton_iff]; exact one_ne_zero)
  have hf1 : f 1 = 1 := hf () rfl
  have hfc : Continuous f := IsModuleTopology.continuous_of_linearMap f
  have key : ∀ d : Gv G v, f (((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : Qv v ⊗[ℚ] G.C) *
      sL ((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : Qv v ⊗[ℚ] G.C)) =
      (((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v) := by
    intro d
    have hd : (((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) *
        (starT G.star (Qv v) ((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : Qv v ⊗[ℚ] G.C)).unop =
        algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) (((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v) := d.2
    show f (_ * (starT G.star (Qv v) _).unop) = _
    rw [hd, Algebra.algebraMap_eq_smul_one, map_smul, hf1, smul_eq_mul, mul_one]
  set L1 : Set (Qv v) := (fun u : (Qv v ⊗[ℚ] G.C)ˣ => f ((u : Qv v ⊗[ℚ] G.C) * sL u)) '' K with hL1
  set L2 : Set (Qv v) := (fun u : (Qv v ⊗[ℚ] G.C)ˣ =>
    f (((u⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * sL ((u⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C))) '' K with hL2
  have hL1c : IsCompact L1 := hK.image (hfc.comp (Units.continuous_val.mul (hsc.comp Units.continuous_val)))
  have hL2c : IsCompact L2 := hK.image (hfc.comp (Units.continuous_coe_inv.mul (hsc.comp Units.continuous_coe_inv)))
  set T : Set (Qv v)ˣ := Units.embedProduct (Qv v) ⁻¹' (L1 ×ˢ (MulOpposite.op '' L2)) with hT
  have hTc : IsCompact T :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hL1c.prod (hL2c.image MulOpposite.continuous_op))
  set Z : Set ((Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ) := {x | ((x.1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) *
      sL ((x.1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
      algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) ((x.2 : (Qv v)ˣ) : Qv v)} with hZ
  have hZc : IsClosed Z := isClosed_eq
    ((Units.continuous_val.comp continuous_fst).mul (hsc.comp (Units.continuous_val.comp continuous_fst)))
    ((continuous_algebraMap (Qv v) (Qv v ⊗[ℚ] G.C)).comp (Units.continuous_val.comp continuous_snd))
  have himg : Subtype.val '' {d : Gv G v | (d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 ∈ K} = (K ×ˢ T) ∩ Z := by
    ext x
    constructor
    · rintro ⟨d, hdK, rfl⟩
      have k2 := key d⁻¹
      simp only [Subgroup.coe_inv, Prod.fst_inv, Prod.snd_inv] at k2
      refine ⟨⟨hdK, ?_⟩, d.2⟩
      show Units.embedProduct (Qv v) _ ∈ L1 ×ˢ (MulOpposite.op '' L2)
      rw [Units.embedProduct_apply]
      exact ⟨⟨_, hdK, key d⟩, ⟨_, ⟨_, hdK, k2⟩, rfl⟩⟩
    · rintro ⟨⟨hK1, -⟩, hZ1⟩
      exact ⟨⟨x, hZ1⟩, hK1, rfl⟩
  exact Subtype.isCompact_iff.2 (himg ▸ (hK.prod hTc).inter_right hZc)

end GlobalTheory.OrbFinAf
end
end

section

noncomputable section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical RestrictedProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

theorem finiteAdeleRingAway_ext {x y : AfP p} (h : ∀ v : AwayP p, AfP.eval v x = AfP.eval v y) : x = y :=
  Subtype.ext (funext h)

theorem exists_afP (s : ∀ v : AwayP p, Qv v)
    (hs : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), s v ∈ v.1.adicCompletionIntegers ℚ) :
    ∃ t : AfP p, ∀ v, AfP.eval v t = s v :=
  ⟨(⟨s, hs⟩ : Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]), fun _ => rfl⟩

variable (G : HTGroup p)

abbrev basA : Module.Basis (Fin (Module.finrank ℚ G.C)) (AfP p) (AfP p ⊗[ℚ] G.C) :=
  Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)

abbrev mapV (v : AwayP p) : AfP p ⊗[ℚ] G.C →ₐ[ℚ] Qv v ⊗[ℚ] G.C :=
  Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)

theorem repr_mapV (v : AwayP p) (z : AfP p ⊗[ℚ] G.C) (i : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (mapV G v z) i = AfP.eval v ((basA G).repr z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    simp [basV, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem eq_of_mapV {z z' : AfP p ⊗[ℚ] G.C} (h : ∀ v, mapV G v z = mapV G v z') : z = z' :=
  (basA G).ext_elem fun i => finiteAdeleRingAway_ext fun v => by rw [← repr_mapV, ← repr_mapV, h v]

theorem exists_of_local (y : ∀ v : AwayP p, Qv v ⊗[ℚ] G.C)
    (hy : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), IsIntV G v (y v)) :
    ∃ z : AfP p ⊗[ℚ] G.C, ∀ v, mapV G v z = y v := by
  choose a ha using fun i : Fin (Module.finrank ℚ G.C) =>
    exists_afP (fun v => (basV G v).repr (y v) i) (hy.mono fun v hv => hv i)
  refine ⟨(basA G).equivFun.symm a, fun v => (basV G v).ext_elem fun i => ?_⟩
  rw [repr_mapV, ← ha i v]
  congr 1
  exact congrFun ((basA G).equivFun.apply_symm_apply a) i

theorem mapV_star (v : AwayP p) (z : AfP p ⊗[ℚ] G.C) :
    (starT G.star (Qv v) (mapV G v z)).unop = mapV G v (starT G.star (AfP p) z).unop := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      starT_tmul]
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]

theorem mapV_algebraMap (v : AwayP p) (s : AfP p) :
    mapV G v (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s) = algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) (AfP.eval v s) := by
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem exists_glue : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (h : ∀ v : AwayP p, Gv G v),
    (∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), h v ∈ IntV G v) → ∃ g : G.GAf, ∀ v, piV G v g = h v := by
  intro p _ G h hint
  obtain ⟨X, hX⟩ := exists_of_local G
    (fun v => ((((h v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ)) : Qv v ⊗[ℚ] G.C))
    (hint.mono fun v hv => hv.1)
  obtain ⟨Y, hY⟩ := exists_of_local G
    (fun v => ((((h v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C))
    (hint.mono fun v hv => hv.2.1)
  obtain ⟨s, hs⟩ := exists_afP (fun v => (((h v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v))
    (hint.mono fun v hv => hv.2.2.1)
  obtain ⟨s', hs'⟩ := exists_afP (fun v => ((((h v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2)⁻¹ : (Qv v)ˣ) : Qv v))
    (hint.mono fun v hv => hv.2.2.2)
  have hXY : X * Y = 1 := eq_of_mapV G fun v => by rw [map_mul, hX, hY, map_one, Units.mul_inv]
  have hYX : Y * X = 1 := eq_of_mapV G fun v => by rw [map_mul, hX, hY, map_one, Units.inv_mul]
  have hss : s * s' = 1 := finiteAdeleRingAway_ext fun v => by rw [map_mul, hs, hs', map_one, Units.mul_inv]
  have hss' : s' * s = 1 := finiteAdeleRingAway_ext fun v => by rw [map_mul, hs, hs', map_one, Units.inv_mul]
  let U : (AfP p ⊗[ℚ] G.C)ˣ := ⟨X, Y, hXY, hYX⟩
  let c : (AfP p)ˣ := ⟨s, s', hss, hss'⟩
  have hmem : (U, c) ∈ UPts G.star (AfP p) := by
    show X * (starT G.star (AfP p) X).unop = algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s
    refine eq_of_mapV G fun v => ?_
    rw [map_mul, ← mapV_star, hX, mapV_algebraMap, hs]
    exact (h v).2
  refine ⟨⟨(U, c), hmem⟩, fun v => ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    exact hX v
  · apply Units.ext
    exact hs v

end GlobalTheory.OrbFinAf
end
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem rat_valuation_le_one_eventually (x : ℚ) :
    ∀ᶠ w : HeightOneSpectrum ℤ in Filter.cofinite, w.valuation ℚ x ≤ 1 := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℤ) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hI : Ideal.span {b} ≠ (0 : Ideal ℤ) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hd
  apply hw
  have h1 : w.valuation ℚ (algebraMap ℤ ℚ b) = 1 :=
    le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hd ((w.valuation_lt_one_iff_dvd b).1 h))
  rw [map_div₀, h1, div_one]
  exact w.valuation_le_one a

variable {p : ℕ} [Fact p.Prime]

theorem rat_mem_integers_eventually (x : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), algebraMap ℚ (Qv v) x ∈ v.1.adicCompletionIntegers ℚ := by
  have h := (Function.Injective.tendsto_cofinite (f := fun v : AwayP p => v.1) Subtype.val_injective).eventually
    (rat_valuation_le_one_eventually x)
  filter_upwards [h] with v hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 x).trans_le hv

def starLin (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] : (R ⊗[ℚ] G.C) →ₗ[R] (R ⊗[ℚ] G.C) where
  toFun a := (starT G.star R a).unop
  map_add' x y := by rw [map_add (f := _), MulOpposite.unop_add]
  map_smul' r x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s y =>
      rw [TensorProduct.smul_tmul', starT_tmul, starT_tmul, TensorProduct.smul_tmul', RingHom.id_apply]
    | add x y hx hy =>
      rw [smul_add, map_add (f := _), MulOpposite.unop_add, hx, hy, map_add (f := _), MulOpposite.unop_add, smul_add]

theorem starLin_apply (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (a : R ⊗[ℚ] G.C) :
    starLin G R a = (starT G.star R a).unop := rfl

theorem isIntV_star_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a : Qv v ⊗[ℚ] G.C, IsIntV G v a →
      IsIntV G v (starT G.star (Qv v) a).unop := by
  intro p _ G
  have hs : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      ∀ ij : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C),
        algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr (G.star (Module.finBasis ℚ G.C ij.2)).unop ij.1)
          ∈ v.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun ij => rat_mem_integers_eventually _
  filter_upwards [hs] with v hv a ha i

  rw [← starLin_apply, ← (basV G v).sum_repr a, map_sum, map_sum, Finsupp.finsetSum_apply]
  refine sum_mem fun j _ => ?_
  rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  refine mul_mem (ha j) ?_
  have hb : basV G v j = (1 : Qv v) ⊗ₜ Module.finBasis ℚ G.C j := by
    simp [basV, Algebra.TensorProduct.basis_apply]
  rw [hb, starLin_apply, starT_tmul, basV, Algebra.TensorProduct.basis_repr_tmul, one_smul,
    Finsupp.mapRange_apply]
  exact hv (i, j)

end GlobalTheory.OrbFinAf
end
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.OrbFinAfFixed

theorem rat_eventually_int (p : ℕ) (q : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) q ∈ v.1.adicCompletionIntegers ℚ := by
  have h : ∀ᶠ w in (Filter.cofinite : Filter (HeightOneSpectrum ℤ)),
      algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q w ∈ w.adicCompletionIntegers ℚ :=
    (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2
  have h2 : ∀ᶠ w in (Filter.cofinite : Filter (HeightOneSpectrum ℤ)),
      algebraMap ℚ (w.adicCompletion ℚ) q ∈ w.adicCompletionIntegers ℚ :=
    h.mono fun w hw => by rwa [FiniteAdeleRing.algebraMap_apply] at hw
  exact (Subtype.val_injective.tendsto_cofinite).eventually h2

theorem basV_repr_one_tmul (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (c : G.C) (i) :
    (basV G v).repr ((1 : Qv v) ⊗ₜ[ℚ] c) i = algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr c i) := by
  simp [basV, Algebra.TensorProduct.basis_repr_tmul]

theorem isIntV_one_tmul_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (c : G.C),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] c) := by
  intro p _ G c
  have h : ∀ i, ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr c i) ∈ v.1.adicCompletionIntegers ℚ :=
    fun i => rat_eventually_int p _
  refine (Filter.eventually_all.2 h).mono fun v hv i => ?_
  rw [basV_repr_one_tmul]
  exact hv i

end GlobalTheory.OrbFinAfFixed
end
