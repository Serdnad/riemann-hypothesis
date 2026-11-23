module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle374
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle491
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle375
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorJacquetEigenLeft
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle377
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle116
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle376
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle367
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

theorem _root_.GlobalTheory.T.exists_nontrivial_derivative : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k m) V), IsSmooth τ → Nontrivial V → ∃ n ≤ m, Nontrivial (TwJacquet τ (derUnipM k m n) (derCharM k ψ m n)) := by
  first | exact @GlobalTheory.CompanionTheory.BZMirDer.NonZero.exists_derivative_nontrivial | exact GlobalTheory.CompanionTheory.BZMirDer.NonZero.exists_derivative_nontrivial | (intros; apply GlobalTheory.CompanionTheory.BZMirDer.NonZero.exists_derivative_nontrivial <;> assumption)
end

section

noncomputable section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SegScalar

theorem absPow_natCast (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) : absPow k (n : ℂ) = absPow k 1 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, absPow_add, ih, pow_succ]

theorem absPow_pow_comm (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a d : ℕ) (t : kˣ) :
    (((absPow k (a : ℂ) ^ d) t : ℂˣ) : ℂ) = ((absPow k (d : ℂ) t : ℂˣ) : ℂ) ^ a := by
  rw [absPow_natCast, absPow_natCast, ← pow_mul, mul_comm a d, MonoidHom.pow_apply, MonoidHom.pow_apply, pow_mul,
    Units.val_pow_eq_pow_val]

theorem prod_mul_pow (l : ℕ) (c e : ℂ) :
    ∏ a : Fin l, (c * e ^ (a : ℕ)) = c ^ l * e ^ (l * (l - 1) / 2) := by
  rw [Fin.prod_univ_eq_prod_range (fun a => c * e ^ a) l, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range, Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]

theorem scalarBy_of_isLSeg (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Γ : Segment k) (y : IrrGL (k := k)) : IsLSeg Γ y.rep → ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy Γ.first t c →
      Zl.ScalarBy y t (c ^ Γ.len * ((absPow k (Γ.first.1 : ℂ) t : ℂˣ) : ℂ) ^ (Γ.len * (Γ.len - 1) / 2)) := by
  intro hL t c hc
  obtain ⟨hd, -, f, hf, -⟩ := hL
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar Γ.first.2.rep.smooth Γ.first.2.rep.irr
  have hωc : ((ω t : ℂˣ) : ℂ) = c := by
    haveI := Model.nontrivial_of_isIrreducible Γ.first.2.rep.irr
    obtain ⟨w, hw⟩ := exists_ne (0 : Γ.first.2.rep.V)
    have h1 : ((ω t : ℂˣ) : ℂ) • w = c • w := (hω t w).symm.trans (hc w)
    exact smul_left_injective ℂ hw h1
  have hterm : ∀ a : Fin Γ.len, HasCentralChar (Γ.term a).rep (ω * absPow k ((a : ℕ) : ℂ) ^ Γ.first.1) :=
    fun a => UnitaryOrder.hasCentralChar_nu Γ.first hω ((a : ℕ) : ℂ)
  have hsc : ∀ v, y.rep (Matrix.GeneralLinearGroup.scalar (Fin y.1) t) v =
      (∏ a : Fin Γ.len, ((((ω * absPow k ((a : ℕ) : ℂ) ^ Γ.first.1) t : ℂˣ)) : ℂ)) • v := by
    intro v
    obtain ⟨w, rfl⟩ := hf v
    have h1 := GlobalTheory.BoundaryMaps.multiProd_scalar (stdBlocks (fun a => (Γ.term a).1) hd)
      (fun a => (Γ.term a).rep) _ hterm t w
    rw [← f.isIntertwining]
    exact (congrArg f h1).trans (map_smul f _ _)
  have h2 : ∏ a : Fin Γ.len, ((((ω * absPow k ((a : ℕ) : ℂ) ^ Γ.first.1) t : ℂˣ)) : ℂ) =
      c ^ Γ.len * ((absPow k (Γ.first.1 : ℂ) t : ℂˣ) : ℂ) ^ (Γ.len * (Γ.len - 1) / 2) := by
    rw [← prod_mul_pow]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [MonoidHom.mul_apply, Units.val_mul, hωc, absPow_pow_comm]
  rw [← h2]
  exact hsc

end GlobalTheory.CompanionTheory.SegScalar

end
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.double_coset_volume_le : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)), μ.IsHaarMeasure → ∀ m : ℕ, 1 ≤ m → ∀ (p1 p2 : GL (Fin N) k), p1 ∈ KO k (Fin N) → p2 ∈ KO k (Fin N) → ∀ g : Fin (N - 1) → ℕ, μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {h | ∃ x ∈ Zls.Km k N m, ∃ y ∈ Zls.Km k N m, h = p1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p2}) ≤ (Nat.card 𝓀[k] : ENNReal) ^ (∑ j : Fin (N - 1), g j * (((j : ℕ) + 1) * (N - ((j : ℕ) + 1)))) * μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k))) := by
  first | exact @GlobalTheory.CompanionTheory.KmVolume.measure_translated_doubleCoset_le | exact GlobalTheory.CompanionTheory.KmVolume.measure_translated_doubleCoset_le | (intros; apply GlobalTheory.CompanionTheory.KmVolume.measure_translated_doubleCoset_le <;> assumption)
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.matrix_coefficient_hecke_decay : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → IsAdmissible π → Zls.HeckeSpectral π → ∀ m : ℕ, 1 ≤ m → ∀ v ∈ fixed π (Zls.Km k N m), ∀ l : Module.Dual ℂ V, (∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l) → ∃ (C : ℝ) (ρ : Fin (N - 1) → ℝ), (∀ j, 0 ≤ ρ j) ∧ (∀ j : Fin (N - 1), (Nat.card 𝓀[k] : ℝ) ^ (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) * ρ j ^ 2 < 1) ∧ ∀ g : Fin (N - 1) → ℕ, ‖l (π (Zls.diagPow k N (Zls.lamOf g)) v)‖ ≤ C * ∏ j, ρ j ^ g j := by
  first | exact @GlobalTheory.CompanionTheory.CoeffBound.coeff_bound | exact GlobalTheory.CompanionTheory.CoeffBound.coeff_bound | (intros; apply GlobalTheory.CompanionTheory.CoeffBound.coeff_bound <;> assumption)
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.hecke_operator_jacquet_eigen_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ m : ℕ, 1 ≤ m → ∀ (d : Fin 2 → ℕ) (hd : ∑ a, d a = N), 0 < d 0 → 0 < d 1 → ∀ T : Module.End ℂ (fixed π (Zls.Km k N m)), Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.omegaVec N (d 0))) T → ∀ v : fixed π (Zls.Km k N m), (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) = 0 → ∃ r : ℕ, (T ^ r) v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HeckeNilp.hecke_nilpotent | exact GlobalTheory.CompanionTheory.HeckeNilp.hecke_nilpotent | (intros; apply GlobalTheory.CompanionTheory.HeckeNilp.hecke_nilpotent <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.jacquet_multiplicity_drop_zero_blocks : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' N : ℕ} (y : Fin r → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → ∀ (hd' : ∑ a, (y (o a)).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), jm y hd π = jm (fun a => y (o a)) hd' π := by
  first | exact @GlobalTheory.CompanionTheory.FineProd.JmDrop.jm_drop | exact GlobalTheory.CompanionTheory.FineProd.JmDrop.jm_drop | (intros; apply GlobalTheory.CompanionTheory.FineProd.JmDrop.jm_drop <;> assumption)
end

section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Casselman

theorem exists_fin_coset_reps_of_isDom : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), ∀ t : D.T, D.IsDom t → ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → G,
      (∀ i, x i ∈ D.J ⊓ D.N) ∧
        ∀ y ∈ D.J, ∃! i, (x i)⁻¹ * y ∈ D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom := by
  intro G _ _ _ D t ht
  exact GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps G D.J
    (D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom) (D.J ⊓ D.N)
    D.isCompact_J (GlobalTheory.CompanionTheory.TopGroup.inter_conj_isOpen G D.J D.isOpen_J (t : G)) inf_le_left inf_le_left
    (exists_mem_inf_conj_of_isDom G D t ht)

end GlobalTheory.CompanionTheory.Casselman
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL PositivityTheory.Rg.Cz
open scoped Classical

namespace GlobalTheory.CompanionTheory.FrameCasimir

theorem sum_embeddings {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : Type} [AddCommMonoid N]
    (f : (E →+* ℂ) → N) :
    ∑ τ, f τ = ∑ v : InfinitePlace E, (f v.embedding + f (ComplexEmbedding.conjugate v.embedding)) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun τ : E →+* ℂ => InfinitePlace.mk τ) f]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hne : v.embedding ≠ ComplexEmbedding.conjugate v.embedding := by
    intro h
    have hc : v.IsComplex := IsTotallyComplex.isComplex v
    exact (InfinitePlace.isComplex_iff.1 hc) (ComplexEmbedding.isReal_iff.2 h.symm)
  have hf : (Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = v) =
      {v.embedding, ComplexEmbedding.conjugate v.embedding} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      rcases InfinitePlace.embedding_mk_eq τ with h | h
      · exact Or.inl h.symm
      · right
        rw [h]
        exact (star_star τ).symm
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding v
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  rw [hf, Finset.sum_pair hne]

theorem atEmb_embedding {E : Type} [Field E] (v : InfinitePlace E) (z : ℂ) :
    atEmb v.embedding z = (Pi.single v z : Cinf E) := by
  unfold atEmb
  rw [if_pos (by rw [InfinitePlace.mk_embedding])]
  congr 1 <;> simp

theorem map_single_atEmb {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {N : Type} [AddCommGroup N]
    [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (φ : Lie E a →ₗ[ℝ] N) (τ : E →+* ℂ) (i j : Fin a) (z : ℂ) :
    φ (toL (Matrix.single i j (atEmb τ z))) =
      z • cx τ φ i j + starRingEnd ℂ z • cx (ComplexEmbedding.conjugate τ) φ i j := by
  let L : Cinf E →ₗ[ℝ] N :=
    { toFun := fun x => φ (toL (Matrix.single i j x))
      map_add' := fun x y => by
        rw [Matrix.single_add]
        exact φ.map_add _ _
      map_smul' := fun r x => by
        rw [← Matrix.smul_single]
        exact φ.map_smul r _ }
  have hL : ∀ x, φ (toL (Matrix.single i j x)) = L x := fun _ => rfl
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  rw [hL, atEmb_eq, map_add (f := _), map_smul, map_smul]
  simp only [cx, hL, atEmb_conj, map_one, Complex.conj_I, e, map_neg]
  have h1 := Complex.add_conj z
  have h2 := Complex.sub_conj z
  push_cast at h1 h2
  match_scalars
  · simp only [Complex.coe_algebraMap]; linear_combination (-1 / 2 : ℂ) * h1
  · simp only [Complex.coe_algebraMap]; linear_combination (Complex.I / 2 : ℂ) * h2 + z.im * Complex.I_mul_I

theorem alg_sq {R : Type} [Ring R] [Algebra ℂ R] (u w : R) :
    (u + w) * (u + w) - (Complex.I • u - Complex.I • w) * (Complex.I • u - Complex.I • w) =
      (2 : ℂ) • (u * u) + (2 : ℂ) • (w * w) := by
  rw [← smul_sub, smul_mul_smul_comm, Complex.I_mul_I]
  simp only [mul_add, add_mul, sub_mul, mul_sub]
  module

theorem alg_sum {R : Type} [Ring R] [Algebra ℂ R] {a : ℕ} (P : Fin a → Fin a → R) (c d : ℂ)
    (h0 : c * c + d * d = 0) (h1 : 2 * (c * d) = 1) :
    ∑ i, ∑ j, (c • P i j + d • P j i) * (c • P i j + d • P j i) = ∑ i, ∑ j, P i j * P j i := by
  have e : ∀ i j, (c • P i j + d • P j i) * (c • P i j + d • P j i) =
      (c * c) • (P i j * P i j) + (c * d) • (P i j * P j i) + (c * d) • (P j i * P i j) + (d * d) • (P j i * P j i) := by
    intro i j
    simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm]
    module
  simp only [e, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [Finset.sum_comm (f := fun i j => P j i * P i j), Finset.sum_comm (f := fun i j => P j i * P j i)]
  generalize (∑ i, ∑ j, P i j * P i j) = S
  generalize (∑ i, ∑ j, P i j * P j i) = T
  calc (c * c) • S + (c * d) • T + (c * d) • T + (d * d) • S = (c * c + d * d) • S + (2 * (c * d)) • T := by module
    _ = T := by rw [h0, h1, zero_smul, one_smul, zero_add]

theorem iM_single {E : Type} [Field E] {a : ℕ} (v : InfinitePlace E) (i j : Fin a) (z : ℂ) :
    iM (Matrix.single i j (Pi.single v z : Cinf E)) = Matrix.single i j (Pi.single v (Complex.I * z) : Cinf E) := by
  unfold iM
  rw [Matrix.smul_single]
  congr 1
  funext w
  by_cases hw : w = v
  · subst hw
    simp
  · simp [Pi.single_eq_of_ne hw]

theorem fr_val {E : Type} [Field E] {a : ℕ} (v : InfinitePlace E) (i j : Fin a) :
    (fr (v, i, j) : Herm E a).1 = Matrix.single i j (Pi.single v ((1 + Complex.I) / 2) : Cinf E) +
      Matrix.single j i (Pi.single v (starRingEnd ℂ ((1 + Complex.I) / 2)) : Cinf E) := by
  change frU (v, i, j) + star (frU (v, i, j)) = _
  congr 1
  unfold frU
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single]
  congr 1
  funext w
  by_cases hw : w = v
  · subst hw
    simp only [Pi.star_apply, Pi.single_eq_same, Complex.star_def]
  · simp [Pi.single_eq_of_ne hw]

theorem frameCas : FrameCas := by
  intro E _ _ _ a M _ _ _ _ φ
  set c : ℂ := (1 + Complex.I) / 2 with hc
  have hc0 : c * c + starRingEnd ℂ c * starRingEnd ℂ c = 0 := by
    simp only [hc, map_div₀, map_add (f := _), map_one, Complex.conj_I, map_ofNat]
    ring_nf
    simp
  have hc1 : 2 * (c * starRingEnd ℂ c) = 1 := by
    simp only [hc, map_div₀, map_add (f := _), map_one, Complex.conj_I, map_ofNat]
    ring_nf
    simp
    norm_num
  let P : InfinitePlace E → Fin a → Fin a → Module.End ℂ M := fun v => cx v.embedding φ
  let Q : InfinitePlace E → Fin a → Fin a → Module.End ℂ M := fun v => cx (ComplexEmbedding.conjugate v.embedding) φ
  let u : InfinitePlace E → Fin a → Fin a → Module.End ℂ M := fun v i j => c • P v i j + starRingEnd ℂ c • P v j i
  let w : InfinitePlace E → Fin a → Fin a → Module.End ℂ M := fun v i j => starRingEnd ℂ c • Q v i j + c • Q v j i
  have hs : ∀ v i j z, φ (toL (Matrix.single i j (Pi.single v z : Cinf E))) = z • P v i j + starRingEnd ℂ z • Q v i j := by
    intro v i j z
    rw [← atEmb_embedding]
    exact map_single_atEmb φ v.embedding i j z
  have hadd : ∀ A B : Matrix (Fin a) (Fin a) (Cinf E), φ (toL (A + B)) = φ (toL A) + φ (toL B) :=
    fun A B => φ.map_add (toL A) (toL B)
  have hfr : ∀ v i j, φ (toL (fr (v, i, j) : Herm E a).1) = u v i j + w v i j := by
    intro v i j
    rw [fr_val, hadd, hs, hs, Complex.conj_conj]
    simp only [u, w]
    abel
  have hiM : ∀ v i j, φ (toL (iM (fr (v, i, j) : Herm E a).1)) = Complex.I • u v i j - Complex.I • w v i j := by
    intro v i j
    have e : iM ((fr (v, i, j) : Herm E a).1) = iM (Matrix.single i j (Pi.single v c : Cinf E)) +
        iM (Matrix.single j i (Pi.single v (starRingEnd ℂ c) : Cinf E)) := by
      rw [fr_val]
      exact smul_add _ _ _
    rw [e, iM_single, iM_single, hadd, hs, hs]
    simp only [u, w, map_mul, Complex.conj_I, Complex.conj_conj]
    module
  have L1 : ∑ k : InfinitePlace E × Fin a × Fin a, φ (toL (fr k : Herm E a).1) * φ (toL (fr k : Herm E a).1) =
      ∑ v, ∑ i, ∑ j, (u v i j + w v i j) * (u v i j + w v i j) := by
    simp only [Fintype.sum_prod_type, hfr]
  have L2 : ∑ k : InfinitePlace E × Fin a × Fin a, φ (toL (iM (fr k : Herm E a).1)) * φ (toL (iM (fr k : Herm E a).1)) =
      ∑ v, ∑ i, ∑ j, (Complex.I • u v i j - Complex.I • w v i j) * (Complex.I • u v i j - Complex.I • w v i j) := by
    simp only [Fintype.sum_prod_type, hiM]
  rw [L1, L2, sum_embeddings, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hu : ∑ i, ∑ j, u v i j * u v i j = ∑ i, ∑ j, P v i j * P v j i :=
    alg_sum (P v) c (starRingEnd ℂ c) hc0 hc1
  have hw : ∑ i, ∑ j, w v i j * w v i j = ∑ i, ∑ j, Q v i j * Q v j i :=
    alg_sum (Q v) (starRingEnd ℂ c) c (by rw [add_comm]; exact hc0) (by rw [mul_comm (starRingEnd ℂ c)]; exact hc1)
  change _ = (2 : ℂ) • (∑ i, ∑ j, P v i j * P v j i + ∑ i, ∑ j, Q v i j * Q v j i)
  rw [← hu, ← hw, smul_add, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => alg_sq _ _

end GlobalTheory.CompanionTheory.FrameCasimir
end
end

section

namespace GlobalTheory.CompanionTheory.GKHarmonic

theorem harmonic : PositivityTheory.Rg.Cz.Harmonic := by
  intro E _ _ a M _ _ _ _ κ L hd q ω hc h0
  cases q with
  | zero => exact Or.inl ⟨ω, hc, hd 0 ω hc, h0⟩
  | succ q => exact Or.inr ⟨q, ω, hc, hd _ ω hc, fun η hη h => h0 (h.symm.trans (hd q η hη))⟩

end GlobalTheory.CompanionTheory.GKHarmonic
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

theorem _root_.GlobalTheory.T.phi_product_rank_zero_trivial : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (ρ : GRep k (m + 1)) (τ : MRep k 0) (h : (m + 1) + 0 = (m + 0) + 1), IsSmooth ρ.ρ → IsSmooth τ.ρ → Subsingleton (phiN ψ (mcast h (prodGPn ρ τ))).V := by
  first | exact @GlobalTheory.CompanionTheory.PhiGpZero.phiN_prodGPn_zero | exact GlobalTheory.CompanionTheory.PhiGpZero.phiN_prodGPn_zero | (intros; apply GlobalTheory.CompanionTheory.PhiGpZero.phiN_prodGPn_zero <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.LbElem.ConjMonomial

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdBlocks_ones (N : ℕ) (a : Fin N) (i : Fin (ones N a)) :
    stdBlocks (ones N) (sum_ones N) ⟨a, i⟩ = a := by
  apply Fin.ext
  rw [stdBlocks_val]
  have hi : (i : ℕ) = 0 := by
    have := i.2
    simp only [ones] at this
    omega
  simp [ones, hi]

theorem tor_offDiag {N : ℕ} {x : GL (Fin N) k} (hx : x ∈ Tor k N) {i j : Fin N} (hij : i ≠ j) :
    (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  obtain ⟨s, rfl⟩ := hx
  have h : (leviEmb k (stdBlocks (ones N) (sum_ones N)) s : Matrix (Fin N) (Fin N) k)
      (stdBlocks (ones N) (sum_ones N) ⟨i, ⟨0, by simp [ones]⟩⟩)
      (stdBlocks (ones N) (sum_ones N) ⟨j, ⟨0, by simp [ones]⟩⟩) = 0 := by
    classical
    simp [leviEmb, Matrix.blockDiagonal'_apply, hij]
  rwa [stdBlocks_ones, stdBlocks_ones] at h

theorem mem_tor_of_offDiag {N : ℕ} (x : GL (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0) : x ∈ Tor k N := by
  have hd : ∀ i, (x : Matrix (Fin N) (Fin N) k) i i ≠ 0 := by
    intro i h0
    have h1 := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i i) (mul_inv_cancel x)
    simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, Matrix.one_apply_eq] at h1
    rw [Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro l _
      by_cases hl : i = l
      · subst hl
        rw [h0, zero_mul]
      · rw [h i l hl, zero_mul]
  refine ⟨fun a => Units.map (algebraMap k (Matrix (Fin (ones N a)) (Fin (ones N a)) k)).toMonoidHom
    (Units.mk0 _ (hd a)), ?_⟩

  apply Units.ext
  ext i j
  by_cases hij : i = j
  · subst hij
    have h1 : (leviEmb k (stdBlocks (ones N) (sum_ones N))
        (fun a => Units.map (algebraMap k (Matrix (Fin (ones N a)) (Fin (ones N a)) k)).toMonoidHom
          (Units.mk0 _ (hd a))) : Matrix (Fin N) (Fin N) k)
        (stdBlocks (ones N) (sum_ones N) ⟨i, ⟨0, by simp [ones]⟩⟩)
        (stdBlocks (ones N) (sum_ones N) ⟨i, ⟨0, by simp [ones]⟩⟩) = (x : Matrix (Fin N) (Fin N) k) i i := by
      simp [leviEmb, Matrix.blockDiagonal'_apply_eq, Matrix.algebraMap_matrix_apply]
    rw [stdBlocks_ones] at h1
    rw [h1]
  · have h1 : (leviEmb k (stdBlocks (ones N) (sum_ones N))
        (fun a => Units.map (algebraMap k (Matrix (Fin (ones N a)) (Fin (ones N a)) k)).toMonoidHom
          (Units.mk0 _ (hd a))) : Matrix (Fin N) (Fin N) k)
        (stdBlocks (ones N) (sum_ones N) ⟨i, ⟨0, by simp [ones]⟩⟩)
        (stdBlocks (ones N) (sum_ones N) ⟨j, ⟨0, by simp [ones]⟩⟩) = 0 := by
      classical
      simp [leviEmb, Matrix.blockDiagonal'_apply, hij]
    rw [stdBlocks_ones, stdBlocks_ones] at h1
    rw [h i j hij]
    exact h1

end GlobalTheory.CompanionTheory.LbElem.ConjMonomial

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

theorem _root_.GlobalTheory.T.modulus_trivial_on_levi_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsCompact (J : Set (GL (Fin N) k)) → ∀ x ∈ KM k N J d hd, deltaHalf k (Bl d) x = 1 := by
  first | exact @GlobalTheory.CompanionTheory.HalfModCompact.deltaHalf_eq_one_of_mem_KM | exact GlobalTheory.CompanionTheory.HalfModCompact.deltaHalf_eq_one_of_mem_KM | (intros; apply GlobalTheory.CompanionTheory.HalfModCompact.deltaHalf_eq_one_of_mem_KM <;> assumption)
end
