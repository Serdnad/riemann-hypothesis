module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff
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
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.killsMat_of :
    UpperTheory.Gal.W2.KillsMat := by
  intro F _ _ O _ bar g ρ a D P₀ hP ga H hH q
  have hpow : ∀ (i : ℕ) (x : D.La), P₀ ((ga ^ i) x) = (H ^ i) *ᵥ P₀ x := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, ih, hH, Matrix.mulVec_mulVec, pow_succ]
  have hsum : ∀ x, P₀ (q.sum fun i b => a b • (ga ^ i) x) =
      (q.sum fun i b => ρ (a b) * H ^ i) *ᵥ P₀ x := by
    intro x

    simp only [Polynomial.sum_def, map_sum, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hP.1, hpow, Matrix.mulVec_mulVec]
  constructor
  · intro hk
    have hz : ∀ x, (q.sum fun i b => ρ (a b) * H ^ i) *ᵥ P₀ x = 0 := fun x => by
      rw [← hsum, hk x, map_zero]
    have hlin : (Matrix.mulVecLin (q.sum fun i b => ρ (a b) * H ^ i)).restrictScalars ℝ = 0 :=
      GlobalTheory.PerCoordU.ext_per hP fun x => by simpa using hz x
    have hv : ∀ v, (q.sum fun i b => ρ (a b) * H ^ i) *ᵥ v = 0 := fun v => by
      simpa using LinearMap.congr_fun hlin v
    exact Matrix.mulVec_injective (funext fun v => by rw [hv v, Matrix.zero_mulVec])
  · intro h x
    apply hP.2.1
    rw [hsum, h, map_zero, Matrix.zero_mulVec]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.traceDual_of :
    UpperTheory.Gal.W2.TraceDual := by
  intro F _ _ s hs
  classical
  let e := NumberField.RingOfIntegers.basis F
  choose m hm using fun k => hs (e k)
  let L : F →ₗ[ℚ] ℚ := (NumberField.integralBasis F).constr ℚ (fun k => (m k : ℚ))
  let D := (Algebra.traceForm ℚ F).toDual (traceForm_nondegenerate ℚ F)
  let b : F := D.symm L
  have hb : ∀ x : F, Algebra.trace ℚ F (b * x) = L x := by
    intro x
    have h := LinearMap.congr_fun (D.apply_symm_apply L) x
    rw [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] at h
    exact h
  have htr : ∀ x : F, algebraMap ℚ ℂ (Algebra.trace ℚ F x) = ∑ τ : F →+* ℂ, τ x := by
    intro x
    rw [trace_eq_sum_embeddings ℂ]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ).symm _ _ (fun σ => rfl)
  have hk : ∀ k, ∑ τ : F →+* ℂ, τ (e k : F) * (τ b - s τ) = 0 := by
    intro k
    simp only [mul_sub, Finset.sum_sub_distrib, ← map_mul]
    rw [hm k, ← htr, mul_comm (e k : F) b, hb, sub_eq_zero]
    have he : (e k : F) = NumberField.integralBasis F k := by
      rw [NumberField.integralBasis_apply]
    rw [he, Module.Basis.constr_basis]
    simp
  let P : ((F →+* ℂ) → ℂ) →ₗ[ℂ] ℂ := ∑ τ, (τ b - s τ) • LinearMap.proj τ
  have hP : P = 0 := by
    apply (NumberField.canonicalEmbedding.latticeBasis F).ext
    intro k
    simp only [P, NumberField.canonicalEmbedding.latticeBasis_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.proj_apply,
      NumberField.canonicalEmbedding.apply_at, smul_eq_mul, LinearMap.zero_apply]
    rw [← hk k]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [mul_comm, NumberField.integralBasis_apply]
  refine ⟨b, fun τ => ?_⟩
  have h := LinearMap.congr_fun hP (Pi.single τ 1)
  simp [P, Pi.single_apply] at h
  rw [sub_eq_zero] at h
  exact h.symm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private lemma realTrace_toLin (g : ℕ) (H : Matrix (Fin g) (Fin g) ℂ) :
    ((LinearMap.trace ℝ (Fin g → ℂ) ((Matrix.toLin' H).restrictScalars ℝ) : ℝ) : ℂ) =
      H.trace + (starRingEnd ℂ) H.trace := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (Complex.basisOneI.smulTower' (Pi.basisFun ℂ (Fin g))),
    LinearMap.restrictScalars_toMatrix]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Matrix.comp_apply, Matrix.map_apply]
  have hb : ∀ z : ℂ, ∑ a, Algebra.leftMulMatrix Complex.basisOneI z a a = 2 * z.re := by
    intro z
    rw [← Algebra.trace_complex_apply, Algebra.trace_eq_matrix_trace Complex.basisOneI]
    rfl

  simp only [hb, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', map_sum, ← Finset.sum_add_distrib,
  Complex.add_conj]
  push_cast
  rfl

private lemma trace_of_basis (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] (g : ℕ)
    (P : L →+ (Fin g → ℂ)) (hinj : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (f : L →ₗ[ℤ] L) (H : Matrix (Fin g) (Fin g) ℂ) (hf : ∀ x, P (f x) = H *ᵥ P x) :
    ((LinearMap.trace ℤ L f : ℤ) : ℝ) =
      LinearMap.trace ℝ (Fin g → ℂ) ((Matrix.toLin' H).restrictScalars ℝ) := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let Lsub : Submodule ℤ (Fin g → ℂ) := LinearMap.range P.toIntLinearMap
  have hcar : (Lsub : Set (Fin g → ℂ)) = Set.range P := LinearMap.coe_range _
  haveI : DiscreteTopology Lsub := hd
  haveI : IsZLattice ℝ Lsub := ⟨by rw [hcar]; exact hs⟩
  let e : L ≃ₗ[ℤ] Lsub := LinearEquiv.ofInjective P.toIntLinearMap hinj
  let bV := (b.map e).ofZLatticeBasis ℝ Lsub
  have hbV : ∀ i, bV i = P (b i) := fun i => by
    simp [bV, e]
    rfl
  rw [LinearMap.trace_eq_matrix_trace ℤ b, LinearMap.trace_eq_matrix_trace ℝ bV]
  have hM : LinearMap.toMatrix bV bV ((Matrix.toLin' H).restrictScalars ℝ) =
      (LinearMap.toMatrix b b f).map (Int.cast : ℤ → ℝ) := by
    ext i j
    have hsum : (Matrix.toLin' H).restrictScalars ℝ (bV j) =
        ∑ k, ((b.repr (f (b j)) k : ℤ) : ℝ) • bV k := by
      rw [LinearMap.restrictScalars_apply, hbV, Matrix.toLin'_apply, ← hf]
      conv_lhs => rw [← b.sum_repr (f (b j))]

      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, hbV, Int.cast_smul_eq_zsmul]
    rw [LinearMap.toMatrix_apply, hsum, Matrix.map_apply, LinearMap.toMatrix_apply, bV.repr_sum_self]
  rw [hM, Matrix.trace, Matrix.trace]
  simp

theorem UpperTheory.Gal.W2.traceLat_of :
    UpperTheory.Gal.W2.TraceLat := by
  intro L _ _ _ g P hinj hd hs f H hf
  rw [← realTrace_toLin, ← trace_of_basis L g P hinj hd hs f H hf]
  push_cast
  rfl
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private lemma exists_fin_map (n : ℕ) (s : Multiset ℂ) (h : Multiset.card s = n) :
    ∃ r : Fin n → ℂ, (Finset.univ : Finset (Fin n)).val.map r = s := by
  induction n generalizing s with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    rw [Multiset.card_eq_zero] at h
    simp [h]
  | succ n ih =>
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.1 (by omega : 0 < Multiset.card s)
    obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
    obtain ⟨r, hr⟩ := ih t (by simpa using h)
    refine ⟨Fin.cons a r, ?_⟩
    rw [Fin.univ_val_map, List.ofFn_succ, ← Multiset.cons_coe]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← Fin.univ_val_map, hr]

private lemma newton_step (n k : ℕ) (r : Fin n → ℂ) :
    (k : ℂ) * ((Finset.univ : Finset (Fin n)).val.map r).esymm k =
      (-1) ^ (k + 1) * ∑ a ∈ (Finset.HasAntidiagonal.antidiagonal k).filter (fun a => a.1 < k),
        (-1) ^ a.1 * ((Finset.univ : Finset (Fin n)).val.map r).esymm a.1 *
          (((Finset.univ : Finset (Fin n)).val.map r).map fun x => x ^ a.2).sum := by
  have h := congrArg (MvPolynomial.aeval (R := ℂ) r) (MvPolynomial.mul_esymm_eq_sum (Fin n) ℂ k)

  simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
  MvPolynomial.aeval_esymm_eq_multiset_esymm] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1

  simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X, Multiset.map_map,
  Function.comp_def]
  rfl

private lemma esymm_descends (F : Type) [Field F] [NumberField F] (n : ℕ)
    (m : (F →+* ℂ) → Multiset ℂ) (hc : ∀ τ, Multiset.card (m τ) = n)
    (hpow : ∀ j : ℕ, ∃ b : F, ∀ τ, ((m τ).map fun r => r ^ j).sum = τ b) (k : ℕ) :
    ∃ b : F, ∀ τ, (m τ).esymm k = τ b := by
  choose p hp using hpow
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨1, fun τ => by simp [Multiset.esymm]⟩
    choose! e he using ih
    refine ⟨(k : F)⁻¹ * ((-1) ^ (k + 1) *
      ∑ a ∈ (Finset.HasAntidiagonal.antidiagonal k).filter (fun a => a.1 < k),
        (-1) ^ a.1 * e a.1 * p a.2), fun τ => ?_⟩
    obtain ⟨r, hr⟩ := exists_fin_map n (m τ) (hc τ)
    have hs := newton_step n k r
    rw [hr] at hs
    have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'

    simp only [map_mul, map_inv₀, map_natCast, map_pow, map_neg, map_one, map_sum]
    rw [eq_inv_mul_iff_mul_eq₀ hk', hs]
    congr 1
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [he a.1 (Finset.mem_filter.1 ha).2 τ, hp]

theorem UpperTheory.Gal.W2.newtonPoly_of :
    UpperTheory.Gal.W2.NewtonPoly := by
  intro F _ _ n m hc hpow
  choose b hb using esymm_descends F n m hc hpow
  refine ⟨∑ j ∈ Finset.range (n + 1), (-1) ^ j * (C (b j) * X ^ (n - j)), ?_⟩
  have hmap : ∀ τ : F →+* ℂ, Polynomial.map τ
      (∑ j ∈ Finset.range (n + 1), (-1) ^ j * (C (b j) * X ^ (n - j))) =
      ((m τ).map fun r => X - C r).prod := by
    intro τ

    rw [Multiset.prod_X_sub_X_eq_sum_esymm, hc τ, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hb j τ]
  obtain ⟨τ⟩ : Nonempty (F →+* ℂ) := inferInstance
  have hmon : ((m τ).map fun r => X - C r).prod.Monic :=
    Polynomial.monic_multiset_prod_of_monic _ _ fun r _ => Polynomial.monic_X_sub_C r
  refine ⟨?_, ?_, hmap⟩
  · have h1 := Polynomial.leadingCoeff_map_of_injective τ.injective
      (∑ j ∈ Finset.range (n + 1), (-1) ^ j * (C (b j) * X ^ (n - j)))
    rw [hmap τ, hmon.leadingCoeff] at h1
    exact τ.injective (by rw [← h1, map_one])
  · rw [← Polynomial.natDegree_map_eq_of_injective τ.injective, hmap τ,
      Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hc τ]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem span_joint (g : ℕ) (I : Type) (M : I → Matrix (Fin g) (Fin g) ℂ)
    (hc : ∀ i j, M i * M j = M j * M i)
    (hp : ∀ i, ∃ p : ℂ[X], p.Separable ∧ aeval (M i) p = 0) :
    Submodule.span ℂ {v : Fin g → ℂ | ∃ c : I → ℂ, ∀ i, (M i).mulVec v = c i • v} = ⊤ := by
  classical
  let f : I → Module.End ℂ (Fin g → ℂ) := fun i => Matrix.toLinAlgEquiv' (M i)
  have hss : ∀ i, (f i).IsFinitelySemisimple := by
    intro i
    obtain ⟨p, hsep, hpz⟩ := hp i
    apply Module.End.IsSemisimple.isFinitelySemisimple
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree
    show aeval (Matrix.toLinAlgEquiv' (M i)) p = 0
    rw [Polynomial.aeval_algEquiv]
    simp [hpz]
  have hcomm : Pairwise fun i j => Commute (f i) (f j) := by
    intro i j _
    show Matrix.toLinAlgEquiv' (M i) * Matrix.toLinAlgEquiv' (M j) =
      Matrix.toLinAlgEquiv' (M j) * Matrix.toLinAlgEquiv' (M i)
    rw [← map_mul, ← map_mul, hc]
  have htop : ∀ i, iSup (fun t => (f i).maxGenEigenspace t) = ⊤ :=
    fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i)
  have hall := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f hcomm htop
  rw [eq_top_iff, ← hall]
  refine iSup_le fun χ => ?_
  intro v hv
  apply Submodule.subset_span
  refine ⟨χ, fun i => ?_⟩
  have hvi : v ∈ (f i).maxGenEigenspace (χ i) := (Submodule.mem_iInf _).1 hv i
  rw [(hss i).maxGenEigenspace_eq_eigenspace, Module.End.mem_eigenspace_iff] at hvi
  simpa [f] using hvi

theorem UpperTheory.Gal.W2.simDiag_of :
    UpperTheory.Gal.W2.SimDiag := by
  intro g I M hc hp
  classical
  have hspan := span_joint g I M hc hp
  obtain ⟨b, hbS, hbspan, hli⟩ :=
    exists_linearIndependent ℂ {v : Fin g → ℂ | ∃ c : I → ℂ, ∀ i, (M i).mulVec v = c i • v}
  let B := Module.Basis.mk hli (le_of_eq (by rw [Subtype.range_coe, hbspan, hspan]))
  let B' := B.reindex (B.indexEquiv (Pi.basisFun ℂ (Fin g)))
  have hmem : ∀ k, ∃ c : I → ℂ, ∀ i, (M i).mulVec (B' k) = c i • B' k := by
    intro k
    have : B' k ∈ b := by
      simp only [B', B, Module.Basis.reindex_apply, Module.Basis.mk_apply]
      exact Subtype.mem _
    exact hbS this
  choose c hc' using hmem
  refine ⟨(Pi.basisFun ℂ (Fin g)).toMatrix B', fun i k => c k i, ?_, fun i => ?_⟩
  · rw [← Module.Basis.det_apply]
    exact ((Pi.basisFun ℂ (Fin g)).isUnit_det B').ne_zero
  · ext r k
    rw [Matrix.mul_diagonal]
    have h := congr_fun (hc' k i) r
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    simp only [Matrix.mul_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [h, mul_comm]
end
