module

public import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle186
public import Formalism.LocalRingCardinality.Bundle005
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle224
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle126
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle228
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle223
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle277
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle281
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSelfDualPairGaloisConjugateHomLattice
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open Formalism.BasicNotions NumberField

noncomputable section

namespace GlobalTheory.ProvisionalDivX

section Form

variable {K : Type} [Field K] (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
  (c : Module.Basis (Fin n) ℂ W)

end Form

structure MjForm (D : D7) (j : ℕ) where

  H : HLat D.what₂.LL

  jm : H.V →ₛₗ[D.what₂.embLL] D.what₂.Mj j
  good : H.Good
  basis : LinearIndependent ℂ (fun i => jm (H.b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jm (H.b i))) = ⊤
  lat : 1 ≤ j → j ≤ D.R.m → ∀ x, x ∈ H.L ↔ ∃ c : D.what₂.Mj j → 𝓞 D.what₂.LL,
    jm x = ∑ v ∈ (D.what₂.MjLat j).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v
  sub : 1 ≤ j → j ≤ D.R.m → ∀ x ∈ (D.what₂.MjLat j).gen, x ∈ Set.range jm
  metric : ∀ x, Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord H.b H.X
    (InfinitePlace.mk D.what₂.embLL) x) = ‖jm x‖

theorem resChar_eq_iff (D : D7) {p : ℕ} (hp : p.Prime) (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w = p ↔ (p : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  constructor
  · intro h; rw [← h]; exact resChar_mem D w
  · intro hmem
    by_contra hne
    have hcop : Nat.Coprime (D.what₂.places.resChar w) p :=
      (Nat.coprime_primes (D.what₂.places.resChar_prime w) hp).mpr hne
    obtain ⟨a, b, hab⟩ : IsCoprime ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) (p : 𝓞 D.what₂.LL) :=
      hcop.cast
    apply (D.plEq w).isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (resChar_mem D w)) (Ideal.mul_mem_left _ _ hmem)

def placeEquiv (D : D7) (p : ℕ) [hp : Fact p.Prime] :
    Formalism.L2.Geo.PlL D p ≃ {w : D.what₂.places.Pl // D.what₂.places.resChar w = p} :=
  (D.plEq.subtypeEquiv (resChar_eq_iff D hp.out)).symm

theorem wtL_eq_ramIdx_mul (D : D7) (p : ℕ) [hp : Fact p.Prime] (la : Formalism.L2.Geo.PlL D p) :
    Formalism.L2.Geo.wtL D p la = (D.what₂.places.ramIdx (placeEquiv D p la).1 : ℝ) *
      (padicValNat p (Ideal.absNorm (D.plEq (placeEquiv D p la).1).asIdeal) : ℝ) /
        (Module.finrank ℚ D.what₂.LL : ℝ) := by
  have he : D.plEq (placeEquiv D p la).1 = la.1 := D.plEq.apply_symm_apply _
  have := liesOver_of_mem p hp.out la.1 la.2
  have hN := Ideal.pow_inertiaDeg p la.1.asIdeal
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.out.one_lt)).ne'
  have hval : padicValNat p (p ^ la.1.asIdeal.inertiaDeg ℤ) = la.1.asIdeal.inertiaDeg ℤ := by
    rw [Nat.padicValNat_def, Nat.multiplicity_prime_pow]
  rw [D.ram_eq, he, Formalism.L2.Geo.wtL, ← hN, hval]
  push_cast
  rw [Real.log_pow]
  field_simp

def smallShim (D : D7) (r : ℕ) : DV.ShimX D.what₂.Tau :=
  provisionalShimX D.what₂.Tau (max r 2) 1 ∅ le_rfl (by omega) (by simp)

end GlobalTheory.ProvisionalDivX

namespace GlobalTheory

open ProvisionalDivX

def provisionalDivX (D : D7) (G : DV.Geo D.what₂.LL) (Y : G.Var)
    (jc : ∀ (p : ℕ) [Fact p.Prime], DV.KW p →+* ℂ)
    (M : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ),
      DV.Mdl D p (max r 2) (DV.rkOf (DV.PsiOf D (jc p)) (max r 2) 1))
    (F : ∀ j, MjForm D j) : DivX D :=
  letI := D.host.cmStar
  { geo := G
    Lev := Unit
    levPr := fun _ => ∅
    shv := fun S _ => smallShim D S.rank
    shv_N := fun _ _ h => max_eq_left h
    shv_lev := fun _ _ => rfl
    PlP := fun p _ => Formalism.L2.Geo.PlL D p
    plpFin := fun p _ => Formalism.L2.Geo.finPl D p
    plpNe := fun p _ => Formalism.L2.Geo.plL_ne D p
    wtP := fun p _ => Formalism.L2.Geo.wtL D p
    divisorWeight_nonneg := fun p _ => Formalism.L2.Geo.wtL_nonneg D p
    divisorWeight_sum := fun p _ => Formalism.L2.Geo.wtL_sum D p
    plP := fun p _ => placeEquiv D p
    divisorWeight_def := fun p _ => wtL_eq_ramIdx_mul D p
    jC := fun p _ _ => jc p
    Mp := fun _ _ _ _ _ => Unit
    md := fun S _ p _ _ _ => M p S.rank
    vdd := fun _ _ => 0
    vdd_unram := fun _ _ _ => rfl
    phiFr_unram := fun _ _ _ _ _ _ => rfl
    vdd_nonneg := fun _ _ => le_rfl
    CurveM := fun _ _ _ _ _ _ => Empty
    degM := fun _ _ _ _ _ _ _ _ => 0
    htMdl := fun _ _ _ _ _ => ()
    htCurve := fun _ _ p _ =>
      { toFun := fun c => Empty.elim c
        invFun := fun c => c.2
        left_inv := fun c => Empty.elim c
        right_inv := fun c => Empty.elim c.2 }
    htCurve_deg := fun _ _ _ _ c => Empty.elim c
    MjH := fun j => (F j).H
    MjH_good := fun j => (F j).good
    jM := fun j => (F j).jm
    jM_basis := fun j => (F j).basis
    jM_lat := fun j => (F j).lat
    MjLat_sub := fun j => (F j).sub
    jM_metric := fun j _ _ => (F j).metric
    Qp := fun _ => ∅
    degreeZero_partial_set_empty := rfl
    Qp_muAt := fun _ => Finset.notMem_empty _
    Qp_g := fun _ _ _ => Finset.notMem_empty _
    QPl := fun _ => Empty
    qv := fun _ v => v.elim
    qv_gt := fun _ v => v.elim
    qv_char := fun _ _ v => v.elim
    nu := fun _ v => v.elim
    nu_ne := fun _ v => v.elim
    nu_abs := fun _ v => v.elim
    ZQ := fun _ v => v.elim
    quotientLocalValueFirst := fun _ v => v.elim
    typeDim := fun _ v => v.elim
    Comp := fun _ => Unit
    degHH := fun _ _ _ => 0
    Yv := fun _ _ => Y
    Ybd := fun _ _ => G.supp Y 0
    Lw := fun _ _ => 0
    iMj := fun _ _ => 0
    iMj_mem := fun _ _ _ => Submodule.zero_mem _
    logLam := fun j σ _ => Real.log (D.what₂.lamP D.what₂.mu0 j σ)
    logLam_base := fun _ _ => rfl
    kapR := fun _ => kapSharp D
    kapR_pos := fun _ => RowSide.kapOf_pos _ _
    kapR_conj := fun _ => rfl
    Surf := Empty
    surfCh2 := fun s => s.elim
    surfDegOm := fun s => s.elim
    SurfFp := Empty
    surfFpCh2 := fun s => s.elim }

end GlobalTheory

end
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory

theorem irrU_of_dense_graded_irrGK :
    ∀ (p q : ℕ) (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), Function.Injective j → Dense (Set.range j) → (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → IrrGK M → ∀ (N : ℕ → Submodule ℂ M.V) (k : T.G) (lam : ℕ → ℂ), (∀ m, FiniteDimensional ℂ (N m)) → (⨆ m, N m) = ⊤ → k ∈ T.Kset → Function.Injective lam → (∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x) → IrrU σ := by
  intro p q T σ M j hinj hd hder hirr N k lam hfin hN _ hlam heig
  haveI := hirr.1
  refine ⟨hinj.nontrivial, fun S hS hinv => ?_⟩
  haveI : CompleteSpace S := hS.completeSpace_coe
  have hreal : ∀ Y ∈ upq p q, ∀ y, j y ∈ S → j (M.act Y y) ∈ S := by
    intro Y hY y hy
    rw [← S.orthogonal_orthogonal, Submodule.mem_orthogonal]
    intro w hw
    have h1 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hder Y hY y)
    have h2 : HasDerivAt (fun _ : ℝ => (0 : ℂ)) (inner ℂ w (j (M.act Y y))) 0 := by
      refine HasDerivAt.congr_of_eventuallyEq h1 (Filter.Eventually.of_forall fun t => ?_)
      exact (Submodule.inner_left_of_mem_orthogonal (hinv _ _ hy) hw).symm
    exact h2.unique (hasDerivAt_const _ _)
  have hstab : ∀ Z, ∀ y ∈ S.comap j, M.act Z y ∈ S.comap j := by
    intro Z y hy
    obtain ⟨X, hX, Y, hY, rfl⟩ := GlobalTheory.FockTensor.exists_upq_add Z
    rw [Submodule.mem_comap] at hy ⊢
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    exact S.add_mem (hreal X hX y hy) (S.smul_mem _ (hreal Y hY y hy))
  rcases hirr.2 _ hstab with h | h
  · left
    have hperp : ∀ b ∈ Sᗮ, σ.π k b ∈ Sᗮ := by
      intro b hb
      rw [Submodule.mem_orthogonal']
      intro u hu
      rw [GlobalTheory.FockTensor.inner_pi_left]
      exact Submodule.inner_left_of_mem_orthogonal (hinv _ _ hu) hb
    have hdense : Dense ((⨆ m, (N m).map j : Submodule ℂ σ.H) : Set σ.H) := by
      rw [← Submodule.map_iSup, hN, Submodule.map_top]
      exact hd
    have hle : (⨆ m, (N m).map j : Submodule ℂ σ.H) ≤ Sᗮ := by
      refine iSup_le fun m => ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨a, ha, b, hb, hab⟩ := S.exists_add_mem_mem_orthogonal (j x)
      have he := heig m x hx
      rw [hab, map_add (f := _), smul_add] at he
      have hdiff : σ.π k a - lam m • a = lam m • b - σ.π k b := by
        rw [sub_eq_sub_iff_add_eq_add, he, add_comm]
      have h1 : σ.π k a - lam m • a ∈ S := S.sub_mem (hinv _ _ ha) (S.smul_mem _ ha)
      have h2 : σ.π k a - lam m • a ∈ Sᗮ := by
        rw [hdiff]
        exact Sᗮ.sub_mem (Sᗮ.smul_mem _ hb) (hperp b hb)
      have h3 : σ.π k a = lam m • a :=
        sub_eq_zero.1 (inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal h1 h2))
      have h4 := GlobalTheory.mem_of_isometry_eigen_of_dense_iSup σ.H (σ.π k) (σ.isom k)
        (fun m => (N m).map j) lam hlam (fun m => by haveI := hfin m; infer_instance)
        (by rintro m _ ⟨x, hx, rfl⟩; exact heig m x hx) hdense m a h3
      obtain ⟨x', -, hx'⟩ := h4
      have h5 : x' ∈ S.comap j := by rw [Submodule.mem_comap, hx']; exact ha
      rw [h, Submodule.mem_bot] at h5
      rw [h5, map_zero] at hx'
      rw [hab, ← hx', zero_add]
      exact hb
    rw [← Submodule.orthogonal_eq_top_iff, eq_top_iff]
    intro v _
    exact closure_minimal hle S.isClosed_orthogonal (hdense v)
  · right
    rw [eq_top_iff]
    intro v _
    refine closure_minimal ?_ hS (hd v)
    rintro _ ⟨x, rfl⟩
    have : x ∈ S.comap j := by rw [h]; trivial
    exact this

end GlobalTheory
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 MeasureTheory
open scoped BigOperators

noncomputable section

namespace GlobalTheory.UnitaryTheta

theorem isAddHaarMeasure_pi {ι G : Type} [Fintype ι] [NormedAddCommGroup G] [MeasureSpace G] [BorelSpace G]
    [SecondCountableTopology G] [SigmaFinite (volume : Measure G)] [(volume : Measure G).IsAddHaarMeasure] :
    (volume : Measure (ι → G)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _

instance isAddHaarMeasure_VC (D : D7) (N N' : ℕ) : (volume : Measure (VC D N N')).IsAddHaarMeasure := by
  haveI : (volume : Measure (Fin N → ℂ)).IsAddHaarMeasure := isAddHaarMeasure_pi
  haveI : (volume : Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure := isAddHaarMeasure_pi
  exact isAddHaarMeasure_pi

theorem area_pos (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hC : Crv D cc δ) : 0 < area (lamOf D cc δ) := by
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hC
  exact (GlobalTheory.PlaneLattice.area_pos_and_selfDual L _ hL).1

theorem emb_conj (D : D7) (φ : D.host.E →+* ℂ) (x : D.host.E) :
    φ (D.host.conj x) = (starRingEnd ℂ) (φ x) :=
  D.host.conjE_apply φ x

theorem map_hYY (D : D7) {N N' : ℕ} (x y : Matrix (Fin N') (Fin N) D.host.E) :
    D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) =
      ∑ τ, ∑ i, ∑ j, embT D τ (x i j) * (starRingEnd ℂ) (embT D τ (y i j)) := by
  rw [hYY, ← GlobalTheory.InducedType.sum_eq_trace D]

  simp only [map_sum, map_mul, emb_conj]

theorem map_hYY_symm (D : D7) {N N' : ℕ} (x y : Matrix (Fin N') (Fin N) D.host.E) :
    D.host.φ₀ ((hYY D y x : D.host.K) : D.host.E) =
      (starRingEnd ℂ) (D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E)) := by

  simp only [map_hYY, map_sum, map_mul, Complex.conj_conj, mul_comm]

theorem map_hYY_smul_left (D : D7) {N N' : ℕ} (z : D.host.K) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    D.host.φ₀ ((hYY D (z • x) y : D.host.K) : D.host.E) =
      D.host.φ₀ (z : D.host.E) * D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) := by
  simp only [map_hYY, Finset.mul_sum, Matrix.smul_apply]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← GlobalTheory.InducedType.restrict_K D τ z, ← mul_assoc, ← map_mul]
  rfl

theorem map_hYY_smul_right (D : D7) {N N' : ℕ} (z : D.host.K) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    D.host.φ₀ ((hYY D x (z • y) : D.host.K) : D.host.E) =
      (starRingEnd ℂ) (D.host.φ₀ (z : D.host.E)) * D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) := by
  rw [map_hYY_symm, map_hYY_smul_left, map_mul, ← map_hYY_symm]

theorem onB_smul (D : D7) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : OnB D b)
    (z : D.host.K) (hz : D.host.φ₀ (z : D.host.E) * (starRingEnd ℂ) (D.host.φ₀ (z : D.host.E)) = 1) :
    OnB D (fun j => z • b j) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  refine ⟨fun i j => ?_, ?_⟩
  · rw [← hb.1 i j]
    apply Subtype.ext
    apply D.host.φ₀.injective
    rw [map_hYY_smul_left, map_hYY_smul_right, ← mul_assoc, hz, one_mul]
  · rw [eq_top_iff, ← hb.2, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have : b j = z⁻¹ • (z • b j) := by rw [smul_smul, inv_mul_cancel₀ hz0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.UnitaryTheta
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.admJ_and_torsion_data_algebraic : ∀ (D : D7), admG1 D → GL3Theta.admJ D ∧ ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → DataIn D (tor0 D cc δ) Qbar ∧ ∀ t, InRationalLattice (lamOf D cc δ) t → t ∉ (lamOf D cc δ) → wpF (lamOf D cc δ) t ∈ Qbar ∧ wpD (lamOf D cc δ) t ∈ Qbar := by
  first | exact @GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data | exact GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data | (intros; apply GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_traceDual_family_homLattice : ∀ (D : D7), (∃ (r : ℕ) (a a' : Fin r → D.host.E), (∀ k, a k ∈ D.host.AA0) ∧ (∀ k, a' k ∈ D.host.AA0) ∧ ∀ t : D.host.E, t = ∑ k, (Algebra.trace D.host.K D.host.E (t * D.host.conj (a' k))) • a k) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' → ∃ (r : ℕ) (y y' : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ i, y i ∈ YYl D L L') ∧ (∀ i, y' i ∈ YYl D L L') ∧ ∀ x : Matrix (Fin N') (Fin N) D.host.E, x = ∑ i, hYY D x (y' i) • y i := by
  first | exact @GlobalTheory.HomDual.exists_dual_family_hom | exact GlobalTheory.HomDual.exists_dual_family_hom | (intros; apply GlobalTheory.HomDual.exists_dual_family_hom <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.hermitian_pairing_integral_values : ∀ (D : D7) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' → ∀ x ∈ YYl D L L', ∀ y ∈ YYl D L L', hYY D x y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  first | exact @GlobalTheory.NormSum.TraceInt.hYY_integral | exact GlobalTheory.NormSum.TraceInt.hYY_integral | (intros; apply GlobalTheory.NormSum.TraceInt.hYY_integral <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.orthonormal_realBasis_complex_coordinates : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → (∀ i j, coordB D (tor0 D cc δ) b i (embV D (tor0 D cc δ) (b j)) = if i = j then 1 else 0) ∧ ∀ z : VC D N N', z = ∑ j, coordB D (tor0 D cc δ) b j z • embV D (tor0 D cc δ) (b j) := by
  first | exact @GlobalTheory.OrthoCoord.orthonormal_coord | exact GlobalTheory.OrthoCoord.orthonormal_coord | (intros; apply GlobalTheory.OrthoCoord.orthonormal_coord <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_selfDual_pair_galoisConjugate_homLattice : ∀ (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E), (∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E)) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' → ∃ (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L₁ ∧ SD D L₁' ∧ ∀ A : Matrix (Fin N') (Fin N) D.host.E, A ∈ YYl D L L' ↔ A.map σ ∈ YYl D L₁ L₁' := by
  first | exact @GlobalTheory.GaloisTwist.exists_conjugate_pair | exact GlobalTheory.GaloisTwist.exists_conjugate_pair | (intros; apply GlobalTheory.GaloisTwist.exists_conjugate_pair <;> assumption)
end
