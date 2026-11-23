module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1999
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FinitelyManyMarkedClassesTermDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1976
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle442
public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
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
import Mathlib.RingTheory.Ideal.Norm.RelNorm
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm

@[expose] public section

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

theorem submatrix_mul_right' {R : Type} [CommRing R] {m n o p : ℕ} (P : Matrix (Fin m) (Fin n) R)
    (Q : Matrix (Fin n) (Fin o) R) (e : Fin p → Fin o) : (P * Q).submatrix id e = P * Q.submatrix id e := by
  ext i j; simp [Matrix.mul_apply]

theorem submatrix_eq_mul_one {R : Type} [CommRing R] {m n p : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (e : Fin p → Fin n) : A.submatrix id e = A * (1 : Matrix (Fin n) (Fin n) R).submatrix id e := by
  ext i j; simp [Matrix.mul_apply, Matrix.one_apply]

theorem flag_mat {R : Type} [CommRing R] {n r : ℕ} (A : Matrix (Fin n) (Fin r) R)
    (A' : Matrix (Fin r) (Fin n) R) (hA : A' * A = 1) (M : Matrix (Fin n) (Fin n) R)
    (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r) (hS : ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k)
    (d : Fin s → ℕ) (hd : ∀ i, d i = (S.filter (· < Fin.castLE hs i)).card)
    (hM : ∀ k ∈ S, ∃ Bk : Matrix (Fin (k.val + 1)) (Fin (k.val + 1)) R,
      M * A.submatrix id (Fin.castLE k.2) = A.submatrix id (Fin.castLE k.2) * Bk) :
    ∃ B : Matrix (Fin s) (Fin s) R, B.BlockTriangular d ∧
      M * A.submatrix id (Fin.castLE hs) = A.submatrix id (Fin.castLE hs) * B := by
  have key : ∀ k ∈ S, ∀ j : Fin r, j ≤ k →
      (∀ l : Fin r, k < l → (A' * M * A) l j = 0) ∧ ∀ a, (M * A) a j = (A * (A' * M * A)) a j := by
    intro k hk j hj
    obtain ⟨Bk, hB⟩ := hM k hk
    have hAk : A' * A.submatrix id (Fin.castLE k.2) = (1 : Matrix (Fin r) (Fin r) R).submatrix id (Fin.castLE k.2) := by
      rw [← submatrix_mul_right', hA]
    have hTk : (A' * M * A).submatrix id (Fin.castLE k.2) =
        (1 : Matrix (Fin r) (Fin r) R).submatrix id (Fin.castLE k.2) * Bk := by
      rw [Matrix.mul_assoc, submatrix_mul_right', submatrix_mul_right', hB, ← Matrix.mul_assoc, hAk]
    have hjk : j.val < k.val + 1 := Nat.lt_succ_of_le hj
    have hj' : Fin.castLE k.2 (⟨j.val, hjk⟩ : Fin (k.val + 1)) = j := Fin.ext rfl
    refine ⟨fun l hl => ?_, fun a => ?_⟩
    · have := congrFun (congrFun hTk l) ⟨j.val, hjk⟩
      rw [Matrix.submatrix_apply, hj'] at this
      change (A' * M * A) l j = _ at this
      rw [this, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l' _ => ?_
      have hne : l ≠ Fin.castLE k.2 l' := by
        intro h; have := congrArg Fin.val h; simp at this; have := l'.2; have := Fin.lt_def.1 hl; omega
      simp [Matrix.one_apply, hne]
    · have e1 : M * A.submatrix id (Fin.castLE k.2) = (A * (A' * M * A)).submatrix id (Fin.castLE k.2) := by
        rw [hB, submatrix_mul_right', hTk, ← Matrix.mul_assoc, ← submatrix_eq_mul_one]
      have := congrFun (congrFun e1 a) ⟨j.val, hjk⟩
      rw [← submatrix_mul_right', Matrix.submatrix_apply, Matrix.submatrix_apply, hj'] at this
      exact this
  have hsmall : ∀ j : Fin r, j.val < s → ∀ l : Fin r, s ≤ l.val → (A' * M * A) l j = 0 := by
    intro j hj l hl
    obtain ⟨k, hk, hjk⟩ := (hS j).1 hj
    have hks : k.val < s := (hS k).2 ⟨k, hk, le_rfl⟩
    exact (key k hk j hjk).1 l (Fin.lt_def.2 (by omega))
  refine ⟨(A' * M * A).submatrix (Fin.castLE hs) (Fin.castLE hs), fun i j hij => ?_, ?_⟩
  · obtain ⟨k, hk, h1, h2⟩ := (depth_lt_iff S s hs d hd i j).1 hij
    exact (key k hk _ h1).1 _ h2
  · ext a j
    have hj : (Fin.castLE hs j).val < s := j.2
    obtain ⟨k, hk, hjk⟩ := (hS _).1 hj
    have e := (key k hk _ hjk).2 a
    rw [← submatrix_mul_right']
    change (M * A) a (Fin.castLE hs j) = _
    rw [e, Matrix.mul_apply, Matrix.mul_apply]
    symm
    rw [show (∑ x : Fin s, A.submatrix id (Fin.castLE hs) a x * (A' * M * A).submatrix (Fin.castLE hs) (Fin.castLE hs) x j) =
        ∑ l ∈ Finset.univ.map (Fin.castLEEmb hs), A a l * (A' * M * A) l (Fin.castLE hs j) from by
      rw [Finset.sum_map]; rfl]
    refine Finset.sum_subset (Finset.subset_univ _) fun l _ hl => ?_
    have : s ≤ l.val := by
      by_contra h; push_neg at h
      exact hl (Finset.mem_map.2 ⟨⟨l.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    rw [hsmall _ hj l this, mul_zero]

end GlobalTheory.TieStd

namespace GlobalTheory.TieStd


open GlobalTheory.StdPar in
theorem levi_le_leviFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r),
    (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) →
    GlobalTheory.StdPar.levi σ J X Y S ≤
      GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S s hs hS d hd
  have side : ∀ Z W : Matrix (Fin n) (Fin r) E, Formalism.UG.cT (σ : E →+* E) W * J * Z = 1 →
      ∀ g : GAd σ J, (∀ k ∈ S, g ∈ frameStab σ J (initCols Z k) ⊤) →
      ∃ B : Matrix (Fin s) (Fin s) (AF F ⊗[F] E), B.BlockTriangular d ∧
        (matHom _ σ J g).1 * adMat F (Z.submatrix id (Fin.castLE hs)) =
          adMat F (Z.submatrix id (Fin.castLE hs)) * B := by
    intro Z W hWZ g hg
    have hA : adMat F (Formalism.UG.cT (σ : E →+* E) W * J) * adMat F Z = 1 := by
      rw [← Matrix.map_mul, hWZ, Matrix.map_one _ (map_zero _) (map_one _)]
    exact flag_mat (adMat F Z) _ hA _ S s hs hS d hd fun k hk => by
      obtain ⟨B, -, e⟩ := hg k hk
      exact ⟨B.1, e⟩
  have mem : ∀ g ∈ levi σ J X Y S, ∀ k ∈ S,
      g ∈ frameStab σ J (initCols X k) ⊤ ∧ g ∈ frameStab σ J (initCols Y k) ⊤ := fun g hg k hk => by
    simp only [levi, Subgroup.mem_iInf, Subgroup.mem_inf] at hg
    exact hg k hk
  have hyx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := yx h hJ hW
  intro g hg
  have hgi := inv_mem hg
  exact Subgroup.mem_inf.2
    ⟨⟨side X Y hyx g fun k hk => (mem g hg k hk).1, side X Y hyx g⁻¹ fun k hk => (mem _ hgi k hk).1⟩,
      ⟨side Y X hW.xy g fun k hk => (mem g hg k hk).2, side Y X hW.xy g⁻¹ fun k hk => (mem _ hgi k hk).2⟩⟩

end GlobalTheory.TieStd
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

theorem sum_castLE_of_zero {M : Type*} [AddCommMonoid M] {m s : ℕ} (hm : m ≤ s) (g : Fin s → M)
    (hg : ∀ i : Fin s, m ≤ i.val → g i = 0) : ∑ i : Fin s, g i = ∑ i : Fin m, g (Fin.castLE hm i) := by
  symm
  refine Eq.trans (Finset.sum_map Finset.univ (Fin.castLEEmb hm) g).symm ?_
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hg i (not_lt.1 fun h => hi ?_)
  exact Finset.mem_map.2 ⟨⟨i.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩

theorem mul_submatrix_castLE {R ι' κ : Type*} [CommRing R] {m s : ℕ} (hm : m ≤ s) (C : Matrix ι' (Fin s) R)
    (B : Matrix (Fin s) (Fin s) R) (hB : ∀ i j : Fin s, m ≤ i.val → j.val < m → B i j = 0) (f : κ → ι') :
    (C * B).submatrix f (Fin.castLE hm) =
      C.submatrix f (Fin.castLE hm) * B.submatrix (Fin.castLE hm) (Fin.castLE hm) := by
  ext a j
  simp only [submatrix_apply, Matrix.mul_apply]
  exact sum_castLE_of_zero hm _ fun i hi => by rw [hB i _ hi j.2, mul_zero]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem mem_frameStab_of_mem_parFlag {s m : ℕ} (hm : m ≤ s) (C : Matrix (Fin n) (Fin s) E)
    (L : Matrix (Fin s) (Fin n) E) (hL : L * C = 1) (d : Fin s → ℕ)
    (hd : ∀ i j : Fin s, m ≤ i.val → j.val < m → d j < d i) {g : GAd σ J} (hg : g ∈ GlobalTheory.UAut.parFlag σ J C d) :
    g ∈ GlobalTheory.StdPar.frameStab σ J (C.submatrix id (Fin.castLE hm)) ⊤ := by
  obtain ⟨⟨B, hB, e⟩, B', hB', e'⟩ := hg
  have hL' : adMat F L * adMat F C = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have hMM : (matHom _ σ J g).1 * (matHom _ σ J g⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hBB : B * B' = 1 := by
    calc B * B' = adMat F L * (adMat F C * B) * B' := by rw [← Matrix.mul_assoc, hL', Matrix.one_mul]
      _ = adMat F L * ((matHom _ σ J g).1 * ((matHom _ σ J g⁻¹).1 * adMat F C)) := by
          simp only [← e, e', Matrix.mul_assoc]
      _ = 1 := by rw [← Matrix.mul_assoc (matHom _ σ J g).1, hMM, Matrix.one_mul, hL']
  have hz : ∀ {A : Matrix (Fin s) (Fin s) (AF F ⊗[F] E)}, A.BlockTriangular d →
      ∀ i j : Fin s, m ≤ i.val → j.val < m → A i j = 0 := fun hA i j hi hj => hA (hd i j hi hj)
  have hU : B.submatrix (Fin.castLE hm) (Fin.castLE hm) * B'.submatrix (Fin.castLE hm) (Fin.castLE hm) = 1 := by
    rw [← mul_submatrix_castLE hm B B' (hz hB') (Fin.castLE hm), hBB, Matrix.submatrix_one _ (Fin.castLE_injective hm)]
  refine ⟨⟨_, _, hU, mul_eq_one_comm.1 hU⟩, Subgroup.mem_top _, ?_⟩
  show (matHom _ σ J g).1 * (adMat F C).submatrix id (Fin.castLE hm) =
    (adMat F C).submatrix id (Fin.castLE hm) * B.submatrix (Fin.castLE hm) (Fin.castLE hm)
  rw [← mul_submatrix_castLE hm _ B (hz hB) id, ← e]
  ext a j
  simp [Matrix.mul_apply]

end GlobalTheory.TieStd

namespace GlobalTheory.TieStd

theorem leviFlag_le_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E),
    IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) →
    ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) →
    GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d ≤
      GlobalTheory.StdPar.levi σ J X Y S := by
  intro F E _ _ _ _ _ σ hσ n J hJ r X Y hW S s hs hS d hd g hg
  obtain ⟨hgX, hgY⟩ := Subgroup.mem_inf.1 hg
  have hyx := GlobalTheory.StdPar.yx hσ hJ hW
  have hLX : Formalism.UG.cT (σ : E →+* E) (Y.submatrix id (Fin.castLE hs)) * J * X.submatrix id (Fin.castLE hs) = 1 := by
    rw [cT_submatrix_mul, hyx, Matrix.submatrix_one _ (Fin.castLE_injective hs)]
  have hLY : Formalism.UG.cT (σ : E →+* E) (X.submatrix id (Fin.castLE hs)) * J * Y.submatrix id (Fin.castLE hs) = 1 := by
    rw [cT_submatrix_mul, hW.xy, Matrix.submatrix_one _ (Fin.castLE_injective hs)]
  rw [GlobalTheory.StdPar.levi, Subgroup.mem_iInf]
  intro k
  rw [Subgroup.mem_iInf]
  intro hk
  have hm : k.val + 1 ≤ s := (hS k).2 ⟨k, hk, le_rfl⟩
  have hdk : ∀ i j : Fin s, k.val + 1 ≤ i.val → j.val < k.val + 1 → d j < d i := fun i j hi hj =>
    (depth_lt_iff S s hs d hd i j).2 ⟨k, hk, Fin.le_iff_val_le_val.2 (Nat.lt_succ_iff.1 hj), Fin.lt_iff_val_lt_val.2 hi⟩
  exact Subgroup.mem_inf.2 ⟨mem_frameStab_of_mem_parFlag σ J hm _ _ hLX d hdk hgX,
    mem_frameStab_of_mem_parFlag σ J hm _ _ hLY d hdk hgY⟩

end GlobalTheory.TieStd
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

theorem _root_.GlobalTheory.T.compactRealPlace_torusClasses_signVectors : ∀ {D : D7} (V : HSp D) {S : D.what₂.Tau → SPar} (M : DSModel V S) (ρ : D.what₂.Tau)
    (P : PPol D.sp.cm.sig V.rank), CompactSpace (Tor P (placeOf D ρ).Completion) →
    (XSet P (placeOf D ρ).Completion V.gram).Finite ∧
      ∃ (y : XSet P (placeOf D ρ).Completion V.gram → Equiv.Perm (Fin V.rank))
        (θ : XSet P (placeOf D ρ).Completion V.gram → Fin V.rank → ℝ),
        Function.Bijective (fun p : compactWeyl (M.ε ρ) × XSet P (placeOf D ρ).Completion V.gram =>
          (y p.2)⁻¹ * p.1.1) ∧
        (∀ q a, Complex.exp (θ q a * Complex.I) = cxRoots (embOverOf D ρ).1 P ((y q)⁻¹ a)) ∧
        ∀ q, ∃ g : GArch D.sp.cm.sig V.gram (placeOf D ρ), frameMat M ρ (g⁻¹ * gam q.2.choose_spec.choose_spec.2 * g) =
          Matrix.diagonal fun a => Complex.exp (θ q a * Complex.I) := by
  first | exact @GlobalTheory.RealSigns.signs_real | exact GlobalTheory.RealSigns.signs_real | (intros; apply GlobalTheory.RealSigns.signs_real <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.test_places_prime_to_level : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ w ∈ ch.G.pl.W0,
    ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  first | exact @GlobalTheory.PlacesPrime.places_prime_to_level | exact GlobalTheory.PlacesPrime.places_prime_to_level | (intros; apply GlobalTheory.PlacesPrime.places_prime_to_level <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.RootSumWeights.RegularPairCommutatorLemmas

theorem commComm_conj {S : Type} [Ring S] (u : S) (v : Sˣ)
    (h : ∀ a b : S, Commute a u → Commute b u → Commute a b) :
    ∀ a b : S, Commute a (v * u * v⁻¹) → Commute b (v * u * v⁻¹) → Commute a b := by
  intro a b ha hb
  have key : ∀ c : S, Commute c (v * u * v⁻¹) → Commute (((v⁻¹ : Sˣ) : S) * c * v) u := by
    intro c hc
    unfold Commute SemiconjBy at hc ⊢
    calc (((v⁻¹ : Sˣ) : S) * c * v) * u = ((v⁻¹ : Sˣ) : S) * (c * (v * u * ((v⁻¹ : Sˣ) : S))) * v := by
          simp [mul_assoc]
      _ = ((v⁻¹ : Sˣ) : S) * ((v * u * ((v⁻¹ : Sˣ) : S)) * c) * v := by rw [hc]
      _ = u * (((v⁻¹ : Sˣ) : S) * c * v) := by simp [mul_assoc]
  have h' := h _ _ (key a ha) (key b hb)
  unfold Commute SemiconjBy at h' ⊢
  have := congrArg (fun z => (v : S) * z * ((v⁻¹ : Sˣ) : S)) h'
  simpa [mul_assoc] using this

variable {p : ℕ} [Fact p.Prime]

theorem regAf_conj (G : HTGroup p) (g h : G.GAf) (hg : RegAf G g) : RegAf G (h⁻¹ * g * h) := by
  obtain ⟨w, hw⟩ := hg
  refine ⟨w, ?_⟩
  have e : ((ubcMap (AfP.eval w) (h⁻¹ * g * h)).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      (((ubcMap (AfP.eval w) h).1.1⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
        ((ubcMap (AfP.eval w) g).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
        ((((ubcMap (AfP.eval w) h).1.1⁻¹)⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
    simp [map_mul, map_inv]
  rw [e]
  exact commComm_conj _ _ hw

theorem commComm_tmul (G : HTGroup p) (K : Type) [Field K] [Algebra ℚ K] (γ : G.C)
    (hsep : (minpoly G.F γ).Separable) (hdeg : (minpoly G.F γ).natDegree = G.n) :
    ∀ a b : K ⊗[ℚ] G.C, Commute a ((1 : K) ⊗ₜ γ) → Commute b ((1 : K) ⊗ₜ γ) → Commute a b := by
  set Z := Subalgebra.centralizer ℚ ({γ} : Set G.C) with hZdef
  have hZ : ∀ x y : Z, x * y = y * x := by
    intro x y
    apply Subtype.ext
    have hc := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC γ hsep hdeg
    have hx : ∀ g ∈ ({γ} : Set G.C), g * (x : G.C) = x * g := (Subalgebra.mem_centralizer_iff _).1 x.2
    have hy : ∀ g ∈ ({γ} : Set G.C), g * (y : G.C) = y * g := (Subalgebra.mem_centralizer_iff _).1 y.2
    show (x : G.C) * y = y * x
    have hy' : (y : G.C) ∈ Subalgebra.centralizer G.F ({γ} : Set G.C) := by
      rw [Subalgebra.mem_centralizer_iff]; exact hy
    rw [hc] at hy'
    have h2 := Algebra.adjoin_le_centralizer_centralizer G.F ({γ} : Set G.C) hy'
    rw [Subalgebra.mem_centralizer_iff] at h2
    have hx' : (x : G.C) ∈ Subalgebra.centralizer G.F ({γ} : Set G.C) := by
      rw [Subalgebra.mem_centralizer_iff]; exact hx
    exact h2 x hx'
  have hcomm : ∀ a b : K ⊗[ℚ] Z, a * b = b * a := by
    intro a b
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [add_mul, mul_add, hx, hy]
    | tmul r x =>
      induction b using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [add_mul, mul_add, hx, hy]
      | tmul s y => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm r s, hZ x y]
  have hcen := Subalgebra.centralizer_coe_image_includeRight_eq_center_tensorProduct ℚ K G.C ({γ} : Set G.C)
  have mem : ∀ c : K ⊗[ℚ] G.C, Commute c ((1 : K) ⊗ₜ γ) →
      c ∈ (Algebra.TensorProduct.map (AlgHom.id ℚ K) Z.val).range := by
    intro c hc
    rw [← hcen, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨g, hg, rfl⟩
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hc.eq.symm
  intro a b ha hb
  obtain ⟨a', rfl⟩ := mem a ha
  obtain ⟨b', rfl⟩ := mem b hb
  unfold Commute SemiconjBy
  rw [← map_mul, ← map_mul, hcomm]

theorem regAf_pair (G : HTGroup p) (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) P.β x t) (h : G.GAf) : RegAf G (h⁻¹ * P.toAf x t hx P.self * h) := by
  apply regAf_conj
  obtain ⟨w⟩ := finitePlacesAway_nonempty p
  refine ⟨w, ?_⟩
  let φ := Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C)
  have e : ((ubcMap (AfP.eval w) (P.toAf x t hx P.self)).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      ((Units.map φ.toRingHom.toMonoidHom x : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
        ((1 : w.1.adicCompletion ℚ) ⊗ₜ (P.γ : G.C)) *
        (((Units.map φ.toRingHom.toMonoidHom x)⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
    show φ ((x : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (P.γ : G.C) * ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) = _
    rw [map_mul, map_mul]
    simp [φ, inC, Units.coe_map_inv]
  rw [e]
  exact commComm_conj _ _ (commComm_tmul G _ _ P.reg.2 P.reg.1)

end GlobalTheory.RootSumWeights.RegularPairCommutatorLemmas

namespace GlobalTheory.RootSumWeights.RegularPairCommutatorLemmas

theorem finitely_many_marked_classes_degree_one_of_regular (hI : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → (∀ g, f g ≠ 0 → RegAf G g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
    Set.Finite {Q : Cls G | (∃ μ, (Quot.out Q).Mark μ) ∧ (Quot.out Q).term L.K.toSubgroup f 1 K' f' ≠ 0}) :
    GlobalTheory.RootSumWeights.FinitelyManyMarkedClassesTermDegreeOne := by
  intro p _ G ha L f K' f' hf hf'
  let f₀ : G.GAf → ℂ := fun g => if RegAf G g then f g else 0
  have hiff : ∀ (k g : G.GAf), RegAf G (k⁻¹ * g * k) ↔ RegAf G g := by
    intro k g
    refine ⟨fun h => ?_, fun h => regAf_conj G g k h⟩
    have := regAf_conj G _ k⁻¹ h
    simpa [mul_assoc] using this
  have hf₀ : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f₀ := by
    obtain ⟨h1, h2, h3, S, hS⟩ := hf
    refine ⟨h1, h2, fun k hk g => ?_, S, fun g hg => hS g ?_⟩
    · have e := h3 k hk g
      simp only [MonoidHom.id_apply] at e ⊢
      simp only [f₀, e, hiff]
    · intro h; apply hg; simp [f₀, h]
  have hreg : ∀ g, f₀ g ≠ 0 → RegAf G g := fun g hg => by
    by_contra h; exact hg (by simp [f₀, h])
  have hterm : ∀ P : Pair G, P.term L.K.toSubgroup f 1 K' f' = P.term L.K.toSubgroup f₀ 1 K' f' := by
    intro P
    have key : ∀ x t hx δ z, P.termAt L.K.toSubgroup f 1 K' f' x t hx δ z =
        P.termAt L.K.toSubgroup f₀ 1 K' f' x t hx δ z := by
      intro x t hx δ z
      unfold Pair.termAt pointSum
      refine finsum_congr fun q => ?_
      have : f ((Quotient.out q).1⁻¹ * P.toAf x t hx P.self * (Quotient.out q).1) =
          f₀ ((Quotient.out q).1⁻¹ * P.toAf x t hx P.self * (Quotient.out q).1) := by
        simp only [f₀, if_pos (regAf_pair G P x t hx _)]
      rw [this]
    unfold Pair.term
    split_ifs <;> simp only [key]
  have hfin := hI p G ha L f₀ hf₀ hreg K' f' hf'
  simpa only [hterm] using hfin

end GlobalTheory.RootSumWeights.RegularPairCommutatorLemmas

theorem GlobalTheory.RootSumWeights.finitely_many_marked_classes_term_degree_one : GlobalTheory.RootSumWeights.FinitelyManyMarkedClassesTermDegreeOne := GlobalTheory.RootSumWeights.RegularPairCommutatorLemmas.finitely_many_marked_classes_degree_one_of_regular GlobalTheory.T.finite_markedPairClasses_degreeOne_term_ne_zero
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

noncomputable section

namespace GlobalTheory.ModulNorm

open GlobalTheory.SumSize

theorem absNorm_map_of_finrank_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (I : Ideal (𝓞 F)) :
    Ideal.absNorm (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) I) = Ideal.absNorm I ^ 2 := by
  rw [Ideal.absNorm_algebraMap, ← h2]
  congr 1
  exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm

theorem absNorm_le_sq_of_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (P : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm P.asIdeal ≤ Ideal.absNorm (P.under (𝓞 F)).asIdeal ^ 2 := by
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (P.under (𝓞 F)).asIdeal ≤ P.asIdeal :=
    Ideal.map_le_iff_le_comap.2 le_rfl
  have hd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [absNorm_map_of_finrank_two h2] at hd
  refine Nat.le_of_dvd (pow_pos (Nat.pos_of_ne_zero ?_) 2) hd
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact (P.under (𝓞 F)).ne_bot

theorem absNorm_modul_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), D.host.F = maximalRealSubfield D.host.E → (Ideal.absNorm G.modul : ℝ) ≤ Real.exp (2 * sig G) := by
  intro D T L sc G hF
  have h2 : Module.finrank D.host.F D.host.E = 2 := by
    rw [hF]; exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hmod : G.modul = ∏ v ∈ G.pl.S0, (G.pl.w v).asIdeal ^ G.pl.depth sc v := rfl
  rw [hmod, map_prod, Nat.cast_prod, sig, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun v _ => by positivity) fun v hv => ?_
  have hw : Ideal.absNorm (G.pl.w v).asIdeal ≤ Ideal.absNorm v.asIdeal ^ 2 := by
    have := absNorm_le_sq_of_under h2 (G.pl.w v)
    rwa [G.pl.under_w hv] at this
  have hpos : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  rw [map_pow, Nat.cast_pow]
  calc ((Ideal.absNorm (G.pl.w v).asIdeal : ℕ) : ℝ) ^ G.pl.depth sc v
      ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ 2) ^ G.pl.depth sc v := by
        gcongr
        exact_mod_cast hw
    _ = Real.exp (2 * ((G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal))) := by
        rw [← pow_mul, ← Real.rpow_natCast, Real.rpow_def_of_pos hpos]
        congr 1
        push_cast
        ring

end GlobalTheory.ModulNorm
end
end
