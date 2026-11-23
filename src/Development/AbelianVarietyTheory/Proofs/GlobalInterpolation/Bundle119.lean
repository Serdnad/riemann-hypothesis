module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle116
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle286
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle281
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyInverseHalfDifferent
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle007
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
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle082
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle033
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.PolyRealU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem continuous_entry (τ : E →+* ℂ) (i j : Fin n) :
    Continuous fun x : infU E n => (cEmb τ x.1).val i j := by
  have h1 : Continuous (coord (E := E) τ) := by
    unfold coord
    split_ifs
    · exact continuous_apply _
    · exact Complex.continuous_conj.comp (continuous_apply _)
  have h2 : Continuous (pInf E) := continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst
  have h3 : Continuous fun x : infU E n => (x.1.1.val : Matrix (Fin n) (Fin n) (Ad E)) i j :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_elem i j
  exact h1.comp (h2.comp h3)


omit [NumberField E] [IsCMField E] in
theorem coord_star' (τ : E →+* ℂ) (z : Cinf E) : coord τ (star z) = star (coord τ z) := by
  unfold coord
  split_ifs <;> rfl

theorem coord_conj (τ : E →+* ℂ) (z : Cinf E) : coord (ComplexEmbedding.conjugate τ) z = star (coord τ z) := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    (InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex (InfinitePlace.mk τ)))
      (ComplexEmbedding.isReal_iff.2 h)
  unfold coord
  rw [InfinitePlace.mk_conjugate_eq]
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · rw [if_pos h, if_neg (by rw [h]; exact hne.symm)]
    rfl
  · rw [if_pos h, if_neg (by rw [h]; exact hne)]
    simp

theorem entry_inv (τ : E →+* ℂ) (x : UA E n) (i j : Fin n) :
    (cEmb τ x⁻¹).val i j = star ((cEmb τ x).val j i) := by
  have hx : Formalism.UG.cT (conjAd E) x.1.val * 1 * x.1.val = 1 := x.2
  rw [Matrix.mul_one] at hx
  have h1 : (x.1⁻¹).val = Formalism.UG.cT (conjAd E) x.1.val := Units.inv_eq_of_mul_eq_one_left hx
  have h2 : ∀ y, pInf E (conjAd E y) = star (pInf E y) := fun y => by
    change (infEq E).symm (infEq E _) = _
    rw [RingEquiv.symm_apply_apply]
    rfl
  change coord τ (pInf E ((x.1⁻¹).val i j)) = star (coord τ (pInf E (x.1.val j i)))
  rw [h1, ← coord_star', ← h2]
  rfl

theorem eq_of_entry {x y : infU E n} (h : ∀ τ i j, (cEmb τ x.1).val i j = (cEmb τ y.1).val i j) : x = y := by
  refine Subtype.ext (Subtype.ext (ga_ext ?_ ?_))
  · ext i j w
    have h1 : coord w.embedding (pInf E (x.1.1.val i j)) = coord w.embedding (pInf E (y.1.1.val i j)) :=
      h w.embedding i j
    unfold coord at h1
    rw [InfinitePlace.mk_embedding, if_pos rfl] at h1
    exact h1
  · exact (MonoidHom.mem_ker.1 x.2).trans (MonoidHom.mem_ker.1 y.2).symm

theorem coprod_adjoin {G : Type} [Mul G] (S : Set (G → ℂ))
    (hS : ∀ p ∈ S, ∃ (m : ℕ) (a b : Fin m → G → ℂ), (∀ i, a i ∈ Algebra.adjoin ℂ S ∧ b i ∈ Algebra.adjoin ℂ S) ∧
      ∀ x k, p (x * k) = ∑ i, a i x * b i k) :
    ∀ p ∈ Algebra.adjoin ℂ S, ∃ (m : ℕ) (a b : Fin m → G → ℂ),
      (∀ i, a i ∈ Algebra.adjoin ℂ S ∧ b i ∈ Algebra.adjoin ℂ S) ∧ ∀ x k, p (x * k) = ∑ i, a i x * b i k := by
  first
  | exact @_root_.GlobalTheory.SplittingAdditive.main
  | exact _root_.GlobalTheory.SplittingAdditive.main
  | (apply _root_.GlobalTheory.SplittingAdditive.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SplittingAdditive.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SplittingAdditive.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SplittingAdditive.main ..)

theorem poly_infU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, Continuous p) ∧ (∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, star p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) ∧ (∀ x y : infU E n, x ≠ y → ∃ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, p x ≠ p y) ∧ (∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, (fun x => p x⁻¹) ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) ∧ ∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∃ (m : ℕ) (a b : Fin m → infU E n → ℂ), (∀ i, a i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j} ∧ b i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) ∧ ∀ x k, p (x * k) = ∑ i, a i x * b i k := by
  first
  | exact @_root_.GlobalTheory.CoordinateEmbeddingSplits.main
  | exact _root_.GlobalTheory.CoordinateEmbeddingSplits.main
  | (apply _root_.GlobalTheory.CoordinateEmbeddingSplits.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoordinateEmbeddingSplits.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoordinateEmbeddingSplits.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoordinateEmbeddingSplits.main ..)

end GlobalTheory.PolyRealU
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem _root_.GlobalTheory.T.fourfoldLattice_isometry_denominator_coprime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime (Ideal.absNorm cc) q → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → ∀ (G : (Fin 4 × D.what₂.Tau → D.host.K) ≃ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)), (∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E)) → ∀ x : Fin 4 → D.host.E, (∀ a, x a ∈ D.host.AA0) → ∃ s : ℕ, Nat.Coprime s q ∧ ∀ w, (s : D.host.K) * G (B.γ₀.g x) w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  first | exact @GlobalTheory.MomKapi.denom_prime_to | exact GlobalTheory.MomKapi.denom_prime_to | (intros; apply GlobalTheory.MomKapi.denom_prime_to <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.HomLocBasis

open GlobalTheory.PlaceInt.LocBasis Module

theorem exists_basis_primeTo {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (m : ℕ) (hm : 0 < m) (L : Submodule (𝓞 K) V) (hfg : L.FG) :
    ∃ (r : ℕ) (b : Fin r → V), LinearIndependent K b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, ∃ k : ℕ, Nat.Coprime k m ∧ k • w ∈ Submodule.span (𝓞 K) (Set.range b) := by
  first
  | exact @_root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime
  | exact _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime
  | (apply _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime ..)


open Formalism.MainNotions.TaylorLogMetric in
theorem exists_nnBasis : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), p.Prime → Nat.Coprime (Ideal.absNorm cc) p → TaylorLogMetric.admitted D N N' L L' → ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), TaylorLogMetric.NNBasis D (TaylorLogMetric.tor0 D cc δ) δ p L L' b := by
  intro D cc δ p N N' L L' hp hcc hA
  have hL : StandardLatticesGL3.SD D L := hA.2.2.1
  have hL' : StandardLatticesGL3.SD D L' := hA.2.2.2
  obtain ⟨s, y, y', hy, hy', hexp⟩ := GlobalTheory.HomDual.exists_dual_family_hom D
    (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'
  let Y : Submodule (𝓞 D.host.K) (Matrix (Fin N') (Fin N) D.host.E) :=
    Submodule.span (𝓞 D.host.K) (Set.range y)
  have hYle : ∀ x ∈ Y, x ∈ YYl D L L' := by
    intro x hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    exact (YYl D L L').sum_mem fun i _ => GlobalTheory.ThetaConj.smul_mem_YYl D L L' (c i) (hy i)
  have hYge : ∀ x ∈ YYl D L L', x ∈ Y := by
    intro x hx
    have hi : ∀ i, ∃ t : 𝓞 D.host.K, (t : D.host.K) = hYY D x (y' i) := fun i =>
      GlobalTheory.NormSum.TraceInt.hYY_integral D N N' L L' hL hL' x hx (y' i) (hy' i)
    choose t ht using hi
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨t, ?_⟩
    conv_rhs => rw [hexp x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ht]; rfl
  obtain ⟨r, b, hli, hb, hw⟩ := exists_basis_primeTo p hp.pos Y (Submodule.fg_span (Set.finite_range y))
  set n : ℕ := Ideal.absNorm cc with hn
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, Nat.coprime_zero_left] at hcc
    exact hp.one_lt.ne' hcc
  have hnK : (n : D.host.K) ≠ 0 := by exact_mod_cast hn0
  refine ⟨r, fun i => n • b i, ⟨?_, fun i => ?_, fun w hwY => ?_⟩, fun i => ?_⟩
  · have := hli.units_smul fun _ => Units.mk0 _ hnK
    have e : (fun i => n • b i) = (fun _ : Fin r => Units.mk0 _ hnK) • b := by
      funext i
      simp [Units.smul_def, Nat.cast_smul_eq_nsmul]
    rw [e]; exact this
  · refine ⟨1, by simp, ?_⟩
    rw [Nat.cast_one, one_smul]
    exact nsmul_mem (hYle _ (hb i)) n
  · obtain ⟨k, hk, hkw⟩ := hw w (hYge w hwY)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hkw
    refine ⟨n * k, Nat.Coprime.mul_left hcc hk, c, ?_⟩
    rw [Nat.cast_smul_eq_nsmul, mul_smul, ← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm]; rfl
  · refine AddSubgroup.subset_closure ⟨δ * n, AddSubgroup.subset_closure ⟨(n : 𝓞 D.host.K), Ideal.absNorm_mem cc, ?_⟩,
      b i, hYle _ (hb i), ?_⟩
    · simp
    · funext τ j k
      change δ * embT D τ ((n • b i) j k) = δ * n * embT D τ (b i j k)
      rw [Matrix.smul_apply, map_nsmul, nsmul_eq_mul, mul_assoc]

end GlobalTheory.HomLocBasis
end
