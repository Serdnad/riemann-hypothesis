module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle001
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ChartLatticeFinitelyGenerated
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.Style
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
public import ReciprocityTheory.SemistableReduction.Bundle003
public import Mathlib.NumberTheory.NumberField.Norm
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

namespace GlobalTheory.CompanionTheory.Ar.Cusp.GlobDet

section Index

variable {W : Type} [AddCommGroup W]

theorem relIndex_pair (Λ : AddSubgroup W) (M a : W →+ W) (hM : Function.Injective M)
    (hc : ∀ x, a (M x) = M (a x)) (h2 : Λ.map a ≤ Λ) (i2 : (Λ.map a).relIndex Λ ≠ 0)
    (h3 : Λ.map (a.comp M) ≤ Λ) (i3 : (Λ.map (a.comp M)).relIndex Λ ≠ 0) :
    Λ.relIndex (Λ.map M) ≠ 0 ∧ (Λ.map M).relIndex Λ ≠ 0 := by
  have e3 : Λ.map (a.comp M) = (Λ.map a).map M := by
    rw [AddSubgroup.map_map]
    congr 1
    ext x
    exact hc x
  have l1 : Λ.map (a.comp M) ≤ Λ.map M := by rw [e3]; exact AddSubgroup.map_mono h2
  have n1 : (Λ.map (a.comp M)).relIndex (Λ.map M) ≠ 0 := by
    rw [e3, AddSubgroup.relIndex_map_map_of_injective _ _ hM]; exact i2
  have o1 : (Λ.map M).relIndex (Λ.map (a.comp M)) ≠ 0 := by
    rw [AddSubgroup.relIndex_eq_one.2 l1]; exact one_ne_zero
  have o3 : Λ.relIndex (Λ.map (a.comp M)) ≠ 0 := by
    rw [AddSubgroup.relIndex_eq_one.2 h3]; exact one_ne_zero
  exact ⟨AddSubgroup.relIndex_ne_zero_trans o3 n1, AddSubgroup.relIndex_ne_zero_trans o1 i3⟩

end Index

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

noncomputable def mulVecHom (T : Matrix (Fin n) (Fin n) L) : (Fin n → L) →+ (Fin n → L) :=
  AddMonoidHom.mk' (fun x => T *ᵥ x) (Matrix.mulVec_add T)

theorem mulVecHom_apply (T : Matrix (Fin n) (Fin n) L) (x : Fin n → L) : mulVecHom T x = T *ᵥ x := rfl

theorem frame_eq_map (T : Matrix (Fin n) (Fin n) L) :
    (frame T).toAddSubgroup = (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.map (mulVecHom T) := by
  ext x
  rw [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, mem_frame]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨_, (Submodule.mem_toAddSubgroup _).2 (mem_frame.2 ⟨z, by simp⟩), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := mem_frame.1 ((Submodule.mem_toAddSubgroup _).1 hy)
    exact ⟨z, by simp [mulVecHom_apply]⟩

theorem frame_map_le (D : Matrix (Fin n) (Fin n) (𝓞 L)) :
    frame (D.map (algebraMap (𝓞 L) L)) ≤ frame (1 : Matrix (Fin n) (Fin n) L) := by
  rw [frame, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact mem_frame_one.2 fun i => ⟨D i k, rfl⟩

theorem log_abs_norm (x : 𝓞 L) (hx : x ≠ 0) :
    Real.log ((|Algebra.norm ℤ x| : ℤ) : ℝ) = ∑ σ : L →+* ℂ, Real.log ‖σ (algebraMap (𝓞 L) L x)‖ := by
  have hx' : algebraMap (𝓞 L) L x ≠ 0 := by simpa using hx
  rw [← Real.log_prod (fun σ _ => norm_ne_zero_iff.2 ((map_ne_zero σ).2 hx'))]
  congr 1
  have h1 : ∏ σ : L →+* ℂ, σ (algebraMap (𝓞 L) L x) =
      algebraMap ℚ ℂ (Algebra.norm ℚ (algebraMap (𝓞 L) L x)) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ (algebraMap (𝓞 L) L x)]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ _
      (fun σ => by simp [RingHom.equivRatAlgHom_apply])
  rw [← norm_prod, h1, ← Algebra.coe_norm_int x]
  simp

theorem relIndex_frame (D : Matrix (Fin n) (Fin n) (𝓞 L)) (hD : D.det ≠ 0) :
    (((frame (D.map (algebraMap (𝓞 L) L))).toAddSubgroup.relIndex
      (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup : ℕ) : ℤ) = |Algebra.norm ℤ D.det| := by
  have hb : LinearIndependent L (fun k j => (1 : Matrix (Fin n) (Fin n) L) j k) := by
    have e : (fun k j => (1 : Matrix (Fin n) (Fin n) L) j k) = ⇑(Pi.basisFun L (Fin n)) := by
      funext k j
      simp [Matrix.one_apply, Pi.single_apply]
    rw [e]
    exact (Pi.basisFun L (Fin n)).linearIndependent
  have h := ReciprocityTheory.MultiplicativeHeights.relIndex_span_comb _ hb D hD
  have e : frame (D.map (algebraMap (𝓞 L) L)) = Submodule.span (𝓞 L)
      (Set.range fun j => ∑ i, D i j • fun l => (1 : Matrix (Fin n) (Fin n) L) l i) := by
    rw [frame]
    congr 2
    funext k j
    simp [Finset.sum_apply, Matrix.one_apply, Algebra.smul_def]
  rw [e]
  exact h

theorem relIndex_frame_ne (D : Matrix (Fin n) (Fin n) (𝓞 L)) (hD : D.det ≠ 0) :
    (frame (D.map (algebraMap (𝓞 L) L))).toAddSubgroup.relIndex
      (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup ≠ 0 := by
  intro h
  have h1 := relIndex_frame D hD
  rw [h, Nat.cast_zero, eq_comm, abs_eq_zero, Algebra.norm_eq_zero_iff] at h1
  exact hD h1

theorem log_relIndex_frame (D : Matrix (Fin n) (Fin n) (𝓞 L)) (hD : D.det ≠ 0) :
    Real.log (((frame (D.map (algebraMap (𝓞 L) L))).toAddSubgroup.relIndex
      (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup : ℕ) : ℝ) =
      ∑ σ : L →+* ℂ, Real.log ‖σ (algebraMap (𝓞 L) L D.det)‖ := by
  rw [← log_abs_norm _ hD, ← relIndex_frame D hD]
  simp

theorem exists_int_matrix (C : Matrix (Fin n) (Fin n) L) :
    ∃ (d : 𝓞 L) (D : Matrix (Fin n) (Fin n) (𝓞 L)), d ≠ 0 ∧
      D.map (algebraMap (𝓞 L) L) = algebraMap (𝓞 L) L d • C := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 L))
    (fun p : Fin n × Fin n => C p.1 p.2)
  choose D hD using hb
  refine ⟨b, Matrix.of fun i j => D (i, j), nonZeroDivisors.ne_zero b.2, ?_⟩
  ext i j
  simpa [Algebra.smul_def] using hD (i, j)

theorem coe_det (D : Matrix (Fin n) (Fin n) (𝓞 L)) :
    algebraMap (𝓞 L) L D.det = (D.map (algebraMap (𝓞 L) L)).det := by
  rw [RingHom.map_det]
  rfl

theorem gIdx_frame : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (C : Matrix (Fin n) (Fin n) L),
    C.det ≠ 0 →
    (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.relIndex (frame C).toAddSubgroup ≠ 0 ∧
    (frame C).toAddSubgroup.relIndex (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup ≠ 0 ∧
    gIdx (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup (frame C).toAddSubgroup =
      ∑ σ : L →+* ℂ, Real.log ‖σ C.det‖ := by
  intro L _ _ n C hC
  obtain ⟨d, D, hd, hDC⟩ := exists_int_matrix C
  have hδ : algebraMap (𝓞 L) L d ≠ 0 := by simpa using hd
  obtain ⟨δ, hδe⟩ : ∃ δ, δ = algebraMap (𝓞 L) L d := ⟨_, rfl⟩
  rw [← hδe] at hDC hδ
  obtain ⟨S, hSe⟩ : ∃ S : Matrix (Fin n) (Fin n) (𝓞 L), S = d • 1 := ⟨_, rfl⟩
  have hS : S.map (algebraMap (𝓞 L) L) = δ • 1 := by
    ext i j
    by_cases h : i = j <;> simp [hSe, hδe, Matrix.smul_apply, Matrix.one_apply, h]
  have hSdet : S.det = d ^ n := by simp [hSe, Matrix.det_smul]
  have hDdet : algebraMap (𝓞 L) L D.det = δ ^ n * C.det := by
    rw [coe_det, hDC, Matrix.det_smul, Fintype.card_fin]
  have hS0 : S.det ≠ 0 := by rw [hSdet]; exact pow_ne_zero _ hd
  have hD0 : D.det ≠ 0 := by
    intro h
    rw [h, map_zero] at hDdet
    exact mul_ne_zero (pow_ne_zero _ hδ) hC hDdet.symm
  set Λ := (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup with hΛ
  have ea : Λ.map (mulVecHom (δ • 1)) = (frame (S.map (algebraMap (𝓞 L) L))).toAddSubgroup := by
    rw [hS, frame_eq_map]
  have eM : (mulVecHom (δ • 1)).comp (mulVecHom C) = mulVecHom (D.map (algebraMap (𝓞 L) L)) := by
    refine AddMonoidHom.ext fun x => ?_
    simp [mulVecHom_apply, hDC, Matrix.smul_mulVec]
  have eaM : Λ.map ((mulVecHom (δ • 1)).comp (mulVecHom C)) =
      (frame (D.map (algebraMap (𝓞 L) L))).toAddSubgroup := by
    rw [eM, frame_eq_map]
  have hc : ∀ x, mulVecHom (δ • 1) (mulVecHom C x) = mulVecHom C (mulVecHom (δ • 1) x) := by
    intro x
    simp [mulVecHom_apply, Matrix.smul_mulVec, Matrix.mulVec_smul]
  have hinj : Function.Injective (mulVecHom C) :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det C).2 (IsUnit.mk0 _ hC))
  have h2 : Λ.map (mulVecHom (δ • 1)) ≤ Λ := by
    rw [ea]; exact fun x hx => frame_map_le S hx
  have i2 : (Λ.map (mulVecHom (δ • 1))).relIndex Λ ≠ 0 := by
    rw [ea]; exact relIndex_frame_ne S hS0
  have h3 : Λ.map ((mulVecHom (δ • 1)).comp (mulVecHom C)) ≤ Λ := by
    rw [eaM]; exact fun x hx => frame_map_le D hx
  have i3 : (Λ.map ((mulVecHom (δ • 1)).comp (mulVecHom C))).relIndex Λ ≠ 0 := by
    rw [eaM]; exact relIndex_frame_ne D hD0
  obtain ⟨p1, p2⟩ := relIndex_pair Λ _ _ hinj hc h2 i2 h3 i3
  have hf := GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.gIdx_frac Λ _ _ hinj hc h2 i2 h3 i3
  rw [ea, eaM, log_relIndex_frame S hS0, log_relIndex_frame D hD0] at hf
  have eC : (frame C).toAddSubgroup = Λ.map (mulVecHom C) := frame_eq_map C
  refine ⟨by rw [eC]; exact p1, by rw [eC]; exact p2, ?_⟩
  rw [eC, gIdx_swap, hf]
  have hsum : ∀ σ : L →+* ℂ, Real.log ‖σ (algebraMap (𝓞 L) L D.det)‖ =
      Real.log ‖σ (algebraMap (𝓞 L) L S.det)‖ + Real.log ‖σ C.det‖ := by
    intro σ
    have a1 : ‖σ (algebraMap (𝓞 L) L S.det)‖ ≠ 0 := by
      rw [norm_ne_zero_iff, map_ne_zero, hSdet, map_pow, ← hδe]
      exact pow_ne_zero _ hδ
    have a2 : ‖σ C.det‖ ≠ 0 := by
      rw [norm_ne_zero_iff, map_ne_zero]; exact hC
    rw [← Real.log_mul a1 a2, ← norm_mul, ← map_mul, hDdet, hSdet, map_pow, ← hδe]
  simp_rw [hsum]
  rw [Finset.sum_add_distrib]
  ring

end GlobalTheory.CompanionTheory.Ar.Cusp.GlobDet
end

section

open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex

variable {L : Type} [Field L] [NumberField L] {W : Type} [AddCommGroup W] [Module (𝓞 L) W]

def cond (A B : Submodule (𝓞 L) W) : Ideal (𝓞 L) where
  carrier := {u | ∀ x ∈ A, u • x ∈ B}
  add_mem' := fun {a b} ha hb x hx => by
    rw [add_smul]; exact B.add_mem (ha x hx) (hb x hx)
  zero_mem' := fun x _ => by rw [zero_smul]; exact B.zero_mem
  smul_mem' := fun c u hu x hx => by
    rw [smul_eq_mul, mul_smul]; exact B.smul_mem c (hu x hx)

theorem mem_cond {A B : Submodule (𝓞 L) W} {u : 𝓞 L} :
    u ∈ cond A B ↔ ∀ x ∈ A, u • x ∈ B := Iff.rfl

theorem exists_reps {A B : Submodule (𝓞 L) W}
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0) :
    ∃ S : Finset W, (∀ r ∈ S, r ∈ A) ∧ ∀ x ∈ A, ∃ r ∈ S, x - r ∈ B := by
  classical
  have hQ : Finite (A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero hfin
  have := Fintype.ofFinite (A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup)
  refine ⟨Finset.univ.image
    (fun q : A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup =>
      ((Quotient.out q : A.toAddSubgroup) : W)), ?_, ?_⟩
  · intro r hr
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hr
    exact (Quotient.out q).2
  · intro x hx
    let q : A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup :=
      QuotientAddGroup.mk ⟨x, hx⟩
    refine ⟨((Quotient.out q : A.toAddSubgroup) : W),
      Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩, ?_⟩
    have hq : (QuotientAddGroup.mk (Quotient.out q) :
        A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup) = q := Quotient.out_eq q
    have h := QuotientAddGroup.eq.mp hq
    rw [AddSubgroup.mem_addSubgroupOf] at h
    have h' : -((Quotient.out q : A.toAddSubgroup) : W) + x ∈ B := h
    rwa [neg_add_eq_sub] at h'

theorem cond_ne_bot {A B : Submodule (𝓞 L) W}
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0) : cond A B ≠ ⊥ := by
  intro hbot

  have hmem : ((B.toAddSubgroup.relIndex A.toAddSubgroup : ℕ) : 𝓞 L) ∈ cond A B := by
    refine mem_cond.mpr fun x hx => ?_
    rw [Nat.cast_smul_eq_nsmul]
    exact AddSubgroup.nsmul_relIndex_mem B.toAddSubgroup hx
  rw [hbot, Ideal.mem_bot] at hmem
  exact hfin (Nat.cast_eq_zero.mp hmem)

theorem exists_mem_cond_notMem {A B : Submodule (𝓞 L) W} (w : FinitePlace L)
    (hloc : locAt w A = locAt w B)
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0) :
    ∃ s ∈ cond A B, s ∉ w.maximalIdeal.asIdeal := by
  classical
  obtain ⟨S, hSA, hS⟩ := exists_reps hfin
  have hex : ∀ r ∈ S, ∃ t : 𝓞 L, t ∉ w.maximalIdeal.asIdeal ∧ t • r ∈ B := by
    intro r hr
    have hr' : r ∈ locAt w B := by rw [← hloc]; exact le_locAt w A (hSA r hr)
    exact mem_locAt.mp hr'
  choose! t ht using hex
  have := w.maximalIdeal.isPrime
  refine ⟨∏ r ∈ S, t r, mem_cond.mpr fun x hx => ?_, ?_⟩
  · obtain ⟨r, hr, hxr⟩ := hS x hx
    have hrB : (∏ r ∈ S, t r) • r ∈ B := by
      rw [← Finset.mul_prod_erase S t hr, mul_comm, mul_smul]
      exact B.smul_mem _ (ht r hr).2
    have hx' : x = r + (x - r) := by abel
    rw [hx', smul_add]
    exact B.add_mem hrB (B.smul_mem _ hxr)
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨r, hr, hmem⟩
    exact (ht r hr).1 hmem

theorem cond_sup_span_eq_top {A B : Submodule (𝓞 L) W} (v : FinitePlace L)
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0)
    (hloc : ∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w B)
    {t : 𝓞 L} (ht : t ∉ v.maximalIdeal.asIdeal) : cond A B ⊔ Ideal.span {t} = ⊤ := by
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  have hPbot : P ≠ ⊥ := by
    intro hP
    apply cond_ne_bot hfin
    rw [eq_bot_iff, ← hP]
    exact le_sup_left.trans hle
  obtain ⟨Q, hQ⟩ : ∃ Q : HeightOneSpectrum (𝓞 L), Q.asIdeal = P :=
    ⟨⟨P, hPmax.isPrime, hPbot⟩, rfl⟩
  by_cases hw : FinitePlace.mk Q = v
  · apply ht
    rw [← hw, FinitePlace.maximalIdeal_mk, hQ]
    exact hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self t))
  · obtain ⟨s, hs, hsP⟩ := exists_mem_cond_notMem (FinitePlace.mk Q) (hloc _ hw) hfin
    apply hsP
    rw [FinitePlace.maximalIdeal_mk, hQ]
    exact hle (Ideal.mem_sup_left hs)

theorem exists_bezout {A B : Submodule (𝓞 L) W} (v : FinitePlace L)
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0)
    (hloc : ∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w B)
    {t : 𝓞 L} (ht : t ∉ v.maximalIdeal.asIdeal) :
    ∃ s u : 𝓞 L, u ∈ cond A B ∧ s * t + u = 1 := by
  have h1 : (1 : 𝓞 L) ∈ cond A B ⊔ Ideal.span {t} := by
    rw [cond_sup_span_eq_top v hfin hloc ht]; exact Submodule.mem_top
  obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.mp h1
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  exact ⟨s, u, hu, by rw [add_comm]; exact huz⟩

theorem relIndex_locAt (L : Type) [Field L] [NumberField L] (W : Type) [AddCommGroup W]
    [Module (𝓞 L) W] (v : FinitePlace L) (A B : Submodule (𝓞 L) W) (hBA : B ≤ A)
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0)
    (hloc : ∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w B) :
    (locAt v B).toAddSubgroup.relIndex (locAt v A).toAddSubgroup =
      B.toAddSubgroup.relIndex A.toAddSubgroup := by
  have hle : A.toAddSubgroup ≤ (locAt v A).toAddSubgroup := fun x hx => le_locAt v A hx

  have hback : ∀ x ∈ A, x ∈ locAt v B → x ∈ B := by
    intro x hxA hx
    obtain ⟨t, ht, htx⟩ := mem_locAt.mp hx
    obtain ⟨s, u, hu, hsu⟩ := exists_bezout v hfin hloc ht
    have hx' : x = s • (t • x) + u • x := by rw [smul_smul, ← add_smul, hsu, one_smul]
    rw [hx']
    exact B.add_mem (B.smul_mem s htx) (mem_cond.mp hu x hxA)

  let f := (QuotientAddGroup.mk' ((locAt v B).toAddSubgroup.addSubgroupOf
    (locAt v A).toAddSubgroup)).comp (AddSubgroup.inclusion hle)
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
    obtain ⟨t, ht, hty⟩ := mem_locAt.mp hy
    obtain ⟨s, u, hu, hsu⟩ := exists_bezout v hfin hloc ht
    refine ⟨⟨s • (t • y), A.smul_mem s hty⟩, ?_⟩
    simp only [f, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply]
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    show -(s • (t • y)) + y ∈ locAt v B
    have hu' : u = 1 - s * t := by rw [← hsu]; ring
    have hyeq : -(s • (t • y)) + y = u • y := by
      rw [hu', sub_smul, one_smul, smul_smul, neg_add_eq_sub]
    rw [hyeq]
    exact mem_locAt.mpr ⟨t, ht, by rw [smul_comm]; exact mem_cond.mp hu _ hty⟩
  have hker : f.ker = B.toAddSubgroup.addSubgroupOf A.toAddSubgroup := by
    ext ⟨x, hx⟩
    simp only [f, AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_inclusion,
      Submodule.mem_toAddSubgroup]
    exact ⟨fun h => hback x hx h, fun h => le_locAt v B h⟩
  unfold AddSubgroup.relIndex
  rw [← hker, AddSubgroup.index_eq_card, AddSubgroup.index_eq_card]
  exact (Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv).symm

end GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem isDomain_and_isIntegrallyClosed_stalk_sp_field (K : Type) [Field K] (y : Sp K) :
    IsDomain ((Sp K).presheaf.stalk y) ∧ IsIntegrallyClosed ((Sp K).presheaf.stalk y) := by
  let p : PrimeSpectrum K := y
  have hle : p.asIdeal.primeCompl ≤ IsUnit.submonoid K := fun x hx =>
    isUnit_iff_ne_zero.2 fun h0 => hx (h0 ▸ p.asIdeal.zero_mem)
  let e₁ : K ≃+* Localization.AtPrime p.asIdeal :=
    (IsLocalization.atUnits K p.asIdeal.primeCompl hle).toRingEquiv
  let e₂ : (Sp K).presheaf.stalk y ≃+* Localization.AtPrime p.asIdeal :=
    (AlgebraicGeometry.Spec.stalkIso (CommRingCat.of K) p).commRingCatIsoToRingEquiv
  let e : K ≃+* (Sp K).presheaf.stalk y := e₁.trans e₂.symm
  haveI := Field.instIsIntegrallyClosed K
  exact ⟨(MulEquiv.isField (Field.toIsField K) e.symm.toMulEquiv).isDomain, IsIntegrallyClosed.of_equiv e⟩

theorem isDomain_stalk_of_smoothOfRelativeDimension_field (K : Type) [Field K] (e : ℕ)
    (X : Scheme.{0}) (g : X ⟶ Sp K) (hg : SmoothOfRelativeDimension e g) (x : X) :
    IsDomain (X.presheaf.stalk x) := by
  haveI : Smooth g := SmoothOfRelativeDimension.smooth e g
  exact (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth g
    (isDomain_and_isIntegrallyClosed_stalk_sp_field K) x).1

end GlobalTheory.CompanionTheory.Ar.SncBase
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.normal_codim_one_stalk_dvr : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X], IsNormalScheme X → ∀ p : X, ringKrullDim (X.presheaf.stalk p) = 1 → ∃ _ : IsDomain (X.presheaf.stalk p), IsDiscreteValuationRing (X.presheaf.stalk p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.stalk_isDiscreteValuationRing_of_dim_one | exact GlobalTheory.CompanionTheory.Ar.stalk_isDiscreteValuationRing_of_dim_one | (intros; apply GlobalTheory.CompanionTheory.Ar.stalk_isDiscreteValuationRing_of_dim_one <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace GlobalTheory.CompanionTheory.Ar.Geo

theorem chartBundle_lat_fg : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (B : ChartBundle O x r (Fin r → Ω)) (c : ι), x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ B.lat c) ∧
      ∀ e ∈ B.lat c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k :=
  PositivityTheory.Xgn.chart_lattice_finitely_generated

end GlobalTheory.CompanionTheory.Ar.Geo
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_pullback_equivalence : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (R : Type) [CommRing R] (x' : Sp R ⟶ S') (E : Type) [AddCommGroup E] [Module R E], (∀ M : LieModel G (x' ≫ f) E, ∃ M' : LieModel G' x' E, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left) ∧ ∀ M' : LieModel G' x' E, ∃ M : LieModel G (x' ≫ f) E, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback | exact GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback | (intros; apply GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback <;> assumption)
end
