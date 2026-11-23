module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle030
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Formalism.LocalRingCardinality.Bundle001
public import Formalism.LocalRingCardinality.DataHost
public import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

private theorem UpperTheory.Reformulated.B.Gc1.kset_subset {n : ℕ} (ε : Fin n → Bool) :
    PI.UpqRep.Kset ε ⊆ PI.UpqRep.UJset ε := by
  intro g hg
  have h1 : star g * g = 1 := (Matrix.mem_unitaryGroup_iff' ).1 hg.1
  show g.conjTranspose * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, h1, Matrix.one_mul]

theorem UpperTheory.Reformulated.B.Gc1.kFinStab :
    CompanionTheory.D.DSIC.KFinStab := by
  intro n ε H _ _ σ S E _ hS
  obtain ⟨V₀, h1, h2⟩ := UpperTheory.exists_invariant_subspace H (Matrix (Fin n) (Fin n) ℂ) (Fin n × Fin n) (PI.UpqRep.Kset ε)
    (fun g => (σ g : H →ₗ[ℂ] H)) S (fun p => E p.1 p.2)
    (fun g p q => g q.1 p.1 * g⁻¹ p.2 q.2)
    (fun g hg v hv => hS.stab g (UpperTheory.Reformulated.B.Gc1.kset_subset ε hg) v hv)
    (fun g hg p v w hw => by
      rw [Fintype.sum_prod_type]
      exact hS.conj g (UpperTheory.Reformulated.B.Gc1.kset_subset ε hg) p.1 p.2 v w hw)
  exact ⟨V₀, h1, fun a b => h2 (a, b)⟩
end

section

theorem UpperTheory.Reformulated.B.PrimeApproximation.yPrime_approx :
    ∀ {R σ : Type} [inst : CommRing R] {y : σ → R} {f : R} {BB : Type} [inst_1 : CommRing BB] [inst_2 : Algebra R BB],
      UpperTheory.V.Pa.Core.IsYCpl y f BB →
        ∀ (n : ℕ) (J : Ideal R),
          ∀ x ∈ Ideal.map (Algebra.algebraMap R BB) J,
            ∃ (k : ℕ),
              ∃ a ∈ J,
                (Algebra.algebraMap R BB : R → BB) f ^ k * x - (Algebra.algebraMap R BB : R → BB) a ∈
                  Ideal.map (Algebra.algebraMap R BB) (Ideal.span (Set.range y) ^ n) := by
  intro R σ _ y f BB _ _ h n J x hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨0, a, ha, ?_⟩
    rw [pow_zero, one_mul, sub_self]
    exact Ideal.zero_mem _
  · refine ⟨0, 0, J.zero_mem, ?_⟩
    rw [mul_zero, map_zero, sub_self]
    exact Ideal.zero_mem _
  · rintro u v - - ⟨k, a, ha, hu⟩ ⟨m, b, hb, hv⟩
    refine ⟨k + m, f ^ m * a + f ^ k * b,
      J.add_mem (J.mul_mem_left _ ha) (J.mul_mem_left _ hb), ?_⟩
    have key := Ideal.add_mem _
      (Ideal.mul_mem_left _ (algebraMap R BB f ^ m) hu)
      (Ideal.mul_mem_left _ (algebraMap R BB f ^ k) hv)
    convert key using 1
    simp only [map_add (f := _), map_mul, map_pow]
    ring
  · rintro c u - ⟨k, a, ha, hu⟩
    obtain ⟨j, r, hr⟩ := h.dense n c
    refine ⟨j + k, r * a, J.mul_mem_left _ ha, ?_⟩
    have key := Ideal.add_mem _
      (Ideal.mul_mem_left _ (algebraMap R BB f ^ j * c) hu)
      (Ideal.mul_mem_right (algebraMap R BB a) _ hr)
    convert key using 1
    simp only [map_mul, smul_eq_mul]
    ring
end

section

theorem UpperTheory.Reformulated.B.Qm13.cov_of_local :
    ∀ {O : Type} [inst : CommRing O] {X : AlgebraicGeometry.Scheme} (Q : X.Opens → Prop)
    (q : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of O)) [AlgebraicGeometry.IsSeparated q]
    [AlgebraicGeometry.QuasiCompact q],
    (∀ (x : ↥X), ∃ (V : X.Opens) (d : ℕ), x ∈ V ∧ Q V ∧ Nonempty (CrystallineSemistableComparison.Pb.Coord q V d)) →
      ∃ (U : CrystallineSemistableComparison.Pb.Cov q),
        ∀ (α : U.ι),
          Q
            (U.U
              α) := by
  intro O _ X Q q _ _ h
  choose V d hx hQ hc using h
  have : CompactSpace X := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace q
  have : X.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from q]; infer_instance⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  refine ⟨⟨s, fun a => V a, fun a => d a, fun a => (hc a).some, ?_, fun S hS => ?_⟩, fun a => hQ _⟩
  · refine top_le_iff.1 fun x _ => ?_
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩
  · exact AlgebraicGeometry.IsAffineOpen.biInf (S : Set s) S.finite_toSet hS
      fun a _ => (hc a).some.affine
end

section

private theorem UpperTheory.Reformulated.B.Qh47.exists_nat_mul_integral {E : Type} [Field E] [NumberField E]
    (a : E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : E) * a) := by
  have hq : IsAlgebraic ℚ a := Algebra.IsAlgebraic.isAlgebraic a
  have hz : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 hq
  obtain ⟨y, hy, hi⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hi
  rcases Int.natAbs_eq y with h | h
  · have h2 : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [h]
      exact (Int.cast_natCast _).symm
    rw [h2]; exact hi
  · have h2 : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [h]
      rw [Int.cast_neg, neg_neg, Int.cast_natCast]
    rw [h2, neg_mul]; exact hi.neg

theorem UpperTheory.Reformulated.B.Qh47.m_exists_nat_smul_mem :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : StarRing E] {S : Formalism.BasicNotions.HSpace E}
      (M : Submodule (NumberField.RingOfIntegers E) S.V) {x : S.V},
      x ∈ Submodule.span E (↑M : Set S.V) → ∃ (n : ℕ), (0 : ℕ) < n ∧ n • x ∈ M := by
  intro E _ _ _ S M x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_pos, by rw [one_smul]; exact M.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨n, hn, hny⟩ := hy
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hmx n
    · rw [mul_smul]; exact nsmul_mem hny m
  | smul a x _ hx =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨n, hn, hi⟩ := UpperTheory.Reformulated.B.Qh47.exists_nat_mul_integral a
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    obtain ⟨b, hb⟩ : ∃ b : NumberField.RingOfIntegers E, algebraMap _ E b = (n : E) * a :=
      ⟨⟨(n : E) * a, hi⟩, rfl⟩
    have e : (n * m) • a • x = b • m • x := by
      rw [mul_smul n m, smul_comm m a x, ← algebraMap_smul E b, hb, mul_smul,
        Nat.cast_smul_eq_nsmul]
    rw [e]
    exact M.smul_mem b hmx
end

section

noncomputable def UpperTheory.Reformulated.B.EmbeddingTypeJumps.crd :
    {E : Type} →
      [inst : Field E] → [inst_1 : NumberField E] → [inst_2 : StarRing E] → (W : Formalism.BasicNotions.HSpace E) → Set (Fin W.rank → E) :=
    fun {E : Type} [Field E] [NumberField E] [StarRing E] (W : Formalism.BasicNotions.HSpace E) ↦
      {x : Fin W.rank → E | ∑ i : Fin W.rank, x i • (W.frame : Fin W.rank → W.V) i ∈ W.L0}

private theorem UpperTheory.Reformulated.B.EmbeddingTypeJumps.integral_smul_mem {E : Type} [Field E] [NumberField E] [StarRing E]
    (W : Formalism.BasicNotions.HSpace E) {a : E} (ha : IsIntegral ℤ a) {v : W.V} (hv : v ∈ W.L0) :
    a • v ∈ W.L0 := by
  let b : NumberField.RingOfIntegers E := ⟨a, ha⟩
  have h : (algebraMap (NumberField.RingOfIntegers E) E b) • v ∈ W.L0 := by
    rw [algebraMap_smul]
    exact W.L0.smul_mem b hv
  exact h

private theorem UpperTheory.Reformulated.B.EmbeddingTypeJumps.exists_int_smul_mem {E : Type} [Field E] [NumberField E] [StarRing E]
    (W : Formalism.BasicNotions.HSpace E) (v : W.V) : ∃ n : ℤ, n ≠ 0 ∧ (n : E) • v ∈ W.L0 := by
  classical
  have := W.standardTuple_isLattice
  obtain ⟨s, hs⟩ := Submodule.IsLattice.fg E W.L0
  obtain ⟨n, hn, hgen⟩ := exists_integral_multiples ℤ ℚ (s.image (W.hT v))
  refine ⟨n, hn, ?_⟩
  rw [Int.cast_smul_eq_zsmul E]
  let f := (W.hT (n • v)).restrictScalars (NumberField.RingOfIntegers E)
  have hpair : W.L0 ≤ (1 : Submodule (NumberField.RingOfIntegers E) E).comap f := by
    rw [← hs, Submodule.span_le]
    intro y hy
    have hint := hgen (W.hT v y) (Finset.mem_image_of_mem (W.hT v) hy)
    apply Submodule.mem_one.mpr
    refine ⟨⟨n • W.hT v y, hint⟩, ?_⟩
    change n • W.hT v y = W.hT (n • v) y
    rw [map_zsmul]
    exact (map_zsmul (LinearMap.evalAddMonoidHom y) n (W.hT v)).symm
  have hself : Formalism.HermitianLatticesTheory.dual W.hT W.L0 = W.L0 :=
    W.baseLattice_isUnimodular
  rw [← hself]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf,
    Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
  intro y hy
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hpair hy)
  have hint : IsIntegral ℤ (W.hT (n • v) y) := ha ▸ a.property
  have hstar := hint.map_of_comp_eq (RingHom.id ℤ) (starRingEnd E) (by ext <;> simp)
  rw [W.herm.eq (n • v) y] at hstar
  exact ⟨⟨_, hstar⟩, rfl⟩

theorem UpperTheory.Reformulated.B.EmbeddingTypeJumps.crd_low :
    ∀ {F E : Type} [inst : Field F] [NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E]
      [inst_5 : StarRing E] (W : Formalism.BasicNotions.HSpace E),
      ∃ (c : NumberField.RingOfIntegers F),
        c ≠ (0 : NumberField.RingOfIntegers F) ∧
          ∀ (i : Fin W.rank) (e : E), IsIntegral ℤ e → Pi.single i ((↑c : F) • e) ∈ UpperTheory.Reformulated.B.EmbeddingTypeJumps.crd W := by
  intro F E _ _ _ _ _ _ W
  choose n hn hmem using fun i : Fin W.rank => UpperTheory.Reformulated.B.EmbeddingTypeJumps.exists_int_smul_mem W (W.frame i)
  refine ⟨((∏ i, n i : ℤ) : NumberField.RingOfIntegers F), ?_, ?_⟩
  · exact Int.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hn i)
  · intro i e he
    obtain ⟨k, hk⟩ : n i ∣ ∏ j, n j := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
    have hk' : IsIntegral ℤ (k • e) := he.smul k
    have hm := UpperTheory.Reformulated.B.EmbeddingTypeJumps.integral_smul_mem W hk' (hmem i)
    have hc : ((((∏ j, n j : ℤ) : NumberField.RingOfIntegers F) : F)) • e = (k • e) * (n i : E) := by
      rw [hk, Algebra.smul_def, NumberField.RingOfIntegers.coe_eq_algebraMap, map_intCast,
        map_intCast, zsmul_eq_mul, Int.cast_mul]
      ring
    show ∑ j : Fin W.rank, (Pi.single i _ : Fin W.rank → E) j • W.frame j ∈ W.L0
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, hc, mul_smul]
    exact hm
end

section

theorem UpperTheory.Reformulated.B.Rc9.conj_sqrt :
    ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R),
    (H.conj : H.E → H.E) H.sqd =
      -H.sqd := by
  intro R H
  have h := H.gal_sqd H.conj
  have hc : H.gal H.conj = R.toFrame.cc := H.gal.apply_symm_apply _
  have h2 : (R.toFrame.cc).1.2 = -1 := rfl
  rw [hc, h2] at h
  simpa using h
end

section

attribute [local instance] Subfield.toField._proof_1 SubfieldClass.toField._proof_12 SubringClass.toRing._proof_8

theorem UpperTheory.Reformulated.B.Qj12.exists_prime_of_different_le :
    ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥H.F)),
    differentIdeal ℤ (NumberField.RingOfIntegers ↥H.F) ≤ v.asIdeal →
      ∃ (p : ℕ),
        Nat.Prime p ∧
          p ∣ H.QS * H.q * H.d ∧
            (↑p : NumberField.RingOfIntegers ↥H.F) ∈
              v.asIdeal := by
  intro R H v h
  have h1 := h (Ideal.absNorm_mem _)
  rw [NumberField.absNorm_differentIdeal H.F] at h1
  have h0 : (NumberField.discr H.F).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero H.F)
  rw [← Nat.prod_primeFactorsList h0, Nat.cast_list_prod, ← Multiset.prod_coe] at h1
  obtain ⟨x, hx, hxv⟩ := (v.isPrime.multiset_prod_mem_iff_exists_mem _).1 h1
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 hx)
  have hpp := Nat.prime_of_mem_primeFactorsList hp
  refine ⟨p, hpp, H.der.discr_primes.1 p hpp ?_, hxv⟩
  rw [H.der.discr_sq]
  exact (Int.natCast_dvd.2 (Nat.dvd_of_mem_primeFactorsList hp)).trans (dvd_pow_self _ two_ne_zero)
end
