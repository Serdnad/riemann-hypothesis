module

public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.Topology.Instances.Matrix
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Dec.{u_1, u_2} :
    {F : Type u_1} →
      {Ω : Type u_2} →
        [inst : Field F] →
          [inst_1 : Field Ω] → [inst_2 : Algebra F Ω] → ValuationSubring Ω → Subgroup (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G F Ω) :=
    fun {F : Type u_1} {Ω : Type u_2} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω) ↦
      ValuationSubring.decompositionSubgroup F A

noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.FreeRatios :
    {κ ι : Type} → [inst : Field κ] → (ι → κˣ) → Prop :=
    fun {κ ι : Type} [Field κ] (α : ι → κˣ) ↦ ∀ (i j : ι), i ≠ j → ∀ (m : ℕ), (0 : ℕ) < m → α i ^ m ≠ α j ^ m

noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.mat :
    {H k : Type} → [inst : Group H] → [inst_1 : CommRing k] → {n : ℕ} → (H →* GL (Fin n) k) → H →* Matrix (Fin n) (Fin n) k :=
    fun {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k) ↦
      (Units.coeHom (Matrix (Fin n) (Fin n) k)).comp r

noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.FreeAt :
    (l : ℕ) →
      [inst : Fact (Nat.Prime l)] →
        {F Ω : Type} →
          [inst_1 : Field F] →
            [inst_2 : Field Ω] →
              [inst_3 : Algebra F Ω] → {n : ℕ} → (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G F Ω →* GL (Fin n) (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l)) → Prop :=
    fun (l : ℕ) [Fact (Nat.Prime l)] {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {n : ℕ}
        (r : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G F Ω →* GL (Fin n) (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l)) ↦
      ∀ (A : ValuationSubring Ω),
        (A.valuation : Ω → A.ValueGroup) (↑l : Ω) < (1 : A.ValueGroup) →
          ∃ g ∈ UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Dec A,
            (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.cycZ F Ω l : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G F Ω → ℤ_[l]ˣ) g = (1 : ℤ_[l]ˣ) ∧
              ∃ (α : Fin n → (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l)ˣ),
                UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.FreeRatios α ∧
                  ((UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.mat r : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G F Ω → Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l))
                        g).charpoly =
                    ∏ i : Fin n,
                      (Polynomial.X -
                        (Polynomial.C : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l → Polynomial (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l))
                          (↑(α i) : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l))

noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.galEmb :
    (k E Ω : Type) →
      [inst : Field k] →
        [inst_1 : Field E] →
          [inst_2 : Field Ω] →
            [inst_3 : Algebra k Ω] →
              [inst_4 : Algebra E Ω] →
                [inst_5 : Algebra k E] → [IsScalarTower k E Ω] → UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G E Ω →* UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G k Ω :=
    fun (k E Ω : Type) [Field k] [Field E] [Field Ω] [Algebra k Ω] [Algebra E Ω] [Algebra k E] [IsScalarTower k E Ω] ↦
      AlgEquiv.restrictScalarsHom k

private theorem UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.charpoly_pow_two {k : Type} [Field k] (M : Matrix (Fin 2) (Fin 2) k) (a b : k)
    (h : M.charpoly = (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b)) (m : ℕ) :
    (M ^ m).charpoly = (Polynomial.X - Polynomial.C (a ^ m)) * (Polynomial.X - Polynomial.C (b ^ m)) := by
  have ht : M.trace = a + b := by
    have h0 := congrArg (fun p => Polynomial.eval 0 p) h
    have h1 := congrArg (fun p => Polynomial.eval 1 p) h
    rw [Matrix.charpoly_fin_two] at h0 h1
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at h0 h1
    linear_combination h0 - h1
  have hd : M.det = a * b := by
    have h1 := congrArg (fun p => Polynomial.eval 0 p) h
    rw [Matrix.charpoly_fin_two] at h1
    simpa using h1
  have hsq : M ^ 2 = (a + b) • M - (a * b) • (1 : Matrix (Fin 2) (Fin 2) k) := by
    rw [← ht, ← hd, Matrix.trace_fin_two, Matrix.det_fin_two, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have htr : ∀ n : ℕ, (M ^ n).trace = a ^ n + b ^ n := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simp [one_add_one_eq_two]
    | one => simpa using ht
    | more n h0 h1 =>
      rw [pow_add M n 2, hsq, mul_sub, Matrix.mul_smul, Matrix.mul_smul, mul_one, ← pow_succ,
        Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, h0, h1, smul_eq_mul, smul_eq_mul]
      ring
  rw [Matrix.charpoly_fin_two, htr, Matrix.det_pow, hd, mul_pow, Polynomial.C_add, Polynomial.C_mul]
  ring

private theorem UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.exists_pow_fix {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (L : Type)
    [Field L] [NumberField L] [Algebra L Ω] (g : Gal(Ω/ℚ)) :
    ∃ m : ℕ, 0 < m ∧ ∃ g' : Gal(Ω/L), AlgEquiv.restrictScalarsHom ℚ g' = g ^ m := by
  let K : IntermediateField ℚ Ω := (IsScalarTower.toAlgHom ℚ L Ω).fieldRange
  haveI : FiniteDimensional ℚ K :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ L Ω)).toLinearEquiv.finiteDimensional
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hi : K.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  obtain ⟨m, hm, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hi g
  rw [IntermediateField.mem_fixingSubgroup_iff] at hmem
  refine ⟨m, hm, AlgEquiv.ofRingEquiv (f := (g ^ m).toRingEquiv) (fun x => hmem _ ⟨x, rfl⟩), ?_⟩
  ext x
  rfl

theorem UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.freeRes :
    ∀ {Ω : Type} [inst : Field Ω] [inst_1 : CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [inst_3 : Fact (Nat.Prime l)] (L : Type)
      [inst_4 : Field L] [inst_5 : NumberField L] [inst_6 : Algebra L Ω] [IsAlgClosure L Ω]
      (W : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G ℚ Ω →* GL (Fin (2 : ℕ)) (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l)),
      UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.FreeAt l W → UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.FreeAt l (W.comp (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.galEmb ℚ L Ω)) := by
  intro Ω _ _ _ l _ L _ _ _ _ W hW A hA
  obtain ⟨g, hgD, hgc, α, hα, hch⟩ := hW A hA
  obtain ⟨m, hm, g', hg'⟩ := UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.exists_pow_fix L g
  refine ⟨g', ?_, ?_, fun i => α i ^ m, ?_, ?_⟩
  · have h1 : g ^ m ∈ UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Dec A := Subgroup.pow_mem _ hgD m
    rw [← hg'] at h1
    exact h1
  · have h1 : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.cycZ ℚ Ω l (g ^ m) = 1 := by rw [map_pow, hgc, one_pow]
    rw [← hg'] at h1
    exact h1
  · intro i j hij n hn
    have h1 := hα i j hij (m * n) (Nat.mul_pos hm hn)
    simpa only [pow_mul] using h1
  · have h1 : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.mat (W.comp (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.galEmb ℚ L Ω)) g' = UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.mat W g ^ m := by
      rw [← map_pow, ← hg']
      rfl
    rw [Fin.prod_univ_two] at hch
    rw [h1, Fin.prod_univ_two, UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.charpoly_pow_two _ _ _ hch m]
    simp only [Units.val_pow_eq_pow_val]
end

section

namespace UpperTheory.Reformulated.B.BorelApproximation

@[reducible] noncomputable def Pl : (E : Type) →
  [inst : Field E] → [NumberField E] → Type :=
  fun E [Field E] [NumberField E] => IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)

@[reducible] noncomputable def GLw : {E : Type} →
  [inst : Field E] → [inst_1 : NumberField E] → ℕ → Pl E → Type :=
  fun {E} [Field E] [NumberField E] n w => GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w)

theorem aux3 : ∀ (k : Type) [inst : Field k],
  SubsemiringClass (Subring k) k := by
  intro k _
  infer_instance

theorem aux4 : ∀ (k : Type) [inst : Field k] [inst_1 : ValuativeRel k]
  [inst_2 : TopologicalSpace k] [IsNonarchimedeanLocalField k], IsLocalRing ↥(ValuativeRel.valuation k).integer := by
  intro k _ _ _ _
  infer_instance

noncomputable def blk : {α n : Type} → {m : α → Type} → (a : α) × m a ≃ n → n → α :=
  fun {α n} {m} e i => (e.symm i).fst

theorem aux6 : ∀ (R : Type) [inst : CommRing R] {α n : Type}
  {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n] [inst_3 : DecidableEq n] (e : (a : α) × m a ≃ n)
  {x y : GL n R},
  x ∈ {g : GL n R | g.val.BlockTriangular (blk e)} →
    y ∈ {g : GL n R | g.val.BlockTriangular (blk e)} →
      x * y ∈ {g : GL n R | g.val.BlockTriangular (blk e)} := by
  intro R _ α n m _ _ _ e x y hx hy
  exact Matrix.BlockTriangular.mul hx hy

theorem aux7 : ∀ (R : Type) [inst : CommRing R] {α n : Type}
  {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n] [inst_3 : DecidableEq n] (e : (a : α) × m a ≃ n),
  1 ∈ {g : GL n R | g.val.BlockTriangular (blk e)} := by
  intro R _ α n m _ _ _ e
  exact Matrix.blockTriangular_one

theorem aux8 : ∀ (R : Type) [inst : CommRing R] {α n : Type}
  {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n] [inst_3 : DecidableEq n] (e : (a : α) × m a ≃ n)
  {x : GL n R},
  x ∈ {g : GL n R | g.val.BlockTriangular (blk e)} →
    x⁻¹ ∈ {g : GL n R | g.val.BlockTriangular (blk e)} := by
  intro R _ α n m _ _ _ e x hx
  have hx : Matrix.BlockTriangular (x : Matrix n n R) (blk e) := hx
  letI := x.invertible
  change Matrix.BlockTriangular ((x⁻¹ : GL n R) : Matrix n n R) (blk e)
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hx

noncomputable def parab : (R : Type) →
  [inst : CommRing R] →
    {α n : Type} →
      {m : α → Type} →
        [LinearOrder α] → [inst_2 : Fintype n] → [inst_3 : DecidableEq n] → (a : α) × m a ≃ n → Subgroup (GL n R) :=
  fun R [inst : CommRing R] {α n} {m} [inst_1 : LinearOrder α] [inst_2 : Fintype n] [inst_3 : DecidableEq n] e =>
    { carrier := {g : GL n R | g.val.BlockTriangular (blk e)},
      mul_mem' := @aux6 R inst α n m inst_1 inst_2 inst_3 e,
      one_mem' := aux7 R e,
      inv_mem' := @aux8 R inst α n m inst_1 inst_2 inst_3 e }

noncomputable def points : (n : Type) → (_ : n) × Unit ≃ n :=
  fun n => Equiv.sigmaUnique n fun x => Unit

noncomputable def borel : (R : Type) →
  [inst : CommRing R] →
    (n : Type) → [inst_1 : Fintype n] → [inst_2 : DecidableEq n] → [LinearOrder n] → Subgroup (GL n R) :=
  fun R [CommRing R] n [Fintype n] [DecidableEq n] [LinearOrder n] =>
    parab R (points n)

noncomputable def iwahori : (k : Type) →
  [inst : Field k] →
    [inst_1 : ValuativeRel k] →
      [inst_2 : TopologicalSpace k] →
        [IsNonarchimedeanLocalField k] →
          (n : Type) → [inst_4 : Fintype n] → [inst_5 : DecidableEq n] → [LinearOrder n] → Subgroup (GL n k) :=
  fun k [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] n [Fintype n] [DecidableEq n]
      [LinearOrder n] =>
    Subgroup.map (Matrix.GeneralLinearGroup.map (Algebra.algebraMap (↥(ValuativeRel.valuation k).integer) k))
      (Subgroup.comap (Matrix.GeneralLinearGroup.map (IsLocalRing.residue ↥(ValuativeRel.valuation k).integer))
        (borel
          (IsLocalRing.ResidueField ↥(ValuativeRel.valuation k).integer) n))

@[reducible] noncomputable def complRel : {F : Type} →
  [inst : Field F] →
    [inst_1 : NumberField F] →
      (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
        ValuativeRel (IsDedekindDomain.HeightOneSpectrum.adicCompletion F p) :=
  fun {F} [Field F] [NumberField F] p => ValuativeRel.ofValuation Valued.v

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
private theorem exists_near {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (NumberField.RingOfIntegers F)) (x : adicCompletion F p)
    (hx : Valued.v x ≤ 1) :
    ∃ a : NumberField.RingOfIntegers F, Valued.v (x - algebraMap _ (adicCompletion F p) a) < 1 := by
  have hb : {y : adicCompletion F p | Valued.v (y - x) < 1} ∈ nhds x := by
    rw [Valued.mem_nhds]
    refine ⟨1, fun y hy => ?_⟩
    simpa using hy
  obtain ⟨k, hk⟩ := (denseRange_algebraMap F p).mem_nhds hb
  have hk : Valued.v (algebraMap F (adicCompletion F p) k - x) < 1 := hk
  have hv : ∀ y : F, Valued.v (algebraMap F (adicCompletion F p) y) = p.valuation F y :=
    fun y => valuedAdicCompletion_eq_valuation' p y
  have hk1 : p.valuation F k ≤ 1 := by
    rw [← hv, ← sub_add_cancel (algebraMap F (adicCompletion F p) k) x]
    exact Valuation.map_add_le _ hk.le hx
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer p hk1 1
  refine ⟨a, ?_⟩
  rw [← hv, map_sub, ← IsScalarTower.algebraMap_apply, Units.val_one] at ha
  rw [Valuation.map_sub_swap, ← sub_add_sub_cancel _ (algebraMap F (adicCompletion F p) k)]
  exact Valuation.map_add_lt _ ha hk

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
private theorem finite_residue {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Finite (IsLocalRing.ResidueField (adicCompletionIntegers F p)) := by
  have hfin : Finite (NumberField.RingOfIntegers F ⧸ p.asIdeal) :=
    p.asIdeal.finiteQuotientOfFreeOfNeBot p.ne_bot
  have hmax : ∀ y : adicCompletionIntegers F p, Valued.v y.1 < 1 →
      IsLocalRing.residue _ y = 0 := fun y hy => by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hy.ne
  let φ : NumberField.RingOfIntegers F →+* IsLocalRing.ResidueField (adicCompletionIntegers F p) :=
    (IsLocalRing.residue _).comp (algebraMap _ _)
  have hker : ∀ a ∈ p.asIdeal, φ a = 0 := fun a ha => by
    refine hmax _ ?_
    rw [algebraMap_adicCompletionIntegers_apply, valuedAdicCompletion_eq_valuation']
    exact (valuation_lt_one_iff_mem p a).2 ha
  refine Finite.of_surjective (Ideal.Quotient.lift p.asIdeal φ hker) fun z => ?_
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨a, ha⟩ := exists_near p x.1 x.2
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  rw [Ideal.Quotient.lift_mk, eq_comm, ← sub_eq_zero]
  have := hmax (x - algebraMap _ _ a) ha
  rwa [map_sub] at this

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
private theorem locCompact {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    LocallyCompactSpace (adicCompletion F p) := by
  have h := (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (K := adicCompletion F p)).2
    ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (adicCompletionIntegers F p)),
      finite_residue p⟩
  exact locallyCompact_of_proper

theorem zero_contDiffOn_supported : ∀ {F : Type} [inst : Field F]
  [inst_1 : NumberField F] (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
  IsNonarchimedeanLocalField (IsDedekindDomain.HeightOneSpectrum.adicCompletion F p) := by
  intro F _ _ p
  letI := complRel p
  haveI : (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  haveI : IsValuativeTopology (p.adicCompletion F) :=
    IsValuativeTopology.of_mem_nhds_zero_iff_vle
      (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)))
      (fun {s} => Valued.is_topological_valuation s)
  haveI := locCompact p
  haveI : ValuativeRel.IsNontrivial (p.adicCompletion F) :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)))).2 inferInstance
  exact {}

noncomputable def iwGL : {E : Type} →
  [inst : Field E] →
    [inst_1 : NumberField E] →
      (n : ℕ) →
        (w : Pl E) →
          Subgroup (GLw n w) :=
  fun {E} [Field E] [NumberField E] n w => by
    letI := complRel w
    haveI := zero_contDiffOn_supported w
    exact iwahori (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w) (Fin n)

noncomputable def dcos : {E : Type} →
  [inst : Field E] →
    [inst_1 : NumberField E] →
      (n : ℕ) →
        (w : Pl E) →
          GLw n w →
            GLw n w → ℂ :=
  fun {E} [Field E] [NumberField E] n w t y => by
    classical
    exact if ∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, y = x * t * z then 1 else 0

theorem dcos_left : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
  [NumberField.IsCMField E] {m : ℕ} {w : Pl E}
  (t k g : GLw m w),
  k ∈ iwGL m w →
    dcos m w t (k * g) =
      dcos m w t g := by
  intro E _ _ _ m w t k g hk
  unfold dcos
  refine congrArg (fun P : Prop => @ite ℂ P (Classical.propDecidable P) 1 0) (propext ⟨?_, ?_⟩)
  · rintro ⟨x, hx, z, hz, h⟩
    refine ⟨k⁻¹ * x, mul_mem (inv_mem hk) hx, z, hz, ?_⟩
    rw [mul_assoc k⁻¹, mul_assoc k⁻¹, ← h, inv_mul_cancel_left]
  · rintro ⟨x, hx, z, hz, h⟩
    refine ⟨k * x, mul_mem hk hx, z, hz, ?_⟩
    rw [h, mul_assoc k, mul_assoc k]

end UpperTheory.Reformulated.B.BorelApproximation
end

section

open Filter Topology ValuativeRel

private theorem small_powers {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (V : Set k) (hV : V ∈ nhds (0 : k)) :
    ∀ᶠ c : ℕ in atTop, ∀ x ∈ IsLocalRing.maximalIdeal ↥(valuation k).integer ^ c,
      (x : k) ∈ V := by
  obtain ⟨γ, hγ, hs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hV
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(valuation k).integer
  have hlt : valuation k (π : k) < 1 := by
    refine lt_of_le_of_ne π.2 fun h => hπ.not_isUnit ?_
    exact (Valuation.integer.integers (valuation k)).isUnit_of_one' h
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨N, hN⟩ := exists_pow_lt₀ hlt (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop N] with c hc x hx
  have hx' := Ideal.pow_le_pow_right hc hx
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hx'
  obtain ⟨a, rfl⟩ := hx'
  apply hs
  have ha : valuation k (a : k) ≤ 1 := a.2
  change valuation k ((a : k) * (π : k) ^ N) < γ
  rw [map_mul, map_pow]
  calc _ ≤ 1 * valuation k (π : k) ^ N := by gcongr
    _ < γ := by simpa using hN

private theorem entry_mem {k : Type} [Field k] [ValuativeRel k] {n : ℕ}
    (I : Ideal ↥(valuation k).integer) (g : GL (Fin n) k)
    (hg : g ∈ Subgroup.map
      (Matrix.GeneralLinearGroup.map (algebraMap (↥(valuation k).integer) k))
      (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk I)).ker) (i j : Fin n) :
    ∃ x ∈ I, (x : k) = (g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j := by
  obtain ⟨h, hh, rfl⟩ := hg
  have h1 : Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk I) h = 1 := hh
  have h2 : Ideal.Quotient.mk I ((h : Matrix (Fin n) (Fin n) _) i j)
      = (1 : Matrix (Fin n) (Fin n) (_ ⧸ I)) i j :=
    by
      have h4 := Units.ext_iff.mp h1
      exact congrFun (congrFun h4 i) j
  refine ⟨(h : Matrix (Fin n) (Fin n) _) i j - (1 : Matrix (Fin n) (Fin n) _) i j, ?_, ?_⟩
  · rw [← Ideal.Quotient.eq, h2]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · have h3 : ((Matrix.GeneralLinearGroup.map (algebraMap (↥(valuation k).integer) k) h :
        GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
        = (((h : Matrix (Fin n) (Fin n) ↥(valuation k).integer) i j : _) : k) := rfl
    rw [h3]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

private theorem tendsto_val {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {α : Type} (L : Filter α) (c : α → ℕ)
    (hc : Tendsto c L atTop) (g : α → GL (Fin n) k)
    (hg : ∀ᶠ a in L, g a ∈ Subgroup.map
      (Matrix.GeneralLinearGroup.map (algebraMap (↥(valuation k).integer) k))
      (Matrix.GeneralLinearGroup.map (n := Fin n)
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(valuation k).integer ^ c a))).ker) :
    Tendsto (fun a => (g a : Matrix (Fin n) (Fin n) k)) L (nhds 1) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  rw [← tendsto_sub_nhds_zero_iff]
  refine tendsto_def.mpr fun V hV => ?_
  filter_upwards [hg, hc.eventually (small_powers V hV)] with a ha hs
  obtain ⟨x, hx, e⟩ := entry_mem _ _ ha i j
  have := hs x hx
  rwa [e] at this

theorem UpperTheory.congruence_subgroup_eventually :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (U : Set (GL (Fin n) k)), U ∈ nhds (1 : GL (Fin n) k) →
        ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → ∀ g : GL (Fin n) k, g ∈ Subgroup.map (Matrix.GeneralLinearGroup.map (algebraMap (↥(ValuativeRel.valuation k).integer) k))
          (Matrix.GeneralLinearGroup.map (n := Fin n)
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation k).integer ^ c))).ker → g ∈ U := by
  intro k _ _ _ _ n U hU
  let K : ℕ → Subgroup (GL (Fin n) k) := fun c => Subgroup.map
      (Matrix.GeneralLinearGroup.map (algebraMap (↥(valuation k).integer) k))
      (Matrix.GeneralLinearGroup.map (n := Fin n)
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(valuation k).integer ^ c))).ker
  let L : Filter (ℕ × GL (Fin n) k) := comap Prod.fst atTop ⊓ 𝓟 {p | p.2 ∈ K p.1}
  have hc : Tendsto Prod.fst L atTop := tendsto_comap.mono_left inf_le_left
  have hK : ∀ᶠ p in L, p.2 ∈ K p.1 := mem_inf_of_right (mem_principal_self _)
  have h1 := tendsto_val L Prod.fst hc Prod.snd hK
  have h2 := tendsto_val L Prod.fst hc (fun p => p.2⁻¹) (hK.mono fun p hp => (K p.1).inv_mem hp)
  have h : Tendsto Prod.snd L (nhds (1 : GL (Fin n) k)) := by
    rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
    refine Tendsto.prodMk_nhds h1 ?_
    exact (MulOpposite.continuous_op.tendsto _).comp h2
  have h3 : ∀ᶠ p in L, p.2 ∈ U := h hU
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at h3
  obtain ⟨c₀, h₀⟩ := h3
  exact ⟨c₀, fun c hc g hg => h₀ c hc (c, g) rfl hg⟩
end
