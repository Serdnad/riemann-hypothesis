module

public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Formalism.SharpRestriction.ParConsts
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle167
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabRing

open Formalism.UG

theorem cT_add_rect {R : Type} [CommRing R] (σ : R →+* R) {a b : Type} (M N : Matrix a b R) :
    cT σ (M + N) = cT σ M + cT σ N := by
  ext i j; simp [cT]

theorem exists_emb_block {R : Type} [CommRing R] (σ : R →+* R) {n m k : Type}
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    (J : Matrix n n R) (J' : Matrix m m R) (X : Matrix n k R) (U : Matrix k n R)
    (A : Matrix n m R) (A' : Matrix m n R)
    (hB : IsUnit (cT σ X * J * X)) (hXA : cT σ X * J * A = 0) (hAX : cT σ A * J * X = 0)
    (hJ : cT σ A * J * A = J') (h1 : A' * A = 1) (h2 : A' * X = 0) (h3 : U * A = 0) (h4 : U * X = 1)
    (h5 : X * U + A * A' = 1) :
    ∃ j : UJ σ J' →* UJ σ J,
      (∀ g, ((j g : GL n R) : Matrix n n R) = X * U + A * ((g : GL m R) : Matrix m m R) * A') ∧
      ∀ h : UJ σ J, ((h : GL n R) : Matrix n n R) * X = X → h ∈ j.range := by
  have hmul : ∀ g g' : Matrix m m R,
      (X * U + A * g * A') * (X * U + A * g' * A') = X * U + A * (g * g') * A' := by
    intro g g'
    calc (X * U + A * g * A') * (X * U + A * g' * A')
        = X * (U * X) * U + X * (U * A) * g' * A' + (A * g * (A' * X) * U + A * g * (A' * A) * g' * A') := by
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
      _ = _ := by rw [h1, h2, h3, h4]; simp [Matrix.mul_assoc]
  have hone : X * U + A * (1 : Matrix m m R) * A' = 1 := by rw [Matrix.mul_one, h5]
  have hform : ∀ g : Matrix m m R, cT σ (X * U + A * g * A') * J * (X * U + A * g * A')
      = cT σ U * (cT σ X * J * X) * U + cT σ A' * (cT σ g * J' * g) * A' := by
    intro g
    calc cT σ (X * U + A * g * A') * J * (X * U + A * g * A')
        = cT σ U * (cT σ X * J * X) * U + cT σ U * (cT σ X * J * A) * g * A'
          + (cT σ A' * cT σ g * (cT σ A * J * X) * U
            + cT σ A' * (cT σ g * (cT σ A * J * A) * g) * A') := by
          simp only [cT_add_rect, cT_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
      _ = _ := by rw [hXA, hAX, hJ]; simp
  have hJJ : cT σ U * (cT σ X * J * X) * U + cT σ A' * J' * A' = J := by
    have := hform 1
    rw [hone] at this
    simpa [cT_one] using this.symm
  let j0 : GL m R → GL n R := fun g =>
    ⟨X * U + A * (g : Matrix m m R) * A', X * U + A * ((g⁻¹ : GL m R) : Matrix m m R) * A',
      by rw [hmul, Units.mul_inv, hone], by rw [hmul, Units.inv_mul, hone]⟩
  have hmem : ∀ g : UJ σ J', j0 g ∈ UJ σ J := by
    intro g
    have hg : cT σ ((g : GL m R) : Matrix m m R) * J' * ((g : GL m R) : Matrix m m R) = J' := g.2
    change cT σ (X * U + A * ((g : GL m R) : Matrix m m R) * A') * J
      * (X * U + A * ((g : GL m R) : Matrix m m R) * A') = J
    rw [hform, hg, hJJ]
  let j : UJ σ J' →* UJ σ J :=
    { toFun := fun g => ⟨j0 g, hmem g⟩
      map_one' := by
        apply Subtype.ext; apply Units.ext
        exact hone
      map_mul' := by
        intro g g'
        apply Subtype.ext; apply Units.ext
        exact (hmul _ _).symm }
  refine ⟨j, fun g => rfl, ?_⟩
  have hXJ : cT σ X * J = cT σ X * J * X * U := by
    calc cT σ X * J = cT σ X * J * (X * U + A * A') := by rw [h5, Matrix.mul_one]
      _ = cT σ X * J * X * U + cT σ X * J * A * A' := by
        simp only [Matrix.mul_add, Matrix.mul_assoc]
      _ = _ := by rw [hXA]; simp
  have key : ∀ h : Matrix n n R, cT σ h * J * h = J → h * X = X → A * (A' * h * A) = h * A := by
    intro h hh hX
    have e1 : cT σ X * J * X * (U * h * A) = 0 := by
      calc cT σ X * J * X * (U * h * A) = (cT σ X * J * X * U) * h * A := by
            simp only [Matrix.mul_assoc]
        _ = cT σ (h * X) * J * h * A := by rw [← hXJ, hX]
        _ = cT σ X * (cT σ h * J * h) * A := by simp only [cT_mul, Matrix.mul_assoc]
        _ = 0 := by rw [hh, hXA]
    have e2 : U * h * A = 0 := by
      obtain ⟨b, hb⟩ := hB
      rw [← hb] at e1
      calc U * h * A = ((b⁻¹ : GL k R) : Matrix k k R) * (b : Matrix k k R) * (U * h * A) := by
            rw [Units.inv_mul, Matrix.one_mul]
        _ = 0 := by rw [Matrix.mul_assoc, e1, Matrix.mul_zero]
    calc A * (A' * h * A) = X * (U * h * A) + A * (A' * h * A) := by rw [e2]; simp
      _ = (X * U + A * A') * h * A := by simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = h * A := by rw [h5, Matrix.one_mul]
  intro h hX
  have hh : cT σ ((h : GL n R) : Matrix n n R) * J * ((h : GL n R) : Matrix n n R) = J := h.2
  have hh' : cT σ (((h : GL n R)⁻¹ : GL n R) : Matrix n n R) * J
      * (((h : GL n R)⁻¹ : GL n R) : Matrix n n R) = J := (h⁻¹).2
  have hX' : (((h : GL n R)⁻¹ : GL n R) : Matrix n n R) * X = X := by
    conv_lhs => rw [← hX]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have k1 := key _ hh hX
  have k2 := key _ hh' hX'
  let g : GL m R := ⟨A' * ((h : GL n R) : Matrix n n R) * A,
    A' * (((h : GL n R)⁻¹ : GL n R) : Matrix n n R) * A,
    by rw [Matrix.mul_assoc _ A, k2, Matrix.mul_assoc A', ← Matrix.mul_assoc _ _ A, Units.mul_inv,
      Matrix.one_mul, h1],
    by rw [Matrix.mul_assoc _ A, k1, Matrix.mul_assoc A', ← Matrix.mul_assoc _ _ A, Units.inv_mul,
      Matrix.one_mul, h1]⟩
  have hg : g ∈ UJ σ J' := by
    change cT σ (A' * ((h : GL n R) : Matrix n n R) * A) * J'
      * (A' * ((h : GL n R) : Matrix n n R) * A) = J'
    calc cT σ (A' * ((h : GL n R) : Matrix n n R) * A) * J' * (A' * ((h : GL n R) : Matrix n n R) * A)
        = cT σ (A * (A' * ((h : GL n R) : Matrix n n R) * A)) * J
          * (A * (A' * ((h : GL n R) : Matrix n n R) * A)) := by
          rw [cT_mul σ A, ← hJ]; simp only [Matrix.mul_assoc]
      _ = cT σ A * (cT σ ((h : GL n R) : Matrix n n R) * J * ((h : GL n R) : Matrix n n R)) * A := by
          rw [k1]; simp only [cT_mul, Matrix.mul_assoc]
      _ = J' := by rw [hh, hJ]
  refine ⟨⟨g, hg⟩, ?_⟩
  apply Subtype.ext; apply Units.ext
  change X * U + A * (A' * ((h : GL n R) : Matrix n n R) * A) * A' = ((h : GL n R) : Matrix n n R)
  rw [k1]
  calc X * U + ((h : GL n R) : Matrix n n R) * A * A'
      = ((h : GL n R) : Matrix n n R) * X * U + ((h : GL n R) : Matrix n n R) * A * A' := by rw [hX]
    _ = ((h : GL n R) : Matrix n n R) * (X * U + A * A') := by
      simp only [Matrix.mul_add, Matrix.mul_assoc]
    _ = _ := by rw [h5, Matrix.mul_one]

theorem exists_emb : ∀ (R : Type) [CommRing R] (σ : R →+* R) (n m : ℕ) (J : Matrix (Fin n) (Fin n) R) (J' : Matrix (Fin m) (Fin m) R) (x u : Fin n → R) (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R), IsUnit ((fun i => σ (x i)) ⬝ᵥ (J *ᵥ x)) → (fun i => σ (x i)) ᵥ* (J * A) = 0 → Formalism.UG.cT σ A *ᵥ (J *ᵥ x) = 0 → Formalism.UG.cT σ A * J * A = J' → A' * A = 1 → A' *ᵥ x = 0 → u ᵥ* A = 0 → u ⬝ᵥ x = 1 → vecMulVec x u + A * A' = 1 → ∃ j : Formalism.UG.UJ σ J' →* Formalism.UG.UJ σ J, (∀ g, ((j g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = vecMulVec x u + A * ((g : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * A') ∧ ∀ h : Formalism.UG.UJ σ J, ((h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ x = x → h ∈ j.range := by
  intro R _ σ n m J J' x u A A' hB hXA hAX hJ h1 h2 h3 h4 h5
  have hc : cT σ (replicateCol Unit x) = replicateRow Unit (fun i => σ (x i)) := by
    ext i j; simp [cT]
  rw [vecMulVec_eq Unit] at h5 ⊢
  obtain ⟨j, hj1, hj2⟩ := exists_emb_block σ J J' (replicateCol Unit x) (replicateRow Unit u) A A'
    (by
      rw [hc, Matrix.mul_assoc, ← replicateCol_mulVec, replicateRow_mul_replicateCol,
        Matrix.isUnit_iff_isUnit_det]
      simpa using hB)
    (by rw [hc, Matrix.mul_assoc, ← replicateRow_vecMul, hXA]; simp)
    (by rw [Matrix.mul_assoc, ← replicateCol_mulVec, ← replicateCol_mulVec, hAX]; simp)
    hJ h1
    (by rw [← replicateCol_mulVec, h2]; simp)
    (by rw [← replicateRow_vecMul, h3]; simp)
    (by rw [replicateRow_mul_replicateCol, h4]; ext i j; simp)
    h5
  exact ⟨j, hj1, fun h hx => hj2 h (by rw [← replicateCol_mulVec, hx])⟩

end GlobalTheory.StabRing
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem isClosed_range_of_isCompact_preimage {G H : Type} [Group G] [Group H] [TopologicalSpace G]
    [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (φ : G →* H) (hφ : Continuous φ) (U : Set H)
    (hU : IsOpen U) (h1 : (1 : H) ∈ U) (hc : IsCompact (φ ⁻¹' U)) : IsClosed (Set.range φ) := by
  have hcl : IsClosed (U ∩ Set.range φ) := by
    have e : U ∩ Set.range φ = φ '' (φ ⁻¹' U) := by
      ext y
      constructor
      · rintro ⟨hy, g, rfl⟩
        exact ⟨g, hy, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨hg, g, rfl⟩
    rw [e]
    exact (hc.image hφ).isClosed
  refine closure_subset_iff_isClosed.mp fun x hx => ?_
  have hO : IsOpen ((fun s => s⁻¹ * x) ⁻¹' U) := hU.preimage (by fun_prop)
  have hxO : x ∈ (fun s => s⁻¹ * x) ⁻¹' U := by
    show x⁻¹ * x ∈ U
    rwa [inv_mul_cancel]
  obtain ⟨s, hsU, g, rfl⟩ := mem_closure_iff.mp hx _ hO hxO
  have hy : (φ g)⁻¹ * x ∈ closure (Set.range φ) :=
    map_mem_closure (f := fun s => (φ g)⁻¹ * s) (by fun_prop) hx
      (by rintro _ ⟨k, rfl⟩; exact ⟨g⁻¹ * k, by simp⟩)
  have hyU : (φ g)⁻¹ * x ∈ U ∩ Set.range φ := by
    rw [← hcl.closure_eq]
    exact hU.inter_closure ⟨hsU, hy⟩
  obtain ⟨-, k, hk⟩ := hyU
  exact ⟨g * k, by rw [map_mul, hk, mul_inv_cancel_left]⟩

theorem nhds_one_hasBasis_Kg (I : AutInst) : (nhds (1 : I.Gf)).HasBasis (fun N : ℕ => 1 ≤ N) I.Kg := by
  refine ⟨fun t => ⟨fun ht => I.topf_basis t ht, ?_⟩⟩
  rintro ⟨N, hN, hsub⟩
  refine Filter.mem_of_superset ((I.topf_open N hN).mem_nhds ?_) hsub
  simp only [Set.mem_setOf_eq]
  refine ⟨?_, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
  · simpa using one_mem (Formalism.UG.stabGL (lamAf (F := I.F) I.L))
  · simp

theorem isClosedEmbedding_of_preimage_Kg (I I' : AutInst) (φ : I'.Gf →* I.Gf)
    (h : ∀ (N : ℕ) (g : I'.Gf), g ∈ I'.Kg N ↔ φ g ∈ I.Kg N) : Topology.IsClosedEmbedding φ := by
  have hpre : (fun N : ℕ => φ ⁻¹' I.Kg N) = I'.Kg := by
    funext N
    ext g
    exact (h N g).symm
  have hb : (nhds (1 : I'.Gf)).HasBasis (fun N : ℕ => 1 ≤ N) fun N => φ ⁻¹' I.Kg N := by
    rw [hpre]
    exact nhds_one_hasBasis_Kg I'
  have hind : Topology.IsInducing φ :=
    IsTopologicalGroup.isInducing_iff_nhds_one.mpr
      (hb.eq_of_same_basis ((nhds_one_hasBasis_Kg I).comap φ))
  have hT' := GlobalTheory.CongTop.adelic_topology I'
  haveI : T2Space I'.Gf := hT'.1
  haveI : T2Space I.Gf := (GlobalTheory.CongTop.adelic_topology I).1
  obtain ⟨hopen1, ⟨K, hK⟩, -⟩ := hT'.2.2.2.2.2.2 1 le_rfl
  have hKcl : IsClosed (I'.Kg 1) := by
    rw [← hK]
    exact K.isClosed_of_isOpen (by rw [hK]; exact hopen1)
  have hcpt : IsCompact (φ ⁻¹' I.Kg 1) := by
    rw [show φ ⁻¹' I.Kg 1 = I'.Kg 1 from congrFun hpre 1]
    exact hT'.2.2.2.1.of_isClosed_subset hKcl fun x hx => hx.1
  have hU : IsOpen (I.Kg 1) := ((GlobalTheory.CongTop.adelic_topology I).2.2.2.2.2.2 1 le_rfl).1
  have h1 : (1 : I.Gf) ∈ I.Kg 1 := mem_of_mem_nhds ((nhds_one_hasBasis_Kg I).mem_of_mem le_rfl)
  exact ⟨hind.isEmbedding, isClosed_range_of_isCompact_preimage φ hind.continuous (I.Kg 1) hU h1 hcpt⟩

theorem isClosedEmbedding_of_conj_Kg : ∀ (I I' : AutInst) (j : I'.Gf →* I.Gf) (xf : I.Gf),
    (∀ (N : ℕ) (g : I'.Gf), g ∈ I'.Kg N ↔ xf⁻¹ * j g * xf ∈ I.Kg N) → Topology.IsClosedEmbedding j := by
  intro I I' j xf hj
  let ψ : I'.Gf →* I.Gf := (MulAut.conj xf⁻¹).toMonoidHom.comp j
  have hψ : ∀ g, ψ g = xf⁻¹ * j g * xf := fun g => by simp [ψ, MulAut.conj_apply]
  have hc : Topology.IsClosedEmbedding ψ :=
    isClosedEmbedding_of_preimage_Kg I I' ψ fun N g => by rw [hψ]; exact hj N g
  have e : (j : I'.Gf → I.Gf) = ((Homeomorph.mulLeft xf).trans (Homeomorph.mulRight xf⁻¹)) ∘ ψ := by
    funext g
    simp [hψ, mul_assoc]
  rw [e]
  exact ((Homeomorph.mulLeft xf).trans (Homeomorph.mulRight xf⁻¹)).isClosedEmbedding.comp hc

end GlobalTheory.StabUnfold
end

section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem sizes_record_at {D : D7} (L : SizeData₂ D) (h : SizesAt L) (Cs : ℝ) (hCs : 5 ≤ Cs)
    (hx : 16 ≤ L.sc.x) (j : Fin 2) :
    Real.exp (8 * L.sc.x ^ L.sc.eps) ≤ (D.host.g j : ℝ) ∧ L.sc.x ^ 2 ≤ (D.R.f : ℝ) ∧
      (D.R.f : ℝ) ≤ L.sc.x ^ Cs ∧ (D.R.m : ℝ) ≤ L.sc.x ^ Cs ∧ 100 ≤ D.R.r ∧
      (D.R.r : ℝ) ≤ L.sc.x ^ Cs ∧
      Real.exp (L.sc.x ^ (L.sc.ez / 6)) ≤ ((min D.host.q D.host.d : ℕ) : ℝ) := by
  obtain ⟨hN, -, hK, -, -, -, hQ, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -⟩ := h
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have hmk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
  have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hkb : (D.R.k : ℝ) ≤ L.sc.x ^ (19 / 4 : ℝ) := by
    refine hK.2.trans (Real.rpow_le_rpow_of_exponent_le hx1.le ?_)
    unfold szTh
    linarith
  have h2 : (2 : ℝ) ≤ L.sc.x ^ (1 / 4 : ℝ) := by
    have e : (2 : ℝ) = (16 : ℝ) ^ (1 / 4 : ℝ) := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [e]
    exact Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  have h2k : 2 * (D.R.k : ℝ) ≤ L.sc.x ^ Cs := by
    calc 2 * (D.R.k : ℝ) ≤ L.sc.x ^ (1 / 4 : ℝ) * L.sc.x ^ (19 / 4 : ℝ) :=
          mul_le_mul h2 hkb (by linarith) (by linarith)
      _ = L.sc.x ^ (5 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
      _ ≤ L.sc.x ^ Cs := Real.rpow_le_rpow_of_exponent_le hx1.le hCs
  have hn : L.sc.x ^ 2 ≤ (D.R.n : ℝ) := by
    refine le_trans ?_ hN.1
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hx1.le
    unfold szTh
    push_cast
    linarith
  have hf : L.sc.x ^ 2 ≤ (D.R.f : ℝ) := by
    refine hn.trans ?_
    exact_mod_cast (by unfold Ranks.f; omega : D.R.n ≤ D.R.f)
  have hfk' : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have hmk' : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hr : (D.R.r : ℝ) ≤ 2 * (D.R.k : ℝ) := by
    exact_mod_cast (by unfold Ranks.r; omega : D.R.r ≤ 2 * D.R.k)
  have hf100 : 100 ≤ D.R.f := by
    have : (100 : ℝ) ≤ D.R.f := by nlinarith
    exact_mod_cast this
  refine ⟨?_, hf, by linarith, by linarith, by unfold Ranks.r; omega, by linarith, ?_⟩
  · refine le_trans ?_ (hG j j).1
    have e : Real.exp (8 * L.sc.x ^ L.sc.eps) = L.sc.b ^ 8 := by
      unfold Scale.b Scale.L
      rw [← Real.exp_nat_mul]
      norm_num
    have hb : 0 < L.sc.b := Real.exp_pos _
    rw [e]
    exact pow_le_pow_left₀ hb.le (le_mul_of_one_le_left hb.le hk1) 8
  · have hq : (0 : ℝ) < D.host.q := by
      have := D.host.qd_big.1
      exact_mod_cast (by omega : 0 < D.host.q)
    have hd : (0 : ℝ) < D.host.d := by
      have := D.host.qd_big.2
      exact_mod_cast (by omega : 0 < D.host.d)
    rw [Nat.cast_min]
    refine le_min ((Real.le_log_iff_exp_le hq).1 hQ.1) ((Real.le_log_iff_exp_le hd).1 ?_)
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hx1.le ?_) hQ.2.2.2.1
    have := L.sc.ez_pos
    linarith

theorem family_eventually_size_bounds : ∀ (eps : ℝ) (Fm : FamP eps) (Cs : ℝ), 5 ≤ Cs → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (j : Fin 2), Real.exp (8 * x ^ eps) ≤ ((Fm.D x i).host.g j : ℝ) ∧ x ^ 2 ≤ ((Fm.D x i).R.f : ℝ) ∧ ((Fm.D x i).R.f : ℝ) ≤ x ^ Cs ∧ ((Fm.D x i).R.m : ℝ) ≤ x ^ Cs ∧ 100 ≤ (Fm.D x i).R.r ∧ ((Fm.D x i).R.r : ℝ) ≤ x ^ Cs ∧ Real.exp (x ^ (Fm.ez / 6)) ≤ ((min (Fm.D x i).host.q (Fm.D x i).host.d : ℕ) : ℝ) := by
  intro eps Fm Cs hCs
  refine ⟨max 16 (Fm.x1 + 1), fun x hx i j => ?_⟩
  have h16 : 16 ≤ x := (le_max_left _ _).trans hx
  have hx1 : Fm.x1 < x := by linarith [(le_max_right _ _).trans hx]
  have := sizes_record_at (Fm.L x i) (Fm.sizes x hx1 i) Cs hCs (by rw [Fm.L_x x i hx1]; exact h16) j
  rw [Fm.L_x x i hx1, Fm.L_eps x i, Fm.L_ez x i] at this
  exact this

end GlobalTheory
end

section

open Formalism.MainNotions Formalism.BasicNotions Filter

namespace GlobalTheory

theorem sizes_large_of_power_bounds {D : D7} (L : SizeData₂ D) (h : SizesAt L) (M : ℝ)
    (h1 : M ≤ L.sc.x ^ (1 / 4 : ℝ)) (h2 : M ≤ L.sc.x ^ L.sc.eps)
    (h3 : 5 * |M| * Real.log L.sc.x ≤ L.sc.x ^ L.sc.eps) :
    M ≤ (D.R.m : ℝ) ∧ M ≤ L.sc.L ∧ (D.R.k : ℝ) ^ M ≤ L.sc.b ∧ D.host.rdE ≤ L.sc.b ∧
      (D.R.k : ℝ) * (D.R.m : ℝ) ^ 10 ≤ (D.s.Del : ℝ) := by
  obtain ⟨-, hM, hK, -, hT, hC, hQ, -, -, -, -, -, -, -, -, -, hD, -⟩ := h
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have hL0 : 0 ≤ L.sc.L := by unfold Scale.L; positivity
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp hL0
  refine ⟨?_, h2, ?_, ?_, ?_⟩
  · refine h1.trans (le_trans ?_ hM.1)
    have e : Real.sqrt (L.sc.x * L.sc.delta1) = L.sc.x ^ ((1 + -(L.sc.eps / 8)) * (1 / 2)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_mul hx0.le, Real.rpow_add hx0, Real.rpow_one]
      rfl
    rw [e, ← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_le hx1.le
    unfold szTh
    linarith
  · have hk1 : (1 : ℝ) ≤ D.R.k := by
      have := D.R.m_add_three_le_k
      exact_mod_cast (by omega : 1 ≤ D.R.k)
    have hk5 : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) := by
      refine hK.2.trans (Real.rpow_le_rpow_of_exponent_le hx1.le ?_)
      unfold szTh
      linarith
    calc (D.R.k : ℝ) ^ M ≤ (D.R.k : ℝ) ^ |M| := Real.rpow_le_rpow_of_exponent_le hk1 (le_abs_self M)
      _ ≤ (L.sc.x ^ (5 : ℝ)) ^ |M| := Real.rpow_le_rpow (by linarith) hk5 (abs_nonneg M)
      _ = Real.exp (5 * |M| * Real.log L.sc.x) := by
          rw [← Real.rpow_mul hx0.le, Real.rpow_def_of_pos hx0, mul_comm]
      _ ≤ L.sc.b := Real.exp_le_exp.mpr h3
  · have hr := hQ.2.2.2.2.2.2.2
    have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
      have hn : ∀ n : ℕ, Real.sqrt n ≤ n := by
        intro n
        rw [Real.sqrt_le_left (by positivity)]
        exact_mod_cast Nat.le_self_pow two_ne_zero n
      exact_mod_cast hn (D.host.q * D.host.d)
    have hn0 : (0 : ℝ) ≤ D.R.n := by positivity
    have hqd : (0 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by positivity
    have hc : D.host.rdE ≤ szCond L := by
      unfold szCond
      nlinarith [mul_le_mul_of_nonneg_left hs hn0, mul_nonneg hn0 hqd]
    refine hc.trans ?_
    rcases le_total (szCond L) 1 with h | h
    · exact h.trans hb1
    · have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ hT.1
      calc szCond L ≤ szCond L ^ 36 := le_self_pow₀ h (by norm_num)
        _ ≤ szCond L ^ 36 * (D.R.t : ℝ) ^ 150 := le_mul_of_one_le_right (by positivity) ht
        _ ≤ Real.sqrt L.sc.b := hC
        _ ≤ L.sc.b := by
          rw [Real.sqrt_le_left (by linarith)]
          nlinarith
  · refine le_trans ?_ hD.1
    have : (D.R.k : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
      exact_mod_cast Nat.le_add_right _ _
    gcongr

theorem family_sizes_eventually_large : ∀ (eps : ℝ) (Fm : FamP eps) (M : ℝ), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Fm.x1 < x ∧ M ≤ ((Fm.D x i).R.m : ℝ) ∧ M ≤ (Fm.L x i).sc.L ∧ ((Fm.D x i).R.k : ℝ) ^ M ≤ (Fm.L x i).sc.b ∧ (Fm.D x i).host.rdE ≤ (Fm.L x i).sc.b ∧ ((Fm.D x i).R.k : ℝ) * ((Fm.D x i).R.m : ℝ) ^ 10 ≤ ((Fm.D x i).s.Del : ℝ) := by
  intro eps Fm M
  have he : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]
    exact (Fm.L 0 i).sc.eps_pos
  have e1 : ∀ᶠ x : ℝ in atTop, M ≤ x ^ (1 / 4 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop M
  have e2 : ∀ᶠ x : ℝ in atTop, M ≤ x ^ eps := (tendsto_rpow_atTop he).eventually_ge_atTop M
  have e3 : ∀ᶠ x : ℝ in atTop, 5 * |M| * Real.log x ≤ x ^ eps := by
    have := ((isLittleO_log_rpow_atTop he).const_mul_left (5 * |M|)).bound one_pos
    filter_upwards [this, eventually_ge_atTop 0] with x hx h0
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 _)] at hx
    exact (le_abs_self _).trans hx
  obtain ⟨x0, hx0⟩ := eventually_atTop.mp (e1.and (e2.and (e3.and (eventually_gt_atTop Fm.x1))))
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := hx0 x hx
  refine ⟨a4, sizes_large_of_power_bounds (Fm.L x i) (Fm.sizes x a4 i) M ?_ ?_ ?_⟩ <;>
    simp only [Fm.L_x x i a4, Fm.L_eps x i] <;> assumption

end GlobalTheory
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem measurePreserving_of_sum_sq_eq : ∀ (k a b : ℕ), k = a + b → ∀ Q : (Fin k → ℝ) →ₗ[ℝ] (Fin a → ℝ) × (Fin b → ℝ), (∀ z, ∑ i, (Q z).1 i ^ 2 + ∑ i, (Q z).2 i ^ 2 = ∑ i, z i ^ 2) → MeasurePreserving Q volume volume := by
  intro k a b hk Q hQ
  let L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin a ⊕ Fin b) :=
    (WithLp.linearEquiv 2 ℝ (Fin a ⊕ Fin b → ℝ)).symm.toLinearMap ∘ₗ
      (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) ℝ ℝ).symm.toLinearMap ∘ₗ Q ∘ₗ
      (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).toLinearMap
  have hL : ∀ z, ‖L z‖ = ‖z‖ := by
    intro z
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp only [Real.norm_eq_abs, sq_abs, Fintype.sum_sum_type]
    rw [← hQ z.ofLp]
    rfl
  let Li : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a ⊕ Fin b) := ⟨L, hL⟩
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin k))
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin a ⊕ Fin b)) := by
    simp [hk]
  have h1 := (Li.toLinearIsometryEquiv hd).measurePreserving
  have h2 := PiLp.volume_preserving_toLp (Fin k)
  have h3 := PiLp.volume_preserving_ofLp (Fin a ⊕ Fin b)
  have h4 := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => ℝ)
  have h := h4.comp (h3.comp (h1.comp h2))
  exact h

end GlobalTheory.IwConst
end
