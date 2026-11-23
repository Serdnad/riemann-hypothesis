module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.DualLattices.RidConvolutionDerivation
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AevalSurjectiveOfSpanCotangent
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Formalism.RealPlaceAnalysis.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle428
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle429
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle340
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.HeightOneDual

variable {K H : Type} [Field K] [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H]

theorem cobOne_toConv_eq_zero {δ : H →ₗ[K] K} (hδ : ReciprocityTheory.PGsh.IsPtDer δ) :
    cobOne K (CartierDual K H) (WithConv.toConv δ) = 0 := by
  rw [cobOne_apply, sub_sub, sub_eq_zero, CartierDual.comul_eq_iff]
  intro a b
  rw [map_add (f := _), LinearMap.add_apply, CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul,
    CartierDual.one_apply, CartierDual.one_apply]
  change _ = δ (a * b)
  rw [hδ a b]
  change δ a * counit b + counit a * δ b = _
  ring

theorem apply_convD (φ : CartierDual K H) (δ : H →ₗ[K] K) (y : H) :
    φ (ReciprocityTheory.PGsh.convD δ y) = (φ * WithConv.toConv δ) y := by
  rw [CartierDual.mul_apply, CartierDual.pair_tmul]
  simp only [ReciprocityTheory.PGsh.convD, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  generalize comul (R := K) y = t
  induction t with
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | tmul a b => simp [mul_comm]

theorem adjoin_primitive_eq_top : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H],
    (∀ a ∈ augIdeal K H, a ^ p = 0) →
    Algebra.adjoin K {φ : CartierDual K H | cobOne K (CartierDual K H) φ = 0} = ⊤ := by
  intro p hp K H _ _ _ _ _ _ hpow
  classical
  set ε := counitAlgHom K H with hεdef
  set S := Algebra.adjoin K {φ : CartierDual K H | cobOne K (CartierDual K H) φ = 0} with hSdef
  haveI : Module.Finite K (AugCot ε) := Module.Finite.of_surjective _ (AugCot.d_surjective ε)
  let b := Module.finBasis K (AugCot ε)
  choose x hx using fun i => (RingHom.ker ε).toCotangent_surjective (b i)
  let y : Fin (Module.finrank K (AugCot ε)) → H := fun i => (x i : H)
  have hy : ∀ i, y i ∈ RingHom.ker ε := fun i => (x i).2
  have hsum : ∀ l : Fin (Module.finrank K (AugCot ε)) → K,
      AugCot.d ε (∑ i, l i • y i) = ∑ i, l i • b i := by
    intro l

    simp [y, map_sum, hx]
  have hmem : ∀ l : Fin (Module.finrank K (AugCot ε)) → K, (∑ i, l i • y i) ∈ RingHom.ker ε := by
    intro l
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (hy i)
  have hspan : ∀ z ∈ RingHom.ker ε, ∃ l : Fin (Module.finrank K (AugCot ε)) → K,
      z - ∑ i, l i • y i ∈ RingHom.ker ε ^ 2 := by
    intro z hz
    refine ⟨b.repr (AugCot.d ε z), ?_⟩
    have h1 : AugCot.d ε (z - ∑ i, b.repr (AugCot.d ε z) i • y i) = 0 := by
      rw [map_sub, hsum, b.sum_repr, sub_self]
    rwa [AugCot.d_of_mem _ (sub_mem hz (hmem _)), Ideal.toCotangent_eq_zero] at h1
  have hind : ∀ l : Fin (Module.finrank K (AugCot ε)) → K,
      ∑ i, l i • y i ∈ RingHom.ker ε ^ 2 → l = 0 := by
    intro l hl
    have h1 : AugCot.d ε (∑ i, l i • y i) = 0 := by
      rw [AugCot.d_of_mem _ (hmem _), Ideal.toCotangent_eq_zero]
      exact hl
    rw [hsum] at h1
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent l h1 i
  have : IsNoetherianRing H := isNoetherian_of_tower K inferInstance
  have hnil : IsNilpotent (RingHom.ker ε) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro f hf
    exact ⟨p, hpow f hf⟩
  have hsurj := GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent ε hnil y hy hspan
  obtain ⟨δ, hδ, hδx⟩ := GlobalTheory.HeightOneHopf.exists_isPtDer_dual y hy hind

  let Z : Set H := {h | ∀ φ ∈ S, φ h = 0}
  have hZε : ∀ h ∈ Z, ε h = 0 := fun h hh => by
    have h1 := hh 1 S.one_mem
    rwa [CartierDual.one_apply] at h1
  have hZD : ∀ i, ∀ h ∈ Z, ReciprocityTheory.PGsh.convD (δ i) h ∈ Z := fun i h hh φ hφ => by
    rw [apply_convD]
    exact hh _ (S.mul_mem hφ (Algebra.subset_adjoin (cobOne_toConv_eq_zero (hδ i))))
  have hZ0 : ∀ h ∈ Z, h = 0 := by
    intro h hh
    obtain ⟨P, rfl⟩ := hsurj h
    have hc := ReciprocityTheory.PGsh.coeff_eq_zero_of_stable ε y hy (fun i => ReciprocityTheory.PGsh.convD (δ i))
      (fun i => ReciprocityTheory.PGsh.convD_mul _ (hδ i)) (fun i j =>
        (ReciprocityTheory.PGsh.counit_convD (δ i) (y j)).trans (hδx i j)) hsurj
      (CharP.cast_eq_zero K p) (fun n h0 hn => by
        rw [isUnit_iff_ne_zero, Ne, CharP.cast_eq_zero_iff K p]
        exact Nat.not_dvd_of_pos_of_lt h0 hn) Z hZε hZD P hh
    exact ReciprocityTheory.PGsh.aeval_eq_zero_of_mem_span y (fun j => hpow _ (hy j))
      (ReciprocityTheory.PGsh.mem_span_pow_of_coeff hc)

  let W : Submodule K (Module.Dual K H) :=
    (Subalgebra.toSubmodule S).map (CartierDual.toDual K H).toLinearMap
  have hW : W.dualCoannihilator = ⊥ := by
    refine eq_bot_iff.2 fun h hh => ?_
    rw [Submodule.mem_dualCoannihilator] at hh
    rw [Submodule.mem_bot]
    exact hZ0 h fun φ hφ => hh _ ⟨φ, hφ, rfl⟩
  have hWtop : W = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hW, Submodule.dualAnnihilator_bot]
  rw [← Algebra.toSubmodule_eq_top, eq_top_iff]
  intro φ _
  have h1 : CartierDual.toDual K H φ ∈ W := hWtop ▸ Submodule.mem_top
  obtain ⟨ψ, hψ, e⟩ := h1
  rwa [(CartierDual.toDual K H).injective e] at hψ

end GlobalTheory.HeightOneDual
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FinTypCount

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => maximalRealSubfield L

theorem countable_field : Countable L :=
  (Module.finBasis ℚ L).equivFun.toEquiv.injective.countable

theorem tmul_mem_ALint (o : 𝓞 L) {a : AFplus L} (ha : ∀ v, a v ∈ v.adicCompletionIntegers L⁺) :
    ((o : L) ⊗ₜ[L⁺] a : AL L) ∈ ALint L := by
  have h1 : ((o : L) ⊗ₜ[L⁺] (1 : AFplus L) : AL L) ∈ ALint L :=
    Subring.subset_closure (Or.inl ⟨o, rfl⟩)
  have h2 : ((1 : L) ⊗ₜ[L⁺] a : AL L) ∈ ALint L :=
    Subring.subset_closure (Or.inr ⟨a, ha, rfl⟩)
  have := Subring.mul_mem _ h1 h2
  rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this

theorem exists_nat_smul_int (e : L) : ∃ D : ℕ, 0 < D ∧ ∃ o : 𝓞 L, (o : L) = D • e := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := L) ({e} : Finset L)
  refine ⟨(y * y).natAbs, Int.natAbs_pos.2 (mul_ne_zero hy hy), ?_⟩
  have hi : IsIntegral ℤ ((y * y).natAbs • e) := by
    rw [← natCast_zsmul, Int.natAbs_of_nonneg (mul_self_nonneg y), mul_smul]
    exact (h e (Finset.mem_singleton_self e)).smul y
  exact ⟨⟨_, hi⟩, rfl⟩

theorem exists_approx (M : ℕ) (hM : 0 < M) (x : AL L) :
    ∃ c : L, ∃ y ∈ ALint L, x = c ⊗ₜ[L⁺] (1 : AFplus L) + M • y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    obtain ⟨c, y, hy, rfl⟩ := hx
    obtain ⟨c', y', hy', rfl⟩ := hx'
    exact ⟨c + c', y + y', add_mem hy hy', by rw [TensorProduct.add_tmul, smul_add]; abel⟩
  | tmul e a =>
    obtain ⟨D, hD, o, ho⟩ := exists_nat_smul_int e
    obtain ⟨k, a', ha', rfl⟩ :=
      (GlobalTheory.AdLat.strong_approximation_mod_nat L⁺ (D * M) (Nat.mul_pos hD hM)).1 a
    refine ⟨algebraMap L⁺ L k * e, _, tmul_mem_ALint o ha', ?_⟩
    rw [TensorProduct.tmul_add, Algebra.algebraMap_eq_smul_one k, ← TensorProduct.smul_tmul,
      ← Algebra.smul_def, ho, TensorProduct.smul_tmul', TensorProduct.tmul_smul, mul_comm, mul_smul]
    simp only [TensorProduct.smul_tmul']

theorem exists_denom (x : AL L) : ∃ m : ℕ, 0 < m ∧ (m : AL L) * x ∈ ALint L := by
  obtain ⟨c, y, hy, rfl⟩ := exists_approx 1 one_pos x
  obtain ⟨D, hD, o, ho⟩ := exists_nat_smul_int c
  refine ⟨D, hD, ?_⟩
  have e1 : (D : AL L) * (c ⊗ₜ[L⁺] (1 : AFplus L)) = (o : L) ⊗ₜ[L⁺] (1 : AFplus L) := by
    rw [ho, ← nsmul_eq_mul, TensorProduct.smul_tmul']
  rw [mul_add, e1, one_smul]
  exact add_mem (tmul_mem_ALint o (fun v => one_mem _)) (Subring.mul_mem _ (natCast_mem _ _) hy)

variable {n : ℕ}

theorem exists_denom_matrix (G : Matrix (Fin n) (Fin n) (AL L)) :
    ∃ m : ℕ, 0 < m ∧ ∀ i j, (m : AL L) * G i j ∈ ALint L := by
  classical
  choose m hm h using fun p : Fin n × Fin n => exists_denom (G p.1 p.2)
  refine ⟨∏ p, m p, Finset.prod_pos fun p _ => hm p, fun i j => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ (i, j))
  rw [hk, Nat.cast_mul, mul_comm ((m (i, j) : ℕ) : AL L), mul_assoc]
  exact Subring.mul_mem _ (natCast_mem _ _) (h (i, j))

theorem exists_code (N : ℕ) (hN : 0 < N) (g : GAf L n) :
    ∃ p : ℕ × (Fin n → Fin n → L), 0 < p.1 ∧
      (∀ i j, (p.1 : AL L) * (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L) ∧
      ∀ i j, ∃ y ∈ ALint L, (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j =
        p.2 i j ⊗ₜ[L⁺] (1 : AFplus L) + (p.1 * N) • y := by
  obtain ⟨m, hm, h⟩ := exists_denom_matrix (g.1 : Matrix (Fin n) (Fin n) (AL L))
  choose c y hy e using fun i j =>
    exists_approx (m * N) (Nat.mul_pos hm hN) ((g.1 : Matrix (Fin n) (Fin n) (AL L)) i j)
  exact ⟨(m, c), hm, h, fun i j => ⟨y i j, hy i j, e i j⟩⟩

theorem inv_val (g : GAf L n) :
    (((g⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      conjT (conjAL L) (g.1 : Matrix (Fin n) (Fin n) (AL L)) := by
  have hm := g.2
  simp only [GA, UGroup, Subgroup.mem_mk] at hm
  exact Units.inv_eq_of_mul_eq_one_right hm

theorem cong_of_code {N m : ℕ} {c : Fin n → Fin n → L} {g g' : GAf L n}
    (hg : ∀ i j, (m : AL L) * (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L)
    (e : ∀ i j, ∃ y ∈ ALint L, (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j =
      c i j ⊗ₜ[L⁺] (1 : AFplus L) + (m * N) • y)
    (e' : ∀ i j, ∃ y ∈ ALint L, (g'.1 : Matrix (Fin n) (Fin n) (AL L)) i j =
      c i j ⊗ₜ[L⁺] (1 : AFplus L) + (m * N) • y) :
    Cong L n N (g⁻¹ * g') := by
  choose y hy ey using e
  choose y' hy' ey' using e'
  set A : Matrix (Fin n) (Fin n) (AL L) := (((g⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hAdef
  have hAint : ∀ i j, (m : AL L) * A i j ∈ ALint L := by
    intro i j
    rw [hAdef, inv_val]
    simp only [conjT, Matrix.transpose_apply, Matrix.map_apply]
    have := conjAL_mem_ALint L (hg j i)
    rwa [map_mul, map_natCast] at this
  have hAG : A * (g.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := Units.inv_mul g.1
  set Y : Matrix (Fin n) (Fin n) (AL L) := Matrix.of fun i j => y' i j - y i j
  have hG' : (g'.1 : Matrix (Fin n) (Fin n) (AL L)) =
      (g.1 : Matrix (Fin n) (Fin n) (AL L)) + (N : AL L) • ((m : AL L) • Y) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Y, Matrix.of_apply, smul_eq_mul, ey, ey',
      nsmul_eq_mul]
    push_cast
    ring
  have hk : (((g⁻¹ * g' : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      1 + (N : AL L) • (((m : AL L) • A) * Y) := by
    change A * (g'.1 : Matrix (Fin n) (Fin n) (AL L)) = _
    rw [hG', Matrix.mul_add, hAG, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hz : ∀ i j, (((m : AL L) • A) * Y) i j ∈ ALint L := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, Y, Matrix.of_apply, smul_eq_mul]
    exact Subring.sum_mem _ fun k _ =>
      Subring.mul_mem _ (hAint i k) (Subring.sub_mem _ (hy' k j) (hy k j))
  refine ⟨fun i j => ?_, fun i j => ⟨_, hz i j, ?_⟩⟩
  · show (((g⁻¹ * g' : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L
    rw [hk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine Subring.add_mem _ ?_ (Subring.mul_mem _ (natCast_mem _ _) (hz i j))
    rw [Matrix.one_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · rw [hk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring

theorem rt_mul (h h' : GAf L n) (f : GAf L n → ℂ) : rt L n (h * h') f = rt L n h (rt L n h' f) := by
  funext x
  simp [rt, mul_assoc]

theorem countable_range_rt {f : GAf L n → ℂ} {N : ℕ} (hN : 0 < N)
    (hf : ∀ κ, Cong L n N κ → rt L n κ f = f) :
    (Set.range fun h : GAf L n => rt L n h f).Countable := by
  classical
  haveI := countable_field (L := L)
  choose p _ hp2 hp3 using exists_code (L := L) (n := n) N hN
  let Ψ : ℕ × (Fin n → Fin n → L) → (GAf L n → ℂ) := fun q =>
    if hq : ∃ g, p g = q then rt L n hq.choose f else 0
  have key : ∀ g, rt L n g f = Ψ (p g) := by
    intro g
    have hq : ∃ g', p g' = p g := ⟨g, rfl⟩
    simp only [Ψ, dif_pos hq]
    have e := hq.choose_spec
    have h3 := hp3 hq.choose
    rw [e] at h3
    have hc : Cong L n N (g⁻¹ * hq.choose) :=
      cong_of_code (c := (p g).2) (hp2 g) (hp3 g) h3
    calc rt L n g f = rt L n g (rt L n (g⁻¹ * hq.choose) f) := by rw [hf _ hc]
      _ = rt L n hq.choose f := by rw [← rt_mul, mul_inv_cancel_left]
  refine (Set.countable_range Ψ).mono ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨p g, (key g).symm⟩

end GlobalTheory.FinTypCount

namespace GlobalTheory


open GlobalTheory.FinTypCount in
theorem FinTyp.rank_le_aleph0 : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    (π : Formalism.L2.NG.FinTyp L n), Module.rank ℂ π.S ≤ Cardinal.aleph0 := by
  intro L _ _ _ n π
  obtain ⟨f, hfS, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne
  obtain ⟨N, hN, hfix⟩ := π.smooth f hfS
  let T := Submodule.span ℂ (Set.range fun h : GAf L n => rt L n h f)
  have hle : T ≤ π.S := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, rfl⟩
    exact π.stable h f hfS
  have hst : ∀ h, ∀ u ∈ T, rt L n h u ∈ T := by
    intro h u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h', rfl⟩ := hx
      exact Submodule.subset_span ⟨h * h', rt_mul h h' f⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have hfT : f ∈ T := Submodule.subset_span ⟨1, by funext x; simp [rt]⟩
  have hT : T = π.S := by
    rcases π.irr T hle hst with h | h
    · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ hfT)) hf0
    · exact h
  rw [← hT]
  exact (rank_span_le _).trans (Cardinal.le_aleph0_iff_set_countable.2 (countable_range_rt hN hfix))

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory

theorem exists_lift_finiteEtale_testRing : ∀ (Y Z : Scheme.{0}) (π : Z ⟶ Y), IsFinite π → Etale π → Surjective π →
    ∀ (K : Type) [Field K] (p : TRing K) (x : Sp p.R ⟶ Y), ∃ (q : TRing K) (ι : p.R →ₐ[K] q.R),
      (letI := ι.toRingHom.toAlgebra; Module.FaithfullyFlat p.R q.R ∧ Algebra.Etale p.R q.R) ∧
      ∃ z : Sp q.R ⟶ Z, z ≫ π = spMap ι.toRingHom ≫ x := by
  intro Y Z π hfin het hsurj K _ p x
  let P := pullback π x
  let f : P ⟶ Sp p.R := pullback.snd π x
  have : IsFinite f := inferInstance
  have : Etale f := inferInstance
  have : Surjective f := inferInstance
  have : IsAffine P := isAffine_of_isAffineHom f
  let g : Spec Γ(P, ⊤) ⟶ Spec (CommRingCat.of p.R) := P.isoSpec.inv ≫ f
  let φ : CommRingCat.of p.R ⟶ Γ(P, ⊤) := Spec.preimage g
  have hφ : Spec.map φ = g := Spec.map_preimage g
  have hg_et : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hg_surj : Surjective (Spec.map φ) := by rw [hφ]; infer_instance
  have hφet : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 hg_et
  have hφff : φ.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff φ).1 ⟨inferInstance, hg_surj⟩
  letI : Algebra p.R Γ(P, ⊤) := φ.hom.toAlgebra
  have hBet : Algebra.Etale p.R Γ(P, ⊤) := hφet
  have hBff : Module.FaithfullyFlat p.R Γ(P, ⊤) := hφff
  have hpred : _root_.IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  have hBred : _root_.IsReduced Γ(P, ⊤) := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced p.R Γ(P, ⊤)
  letI : Algebra K Γ(P, ⊤) := (φ.hom.comp (algebraMap K p.R)).toAlgebra
  haveI : IsScalarTower K p.R Γ(P, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FiniteType K Γ(P, ⊤) := Algebra.FiniteType.trans (S := p.R) inferInstance inferInstance
  obtain ⟨n, s, hs⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType K Γ(P, ⊤))
  have hrad : (RingHom.ker s).IsRadical := (Ideal.isRadical_iff_quotient_reduced _).2
    (isReduced_of_injective (Ideal.kerLiftAlg s) (Ideal.kerLiftAlg_injective s))
  let q : TRing K := ⟨n, RingHom.ker s, hrad⟩
  let e : q.R ≃ₐ[K] Γ(P, ⊤) := Ideal.quotientKerAlgEquivOfSurjective hs
  let φK : p.R →ₐ[K] Γ(P, ⊤) := { φ.hom with commutes' := fun _ => rfl }
  let ι : p.R →ₐ[K] q.R := e.symm.toAlgHom.comp φK
  refine ⟨q, ι, ?_, ?_⟩
  · letI := ι.toRingHom.toAlgebra
    let e' : Γ(P, ⊤) ≃ₐ[p.R] q.R := AlgEquiv.ofRingEquiv (f := e.symm.toRingEquiv) (fun _ => rfl)
    exact ⟨Module.FaithfullyFlat.of_linearEquiv _ _ e'.symm.toLinearEquiv, Algebra.Etale.of_equiv e'⟩
  · refine ⟨Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ P.isoSpec.inv ≫ pullback.fst π x, ?_⟩
    have hι : CommRingCat.ofHom ι.toRingHom = φ ≫ CommRingCat.ofHom e.symm.toRingHom := rfl
    rw [Category.assoc, Category.assoc, pullback.condition]
    change _ ≫ g ≫ x = _
    rw [← hφ, ← Category.assoc, ← Spec.map_comp, ← hι]

end GlobalTheory
end

section

noncomputable section

open Matrix
open Formalism.REAL (qdet qminor Tm)

namespace GlobalTheory.CentreFin

section Alg
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem qdet_mem {k : ℕ} {E : Fin k → Fin k → A} {S : Subalgebra ℂ A} (h : ∀ a b, E a b ∈ S) (u : ℂ) : qdet E u ∈ S := by
  unfold qdet qminor
  refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) ?_
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  unfold Tm
  refine Subalgebra.add_mem _ ?_ (h _ _)
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact Subalgebra.zero_mem _

theorem commute_qdet {k : ℕ} {E : Fin k → Fin k → A} {x : A} (h : ∀ a b, Commute x (E a b)) (u : ℂ) :
    Commute x (qdet E u) :=
  ((Subalgebra.mem_centralizer_iff ℂ).1 (qdet_mem (S := Subalgebra.centralizer ℂ {x})
    (fun a b => (Subalgebra.mem_centralizer_iff ℂ).2 fun _ hg => by rw [hg]; exact h a b) u) x rfl)

theorem exists_coef {k : ℕ} (E : Fin k → Fin k → A) (s : ℂ) {B : Subalgebra ℂ A} (hB : ∀ u, qdet E u ∈ B) :
    ∃ c : ℕ → A, c k = 1 ∧ (∀ j ≤ k, c j ∈ B) ∧ (∀ u, qdet E (u - s) = ∑ j ∈ Finset.range (k + 1), u ^ j • c j) ∧
      (∑ i, E i i = 0 ∨ ∃ j ≤ k, ∃ t : ℂ, ∑ i, E i i = c j + t • (1 : A)) := by
  cases k with
  | zero => exact ⟨fun _ => 1, rfl, fun _ _ => one_mem _, fun u => by simp [qdet, qminor], Or.inl (by simp)⟩
  | succ m =>
    obtain ⟨c, t, h1, h2, h3⟩ := GlobalTheory.T.shifted_capelli_determinant_subleading_coeff_trace A m E s
    refine ⟨c, h1, fun j hj => ?_, h3, Or.inr ⟨m, m.le_succ, -t, by rw [h2, neg_smul, add_neg_cancel_right]⟩⟩
    exact GlobalTheory.coeff_mem_of_poly_values_mem A (Subalgebra.toSubmodule B) _ c (fun u => h3 u ▸ hB _) j (Nat.lt_succ_of_le hj)

end Alg

section Loc
variable {n : ℕ} {J p q : Matrix (Fin n) (Fin n) ℂ}

end Loc

end GlobalTheory.CentreFin

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

theorem _root_.GlobalTheory.T.neg_inv_ratio_isNorm_of_neg_ratio_isNorm : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (δ : F) (b : Module.Basis (Fin 2) F E), b 0 = 1 → σ (b 1) = -b 1 → b 1 * b 1 = algebraMap F E δ → ∀ f₁ f₂ : F, f₁ ≠ 0 → f₂ ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] (ε : R) (t : R ⊗[F] E), algebraMap R (R ⊗[F] E) ε * (t * sigR R σ t + algebraMap F (R ⊗[F] E) (f₁ / f₂)) = 0 → ∃ p q : R, ε * (algebraMap F R (-(f₂ / f₁)) - (p ^ 2 - algebraMap F R δ * q ^ 2)) = 0 := by
  first | exact @GlobalTheory.PlaneSU.NormSwap.neg_inv_ratio_norm | exact GlobalTheory.PlaneSU.NormSwap.neg_inv_ratio_norm | (intros; apply GlobalTheory.PlaneSU.NormSwap.neg_inv_ratio_norm <;> assumption)
end
