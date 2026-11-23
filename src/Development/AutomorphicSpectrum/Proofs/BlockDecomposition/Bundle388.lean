module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle483
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle291
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle374
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle112
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle381
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SqIntHecke

theorem lintegral_sq_lt_top_of_cover {X ι κ : Type*} [MeasurableSpace X] (μ : Measure X) (F : X → ℝ) [Finite ι]
    [Countable κ] (A : ι → κ → Set X) (hcov : ∀ x, ∃ i j, x ∈ A i j) (b w : ι → κ → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (E : ENNReal) (hE : E < ⊤) (hF : ∀ i j, ∀ x ∈ A i j, ‖F x‖ ≤ b i j)
    (hμ : ∀ i j, μ (A i j) ≤ ENNReal.ofReal (w i j) * E)
    (hsum : ∀ i, Summable fun j => b i j ^ 2 * w i j) :
    ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂μ < ⊤ := by
  classical
  have := Fintype.ofFinite ι
  have hu : (⋃ p : ι × κ, A p.1 p.2) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨i, j, h⟩ := hcov x
    exact ⟨(i, j), h⟩
  have h1 : ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂μ ≤ ∑' p : ι × κ, ∫⁻ x in A p.1 p.2, ‖F x‖ₑ ^ (2 : ℝ) ∂μ := by
    conv_lhs => rw [← setLIntegral_univ, ← hu]
    exact lintegral_iUnion_le _ _
  have h2 : ∀ p : ι × κ, ∫⁻ x in A p.1 p.2, ‖F x‖ₑ ^ (2 : ℝ) ∂μ ≤
      ENNReal.ofReal (b p.1 p.2 ^ 2 * w p.1 p.2) * E := by
    rintro ⟨i, j⟩
    have h3 : ∫⁻ x in A i j, ‖F x‖ₑ ^ (2 : ℝ) ∂μ ≤ ∫⁻ x in A i j, ENNReal.ofReal (b i j ^ 2) ∂μ := by
      refine setLIntegral_mono measurable_const fun x hx => ?_
      rw [ENNReal.rpow_two, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hF i j x hx) 2)
    refine h3.trans ?_
    rw [setLIntegral_const, ENNReal.ofReal_mul (sq_nonneg _), mul_assoc]
    gcongr
    exact hμ i j
  refine (h1.trans (ENNReal.tsum_le_tsum h2)).trans_lt ?_
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_prod (f := fun i j => ENNReal.ofReal (b i j ^ 2 * w i j))]
  refine ENNReal.mul_lt_top ?_ hE
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (sq_nonneg _) (hw i j)) (hsum i)]
  exact ENNReal.ofReal_lt_top

theorem sq_mul_pow_eq {r : ℕ} (q : ℝ) (e g : Fin r → ℕ) (ρ : Fin r → ℝ) (C : ℝ) :
    (C * ∏ j, ρ j ^ g j) ^ 2 * q ^ (∑ j, g j * e j) = C ^ 2 * ∏ j, (q ^ e j * ρ j ^ 2) ^ g j := by
  have h1 : ∏ j, (q ^ e j) ^ g j = q ^ (∑ j, g j * e j) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun j _ => by rw [← pow_mul, mul_comm]
  have h2 : ∏ j, (ρ j ^ 2) ^ g j = (∏ j, ρ j ^ g j) ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun j _ => by rw [← pow_mul, ← pow_mul, mul_comm]
  simp only [mul_pow _ _ (g _)]
  rw [Finset.prod_mul_distrib, h1, h2, mul_pow C, mul_assoc, mul_comm (q ^ _)]

theorem isSqIntCoeff_of_heckeSpectral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π → Zls.UnitaryCentral π →
    Zls.HeckeSpectral π → IsSqIntCoeff π := by
  intro k _ _ _ _ N V _ _ π hs hi ha hu hH
  unfold IsSqIntCoeff CoeffLp
  intro _ _ μ hμ v l hl
  have hcen : ∀ z ∈ Subgroup.center (GL (Fin N) k), ∀ w, ‖l (π z w)‖ = ‖l w‖ := by
    intro z hz w
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
    obtain ⟨t, rfl⟩ := hz
    obtain ⟨c, hc⟩ := GlobalTheory.T.admissible_irreducible_central_scalar k N V π hs hi ha t
    rw [hc, map_smul, norm_smul, hu t c hc, one_mul]
  have hF : ∀ g : GL (Fin N) k, ‖l (π (QuotientGroup.mk g : AdGL k N).out v)‖ = ‖l (π g v)‖ := by
    intro g
    obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL (Fin N) k)) g
    rw [hz, Subgroup.mem_center_iff.1 z.2 g, map_mul, Module.End.mul_apply, hcen _ z.2]
  have hmeas : AEStronglyMeasurable (fun q : AdGL k N => ‖l (π q.out v)‖) μ := by
    refine Continuous.aestronglyMeasurable ((QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_)
    rw [show (fun q : AdGL k N => ‖l (π q.out v)‖) ∘ QuotientGroup.mk = fun g => ‖l (π g v)‖ from funext hF]
    exact ((SqIntBridge.isLocallyConstant_orbit hs v).comp fun w => ‖l w‖).continuous
  refine ⟨fun q => ‖l (π q.out v)‖, hF, ?_⟩
  unfold MemLp
  rw [show ENNReal.ofReal 2 = 2 by simp, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hmeas]
  simp only [ENNReal.toReal_ofNat]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : Subsingleton (GL (Fin 0) k) := inferInstance
    have h1 : Subsingleton (AdGL k 0) := ⟨fun x y => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      rw [Subsingleton.elim a b]⟩
    have h2 : μ Set.univ < ⊤ := isCompact_univ.measure_lt_top
    refine lintegral_sq_lt_top_of_cover μ _ (fun _ _ : Unit => Set.univ) (fun _ => ⟨(), (), trivial⟩)
      (fun _ _ => ‖l (π (1 : AdGL k 0).out v)‖) (fun _ _ => 1) (fun _ _ => zero_le_one) _ h2 ?_ (by simp)
      (fun _ => (hasSum_fintype _).summable)
    intro _ _ x _
    rw [Subsingleton.elim x 1, norm_norm]
  obtain ⟨m1, hm1, hK1⟩ := GlobalTheory.T.congruence_subgroup_basis_nhds k N _ (hs v) (by simp)
  obtain ⟨m2, hm2, hK2⟩ := GlobalTheory.T.congruence_subgroup_basis_nhds k N _ hl (by simp [Module.End.one_eq_id])
  have hm : 1 ≤ max m1 m2 := hm1.trans (le_max_left _ _)
  obtain ⟨m, hmm⟩ : ∃ m, m = max m1 m2 := ⟨_, rfl⟩
  rw [← hmm] at hm
  have hv : v ∈ fixed π (Zls.Km k N m) := by
    rintro ⟨x, hx⟩
    have : π x v = v := hK1 (GlobalTheory.T.congruence_subgroup_antitone k N m1 m (hmm ▸ le_max_left _ _) hx)
    simpa using this
  have hlK : ∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l := fun x hx =>
    hK2 (GlobalTheory.T.congruence_subgroup_antitone k N m2 m (hmm ▸ le_max_right _ _) hx)
  obtain ⟨s, hsK, hcov⟩ := GlobalTheory.T.cartan_decomposition_congruence k N m hm hN
  have key : ∀ p : s, ∃ (C : ℝ) (ρ : Fin (N - 1) → ℝ), (∀ j, 0 ≤ ρ j) ∧
      (∀ j : Fin (N - 1), (Nat.card 𝓀[k] : ℝ) ^ (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) * ρ j ^ 2 < 1) ∧
      ∀ g : Fin (N - 1) → ℕ, ∀ x ∈ Zls.Km k N m, ∀ y ∈ Zls.Km k N m,
        ‖l (π (p.1.1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p.1.2) v)‖ ≤ C * ∏ j, ρ j ^ g j := by
    rintro ⟨p, hp⟩
    obtain ⟨h1, h2⟩ := hsK p hp
    obtain ⟨hf, hli, heq⟩ := GlobalTheory.T.matrix_coefficient_cartan_translate k N V π m v hv l hlK p.1 p.2 h1 h2
    obtain ⟨C, ρ, hρ0, hρ1, hb⟩ := GlobalTheory.T.matrix_coefficient_hecke_decay k N V π hs ha hH m hm (π p.2 v) hf (l ∘ₗ π p.1) hli
    refine ⟨C, ρ, hρ0, hρ1, fun g x hx y hy => ?_⟩
    rw [heq _ x hx y hy]
    exact hb g
  choose C ρ hρ0 hρ1 hbound using key
  refine lintegral_sq_lt_top_of_cover μ _
    (fun (p : s) (g : Fin (N - 1) → ℕ) => (QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
      {h | ∃ x ∈ Zls.Km k N m, ∃ y ∈ Zls.Km k N m, h = p.1.1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p.1.2})
    ?_ (fun p g => C p * ∏ j, ρ p j ^ g j)
    (fun _ g => (Nat.card 𝓀[k] : ℝ) ^ (∑ j : Fin (N - 1), g j * (((j : ℕ) + 1) * (N - ((j : ℕ) + 1)))))
    (fun _ _ => by positivity)
    (μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k))))
    (GlobalTheory.T.congruence_subgroup_finite_volume k N μ hμ m) ?_ ?_ ?_
  · intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨p, hp, g, a, ha', b, hb, z, hz, rfl⟩ := hcov h
    exact ⟨⟨p, hp⟩, g, _, ⟨a, ha', b, hb, rfl⟩, (QuotientGroup.mk_mul_of_mem _ hz).symm⟩
  · rintro p g _ ⟨h, ⟨a, ha', b, hb, rfl⟩, rfl⟩
    show ‖‖l (π (QuotientGroup.mk _ : AdGL k N).out v)‖‖ ≤ _
    rw [norm_norm, hF]
    exact hbound p g a ha' b hb
  · intro p g
    obtain ⟨h1, h2⟩ := hsK p.1 p.2
    refine (GlobalTheory.T.double_coset_volume_le k N μ hμ m hm p.1.1 p.1.2 h1 h2 g).trans_eq ?_
    rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  · intro p
    have h := GlobalTheory.CompanionTheory.Summability.summable_prod_pow_multiIndex (N - 1)
      (fun j => (Nat.card 𝓀[k] : ℝ) ^ (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) * ρ p j ^ 2)
      (fun j => by positivity) (hρ1 p)
    exact (h.mul_left (C p ^ 2)).congr fun g => (sq_mul_pow_eq _ _ g _ _).symm

end GlobalTheory.CompanionTheory.SqIntHecke
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProd

universe u

theorem sub_positions_univ {α : Type u} {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (i : Fin h) :
    ∃ o : Fin (sub W c i).length → Fin W.length, StrictMono o ∧ (∀ j, c j = i ↔ j ∈ Set.range o) ∧
      ∀ a, (sub W c i).get a = W.get (o a) := by
  have key : ∀ L : List (Fin W.length), L.Pairwise (· < ·) → (∀ j, j ∈ L ↔ c j = i) →
      ∃ o : Fin (L.map W.get).length → Fin W.length, StrictMono o ∧ (∀ j, c j = i ↔ j ∈ Set.range o) ∧
        ∀ a, (L.map W.get).get a = W.get (o a) := by
    intro L hpw hmem
    have hlen : (L.map W.get).length = L.length := by simp
    refine ⟨fun a => L.get (Fin.cast hlen a), ?_, ?_, ?_⟩
    · intro a b hab
      have hab' : Fin.cast hlen a < Fin.cast hlen b := by
        first
        | exact hab
        | simpa [Fin.lt_def] using hab
      exact List.pairwise_iff_get.1 hpw (Fin.cast hlen a) (Fin.cast hlen b) hab'
    · intro j
      constructor
      · intro hj
        obtain ⟨n, hn⟩ := List.mem_iff_get.1 ((hmem j).2 hj)
        refine ⟨Fin.cast hlen.symm n, ?_⟩
        first
        | exact hn
        | simpa using hn
      · rintro ⟨a, rfl⟩
        exact (hmem _).1 (List.mem_iff_get.2 ⟨_, rfl⟩)
    · intro a
      simp [List.get_eq_getElem]
  exact key ((List.finRange W.length).filter (fun p => decide (c p = i)))
    ((List.pairwise_lt_finRange _).filter _) (fun j => by simp)

end GlobalTheory.CompanionTheory.FineProd

namespace GlobalTheory.CompanionTheory.FineProd

theorem jm_row : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (W : List (IrrGL (k := k))) (c : Fin W.length → Fin h) (i : Fin h) (Y : Fin W.length → IrrGL (k := k)), (∀ j, c j = i → Y j = W.get j) → (∀ j, c j ≠ i → (Y j).1 = 0) → ∀ (hd : ∑ j, (Y j).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), jm Y hd π = jmL (sub W c i) π := by
  intro k _ _ _ _ h N W c i Y hY h0 hd V _ _ π
  obtain ⟨o, ho, hr, hg⟩ := sub_positions_univ W c i
  have hget : (sub W c i).get = fun a => Y (o a) := by
    funext a
    rw [hg a, hY (o a) ((hr (o a)).2 ⟨a, rfl⟩)]
  have hsum : ∑ a, (Y (o a)).1 = N := by
    rw [← hd]
    have himg : ∑ j ∈ Finset.univ.image o, (Y j).1 = ∑ a, (Y (o a)).1 :=
      Finset.sum_image (fun a _ b _ e => ho.injective e)
    rw [← himg]
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro j _ hj
    refine h0 j ?_
    intro e
    obtain ⟨a, rfl⟩ := (hr j).1 e
    exact hj (Finset.mem_image_of_mem o (Finset.mem_univ a))
  have hnz : ∀ j, (Y j).1 ≠ 0 → j ∈ Set.range o := by
    intro j hj
    refine (hr j).1 ?_
    by_contra e
    exact hj (h0 j e)
  have hdeg : ∑ a, ((sub W c i).get a).1 = N := by
    rw [hget]
    exact hsum
  have hcongr : ∀ {r : ℕ} (x y : Fin r → IrrGL (k := k)) (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N),
      x = y → jm x hx π = jm y hy π := by
    intro r x y hx hy e
    subst e
    rfl
  rw [GlobalTheory.T.jacquet_multiplicity_drop_zero_blocks Y hd o ho hnz hsum π, jmL, dite_eq_left hdeg]
  exact hcongr _ _ _ _ hget.symm

end GlobalTheory.CompanionTheory.FineProd
end

section

open MeasureTheory Matrix
open scoped NNReal

namespace GlobalTheory.CompanionTheory.GLUnimod

variable {n : ℕ}

noncomputable def dg (d : Fin n → ℂˣ) : GL (Fin n) ℂ where
  val := diagonal fun i => (d i : ℂ)
  inv := diagonal fun i => (((d i)⁻¹ : ℂˣ) : ℂ)
  val_inv := by simp [diagonal_mul_diagonal, diagonal_one]
  inv_val := by simp [diagonal_mul_diagonal, diagonal_one]

theorem dg_mul (d e : Fin n → ℂˣ) : dg (d * e) = dg d * dg e := by
  apply Units.ext
  simp [dg, diagonal_mul_diagonal]

theorem dg_one : dg (1 : Fin n → ℂˣ) = 1 := by
  apply Units.ext
  simp [dg, diagonal_one]

noncomputable def pm (σ : Equiv.Perm (Fin n)) : GL (Fin n) ℂ where
  val := σ.toPEquiv.toMatrix
  inv := σ.symm.toPEquiv.toMatrix
  val_inv := by
    rw [PEquiv.toMatrix_toPEquiv_mul]
    ext i j
    simp [Matrix.one_apply]
  inv_val := by
    rw [PEquiv.toMatrix_toPEquiv_mul]
    ext i j
    simp [Matrix.one_apply]

theorem pm_mul_dg (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂˣ) :
    pm σ * dg d = dg (d ∘ σ) * pm σ := by
  ext1
  ext i j
  simp only [pm, dg, Units.val_mul, mul_diagonal, diagonal_mul, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Function.comp_apply]
  split_ifs with h
  · subst h
    ring
  · ring

noncomputable def tv {i j : Fin n} (hij : i ≠ j) (c : ℂ) : GL (Fin n) ℂ where
  val := transvection i j c
  inv := transvection i j (-c)
  val_inv := by rw [transvection_mul_transvection_same _ _ hij]; simp
  inv_val := by rw [transvection_mul_transvection_same _ _ hij]; simp

theorem tv_mul {i j : Fin n} (hij : i ≠ j) (c : ℂ) : tv hij c * tv hij c = tv hij (2 * c) := by
  ext1
  simp only [tv, Units.val_mul]
  rw [transvection_mul_transvection_same _ _ hij, two_mul]

theorem dg_mul_tv {i j : Fin n} (hij : i ≠ j) (c : ℂ) (d : Fin n → ℂˣ) (hi : (d i : ℂ) = 2)
    (hj : (d j : ℂ) = 1) : dg d * tv hij c = tv hij (2 * c) * dg d := by
  ext1
  ext k l
  simp only [dg, tv, Units.val_mul, transvection, diagonal_mul, mul_diagonal, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  by_cases hk : i = k <;> by_cases hl : j = l
  · subst hk hl
    simp [hij, hi, hj]
  · subst hk
    simp [hl]
    split_ifs with h <;> simp only [h]
  · subst hl
    simp [hk]
    split_ifs with h <;> simp only [h]
  · simp [hk, hl]
    split_ifs with h <;> simp only [h]

theorem char_ne_zero {H : Type*} [Group H] (χ : H →* ℝ≥0) (g : H) : χ g ≠ 0 := by
  intro h
  have h1 : χ g * χ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem char_tv (χ : GL (Fin n) ℂ →* ℝ≥0) {i j : Fin n} (hij : i ≠ j) (c : ℂ) :
    χ (tv hij c) = 1 := by
  have h1 : χ (tv hij c) * χ (tv hij c) = χ (tv hij (2 * c)) := by rw [← map_mul, tv_mul]
  let d : Fin n → ℂˣ := fun k => if k = i then Units.mk0 2 two_ne_zero else 1
  have hi : (d i : ℂ) = 2 := by simp [d]
  have hj : (d j : ℂ) = 1 := by simp [d, hij.symm]
  have h2 : χ (dg d) * χ (tv hij c) = χ (tv hij (2 * c)) * χ (dg d) := by
    rw [← map_mul, ← map_mul, dg_mul_tv hij c d hi hj]
  have h3 : χ (tv hij c) = χ (tv hij (2 * c)) := by
    rw [mul_comm (χ (tv hij (2 * c)))] at h2
    exact mul_left_cancel₀ (char_ne_zero χ _) h2
  have h4 : χ (tv hij c) * χ (tv hij c) = χ (tv hij c) * 1 := by rw [mul_one, h1, h3]
  exact mul_left_cancel₀ (char_ne_zero χ _) h4

theorem char_dg (χ : GL (Fin n) ℂ →* ℝ≥0) (hz : ∀ z : GL (Fin n) ℂ, (∀ g, z * g = g * z) → χ z = 1)
    (d : Fin n → ℂˣ) : χ (dg d) = 1 := by
  let D : (Fin n → ℂˣ) →* GL (Fin n) ℂ :=
    { toFun := dg, map_one' := dg_one, map_mul' := dg_mul }
  have hperm : ∀ σ : Equiv.Perm (Fin n), χ (dg (d ∘ σ)) = χ (dg d) := by
    intro σ
    have h := congrArg χ (pm_mul_dg σ d)
    rw [map_mul, map_mul, mul_comm (χ (pm σ))] at h
    exact (mul_right_cancel₀ (char_ne_zero χ (pm σ)) h).symm
  obtain ⟨v, hv_def⟩ : ∃ v : Fin n → ℂˣ, v = ∏ σ : Equiv.Perm (Fin n), d ∘ σ := ⟨_, rfl⟩
  have hv : ∀ k l, v k = v l := by
    intro k l
    rw [hv_def, Finset.prod_apply, Finset.prod_apply]
    exact Fintype.prod_equiv (Equiv.mulRight (Equiv.swap k l)) _ _
      (fun σ => by simp [Equiv.Perm.mul_apply, Equiv.swap_apply_right])
  have hcent : ∀ g, dg v * g = g * dg v := by
    intro g
    ext1
    ext k l
    simp only [dg, Units.val_mul, diagonal_mul, mul_diagonal]
    rw [hv k l, mul_comm]
  have h1 : χ (dg v) = 1 := hz _ hcent
  have h2 : χ (dg v) = χ (dg d) ^ (Fintype.card (Equiv.Perm (Fin n))) := by
    have e : χ (dg v) = (χ.comp D) v := rfl
    rw [e, hv_def, map_prod]
    simp only [MonoidHom.comp_apply, D, MonoidHom.coe_mk, OneHom.coe_mk, hperm]
    rw [Finset.prod_const, Finset.card_univ]
  have hm : Fintype.card (Equiv.Perm (Fin n)) ≠ 0 := Fintype.card_ne_zero
  rw [h1] at h2
  exact (pow_eq_one_iff_of_nonneg (by simp) hm).1 h2.symm

theorem char_eq_one (χ : GL (Fin n) ℂ →* ℝ≥0)
    (hz : ∀ z : GL (Fin n) ℂ, (∀ g, z * g = g * z) → χ z = 1) (g : GL (Fin n) ℂ) : χ g = 1 := by
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ u : GL (Fin n) ℂ, (u : Matrix (Fin n) (Fin n) ℂ) = M → χ u = 1)
    (g : Matrix (Fin n) (Fin n) ℂ) ?_ ?_ ?_ ?_ g rfl
  · exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  · intro D hD u hu
    rw [det_diagonal] at hD
    have hD' : ∀ i, D i ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
    have hu' : u = dg (fun i => Units.mk0 (D i) (hD' i)) := by
      ext1
      simp [hu, dg]
    rw [hu']
    exact char_dg χ hz _
  · intro t u hu
    have hu' : u = tv t.hij t.c := by
      ext1
      simp [hu, tv, Matrix.TransvectionStruct.toMatrix]
    rw [hu']
    exact char_tv χ t.hij t.c
  · intro A B hA hB hPA hPB u hu
    obtain ⟨a, rfl⟩ : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hA)
    obtain ⟨b, rfl⟩ : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).2 (isUnit_iff_ne_zero.2 hB)
    have hu' : u = a * b := by
      ext1
      simp [hu]
    rw [hu', map_mul, hPA a rfl, hPB b rfl, one_mul]

theorem unimod : PositivityTheory.RgBcC.Unimod := by
  intro n _ _ μ _
  haveI : T2Space (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (T2Space (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) ℂ)).symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (PositivityTheory.RgTw.G n) :=
    (Units.isClosedEmbedding_embedProduct :
      Topology.IsClosedEmbedding (Units.embedProduct (Matrix (Fin n) (Fin n) ℂ))).locallyCompactSpace
  haveI : SecondCountableTopology (PositivityTheory.RgTw.G n) :=
    (Units.isEmbedding_embedProduct :
      Topology.IsEmbedding (Units.embedProduct (Matrix (Fin n) (Fin n) ℂ))).secondCountableTopology
  have hmap : ∀ g : PositivityTheory.RgTw.G n,
      Measure.map (· * g) μ = Measure.modularCharacter g • μ := by
    intro g
    have e1 := Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ
    have e2 := Measure.modularCharacterFun_eq_haarScalarFactor μ g
    rw [← e2] at e1
    exact e1
  have hχ : ∀ g : PositivityTheory.RgTw.G n, Measure.modularCharacter g = 1 := by
    refine char_eq_one Measure.modularCharacter ?_
    intro z hz
    have hc : Measure.map (· * z) μ = μ := by
      have h : (fun x => x * z) = (fun x => z * x) := funext fun x => (hz x).symm
      rw [h, map_mul_left_eq_self]
    have e2 := Measure.modularCharacterFun_eq_haarScalarFactor μ z
    simp only [hc, Measure.haarScalarFactor_self] at e2
    exact e2
  have hR : μ.IsMulRightInvariant := ⟨fun g => by rw [hmap, hχ g, one_smul]⟩
  exact ⟨hR, GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ⟩

end GlobalTheory.CompanionTheory.GLUnimod
end

section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Casselman

theorem mk_mem_fixed_jac : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ v : fixed π J, (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) ∈ fixed (_root_.GlobalTheory.SmGL.jac (stdBlocks d hd) π) (KM k N J d hd) := by
  intro k _ _ _ _ N h d hd J _ hc _ _ V _ _ π _ v x
  have hx : leviEmb k (stdBlocks d hd) (x : Levi k (Bl d)) ∈ J := x.2
  have hv : π (leviEmb k (stdBlocks d hd) (x : Levi k (Bl d))) (v : V) = (v : V) := by
    simpa using v.2 ⟨_, hx⟩
  have hδ : deltaHalf k (Bl d) (x : Levi k (Bl d)) = 1 := GlobalTheory.T.modulus_trivial_on_levi_compact k N h d hd J hc x x.2
  rw [_root_.GlobalTheory.SmGL.jac_mk, hv, hδ]
  simp

end GlobalTheory.CompanionTheory.Casselman
end
