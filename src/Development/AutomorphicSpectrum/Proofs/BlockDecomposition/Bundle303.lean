module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import GroundTheory.AutomorphicForms.GLnLocal
public import Mathlib.Order.CompletePartialOrder
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingDoubleCosetMeasurable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import GroundTheory.AutomorphicForms.InductionParabolic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle293
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
namespace ContractingCosetsPort
open ValuativeRel Matrix GroundTheory.Automorphic.GLnLocal
open GlobalTheory.CompanionTheory.ContractingCosets
variable {k : Type} [Field k] [ValuativeRel k]

theorem coe_leviEmb_zj {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h) :
    (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) : Matrix (Fin N) (Fin N) k) =
      diagonal fun i => if Zl.JC.blockIdx d hd i ≤ j then (t : k) else 1 := by
  apply GlobalTheory.CompanionTheory.ContractingCosets.coe_leviEmb_zj <;> assumption

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem le_of_mk_eq {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hpos : ∀ a, 0 < d a) (t : kˣ)
    (ht : valuation k (t : k) < 1) (j : Fin h) (hj : j.val + 1 < h) (m : ℕ)
    {x y x' y' : GL (Fin N) k} (hx : x ∈ congruenceSubgroup k N m)
    (hy : y ∈ congruenceSubgroup k N m) (hx' : x' ∈ congruenceSubgroup k N m)
    (hy' : y' ∈ congruenceSubgroup k N m) {r r' : ℕ}
    (e : (QuotientGroup.mk (x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y) : AdGL k N) =
      QuotientGroup.mk (x' * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r' * y')) :
    r' ≤ r := by
  have hz := QuotientGroup.eq.1 e
  have hK := congruenceSubgroup_le k N m
  have heq := eq_central_mul hz
  refine le_of_eq_central_mul (δ := fun i => if Zl.JC.blockIdx d hd i ≤ j then (t : k) else 1) t ht
    (fun i => ?_) (i₁ := stdBlocks d hd ⟨j, ⟨0, hpos j⟩⟩)
    (i₂ := stdBlocks d hd ⟨⟨j.val + 1, hj⟩, ⟨0, hpos _⟩⟩) ?_ ?_
    (coe_leviEmb_zj d hd t j)
    (mul_mem (inv_mem (hK hx')) (hK hx)) (mul_mem (hK hy) (inv_mem (hK hy'))) hz heq
  · by_cases hi : Zl.JC.blockIdx d hd i ≤ j
    · exact Or.inl (if_pos hi)
    · exact Or.inr (if_neg hi)
  · simp [Zl.JC.blockIdx]
  · have : ¬ (⟨j.val + 1, hj⟩ : Fin h) ≤ j := by
      rw [Fin.le_def]; simp
    simp [Zl.JC.blockIdx, this]

end ContractingCosetsPort


theorem _root_.GlobalTheory.T.contracting_double_coset_measurable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ a, 0 < d a) → ∀ (t : kˣ), ValuativeRel.valuation k (t : k) < 1 → ∀ (j : Fin h), j.val + 1 < h → ∀ (m : ℕ), 1 ≤ m → ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)], (∀ r : ℕ, MeasurableSet ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g | ∃ x ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, ∃ y ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, g = x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y})) ∧ Pairwise (Function.onFun Disjoint fun r : ℕ => (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g | ∃ x ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, ∃ y ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, g = x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y}) := by
  intro k _ _ _ _ h N d hd hpos t ht j hj m _ _ _
  refine ⟨fun r => ?_, fun r r' hne => ?_⟩
  · exact (QuotientGroup.isOpenMap_coe _
      (GlobalTheory.CompanionTheory.ContractingCosets.isOpen_doubleCoset _
        (GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k N m) _)).measurableSet
  · refine Set.disjoint_left.2 ?_
    rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, e₁⟩ ⟨_, ⟨x', hx', y', hy', rfl⟩, e₂⟩
    have e : (QuotientGroup.mk (x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y) : AdGL k N) =
        QuotientGroup.mk (x' * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r' * y') :=
      e₁.trans e₂.symm
    exact hne (le_antisymm
      (ContractingCosetsPort.le_of_mk_eq d hd hpos t ht j hj m hx' hy' hx hy e.symm)
      (ContractingCosetsPort.le_of_mk_eq d hd hpos t ht j hj m hx hy hx' hy' e))
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JacquetDict

theorem twKer_one_eq_coinvariantsKer {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (U : Subgroup G) :
    twKer ρ U 1 = Representation.Coinvariants.ker (ρ.comp U.subtype) := by
  unfold GlobalTheory.PRep.twKer Representation.Coinvariants.ker
  congr 1
  ext w
  constructor
  · rintro ⟨n, v, rfl⟩
    exact ⟨(n, v), by simp⟩
  · rintro ⟨⟨n, v⟩, rfl⟩
    exact ⟨n, v, by simp⟩

theorem jacquet_stdBlocks_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), ∃ e : Jacquet π (unipRad k (stdBlocks d hd)) ≃ₗ[ℂ] GroundTheory.Automorphic.Parabolic.JacquetModule k N (Zl.JC.blockIdx d hd) π, (∀ v : V, e (Submodule.Quotient.mk v) = Representation.Coinvariants.mk _ v) ∧ ∀ (g : Levi k (fun a => Fin (d a))) (hg : leviEmb k (stdBlocks d hd) g ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd)) (x : Jacquet π (unipRad k (stdBlocks d hd))), e (jacU (stdBlocks d hd) π g x) = GroundTheory.Automorphic.Parabolic.jacquetAction k N (Zl.JC.blockIdx d hd) π ⟨_, hg⟩ (e x) := by
  intro k _ _ _ _ N V _ _ π h d hd
  have hPQ := GlobalTheory.CompanionTheory.ParabolicCompare.unipRad_stdBlocks_eq_unipotentRadical k h N d hd
  have hK : twKer π (unipRad k (stdBlocks d hd)) 1 =
      Representation.Coinvariants.ker
        (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd)).subtype) := by
    rw [hPQ]
    exact twKer_one_eq_coinvariantsKer π _
  refine ⟨Submodule.quotEquivOfEq _ _ hK, ?_, ?_⟩
  · intro v
    rfl
  · intro g hg x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

end GlobalTheory.CompanionTheory.JacquetDict
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.TensHkSum

open PositivityTheory.Rg.BcB.F.Tail.PExp

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem extTensor_apply_eq (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (m : G × H) :
    extTensor ρ σ m = TensorProduct.map (ρ m.1) (σ m.2) := by
  rfl

theorem hkE_eq_sum (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ)
    (hs : {q : G ⧸ K | f q.out ≠ 0}.Finite) :
    hkE ρ K f = ∑ q ∈ hs.toFinset, f q.out • ρ q.out := by
  unfold PositivityTheory.Rg.BcB.F.Tail.PExp.hkE
  apply finsum_eq_sum_of_support_subset
  intro q hq
  rw [Function.mem_support] at hq
  rw [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
  intro h0
  exact hq (by simp [h0])

theorem map_sum_sum_apply {A B : Type} (s : Finset A) (t : Finset B) (a : A → ℂ) (b : B → ℂ)
    (P : A → Module.End ℂ V) (Q : B → Module.End ℂ W) (v : V ⊗[ℂ] W) :
    TensorProduct.map (∑ i ∈ s, a i • P i) (∑ j ∈ t, b j • Q j) v =
      ∑ p ∈ s ×ˢ t, (a p.1 * b p.2) • TensorProduct.map (P p.1) (Q p.2) v := by
  have hB : ∀ (P' : Module.End ℂ V) (Q' : Module.End ℂ W),
      TensorProduct.map P' Q' v = TensorProduct.mapBilinear (RingHom.id ℂ) V W V W P' Q' v := fun P' Q' => by
    rw [TensorProduct.mapBilinear_apply]

  simp only [hB, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_product,
  Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem bijective_mk_out_prod (K : Subgroup G) (L : Subgroup H) :
    Function.Bijective (fun p : (G ⧸ K) × (H ⧸ L) =>
      (QuotientGroup.mk (p.1.out, p.2.out) : (G × H) ⧸ K.prod L)) := by
  constructor
  · rintro ⟨q1, r1⟩ ⟨q2, r2⟩ h
    simp only at h
    rw [QuotientGroup.eq, Subgroup.mem_prod] at h
    obtain ⟨h1, h2⟩ := h
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv] at h1 h2
    have e1 : (QuotientGroup.mk q1.out : G ⧸ K) = QuotientGroup.mk q2.out := QuotientGroup.eq.mpr h1
    have e2 : (QuotientGroup.mk r1.out : H ⧸ L) = QuotientGroup.mk r2.out := QuotientGroup.eq.mpr h2
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at e1 e2
    rw [e1, e2]
  · intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    refine ⟨((QuotientGroup.mk x.1 : G ⧸ K), (QuotientGroup.mk x.2 : H ⧸ L)), ?_⟩
    simp only
    rw [QuotientGroup.eq, Subgroup.mem_prod]
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
    exact ⟨QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk x.1 : G ⧸ K)),
      QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk x.2 : H ⧸ L))⟩

theorem apply_out_mk {X : Type} (K : Subgroup G) (Φ : G → X) (hΦ : ∀ x, ∀ k ∈ K, Φ (x * k) = Φ x) (x : G) :
    Φ (QuotientGroup.mk x : G ⧸ K).out = Φ x := by
  have hk : x⁻¹ * (QuotientGroup.mk x : G ⧸ K).out ∈ K :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk x : G ⧸ K)).symm
  have e := hΦ x _ hk
  rw [mul_inv_cancel_left] at e
  exact e

theorem tensHk : TensHk := by
  intro G H V W _ _ _ _ _ _ ρ σ K L f e hf he hsf hse v hv
  have hfix : ∀ k ∈ K.prod L, extTensor ρ σ k v = v := by
    intro k hk
    have h1 := hv ⟨k, hk⟩
    simpa using h1
  have hinv : ∀ x : G × H, ∀ k ∈ K.prod L,
      (f (x * k).1 * e (x * k).2) • extTensor ρ σ (x * k) v = (f x.1 * e x.2) • extTensor ρ σ x v := by
    intro x k hk
    have hk' := Subgroup.mem_prod.mp hk
    rw [Prod.fst_mul, Prod.snd_mul, hf _ _ hk'.1, he _ _ hk'.2, map_mul, Module.End.mul_apply, hfix k hk]
  have key : (∑ᶠ q : (G × H) ⧸ K.prod L, (f q.out.1 * e q.out.2) • extTensor ρ σ q.out v)
      = ∑ᶠ p : (G ⧸ K) × (H ⧸ L), (f p.1.out * e p.2.out) • TensorProduct.map (ρ p.1.out) (σ p.2.out) v := by
    rw [← finsum_comp_equiv (Equiv.ofBijective _ (bijective_mk_out_prod K L))]
    apply finsum_congr
    intro p
    rw [Equiv.ofBijective_apply]
    have h2 := apply_out_mk (K.prod L) (fun m : G × H => (f m.1 * e m.2) • extTensor ρ σ m v) hinv
      (p.1.out, p.2.out)
    simp only at h2
    rw [extTensor_apply_eq] at h2
    exact h2
  unfold PositivityTheory.Rg.BcB.F.Tail.PExp.hkS
  show (∑ᶠ q : (G × H) ⧸ K.prod L, (f q.out.1 * e q.out.2) • extTensor ρ σ q.out v) = _
  rw [key, hkE_eq_sum ρ K f hsf, hkE_eq_sum σ L e hse, map_sum_sum_apply]
  apply finsum_eq_sum_of_support_subset
  intro p hp
  rw [Function.mem_support] at hp
  rw [Finset.coe_product, Set.mem_prod, Set.Finite.coe_toFinset, Set.Finite.coe_toFinset,
    Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  constructor
  · intro h0
    exact hp (by simp [h0])
  · intro h0
    exact hp (by simp [h0])

end GlobalTheory.CompanionTheory.TensHkSum

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.StandardBlocks

theorem stdBlocks_one {n : ℕ} (hd : ∑ _a : Fin n, 1 = n) (a : Fin n) (i : Fin 1) :
    stdBlocks (fun _ : Fin n => 1) hd ⟨a, i⟩ = a := by
  have hi : (i : ℕ) = 0 := by
    have := i.isLt
    omega
  apply Fin.ext
  rw [stdBlocks_val]
  simp [hi]

theorem blk_stdBlocks {n : ℕ} (hd : ∑ _a : Fin n, 1 = n) (i : Fin n) :
    blk (stdBlocks (fun _ : Fin n => 1) hd) i = i := by
  obtain ⟨⟨a, p⟩, rfl⟩ := (stdBlocks (fun _ : Fin n => 1) hd).surjective i
  rw [blk_apply]
  exact (stdBlocks_one hd a p).symm

theorem unipRad_stdBlocks (k : Type) [Field k] {n : ℕ} (hd : ∑ _a : Fin n, 1 = n) :
    unipRad k (stdBlocks (fun _ : Fin n => 1) hd) = unipB k (Fin n) := by
  have hb2 : ∀ i : Fin n, blk (points (Fin n)) i = i := fun i => by
    have h := blk_apply (points (Fin n)) i ()
    rwa [points_apply] at h
  ext g
  rw [unipB, mem_unipRad, mem_unipRad, mem_parab, mem_parab]
  simp only [blk_stdBlocks, hb2]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a i j => ?_⟩
    have h := h2 a (0 : Fin 1) (0 : Fin 1)
    simp only [stdBlocks_one] at h
    simp only [points_apply]
    rw [h]
    simp [Matrix.one_apply]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a i j => ?_⟩
    have h := h2 a () ()
    simp only [points_apply] at h
    simp only [stdBlocks_one]
    obtain rfl : i = j := Subsingleton.elim i j
    rw [h]
    simp [Matrix.one_apply]

theorem leviEmb_stdBlocks (k : Type) [Field k] {n : ℕ} (hd : ∑ _a : Fin n, 1 = n)
    (t : Levi k fun _ : Fin n => Fin 1) :
    leviEmb k (stdBlocks (fun _ : Fin n => 1) hd) t =
      diagT k (Fin n) fun a => Matrix.GeneralLinearGroup.det (t a) := by
  apply Units.ext
  ext i j
  obtain ⟨⟨a, p⟩, rfl⟩ := (stdBlocks (fun _ : Fin n => 1) hd).surjective i
  obtain ⟨⟨b, q⟩, rfl⟩ := (stdBlocks (fun _ : Fin n => 1) hd).surjective j
  rw [val_diagT]
  by_cases hab : a = b
  · subst hab
    have hpq : p = q := Subsingleton.elim _ _
    subst hpq
    rw [leviEmb_apply_same, stdBlocks_one]
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one, Subsingleton.elim p 0]
  · rw [leviEmb_apply_ne k _ t hab, stdBlocks_one, stdBlocks_one, Matrix.diagonal_apply_ne _ hab]

theorem deltaHalf_stdBlocks (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (t : Levi k fun _ : Fin n => Fin 1) :
    deltaHalf k (fun _ : Fin n => Fin 1) t =
      deltaHalf k (fun _ : Fin n => Unit)
        (leviTorus k (Fin n) fun a => Matrix.GeneralLinearGroup.det (t a)) := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [modExp_fin (fun _ : Fin n => Fin 1) (fun _ => Fintype.card_fin 1) a,
    modExp_fin (fun _ : Fin n => Unit) (fun _ => Fintype.card_unit) a]
  congr 1
  exact (congrFun ((leviTorus k (Fin n)).symm_apply_apply
    fun a => Matrix.GeneralLinearGroup.det (t a)) a).symm

theorem twKer_one_congr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) {N N' : Subgroup G} (h : N = N') : twKer π N 1 = twKer π N' 1 := by
  subst h
  rfl

theorem torusChar_stdBlocks {k : Type} [Field k] {n : ℕ} (χ : Fin n → kˣ →* ℂˣ)
    (t : ∀ _ : Fin n, GL (Fin 1) k) :
    PositivityTheory.Lbc.torusChar χ t =
      (_root_.GlobalTheory.SmGL.torusChar χ (fun a => Matrix.GeneralLinearGroup.det (t a)) : ℂ) := by
  rw [PositivityTheory.Lbc.torusChar, GlobalTheory.SmGL.torusChar, MonoidHom.finsetProd_apply, Units.coe_prod]
  rfl

private theorem smul_mk_eq_smul_mk_of_submodule_eq {V : Type} [AddCommGroup V] [Module ℂ V]
    {p q : Submodule ℂ V} (h : p = q) (a b : ℂ) (u w : V)
    (hk : a • (Submodule.Quotient.mk u : V ⧸ p) = b • Submodule.Quotient.mk w) :
    a • (Submodule.Quotient.mk u : V ⧸ q) = b • Submodule.Quotient.mk w := by
  subst h
  exact hk

theorem stdBridge : PositivityTheory.Rg.BcB.F.Tail.PExp.StdBridge := by
  intro k _ _ _ _ n hd V _ _ π χ y hy heig
  have hK : twKer π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) 1 =
      twKer π (unipRad k (points (Fin n))) 1 :=
    twKer_one_congr π (unipRad_stdBlocks k hd)
  obtain ⟨w, rfl⟩ :=
    Submodule.Quotient.mk_surjective (twKer π (unipRad k (points (Fin n))) 1) y
  refine ⟨(Submodule.Quotient.mk w :
    V ⧸ twKer π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) 1), ?_, ?_⟩
  · intro h
    apply hy
    have h' : w ∈ twKer π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) 1 :=
      (Submodule.Quotient.mk_eq_zero _).mp h
    rw [hK] at h'
    exact (Submodule.Quotient.mk_eq_zero _).mpr h'
  · intro t
    have key : (_root_.GlobalTheory.SmGL.jac (points (Fin n)) π
        (leviTorus k (Fin n) fun a => Matrix.GeneralLinearGroup.det (t a)))
          (Submodule.Quotient.mk w) =
        ((_root_.GlobalTheory.SmGL.torusChar χ fun a => Matrix.GeneralLinearGroup.det (t a) : ℂˣ) : ℂ) •
          Submodule.Quotient.mk w :=
      heig (fun a => Matrix.GeneralLinearGroup.det (t a))
    have hD : leviEmb k (points (Fin n))
        (leviTorus k (Fin n) fun a => Matrix.GeneralLinearGroup.det (t a)) =
        diagT k (Fin n) (fun a => Matrix.GeneralLinearGroup.det (t a)) := rfl
    rw [_root_.GlobalTheory.SmGL.jac_mk, hD] at key
    have heq : (_root_.GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd) π t) (Submodule.Quotient.mk w) =
        PositivityTheory.Lbc.torusChar χ t • (Submodule.Quotient.mk w :
          V ⧸ twKer π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) 1) := by
      rw [_root_.GlobalTheory.SmGL.jac_mk, leviEmb_stdBlocks, deltaHalf_stdBlocks, torusChar_stdBlocks]
      exact smul_mk_eq_smul_mk_of_submodule_eq hK.symm _ _ _ _ key
    rw [Module.End.mem_maxGenEigenspace]
    refine ⟨1, ?_⟩
    rw [pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    exact heq

end GlobalTheory.CompanionTheory.StandardBlocks

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RepTensor

theorem extTensor_left {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (k : G) :
    extTensor ρ σ (k, 1) = TensorProduct.map (ρ k) LinearMap.id :=
  TensorProduct.ext' fun a b => by simp [extTensor_tmul]

theorem extTensor_right {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (h : H) :
    extTensor ρ σ (1, h) = TensorProduct.map LinearMap.id (σ h) :=
  TensorProduct.ext' fun a b => by simp [extTensor_tmul]

theorem contr_left {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Module.End ℂ V) (l : Module.Dual ℂ W) (v : V ⊗[ℂ] W) :
    A (TensorProduct.rid ℂ V (LinearMap.lTensor V l v)) =
      TensorProduct.rid ℂ V (LinearMap.lTensor V l (TensorProduct.map A LinearMap.id v)) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x w => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem contr_right {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (B : Module.End ℂ W) (l : Module.Dual ℂ V) (v : V ⊗[ℂ] W) :
    B (TensorProduct.lid ℂ W (LinearMap.rTensor W l v)) =
      TensorProduct.lid ℂ W (LinearMap.rTensor W l (TensorProduct.map LinearMap.id B v)) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x w => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem mem_fixed_iff' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {K : Subgroup G} {v : V} :
    v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  constructor
  · intro h k hk
    have := h ⟨k, hk⟩
    simpa using this
  · intro h k
    have := h k k.2
    show ρ (k : G) v = ((1 : K →* ℂˣ) k : ℂ) • v
    simpa using this

theorem contrFix : PositivityTheory.Rg.BcB.F.Tail.PExp.ContrFix := by
  intro G H V W _ _ _ _ _ _ ρ σ K L v hv
  have hv' := mem_fixed_iff'.1 hv
  refine ⟨fun l => mem_fixed_iff'.2 fun k hk => ?_, fun l => mem_fixed_iff'.2 fun h hh => ?_⟩
  · have h1 := hv' (k, 1) ⟨hk, L.one_mem⟩
    rw [extTensor_left] at h1
    rw [contr_left, h1]
  · have h1 := hv' (1, h) ⟨K.one_mem, hh⟩
    rw [extTensor_right] at h1
    rw [contr_right, h1]

end GlobalTheory.CompanionTheory.RepTensor
end

section

namespace GlobalTheory.CompanionTheory.HeckeEnd

open PositivityTheory.Rg.BcB.F.Tail.PExp

theorem hkE_fin : HkEFin := by
  intro G V _ _ _ ρ K f hf v
  unfold PositivityTheory.Rg.BcB.F.Tail.PExp.hkE PositivityTheory.Rg.BcB.F.Tail.PExp.hkS
  rw [finsum_eq_sum_of_support_subset (s := hf.toFinset),
    finsum_eq_sum_of_support_subset (s := hf.toFinset), LinearMap.sum_apply]
  · rfl
  all_goals
    intro q hq
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h
    rw [Function.mem_support] at hq
    exact hq (by simp [h])

end GlobalTheory.CompanionTheory.HeckeEnd
end
