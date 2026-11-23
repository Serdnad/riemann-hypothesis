module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle134
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.levelSplit :
    UpperTheory.V.Cj.S.LevelSplit := by
  intro E _ _ a L hL
  have ho : IsOpen ((L ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a : Subgroup (GL (Fin a) (Af E))) :
      Set (GL (Fin a) (Af E))) := hL.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E a)
  have hev := LocSph.eventually_mem (ho.mem_nhds (one_mem _))
  refine ⟨_, ho, inf_le_left, _, Filter.eventually_cofinite.1 hev, fun w hw => ?_⟩
  have hw' := not_not.1 hw
  have h1 : ∀ k ∈ KGL w (n := a), locGL E a w k ∈ L ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a := by
    rintro _ ⟨g, rfl⟩
    exact hw' g
  refine ⟨h1, fun u hu => ?_⟩
  have hk : GeneralLinearGroup.map (pLoc E w) u ∈ KGL w (n := a) := by
    obtain ⟨h2, h3⟩ := (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E a).1 hu.2
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · exact h2 i j w
    · rw [← map_inv]
      exact h3 i j w
  exact ⟨_, hk, _, mul_mem (inv_mem (h1 _ hk)) hu, LocEx.map_pLoc_inv_mul w u, (mul_inv_cancel_left _ _).symm⟩
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.hkLocal :
    UpperTheory.V.Cj.S.SumInner → UpperTheory.V.Cj.S.MatBlock → UpperTheory.V.Cj.S.HkLocal := by
  intro hSum hMat E _ _ w r s ϖ hϖ hu _ j Φ hΦ
  have hπ0 : ((⟨ϖ, hϖ⟩ : Ov E w) : HeightOneSpectrum.adicCompletion E w) ≠ 0 := by
    intro h0
    have h1 : Valued.v ϖ = 0 := by
      have h2 : ϖ = 0 := h0
      rw [h2, map_zero]
    rw [hu] at h1
    exact WithZero.coe_ne_zero h1
  have hq : Fintype.card (satakeRes (Ov E w) ⟨ϖ, hϖ⟩) = qV E w := by
    have key : ∀ z : WithZero (Multiplicative ℤ), z < 1 → z ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      intro z hz
      induction z using WithZero.recZeroCoe with
      | zero => exact zero_le'
      | coe a =>
        rw [← WithZero.coe_one, WithZero.coe_lt_coe] at hz
        rw [WithZero.coe_le_coe]
        have h1 : (Multiplicative.toAdd a : ℤ) < 0 := hz
        change (Multiplicative.toAdd a : ℤ) ≤ -1
        omega
    have hlt : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
      rw [← WithZero.coe_one, WithZero.coe_lt_coe]
      change (-1 : ℤ) < 0
      omega
    have hint := Valuation.valuationSubring.integers
      (Valued.v : Valuation (HeightOneSpectrum.adicCompletion E w) (WithZero (Multiplicative ℤ)))
    have hmax : Ideal.span {(⟨ϖ, hϖ⟩ : HeightOneSpectrum.adicCompletionIntegers E w)} =
        IsLocalRing.maximalIdeal (HeightOneSpectrum.adicCompletionIntegers E w) := by
      ext x
      rw [Ideal.mem_span_singleton]
      constructor
      · intro h
        have h2 := hint.le_of_dvd h
        exact (Valuation.mem_maximalIdeal_iff (v := Valued.v)).2 (lt_of_le_of_lt (h2.trans_eq hu) hlt)
      · intro h
        have h2 := (Valuation.mem_maximalIdeal_iff (v := Valued.v)).1 h
        exact hint.dvd_of_le ((key _ h2).trans_eq hu.symm)
    rw [Fintype.card_eq_nat_card, ← tjcosets_card_residue w]
    show Nat.card (↥(HeightOneSpectrum.adicCompletionIntegers E w) ⧸
      Ideal.span {(⟨ϖ, hϖ⟩ : HeightOneSpectrum.adicCompletionIntegers E w)}) = _
    rw [hmax]
    rfl
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin r) → Finset (Fin s) → ℂ, ∀ A B, T A B =
      ∑ c₁ : satakePairs A → satakeRes (Ov E w) ⟨ϖ, hϖ⟩, ∑ c₂ : satakePairs B → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
        Φ (blk (satakeGL (Ov E w) hπ0 A (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₁ p)))
          (satakeGL (Ov E w) hπ0 B (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₂ p)))) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : Finset (Fin r) × Finset (Fin s) → Fin (r + 1) × Fin (s + 1),
      ∀ AB, κ AB = (⟨AB.1.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ AB.1)⟩,
        ⟨AB.2.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ AB.2)⟩) :=
    ⟨_, fun _ => rfl⟩
  have hS : ∀ S : Finset (Fin (r + s)),
      ∑ c : satakePairs S → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
        Φ (satakeGL (Ov E w) hπ0 S (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))) =
      (qV E w : ℂ) ^ ((sub1 S).card * (s - (sub2 S).card)) * T (sub1 S) (sub2 S) := by
    intro S
    rw [hT]
    have h := hSum r s (satakeRes (Ov E w) ⟨ϖ, hϖ⟩) S (fun c₁ c₂ =>
      Φ (blk (satakeGL (Ov E w) hπ0 (sub1 S) (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₁ p)))
        (satakeGL (Ov E w) hπ0 (sub2 S) (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₂ p)))))
    rw [hq] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    obtain ⟨X, hX⟩ := hMat _ (Ov E w) r s _ hπ0 S (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))
    rw [hX, hΦ]
    rfl
  have hcard : ∀ S : Finset (Fin (r + s)), S.card = (sub1 S).card + (sub2 S).card := by
    intro S
    calc S.card = ∑ i : Fin (r + s), if i ∈ S then 1 else 0 := by simp [Finset.sum_boole]
      _ = _ := Fin.sum_univ_add _
      _ = _ := by simp [sub1, sub2, Finset.sum_boole]
  let e : Finset (Fin (r + s)) ≃ Finset (Fin r) × Finset (Fin s) :=
    { toFun := fun S => (sub1 S, sub2 S)
      invFun := fun AB => AB.1.map (Fin.castAddEmb s) ∪ AB.2.map (Fin.natAddEmb r)
      left_inv := by
        intro S
        ext x
        refine Fin.addCases (fun i => ?_) (fun i => ?_) x <;> simp [sub1, sub2] <;>
          intro y hy h <;> rw [← h] <;> exact hy
      right_inv := by
        rintro ⟨A, B⟩
        ext i <;> simp [sub1, sub2] <;> intro y _ h <;> exfalso <;> rw [Fin.ext_iff] at h <;>
          simp at h <;> have := i.isLt <;> have := y.isLt <;> omega }
  have hsubj : ∀ F : Finset (Fin (r + s)) → ℂ,
      ∑ S : {S : Finset (Fin (r + s)) // S.card = j}, F S.1 =
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin (r + s)) => S.card = j), F S :=
    fun F => (Finset.sum_subtype _ (fun S => by simp) F).symm
  have hG : ∑ i : SatakeIdx (n := r + s) w hϖ j, Φ (satakeB w hϖ hu i) =
      ∑ AB, coef (qV E w) r s j (κ AB) * T AB.1 AB.2 := by
    calc ∑ i : SatakeIdx (n := r + s) w hϖ j, Φ (satakeB w hϖ hu i)
        = ∑ S : {S : Finset (Fin (r + s)) // S.card = j},
            ∑ c : satakePairs S.1 → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
              Φ (satakeGL (Ov E w) hπ0 S.1 (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))) :=
          Fintype.sum_sigma (fun i => Φ (satakeB w hϖ hu i))
      _ = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin (r + s)) => S.card = j),
            ∑ c : satakePairs S → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
              Φ (satakeGL (Ov E w) hπ0 S (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))) :=
          hsubj (fun S => ∑ c : satakePairs S → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
              Φ (satakeGL (Ov E w) hπ0 S (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))))
      _ = ∑ S : Finset (Fin (r + s)), if S.card = j then
            (qV E w : ℂ) ^ ((sub1 S).card * (s - (sub2 S).card)) * T (sub1 S) (sub2 S) else 0 := by
          rw [Finset.sum_filter]
          simp only [hS]
      _ = ∑ S, coef (qV E w) r s j (κ (e S)) * T (e S).1 (e S).2 := by
          refine Finset.sum_congr rfl (fun S _ => ?_)
          simp only [e, Equiv.coe_fn_mk, hκ, coef, hcard S]
          split_ifs <;> simp
      _ = ∑ AB, coef (qV E w) r s j (κ AB) * T AB.1 AB.2 :=
          Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hR : ∀ a b : ℕ, ∑ i₁ : SatakeIdx (n := r) w hϖ a, ∑ i₂ : SatakeIdx (n := s) w hϖ b,
      Φ (blk (satakeB w hϖ hu i₁) (satakeB w hϖ hu i₂)) =
      ∑ AB ∈ (Finset.univ.filter (fun A : Finset (Fin r) => A.card = a)) ×ˢ
        (Finset.univ.filter (fun B : Finset (Fin s) => B.card = b)), T AB.1 AB.2 := by
    intro a b
    rw [Finset.sum_product]
    calc _ = ∑ A : {A : Finset (Fin r) // A.card = a}, ∑ c₁ : satakePairs A.1 → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
            ∑ i₂ : SatakeIdx (n := s) w hϖ b,
              Φ (blk (satakeGL (Ov E w) hπ0 A.1 (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₁ p)))
                (satakeB w hϖ hu i₂)) :=
          Fintype.sum_sigma (fun i₁ => ∑ i₂ : SatakeIdx (n := s) w hϖ b,
            Φ (blk (satakeB w hϖ hu i₁) (satakeB w hϖ hu i₂)))
      _ = ∑ A : {A : Finset (Fin r) // A.card = a}, ∑ B : {B : Finset (Fin s) // B.card = b}, T A.1 B.1 := by
          refine Finset.sum_congr rfl (fun A _ => ?_)
          simp only [hT]
          refine (Finset.sum_congr rfl (fun c₁ _ => Fintype.sum_sigma _)).trans ?_
          exact Finset.sum_comm
      _ = _ := by
          rw [← Finset.sum_subtype (Finset.univ.filter (fun A : Finset (Fin r) => A.card = a)) (by simp)
            (fun A => ∑ B : {B : Finset (Fin s) // B.card = b}, T A B.1)]
          refine Finset.sum_congr rfl (fun A _ => ?_)
          exact (Finset.sum_subtype _ (by simp) _).symm
  rw [hG]
  simp only [hR]
  rw [← Finset.sum_fiberwise Finset.univ κ]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.mul_sum]
  have hfib : Finset.univ.filter (fun AB => κ AB = p) =
      (Finset.univ.filter (fun A : Finset (Fin r) => A.card = (p.1 : ℕ))) ×ˢ
        (Finset.univ.filter (fun B : Finset (Fin s) => B.card = (p.2 : ℕ))) := by
    ext ⟨A, B⟩
    simp [hκ, Prod.ext_iff, Fin.ext_iff]
  rw [hfib]
  refine Finset.sum_congr rfl (fun AB hAB => ?_)
  have hp : κ AB = p := by
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hAB
    rw [hκ]
    ext <;> simp [hAB]
  rw [hp]
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem UpperTheory.V.Cj.S.exists_interp {Y : Type} (V : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ V] :
    ∃ (n : ℕ) (b : Fin n → V) (c : Fin n → Y →₀ ℂ),
      ∀ f ∈ V, ∀ y, f y = ∑ i, (b i).1 y * (c i).sum fun z t => t * f z := by
  classical
  let ev : Y → (V →ₗ[ℂ] ℂ) := fun y => (LinearMap.proj y).comp V.subtype
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro z hz
    by_contra h
    apply hz
    ext y
    by_contra hy
    exact h ⟨ev y, ⟨y, rfl⟩, hy⟩
  let b := Module.finBasis ℂ V
  have hc : ∀ i, ∃ c : Y →₀ ℂ, (c.sum fun z t => t • ev z) = b.coord i := fun i =>
    Finsupp.mem_span_range_iff_exists_finsupp.1 (hspan ▸ Submodule.mem_top)
  choose c hc using hc
  refine ⟨_, b, c, fun f hf y => ?_⟩
  have h := congrArg (ev y) (b.sum_repr ⟨f, hf⟩)

  rw [map_sum] at h
  simp only [map_smul] at h
  refine h.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
  have h2 : b.repr ⟨f, hf⟩ i = (c i).sum fun z t => t * f z := by
    rw [← b.coord_apply, ← hc i, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply]
    rfl
  rw [h2, smul_eq_mul, mul_comm]
  rfl

theorem UpperTheory.V.Cj.S.typesComm :
    UpperTheory.V.Cj.S.TypesComm := by
  intro E _ _ _ a V hV T hT φ hφ g
  obtain ⟨n, b, c, hc⟩ := UpperTheory.V.Cj.S.exists_interp V
  let R : archCompact E a → Module.End ℂ (Sm E a) := fun k => cptRep E a ((Cm.cptEq E a).symm k)
  have hR : ∀ (k : archCompact E a) (ψ : Sm E a) (x), (R k ψ).1 x = ψ.1 (x * infEmb E a k.1) := by
    intro k ψ x
    obtain ⟨k, rfl⟩ := (Cm.cptEq E a).surjective k
    simp only [R]
    rw [MulEquiv.symm_apply_apply, Cm.infEmb_cptEq]
    rfl
  have hTR : ∀ (k : archCompact E a) (ψ : Sm E a), T (R k ψ) = R k (T ψ) := fun k ψ =>
    LinearMap.congr_fun (hT _).eq ψ
  have hev : ∀ (k : archCompact E a) (ψ : Sm E a) (x),
      (∑ i, (b i).1 k • ∑ z ∈ (c i).support, c i z • R z ψ : Sm E a).1 x =
        ∑ i, (b i).1 k * (c i).sum fun z t => t * ψ.1 (x * infEmb E a z.1) := by
    intro k ψ x
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR, Finsupp.sum]
  have h1 : ∀ k : archCompact E a, R k φ = ∑ i, (b i).1 k • ∑ z ∈ (c i).support, c i z • R z φ := by
    intro k
    refine Subtype.ext (funext fun x => ?_)
    rw [hR, hev]
    exact hc _ (hφ x) k
  have h2 : (fun k : archCompact E a => (T φ).1 (g * infEmb E a k.1)) =
      ∑ i, ((c i).sum fun z t => t * (T φ).1 (g * infEmb E a z.1)) • (b i).1 := by
    funext k
    rw [← hR k, ← hTR, h1 k]

    simp only [map_sum, map_smul, hTR]
    rw [hev]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [h2]
  exact V.sum_mem fun i _ => V.smul_mem _ (b i).2
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem exists_types {G H : Type} [Group G] [Group H] (i : H →* G) (W : Submodule ℂ (G → ℂ))
    [FiniteDimensional ℂ W] (hW : ∀ h, ∀ f ∈ W, (fun g => f (g * i h)) ∈ W) :
    ∃ V : Submodule ℂ (H → ℂ), FiniteDimensional ℂ V ∧ (∀ f ∈ V, ∀ k', (fun k => f (k * k')) ∈ V) ∧
      ∀ f ∈ W, ∀ g, (fun k => f (g * i k)) ∈ V := by
  let ρ : H → W →ₗ[ℂ] W := fun h => (LinearMap.funLeft ℂ ℂ fun g => g * i h).restrict (hW h)
  have hρ : ∀ k k' w, ρ (k * k') w = ρ k (ρ k' w) := fun k k' w =>
    Subtype.ext (funext fun g => by
      change w.1 (g * i (k * k')) = w.1 (g * i k * i k')
      rw [map_mul, mul_assoc])
  let m : Module.Dual ℂ W →ₗ[ℂ] W →ₗ[ℂ] (H → ℂ) :=
    LinearMap.mk₂ ℂ (fun l w k => l (ρ k w)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => by funext k; simp) (fun _ _ _ => by funext k; simp)
  refine ⟨LinearMap.range (TensorProduct.lift m), inferInstance, ?_, fun f hf g => ?_⟩
  · rintro _ ⟨t, rfl⟩ k'
    induction t using TensorProduct.inductionOn with
    | tmul l w => exact ⟨l ⊗ₜ ρ k' w, funext fun k => congrArg l (hρ k k' w).symm⟩
    | add s t hs ht => rw [map_add]; exact add_mem hs ht
  · exact ⟨((LinearMap.proj g).comp W.subtype) ⊗ₜ ⟨f, hf⟩, rfl⟩

private theorem exists_types' {G H : Type} [Group G] [Group H] (i : H →* G) (C : Subgroup G) (hi : ∀ k, i k ∈ C) (f : G → ℂ)
    (hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : C => GroundTheory.Automorphic.rightTranslate (k : G) f))) :
    ∃ V : Submodule ℂ (H → ℂ), FiniteDimensional ℂ V ∧ (∀ f ∈ V, ∀ k', (fun k => f (k * k')) ∈ V) ∧
      ∀ g, (fun k => f (g * i k)) ∈ V := by
  obtain ⟨V, h1, h2, h3⟩ := exists_types i
    (Submodule.span ℂ (Set.range fun k : C => GroundTheory.Automorphic.rightTranslate (k : G) f)) (fun k ψ hψ => by
      induction hψ using Submodule.span_induction with
      | mem ψ hψ =>
        obtain ⟨l, rfl⟩ := hψ
        exact Submodule.subset_span ⟨⟨i k, hi k⟩ * l, funext fun g => congrArg f (mul_assoc g (i k) l.1).symm⟩
      | zero => exact zero_mem _
      | add _ _ _ _ a b => exact add_mem a b
      | smul c _ _ a => exact Submodule.smul_mem _ c a)
  exact ⟨V, h1, h2, h3 f (Submodule.subset_span ⟨1, funext fun g => congrArg f (mul_one g)⟩)⟩

private theorem exists_monic {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (W : Submodule ℂ M)
    [FiniteDimensional ℂ W] (hW : ∀ x ∈ W, T x ∈ W) : UpperTheory.V.Af.Fin.AlgMod W ⊥ T := by
  obtain ⟨p, hp, h⟩ := LinearMap.exists_monic_and_aeval_eq_zero ℂ (T.restrict hW)
  refine ⟨p, hp, fun x hx => ?_⟩
  have key : ∀ q : Polynomial ℂ, Polynomial.aeval T q x = (Polynomial.aeval (T.restrict hW) q ⟨x, hx⟩ : W) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add q r hq hr => simp only [map_add (f := _), LinearMap.add_apply, hq, hr, Submodule.coe_add]
    | monomial n c =>
      simp only [Polynomial.aeval_monomial, mul_apply_eq_comp, Module.algebraMap_end_apply, Submodule.coe_smul,
        Module.End.pow_restrict n hW, LinearMap.restrict_apply]
  rw [key, h]
  rfl

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm in
private theorem bdd_span {K : Type} [Field K] [NumberField K] {n : ℕ} (f : archSmooth K n) (h : IsAutomorphicForm f.1) :
    Bdd (Submodule.span ℂ {f}) := by
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, ?_, ?_, fun z hz => ?_⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact h.isLeftInvariant.smul c
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact h.hasModerateGrowth.smul c
  · obtain ⟨U, -, hU⟩ := exists_openSubgroup_rightInvariant h.isSmooth h.isKFinite
    refine ⟨U.toSubgroup, U.isOpen, fun φ hφ u hu g => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact congrArg (c • ·) (hU g u hu)
  · have hK := h.isKFinite
    unfold IsKFinite at hK
    obtain ⟨V, h1, h2, h3⟩ := exists_types' ((infEmb K n).comp (archCompact K n).subtype) Reduction.maxCompact
      (fun k => k.2) f.1 hK
    refine ⟨V, h1, h2, fun φ hφ g => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact V.smul_mem c (h3 g)
  · have hZ : IsZFinite f := h.isZFinite
    unfold IsZFinite at hZ
    refine (exists_monic (uAction z) (Submodule.span ℂ
      ((fun z => uAction z f) '' ((isExpLieAlgebra K n).centerU : Set (UEnv K n)))) (fun ψ hψ => ?_)).mono
      (Submodule.span_mono ?_)
    · induction hψ using Submodule.span_induction with
      | mem ψ hψ =>
        obtain ⟨y, hy, rfl⟩ := hψ
        exact Submodule.subset_span ⟨z * y, mul_mem hz hy, by simp only [map_mul, mul_apply_eq_comp]⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add _ _ _ _ a b => rw [map_add]; exact add_mem a b
      | smul c _ _ a => rw [map_smul]; exact Submodule.smul_mem _ c a
    · rintro _ rfl
      exact ⟨1, one_mem _, by simp only [map_one, Module.End.one_apply]⟩

theorem UpperTheory.V.Cj.S.singleBdd :
    UpperTheory.V.Cj.S.SingleBdd := by
  intro E _ _ _ a φ h
  unfold BddS
  rw [Submodule.map_span, Set.image_singleton]
  exact bdd_span _ ((UpperTheory.V.Cm.isAutForm_iff φ).1 h)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem UpperTheory.V.Cj.S.eig_of_joint (hS : SatOfEig) (hC : CapOfEig)
    {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {T : Set (Pl E)} (hT : T.Finite)
    (φ : Sm E a) (h0 : φ ≠ 0) (haut : IsAutForm φ) (hfix : ∀ w ∉ T, φ ∈ fixed (fL a w) (KGL w (n := a)))
    (l : Ix a T → ℂ) (hl : ∀ i, opIx i φ = l i • φ) :
    ∃ (m : (E →+* ℂ) → Multiset ℂ) (B : Pl E → Multiset ℂˣ), Eig φ m B ∧
      (∀ t u, l (.inl (t, u)) = ((m t).map (u + ·)).prod) ∧
      ∀ (w : Pl E) (hw : w ∉ T) (ϖ : HeightOneSpectrum.adicCompletion E w) (hu : IsUnifV E w ϖ), ∀ j ≤ a,
        l (.inr ⟨⟨w, hw⟩, ⟨_, Tj_mem_hecke hu j⟩⟩) = satEig (qV E w) a (B w) j := by
  classical
  obtain ⟨m, hm⟩ := hC E a φ h0 fun t u => ⟨_, hl (.inl (t, u))⟩
  have hB : ∀ w : Pl E, ∃ B : Multiset ℂˣ, w ∉ T → IsSatVecGL w (fL a w) φ B := by
    intro w
    by_cases hw : w ∈ T
    · exact ⟨0, fun h => (h hw).elim⟩
    · obtain ⟨B, hB⟩ := hS E w a _ (fL a w) φ h0 (hfix w hw) fun h hh => ⟨_, hl (.inr ⟨⟨w, hw⟩, ⟨h, hh⟩⟩)⟩
      exact ⟨B, fun _ => hB⟩
  choose B hB using hB
  refine ⟨m, B, ⟨h0, haut, hm, ?_⟩, fun t u => ?_, fun w hw ϖ hu j hj => ?_⟩
  · exact hT.eventually_cofinite_notMem.mono hB
  · exact smul_left_injective ℂ h0 ((hl (.inl (t, u))).symm.trans ((hm t).2 u))
  · exact smul_left_injective ℂ h0
      ((hl (.inr ⟨⟨w, hw⟩, ⟨_, Tj_mem_hecke hu j⟩⟩)).symm.trans ((hB w hw).2.2.2 ϖ hu j hj))

theorem UpperTheory.V.Cj.S.pairEig :
    UpperTheory.V.Cj.S.TwoVar → UpperTheory.V.Cj.S.StabSp → UpperTheory.V.Cj.S.OpComm → UpperTheory.V.Cj.S.SatOfEig → UpperTheory.V.Cj.S.CapOfEig → UpperTheory.V.Cj.S.PairEig := by
  intro hTV hSt hOp hS hC E _ _ _ r s F S₁ S₂ b₁ b₂ hF h₁ h₂
  obtain ⟨T₁, hT₁, V₁, hS₁, fd₁, aut₁, fix₁, st₁⟩ := hSt E r S₁ b₁
  obtain ⟨T₂, hT₂, V₂, hS₂, fd₂, aut₂, fix₂, st₂⟩ := hSt E s S₂ b₂
  obtain ⟨φ₁, hφ₁, φ₂, hφ₂, l₁, l₂, n₁, n₂, e₁, e₂, H⟩ :=
    hTV _ _ (Sm E r) (Sm E s) V₁ V₂ fd₁ fd₂ (Ix r T₁) (Ix s T₂) opIx opIx st₁ st₂
      (fun i i' v hv => hOp E r T₁ i i' v fun w hw => fix₁ w hw hv)
      (fun i i' v hv => hOp E s T₂ i i' v fun w hw => fix₂ w hw hv) F hF
      (fun y => (h₁ y).imp fun f hf => ⟨hS₁ hf.1, hf.2⟩) (fun x => (h₂ x).imp fun f hf => ⟨hS₂ hf.1, hf.2⟩)
  obtain ⟨m₁, B₁, E₁, c₁, s₁⟩ := eig_of_joint hS hC hT₁ φ₁ n₁ (aut₁ _ hφ₁) (fun w hw => fix₁ w hw hφ₁) l₁ e₁
  obtain ⟨m₂, B₂, E₂, c₂, s₂⟩ := eig_of_joint hS hC hT₂ φ₂ n₂ (aut₂ _ hφ₂) (fun w hw => fix₂ w hw hφ₂) l₂ e₂
  refine ⟨φ₁, φ₂, m₁, m₂, B₁, B₂, E₁, E₂, fun t u v G e hG he => ?_, ?_⟩
  · have := H Unit (fun _ => 1) (fun _ => .inl (t, u)) (fun _ => .inl (t, v)) (fun _ => G) e (fun _ => hG)
      (fun x y => by simpa using he x y)
    rw [← c₁, ← c₂]
    simpa using this
  · filter_upwards [hT₁.eventually_cofinite_notMem, hT₂.eventually_cofinite_notMem] with w hw₁ hw₂ ϖ hu c G e hG he
    have := H (Fin (r + 1) × Fin (s + 1)) c (fun p => .inr ⟨⟨w, hw₁⟩, ⟨_, Tj_mem_hecke hu p.1⟩⟩)
      (fun p => .inr ⟨⟨w, hw₂⟩, ⟨_, Tj_mem_hecke hu p.2⟩⟩) G e hG he
    rw [← this]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [s₁ w hw₁ ϖ hu p.1 (Nat.lt_succ_iff.1 p.1.2), s₂ w hw₂ ϖ hu p.2 (Nat.lt_succ_iff.1 p.2.2)]
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.capOfEig :
    UpperTheory.V.Cj.S.CapOfEig := by
  intro E _ _ _ a φ h0 hc
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  have key : ∀ t : E →+* ℂ, ∃ m : Multiset ℂ, Multiset.card m = a ∧
      ∀ u : ℂ, cap t u φ = (m.map (u + ·)).prod • φ := fun t => by
    obtain ⟨m, hm, h⟩ := GlobalTheory.CuspRep.exists_multiset_qdet (Eop (a := a) t) (((a : ℂ) - 1) / 2) φ f hf
    refine ⟨m, hm, fun u => ?_⟩
    obtain ⟨c, h1⟩ := hc t u
    have h2 : f (cap t u φ) = _ := h u
    rw [h1, map_smul, hf, smul_eq_mul, mul_one] at h2
    rw [h1, h2]
  choose m hm h using key
  exact ⟨m, fun t => ⟨hm t, h t⟩⟩
end
